(* ::Package:: *)

(* ============================================================ *)
(* HOL`Kernel`  — trust boundary                                *)
(*                                                              *)
(* Two encapsulation modes, selected by `$HOLEncapsulationMode` *)
(* read at load time (default: "Strict"):                        *)
(*                                                              *)
(*   "Strict" — closure / gensym encapsulation. The original    *)
(*     design: all kernel state (arityTable, constTypeTable,    *)
(*     axiomList, defnList, axiomIntakeOpen, thmTag) lives in   *)
(*     a Module with Unique gensym names. External code cannot  *)
(*     name these symbols — protection is by *obscurity-via-    *)
(*     gensym* plus context discipline.                          *)
(*                                                              *)
(*     Used by CI's full audit (tests/run_strict.wls). Cannot   *)
(*     be DumpSave-restored across sessions (gensym names       *)
(*     change every cold boot).                                  *)
(*                                                              *)
(*   "Stable" — Private-context fixed names. Kernel state lives *)
(*     at `HOL`Kernel`Private`{holThmTag, arityTable, ...}`     *)
(*     with stable, predictable symbol names. External code is  *)
(*     forbidden from referencing these by *convention + lint*; *)
(*     see CLAUDE.md design-goal section.                       *)
(*                                                              *)
(*     Used for fast iteration: snapshot the bootstrapped       *)
(*     kernel to disk via DumpSave, restore on subsequent runs. *)
(*                                                              *)
(* The defineKernel[…] block below contains all helpers and     *)
(* public API in a single With-substituted body. Mode dispatch  *)
(* at the bottom decides which 6 state symbols to inject.       *)
(* ============================================================ *)

BeginPackage["HOL`Kernel`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`"}];

mkType::usage        = "mkType[name, args] checks arity against the kernel's arity table and returns tyApp[name, args].";
typeArity::usage     = "typeArity[name] returns the arity of a type constructor; throws 'type' if unknown.";
boolTy::usage        = "boolTy — the built-in type tyApp[\"bool\", {}].";
indTy::usage         = "indTy — the built-in type tyApp[\"ind\", {}].";
tyFun::usage         = "tyFun[a, b] builds the function type a -> b = tyApp[\"fun\", {a, b}].";
mkConst::usage       = "mkConst[name, ty] returns const[name, ty] if ty is an instance of the kernel-registered generic type for name.";
constType::usage     = "constType[name] returns the kernel-registered generic type of a constant.";
listConstants::usage = "listConstants[] returns the sorted list of currently registered constant names.";
mkEq::usage          = "mkEq[s, t] builds the term (s = t) after checking typeOf[s] === typeOf[t].";

REFL::usage                = "REFL[t] — primitive. Produces ⊢ t = t.";
TRANS::usage               = "TRANS[thm1, thm2] — primitive. From ⊢ s = t and ⊢ t' = u with t ≡α t', produces ⊢ s = u.";
MKCOMB::usage             = "MKCOMB[thm1, thm2] — primitive. From ⊢ f = g and ⊢ x = y, produces ⊢ f x = g y.";
ABS::usage                 = "ABS[v, thm] — primitive. From ⊢ s = t with v not free in any hypothesis, produces ⊢ (λv.s) = (λv.t).";
BETA::usage                = "BETA[(λx.t) x] — primitive. Produces ⊢ (λx.t) x = t[x/binder].";
ASSUME::usage              = "ASSUME[p] — primitive. For p:bool, produces p ⊢ p.";
EQMP::usage               = "EQMP[thm1, thm2] — primitive. From ⊢ p = q and ⊢ p' with p' ≡α p, produces ⊢ q.";
DEDUCTANTISYM::usage = "DEDUCTANTISYM[thm1, thm2] — primitive. From Γ₁ ⊢ p and Γ₂ ⊢ q, produces (Γ₁\\{q}) ∪ (Γ₂\\{p}) ⊢ p = q.";
INST::usage                = "INST[theta, thm] — primitive. Applies a term substitution to hypotheses and conclusion.";
INSTTYPE::usage           = "INSTTYPE[theta, thm] — primitive. Applies a type substitution to every type annotation in the theorem.";

newConstant::usage              = "newConstant[name, ty] registers a fresh constant with the given generic type.";
newType::usage                  = "newType[name, arity] registers a fresh type constructor of the given arity.";
newDefinition::usage            = "newDefinition[var[c,ty] = rhs] registers c as a constant of type ty and returns ⊢ c = rhs. rhs must be closed and its type variables must be reflected in ty.";
newBasicTypeDefinition::usage = "newBasicTypeDefinition[tyname, absname, repname, thm] where thm is ⊢ P x. Introduces a new type together with abs/rep constants. Returns {absRepThm, repAbsThm}.";
newAxiom::usage                 = "newAxiom[p] — asserts p as an axiom (p must be :bool). After lockAxioms[] this throws.";
lockAxioms::usage                = "lockAxioms[] — closes the newAxiom intake after bootstrap. Subsequent calls to newAxiom throw.";

destThm::usage          = "destThm[th] returns {hyps, concl} of a theorem; throws otherwise.";
hyp::usage              = "hyp[th] returns the sorted hypothesis list of a theorem.";
concl::usage            = "concl[th] returns the conclusion of a theorem.";
isThm::usage            = "isThm[x] is True iff x is a theorem produced by the kernel.";
listAxioms::usage       = "listAxioms[] returns the list of terms posted through newAxiom (in order).";
listDefinitions::usage  = "listDefinitions[] returns the list of (c, rhs) pairs posted through newDefinition (in order).";

$HOLKernelABIVersion::usage  = "$HOLKernelABIVersion — integer, bumped when kernel internal representation changes in a way that invalidates Stable-mode snapshot files.";

(* Mode is read from `Global` $HOLEncapsulationMode` rather than from a *)
(* kernel-local symbol so the wolframscript driver can set it before    *)
(* this file is Get'd. Default is "Strict".                              *)

Begin["`Private`"];

(* ============================================================ *)
(* Pure helper functions (no kernel state — same in both modes) *)
(* ============================================================ *)

tyMatch[tyVar[n_String], target_, theta_Association] :=
  Module[{k = tyVar[n]},
    If[KeyExistsQ[theta, k],
      If[theta[k] === target, theta,
        HOL`Error`holError["term", "tyMatch: inconsistent binding",
          <|"var" -> k, "old" -> theta[k], "new" -> target|>]],
      Append[theta, k -> target]
    ]
  ];
tyMatch[tyApp[n_String, pArgs_List], tyApp[m_String, tArgs_List], theta_Association] :=
  If[n =!= m || Length[pArgs] =!= Length[tArgs],
    HOL`Error`holError["term", "tyMatch: type structure mismatch",
      <|"pattern" -> tyApp[n, pArgs], "target" -> tyApp[m, tArgs]|>],
    Fold[tyMatch[#2[[1]], #2[[2]], #1] &, theta, Transpose[{pArgs, tArgs}]]
  ];
tyMatch[p_, t_, _] :=
  HOL`Error`holError["term", "tyMatch: incompatible shapes",
    <|"pattern" -> p, "target" -> t|>];

destEq[comb[comb[const["=", _], s_], t_]] := {s, t};
destEq[other_] :=
  HOL`Error`holError["rule", "destEq: not an equation", <|"got" -> other|>];

normHyps[lst_] := SortBy[DeleteDuplicatesBy[lst, stripOrigin], stripOrigin];
mergeHyps[a_, b_] := normHyps[Join[a, b]];
removeHyp[hs_, p_] := Module[{ps = stripOrigin[p]}, Select[hs, stripOrigin[#] =!= ps &]];

hypContainsFree[hs_List, v_] := AnyTrue[hs, MemberQ[freesIn[#], v] &];

tyvarsInTerm[var[_, t_]] := tyvars[t];
tyvarsInTerm[bvar[_, t_]] := tyvars[t];
tyvarsInTerm[const[_, t_]] := tyvars[t];
tyvarsInTerm[comb[f_, x_]] := Union[tyvarsInTerm[f], tyvarsInTerm[x]];
tyvarsInTerm[abs[bv_, body_, _]] := Union[tyvarsInTerm[bv], tyvarsInTerm[body]];

betaSubst[bv : bvar[k_Integer, _], depth_Integer, rep_] :=
  If[k == depth, rep, bv];
betaSubst[v : var[_, _], _, _] := v;
betaSubst[c : const[_, _], _, _] := c;
betaSubst[comb[f_, x_], depth_, rep_] :=
  comb[betaSubst[f, depth, rep], betaSubst[x, depth, rep]];
betaSubst[abs[bv_, body_, o_], depth_, rep_] :=
  abs[bv, betaSubst[body, depth + 1, rep], o];

validateTypeName[n_String] /; StringLength[n] > 0 := Null;
validateTypeName[n_] :=
  HOL`Error`holError["kernel", "type name must be a nonempty string", <|"got" -> n|>];

(* ============================================================ *)
(* defineKernel — installs all public HOL`Kernel`* DownValues   *)
(* and the registerConst helper, parameterised over the 6       *)
(* state symbols. Called exactly once per session at boot time. *)
(* ============================================================ *)

(* HoldAll so the 6 state symbols are passed by NAME, not by their *)
(* OwnValues. The body then references the symbols directly, so    *)
(* `AppendTo[axiomList, p]` and `arityTable[name] = arity` mutate   *)
(* the actual symbol's OwnValue (works for both Associations and   *)
(* List symbols).                                                  *)
SetAttributes[defineKernel, HoldAll];
defineKernel[thmTag_, arityTable_, constTypeTable_,
             axiomList_, defnList_, axiomIntakeOpen_] := (

    registerConst[name_String, ty_] := (constTypeTable[name] = ty;);

    HOL`Kernel`typeArity[n_String] :=
      Lookup[arityTable, n,
        HOL`Error`holError["type", "typeArity: unknown type constructor", <|"name" -> n|>]];

    HOL`Kernel`mkType[n_String, args_List] :=
      Module[{ar},
        ar = Lookup[arityTable, n,
          HOL`Error`holError["type", "typeArity: unknown type constructor", <|"name" -> n|>]];
        If[Length[args] =!= ar,
          HOL`Error`holError["type", "mkType: arity mismatch",
            <|"name" -> n, "expected" -> ar, "got" -> Length[args]|>]];
        tyApp[n, args]
      ];
    HOL`Kernel`mkType[n_, args_] :=
      HOL`Error`holError["type", "mkType: bad arguments", <|"name" -> n, "args" -> args|>];

    HOL`Kernel`boolTy = tyApp["bool", {}];
    HOL`Kernel`indTy  = tyApp["ind",  {}];
    HOL`Kernel`tyFun[a_, b_] := HOL`Kernel`mkType["fun", {a, b}];

    HOL`Kernel`constType[name_String] :=
      Lookup[constTypeTable, name,
        HOL`Error`holError["term", "constType: unknown constant", <|"name" -> name|>]];

    HOL`Kernel`listConstants[] := Sort[Keys[constTypeTable]];

    HOL`Kernel`mkConst[name_String, ty_] :=
      Module[{gen},
        gen = HOL`Kernel`constType[name];
        tyMatch[gen, ty, <||>];
        const[name, ty]
      ];

    HOL`Kernel`mkEq[s_, t_] :=
      Module[{ty},
        ty = typeOf[s];
        If[ty =!= typeOf[t],
          HOL`Error`holError["term", "mkEq: type mismatch",
            <|"lhsType" -> ty, "rhsType" -> typeOf[t]|>]];
        comb[
          comb[
            HOL`Kernel`mkConst["=", tyApp["fun", {ty, tyApp["fun", {ty, tyApp["bool", {}]}]}]],
            s],
          t]
      ];

    HOL`Kernel`REFL[t_] := thmTag[{}, HOL`Kernel`mkEq[t, t]];

    HOL`Kernel`TRANS[a : thmTag[h1_List, c1_], b : thmTag[h2_List, c2_]] :=
      Module[{s, t1, t2, u},
        {s, t1} = destEq[c1];
        {t2, u} = destEq[c2];
        If[! aconv[t1, t2],
          HOL`Error`holError["rule", "TRANS: middle terms do not match",
            <|"mid1" -> t1, "mid2" -> t2|>]];
        thmTag[mergeHyps[h1, h2], HOL`Kernel`mkEq[s, u]]
      ];
    HOL`Kernel`TRANS[a_, b_] :=
      HOL`Error`holError["rule", "TRANS: arguments must be theorems", <|"arg1" -> a, "arg2" -> b|>];

    HOL`Kernel`MKCOMB[thmTag[h1_List, c1_], thmTag[h2_List, c2_]] :=
      Module[{f, g, x, y},
        {f, g} = destEq[c1];
        {x, y} = destEq[c2];
        thmTag[mergeHyps[h1, h2],
          HOL`Kernel`mkEq[HOL`Terms`mkComb[f, x], HOL`Terms`mkComb[g, y]]]
      ];
    HOL`Kernel`MKCOMB[a_, b_] :=
      HOL`Error`holError["rule", "MKCOMB: arguments must be theorems", <|"arg1" -> a, "arg2" -> b|>];

    HOL`Kernel`ABS[v : var[_String, _], thmTag[h_List, c_]] :=
      Module[{s, t},
        If[hypContainsFree[h, v],
          HOL`Error`holError["rule", "ABS: binder occurs free in hypotheses",
            <|"binder" -> v|>]];
        {s, t} = destEq[c];
        thmTag[h, HOL`Kernel`mkEq[HOL`Terms`mkAbs[v, s], HOL`Terms`mkAbs[v, t]]]
      ];
    HOL`Kernel`ABS[v_, th_] :=
      HOL`Error`holError["rule", "ABS: first arg must be a var, second a theorem",
        <|"v" -> v, "th" -> th|>];

    HOL`Kernel`BETA[redex : comb[abs[bvar[0, bty_], body_, origin_String],
                                 var[argname_String, aty_]]] /;
        argname === origin && bty === aty :=
      thmTag[{}, HOL`Kernel`mkEq[redex, betaSubst[body, 0, var[argname, aty]]]];
    HOL`Kernel`BETA[other_] :=
      HOL`Error`holError["rule", "BETA: not a trivial β-redex (binder/arg mismatch)",
        <|"got" -> other|>];

    HOL`Kernel`ASSUME[p_] :=
      (If[typeOf[p] =!= tyApp["bool", {}],
         HOL`Error`holError["rule", "ASSUME: term must have type bool",
           <|"got" -> typeOf[p]|>]];
       thmTag[{p}, p]);

    HOL`Kernel`EQMP[thmTag[h1_List, c1_], thmTag[h2_List, c2_]] :=
      Module[{p, q},
        {p, q} = destEq[c1];
        If[! aconv[p, c2],
          HOL`Error`holError["rule", "EQMP: equation LHS does not match second theorem",
            <|"eqLHS" -> p, "second" -> c2|>]];
        thmTag[mergeHyps[h1, h2], q]
      ];
    HOL`Kernel`EQMP[a_, b_] :=
      HOL`Error`holError["rule", "EQMP: arguments must be theorems", <|"arg1" -> a, "arg2" -> b|>];

    HOL`Kernel`DEDUCTANTISYM[thmTag[h1_List, c1_], thmTag[h2_List, c2_]] :=
      thmTag[
        normHyps[Join[removeHyp[h1, c2], removeHyp[h2, c1]]],
        HOL`Kernel`mkEq[c1, c2]
      ];
    HOL`Kernel`DEDUCTANTISYM[a_, b_] :=
      HOL`Error`holError["rule", "DEDUCTANTISYM: arguments must be theorems",
        <|"arg1" -> a, "arg2" -> b|>];

    HOL`Kernel`INST[theta_, thmTag[h_List, c_]] :=
      Module[{th = If[AssociationQ[theta], theta, Association[theta]]},
        thmTag[normHyps[vsubst[th, #] & /@ h], vsubst[th, c]]
      ];
    HOL`Kernel`INST[theta_, other_] :=
      HOL`Error`holError["rule", "INST: second arg must be a theorem", <|"got" -> other|>];

    HOL`Kernel`INSTTYPE[theta_, thmTag[h_List, c_]] :=
      Module[{th = If[AssociationQ[theta], theta, Association[theta]]},
        thmTag[normHyps[instType[th, #] & /@ h], instType[th, c]]
      ];
    HOL`Kernel`INSTTYPE[theta_, other_] :=
      HOL`Error`holError["rule", "INSTTYPE: second arg must be a theorem", <|"got" -> other|>];

    HOL`Kernel`destThm[thmTag[h_List, c_]] := {h, c};
    HOL`Kernel`destThm[other_] :=
      HOL`Error`holError["rule", "destThm: not a theorem", <|"got" -> other|>];

    HOL`Kernel`hyp[thmTag[h_List, _]] := h;
    HOL`Kernel`hyp[other_] :=
      HOL`Error`holError["rule", "hyp: not a theorem", <|"got" -> other|>];

    HOL`Kernel`concl[thmTag[_, c_]] := c;
    HOL`Kernel`concl[other_] :=
      HOL`Error`holError["rule", "concl: not a theorem", <|"got" -> other|>];

    HOL`Kernel`isThm[thmTag[_List, _]] := True;
    HOL`Kernel`isThm[_] := False;

    HOL`Kernel`newType[name_String, arity_Integer] :=
      (validateTypeName[name];
       If[KeyExistsQ[arityTable, name],
         HOL`Error`holError["kernel", "newType: already declared", <|"name" -> name|>]];
       If[arity < 0,
         HOL`Error`holError["kernel", "newType: arity must be ≥ 0", <|"arity" -> arity|>]];
       arityTable[name] = arity;);
    HOL`Kernel`newType[n_, a_] :=
      HOL`Error`holError["kernel", "newType: bad arguments", <|"name" -> n, "arity" -> a|>];

    HOL`Kernel`newConstant[name_String, ty_] :=
      (If[KeyExistsQ[constTypeTable, name],
         HOL`Error`holError["kernel", "newConstant: already declared", <|"name" -> name|>]];
       registerConst[name, ty];);
    HOL`Kernel`newConstant[n_, ty_] :=
      HOL`Error`holError["kernel", "newConstant: bad arguments", <|"name" -> n, "type" -> ty|>];

    HOL`Kernel`newDefinition[tm_] :=
      Module[{cvar, rhs, cname, cty, rty, cconst, rhsTyvars, ctyTyvars},
        If[! MatchQ[tm, comb[comb[const["=", _], var[_String, _]], _]],
          HOL`Error`holError["kernel", "newDefinition: expected `var = term`",
            <|"got" -> tm|>]];
        cvar = tm[[1, 2]];
        rhs  = tm[[2]];
        {cname, cty} = {cvar[[1]], cvar[[2]]};
        If[KeyExistsQ[constTypeTable, cname],
          HOL`Error`holError["kernel", "newDefinition: constant already declared",
            <|"name" -> cname|>]];
        rty = typeOf[rhs];
        If[cty =!= rty,
          HOL`Error`holError["kernel", "newDefinition: LHS/RHS type mismatch",
            <|"lhsType" -> cty, "rhsType" -> rty|>]];
        If[freesIn[rhs] =!= {},
          HOL`Error`holError["kernel", "newDefinition: RHS is not closed",
            <|"frees" -> freesIn[rhs]|>]];
        rhsTyvars = tyvarsInTerm[rhs];
        ctyTyvars = tyvars[cty];
        If[! SubsetQ[ctyTyvars, rhsTyvars],
          HOL`Error`holError["kernel", "newDefinition: RHS has type variables not reflected in constant type",
            <|"rhsTyvars" -> rhsTyvars, "ctyTyvars" -> ctyTyvars|>]];
        registerConst[cname, cty];
        AppendTo[defnList, {cname, rhs}];
        cconst = const[cname, cty];
        thmTag[{},
          comb[
            comb[const["=", tyApp["fun", {cty, tyApp["fun", {cty, tyApp["bool", {}]}]}]], cconst],
            rhs]]
      ];

    HOL`Kernel`newBasicTypeDefinition[tyname_String, absname_String, repname_String,
                                          thmTag[h_List, c_]] :=
      Module[{predicate, witness, rty, argTyvars, absTy, repTy,
              a, r, absConst, repConst, eq1, eq2},
        If[h =!= {},
          HOL`Error`holError["kernel", "newBasicTypeDefinition: hypotheses must be empty",
            <|"hyps" -> h|>]];
        If[! MatchQ[c, comb[_, _]],
          HOL`Error`holError["kernel", "newBasicTypeDefinition: conclusion must be P x",
            <|"got" -> c|>]];
        predicate = c[[1]];
        witness   = c[[2]];
        If[freesIn[predicate] =!= {},
          HOL`Error`holError["kernel", "newBasicTypeDefinition: predicate must be closed",
            <|"frees" -> freesIn[predicate]|>]];
        If[KeyExistsQ[arityTable, tyname],
          HOL`Error`holError["kernel", "newBasicTypeDefinition: type already declared",
            <|"name" -> tyname|>]];
        If[KeyExistsQ[constTypeTable, absname] || KeyExistsQ[constTypeTable, repname],
          HOL`Error`holError["kernel", "newBasicTypeDefinition: abs/rep name already used",
            <|"abs" -> absname, "rep" -> repname|>]];
        If[absname === repname,
          HOL`Error`holError["kernel", "newBasicTypeDefinition: abs and rep names must differ",
            <|"name" -> absname|>]];
        rty = typeOf[witness];
        argTyvars = Sort[tyvarsInTerm[predicate]];
        arityTable[tyname] = Length[argTyvars];
        Module[{newTy},
          newTy = tyApp[tyname, argTyvars];
          absTy = tyApp["fun", {rty, newTy}];
          repTy = tyApp["fun", {newTy, rty}];
          registerConst[absname, absTy];
          registerConst[repname, repTy];
          absConst = const[absname, absTy];
          repConst = const[repname, repTy];
          a = var["a", newTy];
          r = var["r", rty];
          eq1 = HOL`Kernel`mkEq[
                  HOL`Terms`mkComb[absConst, HOL`Terms`mkComb[repConst, a]],
                  a];
          eq2 = HOL`Kernel`mkEq[
                  HOL`Terms`mkComb[predicate, r],
                  HOL`Kernel`mkEq[
                    HOL`Terms`mkComb[repConst, HOL`Terms`mkComb[absConst, r]],
                    r]];
          {thmTag[{}, eq1], thmTag[{}, eq2]}
        ]
      ];
    HOL`Kernel`newBasicTypeDefinition[tyname_, absname_, repname_, th_] :=
      HOL`Error`holError["kernel", "newBasicTypeDefinition: bad arguments",
        <|"tyname" -> tyname, "absname" -> absname, "repname" -> repname, "thm" -> th|>];

    HOL`Kernel`newAxiom[p_] :=
      (If[! axiomIntakeOpen,
         HOL`Error`holError["kernel", "newAxiom: intake has been closed (post-bootstrap)",
           <|"attempt" -> p|>]];
       If[typeOf[p] =!= tyApp["bool", {}],
         HOL`Error`holError["rule", "newAxiom: term must have type bool",
           <|"got" -> typeOf[p]|>]];
       AppendTo[axiomList, p];
       thmTag[{}, p]);

    HOL`Kernel`lockAxioms[] := (axiomIntakeOpen = False;);

    HOL`Kernel`listAxioms[]      := axiomList;
    HOL`Kernel`listDefinitions[] := defnList;
  );

(* ============================================================ *)
(* Initialise state and install. Mode dispatch lives here.       *)
(* ============================================================ *)

If[!ValueQ[HOL`Kernel`$HOLKernelABIVersion],
  HOL`Kernel`$HOLKernelABIVersion = 1];

If[Global`$HOLEncapsulationMode === "Stable",
  (* ---- Stable: Private-context fixed symbols ---- *)
  HOL`Kernel`Private`holThmTag;   (* used as Head only; no OwnValue *)
  HOL`Kernel`Private`arityTable      = <|"bool" -> 0, "ind" -> 0, "fun" -> 2|>;
  HOL`Kernel`Private`constTypeTable  = <||>;
  HOL`Kernel`Private`axiomList       = {};
  HOL`Kernel`Private`defnList        = {};
  HOL`Kernel`Private`axiomIntakeOpen = True;
  With[{alpha = tyVar["a"]},
    HOL`Kernel`Private`constTypeTable["="] =
      tyApp["fun", {alpha, tyApp["fun", {alpha, tyApp["bool", {}]}]}]];
  defineKernel[
    HOL`Kernel`Private`holThmTag,
    HOL`Kernel`Private`arityTable,
    HOL`Kernel`Private`constTypeTable,
    HOL`Kernel`Private`axiomList,
    HOL`Kernel`Private`defnList,
    HOL`Kernel`Private`axiomIntakeOpen];
  ,
  (* ---- Strict (default): Module-local gensym symbols ---- *)
  Module[{thmTagL, arityTableL, constTypeTableL,
          axiomListL, defnListL, axiomIntakeOpenL},
    thmTagL          = Unique["thm$"];
    arityTableL      = <|"bool" -> 0, "ind" -> 0, "fun" -> 2|>;
    constTypeTableL  = <||>;
    axiomListL       = {};
    defnListL        = {};
    axiomIntakeOpenL = True;
    With[{alpha = tyVar["a"]},
      constTypeTableL["="] =
        tyApp["fun", {alpha, tyApp["fun", {alpha, tyApp["bool", {}]}]}]];
    defineKernel[thmTagL, arityTableL, constTypeTableL,
                 axiomListL, defnListL, axiomIntakeOpenL];
  ]
];

End[];
EndPackage[];
