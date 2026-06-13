# HOL-in-Mathematica：项目计划与架构设计

## 0. 一句话概括

用 Mathematica 的 `Module` + 闭包机制重建 LCF 哲学，实现一个可信核极小的高阶逻辑证明助手，风格上对标 HOL Light。

---

## 1. 项目愿景

构建一个在 notebook 里可交互的 HOL 证明助手，满足：

1. **可信核极小**：kernel 只有 10 条左右原始推理规则 + 几条公理 + 3~4 条定义机制。目标 500 行 Mathematica 代码以内。
2. **kernel 之外全部是不可信代码**：所有派生规则、tactic、自动化、parser、pretty printer 都可以任意写错，最坏情况是证不出定理，不会证出错误的定理。
3. **封装由语言机制承担**：`thm` 类型的不可伪造性由 `Module` 的 gensym 机制保证，而不是靠社会契约或约定。
4. **notebook 可运行（非富前端；2026-05 降级）**：notebook 里 `Get` / `Needs` 顶层包即可证明并以文本输出结果，与 `wolframscript` 等价。原计划的证明状态可视化 / 项与类型排版（M6b）已砍——只保留 demo `.nb` 跑标志性定理。
5. **脚本可检查**：kernel、派生规则、tactic 层不依赖 notebook；写好的证明脚本必须能通过 `wolframscript` 无交互跑通，成功退出码 0、失败非零。notebook 的可视化（MakeBoxes、goal 栈渲染）原本就是可选前端、不得进入可信核——现已整体砍掉（§7 M6b）。
6. **以 ℝ 的实数构造 + 点集拓扑作为 stdlib 的收官目标（2026-06-13 大幅收窄）**：发布范围收窄到 **ℝ 经 Dedekind 分割构造 + 序列理论 + 闭区间紧性 + 连通性 + 配套点集拓扑**，做完即宣告 stdlib 完成并发布 GitHub。**不做微积分**（连续 / 微分 / 黎曼积分 / Lebesgue 判据全部移出范围）。**为什么收窄**：(a) 本项目最初目的——验证 WL 的 `Module` 封装机制——已由 kernel + 数塔(到 ℝ-完备有序域) + 5 个自动化 tactic 充分达成；(b) 面向教学的全套数学分析已由隔壁 Lean 项目 `tautology` 承担（tactic + 广度，载体更合适）；(c) 本库另一现实角色是隔壁 `rum` 项目的检验器，它要的是稳定、测试充分、有代表性的 stdlib 表面，不要数学深度。**蓝本**：`tautology` 的 `RealTheory` 脊线是 0-sorry、纯 Lean Init、与本项目自底向上哲学一致的完整参考，逐文件作为 Codex brief 的证明骨架（见 §7 M8 + memory `reference-tautology-lean-blueprint`）。**已砍**：旧 M8 的微积分 + Lebesgue 判据、M9 多元 / Stokes、M10 Fourier / Radon，以及 RealTheory 中与分析脊线正交的部分——基数比较 / Cantor-Bernstein（拽进整套集合论地基）、无穷小数展开 / `0.999…=1`（服务于基数，叶子）、上下极限 limsup/liminf（喂级数判别法，本库不做级数）。路线详见 §7 M8。

参考系：HOL Light（John Harrison，OCaml）。它的 kernel 是已知最小、最清晰的 LCF 风格实现之一，Flyspeck 项目（Kepler 猜想形式化）就建立在它之上。

---

## 2. 设计哲学：LCF + 闭包封装

### 2.1 LCF 原则回顾

Milner 的 LCF（Logic for Computable Functions）引入了一个核心思想：**定理的有效性由抽象数据类型保证**。

- 类型 `thm` 是抽象的，外部代码拿不到它的构造器。
- 只有 kernel 模块内部定义的原始推理规则能产出 `thm` 值。
- 任何 `thm` 类型的值，按构造即为已证明的定理——这叫 **de Bruijn 准则**。

ML 语言本身就是为这个目的发明的。我们在 Wolfram 语言里复刻这一点。

### 2.2 用 Module 闭包充当抽象类型

Mathematica 没有静态类型系统，但有一个等价强度的机制：`Module` 的局部符号会被 gensym 成 `name$nnnn`，外部无法拼写出这个符号，因此：

```mathematica
holKernel = Module[{thmHead, mkThm, REFL, ...},
  (* thmHead 这个符号只有这个 Module 内部的代码知道 *)
  mkThm[hyps_, concl_] := thmHead[hyps, concl];

  REFL[t_] := mkThm[{}, mkEq[t, t]];
  ...

  <| "REFL" -> REFL, "concl" -> (#[[2]] &), ... |>
];
```

外部代码拿到的 `thm` 值形如 `thmHead$1234[{}, ...]`。想要伪造？你得先猜出 `$1234` 那个后缀，而这个数字取决于加载顺序，且在不同会话里不稳定。辅以 `Unique[]` 随机生成的头符号 + 放入私有 Context，基本可以阻止一切非恶意的误用。

### 2.3 与原教旨 LCF 的差别

- OCaml 的 `thm` 是**编译时**保证的不可伪造；我们是**运行时**依赖命名空间的不可伪造。安全性略弱，但足够。
- 不追求防御恶意攻击者。一个决心破坏的用户用 `Names[]`、`DownValues[]`、或者 `Language`FindSymbols` 总能找到内部符号。我们只防止无意的绕过。
- 如果将来要加强，可在 Association 里嵌入一个"签名"——每个 `thm` 自带一个只有 kernel 知道的随机 token，外部操作只在 token 匹配时生效。

---

## 3. 系统架构（分层）

```
┌─────────────────────────────────────────┐
│ Layer 5: 标准库                         │  ← 可信度同用户代码
│ (集合论、自然数、列表、实分析 ...)      │
├─────────────────────────────────────────┤
│ Layer 4: Tactic 层 / 目标栈             │  ← 不可信（错了证不出来）
├─────────────────────────────────────────┤
│ Layer 3: 派生规则                       │  ← 不可信
│ (CONJ, DISJ_CASES, GEN, SPEC, ...)      │
├─────────────────────────────────────────┤
│ Layer 2: 公理与定义机制                 │  ← 可信（写死在 kernel 里）
│ (INFINITY, SELECT, new_definition, ...) │
├─────────────────────────────────────────┤
│ Layer 1: 原始推理规则（10 条）          │  ← 可信核 ★
├─────────────────────────────────────────┤
│ Layer 0: 类型 + 项 + 良构检查           │  ← 可信核 ★
└─────────────────────────────────────────┘
```

星号标记的两层合在一起就是 kernel。我们的全部设计精力投入这里；其余一切都是外围。

**层间 bootstrap 依赖**：Layer 2 的公理（尤其 `INFINITY_AX`）陈述形式里要用到 `∃`、`∧`、`¬`、`ONE_ONE`、`ONTO`，而这些都是 Layer 4 通过 `new_definition` 引入的。所以启动顺序不是"自底向上一次过"，而是：

1. 建好 Layer 0-1（类型、项、10 条原始规则）
2. 用 `new_constant` / `new_definition` 引入 `T`、`∧`、`⇒`、`∀`、`∃`、`¬`、`ONE_ONE`、`ONTO` 等基础定义（跨到 Layer 4 的基础片段）
3. 回到 Layer 2，用 `new_axiom` 声明 `ETA_AX`、`SELECT_AX`、`INFINITY_AX`
4. 继续 Layer 4 其余派生规则和 Layer 5 标准库

`new_axiom` 本身属于 kernel（可信），但它是"真正的信任扩张点"——每次调用都要人工审查一致性。Bootstrap 脚本用它声明 3 条公理后，`new_axiom` 就不再出现在 Kernel Association 里，用户代码从此拿不到它。

横切关注点：parser / pretty printer / notebook UI 独立于这些层，不影响可信核。不过 printer 的正确性独立于 kernel 的 soundness——printer 把 `⊢ False` 错排成 `⊢ True` 不会让定理错，但会骗到读者，所以 printer 也要有回归测试。

---

## 4. 核心数据结构

### 4.1 类型（Layer 0）

HOL 的类型是一个简单的代数数据类型：

```
type ::= Tyvar of string                 (* 类型变量 'a, 'b *)
       | Tyapp of string * type list     (* 类型构造子应用，如 bool, num, 'a -> 'b *)
```

Mathematica 里用符号头表达：

```mathematica
tyVar["a"]                         (* 类型变量 *)
tyApp["bool", {}]                  (* 原子类型常量 *)
tyApp["fun", {tyApp["bool",{}], tyApp["bool",{}]}]   (* bool -> bool *)
```

内建类型常量从 `bool` 和 `ind`（个体，一个无限的论域）开始，函数类型 `fun` 也是内建的。其余都用 `new_type_definition` 机制在 kernel 外定义。

**kernel 需要的类型操作**：
- `mkVarType[name]`, `mkType[name, args]`
- `destVarType`, `destType`
- `typeSubst[theta, ty]` — 类型代换
- `tyvars[ty]` — 收集自由类型变量
- 相等性（结构相等）

### 4.2 项（Layer 0）

```
term ::= Var  of string * type
       | Const of string * type
       | Comb of term * term           (* 函数应用 f x *)
       | Abs  of term * term           (* λ-抽象，第一个参数必须是 Var *)
```

Mathematica 表示：

```mathematica
var["x", tyVar["a"]]
const["=", ... eq 的类型 ...]
comb[f, x]
abs[var["_b0", ty], body, "x"]     (* 第 3 个槽位：绑定变量的显示名 *)
```

**绑定变量的规范化**：为了让结构相等直接蕴含 α-等价，`mkAbs` 把绑定变量重命名为 `_b0, _b1, …`（按嵌套深度），原变量名保存在 `abs` 的第 3 个槽位（origin）供 pretty printer 恢复。外部 observer 解构时拿到的是规范形，printer 再用 origin 还原显示。这把"证明等价性"和"好看"解耦——`mkAbs["x", body_x]` 和 `mkAbs["y", body_y]`（body 结构对应）规范化后完全相等。

**良构约束**：
- `comb[f, x]` 要求 `typeOf[f]` 是 `a -> b` 形式，且 `typeOf[x] == a`。
- `abs[v, body, origin]` 要求第一个参数是 `var[...]`，第三个参数是原始名称字符串（仅用于显示）。
- **所有构造必须经过 smart constructor**，它们做类型检查和 α 规范化；原生 `comb[...]` / `abs[...]` 直接写出来不触发检查，但我们约定 kernel 之外代码不得绕过 `mkComb` / `mkAbs`。这和 HOL Light 的做法一致。

**kernel 需要的项操作**：
- 构造：`mkVar`, `mkConst`, `mkComb`, `mkAbs`（带类型检查）
- 解构：`destVar`, `destConst`, `destComb`, `destAbs`
- `typeOf[term]`
- `freesIn[term]` — 自由变量
- `vsubst[theta, term]` — 项代换（处理捕获）
- `instType[theta, term]` — 类型代换
- α 等价：用带变量捕获处理的代换 + 结构相等实现

变量表示方案选择命名变量 + 显式 α-变换，不用 de Bruijn。理由：调试和 pretty print 友好，性能不是核心目标。

### 4.3 定理（Layer 1）

```
thm = Sequent of term list * term       (* 假设集 ⊢ 结论 *)
```

Mathematica 里就是 `thmHead[hypList, conclTerm]`，其中 `thmHead` 是 kernel Module 的私有符号。

对外暴露：`hyp[th]`、`concl[th]`、`toString[th]`（用于 pretty print）。**不暴露构造器**。

---

## 5. 可信核：原始推理规则

HOL Light 的 10 条（略作符号调整）：

| 规则 | 含义 |
|------|------|
| `REFL t` | `⊢ t = t` |
| `TRANS th1 th2` | `Γ ⊢ s=t`, `Δ ⊢ t=u` ⟹ `Γ∪Δ ⊢ s=u` |
| `MK_COMB (th1, th2)` | `Γ ⊢ f=g`, `Δ ⊢ x=y` ⟹ `Γ∪Δ ⊢ f x = g y` |
| `ABS v th` | `Γ ⊢ s=t`（v 不在 Γ 自由出现）⟹ `Γ ⊢ (λv.s)=(λv.t)` |
| `BETA t` | `⊢ (λx.t) x = t` |
| `ASSUME t` | `{t} ⊢ t`（要求 t : bool） |
| `EQ_MP th1 th2` | `Γ ⊢ p=q`, `Δ ⊢ p` ⟹ `Γ∪Δ ⊢ q` |
| `DEDUCT_ANTISYM_RULE th1 th2` | `Γ ⊢ p`, `Δ ⊢ q` ⟹ `(Γ\{q})∪(Δ\{p}) ⊢ p=q` |
| `INST theta th` | 项变量代换 |
| `INST_TYPE theta th` | 类型变量代换 |

注意：HOL 里**等号是唯一的逻辑原语**。`⇒`、`∧`、`∨`、`¬`、`∀`、`∃` 全部由等号和 lambda 定义出来。比如：

- `T ≡ (λx:bool. x) = (λx:bool. x)`
- `∀ ≡ λP. P = (λx. T)`
- `∧ ≡ λp q. (λf. f p q) = (λf. f T T)`
- `⇒ ≡ λp q. (p ∧ q) = p`
- `¬ ≡ λp. p ⇒ F`

这些定义在 kernel 外用 `new_definition` 做即可。

### 公理

只有 3 条：
- **ETA_AX**：`⊢ (λx. t x) = t`
- **SELECT_AX**：`⊢ P x ⇒ P (@ P)`（Hilbert ε）
- **INFINITY_AX**：`⊢ ∃f:ind→ind. ONE_ONE f ∧ ¬ (ONTO f)`（保证 `ind` 无限）

注意 `INFINITY_AX` 陈述里 `∃`、`∧`、`¬`、`ONE_ONE`、`ONTO` 都不是 kernel 内建的——全是 `new_definition` 产物。所以 `INFINITY_AX` 不能在 kernel 加载最早期就声明，要等 bootstrap 阶段把这些定义完再 `new_axiom` 进来。详见 §3 的层间 bootstrap 顺序。

### 定义 / 扩展机制（kernel 里必须实现的扩展点）

- `new_constant[name, ty]` — 引入未定义常量（小心使用，信任扩张点）
- `new_definition[c = t]` — 常量定义：若 t 是闭项且类型相容，引入新常量 c，产出 `⊢ c = t`
- `new_basic_type_definition[...]` — 子类型定义，从已有类型切出子集构造新类型
- `new_axiom[t]` — 把一个 `: bool` 的闭项直接声明为公理，产出 `⊢ t`。**最强的信任扩张点**。Kernel 的 bootstrap 脚本用它声明 3 条公理后，就把 `new_axiom` 从 Kernel Association 里撤掉——用户代码从此没有入口调用它。

---

## 6. 封装机制的具体实现

Kernel 的骨架（伪代码）：

```mathematica
BeginPackage["HOL`Kernel`"];

(* 公开 API 的占位符 *)
Kernel::usage = "The HOL trusted kernel object.";

Begin["`Private`"];

makeKernel[] := Module[
  {
    (* --- 私有符号：thm 的唯一构造头 --- *)
    thmTag = Unique["thm$"],

    (* --- 可变状态（Module 局部变量；只有下面定义的闭包能读写） --- *)
    typeArityTable = <| "bool" -> 0, "ind" -> 0, "fun" -> 2 |>,
    constTypeTable = <| "=" -> (* generic α→α→bool *) ... |>,
    axiomList      = {},
    defnList       = {},

    (* --- 类型层操作 --- *)
    mkVarType, mkType, typeOf, typeSubst, ...,

    (* --- 项层操作 --- *)
    mkVar, mkConst, mkComb, mkAbs, vsubst, instType, ...,

    (* --- 原始规则 --- *)
    REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP,
    DEDUCT_ANTISYM_RULE, INST, INST_TYPE,

    (* --- 扩展机制（有些仅 bootstrap 期导出） --- *)
    newConstant, newDefinition, newBasicTypeDefinition, newAxiom,

    (* --- 内部 smart constructor（不导出！） --- *)
    mkThm
  },

  mkThm[hyps_List, concl_] := thmTag[Sort @ DeleteDuplicates @ hyps, concl];

  REFL[t_] := mkThm[{}, mkEq[t, t]];

  TRANS[th1_, th2_] := Module[{h1, c1, h2, c2, s, t1, t2, u},
    {h1, c1} = {th1[[1]], th1[[2]]};
    {h2, c2} = {th2[[1]], th2[[2]]};
    (* 检查 c1 形如 s=t1，c2 形如 t2=u，且 t1 等价 t2，然后... *)
    ...;
    mkThm[Union[h1, h2], mkEq[s, u]]
  ];

  (* ... 其余规则 ... *)

  (* 导出 Association *)
  <|
    "REFL"                 -> REFL,
    "TRANS"                -> TRANS,
    "MK_COMB"              -> MK_COMB,
    "ABS"                  -> ABS,
    "BETA"                 -> BETA,
    "ASSUME"               -> ASSUME,
    "EQ_MP"                -> EQ_MP,
    "DEDUCT_ANTISYM_RULE"  -> DEDUCT_ANTISYM_RULE,
    "INST"                 -> INST,
    "INST_TYPE"            -> INST_TYPE,

    (* 观察器 *)
    "concl"                -> (#[[2]] &),
    "hyp"                  -> (#[[1]] &),

    (* 类型/项构造器（这些本身不可信，但 kernel 只通过 thm 保证定理有效性）*)
    "mkVar"                -> mkVar,
    "mkConst"              -> mkConst,
    "mkComb"               -> mkComb,
    "mkAbs"                -> mkAbs,

    (* 公理和定义机制 *)
    "ETA_AX"               -> etaAxiomThm,
    "SELECT_AX"            -> selectAxiomThm,
    "INFINITY_AX"          -> infinityAxiomThm,
    "new_definition"       -> newDefinition,
    "new_basic_type_definition" -> newBasicTypeDefinition
  |>
];

Kernel = makeKernel[];

End[];
EndPackage[];
```

**关键点**：
- `thmTag` 用 `Unique` 生成，外部完全拿不到。
- `mkThm` 不在导出 Association 里，外部没有合法路径调用它。
- `hyp` 和 `concl` 用位置提取（`#[[1]]`、`#[[2]]`），所以即便外部知道 `thmTag`，观察器不依赖它——这让 observer 可以被 kernel 之外替换（pretty printer 等）而不破坏封装。

**加固选项**（视需要实施）：
1. `SetAttributes[Kernel, {Locked, ReadProtected}]`
2. 把 `thmTag` 做成双因子：`thmTag[secret][...]`，其中 `secret` 也是 gensym
3. 用 `System`Private`HoldEntry` 等机制进一步藏匿

**Kernel 是单例**：`Kernel = makeKernel[]` 在 package 加载时执行一次，产生唯一的 `thmTag` 和内部可变状态表。再次调用 `makeKernel[]` 会得到全新的 `thmTag`，旧 Kernel 产出的 `thm` 值对新 Kernel 不再可识别。**因此没有"reset kernel"的安全做法**——想清空状态就只能重启 `wolframscript` 会话。Bootstrap 序列（引入基础定义 + 三条 `new_axiom` 调用）由 Kernel 模块初始化代码一次性执行，对用户而言是原子动作；bootstrap 结束后，Kernel Association 把 `newAxiom` 撤出。

**状态变更 API 的约束**：`new_constant` / `new_definition` / `new_basic_type_definition` 修改 `typeArityTable` / `constTypeTable`、追加 `defnList`；`new_axiom` 追加 `axiomList`。这些是真正的副作用点，每一次调用都应在测试里捕获一次快照，作为"这个 session 引入了什么信任"的审计线索。

---

## 7. 开发路线图

建议以 7 个 milestone 推进。每个 milestone 产出一个可以在 notebook 里跑的 demo。

### M1：Types ✦ 第 1 周
- [x] 数据构造 `tyVar`, `tyApp`
- [x] 操作 `destVarType`, `destType`, `tyvars`, `typeSubst`
- [x] 内建 `bool`, `ind`, `fun` 并提供 `-->` 辅助构造器
- [x] 单元测试：类型等价性、代换、平凡性质

**验收**：能构造 `(α → β) → α → β` 并正确做代换。

### M2：Terms + 良构 ✦ 第 2 周
- [x] `var`, `bvar`, `const`, `comb`, `abs` 数据构造（free / bound 用结构上分离的 head）
- [x] Smart constructor `mkComb`, `mkAbs` 带类型检查
- [x] `typeOf`, `freesIn`, `vsubst`（带捕获避免），`instType`
- [x] α 等价（通过规范化实现）
- [x] 预注册常量：`=` : `α → α → bool`

**验收**：能构造 `λx:α. x` 并验证 `typeOf` 为 `α → α`；做捕获避免代换并通过测试。

### M3：可信核 ✦ 第 3–4 周
- [x] 10 条原始规则全部实现
- [x] `new_constant`、`new_definition`、`new_basic_type_definition`、`new_axiom`
- [x] Bootstrap 序列：定义 `T`、`∧`、`⇒`、`∀`、`∃`、`¬`、`ONE_ONE`、`ONTO`，然后 `new_axiom` 声明 `ETA_AX`、`SELECT_AX`、`INFINITY_AX`，最后把 `newAxiom` 从 Kernel Association 撤下
- [x] 完整的 Module 闭包封装 + 可变状态表（`typeArityTable` / `constTypeTable` / `axiomList` / `defnList`）
- [x] **反向测试**：尝试从外部直接构造 `thm` 应失败；尝试从外部访问 `new_axiom` 应失败

**验收**：
- 定义 `T`，证明 `⊢ T`（端到端跑通 `new_definition` → `REFL` → `SYM`（派生）→ `EQ_MP`）
- 定义 `∧`，证明 `⊢ T ∧ T`

**注**：`⊢ ∀x. x = x` 比想象中复杂，需要 `EQT_INTRO`、`GEN` 等派生规则配合量词 β-展开，留给 M4。

### M4：派生规则库 ✦ 第 5–6 周
在 kernel 之外实现，作为不可信但受信任的日常工具。

- [x] 布尔连接词全套：`CONJ`, `CONJUNCT1/2`, `DISJ1/2`, `DISJCASES`, `NOTINTRO`, `NOTELIM`, `CCONTR`（经典反证法）
- [x] 量词：`GEN`, `SPEC`, `EXISTS`, `CHOOSE`
- [x] 代换策略：`SUBS`（HOL Light literal-equality 语义：给一组等式 thm，把 conclusion 里 LHS 的所有出现一刀切替换成 RHS；不递归进已替换的子项，不对 LHS 自由变量做 unification）。**`SUBST` 暂未做**：HOL Light 的 `SUBST` 是模板驱动的精确位置替换——传 `(eqThm, holeMarker)` 列表加一个带 hole 占位变量的模板，只在模板标出的位置换。SUBS 是粗粒度全替换，SUBST 是细粒度按位置；95% 的需求 SUBS / `REWRITERULE` 就够，HOL Light 自己后期也很少直接用 SUBST。**约定**：碰到第一个真用得上 SUBST 的证明再补
- [x] 重写：`REWRCONV` + `ONCEREWRITERULE` + `REWRITERULE`
- [x] Conversion 组合子：`THENC`, `ORELSEC`, `TRYCONV`, `REPEATC`, `SUBCONV`, `DEPTHCONV`

**验收**：能一行证 `⊢ ∀x y. x = y ⇒ y = x`（对称性）。

### M5：Goal-oriented Tactic 层 ✦ 第 7–8 周
- [x] `goalstack` 对象（又一个 Module 闭包的应用！）`makeGoalstack[]` 返回 `{g, e, b, top, finished}` 闭包
- [x] 基础 tactic（camelCase——避免 `_` 被解析为 `Pattern`）：`conjTac`, `disj1Tac`/`disj2Tac`, `genTac`, `existsTac`, `dischTac`, `assumeTac`, `acceptTac`, `popAssum`, `rewriteTac`
- [x] Tactic 组合子（无下划线，可保留 ALL-CAPS）：`THEN`, `THENL`, `ORELSE`, `REPEAT`, `TRY`, `allTac`/`noTac`
- [x] `prove[term, tactic]` 高级接口
- [~] notebook 里的 goal 可视化（每一步当前目标与假设）—— **已随 M6b 砍掉**；开发时用 `makeGoalstack[]` / `tacResult` 文本打印目标栈即可

**验收**：用 tactic 风格证明一批经典命题逻辑等价式。

### M6：Parser + Pretty Printer ✦ 第 9 周

拆三个子里程碑。M6b 不阻塞 M7（wolframscript 不需要 notebook 渲染），可延后到任意空档。

**M6a — Pretty Printer（ASCII 输出 + 算符注册）**
- [x] 算符注册表：`{name → {fixity, prec, assoc, ascii, unicode}}`，普通 Association（**不进 kernel closure**——排版数据非 soundness-critical），bootstrap 时为内建算符（`=`, `∧`, `∨`, `⇒`, `¬`, `∀`, `∃`, `@`）注册；`λ` 无对应常量，硬编码于 walker
- [x] 单趟 render walk：以 `(ctxPrec, rightExt, nameStack, mode)` 作为下传上下文（实现上等价于 PLAN 原拟的 `term → printTree → String` 两段，但单趟更直观；括号决策和算符元数据在 `renderInfix/renderPrefix/renderApp/renderBinderChain` 各自分支内做）
- [x] 特殊形式逆识别：infix（`a = b`、`p ∧ q`、…）、prefix（`¬ p`）、binder chain（`∀x y z. body`、`λx. body`、`@x. P x`）
- [x] α-renaming for display：进入 `abs` 时维护"已用名"栈；origin 与栈或 body 自由变量撞名时加 `'` 后缀，反复直至唯一
- [x] ASCII / Unicode 双输出（`!`/`?`/`/\`/`\/`/`==>`/`~`/`\` vs `∀`/`∃`/`∧`/`∨`/`⇒`/`¬`/`λ`），默认 Unicode
- [x] `formatThm[th]` → `String`，`⊢ p` 或 `[h1; h2; …] ⊢ p`
- [x] 回归测试：每个内建算符 / 嵌套优先级 / binder 撞名场景（46 测试在 `tests/printer_tests.wl`）
- 已知简化：`=` 在 `bool` 类型上未特化为 `⇔`（HOL Light 把 iff 当作独立、更松的算符）；本期一律按 `=` 在 prec 28 渲染，可读但 `(p = q) ⇒ r` 之类的round-trip保真度要等 M6c parser + iff 特化时再补

**M6b — Notebook MakeBoxes（已砍 / CUT 2026-05）** —— 三项前端排版 / UI 全部取消（零能力损失，仅装修）：MakeBoxes thm 自动排版、term→Box 二维数学排版、Goalstack 可视化面板。理由：系统是纯 WL 包，notebook 里照常 `Get` / `Needs` 运行；Strict 下裸 thm 输出本就靠 `formatThm` 取字符串，自动排版收益不抵成本。
- [ ] **保留：demo `.nb`**（见 §8 `demos/`）—— 内容 = `Needs` 顶层包 → 证明并检查一个标志性定理（文本输出即可，具体定理待定），不依赖任何 MakeBoxes。

**M6c — Parser** ✅
- [x] Tokenizer：标识符、数字、算符、括号、冒号、点号、类型变量记号（ASCII alias `/\ \/ ==> ~ ! ? \ -> |-` → Unicode 在 `opCanon` 内一次映射）
- [x] Pratt parser（算符优先），消费 M6a 的算符注册表（`registeredInfixQ` / `registeredPrefixQ` 直接读 `lookupOperator`）
- [x] 类型推断（最小可用版的 W 算法）：原始 AST + Module 闭包内 `inferImpl` 收集约束 → `unify` 累积 σ → `applyToTerm` → `canonicalize`（自由变量按 name 共享 fresh tyvar，常量 `freshInstantiate` 每次调用独立泛化）
- [x] Binder 语法：`λx y z. body`、`∀x:α. body`、`∃x. body`（`expandBinder` 展开成嵌套 `rAbs` / `rApp[rConst[bs], rAbs[…]]`）
- [x] 类型标注：`(t : ty)`；类型变量 `'a` 语法（`α` 留待 M6b notebook 渲染）
- [x] **绝不调用 `ToExpression`**——纯字符串扫描 + 显式 AST
- [x] 回归测试：parse → print → parse 的 roundtrip 在内建算符全集上 aconv-守恒（`parser_tests.wl` 16 组共 70 断言；含 `tDef` capstone `T = (λx:bool. x) = (λx:bool. x)`）

**实现细节备忘**：
- `holError` 有 `HoldRest`，所以 message 参数里的 `<>` 字符串拼接会被 hold 住、不匹配 `_String` 模式、call 整个无声返回未求值。Parser.wl 内部凡需要拼接 message 的地方都用 `With[{msg = StringJoin[…]}, holError["parser", msg, …]]` 模式预先求值。
- `AssociationMap[(# -> f[#]) &, list]` 在 WL 里把右侧 lambda 当作 *value 构造器*，结果是 `<|k -> (k -> f[k])|>`（Rule 作为值）。要正确建表用 `Association[(# -> f[#]) & /@ list]`。M6c 实现里 `freshInstantiate` 和 `bindTyVar` 都踩过这个坑。

**验收**：`prove["∀ x y. x + y = y + x", ...]`（假设 `+` 已在某个加载的理论里定义）能跑通；M6a 的输出可以喂回 M6c 解析回同一个 term。

### M7：基础数据与数系 ✦ 18–25 周
数学库的底座，按学期工程量预算。原 5 周估计在我们决定走"传统 ℕ→ℤ→ℚ→ℝ + ~~Zorich 风格回切~~（已砍 2026-06）+ 任意整数底无穷小数 + 5 自动化决策过程"之后已不现实，整体扩张到一个学期级别的工程量。

**走向**：
- **教学路线**：杂糅——HOL 类型在底，集合论记号（`∈ ⊆ ∪ ∩ {x|P x}` 等）在表面；只在乘积类型 / 商类型 / 函数空间这三处让"类型 vs 集合"短暂浮现并明讲
- **数构造顺序**：ℕ → ℤ → ℚ → ℝ (**Dedekind 分割**)；序列在 ℝ 之后（Cauchy 序列要序列概念，序列又要 ℝ，所以 Cauchy 路线被教学顺序排除）
- **范畴性 / 多构造（支线）已砍（2026-06-13）**：ℝ 只做 **Dedekind 单一构造**，不做 Cauchy / Eudoxus 与 `ℝ_D≅ℝ_C` 等价、不做阀门室切换（检验器 / 封装验证只需一个典范 ℝ）。**Zorich 内蕴-ℕ 回切此前已砍（2026-06）**。
- **拓扑学**：**不在 M7 末尾打包引入**。开 / 闭 / 紧 / 连通在 M8 作为序列 / 极限工具逐个出现（与 Rudin / Zorich 一致）；全部走**确界 / 序列路线**，绕开可数性地基（见 M8）
- **决策过程实现**：从头写，充分利用 WL 语言特性。oracle + verifier 模式（用 `Resolve` / `Reduce` / `LinearProgramming` 当搜索 oracle 找证据，再让 tactic 通过 10 条原始规则验证），改写表用 `Dispatch` 编译，term bank 用 Association 索引——全部不进信任边界
- **Parser 扩展**：M7 一开始就在 parser 加 set-builder `{x | P x}` 语法（语义即 `λx. P x`，复用现有 binder 机器）。带表达式的 `{f x | P x}`（HOL Light 的 `GSPEC` 形式）等真用到时再补

**Phase 0 — 自动化底座** ~3 周

`auto/`，先于一切数学层。否则后面每个小定理都要手工 `THEN`-chain，效率不可接受。

- [ ] **M7-α / `auto/Meson.wl`** —— MESON：一阶 resolution + Skolemization + paramodulation + subsumption。capstone：propositional 与一阶定理一行 `MESON[]` prove
- [ ] **M7-β / `auto/Simp.wl`** —— SIMP：双向改写 + 条件改写 + congruence rules + 终止策略；改写规则集用 `Dispatch` 编译

**Phase 1 — 代数数据 + 集合记号** ~3 周

- [ ] **M7-1 / `stdlib/Pair.wl`、`Sum.wl`、`Option.wl`** —— 三个代数类型，全部 `new_basic_type_definition`。投影 / 构造子 / recursion principle / `MAP` / `CASE`
- [ ] **M7-2 / `stdlib/Set.wl`** —— 集合记号层，全是 `α → bool` 谓词上的 derived 记号：`IN` / `SUBSET` / `∪` / `∩` / `∖` / `∅` / `UNIV` / `POW` / 像 / 原象 / 有界量词 `∀x ∈ S` / 函数性质（单射 / 满射 / 双射 / 合成 / 恒等）
- [ ] **M7-2-parser** —— Parser 扩展 set-builder `{x | P x}` 语法
- [ ] **M7-γ / `auto/Set.wl`** —— SET 决策过程：集合代数恒等式专用 normalization + MESON 兜底。capstone：`S ∪ T = T ∪ S` 一行

**Phase 2 — 数构造** ~5–7 周

- [x] **M7-3 / `stdlib/Num.wl`**（最大块，原估 2–3 周，实际跨多个会话） —— 从 `ind` + `INFINITY_AX` 走 `IND_SUC` / `IND_0` / `NUM_REP` / `new_basic_type_definition` 经典路径；Peano 三件套；**迭代定理（非完整原始递归）**；`+ ×`、交换 / 结合 / 消去律；`≤ <`；强归纳 / 良序原理；带余除法；`^`；divides + DIV/MOD；gcd；prime + Euclid 引理。FTA（唯一分解）capstone 延后到 M7-4 之后（需要 list / finite 表达分解结构）。

  **子任务（实际实现，按字母顺序）：**
  - [x] **M7-3-a** — IND_SUC + IND_0 由 INFINITY_AX 经 Hilbert ε 提取；helper `selectOfExists[predLam, ∃-thm]`
  - [x] **M7-3-b** — NUM_REP 定义；`newBasicTypeDefinition` 切 num 类型；0 / SUC 定义
  - [x] **M7-3-c** — Peano 公理（SUC_NEQ_0、SUC_INJ、归纳定理）
  - [x] **M7-3-d** — **迭代定理** `⊢ ∀e f. ∃g. g 0 = e ∧ ∀n. g (SUC n) = f (g n)`（**走 iteration 而不是带 index 的完整 recursion**：iteration 对 `+`/`×`/`^` 足够，完整 recursion 留到第一个真正需要 index 的定理出现再做；范围比 HOL Light `num_RECURSION` 窄但够用）
  - [x] **M7-3-e** — `+` = `ITER m SUC`、`×` = `ITER 0 (λa. a + m)`；基本等式 + 左零律
  - [x] **M7-3-f** — `+` 的左后继、交换、结合律
  - [x] **M7-3-g** — `*` 的左后继、交换；`≤` 定义 `m ≤ n ⇔ ∃k. m + k = n` + reflexivity + zero-min
  - [x] **M7-3-h** — 加法 / 乘法消去律；乘法结合 / 分配律；`≤` 传递；`<` scaffolding
  - [x] **M7-3-i** — numCases + addEqZero（左右）+ LEQ 反对称 + LEQ 全序
  - [x] **M7-3-j** — strong induction + 序辅助（notLtZero / leqSucCase / ltSucEqLeq）
  - [x] **M7-3-k** — `^`（ITER 形式）+ 良序原理 + leqCaseEqLt + ltZeroNotZero
  - [x] **M7-3-l** — divisionThm `⊢ ∀m n. ¬(n=0) ⇒ ∃q r. m = n*q + r ∧ r < n`（强归纳 + leqTotal 两路分案）
  - [x] **M7-3-m** — divides + DIV + MOD（DIV/MOD 由 divisionThm 经 selectAx 抽出），divisionPairThm
  - [x] **M7-3-n** — divides 算术：refl / zero / add / multRight / addRight（addRight 经 multAddCancel 辅助归纳）
  - [x] **M7-3-o** — gcd 由唯一性属性 + Hilbert ε 定义；存在性 gcdExistsThm 由 Euclid 算法经强归纳证；gcdSpecThm 派生三性质（divides-left/right/universal）
  - [x] **M7-3-p** — prime 定义 `prime p ⇔ SUC 0 < p ∧ ∀d. d|p ⇒ d = SUC 0 ∨ d = p`；helper 三件套（oneTimesEq / sucNotEqSelf / ltImpliesNotEq）+ dividesLeqThm
  - [x] **M7-3-q** — Euclid 引理 `⊢ ∀p a b. prime p ⇒ p|a*b ⇒ p|a ∨ p|b`（强归纳 + 两路 DIV 分案 + r=0 / r>0 子分案，**不用整数 Bezout**）
  - **FTA 唯一分解** — 延后到 M7-4 之后（list / 有限重数函数表达分解需要 `stdlib/List.wl` 或 `Finite.wl` 才自然）
- [x] **M7-4 / `stdlib/List.wl`、`Finite.wl`** — list 类型 + `HD` / `TL` / `CONS` / `APPEND` / `LENGTH` / `MAP` / `FILTER` / `FOLD`；`FINITE S ↔ ∃l. ∀x. x ∈ S ↔ MEM x l`；基数 `CARD`；有限和 `∑`
- [x] **M7-δ / `auto/Arith.wl`** —— ℕ 上线性算术决策，**实现为 oracle（Fourier–Motzkin，精确有理）+ kernel verifier（Farkas 乘子拼 `+`/`≤` 单调性引理）**，非内部 Cooper QE（Cooper 线 2026-05-28 砍，-∞ 在 ℕ 上不成立）。∃-SAT 走见证搜索 + ground 验证；∀/UNSAT 走 Farkas。原子抽象处理非线性 `m*n`、`LENGTH l` 等。capstone：`∀m n p. m≤n ⇒ m+p≤n+p`
- [x] **M7-5 / `stdlib/Int.wl`** —— **底层走典范代表路线**：`num × num` 上的 `λp. FST p = 0 ∨ SND p = 0` 谓词切 `int` 类型；操作（+, ×, -, |·|）做完 pair-运算后 canonicalize 回典范型；环结构 + 序 + `&_ℤ : num → int` 嵌入。**工作语言层派生 Grothendieck/双向归纳视角**：定义 `intSucc = (+1)`、`intNeg = (0-·)`，导出 `(intNeg ∘ intSucc)² = id` 等代数关系；导出双向归纳定理 `⊢ P 0 ∧ (∀z. P z ⇒ P (intSucc z) ∧ P (intSucc⁻¹ z)) ⇒ ∀z. P z`，作为后续用 ℤ 时的首选证明工具——后续证明在 ℤ 上看不到 pair 结构。**为什么不直接走 K_0 商类型**：HOL 无原生商，set-of-pair 切多一层；为什么不直接 Peano-style 公理化 ℤ（S/N + 双向归纳作公理）：bootstrap 后 `newAxiom` 锁死，必须构造模型，模型成本和典范代表一致或更高，且 ℤ-递归原理多一个"S 与 S⁻¹ 互逆"的一致性义务。
  **DONE 2026-05-31**（stages a–h + 消去律）：carve + `&ℤ` 嵌入 + neg/succ/pred + 加法 abelian 群（comm/assoc/identity/inverse）+ 交换环（comm/distrib/assoc）+ 无零因子 `intMulEqZeroThm` + 乘法消去 `intMulCancelThm` + 线序 `intLe`/`intLt`（refl/antisym/trans/total）+ 加法/取负/按非负乘单调 + `&ℤ` 环/序嵌入同态 + `intAbs` + 双向归纳 `intInductionThm`。Grothendieck 等价层（`canonEquiv`/`canonInj`/`canonRespects`）是 add-assoc/distrib/mul-assoc 良定义性的共用桥；dihedral `RSR=S⁻¹`（`intNegSuccThm`）恰好用于双向归纳的负向下降步。ARITH 经 FST/SND 原子抽象自动处理大量 num 重排。
- [ ] **M7-6 / `stdlib/Rat.wl`**（1 周）—— `int × int*` 商；域结构、序、`&_ℚ : int → rat` 嵌入；ℚ 在自身稠密

**Phase 3 — 实数 + 序列收敛** ~7–9 周

- [ ] **M7-7 / `stdlib/Real/` 主体**（**文件夹**，按 §8.1 新原则；3–4 周）—— Dedekind 分割：**单下集** `L : ℚ→bool`，谓词四条 **非空 ∧ 真（上有界）∧ 向下封闭（严格 <）∧ 无最大元（开）**；"无最大元"是 canonicalizer ⟹ 每实数唯一对应一个 L ⟹ **kernel `=` 即实数相等、无 setoid**（延续 Int/Rat 规范代表主线）。`new_basic_type_definition` 切 `real`；加法（cut 加）、**乘法（Rudin 附录 sign-case：正 cut 上先定义、按符号延拓）**、序（包含）；`&ℝ : rat→real` 嵌入（复合得 ℕ/ℤ ↪ ℝ）；**完备性（sup）构造直给**；Archimedean；ℚ 稠密；nth roots 存在；`√2∈ℝ`、`√2∉ℚ`。文件：`Cut.wl` / `RatAux.wl` / `Field.wl` / `Mul.wl` / `Complete.wl` / `Roots.wl`
  - **`realInv`（乘法逆）✅ 完成 2026-06-09（cold Strict run_all 2200/0）—— ℝ 是域** —— `Real/Inv.wl`，**无 Lean 蓝本**（sibling 项目从未做倒数），从零按 Rudin "Principles" Step 8 写。正核心 `invPos`（cut body `{p | ∃w. ¬REP_x w ∧ 0<w ∧ p·w<1}`）+ `invPosCutIsCutThm`（四条，`0<x` 下）+ `invPosNonnegThm`；硬定理 **`invPosMulThm`（`0<x⇒x·(1/x)=1`，~250 行，Archimedean/`cutStraddle` ⊇ 向，gap`<s₀(1−r)` 使边界比 `y/(y+gap)>r`，witness `(y, t∈(r/y,1/(y+gap)))`）**；符号封装 `realInv`=`COND(0<x)(invPos x)(−invPos(−x))` + `realMulInvThm`（`¬(x=0)⇒x·(1/x)=1`，用 `realMulNeg` 符号同态把 `x<0` 归约到 `0<−x` 核心）。用户定的次序是"先逆元再相容"。实现要点见 memory `project_real_construction`。
  - **有序域 ×/≤ 相容 ✅ 完成 2026-06-10（cold Strict run_all 2212/0）** —— 加法-序 `realLe/LtAddMonoThm`（`realLeAddMono` 是纯 cut 包含 `a⊆b⟹(a+c)⊆(b+c)`）+ 桥接 `realLeSubNonnegThm`（`a≤b⟺0≤b−a`）/`realLtSubPosThm`；乘法-序 `realLeMulMonoThm`（`0≤c⇒a≤b⇒c·a≤c·b`，经桥接归约到 `0≤c·(b−a)=c·b−c·a`，用 distrib+符号积）/`realLtMulMonoThm`。全部放 Mul.wl 末尾"有序域出口"区。
  - **Stage E `&ℝ` 环/序同态 ✅ 完成 2026-06-10（cold Strict run_all 2220/0）—— ℚ↪ℝ 子环/子序嵌入** —— `realOfRatAddThm`（成员级 `r<a+b⟺∃s.s<a∧r−s<b`，density 中点）+ `realOfRatNegThm`（加法逆唯一性消去）+ 非负核心 `realOfRatNnMulThm`（bwd `r<ab⟹∃p<a,q<b,…` 双重 density + ℚ 逆元消去）+ 带符号 `realOfRatMulThm`（4 符号情形 + 新 ℚ 乘-负引理 `ratMulNeg{R,L}`/`ratMulNegNeg`）；`realOfRatLeThm` 已在 Field。坑：`ratNegNegThm` 是 RatAux(Real) 符号不是 `HOL\`Stdlib\`Rat\``，错上下文 SPEC 返回未求值 →"concl: not a theorem"。
  - **GRADUATION ✅ 2026-06-10 —— ℝ 有序域主体完成**：`stdlib/Real/{Cut,RatAux,Field,Mul,Inv}.wl` 全部折叠进 `bootstrap.mx`（加进 `build_snapshot.wls` libs、冷重建），不再是 frontier → `run_fast real` 可用、未来 Real 文件（Complete/Roots/Seq）的 dev 循环含完整有序域。**至此 ℝ = 加法阿贝尔群 + 交换幺环（带符号分配律）+ 域（乘法逆）+ 线性序 + ×/≤ 与 +/≤ 相容 + ℚ 环/序嵌入。**
  - **`Complete.wl`（Dedekind 完备性 + Archimedean + ℚ 稠密）✅ 完成 2026-06-10（cold Strict run_all 2250/0；dev 全回归 2179/0）—— ℝ 是完备有序域** —— `realSup S = ABS_real (λq. ∃a. S a ∧ REP_real a q)`（成员下集之**并**，Lean 蓝本 `Cut/Sup.lean` 直译——蓝本里这是最干净的一个文件）。`supCutIsCutThm`（`(∃a. S a) ⇒ (∃u. ∀a. S a ⇒ a≤u) ⇒ IS_CUT`：c1 取成员的成员、c2 取上界 cut 外一点（包含性反推矛盾）、c3/c4 从 CHOOSE 出的成员 cut 继承）+ 条件式 `repRealSupThm`/`realSupMemThm`；`realSupUpperThm`（`L_a ⊆ ∪`）/`realSupLeastThm`（每点经某 `L_a ⊆ L_v`）/打包 **`dedekindCompleteThm`**。**Archimedean 链**：`realRatBoundThm`（`∀x.∃q. x<&ℝq`——properness 点 `q0∉L_x` 抬 `1+q0`，`q0` 见证非包含）→ `realArchThm`（`∀x.∃n. x<&ℝ(&ℚ(&ℤn))`，接 RatAux 的 `ratArchThm` + 严格传递）。**`realDenseThm`**（`x<y ⇒ ∃q. x<&ℝq ∧ &ℝq<y`：`notLeWitnessThm` 给分离点 `qDe∈L_y∖L_x`，开性 bump 到 `rDe∈L_y`、`qDe<rDe`；左严格由 `qDe` 见证非包含，右严格由 `rDe∈L_y` + `ratLtIrrefl` 杀 `L_y⊆L_{&ℝrDe}`——**不需要第三次开性**）。顺带补齐实数严格序词汇 `realLtImpLeThm`/`realLtLeTransThm`/`realLeLtTransThm`/`realLtTransThm` + 严格序嵌入 `realOfRatLtThm`。新测试 `tests/real_complete_tests.wl`（30 断言）。**零调试一次通过**（两条 hygiene 规则的直接收益：`chooseBody` 从 kernel BETACONV 提取 CHOOSE 假设体、见证一律独特名 `aN/qN/uW/bW/aP/qD/rD/aD/qO/aO/rO/qDe/rDe`）。**NEXT：`auto/RealArith.wl`（M7-ε REAL_ARITH）→ Seq；`Roots.wl`（nth roots、√2）可在 REAL_ARITH 后回补。**
  - **Stage D `realMul` ✅ 完成 2026-06-09（Layers 1+2，cold Strict run_all 2181/0）** —— 交付清单全齐：非负核心 `realNnMul` + L2 带符号 `realMul`（嵌套 `COND` 二分）、`realMul{Comm,Assoc,One,Zero,Distrib}Thm`、`realLeMulNonnegThm`、`realLtMulPosThm`，**含完整 `realMulDistribThm`（带符号分配律，Lean 蓝本唯一缺口、本阶段唯一无参考一步，已证）**。实现要点见下与 memory `project_real_construction`。下面是当时（2026-06-07）的架构设计，已照此落地：
  - **Stage D `realMul` 架构（2026-06-07 定，吸收 GPT-5.5 评估 + `../archive/tautology` Lean 复盘）** —— 乘法是数系塔最硬一阶段，**独立成 `Real/Mul.wl`**（不再追加进 Field.wl，隔离失败定位）；前置先把 Field.wl 里 parked 的 ℚ/ℤ 辅助抽进 `Real/RatAux.wl`（先于 Mul 加载）。三层设计：
    1. **非负核心 `realNnMul`** —— cut body `{r | r<0 ∨ ∃p q. REP_real x p ∧ REP_real y q ∧ 0<p ∧ 0<q ∧ r<p·q}`。**用严格 `<` 而非 Lean 的 `≤`**：Lean `t ≤ p·q` 迫使 open/no-max 证明分出 `t=p·q` 边界并用 `a.no_max` 把 p 抬到 p′（`Cut/Mul.lean` 108–127）；严格 `<` 让 open 退化成纯 density（`ratDenseThm`）。`r<0` 析取项必需（`x=0` 时正积分支落空，靠它仍给出 0 的 cut）。bounded/proper 硬点：非负 cut 仍可能 =0（={r<0}，无正元），Lean 用 `ua' = if 0<ua then ua else 0` 钳到非负再取 `ua'·ub'+1` 作上界（`Cut/Mul.lean` 26–73）→ HOL 用 COND。**所有语义定理强制 `0≤x ∧ 0≤y` 前提、命名带 `Nonneg`、绝不公开无条件版**（无条件分配律是假的：`x,y>0, z<0, y+z<0` 时 `realNnMul x (y+z)=0 ≠ x·y`）。
    2. **符号封装 `realMul`** —— `COND` 按 `0≤x`/`0≤y` **二分**（零自然落入非负分支），NOT 零/正/负三分支。Lean 的三分支 `mul` 把 `mul_assoc` 退化成 3×3×3=27 例 ~93 行手写树（`Cut/MulComm.lean`）——本项目用二分（2×2×2）消去重复分支框架。不引入 `realNonneg` 谓词（Lean 里 `nonneg` 与 `0≤` 即便定义相等仍并存徒增桥接），规范用 `realLe realZero x`。**落地修正（2026-06-09）：** 统一框架不是固定元数的 `realMulSignCases`（各定理的 realMul 子项形状不同，难以统一签名），而是一个二元 `splitSign[t, posFn, negFn]`（EM+DISJCASES 原子），comm/zero/one 直接嵌套它即可；assoc/distrib 则用 **符号同态** `realMulNegLeft`/`realMulNegRight`（`x·(−y)=−(x·y)`，无条件）把负号全部拉到外层，从而把整证归约到已证的非负律——assoc 走"逐符号剥离"递归到 `assocCore`，distrib 走 `distribNonnegX`（0≤x 时对 y,z,(y+z) 分情形）再剥离 `x<0`。这比预想的 `realMulSignCases` 更省、定位更清晰。
    3. **抽象有序域出口** —— `realMul{Comm,Assoc,One,Zero,Distrib}Thm` + `realLeMulNonnegThm`/`realLtMulPosThm`；下游与 REAL_ARITH 只消费这层，不碰 `REP_real`/cut。
    - **Lean 蓝本状态：** 旧记录"Mul.lean BROKEN/无蓝本"是当时的**正确时点快照**（那时乘法尚未写）；该 Lean 项目后来补全了乘法 —— `../archive/tautology` 的 Mul/MulComm/MulDistrib/Sup **无 sorry/admit/axiom，是可用蓝本**：非负核心、带符号 comm/one/assoc、**非负**分配律（`mul_nonneg_add`，⊇ 向需 `nonneg b,c` + 60 行 aux `mul_nonneg_add_ge_aux`）、Dedekind 完备性（`Sup.lean`，供 `Complete.wl` 参考）全部证完。**唯一缺口 = 带符号（一般 cut）分配律** —— Lean 停在非负版没抬升，这是 Stage D 唯一无参考、最难的一步，**交付标准必须含完整 `realMulDistribThm`**。可直接搬的 cut 引理：`exists_pos_of_zero_lt`（0<a⟹∃正元，= GPT 的 `realPosHasPositiveMemThm`）、`exists_gt_both`（两元有公共上界元，分配律 ⊇ 向要用）。
    - **该 Lean 项目为何被放弃（真正的教训，比"缺口在哪"更重要）：** 它是一次对写它的 agent 的能力测试，顺带替我们趟雷；乘法**能证完**，但**前期规划错误（零/正/负三分支 + 无统一 sign-case 消去器 + 有理代数全内联无 RatAux 窄接口）让后期工作量与 token 成本爆炸到超出预算而被弃**。所以本阶段的三层 + 二分 + `realMulSignCases` + 先抽 `RatAux.wl` 不是洁癖，是直接针对这个失败模式的对冲：把复杂度钉在非负核心、用二分把分支树从 3ⁿ 压到 2ⁿ、用 helper 消去重复框架、把有理序/乘法代数前置成稳定入口。
- ~~**M7-7-Zorich**（Zorich 回切：is_nat/is_int/is_rat 谓词 + 归纳集刻画）~~ **砍掉 2026-06**：自底向上构造下 ℕ/ℤ/ℚ 已是类型、`&ℝ` 嵌入像即"ℝ 里的 ℕ/ℤ/ℚ"；归纳集刻画只在抽象范畴性里划算（已排除），且学生初学体会不到价值。两个具体构造等价所需的"嵌入在同构下相容"(`φ∘ι_D = ι_C`) 走一条 ~5 行抽象归纳即可，不碰构造内部、不需谓词。详见 §8.1 与 memory。
- [x] **M7-ε / `auto/RealArith.wl` ✅ 完成 2026-06-11**（实际 1 天，3 个 Codex briefs 005–007 全程外包实现，Claude 架构+验收；冷 Strict run_all 2432/0，已 GRADUATED 进 bootstrap.mx）—— ℝ 线性算术决策：精确 Fourier–Motzkin oracle（严格性追踪 + 乘子证书，非 `Resolve`/`LinearProgramming`）+ Farkas kernel verifier，类比 ARITH。三层：rnum ground 字面量层（同态链上提）→ 证明性规范化（`realLinNormConv` 带符号标准型 + `realAtomNormConv` ×LCD 清分母 + 负部平衡 → 非负 ℕ 系数原子）→ intake/oracle/重放（`realArithProve` + `REALARITH[]` tactic；HOL Light 名 REAL_ARITH 含下划线非法 WL 符号）。**capstone 已证：`∀ a b : ℝ. a < b ⇒ a < (a + b) / 2`**（prover + tactic 双形态）。细节：PROGRESS.md M7-ε 节 + commits 5a988f6/1c2860a/61fa8a7。
- [ ] **M7-8 / `Real/Seq.wl`**（2 周；放 `Real/` 内——螺旋式上升、不追 mathlib 泛化，以后 ℝⁿ / 函数空间各有自己的 seq）—— 序列 `ℕ → ℝ`；ε-N 极限；单调收敛（从 sup）；子列；Bolzano-Weierstrass；Cauchy 列 + **Cauchy 完备性（定理）**
- [ ] **M7-7-cat / `Real/Cauchy.wl`** 〔支线，**非 M8 关键路径**，排在 Seq 之后〕—— 构造 ℝ_Cauchy（有理 Cauchy 列 mod 零列，**全塔第一次真·商 / setoid**——建可复用的"商掉等价"机器：等价类 / 良定义性 / 商上运算 lift）；证 `ℝ_Dedekind ≅ ℝ_Cauchy`（序域同构）；嵌入相容 `φ∘ι_D = ι_C`（~5 行归纳，不碰构造内部）。**Eudoxus（HOL Light 一步到位 ℝ，致敬）待定**：复用同一商机器则便宜、否则贵，届时按工作量定
- [ ] **M7-9 / `Real/Decimal.wl`** 〔支线，教学，**非关键路径**，排在级数机器之后〕—— 数位抽取（floor/Archimedean）；任意底 `b ≥ 2` 展开存在 + 唯一（尾 `(b-1)` / 尾 `0` 二义 caveat）；**有理 ⟺ 最终循环（鸽笼）+ 等比级数（逆向）——零数论，不碰 Fermat/Euler**；**`0.999… = 1`**（等比级数，教学驱动）；（可选）Cantor 对角线 `|ℕ| < |ℝ|`

**M7 capstone**：
- **大 capstone**：`⊢ ∀ S : real → bool. S ≠ ∅ ∧ (∃ b. ∀ x ∈ S. x ≤ b) ⇒ ∃ s. is_sup S s`（确界原理，`dedekindCompleteThm`，已完成）
- **桥接 M8**：`⊢ ∀ a : ℕ → ℝ. Cauchy a ⇒ ∃ L. tendsto a L`（柯西完备性，M8 序列 Stage 5；见下）
- ~~教学 capstone（无穷小数展开唯一性）~~ **砍（2026-06-13）**：无穷小数移出范围（服务于已砍的基数比较）

---

### M8：ℝ 的序列理论 + 闭区间紧性 + 连通性 + 配套点集拓扑 —— stdlib 收官（2026-06-13 重定范围）
**本项目当前且最终的 stdlib 发布目标（做完即宣告 stdlib 完成并发布 GitHub）。** 全程在 `stdlib/Real/` 文件夹内（与已完成的 ℝ-完备有序域共享 context），经 **Dedekind 分割**单一构造（不做 Cauchy / Eudoxus 多构造与阀门室切换），蓝本为 `tautology` 的 `RealTheory` 脊线（0-sorry，逐文件作为 Codex brief 骨架）。**不做微积分。** 不给周估计，以阶段结算。

**贯穿原则——绕开可数性地基。** 全部 capstone 都走 **确界原理 / 序列路线**，不碰 `CountableSet` / 第二可数 / Lindelöf。其直接后果：闭区间 Heine–Borel 走**确界原理 + 勒贝格延拓法**（`{x : [a,x] 可被有限覆盖}` 取确界、证确界 = b），**不走** 区间套 + 二分；并放弃"ℝ 不可数"与"`0.999…=1`"两个会拽进集合论地基的 capstone。

#### M8.1 序列（`Real/Seq.wl`）—— 进行中
- [x] `tendsto`（实 ε、关系式）+ 极限演算（常数 / 唯一 / 和 / 负 / 差）、`convergent`（Stage 1，brief-008）
- [x] `eventually` 组合子 + 收敛 ⇒ 有界 + 远离零 + 绝对值乘法 + 乘积 / 数乘极限律（Stage 2，briefs 009/010）
- [ ] **确界 ⇒ 单调收敛**（`dedekindCompleteThm` → 单调有界收敛；蓝本 `RealSequence/Principles/FromSupMonotone.lean`）（Stage 3）
- [ ] **子列 + Bolzano–Weierstrass**（Peak / 上升指标 → 单调子列 → 单调收敛；蓝本 `RealSequence/Subsequence.lean`）（Stage 4）
- [ ] **柯西准则**（Cauchy ⇒ 收敛，M7 桥接 capstone `⊢ ∀a. Cauchy a ⇒ ∃L. tendsto a L`；蓝本 `RealSequence/Principles/FromSupCauchy.lean`）（Stage 5）
- 完成后 `Seq.wl` 毕业进 `bootstrap.mx`

#### M8.2 闭区间紧性（确界原理路线）
- [ ] 列紧性、聚点紧性（Bolzano–Weierstrass 的集合版）
- [ ] **Heine–Borel**：`[a,b]` 的任意开覆盖有有限子覆盖（确界 + 勒贝格延拓法）
- [ ] **勒贝格数引理**（紧覆盖的勒贝格数；与已砍的测度-Lebesgue 判据是拓扑表亲，同名不同物）
- 蓝本 `RealCompactness/ClosedInterval/{Statements,FromSup*,SeqTo*,...}.lean`（取 `FromSup*` 路线，跳过 Lindelöf / 可数子覆盖文件）

#### M8.3 连通性（核心）
- [ ] connected ⟺ 区间；介值定理味道的核心结论
- 蓝本 `RealConnectedness/Connected.lean`（跳过 `OpenDecomposition` / `ConnectedComponents`——开集 = 可数区间并需要可数性）

#### M8.4 配套点集拓扑（供上面用的基础）
- [ ] 开 / 闭 / 闭包 / 内部 / 子空间（`RealTopology/{Basic,Closed,Intervals,Subspace,...}.lean` 中**不依赖可数基**的部分；跳过 `RationalBasis` / `Lindelof`）

**M8 capstone（一组够得着的经典定理，取代旧的遥远 Lebesgue 判据）：**
- 单调有界收敛定理
- **柯西完备性** `⊢ ∀a. Cauchy a ⇒ ∃L. tendsto a L`
- **Bolzano–Weierstrass**
- **Heine–Borel**（闭区间）+ 勒贝格数引理
- 连通性 / 介值定理

**验收 + 收官**：以上证出后，宣告 stdlib 完成，整理发布到 GitHub。

---

### 已砍范围（2026-06-13 重定）

- ~~**M8 微积分**：连续 / 一致连续 / 微分 / 中值定理 / Taylor / 黎曼积分 / FTC / Lebesgue 零测 / 可积判据~~ —— 全部移出。黎曼积分 + 测度零集既遥远又无蓝本（tautology 也停在 RealTheory 前），不在收窄后的范围内。
- ~~**M9 多元分析 → 一般 Stokes**~~ —— 整体砍。
- ~~**M10 函数项级数 / 含参积分 / Fourier / Poisson 求和 / Radon 反演**~~ —— 整体砍。
- **RealTheory 中与分析脊线正交的部分**：~~基数比较 / Cantor-Bernstein / 连续统~~（拽进 `Foundation/Cardinal` 整套集合论地基，~3000 行正交工程）、~~无穷小数展开 / `0.999…=1`~~（服务于基数，叶子）、~~limsup / liminf~~（喂级数判别法，本库不做级数）、~~开集 = 可数区间并 / Lindelöf / 第二可数~~（需可数性地基，Heine–Borel 改走确界路线绕开）。

---

## 8. 文件与 Package 组织

```
HOL/
├── Kernel.wl               (* Layer 0-1-2，封装 Module *)
├── Basics.wl               (* 对 kernel 的薄封装 + 常用辅助 *)
├── Bool.wl                 (* ∧ ∨ ¬ ∀ ∃ 定义 + 派生规则 *)
├── Equal.wl                (* SYM, TRANS 风格派生 *)
├── Drule.wl                (* 更多派生规则、Conversion *)
├── Tactics.wl              (* Tactic 组合子、goalstack *)
├── Parser.wl               (* 字符串 parser *)
├── Printer.wl              (* Pretty printer + MakeBoxes *)
│
├── auto/                   (* 通用自动化（M7 一起建成） *)
│   ├── Meson.wl            (* MESON_TAC：一阶搜索 *)
│   ├── Simp.wl             (* SIMP_TAC：条件重写 *)
│   ├── SetTac.wl           (* SET_TAC *)
│   ├── Arith.wl            (* ARITH_TAC *)
│   └── RealArith.wl        (* REAL_ARITH / REAL_FIELD *)
│
├── stdlib/                 (* M7：基础数据与数系 *)
│   ├── Pair.wl
│   ├── Sum.wl
│   ├── Option.wl
│   ├── Set.wl              (* α→bool 编码 *)
│   ├── Num.wl              (* 自然数 *)
│   ├── Int.wl
│   ├── Rat.wl
│   ├── Real/               (* M7-7+：文件夹（§8.1）。Dedekind 构造主体 + Seq + Cauchy 等价支线 + Decimal 支线 *)
│   │   ├── Cut.wl          (* 单下集切割 + 序（规范，无 setoid） *)
│   │   ├── Field.wl        (* 加 / 乘（Rudin sign-case）/ &ℝ 嵌入 *)
│   │   ├── Complete.wl     (* sup 完备性 / Archimedean / ℚ 稠密 *)
│   │   ├── Roots.wl        (* nth roots / √2 *)
│   │   ├── Seq.wl          (* 序列 ℕ→ℝ、极限、B-W、Cauchy 完备性 *)
│   │   ├── Cauchy.wl       (* 支线：ℝ_Cauchy 商构造 + Dedekind≅Cauchy *)
│   │   └── Decimal.wl      (* 支线：无穷小数 / 0.999…=1 / 鸽笼，零数论 *)
│   ├── List.wl
│   ├── Finite.wl           (* 有限集、∑ / ∏ 记号 *)
│   └── Complex.wl          (* 可选 *)
│
│   └── Real/               (* M7 ℝ-完备有序域 + M8 序列 / 拓扑 / 紧性 / 连通 *)
│       ├── Cut.wl  RatAux.wl  Field.wl  Mul.wl  Inv.wl   (* M7：ℝ 构造 *)
│       ├── Complete.wl  Abs.wl  MinMax.wl              (* M7：完备性 / |·| / max-min *)
│       ├── Seq.wl         (* M8.1：tendsto、极限演算、单调收敛、子列、柯西 *)
│       ├── Compact.wl     (* M8.2：列紧 / 聚点 / Heine–Borel（确界路线）/ 勒贝格数 *)
│       ├── Connected.wl   (* M8.3：connected ⟺ 区间、介值 *)
│       └── Topology.wl    (* M8.4：开 / 闭 / 闭包 / 内部 / 子空间（不依赖可数基）*)
│       (* auto/RealArith.wl（M7-ε REAL_ARITH）在 auto/ 下，stdlib/Real 之后加载 *)
│       (* 文件可随规模再细分子文件夹；analysis2/3 已砍，不再有 *)
│
├── tests/
│   ├── harness.wl
│   ├── run_all.wls         (* cold Strict 全回归，权威门禁 *)
│   ├── run_all_stable.wls  run_fast.wls  dev.wls  (extend|build)_snapshot.wls
│   └── *_tests.wl          (* kernel / bool / real / real_seq / ... *)
│
└── demos/
    ├── 01-first-proof.nb
    ├── 02-bool-algebra.nb
    └── 03-nat-arithmetic.nb
```

所有加载后，用户在 notebook 里：

```mathematica
<< HOL`

prove[
  "!x y. x /\\ y ==> y /\\ x",
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [
    MATCH_ACCEPT_TAC CONJUNCT2,
    MATCH_ACCEPT_TAC CONJUNCT1
  ]
]
(* 输出：⊢ ∀x y. x ∧ y ⇒ y ∧ x *)
```

---

### 8.1 大文件拆分与可重构性原则（2026-06 立；自 M8 / ℝ 起实行，既有里程碑不回溯）

**背景教训.** 把一个里程碑的数千行代码堆进单一 `.wl` 文件，开发期顺手，但边界判断一旦需要修正（而边界**必然**随新出现的下游消费者而变），重构代价逼近重写——2026-06 把 Rat 携带的 ℕ/int 引理 + Num 的整除性理论重新归位，耗费数个计费时段、超过当初构造 Rat 本身的开销。根因**不是**"当年边界没规划好"（无法未卜先知），而是**架构没有廉价的迁移单元**。结论：架构必须把**可迁移 / 可重构**当作一等属性，目标是让**边界改起来便宜**，而非赌"接口一次设计到位"。

**原则（自 ℝ 起）：**

1. **里程碑 = 文件夹，而非单文件。** 例 `stdlib/Real/`，而非 `stdlib/Real.wl`。

2. **按内部依赖树切，不线性切。** 每个小文件 = 一个相对独立的"定义 / 引理闭包"，有明确的 **exports（接口）** 与 **imports（依赖）**；切分点选在依赖树的自然关节（一组会被一起消费、一起搬动的定理），不机械地一引理一文件。

3. **词汇集中化（比拆文件更关键的配套铁律）。** term-builder / unfold / 小工具这类私有词汇**集中定义、共享**，严禁每文件重定义——否则拆文件只是把"词汇孤岛"从 1 个变成 N 个，跨文件搬运照样要逐处桥接（这正是上次最大的时间黑洞）。两层做法：
   - **里程碑内**：文件夹下各小文件**共享同一个 package context**（都 `BeginPackage["HOL`Stdlib`Real`"]` → `Begin["`Private`"]`），于是 private 符号天然跨文件共享（`HOL`Stdlib`Real`Private`*`），里程碑内部重组无词汇成本。
   - **跨里程碑**：公共 term-builder 收进一个 stdlib 级共享词汇模块，所有 stdlib 文件 import；杜绝 `timesTm` vs `timesN` vs `timesConst` 这类同义异名。

4. **接口只为已知依赖设计，不为未来消费者过度设计。** 押注"可变性"而非"预见性"：边界变了能廉价挪 > 接口完美到不用改（后者正是已被否定的未卜先知）。

5. **granularity 有甜点，勿过碎。** WL 每文件一套 `BeginPackage` / import / 三处 runner 的 load list 都要维护；拆太碎会放大这部分开销。

6. **（已实现 2026-06-04，与拆分正交）增量 / 前沿快照。** WL 是解释型，拆文件**不自动**带来增量编译红利——冷启动仍重证整个世界。落地的是「前沿基线」工作流（比全分层链更简，granularity 甜点）：`bootstrap.mx` = **当前冻结基线** = `build_snapshot.wls` load list 里的文件。开发新文件时把它**留在 list 外**，用 **`tests/dev.wls <frontier.wl> [pat…]`** 迭代——restore 基线 + 只在其上 `Get` 前沿文件 + 跑测试（~0.1s vs ~7min 冷重建；除点名的前沿文件外仍对所有源做过期检查）。文件毕业后加进三个 runner 的 list，再用 **`tests/extend_snapshot.wls <file.wl>`** 把它增量折进 `bootstrap.mx`（~0.2s，不冷重建）。全量 **`tests/build_snapshot.wls`**（可选 `<uptoPattern>` 部分构建 + 逐文件计时）只在**上游改动**或要干净权威基线时跑。dev/extend 同 run_fast 是 Stable 模式（抓逻辑错，抓不住 Strict gensym/加载顺序）⟹ **每阶段权威门槛仍是冷 Strict `run_all`**，并周期性用全量 `build_snapshot` 重定基线（增量快照可能与冷建差几 KB）。实测：前 7 个文件(到 Bool)冷加载仅 0.2s，408s 几乎全在 FTA/Num/Int/Rat 等大 stdlib 文件——印证分层切点应放数系边界。详见 memory `snapshot_frontier_dev_loop`。

7. **不回溯拆分既有里程碑。** Num / Int / Rat / FTA 维持单文件现状；本原则自 M8 / ℝ 起实行。

---

## 9. 测试策略

三层测试：

### 9.1 单元测试（逐文件）
用 `MUnit` 或自己搓个极简 `assert` 宏。每个导出函数至少覆盖：正常路径 + 1 个边界 + 1 个错误输入。

### 9.2 封装测试（关键！）
专门测试封装不被绕过：

- 构造一个 `thm` 合法值，取 `Head`，尝试用这个 head 手搓一个"假定理"——应该要么失败、要么能被检测到。
- 若采用 token 加固方案，则测试无 token 的伪造不被任何 observer 接受。

### 9.3 证明回归测试
经典测试集（HOL Light 的 `basic_tests.ml` 思路）：

- Drinker's paradox: `⊢ ∃x. P x ⇒ ∀y. P y`
- 德摩根律全套
- 选择公理的几个等价形式
- 皮尔斯定律
- 自然数归纳原理使用示例

这些既是 regression，也是文档。

---

## 10. 关键风险与取舍

### 10.1 性能
Mathematica 的符号处理原生是慢的，尤其频繁 `Replace` / `Cases`。而数学库的规模一旦推进到 M8 以后，绝大部分运行时间都在重写和一阶搜索上——性能不再只是 nice-to-have。

- **缓解**：项的规范化（α-normal form）缓存；假设集合用排序不变式下的 `merge` 维护（而非 `Sort + DeleteDuplicates`，后者每次 O(n log n)）；`thm` 不变，可随意共享；常用改写规则网建 discrimination net 索引。
- **目标**：不追求 HOL Light 的绝对数量级，但要达到**实用级**——数学库回归套件（M7 起累计）在合理时间（数分钟量级）内跑完。若 M8 之后某个 tactic 成为瓶颈，就用 Mathematica 的底层模式匹配（`MatchQ`、`Replace` 的 `Heads -> True` 形式、`Dispatch`）替换 pure-LCF 的朴素版本。

#### 10.1.1 持久化基础设施（M7-3 期间引入）

M7-3 推进到 stdlib/Num.wl 时，每次 wolframscript 冷启动需要重新加载所有库 + 触发 Bootstrap，耗时 ~135s。预测 M10 时累计冷启动 2–3 分钟，调试不可忍受。**对策：开关式 kernel encapsulation + DumpSave 快照。**

- **`$HOLEncapsulationMode = "Strict" | "Stable"`**（Kernel.wl 顶部读取）：
  - `"Strict"`（默认，CI / audit 用）：原设计——`Module` 闭包 + `Unique["thm$"]` gensym，保留"防君子"的不可访问性。
  - `"Stable"`（dev 迭代 + 持久化用）：状态符号改为 `HOL`Kernel`Private`{holThmTag, arityTable, ...}` 固定名。trust boundary 改由 *convention + lint* 保证。
- **`tests/build_snapshot.wls`**：Stable 模式冷启动一次 → `DumpSave["bootstrap.mx", contexts]`。~135s 一次性成本。
- **`tests/run_fast.wls [pattern...]`**：restore 快照 + 重设 `$ContextPath` + 跑匹配的测试文件。**针对单模块（如 `num`）跑 ~3s**；跳过 `kernel_tests.wl`（其 pre-bootstrap state 在快照后不可重放）。
- **`tests/lint_private.wls`**：扫描所有 `.wl` / `.wls`，禁止 `Kernel.wl` 之外引用 `HOL`Kernel`Private`*`。
- **CI 矩阵**：两条独立流水线——`tests/run_all.wls`（Strict）和 `tests/run_all_stable.wls`（Stable）。两边都必须通过全量（当前 1817）且通过数一致。一旦 Stable 行为偏离 Strict，视为回归。

**性能效果**：M7-3-f / -g 阶段一次内层调整 3s 反馈，相比冷启动 135–390s 快 50–100×。M8+ 项目规模翻倍以后，这套基础设施会更值。

**设计目标 #0 的修订**：CLAUDE.md trust-boundary 第 0 条原话"closure-based encapsulation 提供 true inaccessibility"是过度承诺——WL 的 introspection 能力（`Names["*"]`、context backtick path）使任何 Module gensym 都可枚举可寻址。修订后的 #0 把保护机制从"gensym 不可猜"降级为"context discipline + review + lint"，但 Strict 模式作为最高约束的 ground truth 保留并在 CI 中持续审计。详见 CLAUDE.md。

### 10.2 等价性检查
HOL 里 α-等价应该是自动的。我们用命名变量，所以要么每次比较都 α-正规化，要么在构造时就规范化。

- **推荐**：`mkAbs` 构造时把绑定变量按深度重命名为 `_b0, _b1, …`（de Bruijn 风味但保留名字）。这样结构相等即 α 等价。真实名字用 origin 字段保留给 printer。

### 10.3 类型多态 vs 依赖类型
HOL 是**秩 1 多态**（let-polymorphism 风格但只在常量层面）。不要试图加依赖类型——那会变成另一个项目（CIC），前面讨论过这不是 Mathematica 的舒适区。

### 10.4 可信核边界
哪些东西属于"可信"？下面这些**必须**在 kernel 里：
- 10 条原始规则
- 3 条公理
- `new_definition` 系列
- 类型与项的 smart constructor（因为 kernel 规则依赖其类型保证）
- α-等价判断

其他一切（pretty printer、parser、tactic、决策过程、重写引擎）都**不得**有能力伪造 `thm`。

---

## 11. 第一周具体任务（给 Claude Code 的 kickoff）

**先把工具链定下来**（省得每个 milestone 重新想）：
- **测试框架**：自搓 ~30 行 `assertEq[actual, expected]` / `assertThrows[expr, tag]` / `runTests[...]`，放 `tests/harness.wl`。`wolframscript tests/run_all.wl` 退出码非零即失败。
- **错误策略**：kernel 内部用 `Throw[Failure["HOLError", <|"tag" -> ..., "msg" -> ...|>], holErrorTag]`，顶层 `Catch` 捕获。测试里用 `assertThrows` 按 tag 校验。不用 `Message` + `$Failed`——无法区分失败类型。
- **Context 布局**：`HOL`Kernel``、`HOL`Bool``、…，每个 `.wl` 文件 `BeginPackage` / `EndPackage`；私有辅助放 `` `Private` `` 子 context。

按顺序执行，每步提交一个可运行的 Mathematica 文件：

1. **`Kernel.wl` 骨架**
   - 建立 `HOL`Kernel`` package
   - 先只暴露 `Kernel["mkVarType"]`, `Kernel["mkType"]`, `Kernel["destType"]`, `Kernel["tyvars"]`, `Kernel["typeSubst"]`
   - 在 `tests/type_tests.wt` 里写 10 条测试

2. **扩充到 Terms**
   - 加 `mkVar`, `mkConst`, `mkComb`, `mkAbs`（带类型检查）
   - `typeOf`, `freesIn`, `vsubst`（正确处理捕获！这是最容易出 bug 的地方，必须有 α-renaming）
   - 测试：构造 Church numerals 的 `λf x. f (f x)` 并检查类型

3. **α-等价的规范化**
   - 实现 `alphaNormalize`，绑定变量重编号
   - 让所有 smart constructor 输出规范形

4. **第一条原始规则 REFL + 观察器**
   - 暴露 `Kernel["REFL"]`, `Kernel["concl"]`, `Kernel["hyp"]`
   - 跑一遍：`Kernel["REFL"][someTerm]` 然后 `Kernel["concl"][%]`
   - 验证：外部无法直接构造 `thmTag[...]`

此时我们已经有了一个玩具 LCF 系统的骨架，可以演示封装机制真的 work。后续按 §7 的 roadmap 推进。

---

## 12. 参考资料

**主要**：
- John Harrison, *HOL Light Tutorial* — <https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf>
- HOL Light 源码，尤其 `fusion.ml`（kernel，几百行）
- Harrison, *Handbook of Practical Logic and Automated Reasoning*（Cambridge, 2009）— 第 6 章讲 LCF 风格实现

**次要**：
- Gordon, Milner, Wadsworth, *Edinburgh LCF* (1979) — 历史文献
- Thomas Hales, *Flyspeck Project* 报告 — 说明这个小核真的撑得起大证明
- Paulson, *The Foundation of a Generic Theorem Prover* (1989) — Isabelle/Pure 的 kernel 讨论

**Mathematica 侧**：
- Wolfram Documentation 里 `Module`、`Unique`、`Context`、`BeginPackage` 的权威说明
- 任何关于 "wolfram language oop" 的讨论帖都可以快速扫一眼，但主要靠自己的设计

---

## 附录 A：第一个真定理的完整证明草图

M3 的端到端 demo 目标是 `⊢ T`（**不是** `⊢ ∀x. x = x`）。

```
1. new_definition[ T = ((λx:bool. x) = (λx:bool. x)) ]
                                      ⟹  ⊢ T = ((λx:bool. x) = (λx:bool. x))   -- th_def

2. REFL (λx:bool. x)                 ⊢ (λx:bool. x) = (λx:bool. x)              -- th_refl

3. SYM th_def                        ⊢ ((λx:bool. x) = (λx:bool. x)) = T
   (SYM 是 TRANS + REFL 的小派生，M3 要顺带写出来)

4. EQ_MP (3) (2)                     ⊢ T                                        ✓
```

注意即使是最简单的 `⊢ T`，也需要一步 `SYM` 派生——所以 §7 M3 的验收只要求到 `⊢ T` 和 `⊢ T ∧ T`，而把 `⊢ ∀x. x = x` 推到 M4：后者需要 `EQT_INTRO`（`⊢ p ⇔ (p = T)`）、`GEN`、量词 β-展开配合，整条链路比一个入门 demo 该有的长度长得多。

---

## 附录 B：成功的判据

项目按阶段设三档判据，每档达到就有对应的对外叙事。

### 第零档：Kernel + 封装（完成 M1–M6）
- ✅ kernel 500 行内，所有原始规则都有注释说明其逻辑内容
- ✅ 封装测试通过：外部代码无法伪造 `thm`，也无法调用撤下的 `new_axiom`
- ✅ 能跑完至少一个小理论（布尔代数的 20 条定理）
- ✅ 有一个 5 分钟的 demo notebook，让一个不懂 HOL 的 Mathematica 用户能看懂在干什么
- ✅ 能讲清楚"为什么这个设计有意思"：LCF 哲学 + Mathematica 的 Module 机制恰好承担了 OCaml 抽象类型的角色

➡️ 够写 blog / 小论文。

### 第一档（最终发布档）：ℝ 序列 + 紧性 + 连通 + 拓扑（完成 M8 = stdlib 收官）
- ✅ `real` 构造完成（Dedekind 单一构造），完备有序域全部定理可被自动化证出
- ✅ `REALARITH` / `MESON` / `SIMP` / `SET` / `ARITH` 均已可用
- [ ] 序列：单调有界收敛、柯西完备性、Bolzano–Weierstrass
- [ ] 闭区间 Heine–Borel（确界 + 勒贝格延拓法）+ 勒贝格数引理
- [ ] 连通 ⟺ 区间、介值定理
- ✅ 回归套件在 `wolframscript` 下数分钟内（cold Strict）/ 秒级（dev / run_fast）跑完

➡️ 够做一门"形式化实分析基础"小课程的配套工具，或写 blog / 上 arXiv；也作为隔壁 `rum` 项目的检验器底座。**做完即宣告 stdlib 完成并发布 GitHub。**

### ~~第二 / 三档：多元分析（M9）/ Fourier + Radon（M10）~~ —— 已砍（2026-06-13）
教学全分析目标移交隔壁 Lean 项目 `tautology`；本项目不再追多元 / Stokes / Fourier / Radon。