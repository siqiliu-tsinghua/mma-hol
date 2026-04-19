# HOL-in-Mathematica：项目计划与架构设计

## 0. 一句话概括

用 Mathematica 的 `Module` + 闭包机制重建 LCF 哲学，实现一个可信核极小的高阶逻辑证明助手，风格上对标 HOL Light。

---

## 1. 项目愿景

构建一个在 notebook 里可交互的 HOL 证明助手，满足：

1. **可信核极小**：kernel 只有 10 条左右原始推理规则 + 几条公理 + 3~4 条定义机制。目标 500 行 Mathematica 代码以内。
2. **kernel 之外全部是不可信代码**：所有派生规则、tactic、自动化、parser、pretty printer 都可以任意写错，最坏情况是证不出定理，不会证出错误的定理。
3. **封装由语言机制承担**：`thm` 类型的不可伪造性由 `Module` 的 gensym 机制保证，而不是靠社会契约或约定。
4. **notebook 友好**：证明状态可视化、项与类型可排版、tactic 可一步步展开观察。
5. **脚本可检查**：kernel、派生规则、tactic 层不依赖 notebook；写好的证明脚本必须能通过 `wolframscript` 无交互跑通，成功退出码 0、失败非零。notebook 的可视化（MakeBoxes、goal 栈渲染）是可选前端，不得进入可信核。
6. **面向本科分析课程的形式化库**：长期目标是把本科数学分析的主干内容机械化到可实用的程度——一元分析推进到黎曼积分的 Lebesgue 可积性判据；多元部分覆盖重积分换元法与欧氏空间带边子流形上的一般 Stokes 公式；Fourier 分析覆盖三类收敛定理（点态 / 一致 / 均方），以 **Poisson 求和公式**与 **Radon 变换反演**（CT 重建的数学原理）作为压轴应用。全程保持在**黎曼积分 + 零测集**框架内，不引入完整勒贝格测度。路线详见 §7 M7–M10。

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
- [ ] 数据构造 `tyVar`, `tyApp`
- [ ] 操作 `destVarType`, `destType`, `tyvars`, `typeSubst`
- [ ] 内建 `bool`, `ind`, `fun` 并提供 `-->` 辅助构造器
- [ ] 单元测试：类型等价性、代换、平凡性质

**验收**：能构造 `(α → β) → α → β` 并正确做代换。

### M2：Terms + 良构 ✦ 第 2 周
- [ ] `var`, `const`, `comb`, `abs` 数据构造
- [ ] Smart constructor `mkComb`, `mkAbs` 带类型检查
- [ ] `typeOf`, `freesIn`, `vsubst`（带捕获避免），`instType`
- [ ] α 等价（通过规范化实现）
- [ ] 预注册常量：`=` : `α → α → bool`

**验收**：能构造 `λx:α. x` 并验证 `typeOf` 为 `α → α`；做捕获避免代换并通过测试。

### M3：可信核 ✦ 第 3–4 周
- [ ] 10 条原始规则全部实现
- [ ] `new_constant`、`new_definition`、`new_basic_type_definition`、`new_axiom`
- [ ] Bootstrap 序列：定义 `T`、`∧`、`⇒`、`∀`、`∃`、`¬`、`ONE_ONE`、`ONTO`，然后 `new_axiom` 声明 `ETA_AX`、`SELECT_AX`、`INFINITY_AX`，最后把 `newAxiom` 从 Kernel Association 撤下
- [ ] 完整的 Module 闭包封装 + 可变状态表（`typeArityTable` / `constTypeTable` / `axiomList` / `defnList`）
- [ ] **反向测试**：尝试从外部直接构造 `thm` 应失败；尝试从外部访问 `new_axiom` 应失败

**验收**：
- 定义 `T`，证明 `⊢ T`（端到端跑通 `new_definition` → `REFL` → `SYM`（派生）→ `EQ_MP`）
- 定义 `∧`，证明 `⊢ T ∧ T`

**注**：`⊢ ∀x. x = x` 比想象中复杂，需要 `EQT_INTRO`、`GEN` 等派生规则配合量词 β-展开，留给 M4。

### M4：派生规则库 ✦ 第 5–6 周
在 kernel 之外实现，作为不可信但受信任的日常工具。

- [ ] 布尔连接词全套：`CONJ`, `CONJUNCT1/2`, `DISJ1/2`, `DISJ_CASES`, `NOT_INTRO`, `NOT_ELIM`, `CCONTR`（经典反证法）
- [ ] 量词：`GEN`, `SPEC`, `EXISTS`, `CHOOSE`
- [ ] 代换策略：`SUBST`, `SUBS`
- [ ] 重写：最简版 `REWR_CONV` + `ONCE_REWRITE_RULE`
- [ ] Conversion 组合子：`THENC`, `ORELSEC`, `TRY_CONV`, `REPEATC`, `SUB_CONV`, `DEPTH_CONV`

**验收**：能一行证 `⊢ ∀x y. x = y ⇒ y = x`（对称性）。

### M5：Goal-oriented Tactic 层 ✦ 第 7–8 周
- [ ] `goalstack` 对象（又一个 Module 闭包的应用！）
- [ ] 基础 tactic：`CONJ_TAC`, `DISJ1_TAC`, `GEN_TAC`, `EXISTS_TAC`, `REWRITE_TAC`, `ASSUME_TAC`
- [ ] Tactic 组合子：`THEN`, `THENL`, `ORELSE`, `REPEAT`, `ALL_TAC`, `NO_TAC`
- [ ] `prove[term, tactic]` 高级接口
- [ ] notebook 里的 goal 可视化（每一步当前目标与假设）

**验收**：用 tactic 风格证明一批经典命题逻辑等价式。

### M6：Parser + Pretty Printer ✦ 第 9 周
- [ ] 字符串到 term 的 parser（中缀、绑定符、类型推断）
- [ ] term 到 `Box` 的 pretty printer，支持数学排版
- [ ] Notebook MakeBoxes 规则让 thm 在输出时渲染成 `⊢ …`
- [ ] 前缀/中缀算符注册机制

**验收**：可以写 `prove["∀ x y. x + y = y + x", ...]`（假设 `+` 已在某个加载的理论里定义）。

### M7：基础数据与数系 ✦ 第 10–14 周
数学库的底座。此阶段必须同时做好**类型层**和**自动化层**两件事——后续所有分析内容对两者都高度依赖。

- [ ] 布尔、Pair、Sum、Option
- [ ] **集合**：编码为 `α → bool`；建立 `∪`、`∩`、`\\`、`⊆`、`𝒫`、笛卡尔积、象 / 原象；`IN` 和 `SUBSET` 的改写规则
- [ ] 自然数 `num`（从 `ind` 的无穷性定义，对齐 HOL Light）、整数 `int`、有理数 `rat`（商类型）
- [ ] **实数 `real`**：Cauchy 序列等价类 / Dedekind cut 二选一构造；导出完备有序域定理。这是整个数学库的成败分界线
- [ ] 列表、有限集合、finite sum / finite product 记号（`∑`、`∏`）
- [ ] `num` / `int` / `real` 的代数恒等式改写集合
- [ ] （可选）复数 `complex`：作为 `real × real` 的代数构造

**必须伴生的自动化**（缺一项，后续分析证明体量都会失控）：
- [ ] `MESON_TAC`：一阶 Model Elimination 证明搜索
- [ ] `SIMP_TAC`：带假设的条件重写引擎，承接 M4 的 `REWRITE_TAC`
- [ ] `SET_TAC`：集合论的小决策程序（布尔化 + `MESON_TAC`）
- [ ] `ARITH_TAC`：自然数 / 整数 Presburger 片段决策
- [ ] `REAL_ARITH`：实数线性算术决策（Fourier–Motzkin 或 Simplex 变种）
- [ ] `REAL_FIELD`：实数域多项式等式 + `REAL_ARITH`（可延后到 M8）

**验收**：
- `⊢ ∀a b c:real. a*(b+c) = a*b + a*c` 一步 `REAL_ARITH`
- `⊢ ∀S T:α→bool. S ∩ T ⊆ S ∪ T` 一步 `SET_TAC`
- 能机械证 `num` / `real` 的域 / 有序域结构定理

---

### M8：一元实分析 — 止于黎曼可积的 Lebesgue 判据
**第一期目标**。从此处开始不再给周估计，以里程碑结算（理由见本节末尾）。

- [ ] **实数拓扑**：绝对值、开 / 闭 / 紧（Heine–Borel）、连通、可数稠密、完备性的等价刻画
- [ ] **序列**：极限 `-->`、`limsup` / `liminf`、子序列、Bolzano–Weierstrass、Cauchy 准则
- [ ] **级数**：部分和、绝对 / 条件收敛、比较 / 根值 / 比值 / Leibniz 判别、绝对收敛的重排定理
- [ ] **函数极限与连续**：`continuous_on`、一致连续、介值 / 最值定理、Heine 定理
- [ ] **微分**：导数、Rolle、Lagrange / Cauchy 中值定理、Taylor 带 Lagrange / 积分余项、L'Hôpital
- [ ] **基本超越函数**：`exp` / `ln` / `sin` / `cos` 由幂级数定义 + 朴素性质（正性、单调、有界、奇偶、`cos(0) = 1` 等）；π 的形式化定义。**完整加法公式与三角恒等式套件需要函数项级数机制，延后到 M10 Part A 回填**
- [ ] **黎曼积分**：`has_integral` 的 Darboux 刻画、线性性、区间加性、FTC I / II、分部积分、一元换元
- [ ] **Lebesgue 零测集**：`negligible S ⟺ ∀ε>0. ∃ 可数区间列覆盖 S 且 ∑长度 < ε`；可数并零测、零测与连续的互动
- [ ] **几乎处处**：`almost_everywhere` 谓词与基本演算
- [ ] **Lebesgue 可积性判据**：`f ∈ R[a,b] ⟺ f 有界 ∧ f 在 [a,b] 上 a.e. 连续`

**验收**：
- 完整机械化 FTC 两半
- 证出 Lebesgue 可积性判据（本里程碑的 capstone）
- 例行计算：`∫_0^1 x^n dx = 1/(n+1)`、`∫ sin = -cos` 等

---

### M9：多元分析 — 止于一般 Stokes 公式
**第二期目标**。基于黎曼积分 + Jordan 容度，不引入完整勒贝格测度。

- [ ] **欧氏空间 `R^n`**：初期按 `num -> real` 的定长 tuple 实现；若后续需要类型级维度（HOL Light 的 `real^N`）再迁移
- [ ] **线性代数**：线性映射、矩阵、行列式、迹、正交群、特征值（够用即止）
- [ ] **`R^n` 拓扑**：范数等价、开闭紧、Heine–Borel、连通
- [ ] **多元微分**：Fréchet 导数、偏导、Jacobi 矩阵、chain rule、Clairaut、多元中值定理
- [ ] **逆映射 / 隐函数定理**
- [ ] **Jordan 容度**：外 / 内容、可测性；与黎曼积分相容；Jordan 零容 ⇒ Lebesgue 零测
- [ ] **多重黎曼积分**：Jordan 可测集上的积分、Fubini（Jordan 版）
- [ ] **重积分换元法**：`φ: A → R^n` 为 `C^1` 微分同胚时，`∫_{φ(A)} f = ∫_A (f∘φ)·|det Dφ|`
- [ ] **曲线 / 曲面积分**：弧长、面积的参数化定义
- [ ] **微分形式**：外代数、`k-form`、外微分 `d`、楔积；`d² = 0`
- [ ] **欧氏空间中的带边子流形**：嵌入定义（局部图 / 水平集 / 参数化）、定向、边界诱导定向
- [ ] **形式在流形上的积分**：`∫_M ω` 通过单位分解定义
- [ ] **一般 Stokes 公式**：`∫_M dω = ∫_∂M ω`（紧定向 `C^∞` 带边子流形）
- [ ] Green、Gauss、经典 Stokes 作为推论

**验收**：
- 证出重积分换元法
- 证出一般 Stokes（带边紧定向子流形版）
- 从一般 Stokes 推出 Green / Gauss / 经典 Stokes

---

### M10：函数项级数、含参积分与 Fourier 分析 — 仍在黎曼积分框架内
**第三期目标**。分前后两半：Part A 建立从 M8 通向 Fourier 的中间层——函数项级数与含参积分；Part B 才进入 Fourier。只依赖 M8 的黎曼积分 + 零测集 + a.e.，不引入 `L^p` 空间的完整勒贝格构造。

#### Part A：函数项级数与含参积分

- [ ] **函数序列的一致收敛**：`uniformly_on` 谓词；一致收敛保持连续；一致极限下交换积分与极限；一致收敛 + 导数一致收敛 ⇒ 可逐项求导；Dini 定理
- [ ] **函数项级数**：Weierstrass M-判别、Abel / Dirichlet 判别；逐项求极限 / 积分 / 求导
- [ ] **幂级数**：Cauchy–Hadamard 收敛半径、收敛区间内的一致收敛、逐项求导与积分、Abel 定理（端点行为）
- [ ] **回填 M8 搁置的超越函数恒等式**：用绝对收敛级数的 Cauchy 乘积得到 `exp(x+y) = exp(x) exp(y)`；导出 sin / cos 的加法公式、三角恒等式全套、De Moivre；至此 `exp` / `ln` / `sin` / `cos` / π 的性质完整
- [ ] **含参正常积分**：`F(y) = ∫_a^b f(x,y) dx` 的连续性、可微性（积分号下求导 / Leibniz 法则）、可积性（积分顺序交换——黎曼意义下的一维 Fubini）
- [ ] **含参反常积分**：`∫_a^∞ f(x,y) dx` 与 `∫_a^b f(x,y) dx`（f 在区间内某点无界）关于参数的一致收敛；M-判别 / Abel / Dirichlet；一致收敛条件下的连续性 / 可微性 / 可积性
- [ ] （可选）**Gamma / Beta 函数**：含参积分的典型应用；Γ 的函数方程 `Γ(x+1) = x·Γ(x)`、`B(p,q) = Γ(p)Γ(q)/Γ(p+q)`

**Part A 验收**：
- 一致收敛保持连续 / 可积 / 可微 三条经典定理机械化
- `exp` / `sin` / `cos` 的加法公式与三角恒等式套件完整
- 例行结果：`d/dy ∫_0^1 sin(xy) dx = ∫_0^1 x cos(xy) dx` 通过 Leibniz 法则一步证出
- （可选）Γ 函数方程

#### Part B：Fourier 级数与 Fourier 变换

- [ ] 周期函数、三角多项式、Fourier 系数
- [ ] Dirichlet 核、Fejér 核及其卷积性质
- [ ] **点态收敛**：Dirichlet 定理（分段光滑函数的 Fourier 级数在连续点处点态收敛；跳跃点收敛到左右极限平均）
- [ ] **一致收敛**：Weierstrass 三角逼近定理、Fejér 一致收敛定理
- [ ] **均方收敛 / Parseval**：在黎曼可积函数的连续子类上（保证黎曼意义下均方收敛合法）
- [ ] 卷积、近似单位
- [ ] **Fourier 变换**：在 Schwartz 类 `𝒮(R)` 或 `C_c^∞` 上定义（使黎曼积分充分）；连续性 / 可微性 / 衰减性通过 Part A 的含参积分机制得到
- [ ] **反演 / Plancherel / Parseval**：Schwartz 类上
- [ ] **Poisson 求和公式**：Schwartz 类上 `∑_n f(n) = ∑_k \hat f(2π k)`；用 Fejér 求和或 Schwartz 衰减直接推导，绕开 `L^2` 完备性

#### Part C：Radon 变换与 CT 重建的数学原理

- [ ] **Radon 变换**：在 Schwartz 类 `𝒮(R^2)` 上定义 `R f(θ, s) = ∫_{x·θ = s} f`；基本线性性与连续性
- [ ] **投影切片定理**（Fourier Slice Theorem）：`\hat{R f}(θ, σ) = \hat f(σ θ)`——一维 Fourier 变换与二维 Fourier 变换通过 Radon 串起来，这是整个 CT 数学框架的中心定理
- [ ] **滤波反投影反演公式**：`f = (1/(4π)) R^* (Λ R f)`，其中 `Λ` 是 Riesz 势（在 Schwartz 类上用一维 Fourier 乘 `|σ|` 表达）
- [ ] 连续性与误差估计：带宽受限近似、有限采样角度的误差界（能做到多少取决于工程进度）

**Part B + C 验收**：
- 完整机械化 Fejér 定理与 Schwartz 类 Fourier 反演
- Poisson 求和公式在 Schwartz 类上证出
- 投影切片定理机械化
- Schwartz 类上的 Radon 反演（滤波反投影）作为 **M10 capstone** 给出完整证明脚本

---

**关于 M8–M10 的时间维度**：不给周估计。参考点：HOL Light 的 Jordan / Riemann / 多元分析 / Stokes 是 Harrison 等人数年工作的成果，我们对标它的黎曼部分（避开勒贝格），工作量小一些但仍然是**多年级别**的工程。紧凑推进下，M8 在半年到一年可达；M9、M10 各自更久。中途可以（也应当）随工程进度调整范围和优先级。

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
│   ├── Real.wl             (* Cauchy 或 Dedekind 构造 *)
│   ├── List.wl
│   ├── Finite.wl           (* 有限集、∑ / ∏ 记号 *)
│   └── Complex.wl          (* 可选 *)
│
├── analysis1/              (* M8：一元实分析 *)
│   ├── Topology.wl         (* R 上拓扑 *)
│   ├── Limits.wl
│   ├── Series.wl
│   ├── Continuous.wl
│   ├── Deriv.wl
│   ├── Taylor.wl
│   ├── Transc.wl           (* exp / ln / sin / cos / π *)
│   ├── Riemann.wl
│   ├── FTC.wl
│   ├── Null.wl             (* Lebesgue 零测、a.e. *)
│   └── LebesgueCriterion.wl
│
├── analysis2/              (* M9：多元分析 *)
│   ├── Vectors.wl          (* R^n *)
│   ├── LinAlg.wl
│   ├── TopologyN.wl
│   ├── DerivN.wl           (* Fréchet 导数 *)
│   ├── InverseFn.wl
│   ├── Jordan.wl           (* Jordan 容度 *)
│   ├── MultiRiemann.wl
│   ├── Fubini.wl
│   ├── ChangeOfVar.wl
│   ├── Forms.wl            (* 微分形式 *)
│   ├── Manifold.wl         (* 带边子流形 *)
│   └── Stokes.wl
│
├── analysis3/              (* M10：函数项级数、含参积分、Fourier、Radon *)
│   │                       (* Part A：Fourier 所需的中间层 *)
│   ├── UnifConv.wl         (* 函数序列 / 级数的一致收敛 *)
│   ├── PowerSeries.wl      (* 幂级数、Cauchy–Hadamard、Abel *)
│   ├── Transc2.wl          (* exp/sin/cos 完整恒等式回填 *)
│   ├── ParamIntegral.wl    (* 含参正常 / 反常积分 *)
│   ├── Gamma.wl            (* 可选 *)
│   │                       (* Part B：Fourier *)
│   ├── Periodic.wl
│   ├── Kernels.wl          (* Dirichlet / Fejér *)
│   ├── PointwiseConv.wl
│   ├── FourierUnifConv.wl
│   ├── Parseval.wl
│   ├── Convolution.wl
│   ├── FourierTransform.wl
│   ├── PoissonSum.wl       (* Poisson 求和公式 *)
│   │                       (* Part C：Radon 变换 / CT 重建 *)
│   ├── Radon.wl            (* R 及其伴随 R^* *)
│   ├── FourierSlice.wl     (* 投影切片定理 *)
│   └── RadonInversion.wl   (* 滤波反投影反演 *)
│
├── tests/
│   ├── harness.wl
│   ├── run_all.wls         (* wolframscript 入口：CI 回归整条线 *)
│   ├── kernel_tests.wt
│   ├── bool_tests.wt
│   ├── real_tests.wt
│   ├── riemann_tests.wt
│   ├── stokes_tests.wt
│   └── fourier_tests.wt
│
└── demos/
    ├── 01-first-proof.nb
    ├── 02-bool-algebra.nb
    ├── 03-nat-arithmetic.nb
    ├── 04-epsilon-delta.nb      (* M8 *)
    ├── 05-riemann-integral.nb   (* M8 *)
    ├── 06-stokes.nb             (* M9 *)
    ├── 07-fourier.nb            (* M10 Part B *)
    └── 08-radon.nb              (* M10 Part C：CT 重建 *)
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

### 第一档：一元分析（完成 M7–M8）
- ✅ `real` 构造完成，完备有序域全部定理可被自动化证出
- ✅ `REAL_ARITH` / `MESON_TAC` / `SIMP_TAC` / `SET_TAC` 均已可用
- ✅ FTC 两半、Taylor 定理、主要超越函数恒等式全部机械化
- ✅ 黎曼积分的 **Lebesgue 可积性判据** 作为 capstone 定理证出
- ✅ 回归套件在 `wolframscript` 下数分钟内跑完

➡️ 够做一门"形式化数学分析"小课程的配套工具，或上 arXiv。

### 第二档：多元分析（完成 M9）
- ✅ 重积分换元法机械化
- ✅ **一般 Stokes 公式**（带边紧定向子流形版）机械化
- ✅ Green / Gauss / 经典 Stokes 作为推论
- ✅ 上述定理的 demo notebook 能让一位数学分析教师看懂并复现

➡️ 这是非平凡的形式化成果——Mathematica 生态内前所未有。

### 第三档：Fourier 分析 + Radon 变换（完成 M10）
- ✅ 三类收敛（点态 / 一致 / 均方）在黎曼积分框架内各自一份完整证明
- ✅ Schwartz 类上的 Fourier 反演公式机械化
- ✅ Poisson 求和公式在 Schwartz 类上证出
- ✅ 投影切片定理机械化
- ✅ Schwartz 类上的 Radon 变换反演（滤波反投影）——CT 重建的数学原理机械化

➡️ 到此为止，本项目已经是一个**可实用**的教学与研究级形式化工具，不再只是"Mathematica 复刻 LCF"的玩具演示。