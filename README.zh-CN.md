# mma-hol

*[English version](README.md)*

一个**用 Wolfram 语言编写的、内核极小的 LCF 式高阶逻辑（HOL）定理证明器**，以
[HOL Light](https://github.com/jrh13/hol-light) 为蓝本。它的标准库从 Dedekind 割构造实数，
并完全基于一个 10 条规则的可信内核证明了一批经典实分析定理——单调收敛、Cauchy 完备性、
Bolzano–Weierstrass、Heine–Borel、区间的连通性刻画——除三条标准 HOL 公理外**零 `sorry`、零额外公理**。

状态：**已完成**——完整测试套件冷启动通过 `3126/0`（两种封装模式下均通过）。

---

## 这个项目真正想验证什么

它首先是**一个关于封装的实验**。出发点是这个问题：

> 在一门没有原生 private 概念的语言里，能否用 Wolfram 语言的 `Module` / `Unique`（gensym）
> 机制，搭出一条类似 C++/Java 访问修饰符那样的 `private` 信任边界？

定理证明器是检验这个问题的理想压力测试，因为它的正确性只取决于一件事：**内核之外的任何代码
都不能凭空造出"定理"类型的值。** 只要封装成立，那个庞大的、不受信任的标准库 / 自动化层里
最严重的 bug 也只能是"证不出一个真命题"——绝不可能造出一个假命题。这就是 LCF 纪律，它把
封装问题变成了一个具体且可证伪的命题。

### 封装是怎么做的

所有可变的内核状态——定理构造子 `thmTag`、常量/元数表、公理与定义注册表——都住在私有
上下文 `` HOL`Kernel`Private` `` 里。一个安装器（`defineKernel`）把 10 条原始推理规则和扩展
API 定义为对这些符号的闭包。外部代码只拿到**公开**接口（`REFL`、`TRANS`、`ABS`、`mkConst`、
`newDefinition`……），永远拿不到一个能用来直接伪造 `thmTag[...]` 的名字。

### 必须坦白的局限

这**不是**一条硬性的安全边界。Wolfram 语言会暴露它的符号表：``Names["HOL`Kernel`Private`*"]``、
`Symbol`、上下文枚举，仍然能在运行时**找到**这些内部符号并去戳它们。所以一个铁了心的调用者
还是能伸手进来。

封装真正买到的是**可审计性，而非强制性**：循规蹈矩的代码**不可能意外地**耦合到内核内部
（根本没有稳定的公开名字可抓），因此任何对信任边界的破坏都必须是蓄意的、因而是可 grep 出来的。
它把审计一个大代码库的成本从"通读全部"降到"检查那一小撮显式的私有名引用"。对一个学习/研究
项目而言，这是一个既正确又可达成的标准。

## 为什么选 LCF + HOL Light

正是 LCF 架构让这个封装问题**值得**问。因为整个系统的健全性归结为一个小内核的完整性，
WL-`Module` 信任边界就有了一项明确的职责，"它成功了吗"也就有了明确的答案。HOL Light 是
经典的极小 LCF 证明器（简单类型 λ-演算上的 10 条原始规则 + 三条公理），因此是天然的蓝本：
小到能忠实重写，又足够表达力在其上发展真正的数学。

一个令人愉快的推论：健全性与**谁写了不受信任的那几层无关**。本仓库的标准库和自动化是在
大量 AI 辅助下开发的（见 [开发署名](#开发署名)）；这丝毫不削弱正确性保证，因为每一条
定理仍由同样的 10 条内核规则重新核验。

## 两种封装模式：Strict 与 Stable

内核有两种模式，由 `` Global`$HOLEncapsulationMode` `` 选择：

| | **Strict**（默认、CI） | **Stable**（开发 / 持久化） |
|---|---|---|
| 内核状态符号 | `Module` 局部 gensym（`thmTag$4271`……）——无稳定名 | 固定名（``HOL`Kernel`Private`thmTag``） |
| 边界 | 由构造强制——外部代码根本没有名字可引用 | 约定 + 一条 CI lint（标记 `Kernel.wl` 之外任何对 ``HOL`Kernel`Private`*`` 的引用） |
| `DumpSave` 快照能否冷重启后恢复？ | 否（gensym 跨序列化不稳定） | **能** |
| 用途 | 权威的正确性闸门；封装实验本身的演示 | `bootstrap.mx` 快照 + 快速开发循环 |

两种模式通过 `defineKernel` 安装器共享**同一份** `Kernel.wl` 主体，CI 在两种模式下都跑完整
套件——所以它们不可能悄悄分叉。这里的取舍正是实验本身要回答的：Strict 给你真正的、无法命名的
私有性，但不能序列化；Stable 给你一个可快速恢复的快照，代价是把边界降级为一条受 lint 约束的约定。

## 标准库

数系自底向上、全部在内核内构造：`Pair`、`Sum`、`Option`、`Set`、`Num`（由无穷公理得 ℕ）、
`List`、`Finite`、`Int`（ℤ 作 Grothendieck 商）、`Rat`（ℚ 作既约分数）、`Real`。

**ℝ 经由 Dedekind 割构造**——单个下集 `L : ℚ → bool`——而非 HOL Light 的 Cauchy / "近似可加
函数"构造。这是一个刻意的、对初学者友好的选择：Dedekind 构造是大多数分析教材采用的那个，割
**就是**实数本身（内核相等即实数相等，无 setoid 商），序关系就是集合包含。随后证明 ℝ 是
完备有序域，并在其上搭一个线性算术判定过程（`REAL_ARITH`，Fourier–Motzkin 神谕 + Farkas
证书内核验证器）。

`stdlib/Real/` 里的分析主线（全部走确界原理——不用 Lindelöf 或可数性机器）：

- **序列**（`Seq`）：实 ε 的 `tendsto`、极限演算、单调收敛定理、子列、**Cauchy 完备性**。
- **紧性**（`Compact`、`CompactSet`）：**Bolzano–Weierstrass**；闭区间 **Heine–Borel**
  （经"可被部分覆盖的点集有确界 = 右端点"）；以及对一般实集的开覆盖谓词 `isCompact`，
  含完整等价 **`isCompact ⟺ isClosed ∧ setBounded ⟺ isSequentiallyCompact`**。
- **连通性**（`Connected`）：**连通 ⟺ 区间**——介值定理的序-拓扑内核。（本库止于点集拓扑，
  没有连续函数层，所以**函数形式**的介值定理 `f(a)<0<f(b) ⇒ ∃c. f(c)=0` 不在范围内——
  但 [`demos/`](demos/) 目录把这一层作为示例搭了出来，并由它导出函数形式介值定理与极值定理。）
- **拓扑**（`Topology`）：开/闭集、补集、相对（子空间）闭。

感兴趣的读者可直接在源码里追这些路线——每个文件是一个按依赖排序的定义/引理闭包，导出显式。
两个值得一提的 HOL 特有设计：

- **没有依赖索引类型的开覆盖。** HOL 没有 `∀{ι : Type}` 量词，所以覆盖不能是族 `U : ι → Set ℝ`。
  改把覆盖编码为**开集的集合** `C : (ℝ → bool) → bool`，再通过"钳制"族 `λV. if C V then V else ∅`
  把多态的闭区间紧性定理实例化在索引类型 `ℝ → bool` 上来复用。
- **实数乘法**用对非负核心的二元符号分情况（`COND` 于 `0 ≤ x` / `0 ≤ y`）定义，使结合律/
  分配律的分情况分析可控（8 种情形，而非朴素的零/正/负三元分裂产生的 27 种）。

## 仓库结构

```
Types.wl Terms.wl Kernel.wl Bootstrap.wl   — 项/类型层 + 可信内核
Bool.wl Equal.wl Drule.wl Tactics.wl       — 派生规则、转换、tactic 引擎
Parser.wl Printer.wl                       — 字符串 ⇄ 项（不用 ToExpression；边界完整）
auto/                                      — MESON、SIMP、SET、ARITH、REAL_ARITH
stdlib/                                    — Pair、Sum、Option、Set、Num、List、Finite、FTA、Int、Rat
stdlib/Real/                               — ℝ 构造 + 分析主线
tests/                                     — 运行器 + 各模块 *_tests.wl
docs/dev/                                  — 设计文档 (PLAN.md)、证明历史 (PROGRESS.md)、开发笔记
```

## 运行

需要 `wolframscript`（Wolfram Engine / Mathematica 14.x）。

```bash
# 权威冷检查（Strict 模式，约 10–15 分钟）：每个文件从源码加载。
wolframscript -file tests/run_all.wls

# 快速子集（Stable 模式，约 3 秒）：恢复 bootstrap.mx 快照。
wolframscript -file tests/run_fast.wls real

# 改动核心文件后重建快照（约 10 分钟）。
wolframscript -file tests/build_snapshot.wls
```

[`demos/`](demos/) 里有两个交互式笔记本供手动探索证明器（在 Mathematica / 免费的 Wolfram
Player 里双击打开）：`examples.nb` 是对内核、自动化与标准库代表性定理的导览；`continuous.nb`
在拓扑之上搭一层连续函数，并在闭区间上导出有界性、极值定理与函数形式的介值定理。详见
[`demos/README.md`](demos/README.md)，API 与如何开发自己的证明见
[`docs/USER_GUIDE.md`](docs/USER_GUIDE.md)。

## 开发署名

本项目**全程由 Claude Opus（Anthropic）以 agentic 工作流主导开发**。在后期实分析阶段，
证明的**路线**参考了一个尚未公开的 Lean 4 项目（`tautology`，同一套实分析塔的 0-`sorry`
重新实现），并将其中一部分从蓝图到 Wolfram 语言证明的翻译工作，在"规格写在这里、每个结果
都在这里对内核核验"的纪律下委派给了 OpenAI 的 Codex CLI。如上所述，不受信任各层的 AI 作者
身份不影响健全性——每条定理都由内核重新核验。

## 许可证

[MIT](LICENSE)——几乎可以任意使用，只需保留版权声明。如需引用本项目，可用
[`CITATION.cff`](CITATION.cff)；[`CONTRIBUTING.md`](CONTRIBUTING.md) 说明了唯一要紧的规则
（不要破坏内核信任边界）。
