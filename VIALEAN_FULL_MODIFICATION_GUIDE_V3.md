# ViaLean 完整修改指南
## 从“符号 Frontier + 可选模型指导”升级为 Persistent Neural-Symbolic Co-Search Engine

**文档定位**：架构设计 + 修复指南 + 重构路线图 + 实施验收标准
**适用仓库**：`RuoranXu/ViaLean`
**基准代码快照**：`main`，2026-09-03
**核心目标**：

> **Lean 持续快速生成并维护证明空间，模型持续创造新的中间结构与连接，LocalSynthesizer 在全过程把这些结构变成可验证的项与义务，Lean kernel 负责最终裁决。**
> ViaLean 不应依赖模型反复猜 tactic、执行失败、读错误、再猜 tactic；也不能只让 Lean 侧提前枚举一点局部未来。系统应同时由 Lean 构造有界、可验证的 symbolic future，并由神经模型主动提出 helper lemma、witness、intermediate value、bridge、generalization、invariant 等当前纯符号枚举不会自然产生的中间对象，再由 Lean 将这些猜想转换为严格 proof obligations。

---

# 目录

1. 项目演进目标
2. 当前实现的正确定位
3. 目标架构总览
4. 核心设计原则
5. 当前代码必须先修的工程问题
6. Proof Atlas：神经符号共享中间表示
7. Goal identity / 状态等价
8. Symbolic transition 统一动作层
9. Atlas Builder 与全局预算
10. Diversity：从顶层 Frontier 扩展到完整 Future Atlas
11. Neural Planner：模型从 tactic generator 升级为规划器
12. Policy + Value + Uncertainty
13. Strategy / Region / Expansion Request
14. Replan：替代反复试错
15. Structured Observation：替代错误文本聊天
16. Typed Model Action DSL 与安全边界
17. 搜索控制器重构
18. Leaf Solver / Router 重构
19. 配置系统重构
20. Model Protocol v2
21. Prompt / 序列化预算
22. Cache、Transposition 与失败记忆
23. 训练数据与自我改进接口
24. 文件级修改地图
25. 分阶段实施路线
26. 测试体系
27. Benchmark 与 Ablation
28. 观测指标与 Trace
29. 向后兼容策略
30. Definition of Done
31. 禁止的反模式
32. 后续研究路线
33. 推荐 Commit / Issue 拆分
34. 最终目标架构

---



# 0.1 架构最终修正：Persistent Co-Search，而不是“Lean 告诉模型真世界”

前两版文档里“Lean 告诉模型哪些世界是真的”仍然太像一次性的 producer/consumer 关系。

ViaLean 真正需要的是：

> **Lean 与模型长期共享一个持续存在的 Proof Workspace。Lean 高频、低成本地扩展和验证局部空间；模型低频但高语义密度地一次输出一批中间假设、结构、项和扩展方向；每一批模型输出都被 Lean 吸收到同一个 Workspace 中，并触发新一轮局部合成、桥接和状态维护。**

不是：

```text
Lean 生成一点
→ 给模型
→ 模型选一个
→ Lean 验证
→ 再问模型
```

而是：

```text
                 Persistent Proof Workspace
                         （持续存在）
                              │
          ┌───────────────────┼────────────────────┐
          │                   │                    │
          ▼                   ▼                    ▼
   Lean Local Expand    Local Synthesizer    Neural Reasoner
   高频、便宜            高频/中频             低频、高语义
          │                   │                    │
          │          构造中间项/证明链接           │
          │                   │            一次提出一批假设
          │                   │            中间值 / lemma
          │                   │            witness / invariant
          │                   │            结构分解 / bridge
          └───────────────────┼────────────────────┘
                              │
                              ▼
                    Workspace 增量更新
                              │
                              ▼
                    所有参与者继续工作
```

这里不存在“Lean 只告诉一次”。

Lean 对 Workspace 的维护是**持续的**。

---

# 0.2 Proof Workspace：同一张图上维护所有状态

不要为“真”和“猜测”建立互不相干的两个世界。

所有对象都在同一个 Workspace 中，只是状态不同。

建议：

```lean
inductive KnowledgeStatus
  | verified
  | pending
  | speculative
  | refuted
  | dominated
```

一个中间 lemma：

```text
L : P → Q
```

可以经历：

```text
speculative
    ↓ Lean elaboration 成功
pending
    ↓ LocalSynthesizer 找到 proof
verified
```

也可能：

```text
speculative
    ↓ statement 根本不能 elaboration
refuted
```

或：

```text
pending
    ↓ 很难证明，而且对主目标无帮助
dominated
```

模型始终看到的是这张带状态的共享地图。

它无需等待 Lean 说：

> “现在这些是真的。”

状态标签本身已经持续存在。

---

# 0.3 Workspace 应是 Proof Hypergraph，而不只是树/普通图

证明关系天然存在：

```text
证明 G
需要同时证明
O1, O2, O3
```

所以最自然的数据结构不是简单 edge：

```text
A → B
```

而是 hyperedge：

```text
Transition T:
    parent = G
    obligations = [O1, O2, O3]
```

建议：

```lean
abbrev WorkspaceNodeId := UInt64
abbrev WorkspaceEdgeId := UInt64

structure WorkspaceNode where
  id          : WorkspaceNodeId
  key         : SemanticKey
  kind        : WorkspaceNodeKind
  status      : KnowledgeStatus
  proposition : Expr
  contextRef  : ContextRef
  origin      : Origin
  utility     : UtilityEstimate

structure WorkspaceHyperedge where
  id           : WorkspaceEdgeId
  source       : WorkspaceNodeId
  operation    : SymbolicOperation
  obligations  : Array WorkspaceNodeId
  status       : KnowledgeStatus
  cost         : CostEstimate
  evidence     : EdgeEvidence
```

例如模型提出 helper lemma `L`：

```text
                 Goal G
                    │
                 cut L
                    │
          ┌─────────┴──────────┐
          ▼                    ▼
      prove L             prove G using L
```

这是一条 AND-hyperedge，而不是两条相互独立的普通边。

---

# 0.4 两个不同节奏：Symbolic Ticks 与 Neural Epochs

这点是“不要反复试错”的关键。

ViaLean 应有两个时间尺度。

## Symbolic Tick

非常频繁地发生：

```text
elaborate
typecheck
exact/apply
constructor
rewrite
simp
small inhabitation
small forward closure
small backward closure
bridge checking
dedup
state update
```

每次成本小。

## Neural Epoch

只在积累了一定新信息后发生。

模型一次不是返回一个 tactic，而是返回一个 **Thought Batch**。

例如：

```text
Batch:
  1. L1 可能是关键 helper lemma
  2. 尝试中间表达式 b
  3. existential witness 可能是 f x
  4. equality region 应继续展开
  5. 归纳时应 generalize y
  6. construction region 暂时不值得投入
```

Lean 对整批内容独立处理。

其中第 2 条失败，不应该导致整轮“模型思考失败”。

第 1、3、4、5 条仍可以继续扩图。

---

# 0.5 ModelThoughtBatch：模型一次输出一段“证明思考”，而非一个动作

建议协议核心变为：

```lean
structure ModelThoughtBatch where
  hypotheses        : Array HypothesisProposal
  intermediateTerms : Array TermProposal
  witnesses         : Array WitnessProposal
  bridges           : Array BridgeProposal
  decompositions    : Array DecompositionProposal
  generalizations   : Array GeneralizationProposal
  invariants        : Array InvariantProposal
  expansionRequests : Array ExpansionRequest
  regionPreferences : Array RegionPreference
  strategySummary   : Option StrategySummary
```

模型可以一次给 5–30 个不同粒度的候选。

数量由 payload budget 控制，而不是强制“一轮只能一个答案”。

核心原则：

> **模型的一串 reasoning 最后应该沉淀成一批可独立验证、可组合、可维护的结构化对象。**

---

# 0.6 Lean 不回复“错误”，而回复 Workspace Delta

每次处理模型 Batch 后，Lean 返回的是增量：

```lean
structure WorkspaceDelta where
  fromVersion      : Nat
  toVersion        : Nat
  accepted         : Array AcceptedObject
  rejected         : Array RejectedObject
  promoted         : Array StatusPromotion
  newNodes         : Array NodeView
  newEdges         : Array EdgeView
  newFacts         : Array FactView
  newBridges       : Array BridgeView
  closedObligations : Array WorkspaceNodeId
  unresolved       : Array WorkspaceNodeId
  budgetState      : BudgetStateView
```

模型下一轮主要看：

```text
从自己上次看到的 workspace version 到现在发生了什么。
```

而不是每次重新塞完整 theorem + 完整 history。

---

# 0.7 Versioned Workspace：维护模型的长期状态

建议：

```lean
structure ProofWorkspace where
  version      : Nat
  nodes        : ...
  hyperedges   : ...
  conjectures  : ...
  observations : ...
  transposition : ...
  synthesisCache : ...
```

以及：

```lean
structure ModelCursor where
  lastSeenVersion : Nat
  activeStrategy  : Option StrategyPlan
  activeRegions   : Array RegionId
  memory          : PlannerMemory
```

每轮：

```text
delta = Workspace.diff(lastSeenVersion, currentVersion)
```

这就是“Lean 一直保持告诉”的工程实现。

不是不断重复 prompt，而是：

> **共享状态 + 增量同步。**

即使实际 provider API 是 stateless HTTP，也可以由 ViaLean 自己维护 `PlannerMemory` 和 compact delta，把这种持续语义模拟出来。

---

# 0.8 Canonical 类能力应升级为 Ubiquitous LocalSynthesizer

这是本版最重要的改变之一。

Canonical 类 term-inhabitation 能力不能只放：

```text
LeafRouter
→ 最后尝试一下
```

它应该贯穿整个搜索。

建议新增：

```text
ViaLean/Synthesis/
  Types.lean
  Local.lean
  Bridge.lean
  Partial.lean
  Query.lean
  Cache.lean
```

核心接口：

```lean
structure LocalSynthesisQuery where
  context     : ContextRef
  task        : SynthesisTask
  budget      : SynthesisBudget

inductive SynthesisTask
  | inhabit (type : Expr)
  | prove (proposition : Expr)
  | synthesizeWitness (domain : Expr) (property : Expr)
  | fillPartial (sketch : PartialTerm)
  | connect (left : SemanticRegion) (right : SemanticRegion)
  | deriveUseful (seedTypes : Array Expr)
```

结果：

```lean
structure LocalSynthesisResult where
  terms        : Array SynthesizedTerm
  obligations  : Array ResidualObligation
  derivedFacts : Array DerivedFact
  bridges      : Array SynthesizedBridge
  stats        : SynthesisStats
```

---

# 0.9 LocalSynthesizer 不是只“证明到终点”，它负责构造中间链接

例如当前主目标：

```text
Γ ⊢ G
```

模型提出：

```text
也许需要一个类型 T 的对象
```

LocalSynthesizer 做：

```text
Γ ⊢ ?t : T
```

如果找到：

```text
t : T
```

它并没有完成 theorem。

但 Workspace 新增：

```text
verified term: t : T
```

这个对象可能打开新的：

```text
apply
rewrite
witness
function application
constructor
helper lemma
```

路径。

这就是最重要的变化：

> **inhabitation 是“空间生成算子”，不是终局 tactic。**

---

# 0.10 Partial Inhabitation：允许构造“还差几个洞”的中间项

非常有价值的能力是：

模型不必一次猜出完整 Lean term。

例如模型给出结构：

```text
f ?x (g ?y)
```

ViaLean 可以把它 elaboration 成受控 partial term：

```text
已知 skeleton
未知 holes
```

再把 holes 转成 proof obligations：

```text
O1 : ⊢ type-of-?x
O2 : ⊢ type-of-?y
```

LocalSynthesizer 分别尝试 inhabit。

建议内部类型：

```lean
structure PartialTerm where
  expr        : Expr
  holes       : Array HoleSpec
  expectedType : Expr

structure HoleSpec where
  mvar        : MVarId
  type        : Expr
  dependencies : Array FVarId
```

安全要求：

- partial term 永远不能直接作为最终 proof；
- 所有 hole 必须最终关闭；
- unresolved hole 只是 Workspace obligation。

这样模型可以提出“结构”，符号系统负责填细节。

---

# 0.11 Canonical-style 搜索应支持被“查询”，而不是只对当前 goal 运行

传统调用：

```text
canonical
```

隐含问题：

```text
给当前 goal 找 inhabitant。
```

ViaLean 更需要：

```text
synthesize T
synthesize a bridge between A and B
enumerate useful inhabitants of family F
fill these holes
try proving conjecture L
```

也就是把 type inhabitation 变成一个 **search service**。

即使最终不直接依赖 Canonical 库，也应该复制这种接口思想。

---

# 0.12 Forward、Backward 与 Synthesizer 三者同时工作

完整空间扩张应该有三条 Lane：

```text
             Forward Lane
        Γ 中能继续推出什么？
                  │
                  ▼
            known region
                  │
                  │
                  │
      LocalSynthesizer / Bridge
          构造中间连接
                  │
                  │
                  ▼
            target region
                  ▲
                  │
            Backward Lane
         G 需要哪些前置条件？
```

Neural model 不只是选 Lane。

它可以说：

```text
Forward 已经有 A, B, C；
Backward 需要 X, Y；
我猜中间对象 M 能连接 C 和 X。
```

然后：

```text
LocalSynthesizer:
  尝试 C → M
  尝试 M → X
```

或者直接构造相应 inhabitants。

这才是真正“模型找中间介值”。

---

# 0.13 Bridge 不限于命题，也包括 Term / Type / Expression

中间链接不应该全部是 proposition。

至少区分：

```lean
inductive BridgeObject
  | proposition (expr : Expr)
  | term        (expr : Expr) (type : Expr)
  | type        (expr : Expr)
  | equalityMidpoint (expr : Expr)
  | witness     (expr : Expr)
  | function    (expr : Expr)
  | invariant   (expr : Expr)
```

例如：

```text
a = c
```

模型找：

```text
b : α
```

这是一个 term bridge。

对于：

```text
∃ x : α, P x
```

找到：

```text
w : α
```

也是 term bridge。

对于函数组合问题，可能需要找：

```text
f : A → B
```

而不是先提出某个 proposition。

---

# 0.14 Semantic Saturation：每次新对象进入 Workspace 后自动产生邻域

模型给出：

```text
M
```

Lean 不应只回复：

```text
M 合法。
```

而应该立即触发便宜的 neighborhood saturation：

```text
M 的类型是什么？
哪些 local 可以作用到 M？
M 可以作用到哪些 local？
哪些 theorem head 与 M 匹配？
是否产生 rewrite？
是否能填已有 hole？
是否能关闭某个 pending obligation？
是否把两个 region 连起来？
```

因此一个模型想法可能自动扩出：

```text
1 个输入
→ 8 条 validated links
→ 3 个新 states
→ 2 个 obligation 被关闭
```

这就是用户所说的：

> Lean 应该突然给出好几条可能有用的东西。

而不是每次只返回“一步成功/失败”。

---

# 0.15 Burst Expansion：Lean 每次应返回“空间爆发”，而不是单步结果

建议增加：

```lean
structure ExpansionBurst where
  seed          : ExpansionSeed
  verifiedTerms : Array TermView
  derivedFacts  : Array FactView
  transitions   : Array TransitionView
  newGoals      : Array GoalView
  bridges       : Array BridgeView
  closures      : Array ClosureView
```

对于一个 seed：

```text
helper lemma L
term t
region R
```

Lean 在严格 budget 内做一个小型爆发式展开：

```text
seed
 ↓
type/elaboration
 ↓
local synthesis
 ↓
one-step forward
 ↓
one-step backward
 ↓
rewrite/equality closure
 ↓
applicable premise scan
 ↓
dedup
```

然后一次返回 Burst。

这会极大提高每次模型交互的信息密度。

---

# 0.16 模型不因为一个 local contradiction 就“停止思考”

当前很多 LLM prover 的问题是：

```text
模型长推理
→ 最后给一个具体 Lean step
→ 这个 step 不成立
→ 整段推理作废
```

ViaLean 要把 reasoning 和 execution 解耦。

模型的一段 reasoning 应拆成：

```text
idea A
idea B
intermediate object C
bridge D
witness E
strategy F
```

Lean 分别验证。

结果可能：

```text
A: invalid
B: useful
C: verified
D: pending
E: type-correct, proof obligation remains
F: still plausible
```

所以一个局部 Lean mismatch 只杀死相关对象，而不是杀死整个模型思路。

---

# 0.17 模型输出必须支持 Dependencies

一段思考通常有依赖：

```text
先构造 M
再用 M 证明 L
再用 L 改写 G
```

协议应支持：

```lean
structure ThoughtObject where
  id           : ThoughtObjectId
  payload      : ThoughtPayload
  dependsOn    : Array ThoughtObjectId
  alternatives : Array ThoughtObjectId
```

Lean 可以维护：

```text
M refuted
→ 只 invalidate 依赖 M 的分支
```

而不是整轮全部重来。

---

# 0.18 Workspace 内必须保留“未完成但有价值”的 partial progress

不能只有：

```text
solved / failed
```

需要：

```text
pending
partially_connected
locally_proven
blocked_on [O1, O2]
low_priority
```

例如 helper lemma：

```text
L
```

主方向 `L → G` 已经很容易，但 `Γ → L` 还没证明。

这条信息非常重要。

模型下一轮应该知道：

> L 的价值很高，现在只差证明 L。

而不是从头重新推理。

---

# 0.19 LocalSynthesizer 的优先级应由 Workspace 的“缺口”驱动

搜索对象不再只是 current goal。

定义：

```lean
structure ProofGap where
  id        : GapId
  kind      : GapKind
  target    : Expr
  utility   : Float
  blockers  : Array WorkspaceNodeId
```

Gap 可能是：

```text
一个 helper lemma 未证明
一个 partial term 的 hole
一个 bridge 左半边
一个 existential witness 类型
一个 constructor field
一个 induction invariant 子条件
```

LocalSynthesizer 永远从高价值 Gap 中取任务。

所以 Canonical-like 能力被整个 Workspace 调用，而不是只由主 goal 调用。

---

# 0.20 为纯符号能力保留 Guaranteed Symbolic Lane

如果目标是至少保持强纯符号方法的能力基础，神经 planner 不能把所有预算都抢走。

建议：

```lean
structure ComputeAllocation where
  guaranteedSymbolic : Nat
  adaptiveSymbolic   : Nat
  neuralDirected     : Nat
```

其中 `guaranteedSymbolic` 始终用于：

```text
systematic inhabitation
standard structural search
definitional equality
bounded recursion
local closure
```

即使模型判断错，也不会完全饿死基础 symbolic search。

这不是保证“必然强过某个外部 solver”，但能避免架构上因为神经指导导致基础能力被替换掉。

---

# 0.21 Canonical-like 引擎的正确能力目标

基于 Canonical 的公开定位，它系统性地搜索 dependent type theory 中的 terms，并能证明 theorem、综合 program、构造对象；因此 ViaLean 的 LocalSynthesizer 应把这类能力视为基础层，而不是竞争对手的“终局 tactic”。

目标能力至少包括：

```text
1. inhabit target type
2. enumerate multiple inhabitants
3. construct intermediate typed terms
4. solve helper lemma obligations
5. fill typed holes
6. synthesize witnesses
7. search function/application compositions
8. exploit dependent local context
9. expose definitional equality routes
10. return multiple alternatives, not first success only
```

尤其第 3、5、6、10 对 ViaLean 很关键。

---

# 0.22 Multiple Inhabitants：不要找到第一个就结束

很多时候：

```text
T
```

有多个 inhabitants：

```text
t1 : T
t2 : T
t3 : T
```

它们虽然类型一样，对后续目标价值完全不同。

LocalSynthesizer API 应支持：

```lean
count : Nat
```

返回 bounded top-N / diverse-N。

Workspace 再根据：

```text
后续可连接性
表达式复杂度
新 region 数
模型 value
```

决定保留谁。

Canonical 的 Lean tactic公开支持枚举多个对象的用例，这说明“inhabitation 不只是证明终点，也可以用于对象构造/枚举”本身是自然能力方向。

---

# 0.23 Continuous Co-Search 主循环

建议最终主循环抽象为：

```lean
partial def coSearch
  (ws : ProofWorkspace)
  (model : PlannerSession)
  : SearchM ProofResult := do

  while !ws.solved && !budget.exhausted do

    -- 1. Lean 高频扩展
    let symbolicBurst ← runFastSymbolicBurst ws
    ws.apply symbolicBurst

    -- 2. 处理中间缺口
    let gaps ← ws.highValueGaps
    for gap in gaps.take synthQuota do
      let r ← localSynthesizer.run gap
      ws.apply r

    -- 3. 不一定每轮调用模型
    if shouldOpenNeuralEpoch ws model then
      let delta := ws.deltaSince model.lastSeenVersion
      let batch ← model.reason delta ws.compactView
      let validationBurst ← absorbThoughtBatch ws batch
      ws.apply validationBurst
      model.lastSeenVersion := ws.version

    -- 4. 已经有足够信息时执行高价值 hyperedge
    for edge in chooseExecutionEdges ws do
      let result ← execute edge
      ws.apply result

  return ws.finalize?
```

实际第一版可以单线程实现。

以后再把：

```text
symbolic burst
local synthesis
model inference
```

并行化。

架构上先保证它们共享同一个 versioned Workspace。

---

# 0.24 什么时候再让模型继续“想一段”

触发条件不只是失败。

更好的条件：

```text
Workspace 出现一批新结构
模型上一个 batch 的大部分已经验证完
出现多个新 bridge 候选需要语义判断
当前 high-value gaps 都无法由 local synthesis 快速关闭
出现新的类型/归纳结构
原策略已完成一个阶段
模型明确请求的 symbolic expansion 已结束
```

这时给模型：

```text
过去 batch 的结果 + 新空间
```

让它继续下一段 reasoning。

因此模型 reasoning 是**分段延续**，不是一次 tactic 一次 round。

---

# 0.25 “模型上下文”应该像 IDE 的持续工作区，而不是聊天记录

模型不需要反复收到：

```text
你之前说……
Lean 报错……
你又说……
Lean 又报错……
```

而应该收到：

```text
Workspace v37

New since v31:
  + term m : M
  + helper L1 verified
  + bridge B2 pending on O7
  - witness w3 rejected: type mismatch
  + equality region expanded with 5 transitions

Still open:
  G0
  O7
  O11

Current high-value gaps:
  ...
```

这是“维护状态”的真正含义。

---

# 0.26 第一版无需做真正并发，但接口必须允许并发

工程落地顺序：

## v2.1

单线程 event loop：

```text
Lean burst
→ synth burst
→ neural epoch
→ absorb
→ Lean burst
```

简单、容易调试。

## v2.2

后台 worker pool：

```text
Workspace
 ↙       ↓        ↘
Lean   Synth    Model
 ↘       ↓        ↙
 event queue / versioned commits
```

如果以后并发，需要：

- immutable query snapshot；
- versioned result；
- stale-result validation；
- deterministic commit policy。

但不要一开始就把并发复杂度引入 proof correctness path。

---

# 0.27 文件结构应进一步修改

建议在原完整版基础上新增：

```text
ViaLean/
  Workspace/
    Types.lean
    State.lean
    Event.lean
    Delta.lean
    Hypergraph.lean
    Gap.lean

  Synthesis/
    Types.lean
    Local.lean
    Inhabit.lean
    Partial.lean
    Bridge.lean
    Saturate.lean
    Cache.lean

  Planner/
    Protocol.lean
    Session.lean
    ThoughtBatch.lean
    Absorb.lean
    Memory.lean
```

其中：

```text
Atlas/
```

可以逐步变成 Workspace 的一个“可视化/摘要视图”。

换言之：

> **Workspace 是真实内部状态；Atlas 是 Workspace 在某一预算和视角下的神经/搜索投影。**

这是比“Atlas 就是全部状态”更稳妥的抽象。

---

# 0.28 重新定义 Atlas

最终建议术语：

```text
Proof Workspace
    = 全量持续状态、hypergraph、状态标签、cache、obligations

Proof Atlas
    = 从 Workspace 中抽取出的 bounded strategic view

Expansion Burst
    = Lean/LocalSynthesizer 一次扩张产生的增量

Thought Batch
    = 模型一次较完整 reasoning 后输出的结构化候选集合

Workspace Delta
    = 两个版本之间发生的变化
```

这样概念就清楚了。

---

# 0.29 ViaLean 真正应形成的能力闭环

```text
模型发现“可能缺一个中间对象”
             ↓
提出多个候选 / 结构 / 类型
             ↓
Lean elaboration + LocalSynthesizer
             ↓
不是只说对错
             ↓
围绕成功候选进行 saturation / burst expansion
             ↓
突然产生多条新连接
             ↓
Workspace 持久保存
             ↓
模型看到新增结构后继续一段更高层 reasoning
             ↓
再创造新的中间链接
             ↓
...
             ↓
某些 pending hyperedges 全部关闭
             ↓
完整 Lean proof term
```

这正是：

> **Lean 快速给空间，模型扩大空间，Lean 再把模型创造的空间变成更多真实空间，两者持续循环。**

---

# 0.30 对“至少强过纯符号”的正确工程策略

能力目标应分两层。

## Floor：Symbolic Floor

ViaLean 必须有一条不依赖模型质量的强 symbolic lane：

```text
systematic local term search
dependent inhabitation
structural proof
equality/defeq
bounded recursion
multiple inhabitant enumeration
```

如果能复用 Canonical 或其它强 solver，可通过 adapter；如果不复用，则 benchmark 必须证明自己的 LocalSynthesizer 至少达到可接受基础能力。

## Gain：Neural Gain

神经层必须证明它增加了 symbolically expensive 的能力：

```text
中间 term invention
helper lemma invention
witness invention
bridge discovery
generalization
invariant discovery
proof decomposition
search-space targeting
```

只有：

```text
Hybrid = Symbolic Floor + measurable Neural Gain
```

才能叫真正神经符号增强。

不能把：

```text
纯符号 solver 的 80 分
```

替换成：

```text
较弱 symbolic 60 分 + LLM 补到 75 分
```

然后称为“更强融合”。

---

# 0.31 新增 Benchmark 指标：Middle-Link Contribution

为了验证 LocalSynthesizer/模型不是只在最后一步工作，应记录：

```text
winning proof 中有多少关键对象不是原始 local/context 中已有的？
这些对象在哪个阶段被构造？
是谁提出的？
谁证明/inhabit 的？
它们连接了哪些 region？
```

建议事件：

```json
{
  "event": "middle_link",
  "object": "M",
  "kind": "term_bridge",
  "origin": "neural",
  "validated_by": "local_synthesizer",
  "introduced_at_depth": 1,
  "used_at_depth": 4,
  "closed_descendants": 7
}
```

核心指标：

```text
Middle-Link Hit Rate
Bridge Utility
Conjecture Promotion Rate
Synthesized-Term Reuse
Average Model Calls per Solved Theorem
Workspace Growth per Neural Epoch
```

如果模型每轮输出后 Lean 只增加 1 个节点，架构还没有发挥出来。

真正理想的是：

```text
一个高质量 neural batch
→ 多个可验证 seed
→ Lean burst 产生几十个有结构的新连接
```

---

# 0.32 最终一句架构定义

ViaLean-v3 应定义为：

> **一个 persistent co-search theorem prover：Lean 的符号引擎持续、高频地维护和扩展 versioned proof workspace；Canonical-like local synthesis 在搜索全过程中构造 inhabitants、partial-term fillings 和中间连接；神经模型以较低频率读取 workspace 增量并一次提出一批高语义中间对象和搜索方向。模型的每个想法都被独立吸收、验证和扩张，局部失败不会抹掉整段 reasoning。最终 proof 是这种持续共搜索逐步收敛出的完整 Lean term。**


# 0.5 关键架构修正：从 Closed-World Atlas 升级为 Open-World Conjecture Atlas

本节是对全文最重要的增强。

ViaLean 不能把“更广视野”理解成：

```text
Lean 当前 goal
  ↓
Lean 多展开几层
  ↓
模型在这些现成 future 中选一个
```

这仍然是 **closed-world symbolic search**：候选世界的边界完全由当前符号枚举器决定。模型即使很聪明，也只能在 Lean 已经生成的菜单中排序。

真正需要的架构是：

```text
                    theorem / global context
                              │
              ┌───────────────┴────────────────┐
              │                                │
              ▼                                ▼
      Symbolic Atlas Builder          Neural Conjecture Engine
              │                                │
      已知可验证 future                 主动创造新的中间对象
              │                                │
              │                 ┌──────────────┼──────────────┐
              │                 │              │              │
              │                 ▼              ▼              ▼
              │             helper lemma     witness      bridge term
              │                 │              │              │
              │                 ▼              ▼              ▼
              │             invariant      generalization  proof split
              │                                │
              └────────────────┬───────────────┘
                               ▼
                  Open-World Proof Atlas
                               │
            verified nodes + speculative conjectures
                               │
                               ▼
                       Lean validation/refinement
                               │
               ┌───────────────┴───────────────┐
               ▼                               ▼
          conjecture useful                reject/prune
               │
               ▼
         turn into obligations
               │
               ▼
        symbolic/neural planning
```

核心区别：

> **符号系统负责枚举“眼前能严格推出什么”；神经系统负责提出“也许应该先证明什么”。**

后者才是 ViaLean 超过纯局部符号搜索的主要能力来源。

---

# 0.6 设计目标：不要只比“排序”，要增加纯符号搜索没有的候选空间

Canonical 一类系统的强项是系统性搜索 dependent type theory 中的 inhabitants。ViaLean 如果仅仅：

```text
相同 symbolic action space
+ 一个更好的 LLM ranker
```

那么本质贡献主要是搜索次序优化。

ViaLean 应增加一个纯符号 bounded enumeration 很难低成本覆盖的候选空间：

```text
Intermediate Lemma Space
Witness Space
Generalization Space
Invariant Space
Bridge Expression Space
Auxiliary Definition Space
Target Transformation Space
Proof Decomposition Space
```

即神经模型不仅预测：

```text
下一步用哪个已有动作
```

还预测：

```text
为了让证明变简单，现在缺少什么中间数学对象？
```

这类“对象创造”必须成为一级接口。

---

# 0.7 三类 Atlas 节点

新的 Atlas 不应把所有节点都当成已经成立。

建议明确分层。

## A. Verified Node

Lean 已验证真实可达：

```lean
structure VerifiedAtlasNode where
  goalKey   : GoalKey
  snapshot  : GoalSnapshot
  proofPath : ...
```

可以安全用于搜索。

## B. Speculative Conjecture

模型提出的中间数学对象：

```lean
structure ConjectureNode where
  id          : ConjectureId
  statement   : Expr
  kind        : ConjectureKind
  origin      : ConjectureOrigin
  confidence  : Float
  expectedGain : Float
  status      : ConjectureStatus
```

重要：

> `ConjectureNode` 不是 local hypothesis，不能因为模型提出就放进 Lean context 当作真命题。

## C. Obligation Node

当系统决定尝试一个 conjecture 后，把它转换成合法 proof obligations。

例如模型提出：

```text
中间引理 L
```

系统使用 cut：

```text
原目标：Γ ⊢ G

变成：
  O1: Γ ⊢ L
  O2: Γ, h : L ⊢ G
```

只有 O1、O2 都成功，conjecture 才形成真实证明。

因此 speculative reasoning 可以很激进，而 proof correctness 完全不受影响。

---

# 0.8 Neural Conjecture Engine

建议新增一级模块：

```text
ViaLean/Conjecture/
  Types.lean
  Generator.lean
  Validate.lean
  Rank.lean
  Compile.lean
  Memory.lean
```

其职责不是执行 tactic，而是主动提出中间对象。

---

## 0.8.1 ConjectureKind

建议：

```lean
inductive ConjectureKind
  | helperLemma
  | equalityBridge
  | iffBridge
  | existentialWitness
  | intermediateValue
  | inductionInvariant
  | inductionGeneralization
  | auxiliaryFunction
  | targetReformulation
  | contradictionTarget
  | caseSplitPredicate
  | cutFormula
  | usefulDefinition
```

---

## 0.8.2 Helper Lemma

例如当前：

```text
Γ ⊢ G
```

模型预测：

```text
L 很可能是通往 G 的桥梁
```

ViaLean 不直接假设 L，而构造：

```text
Γ ⊢ L
Γ, L ⊢ G
```

然后并行/分预算搜索。

模型可以一次提出多个：

```text
L1, L2, L3, ...
```

Lean 做廉价筛选后，只把最有价值的加入 Atlas。

---

## 0.8.3 Equality Bridge

当前 goal：

```text
a = c
```

local 中没有直接 rewrite 路径。

模型可以主动提出中间表达式：

```text
b
```

并建议：

```text
a = b
b = c
```

Atlas 形成：

```text
             a = c
            /     \
       prove a=b   prove b=c
```

这类 bridge term 是纯局部 tactic enumeration 很容易错过、但语言模型可能从语义上发现的结构。

---

## 0.8.4 Intermediate Value / Witness

对于：

```lean
⊢ ∃ x, P x
```

symbolic search 只有在 witness 候选已经存在或可枚举时容易处理。

Neural Conjecturer 可以提出：

```text
w₁
w₂
w₃
```

Lean 先做：

```text
typecheck(wᵢ)
```

再把候选编译为：

```text
⊢ P wᵢ
```

这些 witness 可以来自：

- local expressions 的组合；
- 数学模式；
- retrieved theorem；
- 模型生成的结构化 term；
- 先前 proof memory。

---

## 0.8.5 Induction Invariant / Generalization

困难证明经常不是“下一 tactic 不知道”，而是 theorem statement 对 induction 不友好。

模型应该能提出：

```text
先 generalize x
强化 induction hypothesis
引入 invariant I
换 induction variable
```

例如生成：

```text
原目标 G x

增强目标：
∀ y, R x y → G' x y
```

系统必须把这种建议编译成**可验证的 goal transformation**，而不是让模型自由改 theorem。

最终仍需要证明增强后的 lemma，再实例化回原目标。

---

# 0.9 Conjecture 必须经过四级筛选

模型可以“想得很远”，但不能让 Lean 为每个幻想付高昂代价。

建议四级筛选：

## Stage 1：Well-formedness

检查：

```text
表达式能否在当前 Environment / local context 中 elaboration？
类型是否正确？
free variables 是否合法？
```

失败立即丢弃。

## Stage 2：Cheap symbolic relevance

检查：

- 是否和 target/local 有共享 head symbol；
- 是否减少某个结构复杂度；
- 是否连接两个现有 region；
- 是否与 retrieved premise 可组合；
- 是否只是 target 的 trivial restatement；
- 是否已经存在等价 conjecture。

## Stage 3：Bounded proofability probe

给 conjecture 一个很小预算：

```text
native/Canonical-like leaf search
simp
exact/apply
equality closure
```

如果很容易证明，直接升级成 verified fact。

## Stage 4：Strategic value

如果暂时难证，但它作为 cut 能显著降低主目标复杂度，则仍可进入 speculative Atlas。

---

# 0.10 Bidirectional Proof Search：从 Goal 与 Context 两端相向而行

要获得真正广视野，不应只有：

```text
goal → backwards
```

也不能只有：

```text
locals → forward closure
```

建议建立：

```text
Forward Symbolic Closure
        ↓
    forward facts
        │
        │
        │      Neural Bridge Generator
        │              ↓
        ├────── intermediate lemma / term ──────┐
        │                                       │
        ▼                                       ▼
 local semantic region                    target region
                                                ▲
                                                │
                                      Backward obligations
```

模型的价值尤其体现在：

> 找到 forward region 与 backward region 之间的“桥”。

---

# 0.11 Meet-in-the-Middle 评分

定义一个 conjecture `C` 的价值，不只是“像不像答案”。

可以估计：

```text
bridgeScore(C) =
    relevanceToKnownFacts(C)
  + relevanceToTarget(C)
  + symbolicReachabilityFromContext(C)
  + symbolicReachabilityToGoal(C)
  - proofCost(C)
  - expressionComplexity(C)
```

模型负责 semantic relevance。

Lean 负责：

```text
reachability
type correctness
cheap proofability
actual transition cost
```

两者组合才能形成真正 neuro-symbolic score。

---

# 0.12 Canonical 不应只是 benchmark，也可以成为 ViaLean 的局部执行器

如果项目目标是“至少不弱于优秀纯符号方法，并在需要语义跳跃的题上更强”，最稳妥的架构不是重新实现所有纯符号 inhabitation 能力，而是允许：

```text
ViaLean Planner
     ↓
Proof Atlas
     ↓
LeafRouter
 ┌───────────────┬────────────────┐
 │ ViaLeanNative │ CanonicalBridge│
 └───────────────┴────────────────┘
```

原则：

> **纯符号 solver 擅长的低深度/局部 inhabitant 搜索，ViaLean 应复用或至少公平对标；ViaLean 自己的增益集中在“提出搜索空间中原本不存在的中间对象”和“把计算投向正确 proof basin”。**

这样才能形成能力叠加，而不是和成熟符号 solver 在同一层面重复竞争。

注意：

- 外部 solver 只能作为 proposal/leaf backend；
- 返回结果仍需转成 Lean 可检查 proof；
- shared deadline 必须统一；
- 依赖应可选，ViaLean core 不必强绑定某个 solver。

---

# 0.13 “强过 Canonical”必须定义成实验目标，而不是架构宣称

不能因为引入 LLM 就直接宣称更强。

建议把目标写成：

> **ViaLean-v2 的实验目标是：在保留或接近强纯符号 inhabitation solver 对局部、低深度问题能力的同时，在需要 helper lemma、semantic bridge、witness invention、generalization 或 invariant discovery 的问题上获得显著额外 solve rate。**

必须测试两类题：

## Symbolic-local set

偏向：

```text
type inhabitation
structural recursion
constructor/apply
dependent local reasoning
```

这里不能因为 neural planner 反而退化很多。

## Semantic-jump set

专门设计需要：

```text
中间引理
不显然 witness
等式桥
归纳强化
generalization
辅助定义
多阶段 decomposition
```

这里才是 ViaLean 必须显著超过纯局部 enumeration 的地方。

---

# 0.14 新的系统核心：Atlas 不是“未来列表”，而是“可验证世界 + 可检验假设”

最终建议使用：

```text
                    Open-World Proof Atlas
    ┌─────────────────────────────────────────────┐
    │                                             │
    │  VERIFIED WORLD                             │
    │  - Lean states                              │
    │  - executable transitions                   │
    │  - derived facts                            │
    │  - proven helper lemmas                     │
    │                                             │
    │  SPECULATIVE WORLD                          │
    │  - helper lemma conjectures                 │
    │  - witness candidates                       │
    │  - intermediate values                      │
    │  - invariants                               │
    │  - generalizations                          │
    │  - bridge expressions                       │
    │                                             │
    │  OBLIGATION WORLD                           │
    │  - proof obligations generated by cuts      │
    │  - dependencies among conjectures           │
    │  - verification status                      │
    │                                             │
    └─────────────────────────────────────────────┘
                         │
                         ▼
                  Neural Planner
                 /      |       \
          choose      invent     expand
          region     conjecture  region
                 \      |       /
                         ▼
                 Symbolic Validator
                         │
                         ▼
                     Lean kernel
```

这比“Lean 提前输出一点点东西给模型”更接近真正的神经符号统一系统。


# 1. 项目演进目标

ViaLean 当前已经有一个正确且有研究价值的起点：

```text
Lean Goal
   ↓
symbolic proposals
   ↓
diversity-balanced frontier
   ↓
bounded future paths
   ↓
symbolic scheduler / optional model
   ↓
replay
   ↓
recursive obligations
   ↓
final proof validation
```

下一步不应该简单变成：

```text
更多 LLM 调用
更多 tactic candidates
更多 feedback round
更多 prompt engineering
```

而应该变成：

```text
Lean symbolic state
        ↓
structured proof atlas
        ↓
neural strategic planning
        ↓
symbolic execution / refinement
        ↓
incremental atlas update
        ↓
conditional replanning
        ↓
verified proof
```

目标不是“LLM 更会写 tactic”，而是：

1. 模型看到更宽的证明空间；
2. 模型能比较多个未来，而不是只判断当前一步；
3. 模型能预测一条策略的长期价值；
4. 符号系统主动暴露长尾但合法的证明路线；
5. 失败不会自动触发“再问模型一次”；
6. 模型的判断可以错，但不能破坏 proof correctness；
7. 模型调用是稀疏、高价值、基于结构变化触发的；
8. 无模型时，ViaLean 仍是完整可工作的 symbolic prover。

---

# 2. 当前实现的正确定位

当前代码已经具备以下重要基础，不应推翻：

- `FrontierEngine.build` 会构造多个 perspective；
- 包含 normalization / contradiction / rewrite / elimination / construction / backward / forward / equality / future；
- 顶层 atlas 使用 perspective quota + 交错合并，避免单一 family 完全淹没其它 family；
- future graph 已能做 bounded multi-operator lookahead；
- model policy mode 可以给 action score；
- interactive mode 可以看到 frontier、future 和 feedback；
- replay 在 fresh goal 上执行；
- model 生成的 partial tactic 后续 obligations 会交给普通 symbolic search；
- 失败分支恢复 Meta state；
- 最终 proof 经 `finalizeProof` 检查；
- native solver 与主搜索逻辑概念上已经分离；
- provider、protocol、guidance 已经拆成独立模块。

所以修改方向不是重写项目，而是把：

> “模型看到一些 future preview”

升级为：

> “Atlas 成为系统一级数据结构，模型围绕 Atlas 做规划和价值判断”。

---

# 3. 目标架构总览

最终建议架构：

```text
                           ┌──────────────────────┐
                           │      Lean Goal       │
                           └──────────┬───────────┘
                                      │
                                      ▼
                           ┌──────────────────────┐
                           │  GoalSnapshot/GoalKey│
                           └──────────┬───────────┘
                                      │
                                      ▼
                    ┌────────────────────────────────┐
                    │         Proof Atlas IR         │
                    │                                │
                    │ nodes      transitions         │
                    │ regions    symbolic signals    │
                    │ costs      obligations         │
                    │ facts      proof opportunities │
                    └───────────┬───────────┬────────┘
                                │           │
                 symbolic prior │           │ neural view
                                ▼           ▼
                     ┌──────────────┐  ┌───────────────┐
                     │ Local Search │  │ Neural Planner│
                     │ / Scheduler  │  │ Policy/Value  │
                     └──────┬───────┘  └───────┬───────┘
                            │                  │
                            └────────┬─────────┘
                                     ▼
                           ┌──────────────────────┐
                           │ Search Decision      │
                           │ region / transition  │
                           │ expand / execute     │
                           └──────────┬───────────┘
                                      │
                                      ▼
                           ┌──────────────────────┐
                           │ Symbolic Executor    │
                           │ typed operations     │
                           └──────────┬───────────┘
                                      │
                     ┌────────────────┴────────────────┐
                     ▼                                 ▼
             transition success                 transition failure
                     │                                 │
                     ▼                                 ▼
           child ProofState(s)                 StructuredObservation
                     │                                 │
                     └────────────────┬────────────────┘
                                      ▼
                              Atlas incremental update
                                      │
                        material change? / uncertainty?
                              │               │
                             no              yes
                              │               │
                         local search       replan
                              │               │
                              └───────┬───────┘
                                      ▼
                           ┌──────────────────────┐
                           │   proof completed?   │
                           └──────────┬───────────┘
                                      │ yes
                                      ▼
                              finalizeProof
                                      │
                                      ▼
                                  Lean kernel
```

---

# 4. 核心设计原则

## 4.1 Atlas 是第一公民，不是 prompt 附件

当前 `FrontierProbe.future : Array SymbolicFutureView` 更像一个给模型展示的 preview。

未来应提升为：

```lean
structure ProofAtlas where
  root      : AtlasNodeId
  nodes     : ...
  edges     : ...
  regions   : ...
  facts     : ...
  stats     : AtlasStats
```

搜索器、scheduler、planner、trace、benchmark 全部围绕同一个 Atlas 工作。

---

## 4.2 模型默认不输出 Lean tactic

长期默认协议应该是：

```text
模型：
  - 评估区域
  - 评估节点
  - 给 strategy
  - 请求继续展开某区域
  - 指示应该优先执行哪条 typed transition

Lean：
  - 创建 transition
  - 执行 transition
  - 管理 MVar
  - 递归求解
  - 验证最终 proof
```

模型自由生成 Lean code 可以保留为实验 escape hatch，但不应成为神经符号主路径。

---

## 4.3 Replanning，不是 Retry

错误模式：

```text
model -> tactic A -> fail
model -> tactic B -> fail
model -> tactic C -> fail
```

目标模式：

```text
Atlas A0
   ↓
planner chooses region R
   ↓
symbolic execution
   ↓
observation changes local proof world
   ↓
Atlas A1
   ↓
only if A1 materially differs:
      planner re-evaluates
```

模型调用由“轮数”驱动，改成由“信息增益 / 状态变化”驱动。

---

## 4.4 神经输出永远是 untrusted heuristic

任何 neural score：

```text
policy
value
strategy
uncertainty
region preference
expansion request
```

都不能直接构成 proof。

证明正确性仍完全来自：

```text
Lean Meta construction
+ final reconstructed Expr
+ inferType
+ isDefEq
+ no unresolved MVars
+ chosen axiom policy
```

---

# 5. 当前代码必须先修的工程问题

以下修复建议先于大规模神经符号重构。

---

## P0-1：Model tactic sandbox 不能依赖 namespace prefix

### 当前问题

`Search.lean` 中当前安全检查允许：

```text
Lean.Parser.Tactic.*
Lean.Parser.Term.*
```

并用关键字黑名单拒绝：

```text
run_tac
eval
native
set_option
command
macro
...
```

问题在于：

> namespace 前缀不是 capability boundary。

如果宿主 Environment 中加载额外 syntax/elaborator，仅靠 parser kind 字符串前缀不足以证明该语法就是 ViaLean 希望开放的“纯核心证明能力”。

### 必改

短期：

```lean
inductive AllowedModelSyntax
  | exact
  | apply
  | intro
  | constructor
  | cases
  | rw
  | simp
  | assumption
  | contradiction
  | rfl
```

维护**精确 syntax-kind allowlist**。

长期：

直接取消主路径中的 arbitrary Lean tactic text，改成 Typed Planner Action DSL，见第 16 节。

### 完成标准

- 第三方 tactic extension 无法通过 sandbox；
- command / macro / option / native / `run_tac` 均拒绝；
- 合法能力 unit test 全覆盖；
- 失败后 Meta state 无污染；
- model tactic mode 默认关闭或标为 experimental。

---

## P0-2：Goal fingerprint 必须包含 let semantics

### 当前问题

`Goal.lean` 中 `LocalInfo` 有：

```lean
isLet : Bool
```

但是 fingerprint 只 hash：

```text
target
local.type
```

没有包含 let value。

例如：

```lean
let x : Nat := 1
```

与：

```lean
let x : Nat := 100
```

可能拥有相同 target/type 形状，却不应当在搜索 cycle 语义上被无条件当成同一状态。

### 更大的问题

当前搜索 path 直接保存 `UInt64 fingerprint`。

hash collision 不影响 kernel soundness，但会造成错误剪枝：

```text
实际没访问过
→ hash 撞了
→ 被当成 cycle
→ 搜索 completeness 降低
```

### 修改

新增：

```lean
inductive LocalDeclKind
  | local
  | letDecl

structure LocalKey where
  kind   : LocalDeclKind
  type   : Expr
  value? : Option Expr

structure GoalKey where
  target : Expr
  locals : Array LocalKey
```

`UInt64` 只作为 bucket/index：

```lean
def GoalKey.hash : UInt64
```

逻辑相等需要结构确认。

---

## P0-3：统一 `Goal.lean` 与 `Fingerprint.lean`

当前 `Fingerprint.lean` 已有：

```lean
goalFingerprint
```

而 `Goal.snapshot` 又重复实现一次 locals fold hash。

应删除重复逻辑。

目标：

```lean
Goal.snapshot
  ↓
mkGoalKey
  ↓
GoalKey.hash
```

全仓库只有一个 Goal identity implementation。

---

## P1-1：`frontierMaxProbes` 必须和“工作预算”分开

### 当前行为

`FrontierEngine.build` 先分别计算多个 perspective：

```text
normalization
contradiction
rewrites
elimination
construction
backward
forward
equality
deepFuture
```

之后才交错合并，并在 `frontierMaxProbes` 达到后停止输出。

所以：

```text
frontierMaxProbes = 32
```

限制的是：

> 最终 Atlas 输出数

不是：

> Atlas 构造总工作量

### 修改

增加：

```lean
structure AtlasBudget where
  maxTransitionsTried : Nat
  maxNodesCreated     : Nat
  maxMetaOps          : Nat
  maxRenderedChars    : Nat
```

并与全局 deadline 共同工作。

每个 producer 在执行真正 Meta probe 前必须消费预算。

---

## P1-2：Future expansion 固定 operator 顺序造成偏置

当前 future 大致按：

```text
intro
simp
local apply*
constructor*
cases*
rewrite*
```

依序尝试并受 `frontierFutureWidth` 限制。

如果 local apply 很多，就可能吃满 width，后面的 cases/rewrite 没机会出现。

### 修改

每个 future node 内也使用 family-diverse 调度：

```text
intro queue
normalization queue
backward queue
construction queue
elimination queue
rewrite queue
forward queue
equality queue
```

循环每个 family 取最多一个 child。

即：

> diversity 不只是顶层 atlas 的性质，而是整个 future graph 的不变量。

---

## P1-3：Interactive model prompt 需要真正的 global hard cap

当前 `buildRequest` 会按 `modelContextChars` 给：

```text
target
locals
actions
```

分配预算。

但 `buildInteractionRequest` 在 base 后直接加入：

```text
frontier
feedback
```

因此 `modelContextChars` 并不是最终 serialized request 的硬上限。

### 修改

新增统一：

```lean
structure ModelPayloadBudget where
  maxChars : Nat
  maxAtlasNodes : Nat
  maxFeedback : Nat
```

最终 JSON 序列化后再验证：

```text
serialized.length <= maxChars
```

否则必须继续裁剪。

---

## P1-4：`ucb=true` 与 `deterministic=true` 语义冲突

当前默认同时：

```lean
ucb := true
deterministic := true
```

而排序实现里：

```text
deterministic || !ucb
→ 使用 prior
```

所以默认 `ucb=true` 实际不起作用。

### 修改

改为：

```lean
inductive RankingMode
  | prior
  | ucb
  | planner
  | hybrid
```

确定性单独描述：

```lean
stableTieBreak : Bool
```

UCB 本身完全可以 deterministic。

---

## P1-5：`maxCandidates` 拆义

当前名称容易理解为：

> 当前 node 的全局 action 上限

但实际主要影响 premise retrieval。

改成：

```lean
maxRetrievedPremises
maxActionsPerNode
maxCandidatesPerFamily
```

严格定义三者。

---

## P1-6：`Proposal.family` 不再解析字符串

当前：

```text
source.startsWith "external"
source.startsWith "local"
source.startsWith "library"
```

决定 family。

改为：

```lean
inductive ProposalOrigin
  | local
  | library (name : Name)
  | external
  | normalization
  | derived
  | planner
```

source string 只用于 trace/render。

---

## P1-7：LeafRouter 必须接入主路径

当前已有：

```lean
structure LeafRouter where
  backends : Array LeafSolver
```

但 `Search.directProof?` 仍直接调用：

```lean
solveWithNative
```

所以 Router 只是形式抽象。

### 修改

`SearchState` 持有：

```lean
router : LeafRouter
```

所有 direct/leaf solve 都：

```text
Search → LeafRouter → Native/Other
```

---

## P1-8：拆分 `Search.lean`

建议目标：

```text
ViaLean/Search/
  State.lean
  Controller.lean
  Expand.lean
  Execute.lean
  Replay.lean
  Ranking.lean
  Replan.lean
  Observation.lean
```

不要继续让 `Search.lean` 同时拥有：

- model syntax sandbox；
- feedback；
- ranking；
- recursive search；
- replay；
- direct solver；
- interactive round；
- model candidate execution。

---

# 6. Proof Atlas：神经符号共享中间表示

这是整个重构最重要的部分。

当前 `FrontierProbe` 是：

```text
id
perspective
operation
source
result
executable
subject?
constructor?
symm
goals
facts
future[]
```

其中大量字段是字符串视图。

新的 Atlas 应区分：

```text
内部 executable representation
外部 serializable neural view
```

---

## 6.1 内部结构

建议：

```lean
abbrev AtlasNodeId := UInt64
abbrev TransitionId := UInt64
abbrev RegionId := UInt64

structure AtlasNode where
  id          : AtlasNodeId
  key         : GoalKey
  snapshot    : GoalSnapshot
  depth       : Nat
  parent?     : Option AtlasNodeId
  solved      : Bool := false
  terminal    : Bool := false
  signals     : SymbolicSignals
  estimatedCost : Float := 1.0

structure AtlasTransition where
  id          : TransitionId
  parent      : AtlasNodeId
  operation   : SymbolicOperation
  children    : Array AtlasNodeId
  family      : StrategyFamily
  executable  : Bool
  coupled     : Bool
  cost        : TransitionCost
  evidence    : TransitionEvidence

structure ProofAtlas where
  root        : AtlasNodeId
  nodes       : Std.HashMap AtlasNodeId AtlasNode
  transitions : Std.HashMap TransitionId AtlasTransition
  outgoing    : Std.HashMap AtlasNodeId (Array TransitionId)
  regions     : Array ProofRegion
  stats       : AtlasStats
```

---

## 6.2 Atlas 必须是图，不是字符串 future list

原因：

假设：

```text
S0 --rw h1--> S1
S0 --simp-->  S2
S1 --simp-->  S3
S2 --rw h1--> S3
```

现在如果只是 `path : String`：

```text
rw:h1/simp
simp/rw:h1
```

模型看到两个路径，但实际上它们汇合到同一个状态 `S3`。

真正图结构能告诉模型：

> 两条策略都进入同一 proof basin。

这对 value estimation、搜索预算、去重都非常重要。

---

## 6.3 Region 概念

不要让模型对几十个 node 逐个看。

Atlas 应聚类出策略区域：

```lean
inductive StrategyFamily
  | normalization
  | contradiction
  | equality
  | elimination
  | construction
  | backward
  | forward
  | witness
  | cut
  | structural
  | mixed

structure ProofRegion where
  id             : RegionId
  family         : StrategyFamily
  entryNodes     : Array AtlasNodeId
  representative : Array AtlasNodeId
  size           : Nat
  minDepth       : Nat
  maxDepth       : Nat
  signals        : RegionSignals
```

模型先做粗规划：

```text
哪个 region 值得投入？
```

再做细规划：

```text
region 内哪个 transition 最值得执行？
```

这种 coarse-to-fine 视野远好于一次塞几十个 tactic。

---

# 7. Goal identity / 状态等价

新的 Atlas 必须依赖正确的状态身份。

---

## 7.1 严格 Search Key

用于：

- cycle detection；
- transposition；
- Atlas node dedup。

必须足够严格。

建议：

```lean
structure GoalKey where
  targetHash      : UInt64
  localDeclHashes : Array UInt64
  structuralHash  : UInt64
```

但底层应能在 hash 相同时做 semantic/structural confirmation。

---

## 7.2 Guidance Key 可以更宽松

Planner cache 不一定必须严格等同。

可以做：

```lean
structure GuidanceKey where
  shape          : GoalShape
  normalizedGoal : ...
  localFeatures  : ...
```

这样近似类似状态可以共享 planner prior。

必须明确区分：

```text
Search equality != Neural cache similarity
```

---

## 7.3 α-renaming

不要因为：

```lean
h1 : P
```

改名成：

```lean
foo : P
```

就认为 proof state 本质不同。

所以 `GoalKey` 默认不要把 user-facing binder name 当核心语义。

---

# 8. Symbolic transition 统一动作层

当前系统有：

```text
Proposal
ProofAction
FrontierProbe
StructuralRule
model Lean candidate
```

多个动作概念。

未来建议建立统一 IR：

```lean
inductive SymbolicOperation
  | exactLocal (fvar : FVarId)
  | applyLocal (fvar : FVarId)
  | applyConst (name : Name)
  | intro
  | constructor (name : Name)
  | casesLocal (fvar : FVarId)
  | rewriteLocal (fvar : FVarId) (symm : Bool)
  | simplifyTarget
  | contradiction
  | equalityBridge (...)
  | iffBridge (...)
  | witness (...)
  | cut (...)
```

然后：

```lean
structure SymbolicTransitionCandidate where
  operation : SymbolicOperation
  family    : StrategyFamily
  prior     : Float
  estimatedCost : Float
  origin    : TransitionOrigin
```

所有：

```text
proposer
frontier
planner
scheduler
replay
```

统一操作这个类型。

---

# 9. Atlas Builder 与全局预算

---

## 9.1 Producer 模型

当前 `build` 是 eager：

```text
build normalization array
build contradiction array
build rewrite array
...
merge
```

目标改成 lazy/fair producer：

```lean
structure AtlasProducer where
  family : StrategyFamily
  next?  : State → MetaM (Option Candidate × State)
```

逻辑：

```text
while budget.open && atlas.notFull:
    for producer in producers:
        candidate? ← producer.next?
        if candidate:
            probe/execute observation
            insert node/transition
```

这样：

- 真正做到 global work bound；
- 天然 family fairness；
- 更容易加入 planner-directed expansion；
- 不需要先把所有 family 算完。

---

## 9.2 两种预算分开

### Exploration budget

限制：

```text
多少 symbolic Meta 操作
多少 transition 尝试
多少新 Atlas node
```

### Representation budget

限制：

```text
多少节点发给模型
多少字符/token
多少 region
多少 signals
```

不能混成一个 `frontierMaxProbes`。

---

## 9.3 预算建议

```lean
structure AtlasLimits where
  maxNodes            : Nat := 96
  maxTransitions      : Nat := 160
  maxTransitionsTried : Nat := 256
  maxDepth            : Nat := 3
  maxWidthPerNode     : Nat := 8
  maxPerFamilyPerNode : Nat := 2
  maxRegions          : Nat := 12
  maxFacts            : Nat := 32
```

实际默认值需要 benchmark 决定，不要直接固定以上数字。

---

# 10. Diversity：从顶层 Frontier 扩展到完整 Future Atlas

Diversity 应成为系统 invariant。

---

## 10.1 三层 diversity

### Layer A：Operator diversity

```text
rewrite
cases
apply
constructor
normalize
...
```

不能相互挤占全部预算。

### Layer B：Premise diversity

`apply` family 内：

```text
local premise
library premise
forward-derived premise
```

也应有限额。

### Layer C：Outcome diversity

即使两个操作 family 不同，如果生成：

```text
几乎相同的 child goal
```

也不应该都占 Atlas 预算。

可以基于 `GoalKey` / normalized shape 做 outcome dedup。

---

## 10.2 Rare strategy reserve

为了项目核心“长尾策略可见”，建议保留：

```lean
rareReserve : Nat
```

即无论 prior 多低，以下策略至少保留少量候选：

```text
case split
reverse rewrite
non-obvious constructor
intermediate equality
cut
witness
```

这比简单 top-k 更符合 ViaLean 的研究定位。

---

# 11. Neural Planner：模型从 tactic generator 升级为规划器

新的模型接口不要问：

> “下一步写什么 Lean？”

而问：

> “根据当前 proof atlas，哪一片未来最有价值？为什么？如果现有 atlas 信息不够，应该往哪里继续符号展开？”

---

## 11.1 Planner 输入

至少：

```text
Problem summary
Root goal
Important local dependencies
Atlas regions
Representative nodes
Transitions
Derived facts
Branch complexity
Known dead regions
Budget remaining
Previous strategy
Structured observations
```

注意：

> 不要默认发送完整 raw proof history。

发送的是当前结构化世界状态。

---

## 11.2 Planner 输出

建议：

```lean
structure PlannerDecision where
  rootValue          : Float
  confidence         : Float
  preferredRegions   : Array RegionScore
  transitionScores   : Array TransitionScore
  strategy           : StrategyPlan
  expansionRequests  : Array ExpansionRequest
  avoid              : Array AvoidDirective
```

模型不能直接提供 proof。

---

# 12. Policy + Value + Uncertainty

当前 model guidance 已有：

```text
value
actionScores
```

这个方向应该保留并扩大。

---

## 12.1 Policy

```text
P(transition | atlas)
```

回答：

> 当前 Atlas 里哪条 transition 最值得执行？

---

## 12.2 Value

```text
V(node | atlas context)
```

回答：

> 进入这个 state 后，最终证明成功的前景如何？

---

## 12.3 Cost

符号侧估计：

```text
expected branch count
goal size increase
new metavars
premise application cost
historical solver cost
```

---

## 12.4 Uncertainty

模型应该允许输出：

```text
confidence
```

若：

```text
value 高但 uncertainty 高
```

系统可以选择：

> 先继续 symbolic expand 这个 region，再决策。

这比直接执行更合理。

---

## 12.5 最终综合分数

例如：

```text
score(t) =
    α * symbolicPrior(t)
  + β * neuralPolicy(t)
  + γ * neuralValue(children(t))
  + δ * novelty(t)
  + ε * diversityBonus(t)
  - ζ * expectedCost(t)
  - η * uncertaintyPenalty(t)
```

所有权重都应 benchmark/ablation。

不要硬编码成无法解释的“神秘分数”。

---

# 13. Strategy / Region / Expansion Request

真正有意义的 planner 不只选 transition。

它还应输出高层策略。

---

## 13.1 StrategyPlan

```lean
structure StrategyPlan where
  primaryFamily  : StrategyFamily
  secondary      : Array StrategyFamily
  objective      : String
  horizon        : Nat
  stopCondition  : StrategyStopCondition
```

例如：

```text
Primary: elimination
Objective:
  split hOr, seek contradiction in first branch,
  expose equality in second branch.
```

---

## 13.2 ExpansionRequest

模型可以说：

```text
现在信息不足，不要执行；
请把 equality region 再展开两层。
```

结构：

```lean
structure ExpansionRequest where
  regionId       : RegionId
  family?        : Option StrategyFamily
  extraDepth     : Nat
  extraWidth     : Nat
  reasonCode     : ExpansionReason
```

Lean 侧仍检查全局预算，不一定接受全部请求。

这就是神经与符号真正“协同”：

> 模型决定哪里值得花 symbolic compute，符号引擎负责安全展开。

---

# 14. Replan：替代反复试错

---

## 14.1 不再用固定 `modelMaxRounds` 作为核心逻辑

`modelMaxRounds` 可以保留为安全 cap。

但触发 model query 应改为：

```lean
def shouldReplan
  (oldAtlas : ProofAtlas)
  (newAtlas : ProofAtlas)
  (obs : Array Observation)
  (plan : StrategyPlan)
  : Bool
```

---

## 14.2 建议 Replan 条件

满足任一：

- 当前 plan 指定 region 已耗尽；
- 执行结果与预测结构明显不同；
- 产生高价值新事实；
- 出现新的 contradiction/equality opportunity；
- subgoal count 超出计划；
- 当前 strategy 连续多个 transition 被结构性证伪；
- uncertainty 高且新 Atlas 提供了更多信息；
- 预算状态发生阶段切换；
- planner 请求的 expansion 已完成。

---

## 14.3 不触发 Replan 的情况

以下不应自动调用模型：

- 某一个 equivalent rewrite 失败；
- 某一个 local apply unification 失败；
- 同 family 还有大量已评分替代项；
- 当前 strategy 仍然成立；
- symbolic solver 能直接关闭 child；
- 只是 compiler error text 变化但 proof state 没变化。

---

# 15. Structured Observation：替代错误文本聊天

当前 `SearchFeedback` 主要是：

```text
goal string
action
outcome string
elapsedMs
detail string
```

升级为：

```lean
inductive FailureClass
  | unification
  | noProgress
  | branchExplosion
  | timeout
  | contradictionNotFound
  | rewriteNoMatch
  | premiseMismatch
  | openGoals
  | invalidPlannerSelection
  | budgetDenied
  | internal

structure SearchObservation where
  transitionId   : TransitionId
  parentNode     : AtlasNodeId
  outcome        : ObservationOutcome
  failureClass?  : Option FailureClass
  childNodes     : Array AtlasNodeId
  changedFacts   : Array FactDelta
  branchDelta    : Int
  complexityDelta : Int
  elapsedMs      : Nat
```

---

## 15.1 Error text 只作 debug 字段

可以保留：

```lean
debugDetail? : Option String
```

但 planner 的主输入应该是：

```text
failureClass
state delta
new facts
pruned nodes
```

而不是 Lean exception 原文。

---

# 16. Typed Model Action DSL 与安全边界

长期建议协议 v2 默认禁止模型 arbitrary Lean tactic。

---

## 16.1 Planner 可选的 executable intent

```lean
inductive PlannerExecutableIntent
  | selectTransition (id : TransitionId)
  | expandRegion (id : RegionId)
  | preferFamily (family : StrategyFamily)
  | requestPremiseSearch (query : PremiseQuery)
```

模型只操作 Atlas 已注册对象。

---

## 16.2 可选的 typed action proposal

如果希望模型创造 Atlas 中没有的操作：

```lean
inductive ProposedSymbolicAction
  | applyConst (name : Name)
  | rewriteConst (name : Name) (symm : Bool)
  | casesLocal (localIndex : Nat)
  | exactLocal (localIndex : Nat)
```

Lean 侧：

1. 名称解析；
2. capability 检查；
3. Meta probe；
4. 加入 Atlas；
5. 再进入正常排序。

模型仍然不能直接执行。

---

## 16.3 Raw Lean code 兼容模式

保留：

```text
modelLeanCode := true
```

但建议标记：

```text
experimentalRawLeanCode := false
```

并从默认 planner protocol 移除。

如果保留：

- exact allowlist；
- 独立 heartbeat；
- source chars cap；
- fresh goal；
- no nested model；
- no command；
- no environment mutation；
- final proof boundary。

---

# 17. 搜索控制器重构

目标 `SearchController` 应非常短。

伪代码：

```lean
partial def solveGoal?
  (goal : MVarId)
  (state : SearchState)
  : MetaM (Option Expr) := do

  checkBudget state

  let snap ← snapshot goal
  let key ← mkGoalKey snap

  if state.path.containsStrict key then
    return none

  if let some p ← cheapClose? snap then
    return finalize p

  if let some p ← state.router.solve? goal state.budget then
    return finalize p

  let atlas ← state.atlasBuilder.buildOrReuse snap state

  let decision ← decide atlas state

  for selected in decision.executionOrder do
    let obs ← executeTransition selected state

    state.observations.add obs

    if obs.solved then
      return finalize ...

    state.atlas.update obs

    if shouldReplan ... then
      refreshPlannerDecision ...

  return none
```

控制器不应知道：

- parser syntax 安全细节；
- HTTP JSON；
- native solver 内部算法；
- UCB 公式细节；
- frontier render 细节。

---

# 18. Leaf Solver / Router 重构

---

## 18.1 统一接口

```lean
structure LeafSolver where
  name        : String
  capabilities : SolverCapabilities
  solve?      : MVarId → SolverBudget → MetaM LeafAttempt
```

---

## 18.2 Router

```lean
structure LeafRouter where
  backends : Array LeafSolver
  policy   : RouterPolicy
```

`RouterPolicy`：

```lean
inductive RouterPolicy
  | sequential
  | shapeBased
  | costAware
```

---

## 18.3 Search 只调用 Router

禁止：

```text
Search → solveWithNative
```

目标：

```text
Search → LeafRouter.solve?
```

这样未来可以增加：

- arithmetic leaf solver；
- simp-heavy solver；
- domain-specific solver；
- external verified proof backend；

而无需改 controller。

---

# 19. 配置系统重构

当前 `ProposeConfig` 已经开始拥有大量字段。

建议拆分：

```lean
structure SearchConfig where ...
structure AtlasConfig where ...
structure PlannerConfig where ...
structure SolverConfig where ...
structure TrustConfig where ...
structure TraceConfig where ...

structure ProposeConfig where
  search  : SearchConfig
  atlas   : AtlasConfig
  planner : PlannerConfig
  solver  : SolverConfig
  trust   : TrustConfig
  trace   : TraceConfig
```

---

## 19.1 推荐字段

```lean
inductive RankingMode
  | prior
  | ucb
  | planner
  | hybrid

structure SearchConfig where
  timeoutSec          : Nat := 10
  maxDepth            : Nat := 2
  maxActionsPerNode   : Nat := 32
  rankingMode         : RankingMode := .prior
  stableTieBreak      : Bool := true

structure AtlasConfig where
  enabled             : Bool := true
  maxNodes            : Nat := 96
  maxTransitions      : Nat := 160
  maxWorkUnits        : Nat := 256
  maxDepth            : Nat := 3
  maxWidthPerNode     : Nat := 8
  maxPerFamilyPerNode : Nat := 2
  rareStrategyReserve : Nat := 1
  maxRegions          : Nat := 12

structure PlannerConfig where
  enabled             : Bool := false
  mode                : PlannerMode := .policyValue
  provider            : ...
  maxPayloadChars     : Nat := 16000
  maxCalls            : Nat := 4
  minReplanGain       : Float := ...
  allowExpansionRequest : Bool := true
  allowRawLeanCode    : Bool := false
```

---

# 20. Model Protocol v2

当前 v1 主要是：

```text
target
locals
actions
frontier
feedback
```

v2 应围绕 Atlas。

---

## 20.1 PlannerRequest

建议：

```json
{
  "version": "vialean.planner.v2",
  "request_id": "...",
  "budget": {
    "remaining_ms": 4200,
    "remaining_atlas_work": 72
  },
  "root": {
    "id": "n0",
    "shape": "equality",
    "goal": "..."
  },
  "regions": [
    {
      "id": "r_eq",
      "family": "equality",
      "size": 7,
      "signals": [
        "two_edge_transitive_path",
        "target_size_decreases"
      ],
      "representatives": ["n4", "n8"]
    }
  ],
  "nodes": [
    {
      "id": "n4",
      "depth": 1,
      "goal": "...",
      "signals": {
        "subgoals": 1,
        "contradiction": false,
        "exact_local": true
      }
    }
  ],
  "transitions": [
    {
      "id": "t13",
      "from": "n0",
      "to": ["n4"],
      "family": "equality",
      "operation": "rewrite_local",
      "cost": 1.2
    }
  ],
  "observations": [
    {
      "transition": "t9",
      "outcome": "failed",
      "class": "unification"
    }
  ],
  "previous_plan": {
    "primary_region": "r_eq"
  }
}
```

---

## 20.2 PlannerResponse

```json
{
  "root_value": 0.82,
  "confidence": 0.74,
  "preferred_regions": [
    {"id": "r_eq", "score": 0.93},
    {"id": "r_elim", "score": 0.61}
  ],
  "transition_scores": [
    {"id": "t13", "policy": 0.88, "value": 0.91},
    {"id": "t7", "policy": 0.53, "value": 0.64}
  ],
  "strategy": {
    "primary_family": "equality",
    "objective": "Expose the local equality chain, then use exact/local closure."
  },
  "expansion_requests": [
    {
      "region_id": "r_eq",
      "extra_depth": 1,
      "family": "equality"
    }
  ],
  "avoid": [
    {
      "region_id": "r_construct",
      "reason": "branch_growth"
    }
  ]
}
```

所有字段都是 heuristic。

---

# 21. Prompt / 序列化预算

---

## 21.1 Atlas compression

不能把完整 Atlas 全塞 prompt。

流程：

```text
full internal atlas
      ↓
region summarization
      ↓
representative node selection
      ↓
signal compression
      ↓
serialization budget allocation
      ↓
hard final cap
```

---

## 21.2 Representative node 选择

优先：

- 每个 region 最佳 symbolic prior；
- rare family representative；
- 最低 depth；
- 最大结构变化；
- 已出现 closure signal；
- planner 上一轮请求的 region。

---

## 21.3 最终硬限制

序列化完成后：

```text
payload.length > max
```

必须降级：

1. 删除 debug text；
2. 缩短 goal pretty print；
3. 减少 representative；
4. 合并旧 observations；
5. 最后删除低优先级 region。

绝不能：

> 配置叫 12k，实际 payload 可能 30k。

---

# 22. Cache、Transposition 与失败记忆

---

## 22.1 Transposition Table

Atlas 与 Search 应共享：

```lean
structure TranspositionEntry where
  key            : GoalKey
  status         : NodeStatus
  bestValue?     : Option Float
  attemptedFamilies : ...
  proof?         : Option Expr
```

---

## 22.2 Failure Memory

避免“模型反复试错”的关键之一：

```lean
structure FailureMemory where
  nodeKey       : GoalKey
  operationKey  : OperationKey
  failureClass  : FailureClass
```

相同或等价操作不要重复执行。

---

## 22.3 Semantic equivalence

不仅：

```text
相同字符串不重复
```

还要：

```text
相同 operation + same semantic target
```

不重复。

例如两个 syntactically different planner 请求最终编译成相同：

```text
rewriteLocal h false
```

只执行一次。

---

# 23. 训练数据与自我改进接口

如果 ViaLean 将来做模型训练，这套结构会天然产生高质量数据。

---

## 23.1 每个 node 记录

```text
GoalKey
Atlas summary
candidate transitions
symbolic prior
planner score
execution result
eventual theorem success
proof distance
cost
```

---

## 23.2 正样本

证明路径上的 transition：

```text
positive policy target
```

成功 child 的剩余距离：

```text
value target
```

---

## 23.3 负样本

不是简单：

```text
tactic failed = negative
```

而要分：

```text
illegal
unification impossible
valid but expensive
valid but dead-end
valid but dominated
valid alternative path
```

这比普通 tactic trial-and-error 数据质量高很多。

---

## 23.4 Counterfactual training

Atlas 本身提供：

```text
同一个 state 上多条合法 future
```

所以可以训练：

> 为什么 A 比 B 更值得投入预算？

这正是 ViaLean 相对于普通 proof trace 的独特数据价值。

---

# 24. 文件级修改地图

以下基于当前仓库结构。

---

## `ViaLean/Config.lean`

### 修改

- 拆配置；
- 引入 `RankingMode`；
- `maxCandidates` 拆分；
- 增加 Atlas work/node/transition/global payload budget；
- `modelLeanCode` 迁移成 experimental；
- 增加 planner/replan 配置。

---

## `ViaLean/Goal.lean`

### 修改

- `LocalInfo` 增加 let value；
- snapshot 构建 `GoalKey`；
- 不直接实现 fingerprint；
- 增加 compact symbolic features。

建议：

```lean
value? : Option Expr
key    : GoalKey
```

---

## `ViaLean/Fingerprint.lean`

### 修改

改名或重构成：

```text
GoalKey.lean
```

负责：

- LocalKey；
- GoalKey；
- strict equality；
- hash；
- normalized cache key。

---

## `ViaLean/Proposal.lean`

### 修改

- source string → typed origin；
- 与统一 `SymbolicOperation` 对接。

---

## `ViaLean/Action.lean`

### 修改

把：

```text
ProofAction
ProposalFamily
payload
```

逐步统一到：

```text
SymbolicTransitionCandidate
StrategyFamily
SymbolicOperation
```

短期可保留 adapter。

---

## `ViaLean/Frontier.lean`

这是重构重点。

建议最终拆成：

```text
ViaLean/Atlas/
  Types.lean
  Builder.lean
  Producer.lean
  Diversity.lean
  Future.lean
  Region.lean
  Signals.lean
  Render.lean
  ReplayHandle.lean
```

### 原功能迁移

```text
normalizationProbes  → Producer/Normalization
rewriteProbes        → Producer/Rewrite
eliminationProbes    → Producer/Elimination
constructionProbes   → Producer/Construction
backwardProbes       → Producer/Backward
forwardProbe         → Producer/Forward
equalityChainProbe   → Producer/Equality
deepFuture           → Future
```

---

## `ViaLean/Model/Protocol.lean`

### 修改

保留 v1 decoder 兼容。

新增：

```text
PlannerRequestV2
PlannerResponseV2
RegionView
AtlasNodeView
AtlasTransitionView
ObservationView
ExpansionRequest
```

---

## `ViaLean/Model/Guidance.lean`

建议逐步改名：

```text
Planner/Guidance.lean
```

负责：

- Atlas compression；
- request building；
- final payload cap；
- planner response normalization。

不负责 provider IO。

---

## `ViaLean/Model/Provider.lean`

基本保持。

增加：

- protocol version negotiation；
- planner endpoint/mode；
- model response schema validation。

---

## `ViaLean/Search.lean`

最终拆掉。

拆为：

```text
ViaLean/Search/State.lean
ViaLean/Search/Controller.lean
ViaLean/Search/Decision.lean
ViaLean/Search/Execute.lean
ViaLean/Search/Replay.lean
ViaLean/Search/Replan.lean
ViaLean/Search/Observation.lean
```

---

## `ViaLean/Solver/Router.lean`

从数据结构升级成真正 router。

新增：

```text
solve?
route
backend stats
```

---

## `ViaLean/NativeSolver.lean`

可以逐步迁移到：

```text
ViaLean/Solver/Native.lean
```

并通过 `LeafSolver` 暴露。

---

## `ViaLean/Validate.lean` / `Compose.lean` / `Basic.lean`

保留作为 trust boundary。

新增：

- strict axiom audit 可选模式；
- final proof diagnostic；
- proof dependency policy 文档。

---

## `ViaLean/Trace.lean`

升级 trace schema。

输出：

```text
atlas stats
planner calls
replan cause
region selected
transition selected
value estimate
symbolic cost
observation class
```

---

# 25. 分阶段实施路线

不要一次把所有代码重写。

---

## Phase 0：Characterization

目的：

> 先锁定当前行为。

增加测试：

- 当前 search success；
- frontier diversity；
- interactive replay；
- native fallback；
- deterministic ordering；
- deadline；
- Meta rollback。

**不改算法。**

---

## Phase 1：安全与身份

### 1A
Model sandbox exact allowlist。

### 1B
GoalKey + let semantics。

### 1C
移除 duplicate fingerprint。

### 验收

- 所有旧测试通过；
- 新 adversarial tests 通过。

---

## Phase 2：统一动作 IR

新增：

```text
SymbolicOperation
StrategyFamily
TransitionCandidate
TransitionOrigin
```

让旧 `Proposal` / `ProofAction` 通过 adapter 编译到新 IR。

不要立即删除旧类型。

---

## Phase 3：Atlas v1 内部图

将当前 frontier preview 转换为：

```text
nodes + transitions
```

模型仍可用旧 v1 protocol，先由 `AtlasRender` 转回旧 `FrontierProbe` view。

这样先改内部，不改外部。

---

## Phase 4：真正 global bounded builder

- lazy producers；
- global work budget；
- per-node family diversity；
- outcome dedup；
- transposition。

完成后再 benchmark 与旧 Frontier build 的：

```text
recall
latency
work
```

---

## Phase 5：Search 模块拆分 + Router 接通

确保：

```text
Controller
Decision
Execute
Replay
```

分离。

Search 只依赖：

```text
AtlasEngine
Planner
LeafRouter
TrustBoundary
```

---

## Phase 6：Planner Protocol v2

先实现：

```text
policy + value
```

不做 free-form strategy。

Planner 输入：

```text
regions + representative nodes + transitions
```

输出：

```text
scores + root value
```

---

## Phase 7：Strategy + Expansion Request

让模型可以：

```text
优先 equality region
请求该 region 多展开一层
```

这是第一步真正的 neural-symbolic resource allocation。

---

## Phase 8：Replan Engine

删除“每 round 失败就继续模型 loop”的核心依赖。

引入：

```text
material Atlas delta
strategy exhausted
uncertainty
```

触发条件。

---

## Phase 9：Raw Lean code 降级为实验模式

默认：

```text
planner-only
```

raw tactic：

```text
opt-in compatibility
```

---

## Phase 10：Benchmark + trainable trace

稳定 JSONL：

```text
atlas
planner decision
transition outcome
proof outcome
```

为后续神经训练准备。

---

# 26. 测试体系

---

## 26.1 GoalKey

必须测：

- let value 不同；
- α-renaming；
- local order；
- dependent local；
- same snapshot stability；
- mock collision bucket；
- instantiated MVars。

---

## 26.2 Sandbox

必须测：

- custom tactic extension；
- `run_tac`；
- `set_option`；
- macro；
- syntax quote；
- malformed code；
- huge code；
- heartbeat；
- state rollback。

---

## 26.3 Atlas Bound

压力：

```text
100 locals
50 equalities
20 applicable premises
multiple inductive hypotheses
```

断言：

```text
nodes <= maxNodes
transitions <= maxTransitions
attempted <= maxWork
depth <= maxDepth
```

---

## 26.4 Diversity

构造：

> local apply 有大量候选，但唯一成功路线需要 cases/rewrite。

断言 future atlas 中 rare family 仍可见。

---

## 26.5 Planner

使用 replay/mock provider。

测：

- planner 选合法 transition；
- planner 给不存在 ID；
- planner expansion request 超预算；
- planner response malformed；
- planner value NaN/Inf；
- provider timeout；
- fallback 到 symbolic search。

---

## 26.6 Replan

断言：

- 单个 unification failure 不一定触发 model；
- material new equality 触发；
- strategy region exhausted 触发；
- `maxCalls` 永不超过；
- 相同 Atlas 不重复 query。

---

## 26.7 Determinism

同 theorem 多跑：

```text
Atlas node IDs
transition ordering
planner replay
trace event ordering
final proof
```

在 deterministic 模式稳定。

---

## 26.8 Meta state

所有：

```text
preview
failed transition
failed planner-proposed action
failed solver
```

必须验证 restore。

---

# 27. Benchmark 与 Ablation

没有 benchmark，无法证明“更广视野比 retry 更好”。

---

## 27.1 最少模式

```text
A: native only
B: symbolic current actions only
C: current frontier
D: atlas without neural
E: atlas + policy
F: atlas + policy + value
G: atlas + policy + value + expansion request
H: interactive raw tactic baseline
```

---

## 27.2 关键公平条件

必须 matched compute：

- 相同 wall-clock；
- 或相同 Meta work + model token budget；
- 模型调用数记录；
- prompt token/char 记录。

不能：

```text
Atlas 模式给 20 秒
baseline 给 5 秒
```

然后比较 solve rate。

---

## 27.3 最重要的 ablation

1. 顶层 diversity on/off；
2. future-node diversity on/off；
3. rare reserve on/off；
4. Atlas graph vs flat future list；
5. region summary on/off；
6. policy on/off；
7. value on/off；
8. expansion request on/off；
9. retry rounds vs event-driven replan；
10. error-text feedback vs structured observation；
11. raw tactic generation vs typed planner；
12. transposition on/off。

---

## 27.4 关键指标

```text
solve rate
time-to-proof
p50/p90 latency
Meta transition attempts
Atlas nodes built
model calls/problem
model input chars/tokens
replan count
proof size
branch count
dead region ratio
rare strategy contribution
```

---

## 27.5 “广视野有效”专属指标

建议新增：

### Future Utility

最终 winning path 是否在第一次 Atlas 中已可见。

### Planner Lookahead Gain

模型有 future Atlas 时的选中率 vs 只看 immediate actions。

### Retry Reduction

```text
平均 model calls / solved theorem
```

应明显低于 raw interactive retry。

### Rare Strategy Recall

最终 winning family 为低 prior family 时：

```text
Atlas 能否在执行前暴露它。
```

这会直接支撑 ViaLean 的研究故事。

---

# 28. 观测指标与 Trace

建议所有 trace 结构化为 JSON event。

---

## 28.1 Atlas build event

```json
{
  "event": "atlas_build",
  "goal": "...",
  "nodes": 42,
  "transitions": 63,
  "attempted": 81,
  "elapsed_ms": 119,
  "families": {
    "equality": 8,
    "elimination": 6
  }
}
```

---

## 28.2 Planner event

```json
{
  "event": "planner",
  "root_value": 0.81,
  "confidence": 0.74,
  "selected_region": "r5",
  "payload_chars": 11240,
  "elapsed_ms": 430
}
```

---

## 28.3 Replan event

```json
{
  "event": "replan",
  "cause": "new_symbolic_fact",
  "old_atlas_version": 3,
  "new_atlas_version": 4
}
```

---

# 29. 向后兼容策略

---

## 29.1 Tactic surface 不变

继续支持：

```lean
propose
propose?
propose via_eq ...
propose via_iff ...
propose via_cut ...
propose via_witness ...
```

用户无需知道内部重构。

---

## 29.2 Config migration

旧：

```text
ucb
deterministic
frontierMaxProbes
modelMaxRounds
```

至少一个过渡版本保留。

启动时映射新配置，并在 trace 中提示 deprecated。

---

## 29.3 Model protocol

保留：

```text
vialean.guidance.v1
vialean.interactive.v1
```

新增：

```text
vialean.planner.v2
```

provider 可以声明 capability。

---

# 30. Definition of Done

当以下全部满足，可认为“神经符号一体化 v2”完成。

### Core correctness

- [ ] 最终 proof 全部经过现有 trust boundary。
- [ ] model 不能直接决定 proof acceptance。
- [ ] failure branch 全部 restore Meta state。
- [ ] strict GoalKey 用于 cycle/transposition。
- [ ] let semantics 纳入状态 identity。

### Atlas

- [ ] Atlas 是内部图结构。
- [ ] node/transition 有稳定 ID。
- [ ] future 有 transposition dedup。
- [ ] 每层 family-diverse。
- [ ] global work budget 真正限制构建量。
- [ ] region summary 可用。
- [ ] Atlas 可 incremental update。

### Planner

- [ ] 默认模型不需要输出 Lean tactic。
- [ ] planner 能输出 region preference。
- [ ] planner 能输出 transition policy/value。
- [ ] planner 可选请求 symbolic expansion。
- [ ] uncertainty 被显式表达。
- [ ] malformed planner response 安全 fallback。

### Replan

- [ ] 模型调用是事件驱动，不是纯 round retry。
- [ ] 相同 Atlas 不反复 query。
- [ ] structured observation 取代 error-text 为主反馈。
- [ ] repeated semantic action 自动去重。

### Engineering

- [ ] `Search.lean` 已拆分。
- [ ] `LeafRouter` 已真正接通。
- [ ] Proposal origin 强类型。
- [ ] RankingMode 语义明确。
- [ ] prompt 有 serialized hard cap。
- [ ] Atlas output cap / work cap 分离。

### Evaluation

- [ ] 有 matched-compute benchmark。
- [ ] 有 retry vs replan 对比。
- [ ] 有 flat frontier vs graph Atlas 对比。
- [ ] 有 policy/value/expansion ablation。
- [ ] trace 可生成训练 JSONL。

---

# 31. 禁止的反模式

为了保持路线一致，后续开发避免：

---

## 31.1 不要把“神经符号”理解成更多 LLM round

错误：

```text
modelMaxRounds: 4 → 12
```

不等于神经符号融合。

---

## 31.2 不要让模型负责搜索 legality

模型说：

```text
这个 tactic 应该合法
```

没有意义。

Lean Meta 必须自己 probe。

---

## 31.3 不要把 Atlas 变成大段 pretty-print

如果 Atlas 最终只是：

```text
几十 KB 文本
```

模型仍然是在读日志，不是在理解 proof graph。

---

## 31.4 不要把所有 symbolic score 学习化

以下规则应保留 hard symbolic：

```text
是否合法
是否闭合
是否 no-progress
branch 数
target 是否减少
是否 contradiction
是否 exact local
```

神经模型用于估计：

```text
长期价值
策略方向
跨 family tradeoff
```

---

## 31.5 不要过早引入 MCTS / 并行搜索

先把：

```text
Atlas
GoalKey
Transition
Planner
Value
Replan
Budget
```

做稳。

之后 MCTS 才有干净 state/action/value interface。

---

# 32. 后续研究路线

以下属于 v2 稳定后再做。

---

## 32.1 Learned Value Model

从成功 proof trace 学：

```text
V(AtlasNode)
```

用于减少 LLM 调用。

---

## 32.2 Distilled Local Planner

大模型只生成训练数据。

部署时使用小模型：

```text
Atlas features → policy/value
```

ViaLean 的符号 Atlas 非常适合蒸馏。

---

## 32.3 Graph Encoder

长期可以把：

```text
Expr DAG
local dependency graph
Atlas transition graph
```

编码给 GNN / graph transformer。

这会比 pretty-print prompt 更接近真正 neuro-symbolic representation。

---

## 32.4 Hierarchical Planner

两级：

```text
Strategic Planner
    ↓
choose region / proof idea

Tactical Value Model
    ↓
rank transitions
```

大模型不必在每个 node 调用。

---

## 32.5 Proof Skeleton

Planner 可以提出：

```text
1. eliminate h
2. expose equality
3. normalize
4. close by local theorem
```

但不是 tactic script。

Symbolic engine负责将 skeleton refine 成具体 transition path。

---

## 32.6 Active Symbolic Expansion

模型可以学习：

> 什么地方继续展开 Atlas 最有信息价值。

即：

```text
value of computation
```

而不仅是：

```text
value of action
```

这是 ViaLean 非常值得做的研究点。

---

# 33. 推荐 Commit / Issue 拆分

建议不要按“大重构 PR”提交。

---

## Epic A — Core correctness

### A1
`fix(goal): introduce strict GoalKey with let-binding semantics`

### A2
`refactor(goal): remove duplicate fingerprint implementation`

### A3
`fix(model): replace syntax-prefix sandbox with explicit capabilities`

---

## Epic B — Explicit budgets

### B1
`refactor(config): separate premise, action, atlas-output and atlas-work limits`

### B2
`fix(model): enforce final serialized planner payload cap`

### B3
`refactor(ranking): replace ucb/deterministic boolean interaction with RankingMode`

---

## Epic C — Symbolic IR

### C1
`refactor(action): introduce SymbolicOperation and typed ProposalOrigin`

### C2
`refactor(search): compile legacy ProofAction into transition candidates`

---

## Epic D — Atlas core

### D1
`feat(atlas): introduce node-transition graph representation`

### D2
`feat(atlas): add strict transposition dedup`

### D3
`feat(atlas): add lazy perspective producers`

### D4
`feat(atlas): add per-node diversity scheduler`

### D5
`feat(atlas): add region summaries`

---

## Epic E — Search architecture

### E1
`refactor(search): split state, controller, replay, execution and ranking`

### E2
`refactor(solver): route leaf solving through LeafRouter`

### E3
`feat(search): add structured observations and failure classes`

---

## Epic F — Planner v2

### F1
`feat(planner): add atlas-based protocol v2`

### F2
`feat(planner): add policy and value scoring`

### F3
`feat(planner): add strategy and region preference`

### F4
`feat(planner): add bounded expansion requests`

### F5
`feat(search): event-driven replanning`

### F6
`refactor(model): make raw Lean code an experimental compatibility path`

---

## Epic G — Evaluation

### G1
`test: add adversarial GoalKey, sandbox and budget suites`

### G2
`test: add deterministic atlas/replan replay`

### G3
`bench: add matched-compute atlas ablations`

### G4
`bench: compare retry interaction with event-driven replanning`

### G5
`feat(trace): emit planner-training JSONL`

---

# 34. 最终目标架构

最终 ViaLean 应该具备这样的系统属性：

```text
                    ┌─────────────────────────┐
                    │      Lean theorem       │
                    └────────────┬────────────┘
                                 │
                                 ▼
                    ┌─────────────────────────┐
                    │ GoalSnapshot + GoalKey  │
                    └────────────┬────────────┘
                                 │
                                 ▼
          ┌───────────────────────────────────────────┐
          │                 Proof Atlas               │
          │                                           │
          │ Symbolic states    typed transitions      │
          │ regions            derived facts          │
          │ obligations        cost / diversity       │
          │ transpositions     bounded futures        │
          └──────────────┬─────────────────┬──────────┘
                         │                 │
                         │                 │
              symbolic heuristic       neural reasoning
                         │                 │
                         ▼                 ▼
                ┌───────────────┐  ┌────────────────┐
                │ UCB / priors  │  │ Neural Planner │
                │ local solvers │  │ Policy / Value │
                └───────┬───────┘  │ Strategy       │
                        │          │ Uncertainty    │
                        │          └───────┬────────┘
                        │                  │
                        └──────────┬───────┘
                                   ▼
                          Search Decision
                                   │
             ┌─────────────────────┼────────────────────┐
             │                     │                    │
          execute              expand Atlas          leaf solve
             │                     │                    │
             ▼                     ▼                    ▼
       Typed Symbolic        More verified        LeafRouter
       Transition            future states            │
             │                     │                   │
             └─────────────┬───────┴───────────────────┘
                           ▼
                  Structured Observation
                           │
                     Atlas update
                           │
                 ┌─────────┴──────────┐
                 │                    │
          strategy still valid?   material change?
                 │                    │
                yes                  yes
                 │                    │
             continue              replan
                 │                    │
                 └──────────┬─────────┘
                            ▼
                     proof completed
                            │
                            ▼
                      finalizeProof
                            │
                            ▼
                        Lean kernel
```

---

# 结论

ViaLean 最终不应该是一套：

> **“模型不断向 Lean 提交候选，然后用 Lean 错误驱动下一次猜测”**

的系统。

它应该是一套：

> **Lean 先在严格预算内主动构建多样、可执行、可验证的局部证明未来；神经模型在这个 proof atlas 上理解全局局势，预测哪些区域具有长期价值，并决定把下一份符号计算预算投入哪里；执行结果以结构化状态变化反馈给 Atlas，只有在策略失效或获得新信息时才重新规划。**

这条路线的核心不是“把 LLM 接得更深”，而是建立一个真正共享的神经符号中间层：

```text
                Proof Atlas
             /              \
      Symbolic Engine     Neural Planner
             \              /
             Verified Search
                    |
               Lean Kernel
```

如果这套架构完成，ViaLean 的差异化就不再是：

> “Lean prover 支持 LLM guidance”。

而会变成：

> **一个以 diversity-preserving bounded proof atlas 为世界模型、以 neural policy/value/strategy 为长期决策器、以 Lean symbolic execution 为可信动作执行器的神经符号证明规划系统。**

这才是“模型拥有更广视野，而不是反复试错”的完整工程落点。
