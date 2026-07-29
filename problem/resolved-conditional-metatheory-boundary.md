# R10：条件付きメタ理論の正確な境界

## 状態

- 状態：定理の条件と依存関係は解決済み
- 論文での表示：青字（`\new`）
- 結果：条件付き
- 未放電の source-level obligation：P1，P2

## 問題

保存性，進行性，型安全性，matcher consistency を無条件の結果として述べるには，
source typing から少なくとも次を導く必要がある．

- `#$x` が捕捉する式を atom-input context で型付けできること
- generalized matcher の利用点 instantiation が intrinsic capability を
  強化しないこと
- syntax-directed inference が必要な fresh structural relation を作ること
- 一ステップ規則探索中の埋込み式評価が停止すること

これらを証明せず unconditional theorem と書くと，P1/P2 の反例や big-step の発散を
覆い隠す．一方，必要な premise を明示すれば，局所保存性や reduction case analysis
の大部分は固定できる．

## 固定した解決

### admissibility

論文では二つの source-level obligation を区別する．

- **capture-admissible**：`PPP-VAL` が捕捉する式が atom-input context の期待型で
  型付き評価される．
- **capability-admissible**：runtime matcher occurrence へ至る全 scheme
  instantiation が，定義時の `T-MATCHER` capability を保存する．

matching state と nested MNode 全体で両者が成立することを `Adm(s)`，
evaluation/reduction derivation 全体で成立することを `Adm(D)` と書く．

### 停止性

R4 の `StepTotal(s)` を admissibility と分離する．型能力が正しくても，
埋込み式が発散すれば一ステップ導出は得られないためである．

### 条件付き定理

この境界の下で，次を条件付き結果として述べる．

- PPP Type Preservation
- Matching State Progress
- Type Safety
- Matcher Consistency

Matcher Polymorphism と one-way の局所結果は，P1/P2 の最終放電とは分けて述べる．
abstract，introduction，conclusion，dependency graph も同じ境界に同期する．

## 論文との対応

- abstract の “Grounding”
- contributions
- “Proof status and open obligations”
- Conditional PPP Type Preservation
- Conditional Matching State Progress
- Conditional Type Safety
- Conditional Matcher Consistency
- Appendix の詳細ケースと依存図

「条件付き」は証明を保留した曖昧な但し書きではなく，どの premise を局所証明が
消費するかを明示する interface である．

## Egison 実装との対応

Egison の checker は P1/P2 の一部を局所的に検査するが，`Adm` 全体を保証しない．

- P1：既知 matcher shape では `checkVpScope` を行うが，不透明・高階 flow は残る．
- P2：単相 matcher rigidity は実装するが，`instantiate` は通常の HM relation
  である．
- `StepTotal`：一般の式停止性は検査しない．

したがって，現行 Egison プログラムが checker を通るだけで，論文の条件付き前提を
すべて discharge したとはいえない．

## Lean 機械化との対応

### PPP preservation

[`TypePM/Metatheory/Preservation.lean`](../TypePM/Metatheory/Preservation.lean) の
`ppp_preservation` は `heval` oracle の下で証明済みである．

### Progress

[`TypePM/Metatheory/Progress.lean`](../TypePM/Metatheory/Progress.lean) の
`ms_progress` は，論文の局所 `StepTotal` より強い大域 `htotal` と評価 oracle を
受け取る．

### Type safety

[`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean) の
`type_safety_a`，`type_safety_b_at`，`type_safety_b`，`initial_atom_wt`，
`type_safety` は proof term を持つ．ただし最終 `type_safety` は次の5 interface
premise を取る．

- `hevG`：大域的な evaluation typing
- `hgen`：generalized value が全 scheme instances で型付くこと
- `hsiteReach`：fresh-leaf structural reachability
- `hclorc`：matcher clause typing の利用点への輸送
- `hinstF`：pattern-function body derivation の利用点への輸送

`hevG` のうち `PPP-VAL` に関わる部分は P1 を覆うが，通常の式評価を含む
結合帰納全体も担う．`hgen`／`hclorc` は主に P2，`hsiteReach` は
syntax-directed Algorithm W の fresh-leaf 制限，`hinstF` は pattern-function
dual scheme/body derivation の輸送という独立の機械化ギャップを表す．Lean は
論文の `Adm(D)` そのものからこれらを導く形ではない．

### Matcher consistency

[`TypePM/Metatheory/Safety.lean`](../TypePM/Metatheory/Safety.lean) の
`reaches_preservation`，`terminal_subst_typed`，`search_mem_reaches`，
`matcher_consistency` は一段保存 `hb` の下で証明済みである．

現在の named theorem `matcher_consistency` は `atomScalarOK p m = true` を要求し，
tuple pattern × product matcher を直接含まない．一般 `matchAll` の初期積 slot は
`type_safety` 側の `initial_atom_wt` が扱うが，論文定理と同じ一般ラッパーではない．

## 保証範囲

R10 で解決したのは，何が無条件でなく，どの前提の下で局所証明が完成するかである．
次はまだ解決していない．

- `Adm` を decidable source typing から導くこと
- `hevG` の結合帰納，`hsiteReach` の fresh-leaf 補題，`hinstF` の
  pattern-function 輸送をそれぞれ放電すること
- `hgen`／`hclorc` を P2 の採用設計から放電すること
- Lean の大域停止前提を論文の局所 `StepTotal` に合わせること
- tuple を含む named `matcher_consistency` wrapper の一般化
- full Principal Type Property

## 回帰確認

- abstract と theorem 本文で conditional/unconditional の表現を一致させる．
- Lean に `sorry` がないことと，定理が premise-free であることを混同しない．
- P1，P2，`StepTotal`，fresh-leaf 制限を別々に列挙する．
- Matcher Polymorphism を unconditional safety の代用にしない．
