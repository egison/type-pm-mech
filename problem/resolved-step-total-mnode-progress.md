# R4：`StepTotal` と MNode を含む進行性

## 状態

- 状態：解決済み（前提と証明方法の固定）
- 論文での表示：青字（`\new`）
- 結果の種類：条件付き進行性
- P1/P2 との関係：別の停止性前提

## 問題

matching-state の一ステップ規則は small-step だが，規則選択の途中で式の big-step
評価を要求する．具体的には次が含まれる．

- 値パターン式
- 選ばれた matcher 節の next-matcher 式 `M`
- 選ばれた data arm の decomposition 式 `N`
- 入れ子 MNode の内部 top tree で同様に遭遇する式

これらが発散すると，状態が stuck なのではなく，一ステップの導出を探す計算自体が
終わらない．停止性を仮定せず「すべての整型非終端状態は一歩進む」と述べるのは
強すぎる．

また `MS-MNODE-STEP` は内部 top tree に再帰するため，単純な外側 tree の場合分け
だけでは帰納法が整礎であることが示せない．

## 固定した解決

### `StepTotal`

`StepTotal(s)` を，状態 `s` の top tree に対する有限の規則探索で遭遇するすべての
埋込み big-step 評価が停止するという局所前提として導入する．入れ子 MNode では，
選ばれた内部 top tree に対して再帰的に要求する．

これにより Progress の結論は次の形になる．

> `s` が整型，非終端，admissible で `StepTotal(s)` を満たすなら，
> ある後続状態列 `s → [s₁,…,sₗ]` が存在する．

`l = 0` は正当な match failure であり，stuck ではない．

### MNode 深さ

top tree の構文的 MNode-nesting depth を測度にする．

- atom の深さは 0
- MNode の深さは，内部 stack の各 tree の最大深さに 1 を加えたもの

`MS-MNODE-STEP` が選ぶ内部 top tree は必ず深さが小さいため，この測度による帰納が
整礎になる．pattern function が非再帰であることは expansion の停止を支えるが，
埋込み式 `M`/`N` の停止とは別である．

## 論文との対応

- §3.3 の MNode と探索順序の説明
- §5 の `StepTotal(s)` 定義
- Lemma “Conditional Matching State Progress”
- Appendix の progress 全ケース

形式化は DFS で書かれているが，規則と条件付き安全性の主張は探索順序から独立で
ある．Egison の探索モードとの差を安全性の差とみなさない．

## Egison 実装との対応

Egison は lazy evaluation を使い，`PMMode` により DFS と BFS の両方を選べる．
既定の表層形式は BFS を使う一方，not/forall などは内部で DFS を使う．R4 は
「Egison の全式が停止する」という実装保証ではない．matcher の decomposition や
値パターンが発散すれば，実装でも該当探索は結果を返さない可能性がある．

R4 はその挙動を型エラーや stuck と混同せず，論文の Progress に必要な停止前提を
明示した記録である．

## Lean 機械化との対応

[`TypePM/Metatheory/Progress.lean`](../TypePM/Metatheory/Progress.lean) の
`ms_progress` が matching tree/stack の結合再帰により本体を証明する．主な補題は
次である．

- `canonical_list`
- `pdMatch_typed`
- `armExh_instance`
- `ppm_total`
- `ppm_length`
- `clause_walk`
- `arms_walk`
- `matcherV_progress`

Lean の停止前提は，論文の局所的 `StepTotal(s)` より強い
`htotal : ∀ ρ e, ∃ v, Eval ...` という大域 oracle である．また捕捉式の評価型付けは
別の `heval` oracle で受ける．論文上の `Adm(s)` と `StepTotal(s)` をそのまま
Lean の述語として実装したわけではない．

また，論文は pattern function を非再帰とするが，現在の Lean の
`PatFunWF`／`SigFWF` は pattern-function 呼出しグラフの非循環性を条件に持たない．
`ms_progress` は一歩進行性なのでこの条件なしで証明できるが，Lean が
pattern-function expansion 全体の停止を証明したわけではない．

## 保証範囲

R4 で解決したのは，Progress が必要とする停止性の位置と，MNode 帰納法の
整礎性である．次は証明していない．

- 一般の Egison 式または matcher decomposition の停止性
- DFS/BFS の公平性や全結果列挙の機械化
- pattern-function 呼出しグラフの非循環性と展開全体の停止性の機械化
- P1/P2 の admissibility を source typing から導くこと
- Lean の大域 `htotal` を論文の局所 `StepTotal` へ弱めること

## 回帰確認

- Progress を無条件と呼ばない．
- divergence を stuck terminal state と数えない．
- MNode の内部再帰では，減少する深さまたは同等の整礎測度を明示する．
- `StepTotal` と P1/P2 の `Adm` を一つの前提として潰さず，別に追跡する．
