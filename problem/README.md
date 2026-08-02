# `type-pm` の問題台帳

このディレクトリは，`type-pm-paper` のレビューで見つかった問題を，
1問題1ファイルで追跡するための索引である．

問題を次の2種類に分ける．

- **P（Pending）**：設計判断が残っており，論文では `\todo{...}` により赤字で
  示している問題．
- **R（Resolved）**：`type-pm-paper` の
  `05bf5f8fd41d942f6c0926a86413da9175ea5c5c` より後の編集のうち，
  修正内容と主張範囲を固定でき，論文では `\new{...}` により青字で示している問題．

ここで「解決済み」は，その記録に書かれた範囲の意味論，規則，証明境界，
または実装上の主張が固定されたという意味である．Egison が形式条件を全面的に
強制することや，Lean の最終定理が無条件であることまで一律に意味しない．
各記録の「保証範囲」と「残る境界」を必ず併せて読むこと．

## 未解決の問題

| ID | 問題 | 現在の論文への影響 | 状態 |
|---|---|---|---|
| P1 | [不透明・高階なマッチャーフローに対する値パターンスコープ条件](value-pattern-scope.md) | 捕捉許容性，条件付き保存性・型安全性 | 中核設計解決済み，論文・Lean・Egison への反映待ち |
| P2 | [`Matcher κ τ` による capability と target の分離](matcher-capability-instantiation.md) | 能力許容性，`mPoly`，主要型，partial matcher と安全性定理の境界 | 非 CAS formal core に限定．代数層＋covered-only `CoreSpecWF` 接続済み，source 規則は [`tex/main.tex`](../tex/main.tex) の仕様草案に整理済み，論文同期・Lean source judgment・二種 W・core safety 未実施 |

## 解決済みの問題

| ID | 問題 | 固定したもの |
|---|---|---|
| R1 | [`match` の表層意味論と定理の射程](resolved-surface-match-boundary.md) | 単一節 `matchAll` の成功評価，表層の逐次試行・失敗との境界 |
| R2 | [matcher 節へ送るパターン形の限定](resolved-matcher-clause-dispatch.md) | `matcher-dispatchable` と構文主導ディスパッチ |
| R3 | [matcher 節の到達可能性と arm 網羅性](resolved-matcher-consistency-reachability.md) | catch-all-last，Coverage/refinement の到達性，全インスタンスでの arm 網羅性 |
| R4 | [`StepTotal` と MNode を含む進行性](resolved-step-total-mnode-progress.md) | 埋込み big-step の停止前提，MNode 深さによる進行性証明 |
| R5 | [値パターンパターン捕捉の実行時意味論](resolved-value-pattern-capture-runtime.md) | 原子入力環境の捕捉，同一原子内の穴との順序 |
| R6 | [実行時環境と MNode の整型不変量](resolved-runtime-environment-invariant.md) | `ρ ⊨ Γ`，`ρ_f ⊨ Γ_f` と既存の state/MNode 不変量の結合 |
| R7 | [matcher の固有型，slot，対象型整列](resolved-runtime-matcher-typing-invariant.md) | 単相 rigidity，直接の対象型関係，積 slot の成分別不変量 |
| R8 | [`MS-MATCHER` 保存性の全ケース](resolved-ms-matcher-preservation.md) | Structural-Hole Transfer，general/refinement/catch-all/失敗ケース |
| R9 | [相対的主要性と Algorithm W の主張境界](resolved-relative-principality-boundary.md) | one-way の局所結果，固定入力に相対的な紙上補題，full principality の撤回 |
| R10 | [条件付きメタ理論の正確な境界](resolved-conditional-metatheory-boundary.md) | `Adm`/`StepTotal` 前提，条件付き保存性・進行性・型安全性・整合性 |
| R11 | [Egison 実装と検証結果の主張範囲](resolved-implementation-validation-scope.md) | 実装済み検査，部分近似，既存注釈を含む検証 corpus |
| R12 | [matcher 定義の次マッチャー分解とホール検査](resolved-next-matcher-slot-checking.md) | 複数穴の明示タプル境界，構文形に依存しない成分別 `MatcherSlot` 検査 |

## P1 と R5 の境界

- R5 は，`#$x` が捕捉する値パターン式にどの環境を与えるかという**実行時意味論**
  を固定する．
- P1 は，その式が原子入力環境だけで型付くことを，不透明・高階な matcher の
  流れを含めて**静的に保証する方法**を決める．
- Lean の `VPScoped` は P1 の候補述語であり，現在の `WTTree.atom` と最終
  `type_safety` には配線されていない．したがって R5 の完了を P1 の完了と
  みなしてはならない．

## P2 と R7・R9・R12 の境界

- R7 は，固定された単相導出内で matcher 値の固有能力を保ち，利用位置の
  `MatcherSlot` で検査する規則と実行時不変量を固定する．
- R9 は，one-way 構造関係や固定入力に相対的な局所主要性までを切り出す．
- R12 は，matcher 定義の次マッチャーをホールへ対応付け，各成分をその完全な
  推論型から `MatcherSlot` に対して検査する静的手続きを固定する．
- P2 は，`Matcher κ τ` として capability と target を別 sort・別代入へ
  分離し，二種 scheme generalization，capability substitution，one-way witness の伝播を
  value flow 全体で保持する方針を採用した．Lean では `TypePM/P2/` の独立層に
  二 sort の構文・代入・scheme，one-way match，ShapeCap／observability／projection，
  covered runtime certificate と内部 erasure，runtime matcher/slot 不変量，
  `CapTargetOK` の核を機械化した．
  `CoreSpecWF` は typed-hole capability を保持する静的 `SourceCtx` の下で actual
  clause ごとの決定的 evidence checker を受け，clause/evidence の一対一対応，
  固有 `ShapeCap`，covered runtime matcher invariant，Ξ-closed certificate の
  admissible target specialization による非強化までを導く．checker の明示引数に
  target 型や runtime environment はないが，`SourceCtx` の target/runtime 純粋性は
  concrete instantiation の義務である．source typing／evidence／Coverage の規則は
  [`../tex/main.tex`](../tex/main.tex) の仕様草案に整理した段階であり，論文英日版への
  反映，その Lean source judgment への実装，捕獲環境を運ぶ
  二種代入補題と substitution admissibility，二種 Algorithm W，既存
  `HasTy`／`ValueTy`／matching state の移行，core Type Safety は未実施である．
  R12 の成分検査へ渡される前に scheme lookup が能力を失えば
  回復できないため，R7・R9・R12 の局所結果だけでは閉じない．
- P2 の capability は，`ShapeCap` が証拠として認める constructor clause を
  少なくとも一つ持ち，observable な全 parameter evidence を確定できる matcher
  に構造 head を与える **shape capability** とし，全 constructor の処理を保証する
  `CoverageOK` とは分離する方針を採用した．
  partial matcher も structured capability の候補までは推論できるが，formal core の
  source typing は `CoverageOK` 不足を型エラーとして拒否する．full Egison では同じ
  不足を warning として受理してよいが，その経路は core safety の対象外である．
  `ShapeCap` は general と
  constructor／tuple-headed refinement clause から partial evidence を集め，hole
  は next matcher capability，`_`／`#$x` は `unseen` として exact agreement で
  合成する．不一致と，structured root 以下で最後まで未観測な observable parameter
  は型エラーにし，refinement は `CoverageOK` には数えない．observability は pattern
  signature の capability-visible path が作る依存方程式の least fixpoint とし，
  true phantom，opaque／function 内部，seed のない recursive-only parameter は
  unobservable として canonical `•` にする．constructor field evidence は signature
  parameter の variable identity を保つ fresh instantiation 後，source binder 順でなく
  result argument slot へ投影する．product と capability-visible former をたどり，
  opaque／function で止まり，`unseen` は非寄与，既知 head mismatch は型エラー，
  重複 occurrence は exact merge とする．独立 Lean core では，この projection の
  staged soundness，field/evidence 同時置換不変性，exact merge／finalization，
  observability least fixpoint を証明した．raw 宣言からの graph／signature 構築，
  exact-evidence calculus の相対的主要性，既存 calculus への接続は残る．
  capability 変数は provenance 付き `CapGen` で制限せず，通常型変数と同じ HM
  generalization を別 sort 上で行う．ただし，全 substitution を一般化前に型・環境・
  制約へ適用し，明示量化は local-meta／fresh-skolem 境界つきで検査し，literal root は
  D1 で確定する．
  再帰 binding は通常の単相 HM SCC 規則で推論し，matcher literal 固有の向き付き
  Shape generation obligation だけを別の least-evidence solver で解く．型とは別の
  producer-flow summary を通常の expression rule と同じ構文再帰で計算し，
  first-order evidence へ正規化して，alias／高階 application と binder–RHS knot を
  通る origin を保存する．自己参照，consumer demand，結果注釈は seed にせず，
  finalization と全代入適用後に SCC 外で通常どおり一般化する．この設計の十分性は
  Lean で検証する．formal-core source typing は単一で，全 matcher literal に
  `CoverageOK` を要求する．runtime 証明内部では `ordinary`／`covered` の mode index を
  残してよいが，source から構成するのは covered invariant だけとし，ordinary は
  covered derivation の erasure／weakening 先に限る．Coverage 依存の
  `holeAfterGenerals` は，唯一の canonical bare-hole catch-all が最終にある
  `CatchAllLast` へ置き換える．`CapTargetOK` は closed acyclic alias 展開と明示的な
  surface synonym だけを使う frozen canonical signature environment 上で検査し，
  CAS `groundEquiv`／subtype／reshape／semantic normalization は含めない．open
  combinator は実 slot 値由来の仮定と coupled substitution で整合性を運ぶ．ただし
  現行 `factor`／`term` は nullary `MathValue` pattern signature から evidence を得る
  ため，単純な head view では child capability を保持できない．CAS 向け
  target-indexed pattern-view signature，view-qualified constructor ID，
  kind-aware index projection，runtime extraction preservation が残る最優先の
  設計 blocker である．

## P2 formal core の完了判定

詳細な定理の鎖と受入条件は
[`P2-PROOF-TARGET.md`](../P2-PROOF-TARGET.md) に固定する．

P2 の完了判定は，検証・freeze 済み非 CAS signature を入力とする formal core に
限る．two-sort typing，producer-stable match，actual clause からの
evidence／`ShapeCap`，二種 W／Gen／Inst の value-flow 非強化，`CoverageOK` 必須の
source/runtime safety，singleton direct-self を論文本文と Lean で定義・証明した時点で
P2 を解決済みに移す．P1 の capture admissibility と埋込み計算の停止性は独立前提として
残してよい．

一般 D4 producer flow，raw graph／signature／alias validator，Egison の ordinary
warning／certified mode／load-unit integration，標準ライブラリ移行，D5-CAS は
Egison integration／language extension として別管理し，P2 の完了を妨げない．
`RuntimeSpec` 相対の代数補題や `CoreSpecWF` の接続不変量だけを core calculus の
Preservation／Progress／Type Safety と読み替えてはならない．

## 記録の読み方

各解決済み記録は，原則として次を分離する．

1. 以前の記述または証明で何が問題だったか．
2. 論文で固定した解決．
3. Egison 本体が同じ性質をどこまで実装しているか．
4. Lean がどの定義・定理まで機械化しているか．
5. P1/P2，停止性，実装の部分近似など，解決に含めない境界．

青字の abstract，introduction，conclusion，依存図，付録案内，例示は，
R1–R12 の主張を各所へ反映したものである．独立した問題として重複登録しない．

## 更新手順

1. 未解決問題では「決定すべき質問」に回答し，採用案と却下理由を残す．
2. 決定後は，論文の英語版・日本語版，Egison 実装，Lean の定義・定理境界を
   同じ作業単位で更新する．
3. 解決済み記録には，回帰確認先と，明示的に保証しない範囲を残す．
4. 論文の `\new`／`\todo` を外すときも，本台帳は設計・証明境界の履歴として
   維持する．

## 主な参照先

- 論文：
  [`type-pm-paper/main.tex`](../../type-pm-paper/main.tex)，
  [`type-pm-paper/ja/main.tex`](../../type-pm-paper/ja/main.tex)
- Lean の型・スキーム：
  [`TypePM/Syntax.lean`](../TypePM/Syntax.lean)，
  [`TypePM/TypeRel.lean`](../TypePM/TypeRel.lean)，
  [`TypePM/Typing.lean`](../TypePM/Typing.lean)
- Lean の意味論と実行時不変量：
  [`TypePM/Semantics.lean`](../TypePM/Semantics.lean)，
  [`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean)
- Lean のメタ理論：
  [`TypePM/Metatheory/Preservation.lean`](../TypePM/Metatheory/Preservation.lean)，
  [`TypePM/Metatheory/Progress.lean`](../TypePM/Metatheory/Progress.lean)，
  [`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean)，
  [`TypePM/Metatheory/Safety.lean`](../TypePM/Metatheory/Safety.lean)，
  [`TypePM/Metatheory/Principal.lean`](../TypePM/Metatheory/Principal.lean)
- Egison：
  [`Core.hs`](../../egison/hs-src/Language/Egison/Core.hs)，
  [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs)，
  [`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs)，
  [`Type/Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs)
