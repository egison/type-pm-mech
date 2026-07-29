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
| P1 | [不透明・高階なマッチャーフローに対する値パターンスコープ条件](value-pattern-scope.md) | 捕捉許容性，条件付き保存性・型安全性 | 設計判断待ち |
| P2 | [`Matcher` 添字の能力を保存するスキームインスタンス化](matcher-capability-instantiation.md) | 能力許容性，`mPoly`，主要型，無条件の進行性・型安全性 | 設計判断待ち |

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

## P1 と R5 の境界

- R5 は，`#$x` が捕捉する値パターン式にどの環境を与えるかという**実行時意味論**
  を固定する．
- P1 は，その式が原子入力環境だけで型付くことを，不透明・高階な matcher の
  流れを含めて**静的に保証する方法**を決める．
- Lean の `VPScoped` は P1 の候補述語であり，現在の `WTTree.atom` と最終
  `type_safety` には配線されていない．したがって R5 の完了を P1 の完了と
  みなしてはならない．

## P2 と R7・R9 の境界

- R7 は，固定された単相導出内で matcher 値の固有能力を保ち，利用位置の
  `MatcherSlot` で検査する規則と実行時不変量を固定する．
- R9 は，one-way 構造関係や固定入力に相対的な局所主要性までを切り出す．
- P2 は，一般化された `Matcher` の型スキームを利用点でインスタンス化しても
  その能力を強化しない関係を設計する．通常の HM インスタンス化をそのまま
  使う限り残るため，R7 や R9 の局所結果だけでは閉じない．

## 記録の読み方

各解決済み記録は，原則として次を分離する．

1. 以前の記述または証明で何が問題だったか．
2. 論文で固定した解決．
3. Egison 本体が同じ性質をどこまで実装しているか．
4. Lean がどの定義・定理まで機械化しているか．
5. P1/P2，停止性，実装の部分近似など，解決に含めない境界．

青字の abstract，introduction，conclusion，依存図，付録案内，例示は，
R1–R11 の主張を各所へ反映したものである．独立した問題として重複登録しない．

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
