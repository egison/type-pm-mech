# R6：実行時環境と MNode の整型不変量

## 状態

- 状態：解決済み（実行時判断の補強）
- 論文での表示：青字（`\new`）
- 解決の種類：保存性証明に必要な環境 premise の明示

## 問題

式評価の型保存を matching-state 保存性から利用するには，式を評価する実行時環境が
静的文脈を実現している必要がある．従来の `WT-STATE`／`WT-MNODE` は stack，
substitution，MNode の接尾辞・出現順を追っていたが，次が明示されていなかった．

- 外側の runtime environment `ρ` が `Γ` を実現すること
- pattern function 内部の environment `ρ_f` が `Γ_f` を実現すること

このままでは，`M`，`N`，値パターン式，pattern-function body の評価に
expression-evaluation induction hypothesis を適用する根拠がない．

## 固定した解決

### 型付き環境

`ρ ⊨ Γ` を，`Γ` の各 scheme instance に対して `ρ` の値が対応型を持つという
runtime environment typing として導入する．同様に MNode 内で `ρ_f ⊨ Γ_f` を
要求する．

### 既存の型付き substitution と stack との結合

`θ` は現在までの binding context `Δ₀` を実現し，stack は `Δ₀` から最終
`Δ_goal` まで左から右へ文脈を受け渡す．この既存不変量へ型付き環境を結合する．
MNode 内の `θ_f` は外へ漏らさず，内部 stack だけを型付ける．

### 既存の MNode 構造不変量との結合

未消費 parameter 環境 `rem` について次を保持する．

- 元の parameter 環境の接尾辞である
- parameter 名は相異なる
- 内部 stack の埋込み変数出現列と `rem` が一致する
- 残りの実引数パターンを外側文脈で型付けできる
- 固定した内側 dual context から各 parameter の dual type を回収できる

これらの既存条件と `ρ_f ⊨ Γ_f` を併用することにより，
`MS-MNODE-VARPAT`，`MS-MNODE-DONE`，`MS-MNODE-STEP` の保存性を逐次再構成できる．

## 論文との対応

- “Typed runtime environments”
- Figure の `WT-ATOM`，`WT-MNODE`，`WT-STACK`，`WT-STATE`
- Conditional PPP Type Preservation
- Conditional Type Safety の `MS-PATFUN-*` ケース
- Appendix の runtime-environment weakening と MNode 全ケース

論文の記号 `ρ ⊨ Γ` は，単に環境の変数 domain が一致するだけではなく，
scheme の各許容 instance に対する値型付けまで含む．

## Egison 実装との対応

R6 は Egison に新しい runtime check を要求するものではない．Egison の closure，
matcher value，pattern-function evaluation が実際に持つ lexical environment を，
形式証明側で型付き環境として表現する修正である．

実装との対応を調べるときは，環境の値配置だけでなく，型推論が一般化した scheme と
runtime closure が捕捉する値の対応を確認する必要がある．P2 が未解決なので，
scheme の全 instance を無条件に正当化したとは読まない．

## Lean 機械化との対応

[`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean) に次がある．

- `EnvTyped`
- `SubstTyped`
- `WTTree`／`WTStack`
- `WTStateAt`／`WTState`
- `RemInPhi`

`WTStateAt` は `EnvTyped Γ s.ρ` と，型付き `s.θ`，整型 stack を連言する．
`WTTree.mnode` は `ρ_f` の domain/instance typing，`θ_f` の `SubstTyped`，
接尾辞，出現列，内外 dual context を明示する．

Lean では MNode 内部 stack の入力を `Δθf`（`dom_typed(θ_f)` に対応）とする．
これは pattern-function body 内で先に束縛した変数を後続値パターンが参照するために
必要だと機械化で判明した精密化であり，現行論文も同じ入力文脈へ修正済みである．

[`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean) には
`ppm_occs`，`matom_occs`，`step_occs`，`ppm_noOr`，`matom_noOr` と，
`preserve_mnodeDone`，`preserve_mnodeVarpat`，`preserve_patfunEnter` があり，
MNode を含む保存性の分岐を支える．

## 保証範囲

R6 で解決したのは，保存性証明に必要な runtime environment invariant の形である．
次は別に残る．

- scheme instance が matcher capability を保存すること（P2）
- 捕捉式の自由変数条件を source typing から得ること（P1）
- expression evaluation 全体の無条件型保存

## 回帰確認

- 式評価 IH を使う各ケースで，評価環境を実現する静的文脈を示す．
- MNode の内部 substitution を外側の substitution へ混ぜない．
- `MS-MNODE-VARPAT` 後も parameter の接尾辞と出現順を保つ．
- `EnvTyped` の scheme-instance premise を P2 なしに自動放電したと書かない．
