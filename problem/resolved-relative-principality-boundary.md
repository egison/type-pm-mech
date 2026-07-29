# R9：相対的主要性と Algorithm W の主張境界

## 状態

- 状態：局所結果と主張境界は解決済み
- 論文での表示：青字（`\new`）
- full Principal Type Property：未証明
- 主な残件：P2

## 問題

以前の論文は，matcher rigidity と `Matcher`／`MatcherSlot` coercion を含む系全体に
ついて，Hindley--Milner と同じ full Principal Type Property を証明済みであるかの
ように読めた．しかし，通常の scheme instantiation は matcher 値の intrinsic
capability を強化し得るため，instance relation が未確定なままでは Algorithm W の
完全性と主要型を閉じられない．

一方で，この未解決部分から独立して固定できる局所結果もある．それらを full theorem
と一緒に撤回すると，実際に使える推論上の性質まで失ってしまう．

## 固定した解決

### full claim の撤回

Algorithm W は現在 **candidate Algorithm W** と呼び，次を未証明として明記する．

- capability-preserving scheme instantiation
- Algorithm W 全体の soundness/completeness
- full Principal Type Property
- qualified types を含む主要型定理

pattern-function parameter/result annotation の省略も，示した fragment に対する
local claim に限定する．

### 固定できる局所結果

1. 構造 one-way relation の witness は，固定入力に対して一意である．
2. one-way matching algorithm は関係に対して sound/complete である．
3. 固定した主要入力 derivation の下で，binding context `Δ` の左から右への
   threading は相対的主要性を保つ，という紙上補題を置ける．
4. 固定単相導出内では，tuple matcher／slot coercion の選択を component types から
   局所的に決められる．

3 と 4 は full scheme instantiation を解いた結果ではない．入力 derivation と
単相境界を固定した相対結果である．

## 論文との対応

- pattern-function annotation omission の限定
- §5 の local uniqueness lemmas
- Appendix “Algorithm W”
- Appendix “Principal-Type Lemmas and Open Obligation”
- Relative principality of `Δ`-threading
- dependency graph
- type-class appendix の qualified scheme 境界

青字の目的は「主要型を証明した」と強めることではなく，証明済みの局所部分と
未証明の全体を分離することである．

## Egison 実装との対応

Egison の checker は実際に HM-style inference と局所 coercion check を行う．

- [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs)：
  pattern dual type，pattern-function structural signature，generalization
- [`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs)：
  one-way matcher/slot coercion，matcher rigidity
- [`Type/Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs)：
  scheme instantiation

pattern-function の直接名参照では構造 signature を伝播するが，高階な関数式では
fresh fallback を使う場合がある．これは false rejection を避ける実装上の近似で，
full Algorithm W の完全性証明ではない．

限定型については，scheme instantiation/generalization が constraints を保持し，
[`Type/TypeClassExpand.hs`](../../egison/hs-src/Language/Egison/Type/TypeClassExpand.hs)
が matcher の next matcher と arm 内部を辞書展開する．例えば `eq {Eq a}` と
`sortedList {Ord a}` が動く．しかし，実装が動くことは qualified principal-type
theorem の証明ではない．

## Lean 機械化との対応

機械化済みの局所結果：

- [`TypePM/TypeRel.lean`](../TypePM/TypeRel.lean) の `oneWay_unique`
- [`TypePM/Metatheory/Principal.lean`](../TypePM/Metatheory/Principal.lean) の
  `matchOneWay_sound`／`matchOneWay_complete`

これらにより one-way relation の計算可能性部分は閉じている．ただし，論文が述べる
線形時間 `O(|τ_p| + |τ_m|)` の cost proof は Lean にはない．

現在 Lean で未機械化のもの：

- Algorithm W の6ステップ
- Relative principality of `Δ`-threading
- tuple-of-matchers coercion uniqueness
- slot-tuple coercion uniqueness
- Principal Type Property

したがって，論文付録の青い relative-principality proof は紙上証明であり，
Lean theorem として完成したとは記述しない．

[`TypePM/Metatheory/Polymorphism.lean`](../TypePM/Metatheory/Polymorphism.lean) の
`matcher_polymorphism` は証明済みだが，現在の定理は pattern input context を
`Δ = []` に固定する．論文のより一般的な任意 `Δ₀` 版より狭い．

## P2 へ残るもの

[P2](matcher-capability-instantiation.md) では，matcher intrinsic capability を
強化しない scheme instance relation と，次の両立を決める必要がある．

- `mPoly` の危険な具体構造 instance を拒否する
- `MatcherSlot a a → Matcher [a]` のような安全な parameterized matcher を許す
- 一般化，利用点 instantiation，constraint solving と合成できる
- principal instance と Algorithm W の completeness を述べられる

## 回帰確認

- candidate Algorithm W を完成済みアルゴリズムと呼ばない．
- paper proof と Lean theorem を区別する．
- matcher polymorphism と principal types を同一視しない．
- qualified-type 実装例から qualified principality を結論しない．
- 局所 one-way 結果は P2 と独立なので，未解決扱いへ戻さない．
