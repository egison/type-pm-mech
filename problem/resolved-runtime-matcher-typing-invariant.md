# R7：matcher の固有型，slot，対象型整列

## 状態

- 状態：固定単相導出内では解決済み
- 論文での表示：青字（`\new`）
- scheme-level 能力保存：P2 として未解決

## 問題

matching atom の保存性には，matcher が target と整合し，pattern の構造要求を
満たすことを後続状態まで運ぶ必要がある．以前の議論には三つの弱点があった．

### 単一化可能性の非推移性

`τ_m ∼ τ` と `τ_t ∼ τ` から `τ_m ∼ τ_t` を一般には導けない．
異なる単一化子を暗黙に混ぜると，抽出 target の型と matcher 定義側の型を
同じ後続 atom に使う根拠が失われる．

### matcher 値型と consumer slot の混同

`Matcher τ_m` は値が定義時に確立した固有能力であり，
`MatcherSlot τ_p τ_t` は利用位置の要求である．slot へ通った値について，
固有型，構造 one-way 条件，target unifiability を runtime invariant として
回収できなければならない．

### 積 matcher の witness 合成

tuple matcher 値にも canonical な積の intrinsic type を与え，各成分の slot
導出から積位置の構造・target 条件を回収する必要がある．論文の推論規約では，
各成分の structural index を freshen して変数集合を互いに素にするため，
component witnesses の disjoint union を構成できる．この freshening と
value-level coercion の対応を明記しなければ，積の slot invariant が根拠を失う．

## 固定した解決

### `WT-ATOM` の直接 premise

matching atom は直接次を保持する．

- pattern の dual typing：構造 `τ_p`，target `τ_t`
- matcher 値の固有型 `Matcher τ_m`
- matcher-side fresh rename `τ'_m`
- 構造条件 `τ'_m ⊑ τ_p`
- target 条件 `τ_m ∼ τ_t`
- target 値の型 `v : τ_t`

共通の第三型を介した二つの `∼` ではなく，必要な関係を atom に直接保存する．
target 側では一つの prevailing substitution を使い，構造 witness は
binding-independent な構造添字だけへ作用させる．

### 固有型と slot

matcher 値の intrinsic `Matcher` 型は定義時の能力を表し，利用点でのみ
`MatcherSlot` へ一方向 coercion する．構造 one-way check と target unification は
slot の導出から回収する．matcher literal を自身の定義注釈に対して checking する
文脈だけは，能力を注釈型で確立するための専用例外とする．

### 単相 rigidity

固定単相導出では，異なる `Matcher` 添字同士を通常の単一化で書き換えない．
これにより，bare-variable capability の matcher を構造化型へ cast して
constructor pattern に使う経路を閉じる．

特に built-in `something` の `T-SOME` と runtime 値型は，添字を必ず fresh な
裸変数に固定する．`something : Matcher [a]` のような構造化 capability を
宣言的に直接与えると，constructor/tuple site の Progress 反例が再び開くためである．
これは固定単相導出で閉じた問題であり，一般化された scheme の instance を扱う
P2 とは区別する．

### 積 matcher の canonical type と合成

積 matcher 値には成分 intrinsic types の積を canonical intrinsic type として与える．
各成分の derived slot judgment を取り出し，互いに素になるよう freshen された
component structural witnesses を合併して，積位置の witness を構成する．
runtime tuple pattern は必要に応じて成分 atoms へ分解する．

## 論文との対応

- `Matcher`／`MatcherSlot` の区別と dual check
- Matcher Rigidity
- typed values と `WT-ATOM`
- Matcher-Value Slot Invariant
- Conditional Type Safety の target substitution convention
- Appendix の coercion-spine と terminal coercion の場合分け

## Egison 実装との対応

### dual check

[`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs) の
`checkMatcherAdmissibility` と
[`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs) の
`coerceMatcherToSlot` が，構造 one-way check と target unification を行う．
tuple slot は `coerceSlotTuple` などで成分別に処理する．

関連回帰：

- [`mini-test/60-matcher-slot-parse.egi`](../../egison/mini-test/60-matcher-slot-parse.egi)
- [`mini-test/61-matcher-slot-coerce.egi`](../../egison/mini-test/61-matcher-slot-coerce.egi)
- [`mini-test/80-matcher-slot-tuple.egi`](../../egison/mini-test/80-matcher-slot-tuple.egi)
- [`mini-test/123-multisite-matcher-param.egi`](../../egison/mini-test/123-multisite-matcher-param.egi)

`patternDualType` の probe が何らかの推論エラーで失敗した場合は，その理由を問わず
fresh type へ fallback して false rejection を避ける．後段の通常推論が別の
エラーを検出する場合はあるが，その site の dual structural check は
弱くなり得る．

### rigidity

`Type/Unify.hs` の `unifyG` は，添字がすでに同一でない `TMatcher` 同士を
通常単一化しない．注釈付き matcher literal の定義時だけ，
`Type/Infer.hs` の `unifyMatcherDefType` を使う．

負の回帰：

- `test/type-error/50-matcher-collection-hetero.egi`
- `test/type-error/51-matcher-cast-structured.egi`
- `test/type-error/53-matcher-alias-specialize.egi`

ただし [`Type/Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs) の
`instantiate` は通常の HM instantiation である．単相 rigidity は P2 を解かない．

## Lean 機械化との対応

[`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean) は次を持つ．

- `ValueTy.matcherV`
- `ValueTy.something`
- `ValueTy.prodMatcher`
- `ValueTy.slotV`
- `ValueTy.prodSlot`
- `WTTree.atom`
- `WTTree.atomSlot`
- `WTTree.atomTuple`

`WTTree.atom` は `Unifiable τ_m τ_t` と `ValueTy v τ_t` を直接 premise にする．
[`TypePM/TypeRel.lean`](../TypePM/TypeRel.lean) の `StructReaches`，
`oneWay_trans`，`structReaches_instSig`，`structReaches_prod` が
構造添字の到達関係を支える．

[`TypePM/Metatheory/Preservation.lean`](../TypePM/Metatheory/Preservation.lean) の
`slot_value_inv` と `matcher_slot_invariant` は，slot 型の runtime 値から
成分別の matcher 情報を回収する．`slot_value_inv` は oracle 不要の核である．

`HasTy.something`／`ValueTy.something` は `something` の添字を裸変数に固定し，
`valueTy_something_var`，`something_rejected_at_data`，
`something_rejected_at_prod` が構造化位置での排除を支える．

境界は次である．

- Lean の宣言的 `Scheme.Inst` は通常の無制限 instantiation である．
- matcher rigidity 専用の宣言的 relation はない．
- `ValueTy.matcherV` は現在の導出が保持する定義由来の型付け証拠であり，
  matcher 値の添字が一意であるという canonical-type theorem は証明されていない．
- `StructReaches` は一般の `PatTy` から自動導出されず，最終 `type_safety` は
  `hsiteReach` oracle を取る．
- 論文の「成分 witness の互いに素な和」より Lean の
  `slot_value_inv` の結論は弱く，成分 slot 型を返すところまでである．
  Lean は component variables の disjointness と大域 witness の合併を
  独立定理としては証明していない．

## P2 へ残るもの

[P2](matcher-capability-instantiation.md) は，一般化された matcher 値を scheme から
取り出すときも intrinsic capability が強化されない instance relation を設計する．
現在の固定事項だけで `mPoly : ∀a. Matcher a` を安全に具体構造へ
instance 化できるわけではない．

## 回帰確認

- 二つの `Unifiable` premise を推移的に合成しない．
- matcher 値の intrinsic 型と slot の要求型を同一視しない．
- 論文では tuple component の freshening と disjointness を明示し，
  Lean については未証明の大域 witness 合併を主張しない．
- 単相 rigidity の回帰だけで P2 完了と書かない．
