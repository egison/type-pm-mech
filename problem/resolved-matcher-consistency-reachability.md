# R3：matcher 節の到達可能性と arm 網羅性

## 状態

- 状態：解決済み（形式条件）
- 論文での表示：青字（`\new`）
- 実装状況：一部は完全，一部は保守近似または警告
- P1/P2 との関係：definition-time 条件自体は独立

## 問題

matcher 節は先頭から選ばれ，primitive-pattern pattern が一度成功すると，
その節の data-pattern arms を試す．ここには二種類の行き詰まりがあった．

### 節の到達不能

bare-hole primitive-pattern pattern `$` はすべてのパターンに一致する．Coverage の
general clause や refinement clause より前に置くと，後続節は到達不能になる．
特に constructor pattern が早い catch-all に捕まり，構造能力を持たない
next matcher へ委譲され得る．

### 選択済み節の arm 枯渇

primitive-pattern pattern が成功した後は，後続 matcher 節へ戻らない．
その節のすべての data-pattern arm が target に失敗すると，選択済み節の中で
行き詰まる．多相 matcher では，定義時の型だけでなく全型代入インスタンスの値を
覆う必要がある．

## 固定した解決

論文の Matcher Consistency に次を固定した．

1. bare-hole matcher clause は唯一の最終 catch-all とする．
2. Coverage が要求する general constructor/tuple clauses と任意の refinements は，
   catch-all より前に置く．
3. general，tuple，refinement，value-pattern，catch-all の各節で，data-pattern arms
   は target 型の全値を覆う．
4. 多相 `Matcher τ` では，`τ` の全代入インスタンスについて 3 を要求する．
5. arm 網羅性は自由データ構成子 `Σ_D` に対する通常の ML-style exhaustiveness
   として読む．非自由 target 上の表層 match 網羅性とは別物である．

これにより，節列へ到達した constructor/tuple pattern には到達可能な一般節があり，
先に refinement が選ばれた場合も，選択済み節内に適用可能な arm がある．

## 論文との対応

- Definition “Matcher Consistency” の (1c)，(2)，(3)，(4)
- `T-MATCHER` の catch-all side condition
- Conditional Matching State Progress
- 実装節の arm exhaustiveness，Coverage，clause ordering

循環する catch-all 委譲は stuck terminal state ではなく発散として扱う．その停止性は
R4 の `StepTotal` 側へ分離される．

## Egison 実装との対応

### catch-all の順序

[`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs) は
`IMatcherExpr` ごとに bare-hole 節の存在を要求し，最初の bare-hole の後に節があれば
“move the catch-all clause last” 型の通常エラーにする．

回帰先は
[`minitest/009-matcher-clause-order.egi`](../../egison/minitest/009-matcher-clause-order.egi)
である．実行されるのは正例で，ファイル冒頭の負例はコメントとして診断を記録する．

ただし実装は bare-hole の位置を検査するだけで，論文が要求する catch-all の
data arm と target binding の形全体までは強制しない．

### arm 網羅性

`pdArmsExhaustive` は次を認識する保守近似である．

- 変数，ワイルドカード，irrefutable tuple arm
- empty と cons/snoc の組
- `True` と `False` の組

現在は外側の matcher literal が主対象であり，別 matcher の body を推論中に現れる
matcher literal は診断対象外である．user-defined ADT の全構成子列挙も，
一般 catch-all がなければ保守的に拒否され得る．回帰先は
[`mini-test/124-matcher-dp-arm-exhaustiveness.egi`](../../egison/mini-test/124-matcher-dp-arm-exhaustiveness.egi)
である．

Coverage は opt-in の warning-level 診断であり，hard error ではない．また，
next matcher の固定単相検査は
[R12](resolved-next-matcher-slot-checking.md) に従って実装済みである．1 hole
では式全体を一成分とし，0 hole または複数 hole では明示的な同要素数の
タプルだけを受理する．各成分は完全な `MatcherSlot` の構造・target 両添字に
対して検査され，式構文形による skip はない．それでも Coverage，scoped arm
exhaustiveness，scheme-level の P2 が残るため，Egison が形式的 Matcher
Consistency 全体を強制するとは記述しない．

## Lean 機械化との対応

[`TypePM/Typing.lean`](../TypePM/Typing.lean) の `ConsistentClauses` が次を持つ．

- `coverage`
- `coverageProd`
- `catchall`
- `holeAfterGenerals`
- `armExh`
- `ppBindNodup`
- `armBindNodup`

`armExh` は `∀ U v, VShape v (τ.applyTS U) → ...` と量化し，多相 matcher の利用時
インスタンスを明示的に覆う．
[`TypePM/Metatheory/Progress.lean`](../TypePM/Metatheory/Progress.lean) の
`vshape_applyTS` と `armExh_instance` がこの条件を利用する．
二つの `Nodup` 条件は，primitive-pattern pattern の捕捉環境と data-pattern の
束縛環境を重複なく結合するために使われる．`ppp_preservation` も対応する
捕捉名の相異性を `hnd` として明示的に受け取る．

重要な差が二つある．

1. `holeAfterGenerals` は，各 bare-hole より前に Coverage general clauses があること
   だけを要求する．論文の「唯一の bare-hole が最終節」という強い構文条件を
   完全には表していない．
2. `armExh` は全値を量化する意味的 `Prop` である．論文の有限な構文検査
   アルゴリズム自体は Lean で実装・決定可能性証明されていない．

Lean の条件は現在の進行性証明に十分だが，Definition 4.2 の構文的同一物ではない．
また，これらの definition-time 条件自体は P1/P2 から独立だが，runtime progress
や preservation で利用するときは，value-pattern refinement の捕捉に P1，
runtime matcher capability の保持に P2 の条件が別途必要になる．

## 保証範囲

R3 で固定したのは形式条件と，その条件が進行性に必要な理由である．次は含まない．

- Egison の全 matcher に対する形式条件の完全強制
- Coverage warning を error にするライブラリ設計
- 埋込み評価の停止性（R4）
- 値パターン捕捉の静的許容性（P1）
- matcher capability の scheme-level 保存（P2）

## 回帰確認

- bare-hole 後の節を Egison が受理しないこと．
- 多相 matcher の `armExh` を定義時型だけに狭めないこと．
- selected clause の arm failure を後続 matcher clause への fall-through と
  誤解しないこと．
- 論文条件，Lean の意味的条件，Egison の保守近似を別々に記述すること．
