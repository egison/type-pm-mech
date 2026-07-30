# R12：matcher 定義の次マッチャー分解とホール検査

## 状態

- 状態：設計と形式上の判定は解決済み
- 論文での表示：今回補った Algorithm W と `fresh_rename` の説明は青字（`\new`）
- Lean：宣言的な成分境界と成分別 slot 型付けは実装済み
- Egison：明示タプル境界，完全型の freeze，成分別 slot 検査を実装済み
- 残作業の分類：本項の実装補修は完了（scheme-level の P2 は別）

## 問題

matcher 節の primitive-pattern pattern が `k` 個のホールを持つとき，次マッチャー式
`M` から各ホールへ送る `k` 個の成分を決め，各成分をそのホールの要求
`MatcherSlot κ_l λ_l` に対して検査する必要がある．ここでは次の二つを分けなければ
ならない．

1. **成分境界**：`M` のどの部分式を第 `l` ホールへ対応させるか．
2. **成分検査**：対応付けた式がそのホールの構造・ターゲット要求を満たすか．

これらを混ぜると，積型を持つ不透明な式を暗黙に複数ホールへ分けたり，逆に，
変数・application・lambda など成分式の構文形によって必要な構造検査を
省略したりする．

また，論文の Algorithm W Step 3a/3a′ は，以前 `∼` を書きながら「unify」
「要求を蓄積する」と説明していた．`∼` は伝播しない検査として定義されているので，
既存 `MatcherSlot` の両成分と未確定変数の slot 化には使えない記号であった．

## 固定した解決

### 1．複数穴の成分境界

`k` 個のホールに対する分解を次で固定する．

```text
k = 1    : M 全体を唯一の成分とする
k ≠ 1    : M 自身が明示的な k 要素タプル (M₁, ..., Mₖ) のときだけ分解する
それ以外 : 型エラー
```

したがって，2ホールに対して次は区別される．

```text
(m1, id mPoly)    -- 外側が明示的な2タプルなので成分へ分解する
id (m1, m2)       -- 積を返しても外側が application なので分解しない
ms                -- 積型を持っていても外側が変数なので分解しない
```

0ホールでは明示的な空タプル `()` を要求する．任意の product-matcher 式を
型だけから分解する拡張は採用しない．

### 2．各成分の検査

外側の分解で得た各 `M_l` は，式の構文分類ではなく，ホールとの単一化前に推論した
完全な型を用いて，期待 slot `MatcherSlot κ_l λ_l` に対して検査する．

- `M_l : Matcher μ` なら，固有添字 `μ` を保存する．型変数だけを再帰的に
  新鮮化した `μ' = fresh_rename(μ)` について構造検査 `μ' ⊑ κ_l` を行い，
  その後にターゲット整合性を検査する．ターゲット側の単一化結果を，
  定義時の固有能力を強化する型として扱わない．
- `M_l : MatcherSlot κ' λ'` なら，通常の伝播する等式制約
  `κ' = κ_l`，`λ' = λ_l` を順に MGU で解き，前の代入を次へ受け渡す．
- `M_l : γ` で `γ` が未確定の新鮮型変数なら，通常の等式
  `γ = MatcherSlot κ_l λ_l` を MGU で解く．

同じ完全な型を持つなら，次のような表記の違いだけで判定を変えない．

```text
mPoly
id mPoly
(\m -> m) mPoly
```

これらがいずれも `Matcher α` なら，同じ構造ホールに対して同じ結果になる．一方，
`list mPoly : Matcher [α]` は固有型自体が異なるので，異なる判定になってよい．

ここでいう「構文形に依存しない」は，**成分境界を決めた後の成分検査**についての
条件である．複数穴の成分境界を明示タプルに限定することとは矛盾しない．

### 3．`fresh_rename`

`fresh_rename(τ)` は，型木を再帰的にたどって型変数を新鮮な型変数に置き換え，
同じ変数の反復出現には同じ置換を用い，すべての型構成子を保存する．例えば，

```text
Maybe [a]  -> Maybe [a']
(a, a)     -> (a', a')
```

となる．外側だけを残して内側の構造を新鮮な一変数へ潰す操作ではない．

## 論文との対応

- `T-MATCHER` は `m_i = (m_i^1, ..., m_i^{k_i})` としてホールごとの成分を明示し，
  各 `m_i^l` に `MatcherSlot τ_{p,l}^i τ_{t,l}^i` を要求する．
- Matcher Consistency (1a) は，次マッチャータプルがホールごとに一成分を与え，
  各成分をそのホールの slot で消費すると定める．
- Algorithm W Step 3a/3a′ は，`MatcherSlot` の両成分と新鮮変数について，
  `∼` ではなく通常の伝播する等式制約を MGU で解く記述へ修正した．
- 型関係の記法節に，上記の再帰的な `fresh_rename` の一文定義を追加した．

Appendix の Algorithm W Step 3b にある「タプル式またはそれに束縛された変数」は，
`matchAll` の matcher 位置における slot-tuple coercion の説明である．matcher 定義の
次マッチャーをホールへ分解する本項の境界とは別である．

## Lean 機械化との対応

[`TypePM/Typing.lean`](../TypePM/Typing.lean) の `decomposeME` は，

- `k = 1` なら式全体を一成分
- `k ≠ 1` なら正確に `k` 要素の `.tuple`

とする．同ファイルの `ClauseTy.mk` は，`Ms.zip pairs` の各成分に
`HasTy ... (.slot κ_l λ_l)` を要求する．ここには変数・application・lambda を
区別して slot 検査を省略する分類器はない．

[`TypePM/Metatheory/Progress.lean`](../TypePM/Metatheory/Progress.lean) の
`decomposeME_tuple` は，`k ≠ 1` で分解に成功した元の式が実際にタプル式であることを
反転する．[`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean)
の `decodeM_typed` も同じ成分境界を使って実行時タプル値を成分へ対応付ける．

[`TypePM/TypeRel.lean`](../TypePM/TypeRel.lean) の `Ty.applyRen`／`RenamesTo` は，
型構成子を保った再帰的な型変数改名を表す．ただし Algorithm W 自体は Lean で
機械化されていないので，Step 3a/3a′ の MGU 実装順序まで証明済みという意味ではない．

## Egison 実装との対応

現行 [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs) は，
本項の成分境界と成分検査を形式仕様に合わせて実装している．

### 成分境界

- `k = 1` では次マッチャー式全体を一成分として扱う．
- `k ≠ 1`（0 を含む）では，外側が明示的な正確な `k` 要素
  `ITupleExpr`／`TITupleExpr` の場合だけ成分へ分ける．
- 変数や application が積 matcher 型を返しても，型から複数穴へ暗黙分解せず
  その場で型エラーにする．

### 成分検査

各成分は式構文によらず完全な推論型から `HoleComponentType` へ取り込まれる．
すべての成分を hole target 単一化より先に一括して取り込む．各 hole 成分では，
そこに含まれるすべての `Matcher μ` の能力を一つの injective な置換で再帰的に
改名し，元の target 型と分離して保存する．このため同じ変数の反復出現だけでなく，
積内の複数 `Matcher` 葉が共有する変数も保存される．未確定変数は
`MatcherSlot` へ確定する．

最終注釈を含む代入が得られた後，各 hole の完全な期待 slot を構成し，
[`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs) の既存経路へ送る．
積 slot の one-way 検査では，最初の structural slot に属した型変数の集合を
入れ子を含む全成分へ固定して渡す．先行成分の代入で matcher 側の変数が後続 slot
位置へ現れても，その変数を新たに束縛可能とは扱わない．
`Matcher μ` は freeze 済み能力で構造検査し，元の `μ` で target を検査する．
既存 `MatcherSlot` は構造・target の両成分を通常の MGU で検査し，その代入を
型付き構文木と一般化前の型へ反映する．

## P2 との境界

本項は，利用箇所へ届いた**単相の完全な成分型**をどう検査するかを固定する．
[P2](matcher-capability-instantiation.md) は，その型を環境から取り出す scheme
instantiation が定義元の matcher 能力を保存するかという，より前段の問題である．

したがって，構文依存分岐を除去し明示タプル境界を強制しても，通常の HM
instantiation が `mPoly : Matcher a` を `Matcher [Integer]` に能力強化できる問題は
別に残る．逆に P2 の設計を決めるために，本項の二つの判定を再検討する必要はない．

## 実装補修の完了条件

- [x] `k = 1` では式全体を一成分として検査する．
- [x] `k ≠ 1` では明示的な正確な `k` 要素タプルだけを受理する．
- [x] 各成分の固有型をホールのターゲット単一化前に保存する．
- [x] 各ホールについて完全な `MatcherSlot κ_l λ_l` を構成する．
- [x] `Matcher μ` は再帰的 `fresh_rename` と既存 dual check で検査する．
- [x] `MatcherSlot κ' λ'` は期待 slot と両成分を通常の MGU で検査する．
- [x] 変数・application・lambda などの構文形による検査の省略をなくす．
- [x] `id (m1, m2)` のような非タプル外形を複数穴で拒否する回帰を追加する．
- [x] 同じ `Matcher α` を持つ変数・application 形が構造ホールで同じ結果になる
      正負の回帰を追加する．
- [x] 入れ子の型構造を保存する fresh rename の回帰を追加する．
- [x] 一つの積成分内で共有された matcher 能力変数を同じ fresh 変数へ写す正回帰を
      追加する．
- [x] 反復 slot 変数を介して matcher 側変数を再束縛しない one-way の負回帰を
      追加する．

## 保証範囲

R12 で解決し実装したのは，次マッチャーの成分境界と，各成分に適用すべき
固定単相の静的判断である．P2 の scheme-level 能力保存インスタンス化，
P1 の値パターンスコープ，Algorithm W 全体の主要性証明は，
この記録だけでは完了しない．
