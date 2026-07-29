# R1：`match` の表層意味論と定理の射程

## 状態

- 状態：解決済み
- 論文での表示：青字（`\new`）
- 解決の種類：意味論と定理の射程の明確化

## 問題

論文の構文には複数節の `match` が現れる一方，操作的意味論と型安全性証明の
中心は単一節の `matchAll` である．この差を明記しないと，次まで形式化し証明した
ように読めてしまう．

- 複数節を先頭から試す表層 `match` の評価
- 各節の結果列を連結する操作
- 最初の結果を取り出す `head`
- すべての節が失敗したときの runtime match failure
- `match` 節の網羅性

特に，空の探索結果は `matchAll` では正常な失敗であるのに，表層 `match` では
値ではない runtime match failure を生む．両者を同じ型安全性定理へ入れるには，
例外または失敗結果まで含む別の意味論が必要になる．

## 固定した解決

表層 `match` は，概念上，単一節 `matchAll` の結果列を順に連結し，その `head` を
取る構文糖とする．ただし，現在の core calculus と Conditional Type Safety の
対象は，単一節 `matchAll` の**成功して値を返す評価**に限定する．

したがって，次は現在の定理の外側に置く．

- `head` と列連結の形式意味論
- すべての結果列が空である場合の表層 match failure
- 独立した `T-MATCH` の健全性定理
- 非自由データに対する表層 match 節の網羅性判定

これは失敗を安全な値とみなす修正ではない．定理が扱う評価と，表層実装が報告する
失敗を分離した修正である．

## 論文との対応

- §3 の “Match as syntactic sugar”
- Theorem “Conditional Type Safety”
- §5 の「非網羅な `match`」と matcher arm exhaustiveness の区別

青字では，`head (matchAll₁ ++ … ++ matchAllₙ)` という意図と，空列時の表層失敗が
定理外であることを明記した．

## Egison 実装との対応

Egison 本体は表層の複数節 match と失敗処理を実装しているが，R1 はその実装を
新しく変更した記録ではない．論文の core が実装全体を形式化しているという
過大な主張を避け，形式対象を切り分ける記録である．

実装の探索順序や例外表示が変わっても，core の `matchAll` 定理へ自動的に含まれる
わけではない．表層 `match` の健全性を将来主張するなら，実装に対応する失敗結果と
列操作を意味論へ追加する必要がある．

## Lean 機械化との対応

Lean の式意味論 [`TypePM/Semantics.lean`](../TypePM/Semantics.lean) は
`matchAll` を `Eval` に持ち，探索結果を有限リストとして読む．
型安全性の入口は
[`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean)
の `type_safety` である．

表層 `match`，`head`，結果列の連結，runtime match failure は Lean の対象ではない．
したがって Lean の定理も，論文で固定した狭い射程と整合する．

## 保証範囲

R1 で解決したのは，既存定理の対象を正確に述べることである．次は証明していない．

- 表層 `match` が必ず値または明示的失敗を返すこと
- 表層の節選択順序と Egison の探索実装の完全な対応
- 非自由データに対する match 節網羅性の決定可能性

## 回帰確認

- 論文の型安全性定理を引用するときは「単一節 `matchAll` の成功評価」と書く．
- match failure を値保存の結論へ含めない．
- matcher clause 内の data-pattern arm 網羅性（R3）と，表層 match 節の網羅性を
  混同しない．
