# type-pm-mech 固有ルール

`../type-pm-paper/`(λ_PM:非自由データ型上のアドホック多相パターンマッチの計算体系と型システム)のメタ理論を Lean 4 で機械化するプロジェクト。親ディレクトリ `../CLAUDE.md` の Git 規約(commit/push は明示指示時のみ)に従う。

## ビルド

- **`lake build` を使う**(elan/lake は `~/.elan/bin`。PATH に無ければ `export PATH="$HOME/.elan/bin:$PATH"`)。
- ツールチェーンは `lean-toolchain` で固定(type-tensor-mech と同じ v4.31.0)。勝手に上げない(上げるときは全ビルド+Examples の通過を確認)。
- 生成物は `.lake/` のみ(gitignore 済)。外部依存なし(Mathlib 不使用)。

## 証明の方針

- `sorry` = 「論文に証明があり、未機械化」の印。**新しい `sorry` を増やす変更は原則しない**(定義変更でやむを得ず増える場合は README の現状セクションを更新)。`axiom` は使わない。
- 補題・定理・規則の名前と doc コメントは論文の番号(Fig 1–6 / Def 4.1–4.2 / Lem 5.2, 5.4, 5.5, C.2 / Thm 5.1, 5.3, 5.6, 5.7)と対応させる。対応表と設計判断(名前ベース環境意味論、宣言的インスタンス化読み、fuel 付きインタプリタなど)は README.md にあり、**論文との意図的な差分は必ず README の「設計判断」に追記する**。
- `Examples.lean` は論文 §2 と付録 A.1 の実測例の機械検証(実行 4 本 + 型付け導出、全て証明済)。定義を触ったら最優先でここが通ることを確認する。
- 論文本文(`../type-pm-paper/main.tex`)が真実の源。定義のズレを見つけたら、勝手に合わせず報告する(既に報告済みの 2 件は README「機械化が浮かび上がらせた論文の細部」参照)。

## Lean の罠(このリポジトリで踏んだもの)

- `Π`・`Σ` は予約トークンなので識別子に使えない(`piE`・`SF`/`SD`/`SP` を使用)。
- 構成子の premise で `∃ x, … ∧ (帰納型自身)` は kernel の nested inductive 制限で弾かれる。スコーレム化して補助判断(`ClauseTy`/`ArmsTy`/`ClausesTy`)か ∀ 形にする。
- doc コメント `/-- -/` は `mutual` ブロックに付けられない(`/-!` を使う)。
- 相互帰納族に `induction` タクティクは使えない(`cases` は可)。帰納には結合再帰子(`Search.rec` など、全 motive を明示して不要側を `fun … => True`)を使う(`search_mem_reaches` が実例)。相互族の premise には対応する(自明でも)IH 引数が挿入されるので intro の数に注意。
- `try exact nomatch h` / `try exact absurd h (by simp)` は内側エラーが `try` を突き抜けることがある。行き詰まり等式は `try cases h` で閉じるのが安全。
- 関数の結果で分岐する証明は、深いパターンの joint match より「意味的ガード関数(`piHit`/`pappHit`/`ppShapeOK` ガード)+反転補題」の形が `split at h` と相性がよい。定義側をその形に書く。
