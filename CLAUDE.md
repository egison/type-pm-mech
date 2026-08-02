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

## P2 の証明スコープ

- P2 の完了条件は **非 CAS formal core** に限る。二 sort、producer-stable
  one-way match、実 clause からの evidence／`ShapeCap`、二種 W／Gen／Inst を通る
  value-flow 非強化、`CoverageOK` 必須の source/runtime safety、singleton direct-self を含む。
- formal core は、検証・freeze 済みの observability／constructor signature／alias
  table を入力としてよい。公開 source bridge には `CoreSpecWF` を使い、任意の
  `RuntimeSpec` を source calculus の代用として最終定理に残さない。
- `CoreSpecWF` の checker は静的 `SourceCtx` を読む。checker の明示引数に target 型や
  runtime environment がないことだけから純粋性を主張せず、concrete instantiation で
  target-derived seed の不在、evidence coherence、captured environment の
  `substAdmissible`、`literalSubstitute` を放電する。Ξ-closed と captured environment
  の closedness を混同しない。
- P2 独立層の代数定理と `CoreSpecWF` 相対 runtime invariant を、end-to-end source
  Preservation／Progress／Type Safety と呼ばない。source `HasTy`／`ValueTy`、
  matching state、二種 Algorithm W の移行が完了するまでは安全性は未機械化である。
- 一般 D4 producer flow（alias・transform・相互再帰・高階 origin）、raw
  graph/signature validator、Egison の ordinary Coverage warning／certified mode、
  import 永続化、D5-CAS pattern view は実装拡張であり、P2 formal core の完了を
  妨げない。これらを core 定理の仮定へ紛れ込ませない。
- P1 の capture admissibility と埋込み計算の停止性は P2 と独立な既存前提として
  明示する。

## Lean の罠(このリポジトリで踏んだもの)

- `Π`・`Σ` は予約トークンなので識別子に使えない(`piE`・`SF`/`SD`/`SP` を使用)。
- 構成子の premise で `∃ x, … ∧ (帰納型自身)` は kernel の nested inductive 制限で弾かれる。スコーレム化して補助判断(`ClauseTy`/`ArmsTy`/`ClausesTy`)か ∀ 形にする。
- doc コメント `/-- -/` は `mutual` ブロックに付けられない(`/-!` を使う)。
- 相互帰納族に `induction` タクティクは使えない(`cases` は可)。帰納には結合再帰子(`Search.rec` など、全 motive を明示して不要側を `fun … => True`)を使う(`search_mem_reaches` が実例)。相互族の premise には対応する(自明でも)IH 引数が挿入されるので intro の数に注意。
- `try exact nomatch h` / `try exact absurd h (by simp)` は内側エラーが `try` を突き抜けることがある。行き詰まり等式は `try cases h` で閉じるのが安全。
- 関数の結果で分岐する証明は、深いパターンの joint match より「意味的ガード関数(`piHit`/`pappHit`/`ppShapeOK` ガード)+反転補題」の形が `split at h` と相性がよい。定義側をその形に書く。
