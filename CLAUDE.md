# type-pm-mech 固有ルール

`type-pm-mech` は，`Matcher κ τ` と `MatcherSlot κ τ` を持つ非 CAS Egison core を
Lean 4 で機械化するプロジェクトである．親ディレクトリ `../CLAUDE.md` の規則，特に
commit／push はその都度の明示指示がある場合に限るという規則にも従う．

## ビルド

- Lean toolchain は `lean-toolchain` で固定する．外部依存はなく Mathlib も使わない．
- 全体検証はリポジトリ直下で `lake build` を実行する．
- 形式仕様 `tex/main.tex` は `tex/` で `make` を実行して検証し，
  `tex/type-pm-mech.pdf` を生成する．`main.pdf` は作らない．

## 現行の証明境界

- 現行 calculus は `TypePM/P2/` の二 sort・二 index 版だけである．旧一添字 calculus，
  抽象 `RuntimeSpec`／`CoreSpecWF`，それらに相対的な旧安全性証明を復活させない．
- source matcher literal は actual clause evidence，`ShapeCap`，`CatchAllLast`，
  data-arm exhaustiveness，binder 線形性，`CoverageOK` をすべて要求する．
- scheme の宣言的 instance では capability binder を capability variable へだけ写し，
  producer capability を consumer demand に合わせて構造化する経路を追加しない．
  binder image の相異性と ambient freshness は Algorithm W の強い allocation witness にだけ
  要求する．capability binder の variable-only mapping と構造的な target specialization は
  一つの global pair へ潰さず，binder-local に順序付けて適用する．利用後の輸送も
  producer capability の variable-only mapping と target specialization に限定する．
  `let` の輸送では内側の generalization
  binder を target ambient の外へ局所的に freshen し，数値 identifier の捕捉を避ける．
- recursion は singleton direct-self の単相 `fix` だけを core に含める．alias，mutual
  recursion，高階 origin は fail closed とする．
- Algorithm W の公開 entry point `infer` は，停止する raw 走査 `inferRaw` と
  有限な terminal validator を合成する．公開 `infer` が成功したとき，成功等式だけから
  `infer_success_sound` が concrete `HasTy` を与える状態を維持する．`InferenceInputWF` は
  意図する入力境界を記述するが，fail-closed な validator の soundness 前提には戻さない．
  `WBridgeWF` は validator が内部で構成する証明書であり，呼び出し側の追加前提に
  戻さない．terminal validator の completeness，full principality，principal-type theorem は
  主張しない．
- 動的安全性は concrete `HasTy`／`ValueTy`／matching-state judgments 上で述べる．
  値パターン capture admissibility と局所的な埋込み評価の `StepReady` だけは，
  それぞれ該当する preservation／progress 定理の明示前提としてよい．

## 証明と文書の品質

- `sorry`，`admit`，`axiom` を使わない．型付け導出そのものを field に持つ oracle や，
  任意の capability 輸送を許す blanket premise で穴を隠さない．
- `TypePM.lean` は現行 public surface の全モジュールを import する．変更後は個別 target
  だけでなく必ず `lake build` を通す．
- `TypePM/P2/RecursiveExamples.lean` の list／multiset direct-self 正例，coverage 不足
  multiset と producer-strengthening の負例を回帰として維持する．
- Lean の規則と `tex/main.tex` の仕様を同期する．過去の進捗日誌，解決済み問題メモ，
  旧 calculus の説明は現行 README へ残さない．
