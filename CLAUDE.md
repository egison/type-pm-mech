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

- 現行 calculus は `TypePM/` の二 sort・二 index 版だけである．旧一添字 calculus，
  抽象 `RuntimeSpec`／`CoreSpecWF`，それらに相対的な旧安全性証明を復活させない．
- source matcher literal は actual clause evidence，`ShapeCap`，`CatchAllLast`，
  data-arm exhaustiveness，binder 線形性，`CoverageOK` をすべて要求する．
- value-flow scheme の宣言的 instance（context lookup と pattern-function lookup）では
  capability binder を capability variable へだけ写し，producer capability を consumer
  demand に合わせて構造化する経路を追加しない．constructor／primitive signature の
  `Inst` は binder-supported な通常の二 sort structural instance であり，この
  variable-only 条件の対象ではない．
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
  戻さない．terminal validator の completeness は主張しない．principality は
  そのままの形では `PrincipalityCounterexample` の機械化反例
  （`no_principal_type`）により**反証済み**であり，principal-type theorem を
  無証明で復活させない．制限版（coercion-free／per-sort／evidence 法）は open として
  扱う．
- pattern を含まない `λ`/`let`/`fix` 断片の Damas–Milner 一致は，宣言側の埋め込み
  `DM.HasTy.emb`（`DamasMilner.lean`，閉じた signature 上）だけが証明済みである．
  逆方向（conservativity）と algorithmic acceptance（公開 `infer` が DM program を
  全受理すること）は非主張のまま維持する．
- 動的安全性は concrete `HasTy`／`ValueTy`／matching-state judgments 上で述べる．
  primitive-pattern pattern は depth-first・左から右に走査し，一度 hole を通過した後の
  value-pattern-pattern を禁止する．この順序条件から値パターン capture admissibility を
  導出し，公開 preservation の前提には戻さない．局所的な埋込み評価の `StepReady` だけは
  progress 定理の明示前提としてよい．
- 動的定理の唯一の global 条件 `FrozenSigWF` は仮定に戻さず，実行可能 checker
  `frozenSigWFCheck`＋`frozenSigWFCheck_sound`（`SignatureChecker.lean`）で確立する．
  checker は保守的・fail closed を維持する（pattern constructor は単一パラメータ
  collection family に限定，primitive は canonical scheme 一致，唯一の定義的入力は
  `armExhaustive = basicArmExhaustive`）．具体 signature の `signature_wf` は
  `by decide` で discharge し，`native_decide` を新たに導入しない．

## 証明と文書の品質

- `sorry`，`admit`，`axiom` を使わない．型付け導出そのものを field に持つ oracle や，
  任意の capability 輸送を許す blanket premise で穴を隠さない．
- `TypePM.lean` は現行 public surface の全モジュールを import する．変更後は個別 target
  だけでなく必ず `lake build` を通す．
- 次の executable regression とその正負境界を維持する．
  - `TypePM/CertifiedInferenceRegression.lean`: primitive-pattern pattern の core order を
    `inferRaw` と公開 `infer` の両方で検査する正順 accept／逆順 reject の対．
  - `TypePM/RecursiveExamples.lean`: list／multiset direct-self 正例，coverage 不足 multiset
    負例，および recursive list matcher を slot に適用して `cons $x $rest` の両束縛を
    body で使う静的な公開 inference 旗艦例．この旗艦例について動的実行までは主張しない．
  - `TypePM/ProducerStrengtheningRegression.lean`: polymorphic producer を公開 `infer` が
    拒否し，同じ consumer に concrete producer を与えた control twin が成功する対．
  - `TypePM/DynamicSafetyRegression.lean`: `SF = []` の具体実行と全 mirror を構成し，
    `CoreSafety.evalPreservation` を消費する end-to-end 例．
  - `TypePM/DynamicCaptureRegression.lean`: 合法な value-pattern capture を
    `PPM.pval` から matcher reduction と `CoreSafety.stepPreservation` まで接続する例．
  - `TypePM/PatternCtorCapabilityRegression.lean`: pattern-constructor capability fallback の
    exact projection 前後，public inference の正負対，および実際の protected child に対する
    fail-closed な producer guard を固定する例．
  - `TypePM/DynamicDispatchRegression.lean`: 一つの concrete matcher 実行で
    `matcherPPFail`，`matcherDPFail`，二 child の `PPM.ctor`，成功 arm，terminal search を
    順に発火させる例．
  - `TypePM/PatternFunctionSafetyRegression.lean`: 非空 runtime signature で `papp` から
    pattern-function node `.mnode` を実行し，`CoreSafety` の六フィールドをすべて消費する例．
  - `TypePM/RecursiveExamples.lean` の `listSignature_wf`／`multisetSignature_wf`:
    非空 pattern-constructor 表に対する非空虚な `FrozenSigWF` instance（checker 経由）．
  - `TypePM/DamasMilner.lean`: DM 断片の宣言的埋め込みと多相 `let` 証人．
  - `TypePM/PrincipalityCounterexample.lean`: `(something, something)` の二重型付けと
    `no_principal_type`．
- Lean の規則と `tex/main.tex` の仕様を同期する．過去の進捗日誌，解決済み問題メモ，
  旧 calculus の説明は現行 README へ残さない．
