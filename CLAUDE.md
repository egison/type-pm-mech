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
  無証明で復活させない．`Elaboration.SynthHead`／`CoercionPlan`／`CheckHead` と
  `HasTy.factorHead` が証明するのは surface typing の **root factorization** であり，
  その再帰 premise は `HasTy` のままである．`CoreTyping.lean` の `CoreSynthHead`／`CoreCheck` は
  同じ分解を recursive reconstruction premise へ強化し，`coreCheck_iff_coreTyping` と公開 inference
  bridge を持つ．さらに `CoreTyping.factorNormalHead` は外側 plan に対する
  `Nonempty NormalPlan` witness の論理的存在を与えるが，
  これらを full core principality と呼ばない．
  `Elaboration.CoreTyping` は公開 inference が構成する derivation-structured な `Prop` 証明書
  `Reconstruction.ExprDeriv` の別名であり，明示的 coercion に沿う証明を erase して `HasTy` を得る
  soundness 境界である．proof irrelevance のため観測可能な core data とは呼ばない．
  MGU の最汎性は証明済みである：`Unification.lean` の proof-carrying kernel は `universal`
  field で「返された substitution を任意の unifier が factor する」ことを構成し，
  `mguCapFuel_universal`／`mguTyFuel_universal`（list・spec-level 版含む）が公開定理である．
  これは成功時の性質であり，可解な入力で fuel-bounded wrapper が成功する solvability
  completeness（および構造 fuel の十分性）は open のまま扱う．
  一意性／surface completeness も open として扱う．
  特に `TerminalPatternResolution` の leaf は `rawContext` と任意の `actualContext` を
  独立に持てるため，無条件の `HasTy → ExprDeriv` は主張しない．再帰的 completeness は
  `actualContext = rawContext.applySubst prevailing` を満たす coherent surface subset
  を対象にする．`CoherentSurface.lean` の indices-only
  `CoherentTerminalPatternResolution(s)`／`CoherentResolvedPatternTy` と reconstruction
  bridge は leaf-local な第一境界である．`ThreadedPatternResolution(s)` は raw
  `Context`／`PatternCtx` を全 child で共有し，raw `MonoCtx` を左から右へ threadする強い第二境界で，
  第一境界への forgetful map を持つ．`PatternResolutionDeriv(s)` 自体は同じ raw context／binding
  thread を保持する形へ強化済みであり，W reconstruction motive が直接生成する．その `pval` premise は
  `ExprDeriv` なので，inference-generated な `CoreTyping` は expression／pattern／arm／clause を通じて
  surface typing oracle へ戻らない recursive coherent core certificate である．一方，独立した surface
  `ThreadedPatternResolution(s)` の `pval` premise は plain `HasTy` のままである．expression／arm／clause
  まで含む mutual coherent judgment は `Reconstruction` certificate そのものであり，`CoherentTyping.lean`
  は `CoreTyping` と同じ前例に従って `Coherent.CoherentExpr := ExprDeriv` ほか 10 family を定義的
  abbreviation として公開する（鏡写しの独立 mirror は維持しない）．pattern 層は threaded，式 premise
  （pattern `pval`・arm body・clause next-matcher）は certificate 自身へ再帰する．product lift 構成子
  （`ExprDeriv.coerceProductMatcher`／`coerceSlotTuple`）は raw-source と lift substitution の
  provenance 添字を本体に持ち，W の reconstruction motive（`expectedCoercionSource_deriv`）は
  selector が実際に頭を検査した raw type と terminal substitution を faithful に注入する．恒等
  witness が常に取れるため判断は制限されず，plan replay（`CoercionPlan.toCoreTyping`）と match-free
  埋め込みは縮退 witness を供給する．surface への忘却 `CoherentExpr.toHasTy` と推論成功からの
  `infer_success_coherent` を持ち，pattern 層の standalone threaded 境界への忘却は既存の
  `PatternResolutionDeriv.toThreadedSurface`（`CoherentSurface.lean`）が与える．これを algorithmic
  completeness や principality と呼ばない．最上位目標の注釈不要性は `Coherent.AnnotationFree` として言明を固定する．現行推論器に
  対しては or-pattern 反例（両分岐が同名を束縛すると raw binding context の構文的等価要求で
  拒否される）による反証 `annotationFree_current_refuted`（`AcceptanceGapRegression.lean`）を
  機械化済みで，**完成後の推論器で成立させる到達目標**として扱う（定理でも公理でもなく，
  無証明で主張しない）．principality の存在側は「∀ typing ∃θ plan の factorization 存在定理」を
  先に立て，一意性は canonical boundary（substitution が coercible head を導入しない等）を
  定義してから条件付きで扱う．proof-indexed な derivation
  property や `ElaborableHasTy := ∃ CoreTyping` のような循環的定義で代用しない方針は維持する．
  `CanonicalCoercion.lean` の `Step`／`Spine`／`NormalPlan` は observable な `Type` 値の
  candidate coercion-plan syntax であり，identity と一般 `trans` を分離し，whole-product-first
  の二段経路を固定する．observable step は型の頭を変える3規則だけとし，product-of-slots は
  非空の場合に限り一致する aggregate slot へ `slotTuple` 一段で移す．surface の slot-to-slot
  check は MGU 後の端点等式により `refl` へ吸収する．全 spine の端点非等式と，同じ端点の plan が
  `refl` だけであることは証明済みである．`NormalPlan.comp` は identity 以外の唯一の合成
  `productMatcher; matcherToSlot` を二段 spine へ畳み，空 `slotTuple` は matcher-first の同じ二段経路へ
  送る．`CoercionPlan.normalizable` と逆向きの sound replay により，外側 coercion reachability と
  `Nonempty NormalPlan` の同値は証明済みである．`CoercionPlan : Prop` から `NormalPlan : Type` を
  計算で取り出せないため，これは observable data の生成ではない．同じ端点の `NormalPlan.kinds` 列は
  一意である．raw certificate を含む inhabitant 自体の一意性，
  推論器による plan data の直接生成は主張しない．
  `CapabilityOrigin.lean` は `rigid`／`renameOnly`／`structuralFlexible` ledger，capability component
  に対する admissible post，局所 structural／frozen residual を分ける `PhasedPost`，`Subst.seq`
  閉性，freeze bridge の代数的基礎である．target component は現段階では制約しない．
  `InferState.capabilityOrigins` は fresh／instance／finalized producer の origin を shadow metadata
  として記録するが，constraint acceptance と terminal audit は既存 `protectedCaps` のままなので
  挙動不変である．origin-aware solver への切替前に solve-cut ごとの ledger snapshot，MGU orientation，
  prevailing image leaf を対象とする export freeze event を設計する．constructor／primitive の local
  flexible instance が export 時に freeze される completeness はなお非主張とする．
  product-of-matchers の lift は tuple literal 専用へ戻さず，`let` 後の変数利用位置でも
  挿入できる unary `COERCE-PRODUCT-MATCHER` を維持する．sibling helper
  `expectedCoercionSource` は raw synthesized type が product-of-matchers と見える
  matcher／slot 利用位置でこの lift を，product-of-slots と見える slot 利用位置で
  `COERCE-SLOT-TUPLE` branch を決定的に選び，`alignExprResultAtExpected` が整合を行い，terminal
  reconstruction は明示的 node を構成する．空 product は matcher-product branch を優先する．通常の
  application は function を fresh domain／codomain へ先に整合し，argument を同じ helper で
  domain-directed に check する．prevailing substitution 後に
  初めて product head または matcher／slot component が現れる raw metavariable の completeness は
  product-of-matchers／product-of-slots の双方について非主張とする．
  この gap は normalized image から raw indices を逆算したり prevailing substitution の
  冪等性を仮定したりせず，solve cut で得た normalized product と後続 suffix を明示する
  cut-indexed coercion event として将来扱う．
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
    `inferRaw` と公開 `infer` の両方で検査する正順 accept／逆順 reject の対，および
    product-of-matchers の matcher／slot 利用位置 selector．
  - `TypePM/RecursiveExamples.lean`: list／multiset direct-self 正例，coverage 不足 multiset
    負例，および recursive list matcher を slot に適用して `cons $x $rest` の両束縛を
    body で使う静的な公開 inference 旗艦例．旗艦例の coherent instance
    （`listMatcherMatchAll_coherent`）も固定する．この旗艦例について動的実行までは主張しない．
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
  - `TypePM/ElaborationRegression.lean`: product の root synthesis と明示的
    `COERCE-PRODUCT-MATCHER` plan，および `let` 後の変数利用位置での unary lift．
  - `TypePM/CoherentSurface.lean`: pattern leaf の raw/actual context を結ぶ indices-only
    coherent judgment，surface forgetful map，reconstruction bridge．
  - `TypePM/CoherentTyping.lean`: coherent surface typing の定義的 abbreviation
    （`Coherent.CoherentExpr := ExprDeriv` ほか 10 family），`CoherentExpr.toHasTy`，
    `infer_success_coherent`，match-free 断片の全 coherence
    （`coherent_of_matchFree`）と DM 埋め込みの系（`dm_coherent`），
    および目標命題 `AnnotationFree`（現行推論器へは反証済みの到達目標）．
  - `TypePM/AcceptanceGapRegression.lean`: or-pattern 受理ギャップの対
    （宣言的 `orProgram_typed`・raw／公開拒否・単一分岐 control）と
    現行推論器への `AnnotationFree` 反証 `annotationFree_current_refuted`．
    or binder 修正が入ったら拒否側と反証を受理側の固定へ差し替える．
  - `TypePM/ApplicationCoercionRegression.lean`: domain-directed application の matcher product，
    matcher-to-slot，slot-tuple の三つの明示 surface 導出．対応する公開 inference 成功は
    `CertifiedInferenceRegression.lean` の kernel-evaluated `#guard` で固定し，結果型，terminal
    alignment 端点，componentwise coercion を行わない負例，empty-product matcher precedence も
    検査する．
- Lean の規則と `tex/main.tex` の仕様を同期する．過去の進捗日誌，解決済み問題メモ，
  旧 calculus の説明は現行 README へ残さない．
