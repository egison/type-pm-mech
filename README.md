# type-pm-mech — Egison core の型推論と安全性

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．型には matcher を生成する
`Matcher κ τ` と，matcher を必要とする消費位置を表す `MatcherSlot κ τ` がある．

source program の型付け可能性を定義する judgment は `DDTyping` だけである．実行時安全性の
証明では，推論中の supply や substitution を消去した内部 certificate `RuntimeTyping` を使う．
両者の役割は次の一方向に整理する．

```text
source program
     │
     ▼
 DDTyping                 唯一の source typing
     │ state erasure      実装済み：終端audit付きの全family相互消去
     ▼
 RuntimeTyping            内部の state-free certificate
     │ preservation / progress
     ▼
 runtime safety
```

`RuntimeTyping` は source acceptance を定義する第二の型システムではない．逆に
`RuntimeTyping e τ` から `DDTyping e τ` や推論成功を導くことも意図しない．

## DDTyping

[`TypePM/DemandTyping.lean`](TypePM/DemandTyping.lean) は，全 source form と pattern／arm／
clause 層について demand-directed な型付けを定義する．式層の中心は synthesis と checking
の二判断である．

```text
q; S; Ω; Γ ⊢ e ⇒ τraw      ⊣ q'; S'; Ω'    synthesis
q; S; Ω; Γ ⊢ e ⇐ τexpected ⊣ q'; S'; Ω'    checking
```

`q = (qκ, qτ)` は capability metavariable と target metavariable の次の番号を持つ fresh
supply，`S` はその cut までに得た paired substitution，`Ω` は capability variable の生成由来を
記録する origin ledger である．各規則は子を左から右へ調べ，出力 `q'; S'; Ω'` を次の子へ
渡す．公開 wrapper は canonical initial supply，恒等置換，空 ledger から始め，最後に
`S' τraw` を公開する．Leanでは rawな synthesis derivation，それに構造を一致させた intrinsic
Origin certificate，公開される終端 substitution での audit certificateを分けて
表現する．これらを合わせた判断が公開 source typingである．

`Ω(χ)` は次の三値を取る．未登録の変数は `rigid` として扱う．

- `rigid`: signatureや入力contextに由来し，solveはその変数を固定する．
- `renameOnly`: 既に外へ流れたproducerであり，非structuralな変数へのrenameだけを許す．
- `structuralFlexible`: constructor内部やconsumer demandの局所変数であり，export前だけ構造化を許す．

expression schemeとpattern-function schemeのcapability binderはinstance生成時から
`renameOnly` である．constructor／primitive instanceと単発fresh consumerは
`structuralFlexible` として生成し，使用後にexported payloadへ残る像のleafだけを
`renameOnly` へfreezeする．matcher literalは，最終capabilityに現れる全DD-owned explicit ledger
keyのstructural leafだけをfreezeする．これにはmatcher開始前に生成された `fixMatcher`
placeholderのowned leafも含まれる．ordinary equalityとone-way matcher-to-slot solveはいずれも，
そのcutの `Ω` に対してadmissibleなdeltaでなければならない．

```text
DDTyping Σ Γ e τ  iff
  ∃ τraw q' S' Ω',
    initialSupply Σ Γ; id; ∅; Γ ⊢ e ⇒ τraw ⊣ q'; S'; Ω' ∧
    TerminalAudit S' ∧
    τ = S' τraw
```

この定義は `infer` の成功や `RuntimeTyping` certificate の存在を前提にしない．

## Synthesis，checking，coercion

`DDCheck` は式を一度 synthesize し，その直後の cut で expected type と一度だけ align する．
ここで「一度だけ」とは導出全体で一回ではなく，各 checking cut につき一回という意味である．

非恒等 coercion は，cut で解決した expected type の head が `MatcherSlot` の場合だけ起こる．

| resolved source | resolved expected | alignment |
|---|---|---|
| `Matcher κp τp` | `MatcherSlot κc τc` | matcher-to-slot |
| product of matchers | `MatcherSlot κc τc` | product lift，matcher-to-slot |
| product of slots | `MatcherSlot κc τc` | slot-tuple lift |
| `MatcherSlot κp τp` | `MatcherSlot κc τc` | slot-to-slot equality |
| その他 | その他 | ordinary equality |

expected type が未解決変数なら ordinary equality だけを行う．coercion のために変数を slot
へ推測せず，ordinary equality の失敗後に別 branch を試す rollback も行わない．各 solve は
exact MGU または exact one-way solutionであり，constraint外のmetavariableを構造化しない．
さらにdeltaはcutの `Ω` に適合するため，`renameOnly` producerを `Any` やconstructor capabilityへ
後から強化するsolveは公開判断に入らない．

coercion の場所は `matchAll` や matcher literal に固定されない．たとえば
`use : MatcherSlot κ τ → ρ` へ `m : Matcher κ τ` を渡す場合，関数適用が domain を決め，
引数の checking cut で matcher producer と slot demand が対応付けられる．`matchAll` の
matcher 引数と matcher clause の next-matcher も同じ `DDCheck` を使う．

## RuntimeTyping と安全性

[`TypePM/Source.lean`](TypePM/Source.lean) の `RuntimeTyping` は，fresh supply，solver の実行順，
origin ledger を持たない state-free certificate である．closure と matcher value はこの
certificate を保持し，preservation はそれを `ValueTy` へ移す．
matcher-to-slot coercion も実行器の matching／MGU 成功証拠を保持せず，終端 capability 間の
`CapabilityDemand` だけを保持する．slot-to-slot solve は終端型の等しさへ消去される．実行用の
raw solver certificate は reconstruction がこの意味的証拠へ射影するまでの境界にだけ残る．

実行可能推論については次の経路が機械化済みである．

```text
infer Σ Γ e = some r
  → Reconstruction.ExprDeriv Σ (r.S Γ) e r.resolvedTarget
  → RuntimeTyping Σ (r.S Γ) e r.resolvedTarget
```

中心となる定理は `infer_success_reconstruct` と `infer_success_runtimeTyping` である．公開
`infer` は停止する `inferRaw` と有限の fail-closed terminal validator の合成であり，caller
が bridge certificate や `InferenceInputWF` を渡す必要はない．

`FrozenSigWF` の下では，`RuntimeTyping` を持つ式の評価，matching state の一段保存，局所
progress，到達可能 state の保存，成功 branch の substitution typing を証明済みである．
一般の program termination は主張しない．

## 残る接続

`DDTyping → RuntimeTyping` の state erasure は完成している．public `DDTyping` は
canonical initial supply，恒等置換，空 ledger から始まる raw derivation，構造が対応する
Origin certificate，終端 substitution での audit certificateを保持する．全 raw DD
family で出力 substitution の idempotence を保存することと，各子の出力から根の終端までの
chronological factorization を使い，全14 family の相互 erasure から closed-program の
`RuntimeTyping` を得る．`RuntimeTyping` 自体の存在を `DDTyping` の premise に置く循環はない．

現在残る主な受理接続は次の二つである．

1. `infer → DDTyping` の executable soundness
2. `DDTyping → infer` の受理完全性

一つ目については，successful executable traversalを同じcut列を持つDD derivationへ直接写す
証明を開始している．この接続は`RuntimeTyping`を経由せず，raw target，supply，prevailing
substitution，origin ledgerを保持する内部の帰納パッケージを用いる．

二つ目には，上記 freeze 統合に加え，現行 executable selector が product source の認識に
raw type を使う箇所を cut-resolved view と一致させる必要がある．最終目標は追加 premise の
ない次の定理である．

```text
DDTyping signature [] e τ →
  (infer signature [] e).isSome
```

`nestedCapProgram` と swapped 版は DD で型付かず，推論器も拒否する意図された負例である．
一方，or-pattern，delegating matcher，let-polymorphic な matcher producer は維持すべき正例で
あり，public Origin certificate を伴う回帰で固定済みである．

## Roadmap

roadmap は次の依存関係に従う．`RuntimeTyping` を source typing に戻したり，その derivation の
存在を `DDTyping` の premise に加えたりせず，DD derivation 自身が安全性と実行可能推論への
接続に必要な情報を持つ形を完成させる．

```text
現在の DDTyping／infer／runtime safety
              │
              ▼
[x] 1. freeze provenance と public 回帰
              │
        ┌─────┴──────────┐
        ▼                ▼
[x] 2. DD state erasure   [~] 3. infer success → DDTyping
        │                │
        ▼                ▼
[ ] 4. DD の公開安全性    [ ] 5. DDTyping → infer success
                         │
                         ▼
                    [ ] 6. 受理同値と注釈不要性
```

記号は `[x]` が完了，`[~]` が一部完了，`[ ]` が未完了を表す．

### 進捗サマリ

全7 milestoneのうち，完了3，一部完了1，未着手3である．

| milestone | 状態 | 完了した中心部分 | 残る中心部分 |
|---|---|---|---|
| 0. 基盤 | 完了 | DD判断，exact solve，runtime certificate，既存動的安全性 | なし |
| 1. freeze provenance | 完了 | Origin ledger，public正例／負例回帰 | なし |
| 2. DD state erasure | 完了 | canonical `Scheme`，全14 familyのfactorizationとidempotence，terminal audit，固定終端への相互erasure，closed-program公開定理 | なし |
| 3. infer success → DDTyping | 一部完了 | exact solver bridge，checking alignment全分岐，通常expression constructorの大半 | `fixMatcher`，`letE`，`matcher`，`matchAll`，pattern／arm／clause相互再構成，public中心定理 |
| 4. DDの公開安全性 | 未着手 | closed-program erasureと利用するpreservation／progressは既存 | 動的定理を公開`DDTyping`の前提で合成 |
| 5. DDTyping → infer success | 未着手 | 完全性に必要なexact solver基盤は既存 | traversal完全性，terminal validator完全性 |
| 6. 受理同値 | 未着手 | なし | milestone 3と5の合成 |

現在のcritical pathは，milestone 3のmatcher／pattern／clause相互再構成を閉じ，
`infer success → DDTyping`を完成することである．milestone 4は完了した closed-program
erasureと既存の動的安全性を合成する独立作業になった．

milestone 5は1と2に依存しないが，現在はsource soundnessと公開安全性の完成を
優先するため未着手とする．

なお，現時点でも `infer` 成功から `RuntimeTyping` を再構成する既存定理はある．未完了なのは，
そのruntime certificateを経由せず，successful traceから唯一のsource typingである `DDTyping` を
直接再構成し，さらに `DDTyping` 自体から公開動的安全性を導く新しい経路である．

### [x] 0. 現在の基盤

次は完成済みの出発点であり，後続 milestone で維持する不変量である．

- 全 expression／pattern／arm／clause form に `DDSynth`／`DDCheck` family がある．
- checking は synthesis 後の一 cut で一度だけ alignment を行う．
- 非恒等 coercion は slot-headed expected type に限られる．
- exact MGU，state replay，supply extension，boundedness が証明されている．
- `infer` の成功から reconstruction と `RuntimeTyping` を構成できる．
- `RuntimeTyping`，`ValueTy`，matching-state judgment 上の動的安全性が証明されている．

### [x] 1. Capability freeze provenance の public 回帰を完成する

core 実装は完了している．全 DD family の raw derivation に構造を一致させた intrinsic Origin
certificateがあり，`q; S; Ω` を状態として追跡する．scheme／dual instance は binder imageを
`renameOnly`，constructor instanceとfresh consumerは `structuralFlexible` とし，exportとmatcher
finalizationは外へ残るstructural leafだけを選択的にfreezeする．ordinary equalityとone-way solveは
cutのledgerに対してadmissibleなdeltaだけを受理する．`let` certificateは終端 substitution 後にも
同じgeneralization schemeが得られる安定性を要求する．public wrapperも空ledgerから始める．

originを追跡しない局所導出で現れた反例は，public `DDTyping` 全体の導出不能性まで閉じた
negative regressionとして固定されている．

完了条件：

- [x] ledger の extension，freeze，substitution replay に関する基本補題が全 DD family で成り立つ
  （基本的な supply-scoped ledger 補題と transition 補題は実装済み）．
- [x] `capFreezeProgram` と `letCapFreezeProgram` が public `DDTyping` では導出不能であることを証明する
  （問題となる局所導出，ledger-aware solveによる拒否，program全体のnegative regressionを実装済み）．
- [x] or-pattern，delegating matcher，let-polymorphic producer など既存の正例について public Origin
  certificate を構成する（実装済み）．
- [x] `nestedCapProgram`，matcher-expected product application など既存の負例は導出不能なままである．
- [x] public `DDTyping` は canonical initial ledger から開始し，外部の freeze premise を要求しない．

### [x] 2. DD state erasure を証明する

ledger-aware な DD derivation から supply，prevailing substitution，origin ledger を消去し，
`RuntimeTyping` certificate を構成する相互証明は完了している．expression だけでなく，
expression list，checking，user／primitive／data pattern，arm，clause を含む全 family を
同じ根の終端 substitution へ射影する．

完了した構成は次のとおりである．

- [x] 全14 DD familyの無前提 `StateFactorization` を構成する．
- [x] checking alignment全5分岐を終端 `RuntimeAlignment` へ射影する．
- [x] solver metavariableとscheme bound variableを別datatypeにしたcanonical `Scheme`へ移行し，
  binder名，mask，`NoCapture` 条件を source scheme から除去する．
- [x] finiteなbound indexのopening，fresh allocation，generalization，substitution合成，
  variable value-flow transportを構成する．
- [x] exact solveがidempotentな入力 substitutionからidempotentな出力を作ることを，
  alignment familyとraw DD全14 familyで証明する．
- [x] derivationと同じ形のterminal-audit treeを構成し，`let` generalization，
  matcher finalization，pattern-constructor compatibilityを根の終端 substitutionで固定する．
- [x] chronological factorizationとidempotenceを各子へ渡す固定終端の相互erasureを構成する．
- [x] closed signatureについて
  `DDTyping.runtimeTyping`，すなわち
  `DDTyping signature [] e τ → RuntimeTyping signature [] e τ` を公開定理として閉じる．

<details>
<summary>state erasureの設計</summary>

schemeのbound variableは有限なbound index，推論器のmetavariableは `CapVar`／`TyVar` であり，
構文レベルで異なる．ambient substitutionはbound occurrenceを生成できないため，旧来の
binder-name衝突，mask，`NoCapture` 保存条件は不要になった．generalizationは選んだmetavariableを
直ちにcanonical schemeへcloseし，instance生成はcaller-suppliedなfinite openingで行う．

消去証明は「任意の将来 suffix に対して各nodeが安定する」とは仮定しない．その主張は
`let` のgeneralized setが後続solveで変わり得るため強すぎる．代わりに公開 `DDTyping` は，
raw derivationとOrigin certificateに加え，同じ木構造を持つterminal auditを公開終端
substitutionに対して保持する．auditは局所suffixで一般には保存されない三種類の事実を記録する：

- `let` が終端contextと終端value typeから同じschemeをgeneralizeすること．
- matcherの終端capabilityに対してshape，clause capability，exhaustiveness，coverageが成立すること．
- pattern constructorの引数capabilityと結果capabilityが終端でcompatibleであること．

各raw DD familyはexact solveのidempotenceを保存する．また，各子の出力状態から根の終端状態への
`StateFactorization` がchronological substitutionを与える．相互erasureはこのfactorizationと
idempotenceを再帰的に渡し，variable opening，checking alignment，`let`，matcher／clause，
pattern constructorを含む各constructorを終端の `RuntimeTyping` familyへ射影する．terminal
auditは `RuntimeTyping` の存在を保持するoracleではなく，solverを含まない有限な代数的・
検査可能事実だけを保持する．

</details>

一般の内部定理は入力contextへ根の終端 substitutionを適用した `RuntimeTyping` を構成する．
canonical initial stateと空contextに特殊化すると，公開した型をそのまま持つclosed-program
corollaryが得られる．これによりMilestone 2は，型付けderivationをpremiseに持つoracleや
blanketなcapability transportを追加せず完了した．

### [~] 3. 実行可能推論の DD soundness を証明する

現在の `infer_success_runtimeTyping` より前に，successful trace そのものを ledger-aware DD
derivation へ再構成する．`inferRaw` の fresh allocation 順，solve cut，generalization，matcher
finalization を対応する DD constructor へ写し，terminal validator が確認した freeze event を
DD ledger へ反映する．

#### 現在の進捗

帰納不変量は `Inference.DDSynthRun`，`DDSynthsRun`，`DDCheckRun`，`DDChecksRun`，
`DDPatternRun`，`DDPatternsRun` である．
これらは raw target と実行状態の supply／prevailing substitution／origin ledger を，DD derivation
の入出力 index に正確に一致させる．

完了済み：

- [x] target／capability／paired solver を，DD が要求する exact MGU 契約へ接続した．
- [x] matcher-to-slot，product-matcher lift，slot-to-slot，slot-tuple lift，ordinary equality を含む
  checking alignment の全分岐を `DDAlignRun`／`DDCheckRun` へ再構成した．
- [x] variable，literal，`something`，lambda，tuple，application，constructor，primitive，
  non-matcher `fix` を `DDSynth`／`DDSynthOrigin` へ再構成した．
- [x] synthesis list と checking list の nil／cons traversal を再構成した．
- [x] user-patternのexact-state runを導入し，pattern listのnil／consと，`pvar`，wildcard，
  value pattern，parameter embed，tuple patternを再構成した．
- [x] constructor instance，capability export freeze，direct-self gate，2-target recursive placeholder を，
  実行 state と DD ledger transition の exact index で一致させた．
- [x] batch capability freshening の ledger 順を実行時の head-insertion 順へ canonicalize し，
  2-variable exact-order 回帰と旧表現との `originOf` 同値を証明した．
- [x] public `infer` 成功から `inferRaw` 成功を取り出す入口と，initial run から `DDTyping` への射影を
  用意した．

未完了：

- [ ] `fixMatcher`：stateful／supply-indexed skeleton freshening の3つの相互 family を，
  olean 生成可能な明示再帰証明として構成する．
- [ ] `matcher`／pattern／arm／clause：pattern constructor，and／or，pattern-function applicationと，
  primitive／data pattern，arm，clauseの各 successful traversalを対応するDD Origin familyへ
  相互再構成する．
- [ ] `matchAll`：target，pattern，matcher checking，body の相互 certificate を thread する．
- [ ] `letE`：Origin certificate が要求する terminal generalization stability を実行成功から回収する．
- [ ] 上記を fuel に関する相互帰納定理へ統合し，public `infer success → DDTyping` を閉じる．

`fixMatcher` の一括証明は Lean の対話的検査には通ったが，olean 生成が150秒以上収束しなかったため
採用していない．証明対象が偽なのではなく，3つの相互 family を明示的な再帰補題へ分割する必要がある．
`letE` の generalization stability は，これとは独立した証明課題である．

<details>
<summary>実装経緯と solver certificate の詳細</summary>

最初の帰納不変量として`Inference.DDSynthRun`を定義済みである．これはsuccessful traversalの
raw targetと，実行状態のsupply／prevailing substitution／origin ledgerに正確に一致する
`DDSynth`／`DDSynthOrigin`だけを保持し，canonical initial stateから`DDTyping`へ射影できる．
variable，literal，`something`，lambda，tupleとexpression-listのnil／cons traversalについて
この再構成を実装済みである．またpublic `infer`の成功から対応する`inferRaw`成功を取り出す補題を公開し，
最終corollaryがterminal runtime certificateへ迂回しない入口を用意した．
checking側にもexact-stateな`DDAlignRun`／`DDCheckRun`とsynthesisからの合成補題を用意した．
generic alignmentを実行solverから再構成するには，solverの既存soundness／support／universalityを
DD規則が要求するrange／idempotenceを含む`ExactTargetMGU`／`ExactPairedMGU`まで強めるbridgeが
必要である．ledger-relativeな成功結果についても，成功したsubstitution自体のglobal MGU性を
証明し，DDのexactness契約は弱めない方針である．通常target MGUについてはkernel内部の
`TyRange` certificateを公開し，image target variableが入力constraintのfree-variable範囲を
越えない`TySubst.RangeWithin`まで証明済みである．さらに`TyResult`／`TyListResult`自身が
supportの入力free-variable内性とimage rangeを保持するよう整理し，入力に対する
`TySubst.SupportWithin`も公開済みである．さらにsolverが変更した各support変数を最終imageから
消去する`supportElim`を結果certificateへ加え，そこから`TySubst.Idempotent`を導いた．target
substitutionのimageに現れるcapability variableについても入力constraint内のrangeをcertificateへ
統合し，既存のsoundness／global universalityとこれらの性質をまとめる
`mguTy_exactTargetMGU`を構成した．したがって通常target solverの`ExactTargetMGU` bridgeは完了した．
さらにproducer-to-slot solverの成功からorigin admissibilityを含む`OriginSafeOneWayDelta`を回収し，
matcher-to-slotとproduct-of-matchers liftのalignment，およびそれらを使うchecking分岐を
exact-stateなDD derivationへ再構成した．origin-oriented capability kernelにも入力内support，
range，support elimination，global universalityを保持させ，ledger admissibilityとは独立に
`ExactCapMGU`を構成できるbridgeを完成した．paired solverについても，全unifierがsolver結果を
経由するglobal universalityに加え，capability／target両sortの入力内support，capability image
range，target imageのtarget-variable／capability-variable rangeを全構造分岐で証明済みである．
これらのrangeから前段substitutionによる後段imageのfixednessを導き，paired idempotenceも
全構造分岐で証明した．soundness，global universality，support，range，idempotenceを同じkernel
resultから束ねる`ExactPairedMGU`／`OriginSafeExactPairedMGU` bridgeも完成し，public paired solveと
raw target-equality stepの双方へ公開した．ordinary equalityのうちannotated matcher／slot pairでない
1-solve分岐に加え，matcher／matcherとslot／slotのcapability-then-target 2-solve分岐も
exact-stateな`DDAlignTypesWithLedger`へ再構成済みであり，ordinary type alignmentの3分類を閉じた．
event-onlyな`alignTypes` wrapperと`alignAtSlot`のordinary fallbackもexact-state certificateへ
持ち上げ済みであり，slot-to-slotのcapability-then-target 2-solve分岐も再構成した．次は
raw slot-productのresolved dual transportと空productのproduct-matcher precedenceを含む
slot-tuple liftも再構成済みである．branch別certificateを実行selectorと同じprecedenceで統合し，
raw／resolved product認識がずれる成功不能caseも明示的に排除した．したがって任意のsuccessful
expected-type alignmentとchecking traversalをexact-stateな`DDAlignRun`／`DDCheckRun`へ再構成できる．
このgeneric checking補題を使い，function synthesis，2 target fresh，function alignment，argument checkingを
threadするapplication traversalも`DDSynth`／`DDSynthOrigin`へ再構成した．次はexpression-list checkingの
exact-state `DDChecksRun`とnil／cons traversalも再構成済みである．次はscheme instantiationと
capability export freezeをDD ledger transitionへ接続し，constructor／primitive applicationも
まとめて再構成した．direct-self gate，2 target placeholder，body synthesis，result alignmentをthreadする
non-matcher recursive functionのfix branchも再構成済みである．次はmatcher bodyのfix placeholderと，
matcher／pattern／clauseの相互familyを必要とするbranchへ進む．この接続で見つかったbatch capability
fresheningのledger list順は，`markCapRange`を実行時のhead-insertion順へcanonicalizeして修正し，
2-variable allocationのexact-order回帰と従来表現との`originOf`同値を固定した．`fixMatcher`の
stateful／supply-indexed skeleton対応は，3 mutual familyを明示再帰で証明する必要がある．大規模な
`grind`による一括証明はLean検査には通るもののolean生成が収束しないため採用しない．また`letE`の
Origin certificateが要求するterminal generalization stabilityは，現状の実行成功だけから回収する
bridgeがまだない．したがって以後はmatcher／pattern／clause相互再構成とgeneralization stabilityを
独立milestoneとして進める．

</details>

#### 完了条件

中心定理：

```text
infer signature context e = some result →
  DDTyping signature context e result.resolvedTarget
```

これにより，公開推論器の成功は唯一の source typing に対して sound である，という通常の API を
得る．`RuntimeTyping` はこの定理と milestone 2 の合成から内部的に回収できる．

### [ ] 4. DDTyping から公開動的安全性を導く

milestone 2 の state erasure と既存の preservation／progress を合成し，公開定理の premise から
`RuntimeTyping` を隠す．`FrozenSigWF` は従来どおり実行可能 checker から確立する．

目標とする公開形：

```text
DDTyping signature [] e τ →
FrozenSigWF signature →
runtime safety package for e at τ
```

expression evaluation と matching machine の既存定理をこの入口から利用できること，および
`Soundness` module の公開結果が source typing と runtime safety を同時に返すことを完了条件とする．

### [ ] 5. DDTyping に対する推論器の受理完全性を証明する

DD derivation を左から右に読み，対応する `inferRaw` traversal が成功することを証明する．先に
executable selector の product source 認識を raw view から cut-resolved view へ揃え，DD の
`demandClass` と実装の branch 選択を一致させる．その後，DD の exact solve witness を実行
solver の result へ対応させ，生成された trace が terminal validator を通ることまで示す．

中心定理：

```text
DDTyping signature [] e τ →
  (infer signature [] e).isSome
```

途中結果として raw traversal の完全性と terminal validator の完全性を分けて定理化してよいが，
最終定理には `RawSourceVisible`，`FreezeCompatible`，caller-supplied bridge などの追加 premise を
残さない．

### [ ] 6. 受理同値と注釈不要性を公開する

milestone 3 と 5 を合成し，closed program について source typability と公開推論器の成功を
対応付ける．

```text
(∃ τ, DDTyping signature [] e τ) ↔
  (infer signature [] e).isSome
```

この同値を本 mechanization の annotation-freeness 定理とする．あわせて，`inferType` が返す型と
DD derivation の型の関係を定式化し，DD fragment に対する decidability と，必要なら条件付き
principality を独立に議論する．`RuntimeTyping` 全体の principality 反例を DDTyping の結果として
流用しない．

## 機械化済みの主な性質

- `DDCheck` の非恒等 branch は slot-headed expected type に限られる．
- matcher-headed expected type では ordinary equality しか起こらない．
- DD family の supply は単調に進み，substitution は chronological delta replay に分解できる．
- exact solveと全14 raw DD familyは substitution のidempotenceを保存する．
- DD が公開する型，pattern dual，bindings，hole ledger は終端 supply で有界である．
- exact MGU は constraint 外の metavariable を推測しない．
- matcher literal は shape，catch-all order，data-arm exhaustiveness，binder 線形性，coverage
  evidence をすべて要求する．
- closed signature上で `DDTyping signature [] e τ` から `RuntimeTyping signature [] e τ` を導く．
- `infer` の成功から reconstruction certificate と `RuntimeTyping` を再構成できる．
- `FrozenSigWF` の下で concrete evaluation と matching machine の安全性が成り立つ．
- `sorry`，`admit`，project-defined `axiom` はない．

## モジュール案内

| 層 | 主な module | 役割 |
|---|---|---|
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| DD typing | `DemandTyping`, `DemandTypingOrigin`, `DemandTypingLedgerMetatheory`, `DemandTypingOriginMetatheory`, `DemandTypingInferenceSoundness`, `DemandTypingErasure`, `DemandTypingTerminalAuditBuilder`, `DemandTypingRegression`, `DemandTypingTerminalAuditErasureRegression` | raw規則，intrinsic Origin certificate，ledgerメタ理論，推論からDDへの再構成，state-erasure facade，terminal audit構築，public source typingと回帰 |
| runtime certificate | `Source`, `Reconstruction`, `CoherentSurface`, `CoherentTyping` | state-free certificate と再構成 |
| inference | `Inference*`, `BridgeChecks`, `CertifiedInference` | raw W，origin ledger，validator，成功時の再構成 |
| dynamics | `Semantics`, `Dynamic`, `Preservation`, `Safety` | evaluation，matching machine，安全性 |
| fragments | `DamasMilner`, `DMTerminalAcceptance` | pattern-free DM 断片 |

詳細な定義・定理・回帰の対応は [`docs/details.md`](docs/details.md)，論文形式の規則は
[`tex/main.tex`](tex/main.tex) にある．Lean の public import surface は
[`TypePM.lean`](TypePM.lean) である．

## 検証

```sh
lake build
cd tex
make
```

TeX の出力は `tex/type-pm-mech.pdf` である．
