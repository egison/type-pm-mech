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
     │ state erasure      一部実装：全14 familyのstate factorization
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
`S' τraw` を公開する．Leanでは rawな synthesis derivationと，それに構造を一致させた intrinsic
Origin certificateを分けて表現するが，両者を合わせた上の判断が公開 source typingである．

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

## 未完成の接続

現在の主な未完成部分は三つである．

1. `DDTyping → RuntimeTyping` の state erasure
2. `infer → DDTyping` の executable soundness
3. `DDTyping → infer` の受理完全性

一つ目に必要な capability-origin ledger は DD family 全体へ統合済みである．raw derivation と
同じ形の intrinsic Origin certificate が，fresh allocation，scheme／dual instance，constructor
instance，producer export，matcher finalization，solve cut を追跡する．public `DDTyping` は
canonical initial supply，恒等置換，空 ledger から始まる raw derivationとその certificateの
組だけを受理する．

残っているのは，この Origin derivation を全14 familyのconstructorに沿って
`RuntimeTyping` へ射影する相互state-erasure定理である．supply-scopedな残余substitutionの
admissibility，全14 familyの無前提state factorization，canonical scheme instanceの局所transport，
variable／literal／`something`／lambda／tupleの初期erasure補題までは構成済みである．
`capFreezeProgram` と `letCapFreezeProgram` については，originを追跡しない局所solveが
capabilityを不正に強化できる一方，public `DDTyping` ではプログラム全体が導出不能であることを
end-to-end回帰で固定している．既存正例のOrigin certificateもpublic wrapperまで構成済みで
ある．`RuntimeTyping` の存在を `DDTyping` の premise に埋め込む循環的な定義は採らない．

二つ目については，successful executable traversalを同じcut列を持つDD derivationへ直接写す
証明を開始している．この接続は`RuntimeTyping`を経由せず，raw target，supply，prevailing
substitution，origin ledgerを保持する内部の帰納パッケージを用いる．

三つ目には，上記 freeze 統合に加え，現行 executable selector が product source の認識に
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
[~] 2. DD state erasure   [~] 3. infer success → DDTyping
        │                │
        ▼                ▼
[ ] 4. DD の公開安全性    [ ] 5. DDTyping → infer success
                         │
                         ▼
                    [ ] 6. 受理同値と注釈不要性
```

記号は `[x]` が完了，`[~]` が一部完了，`[ ]` が未完了を表す．

### 進捗サマリ

全7 milestoneのうち，完了2，一部完了2，未着手3である．

| milestone | 状態 | 完了した中心部分 | 残る中心部分 |
|---|---|---|---|
| 0. 基盤 | 完了 | DD判断，exact solve，runtime certificate，既存動的安全性 | なし |
| 1. freeze provenance | 完了 | Origin ledger，public正例／負例回帰 | なし |
| 2. DD state erasure | 一部完了 | 全14 familyのfactorization，多くのconstructor-wise erasure，capture-free poly syntax基盤 | expression `Scheme`のpoly payload移行，variable／`let` transport，matcher／clause終端再構成，pattern-constructorの終端compatibility |
| 3. infer success → DDTyping | 一部完了 | exact solver bridge，checking alignment全分岐，通常expression constructorの大半 | `fixMatcher`，`letE`，`matcher`，`matchAll`，pattern／arm／clause相互再構成，public中心定理 |
| 4. DDの公開安全性 | 未着手 | 利用するpreservation／progressは既存 | milestone 2のclosed-program erasure後に公開定理を合成 |
| 5. DDTyping → infer success | 未着手 | 完全性に必要なexact solver基盤は既存 | traversal完全性，terminal validator完全性 |
| 6. 受理同値 | 未着手 | なし | milestone 3と5の合成 |

現在のcritical pathは次の二本である．

1. milestone 3のmatcher／pattern／clause相互再構成を閉じ，`infer success → DDTyping`を完成する．
2. milestone 2のcapture-free `Scheme`移行とmatcher終端再構成を閉じ，その後milestone 4を合成する．

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

### [~] 2. DD state erasure を証明する

ledger-aware な DD derivation から，supply，prevailing substitution，origin ledger を消去して
`RuntimeTyping` certificate を構成する．expression だけを個別に処理せず，expression list，
user pattern，primitive pattern，data pattern，arm，clause の相互 family 全体について射影を
証明する．`let` では一般化 scheme の binder-local value-flow instance，matcher literalでは
共有 target と terminal hole capability の一致を回収する．

進捗：

- [x] 全14 DD familyの無前提`StateFactorization`を構成する．
- [x] checking alignment全5分岐を終端`RuntimeAlignment`へ射影する．
- [x] expressionの主要構造規則と，data／primitive patternの構造的erasureを構成する．
- [x] scheme substitutionのno-capture条件とbinder-local instance compositionを定式化する．
- [x] solver metavariableとscheme bound variableを型レベルで分離する，scheme専用の
  `PolyCap`／`PolyTy`，canonical `PolyScheme`，close／open境界と旧collisionの
  capture不能回帰を構成する．
- [ ] expression `Scheme`を`PolyTy` payloadへ移行し，mask／`NoCapture`依存を除去する．
- [ ] migration後の無条件なpoly-substitution合成を使い，variable／`let`のtransportを閉じる．
- [ ] matcher／clauseを終端cutで相互に再構成する．
- [ ] pattern constructorの`CapCompatible`を早期freezeせず，終端consumerの証拠から回収する．
- [ ] `DDTyping signature [] e τ → RuntimeTyping signature [] e τ`を公開定理として閉じる．

<details>
<summary>state erasureの実装状況，反例，設計判断の詳細</summary>

現在は，入力cutより前のorigin policyだけを制約するsupply-scopedな
`AdmissiblePostBetween` と，終端substitutionを安全なpostへ分解する`StateFactorization`を定義し，
合成，boundedness，ledger refinement，alignmentの各分岐について基本補題を証明済みである．
式のsynthesis／checkingとそれらのlistに加え，user pattern，primitive pattern，data pattern，arm，
clauseを含む全14 familyのfactorizationを，`SchemesClosed`と入力boundednessだけから得る無前提の
相互定理として構成済みである．canonical scheme／dual-scheme instanceのbinder imageをrename-only
ledgerから局所的にtransportする補題と，variable／literal／`something`／lambda／tupleから
`RuntimeTyping`を得る初期erasure補題もある．さらに，全expression／pattern／arm／clause familyの
終端state-free命題とconstructor-wise合成補題を分離し，checking alignmentの全5分岐を終端の
意味的な`RuntimeAlignment`へ射影した．後続cutを量化する`RuntimeErasureUnder`はliteral，
`something`，lambda，tuple，fix，application，`fixMatcher`，constructor／primitive，synthesis／checking
listの構造規則に加え，expression leafを持たないdata／primitive patternの4 familyについて無前提の
相互closureまで閉じている．user patternもvariable／wildcard／embed／tuple／listまで，matcher armも
pattern・body・tailの再帰合成まで拡張済みであり，value patternもchild expressionのlater-cut
erasureから構造的に合成できる．and／or，pattern-function application，pattern constructorにも
child invariantからの構造補題があり，`matchAll`もtarget，pattern，matcher，bodyの4 child invariantと
各factorizationだけから最終cutへ合成できる．pattern constructorだけは，後続cutでの
`CapCompatible`安定性が明示的な残余条件である．この整理に合わせ，
`RuntimeTyping`と`ValueTy`から実装solverの
raw certificateとglobal `VariablePost`を除き，matcher-to-slotは終端`CapabilityDemand`，
slot-to-slotは終端型等式だけへ消去した．variable leafでは，fresh instanceのcapability binderが
後続cutでもvariableであることはledgerから回収できる一方，`Scheme.applySubst`のbinder maskingを
またぐcontext schemeの合成は無条件には成り立たないことを分離した．さらに，contextとscheme，
前後のsubstitutionがboundedかつsolvedで，actual marked ledgerに対するpostがadmissibleでも，
substitution rangeがscheme binderへ入ると合成則が壊れる具体的なLean反例を固定した．したがって，
残るvariable／`let`にはno-captureなbinder provenance（または真のalpha-renaming）が必要である．
必要なrange hygieneをcap→cap，type→cap，type→typeの3経路に分けた`Scheme.NoCapture`と，そこから
scheme substitutionの逐次合成を得る定理を実装済みである．一方，lookup時点がno-captureでも，
後続のadmissible suffixが新たにbinder captureを起こしてvalue-flow instanceを失わせる第二反例も
固定している．したがって，過去のleaf-local premiseでは足りず，context中の各scheme／free variable
ごとのavoidanceを後続solve全体で保存する必要がある．
この状態不変量を追加する代わりに，scheme payloadをsolverの`Cap`／`Ty`から分離する移行を開始した．
`PolyCap n`／`PolyTy n m`ではbound occurrenceを`Fin`，free occurrenceを既存metavariableで表し，
ambient substitutionのrangeからbound occurrenceを構築できない．`Fin`はcanonicalなde Bruijn index
なので全payloadがalpha-normal formであり，substitutionごとのfresh nominal renameと
alpha-equivalenceを導入せずに構造的等式を維持できる．現時点では基盤とcollision回帰までで，既存
`Scheme`のpayload移行後にこの段落の`NoCapture`残課題を削除する．
この境界は`Context.NoCapture`，context substitutionの逐次合成，binder-local instance composition，
canonical value-flow transportとして補題化済みであり，variable leafの従来のscheme equality／
`InstCompositionAt`／binder equation premiseは，lookup前後の2つの`NoCapture`条件へ簡約できている．
clause側ではfinal matcher capabilityとshape evidenceをmatcher finalizationから渡す必要があり，
matcher本体ではscoped rename-only postをshape／clause transportが使うtotal renamingへ持ち上げる補題が
必要である．supply cut未満でvariable-onlyなpostをcut以上identityのtotal postへ拡張し，boundedな
capability／type／scheme／context上で元のpostと一致する補題は実装済みである．ただしproducerに
現れないstructural leafまでfreezeされるわけではないため，matcher全体へ適用するには有限な関連leaf
だけを追跡するか，clauseを最終cutで直接再構成する必要がある．これらを解決して残るuser pattern，
clause，matcherを相互に閉じることが次のcutである．pattern constructorのchild／result
capabilityを局所cutで一律にexport freezeする案は採れない．`DynamicDispatchRegression`の正例では
`Pair κ`として合成されたpattern resultが，外側のmatcher-to-slot demandで`κ ↦ Any`と正当に
具体化されるためである．実行可能推論のterminal validatorは既にraw operandへ最終substitutionを
再適用して`CapCompatible`を再検査し，`Reconstruction`もその証拠を使用している．したがってDD
state erasureでも，pattern constructor単体を早期freezeするのではなく，最終consumer cutの
compatibility evidenceを直接渡す，またはpattern consumer全体の完了まで検査を遅延する必要がある．

</details>

一般の context では，raw derivationに対応するOrigin certificateを仮定し，終端 substitutionを
contextに適用した `RuntimeTyping` を構成する．そのclosed-program corollaryが中心定理である：

```text
q; S; Ω; context ⊢ e ⇒ raw ⊣ q'; S'; Ω' →
  RuntimeTyping signature (context.applySubst S') e (S'.apply raw)

DDTyping signature [] e τ →
  RuntimeTyping signature [] e τ
```

完了条件は，型付け derivation を premise に持つ oracle や任意の capability transport を
追加せず，freeze 回帰を含む全例についてこの定理を適用できることである．

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
- DD が公開する型，pattern dual，bindings，hole ledger は終端 supply で有界である．
- exact MGU は constraint 外の metavariable を推測しない．
- matcher literal は shape，catch-all order，data-arm exhaustiveness，binder 線形性，coverage
  evidence をすべて要求する．
- `infer` の成功から reconstruction certificate と `RuntimeTyping` を再構成できる．
- `FrozenSigWF` の下で concrete evaluation と matching machine の安全性が成り立つ．
- `sorry`，`admit`，project-defined `axiom` はない．

## モジュール案内

| 層 | 主な module | 役割 |
|---|---|---|
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| DD typing | `DemandTyping`, `DemandTypingOrigin`, `DemandTypingLedgerMetatheory`, `DemandTypingOriginMetatheory`, `DemandTypingInferenceSoundness`, `DemandTypingErasure`, `DemandTypingRegression` | raw規則，intrinsic Origin certificate，ledgerメタ理論，推論からDDへの再構成，state-erasure facade，public source typingと回帰 |
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
