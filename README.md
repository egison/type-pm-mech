# type-pm-mech — Egison core の機械化

## 最上位目標

本リポジトリの完成目標は，次を正確に主張できる機械化を与えることである．

> The soundness of executable type inference for the Egison core is mechanized in Lean 4.

具体的には，executable `infer` が成功したならば，その結果に対応する宣言的な
`HasTy` 導出が必ず得られることを証明する．
公開 `infer` は raw な停止 W 走査 `inferRaw` と有限な terminal validator を合成し，
`infer_success_sound` は成功等式だけから `HasTy` を返す．これは意図する
`InferenceInputWF` 入力に限定した主張より強い．
`WBridgeWF` は validator が内部で構成する証明書であり，呼び出し側の仮定ではない．
plain surface principality は機械化済み反例により偽である．現在はその境界を保ったまま，
推論器が principal core typing を生成し，surface typing を core type の置換と明示的
coercion に分解する定理を次の目標としている．現時点では core evidence を伴う
soundness と surface coercion の root factorization までを証明しており，core
principality／completeness と Egison コンパイラ全体の検証はまだ主張しない．

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．形式仕様は
[`tex/main.tex`](tex/main.tex)，Lean の public import surface は
[`TypePM.lean`](TypePM.lean) である．

現行 calculus は matcher producer と利用位置の要求を分ける．

```text
Matcher     κ τ   -- 値が生成時から持つ intrinsic capability
MatcherSlot κ τ   -- pattern site が要求する consumer capability
```

capability と target type は別 sort，別変数，別 substitution，別 quantifier を持つ．
producer から slot への接続は対称単一化ではなく producer-stable な one-way check で
行う．動的定理は concrete source/runtime judgments だけを使う．

## 証明している範囲

### Source typing

- lambda，application，`let`，tuple，data constructor，primitive，`something`
- matcher literal，`matchAll`，pattern function
- `f ≠ x` と `DirectSelf.Holds f e` を要求する singleton direct-self の単相
  `fix f x.e`
- user pattern，primitive-pattern pattern，primitive data pattern，clause／arm
- actual clause からの決定的 evidence，`PPatCapsAt`，`ShapeCap`，`CoverageOK`

matcher literal の型付けは，actual clause list に対する `CatchAllLast`，data-arm
exhaustiveness，binder 線形性，`CoverageOK` を必須とする．coverage を欠く literal を
追加 mode で受理する経路はない．
Frozen signature の lookup table は有限 map として扱い，pattern-function 名の
非重複性を `FrozenSigWF` が明示的に保持する．
`HasTy.fix_inversion` は宣言的に型付く `fix` からこの二つの条件を回復し，
`higherOrderFix_untypable` は再帰 binder を引数として渡す具体反例の拒否を固定する．
Pattern-function 定義の本体は freeze 済みの完全な signature で型付けする一方，
自身の scheme は generalization の ambient free-variable 集合から除外する．
固定済み lookup scheme と context ごとの局所 generalization は，数値 binder 名の
構文的一致ではなく `DualScheme.ValueFlowEquivalent` で結ぶ．これは両 scheme の
`ValueFlowInst` が同じ引数／結果を許し，自由 capability／target 変数集合も等しいことを
要求する．従って alpha-renaming を含む観測不能な binder 表現差を許す一方，宣言の
value-flow 意味と ambient free-variable 境界は変えない．
自己 `papp` は `pval` 内の `matchAll` や matcher clause の next／arm body を含む
全構文を走査して拒否するため，別定義への参照を許しながら直接自己再帰を受理しない．

各 clause は最終 matcher capability でも添字付けされる．nested primitive-pattern
hole はその構造位置の capability と一致し，bare root hole だけが catch-all として
独立した slot capability を消費できる．Pattern constructor の capability projection は
partial evidence を返してよく，`CapCompatible` がそれを最終 capability の canonical
evidence と exact merge できることを要求する．このため，element capability を直接は
観測しない nullary `nil` も周囲の list capability と整合できる．Generic な
`projectSignature`／`CapCompatible` は result type variable へ到達する evidence だけを
運ぶ **result-variable evidence projection** を行う．Actual clause 専用の
`projectClauseSignature` は，その前段に actual hole evidence に対する
**closed field-head validation** を追加し，この二つを混同しない．
wildcard／value-pattern-pattern による `unseen` child は hole obligation を課さない．
一方，closed structured field は結果へ evidence を運ばなくても，actual hole の next
matcher が field の observable path と同じ capability head／arity を持つことを要求する．
`Matcher none [Integer]` 自体は有効であり，closed list hole の next matcher として
使う場合だけ不適合になる．

さらに formal core の primitive-pattern pattern は depth-first・左から右に走査し，
一度 hole を通過した後に value-pattern-pattern `#$x` が現れる形を禁止する．例えば
`cons $ #$x` や `($, #$x)` は core では不受理だが，`cons #$x $` は受理する．この順序は
`PPatCoreOrder`／`PPat.coreOrderCheck` で表し，`clauseEvidence` の成功条件とする．
`inferRaw` は matcher literal の finalization でこれを検査して不正順序を棄却し，公開
`infer` の terminal validator も最終 substitution の下で clause evidence を再計算する．
従って raw finalization と terminal cut の二箇所が fail closed になる．full Egison では利便性のため
同じ条件を `--pattern-hole-before-primitive-value-pattern-warnings` として警告にしてよい．

Expression context と pattern-function signature の value-flow scheme は，宣言的な
利用を二段階に分ける．最初に量化 capability を binder-local な capability variable
へだけ写し，その結果に量化 target binder だけを support とする構造的な target
substitution を順に適用する．この `ValueFlowInst` relation 自体は binder の像の
相異性や ambient freshness を要求しない．Algorithm W はこの relation を強化した witness として，
両 sort の binder へ互いに異なる fresh variable を signature と context の自由変数に
対して割り当てる．
別 scheme の局所 binder 名はこの ambient scope に含めない．利用側の consumer
demand に合わせて value producer の capability を構造化する instance は作れない．
一方，data constructor，pattern constructor，primitive operation の `Inst` は通常の
binder-supported な二 sort structural instance であり，この variable-only 条件の
対象ではない．
二段階は一つの global paired substitution へ潰さず，capability binder-local な
variable mapping の後へ target specialization を順に適用する．従って，後段が挿入した
自由 capability と同じ
番号の量化 binder があっても捕捉しない．型付け導出の後続輸送も，producer の
capability に対する variable-only mapping と target-only specialization に制限する．
この宣言的 post は単射性，像の相異性，ambient freshness を要求しない．一般の
`RestrictedPost.Chain` から忘却して得ることもできるが，公開再構成が使う target-only
suffix の capability 成分は恒等写像なので，terminal validator は `VariablePost` を
直接構成する．
`let` の輸送では，内側の generalization binder を target ambient の外へ局所的に
freshen してから導出を再構成する．これにより，外側の instance が導入した自由変数と
数値 identifier が一致しても捕捉されない．この freshening は導出される補題であり，
source typing や scheme 等式を追加前提にしない．

### Inference

二種 substitution を持つ executable Algorithm W が expression，pattern，slot，
matcher literal を検査する．各 fresh value instance の producer variable を
`protectedCaps` に記録し，全 solver step がそれらを固定することを実行時にも証明上も
監査する．matcher inference は coverage／exhaustiveness checker を必ず実行する．
Pattern constructor の未観測位置は fresh capability で埋め，literal 全体の prevailing
substitution が確定してから raw hole dual を一度だけ解決する．その後，全 clause の
core order，evidence，`PPatCapsAt` check を最終 capability に対して再計算する．
再計算時の `projectClauseSignature` による closed field-head validation は result type
variable の有無と独立であり，closed structured field の observable capability-head
mismatch も fail closed にする．Generic projection と `CapCompatible` の挙動は変えない．
user pattern constructor の子 pattern が別々の fresh consumer capability を持つために
result-variable の共有構造がまだ見えない場合は，一つの共有 result-variable skeleton を
作り，constructor の各 field type へ展開した demand（例えば `cons` なら
`kappa` と `List kappa`）に子の consumer capability だけを整合させる．最終 zonk 後に
exact projection を再実行し，terminal validator でも最終的な `CapCompatible` を再検査する．
これは pattern consumer 間の制約解決であり，value producer capability を consumer
demand から構造化する seed ではない．protected producer variable は従来どおり固定する．
共有 result variable に到達する field の内部では，到達しない observable subposition を
`none` に canonicalize して field 全体を整合させる保守的な fallback である．その位置だけを
無視する partial/path-wise alignment と W の completeness は主張しない．
再構成では生成時の raw provenance と，substitution 適用後の実際の index で構造を追う
terminal derivation を分ける．nested child の raw index と親の raw field index が
構文的に同一であることは仮定しない．

[`TypePM/PatternCtorCapabilityRegression.lean`](TypePM/PatternCtorCapabilityRegression.lean)
は，独立な二つの child consumer に対して旧 exact projection が失敗すること，fallback
後にはそれらが同じ fresh `kappa` と `List kappa` に zonk され，exact compatibility が
成功することを直接固定する．同じ回帰は protected-producer ledger が不変であり，全 solver
delta が protected producer を固定することも検査する．さらに target 側は整合するが
capability の rigid head が衝突する pctor を `inferRaw` と公開 `infer` が拒否し，capability
だけを整合させた control twin が公開 `infer` と `infer_success_sound` を通ることを対で固定する．
pattern-function instantiation が実際に ledger へ登録した protected variable を `cons` の
tail child に置く負例では，raw unifier が作る structural delta を producer guard が拒否する
ことを，直接 solver と raw/public inference の両方で検査する．

公開 entry point `infer` は，停止する二 sort W 走査 `inferRaw` の結果に
有限な terminal validator を適用する．validator は成功 trace の supply に基づく
binder-local instance，complete public cut での alignment と capability-variable post，
terminal context までの instance 合成，
generalization，coverage evidence を検査し，再構成に必要な `WBridgeWF` を構成する．
solver replay 自体は cross-sort-aware な `Subst.seq` の逐次合成から無条件に導く．
公開 soundness の経路では，生成時の `FreshInstAt` を後続 solver cut ごとに輸送せず，
終端の binder-local `ValueFlowInst`／`Inst` を有限 checker で直接構成する．
その条件に `HasTy` 自体や同型の導出を oracle として含めない．
`infer signature context expression = some result` ならば，`infer_success_sound` が
prevailing substitution で解決した context と結果型に対する concrete declarative
`HasTy` を与える．`InferenceInputWF` は意図する frozen Egison core 入力の静的境界を
別途記述するが，fail-closed な validator により soundness 定理の追加前提にはならない．
呼び出し側が bridge 証明書を渡す必要もない．
後段 post の target component は前段 target range に後段 capability action も適用するため，
二 sort の componentwise 合成や誤った可換性は仮定しない．
terminal validator が raw 成功を棄却する場合はあるため，completeness や full
principal-type theorem は主張しない．

### Principal core elaboration boundary

surface の `HasTy` は動的安全性の境界として維持しつつ，暗黙 coercion を明示化する
elaboration 層を追加した．[`TypePM/Elaboration.lean`](TypePM/Elaboration.lean) の
`SynthHead` は root の非 coercion 規則，`CoercionPlan` はその外側の coercion spine，
`CheckHead` は両者の合成を表す．`HasTy.factorHead` と `checkHead_iff_surface` により，
任意の surface typing がこの形へ分解でき，明示的 plan の replay が元の `HasTy` を
復元することを証明している．ただし `SynthHead` の再帰 premise はまだ `HasTy` であり，
これは **root factorization** であって再帰的な principal-core theorem ではない．

[`TypePM/CoreTyping.lean`](TypePM/CoreTyping.lean) は，既存の derivation-structured な
`Prop` 証明書 `Reconstruction.ExprDeriv` を `CoreTyping` として公開し，公開 `infer` の成功から
推論が選んだ coercion constructor に沿う oracle-free な core evidence が得られ，その
erase が surface soundness を与えることを固定する．Lean の proof irrelevance により，これは
観測可能な elaboration data ではなく，実行時に返す core AST でもない．
[`TypePM/CanonicalCoercion.lean`](TypePM/CanonicalCoercion.lean) はこの `Prop` 値の
`CoercionPlan` とは別に，型の頭を変える3つの observable primitive step，非空 spine，identity を含む `NormalPlan` を
観測可能な `Type` 値の候補 normal-plan syntax として定義する．これは一般の `trans` を持たず，
product matcher から slot への二段経路を `productMatcher; matcherToSlot` と固定する．product of
slots から一致する aggregate slot へは `slotTuple` 一段である．surface の slot-to-slot check は
capability／target MGU と後置換の後で両端が等しいことを証明し，`NormalPlan.refl` へ吸収する．
全 `Step`／`Spine` が端点を変えることと，同じ端点の `NormalPlan` は `refl` だけであることも
証明済みである．空 product の `slotTuple` は constructor 側で禁止し，matcher-product precedence
を syntax にも反映する．既存 surface plan／`HasTy` への replay soundness は証明済みである．
一方，任意 plan の normalization，normalization の一意性，および異なる端点に対する plan
inhabitant の一意性は未証明である．公開推論がこのデータを直接返すことも次段階である．

product-of-matchers から product matcher への規則は
tuple literal 専用ではなく unary な `COERCE-PRODUCT-MATCHER` とした．このため coercion は
`let` の束縛時ではなく変数利用位置にも挿入できる．
`expectedCoercionSource` は matcher／slot が要求されたとき，raw synthesized type が
product-of-matchers なら product-matcher lift，slot が要求され raw type が product-of-slots
なら slot-tuple lift という branch を決定的に選び，`alignExprResultAtExpected` がその後の
type equality または slot alignment を行う．空 product は両 recognizer に一致するため，
coherence policy として product-matcher branch を先に選ぶ．これは selector の決定性であって，
surface coercion 全体の一意性をまだ意味しない．
`checkExprFuel` と通常の関数適用はこの非再帰 helper を共有する．関数適用は function を推論し，
fresh domain／codomain へ整合してから argument を domain に対して check するため，ordinary
application の引数位置でも product matcher／matcher-to-slot／slot-tuple coercion を挿入できる．
terminal reconstruction は同じ選択から `ExprDeriv.coerceProductMatcher` または
`ExprDeriv.coerceSlotTuple` を構成し，solver trace に型付け oracle を追加しない．現段階の
selector は raw type の頭を検査するので，raw metavariable が prevailing substitution 後に初めて
product-of-matchers または product-of-slots になる場合（component metavariable が初めて matcher／
slot になる場合を含む）は completeness の今後の課題として残る．

[`TypePM/CapabilityOrigin.lean`](TypePM/CapabilityOrigin.lean) は capability metavariable を
`rigid`，`renameOnly`，`structuralFlexible` に分ける有限 ledger と，ledger に対する admissible
paired post を定義する．identity と cross-sort-aware な `Subst.seq` による合成閉性，変数単位／
ledger 全体の freeze，freeze 後に既存 `VariablePost` 境界へ入る bridge を証明している．さらに
`PhasedPost` は局所 structural post と frozen residual post を分離し，後者だけを既存
`VariablePost` へ接続する．現段階の `AdmissiblePost` が制約するのは capability component だけで，
target component は意図的に制約していない．これは
constructor／primitive の局所 structural instantiation と既存 producer の非強化を区別する
代数的基礎である．W の `InferState.capabilityOrigins` はこの ledger を shadow metadata として保持し，
一般 fresh capability と constructor／primitive image を `structuralFlexible`，context scheme／
pattern-function image と finalized matcher の visible producer を `renameOnly` と記録する．ただし
constraint acceptance と terminal audit は従来の `protectedCaps` をそのまま使うため，受理挙動はまだ
変えていない．origin-aware solver へ切り替えるには，solve cut ごとの ledger snapshot，MGU の
origin-aware orientation，および raw binder ではなく局所 solve 後に外へ生存する prevailing image の
leaf を freeze する export event が必要である．

今後必要なのは，この root 境界と observable plan syntax を再帰的な canonical core judgment
へ強化することである．その前提として，algorithmic／surface plan から `NormalPlan` への
normalization completeness，component-first 経路を含む critical pair の解消と normalization
uniqueness，coercion の意味的同値，置換に対する naturality，および normalized product が判明した
solve cut を保存する cut-indexed evidence が必要になる．その上で W が生成する core typing の
一意性（binder の alpha 同値を除く），MGU による置換普遍性，および任意の coherent surface
typing がその置換と明示的 coercion から得られる completeness を証明する．現行
`TerminalPatternResolution` の leaf は freshness 用 `rawContext` と
`actualContext` を独立に選べるため，`HasTy` 全体には algorithmic provenance を持たない導出も
含まれる．[`TypePM/CoherentSurface.lean`](TypePM/CoherentSurface.lean) は第一段階として，
各 terminal pattern leaf の actual context を definitionally
`rawContext.applySubst prevailing` に固定する indices-only な
`CoherentTerminalPatternResolution(s)` と `CoherentResolvedPatternTy` を追加する．coherent
evidence から既存 surface judgment への forgetful map と，inference reconstruction の
`PatternResolutionDeriv(s)`／`ResolvedPatternDeriv` がこの leaf-local 境界へ入る bridge も証明する．
さらに `ThreadedPatternResolution(s)` は一つの raw `Context`／`PatternCtx` を全 child で共有し，
raw `MonoCtx` だけを binder 導入順に threadする．この強い judgment から leaf-local 境界への
forgetful map は証明済みである．一方，既存 `PatternResolutionDeriv` は composite node に top-level
raw provenance を保持せず，置換も非単射なので，そこからの一般 bridge は意図的に置かない．次は W の
pattern reconstruction motive 自体から threaded evidence を同時生成する必要がある．また `pval` 内の
式 typing はまだ通常の `HasTy` なので，いずれも pattern-local provenance coherence に限られ，full
recursive coherent surface judgment ではない．その後 expression，arm，clause まで相互再帰的に同じ
境界を広げる．現時点ではこれらを principality として主張しない．

### Runtime safety

runtime matcher value は，生成元の actual clause list と現在の clause cursor を別々に
保持する．suffix cursor は一つの atom dispatch の内部だけで使い，公開 state では
値・captured environment・tree・stack 全体に `Pristine` を要求する．`ValueTy` は
intrinsic capability，target，captured environment，source matcher derivation，coverage
を保持する．matching state の型付けは atom ごとの
prevailing substitution，pattern-function node の隔離された parameter context，
残余 actual argument，内部 stack を追跡する．

Ordered dispatch は失敗済み clause prefix を `DispatchTrace` で追跡する．Frozen
signature の pattern-constructor capability 一意性と coverage-index coherence により，
structured pattern が先行する対応 clause をすべて飛ばして bare-hole catch-all へ到達する
不正な branch を排除する．

`CoreSafety` は次を個別に取り出せる形でまとめ，`core_safety` が concrete
judgment 上の証明を与える．各 preservation／reachability／search 結論は，対象の
concrete derivation に付随する `*RuntimeSigAgrees` mirror と，source context に対する
`RuntimeSigAgrees` を引数に取る．したがって任意の runtime signature を無条件に source
signature と同一視する主張ではない．
[`TypePM/RuntimeAgreementBridge.lean`](TypePM/RuntimeAgreementBridge.lean) は，
`∀ context, RuntimeSigAgrees signature context SF` という一つの global agreement
から，任意の concrete `Eval`／`PPM`／`MAtom`／`Step`／`Search`／`Reaches` 導出に対応する
mirror を，その導出の構造に沿って構成する．従って mirror family は実行導出を外部から
与える oracle ではない．

1. pristine な typed environment からの expression evaluation の preservation
2. matching state 一段の preservation
3. matching state の local progress
4. 到達可能な全 state の型付け
5. 成功した terminal match substitution の型付け
6. 上の終端性質としての matcher consistency

[`TypePM/SignatureChecker.lean`](TypePM/SignatureChecker.lean) は，動的定理の唯一の
global 条件である `FrozenSigWF` を，有限の実行可能検査 `frozenSigWFCheck` の成功から
構成する（`frozenSigWFCheck_sound`）．検査は保守的で fail closed である．canonical な
`nil`／`cons` 宣言が `ListSigWF` を witness し，data constructor は構文的 data root と
binder 被覆を検査して（instantiation の一意性は substitution-agreement の逆補題から
従う），pattern constructor は単一パラメータ collection family（`nil`／`cons`／`join` 型）
に限定して capability projection の明示的 inversion から uniqueness と index coherence を
導出する．各 pattern constructor には `constructorsByFormer` の対応 row と
`(name, arity)` membership を必須とし，row 欠落は fail closed で拒否する．この row は
保守的 coverage index であり，追加 entry は許すが coverage obligation を強めるだけである．primitive は
canonical scheme との一致を検査して delta preservation を
operation ごと（`append`，`splits`）に一度証明する．関数値 field
`armExhaustive = basicArmExhaustive` だけは signature 構成時の定義等式として受け取る．
`DynamicSafetyRegression`／`PatternFunctionSafetyRegression` の `signature_wf` は
この checker の一回の実行（`by decide`）で立ち，`RecursiveExamples` の
`listSignature`／`multisetSignature` には非空 pattern-constructor 表に対する初の
非空虚な `FrozenSigWF`（`listSignature_wf`／`multisetSignature_wf`）が立つ．対応 row を
削った List signature は checker が拒否する．

[`TypePM/DamasMilner.lean`](TypePM/DamasMilner.lean) は，pattern を含まない
`λ`/`let`/direct-self `fix` 断片について，独立に定義した一 sort の Damas–Milner 体系
`DM.HasTy` を与える．その再帰規則は core と同じ `self ≠ argument` と
`DirectSelf.Holds self body` を要求し，**この制限体系のすべての導出が閉じた frozen
signature 上の二 sort 宣言体系へ埋め込まれる**こと（`DM.HasTy.emb`）を証明する．
埋め込みの下で capability sort は不活性で
ある：capability binder は空，capability substitution は自明に作用し（`STy.emb_fcv` = 空），
`let` の一般化は二 sort generalizer と可換（`generalize_emb`）．多相 `let` の証人
`let id = λx.x in (id id) 1` の DM 導出とその埋め込みも固定する．逆方向
（conservativity）と algorithmic acceptance（公開 `infer` が DM program を全受理すること）は
主張しない．

[`TypePM/PrincipalityCounterexample.lean`](TypePM/PrincipalityCounterexample.lean) は，
宣言体系のprincipalityが**そのままの形では偽**であることを機械化された反例で確定する．
閉じた式 `(something, something)` は T-TUPLE でmatcherのproduct型に，
COERCE-PRODUCT-MATCHER でproduct matcher型に型付き，両者の頭構成子（`prod` と `matcher`）は
異なる．tuple式の導出可能型の頭は `prod`/`matcher`/`slot` に限られ（`tuple_ty_head`），
paired substitutionは頭を保存するため，両方をinstanceに持つ導出可能型は存在しない
（`no_principal_type`）．失敗の原因はcoercionの重なりそのもの（使えるproduct matcherの代価）で
あり，capability evidenceとは独立である．制限されたprincipality文はこの重なりを除外する必要が
ある．coercionを持たない DamasMilner 断片は影響を受けない．

[`TypePM/ElaborationRegression.lean`](TypePM/ElaborationRegression.lean) は，この反例の
product 型を canonical な root synthesis として固定し，product matcher view を明示的
`CoercionPlan` として replay する．さらに product 型のまま `let` を越えた変数へ unary lift を
利用位置で適用できることを宣言的に証明する．
[`TypePM/CertifiedInferenceRegression.lean`](TypePM/CertifiedInferenceRegression.lean) は，
executable checker の selector が matcher 期待時に product matcher を，slot 期待時にも
matcher-to-slot の入力となる同じ product matcher branch を決定的に選ぶことに加え，product-of-slots の
slot-tuple 選択と，三種類の coercion を必要とする domain-directed application が公開 inference
で成功することを `#guard` で固定する．各結果が `Int` で，terminal substitution 後の alignment
端点が期待どおりであることも検査し，component ごとの matcher-to-slot を暗黙に挿入する負例は拒否する．
[`TypePM/ApplicationCoercionRegression.lean`](TypePM/ApplicationCoercionRegression.lean) は，対応する
三つの application について，product-matcher，matcher-to-slot，slot-tuple を明示的に使う
surface `HasTy` 導出を与える．さらに空 product の競合を matcher-first の二段 `NormalPlan` へ
固定する．

正当な match failure（後続 state が空）は stuck ではない．値パターン式が原子入力の
context で型付くことを表す局所 `CaptureAdm` は，clause の `PPatCoreOrder`，PP typing，
user-pattern typing，成功した `PPM` から `captureAdm_of_coreOrder` が導く．したがって
`OperationalCaptureAdm` のような caller-supplied premise は公開 safety surface にない．
一段の dispatch が必要とする局所評価・decode 結果だけを `StepReady` として progress に
明示し，一般の program termination は仮定しない．この local progress は古典的な
「型付けだけから一段を発見する」定理ではなく，規則ごとの局所的な実行証拠から concrete
`Step` を組み立てる境界である．

[`TypePM/DynamicSafetyRegression.lean`](TypePM/DynamicSafetyRegression.lean) は，
`SF = []` の concrete frozen signature と実際の `matchAll` 実行について，
`FrozenSigWF`，global runtime agreement，評価・primitive-pattern matching・atom reduction・
step・search・reachability と各 mirror を同時に構成し，`CoreSafety.evalPreservation` を
実際に適用する end-to-end 回帰である．公開 W の結果と保存後の runtime value はともに
`List Int` へ固定する．

[`TypePM/DynamicCaptureRegression.lean`](TypePM/DynamicCaptureRegression.lean) は，合法な
`#$captured` clause について `PPM.pval`，`MAtom.matcher`，`Step`，`Search`，`Reaches`
を具体的に接続する．`AtomTy.mk` から構成した初期 state へ
`CoreSafety.stepPreservation` を適用するため，`captureAdm_of_coreOrder` の value-pattern
分岐が実際の matcher reduction で消費される．結果型は `List Int` に固定する．

[`TypePM/DynamicDispatchRegression.lean`](TypePM/DynamicDispatchRegression.lean) は，具体的な
`cons $x $rest` の実行を，先行 `nil` clause の primitive-pattern mismatch，`cons` clause
先頭 arm の data-pattern mismatch，次 arm の成功へ順に通す．単一の kernel 導出内で
`MAtom.matcherPPFail`，`MAtom.matcherDPFail`，二 child の `PPM.ctor`，`MAtom.matcher` を
発火させ，同じ失敗証拠から `DispatchTrace.nextClause`／`nextArm` も構成する．生成された
`x`／`rest` atom を二段で束縛し，`Step`，`Search`，`Reaches`，`matchAll` の具体評価まで
terminal に閉じる．さらに同じ三段の private cursor 遷移を，非再帰 `Pair α` family の
型付き fixture でも発火させる．後者は `frozenSigWFCheck` と公開 `infer` を通り，非空な
`[(rest, 2), (x, 1)]` へ到達する同一実行に `evalPreservation`，`stepPreservation`，
reachability，search substitution typing，matcher consistency を適用する．

[`TypePM/PatternFunctionSafetyRegression.lean`](TypePM/PatternFunctionSafetyRegression.lean)
は，closed nullary pattern function `unit := ptuple []` を source と runtime の非空
signature に置き，`∀ context, RuntimeSigAgrees` からこの実行に必要な各 mirror を構成する．
非空な `RuntimeSigAgrees.sourceLookup` も step preservation と local progress で実際に消費する．実行は
`papp` から `mnode` へ入り，inner atom reduction と completed-node removal を経て terminal
state に到達する．この一例で `CoreSafety` の六フィールドをすべて具体的に適用し，search
と matcher consistency には実際の `[] ∈ [[]]` を渡す．公開 W の結果も `List Int` に固定する．
加えて非 nullary の `pass(parameter : Unit) := embed parameter` について，context ごとに
fresh な binder を選んだ局所 scheme と固定 lookup scheme の value-flow 外延同値を構成する．これにより
`∀ context, RuntimeSigAgrees` と実際の `patfunEnter` step の `of_global` mirror が，
引数を持つ定義でも成立することを固定する．

### Recursive matcher regressions

[`TypePM/RecursiveExamples.lean`](TypePM/RecursiveExamples.lean) は，外部の
型付け済み matcher 定数ではなく，実際の `fix self m. matcher ...` 本体を検査する．

- list: direct-self source typing と W の成功
- paper-complete multiset interface: list とは別の self binder／clause list に対する
  source typing と W の成功
- simplified multiset: `join` 一般節不足により `coverageCheck = false`，
  `¬ CoverageOK`，raw W，公開 W のすべてが失敗
- generic `listSignature` と `fix` で構成した `listMatcher` を slot に適用し，
  `matchAll` の `cons $x $rest` が束縛した `x` と `rest` の両方を body で使う旗艦例が
  公開 `infer` を通過する．結果型を concrete literal に固定し，成功等式から
  `infer_success_sound` により `HasTy` を再構成する．これは静的 inference 回帰であり，
  再帰 matcher の動的実行は主張しない
- 量化 binder と target specialization 内の自由 capability が同じ番号でも，ordered
  binder-local instance と let generalization が成功

[`TypePM/ProducerStrengtheningRegression.lean`](TypePM/ProducerStrengtheningRegression.lean)
は，同一の structured consumer に対して，fresh capability variable を公開する
polymorphic value producer を公開 `infer` が拒否することと，要求済みの concrete
producer へ置き換えた control twin が成功することを対で検査する．成功側は結果型を
`Int` に固定し，`infer_success_sound` から concrete `HasTy` も構成する．

## 明示的な境界

次はこの formal core の主張に含めない．

- Algorithm W の completeness／full principality
- alias，mutual recursion，transform，高階 origin を含む一般 producer-flow 解析
- raw declaration から frozen signature を構築する validator
- full Egison の warning mode の実装，module/import persistence，標準ライブラリ移行
- CAS の target-indexed pattern view
- 一般の評価停止性

## モジュール

| 層 | 主なファイル | 内容 |
|---|---|---|
| 型代数 | `Syntax`, `Substitution`, `Relation`, `CapMatch`, `Unification` | 二 sort，代入，自然性，one-way match，solver |
| capability | `Observability`, `Shape`, `Projection`, `Canonical`, `CapTarget`, `Recursion` | 観測可能性，evidence，projection，direct-self shape fold |
| source | `Term`, `ClauseEvidence`, `Source`, `SourceSubstitution`, `SourceGeneralization`, `SourceMetatheory`, `PatternFunction` | concrete syntax と宣言的型付け，coverage，安全な一般化と輸送 |
| elaboration | `Elaboration`, `CoreTyping`, `CanonicalCoercion`, `CapabilityOrigin`, `CoherentSurface` | root factorization，暫定 core evidence，observable coercion-plan syntax，origin-sensitive phased post，pattern-local coherent surface 境界 |
| runtime | `Semantics`, `Dynamic`, `Preservation`, `DynamicMetatheory`, `Reachability`, `Safety`, `RuntimeAgreementBridge` | 評価・matching semantics，state invariant，preservation/progress/safety，global agreement からの derivation-local mirror 構成 |
| W | `InferenceBase`, `Inference`, `InferenceInput`, `InferenceHistory`, `Reconstruction`, `BridgeChecks`, `CertifiedInference`, `InferenceRegression`, `Soundness` | raw W 走査，入力整形性，append-only history，terminal validation，declarative reconstruction，公開 inference soundness，concrete safety composition |
| 回帰 | `ClauseEvidenceExamples`, `GeneralizationRegression`, `CertifiedInferenceRegression`, `ApplicationCoercionRegression`, `RecursiveExamples`, `ProducerStrengtheningRegression`, `PatternCtorCapabilityRegression`, `DynamicSafetyRegression`, `DynamicCaptureRegression`, `DynamicDispatchRegression`, `PatternFunctionSafetyRegression` | evidence，source-level binder collision，domain-directed coercion，公開 inference soundness，recursive matcher の旗艦例と正負例，producer non-strengthening と PAT-CON の public control twin，空／非空 runtime signature，capture，型付き ordered dispatch を含む動的安全性の具体適用 |

各ファイルは `TypePM/` 以下にある．

## 検証

Lean 4 toolchain は [`lean-toolchain`](lean-toolchain) で固定し，外部依存や Mathlib は
使わない．

```sh
lake build
```

形式仕様 PDF は必ず `tex/` の Makefile を使う．

```sh
cd tex
make
```

出力は `tex/type-pm-mech.pdf` である．`sorry`，`admit`，project-defined `axiom` は
使用しない．主定理，一般補題，および `#guard`／kernel reduction で評価する小さな回帰は kernel が
検査する．一部の大きな具体的実行回帰で用いる `native_decide` だけは Lean の native compiler を
追加で信頼するため，この二層を区別する．
