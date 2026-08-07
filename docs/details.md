# 詳細仕様と証明状況

この文書はモジュール単位の詳細仕様・証明済み事項・非主張事項の目録である．
大局的な目標・設計原理・ロードマップは [`README.md`](../README.md)，作業規律は
[`CLAUDE.md`](../CLAUDE.md)，形式仕様は [`tex/main.tex`](../tex/main.tex) にある．

## calculus の要点

現行 calculus は matcher producer と利用位置の要求を分ける．

```text
Matcher     κ τ   -- 値が生成時から持つ intrinsic capability
MatcherSlot κ τ   -- pattern site が要求する consumer capability
```

capability と target type は別 sort，別変数，別 substitution，別 quantifier を持つ．
producer から slot への接続は対称単一化ではなく producer-stable な one-way check で
行う．動的定理は concrete source/runtime judgments だけを使う．

`Any` はこの one-way check の **consumer 側に明記されたときだけ** wildcard であり，
任意の producer capability を受理する．producer 側の `Any` は wildcard ではない．また，
consumer 変数 `κ` が一度 `Any` に束縛されても，二度目以降の同じ `κ` は保存された
`Any` と厳密に一致しなければならない．従って `[Any, K]` を `[κ, κ]` に合わせることは
失敗する一方，literal `[Any, κ, κ]` の先頭だけは独立した wildcard になる．対称な
`mguCap` では `Any` は通常の rigid ground constructor であり，`Any = Any` のみが
直接成功する（flexible variable を `Any` へ束縛することはできる）．

## Source typing

対象構文: lambda，application，`let`，tuple，data constructor，primitive，
`something`，matcher literal，`matchAll`，pattern function，`f ≠ x` と
`DirectSelf.Holds f e` を要求する singleton direct-self の単相 `fix f x.e`，
user pattern，primitive-pattern pattern，primitive data pattern，clause／arm，
actual clause からの決定的 evidence，`PPatCapsAt`，`ShapeCap`，`CoverageOK`．

matcher literal の型付けは，actual clause list に対する `CatchAllLast`，data-arm
exhaustiveness，binder 線形性，`CoverageOK` を必須とする．coverage を欠く literal を
追加 mode で受理する経路はない．
Frozen signature の lookup table は有限 map として扱い，pattern-function 名の
非重複性を `FrozenSigWF` が明示的に保持する．
`HasTy.fix_inversion` は宣言的に型付く `fix` からこの二つの条件を回復し，
`higherOrderFix_untypable` は再帰 binder を引数として渡す具体反例の拒否を固定する．
Pattern-function 定義の本体は freeze 済みの完全な signature で型付けする一方，
自身の scheme は generalization の ambient free-variable 集合から除外する．
その canonical core payload は引数と結果（target 型内部の capability も含む）を一つの
occurrence 列として数える．signature または context に自由な ambient capability は
そのまま自由に保ち，非 ambient な変数は，一度だけ現れるなら全出現を `Any` に
canonicalize し，二度以上現れるなら一つだけ量化して共有を保存する．`PatternDefTy` は
この正規化済み引数／結果に対する，一つの prevailing substitution を伴う
`ResolvedPatternTy` として本体を保持する．この prevailing substitution を canonical な
singleton-default substitution そのものとは同一視しない．利用時の `ValueFlowInst` は共有変数の
rename と target specialization だけを行い，singleton default を後付けの構造置換として偽装しない．
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
`Matcher Any [Integer]` 自体は有効であり，closed list hole の next matcher として
使う場合だけ不適合になる．

formal core の primitive-pattern pattern は depth-first・左から右に走査し，
一度 hole を通過した後に value-pattern-pattern `#$x` が現れる形を禁止する．例えば
`cons $ #$x` や `($, #$x)` は core では不受理だが，`cons #$x $` は受理する．この順序は
`PPatCoreOrder`／`PPat.coreOrderCheck` で表し，`clauseEvidence` の成功条件とする．
`inferRaw` は matcher literal の finalization でこれを検査して不正順序を棄却し，公開
`infer` の terminal validator も最終 substitution の下で clause evidence を再計算する．
従って raw finalization と terminal cut の二箇所が fail closed になる．full Egison では利便性のため
同じ条件を `--pattern-hole-before-primitive-value-pattern-warnings` として警告にしてよい．

### value-flow scheme の variable-only 条件

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
自由 capability と同じ番号の量化 binder があっても捕捉しない．型付け導出の後続輸送も，
producer の capability に対する variable-only mapping と target-only specialization に制限する．
この宣言的 post は単射性，像の相異性，ambient freshness を要求しない．一般の
`RestrictedPost.Chain` から忘却して得ることもできるが，公開再構成が使う target-only
suffix の capability 成分は恒等写像なので，terminal validator は `VariablePost` を
直接構成する．
`let` の輸送では，内側の generalization binder を target ambient の外へ局所的に
freshen してから導出を再構成する．これにより，外側の instance が導入した自由変数と
数値 identifier が一致しても捕捉されない．この freshening は導出される補題であり，
source typing や scheme 等式を追加前提にしない．

## Inference（Algorithm W）

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
`Any` に canonicalize して field 全体を整合させる保守的な fallback である．その位置だけを
無視する partial/path-wise alignment と W の completeness は主張しない．
再構成では生成時の raw provenance と，substitution 適用後の実際の index で構造を追う
terminal derivation を分ける．nested child の raw index と親の raw field index が
構文的に同一であることは仮定しない．

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

### coercion selector（現行実装）

`checkExprFuel` は式を期待型なしで先に synthesize し，その出力 state の prevailing
substitution を expected 型へ適用してから head を観測する．matchAll の matcher 位置と
matcher clause の next-matcher 位置は，どちらも slot 頭の expected 型で check する．
通常の application は function を fresh domain／codomain へ先に整合してから argument を
同じ helper で domain-directed に check し，`let` を越えた変数利用位置にも同じ
coercion を挿入できる（lift は tuple literal 専用ではない）．

`expectedCoercionSource` は raw synthesized type が product-of-matchers かつ expected
head が slot のとき product-matcher lift（`alignAtSlot` が続けて producer-stable な
matcher-to-slot を行う二段），raw type が product-of-slots かつ expected head が slot の
とき slot-tuple lift を決定的に選び，`alignExprResultAtExpected` がその後の type
equality または slot alignment を行う．branch 選択は alignment より前に確定し，選んだ
branch の solve が失敗しても別 branch へ切り替えない．空 product は両 recognizer に
一致するため，coherence policy として product-matcher branch（matcher-first の二段）を
先に選ぶ．これは selector の決定性であって，surface coercion 全体の一意性ではない．
`alignAtSlot` の matcher-to-slot 分岐も expected が slot 頭の場合に限られ，
matcher-expected 位置に raw Matcher が来る場合（`Pack something` 等）は coercion では
なく通常単一化で通る．

matcher-expected で product lift 単独（Matcher 終点）を選んでいた旧分岐は段階 3-0 で
撤去済みである．matcher-expected 位置に product-of-matchers が来る形（matcher 引数を
宣言した署名 ctor へのタプル渡し・matcher 頭に固定された λ domain への渡し等）は
意図された拒否であり，負の regression（`productMatcher_expected_source` の identity
検査と `#guard !productMatcherArgumentApplicationSucceeds`）で固定する．
slot-demand 原則自体も selector の定理として機械化済みである：
`expectedCoercionSource_slotDemand`（selector が source を変えたなら prevailing 適用後の
expected は slot 頭）と `expectedCoercionSource_matcherExpected`（matcher 頭の expected
では selector は恒等）．

現段階の selector は `S₁ τraw` ではなく raw `τraw` の頭を検査するので，raw
metavariable が prevailing substitution 後に初めて product-of-matchers または
product-of-slots になる場合（component metavariable が初めて matcher／slot になる場合を
含む）の completeness は非主張である．この gap は normalized image から raw indices を
逆算したり prevailing substitution の冪等性を仮定したりせず，solve cut で得た
normalized product と後続 suffix を明示する cut-indexed coercion event として将来扱う
（README 段階 4-1）．`RawSourceVisible` はこの実装上の死角だけを隔離する fragment
条件であり，expected head による demand の可否とは分けて扱う．

## Coercion・elaboration 層

### 宣言的 coercion 規則（wide `HasTy`）

`HasTy` の coercion 規則は COERCE-MATCHER-TO-SLOT（producer-stable one-way check），
CHECK-SLOT-TO-SLOT，unary COERCE-PRODUCT-MATCHER，COERCE-SLOT-TUPLE である．
これらは位置の demand と無関係に使える意図的に広い**動的安全性の包絡**であり，
このまま維持する（受理完全性の前提には使わない）．product lift が unary であるため，
宣言的には product 型のまま `let` を越えた変数の利用位置にも lift を挿入できる
（`ElaborationRegression.let_bound_pair_checks_as_product_matcher`）．

### root factorization と core certificate

[`TypePM/Elaboration.lean`](../TypePM/Elaboration.lean) の
`SynthHead` は root の非 coercion 規則，`CoercionPlan` はその外側の coercion spine，
`CheckHead` は両者の合成を表す．`HasTy.factorHead` と `checkHead_iff_surface` により，
任意の surface typing がこの形へ分解でき，明示的 plan の replay が元の `HasTy` を
復元することを証明している．ただし `SynthHead` の再帰 premise はまだ `HasTy` であり，
これは **root factorization** であって再帰的な principal-core theorem ではない．

[`TypePM/CoreTyping.lean`](../TypePM/CoreTyping.lean) は，既存の derivation-structured な
`Prop` 証明書 `Reconstruction.ExprDeriv` を `CoreTyping` として公開し，公開 `infer` の成功から
推論が選んだ coercion constructor に沿う oracle-free な core evidence が得られ，その
erase が surface soundness を与えることを固定する．Lean の proof irrelevance により，これは
観測可能な elaboration data ではなく，実行時に返す core AST でもない．`CoreSynthHead` は
再帰 premise をすべて reconstruction evidence に保った非 coercion head，`CoreCheck` はそれと
明示的 `CoercionPlan` の合成であり，`coreCheck_iff_coreTyping` が既存 core certificate との同値を
与える．公開 inference の成功もこの factorization を構成する．
`CoreTyping.factorNormalHead` は外側 plan に対する `Nonempty NormalPlan` witness の
論理的存在を与えるが，これらを full core principality と呼ばない．

### canonical coercion plan

[`TypePM/CanonicalCoercion.lean`](../TypePM/CanonicalCoercion.lean) は `Prop` 値の
`CoercionPlan` とは別に，型の頭を変える3つの observable primitive step
（`productMatcher`／`matcherToSlot`／`slotTuple`），非空 spine，identity を含む
`NormalPlan` を観測可能な `Type` 値の候補 normal-plan syntax として定義する．一般の
`trans` を持たず，product matcher から slot への二段経路を
`productMatcher; matcherToSlot` と固定する．product of slots から一致する aggregate
slot へは `slotTuple` 一段である．surface の slot-to-slot check は capability／target の
決定的 unifier と後置換の後で両端が等しいことを証明し，`NormalPlan.refl` へ吸収する．
全 `Step`／`Spine` が端点を変えることと，同じ端点の `NormalPlan` は `refl` だけである
ことも証明済みである．空 product の `slotTuple` は constructor 側で禁止し，
matcher-product precedence を syntax にも反映する．既存 surface plan／`HasTy` への
replay soundness に加え，`NormalPlan.comp` と `CoercionPlan.normalizable` により任意の
外側 plan が `NormalPlan` を持つことも証明する．空 product は matcher-first の
二段経路へ正規化される．`CoercionPlan : Prop` から `NormalPlan : Type` の値を計算で
取り出せないため，結果は `Nonempty` に包まれる．observable rule 列（`kinds`）は同じ
端点から一意に決まることも証明済みである．raw certificate を含む plan inhabitant 自体の
一意性，および公開推論が observable plan data を直接返すことは未証明である．

slot-demand 原則の下で demand 経路（selector／将来の `DDTyping`）が到達する非恒等
plan は，終点が slot 頭の三形
`[matcherToSlot]`／`[productMatcher, matcherToSlot]`／`[slotTuple]` に限られる．
単独 `[productMatcher]`（Matcher 終点）は plan syntax としては残るが wide `HasTy`
専用になる．

### coherent surface typing

現行 `TerminalPatternResolution` の leaf は freshness 用 `rawContext` と `actualContext` を
独立に選べるため，`HasTy` 全体には algorithmic provenance を持たない導出も含まれ，
無条件の `HasTy → ExprDeriv` は主張しない．再帰的 completeness は
`actualContext = rawContext.applySubst prevailing` を満たす coherent surface subset を
対象にする．[`TypePM/CoherentSurface.lean`](../TypePM/CoherentSurface.lean) は
pattern-local な coherent 境界を与える：各 terminal pattern leaf の actual context を
definitionally `rawContext.applySubst prevailing` に固定する indices-only な
`CoherentTerminalPatternResolution(s)`／`CoherentResolvedPatternTy`（第一境界），一つの
raw `Context`／`PatternCtx` を全 child で共有し raw `MonoCtx` だけを binder 導入順に
thread する強い `ThreadedPatternResolution(s)`（第二境界，第一境界への forgetful map
つき），および surface への forgetful map と reconstruction bridge である．
`PatternResolutionDeriv(s)` も同じ raw context と raw binding thread を保持し，W の
pattern reconstruction motive がこれを直接生成する．その `pval` premise は再帰的な
`ExprDeriv` を要求し，arm と clause も reconstruction family に閉じているため，公開
inference が返す `CoreTyping` は全構文部分で surface typing oracle へ戻らない．一方，
独立した surface `ThreadedPatternResolution(s)` の `pval` premise は plain `HasTy` の
ままである．`pval` leaf のない pattern では threaded surface 境界が reconstruction
証明書へそのまま昇格する（`Pattern.pvalFree`・
`ThreadedPatternResolution.toDeriv_of_pvalFree`）．

[`TypePM/CoherentTyping.lean`](../TypePM/CoherentTyping.lean) はこれを coherent surface
typing として公開する：`CoreTyping` と同じ前例に従い，
`Coherent.CoherentExpr := ExprDeriv` ほか 10 family を定義的 abbreviation とし
（鏡写しの独立 mirror は維持しない），surface への忘却 `CoherentExpr.toHasTy` と
推論成功から coherent typing を得る `infer_success_coherent` を持つ．product lift
構成子（`ExprDeriv.coerceProductMatcher`／`coerceSlotTuple`）は raw-source と lift
substitution の provenance 添字を certificate 本体に持ち，W の reconstruction motive
（`expectedCoercionSource_deriv`）は selector が実際に頭を検査した raw type と terminal
substitution を faithful に注入する．恒等 witness が常に取れるため判断は制限されず，
plan replay（`CoercionPlan.toCoreTyping`）と match-free 埋め込みは縮退 witness を
供給する．coherence が制限するのは pattern の provenance だけなので，`matchAll` と
matcher literal を含まない **match-free 断片では任意の surface typing が coherent**
であり（`coherent_of_matchFree`），その系として Damas–Milner 断片のすべての宣言的
型付けは埋め込みを経て coherent judgment に入る（`dm_coherent`）．これらを
algorithmic completeness や principality とは呼ばない．

### demand-directed judgment

[`TypePM/DemandTyping.lean`](../TypePM/DemandTyping.lean) は，README の設計原理節が
固定した demand-directed judgment を全構文層に対して定義する．主 mutual family は
`DDSynth`／`DDSynths`／`DDCheck`／`DDChecks`／`DDPattern`／`DDPatterns`／`DDArms`／
`DDClause`／`DDClauses` の 9 judgment で，fresh supply と prevailing paired
substitution を入出力で thread する（`DDPattern` は monomorphic binding context も
左から右へ thread する）．式を参照しない `DDPPat`／`DDPPats`（primitive pattern，
holes＋bindings 出力）と `DDDPat`／`DDDPats`（data pattern）は主 mutual block の外で
閉じる自己完結対である．`DDCheck` の規則は一つ（synthesize してから出力 cut で
`DDAlign`）．capability freeze／export ledger の軸は判断に含めない（段階 3-3 の
`FreezeCompatible` 対応条件）．

pattern 層は実行走査を次の二層で写す．fresh 割当は supply-indexed な純関数 twin —
`freshTargetsSupply`（tuple 成分 target）・`freshenSkeletonSupply`（skeleton
freshening，masked／list 版込み）・`patternCtorAssignmentsSupply`（shared result
assignment）・`fixMatcherPlaceholderSupply`（matcher-bodied 再帰 binder の
placeholder）— として，solver 列は関係的整合 — `DDAlignDual`（capability 先行の
dual 整合）・`DDAlignDualList`・`DDAlignTargetList`（constructor field 整合）・
`DDAlignBindings`（or-alternative の名前位置照合＋型単一化）・`DDAlignCtorCaps`
（shared demand への capability solve）・`DDPatternCtorCap`（pattern-constructor
capability の exact-projection fast path／shared-skeleton fallback の二経路）—
として表す．`DDSynth.matchAll` は target synthesis・pattern 推論・match-target
alignment の後に matcher 式へ slot expectation（`.slot dual.cap targetTy`）を
demand し，`DDSynth.matcher` は共有 target を確保して全 clause を走査した後，宣言
規則と同一の executable 検査群（`collectClauseEvidence`・`Shape.inferShape`・
`clauseCapsListCheck`・`catchAllLastCheck`・`matcherBindersCheck`・
`armExhaustiveCheck`・`coverageCheck`，terminal hole caps は `terminalHoleCaps`）を
消費して finalize する．`DDSynth.fixMatcher` は非 matcher template の `fix` 規則と
`NonMatcherBody` で排他になる．

solve delta は実行ソルバに言及しない関係的仕様で制約する：**exact MGU**
`ExactCapMGU`／`ExactTargetMGU`／`ExactPairedMGU`（= bare MGU ∧ `SupportWithin`
制約変数＝制約の外では恒等）と，exact one-way 解 `OneWayDelta`（`matchCap` の
制限付き binding substitution＋capability 適用後 target の exact MGU）．bare 形
`CapMGU`／`TargetMGU`／`PairedMGU`（soundness＋全 unifier の因子化＝kernel
certificate と同形）は no-guess 定理と transport 境界の主語として残す．各規則の
出力 substitution は `Subst.seq` による局所 delta の chronological 合成である．

checking cut の分岐は cut-resolved view（`S₁ τraw` と `S₁ τexpected`）上の決定的
classifier `demandClass`（product-matcher lift／slot-tuple lift／matcher-to-slot／
slot-to-slot／ordinary；空 product は matcher-first）で行い，raw view による分岐は
持たない（現行 selector との raw-source visibility 差は `RawSourceVisible` として
段階 3-3 で扱う）．ordinary 等式整合 `DDAlignTypes` は，同 head の matcher／slot 対で
capability を先に解いてから capability 適用後の target を解き，それ以外は resolved 対
の一回の paired solve である．

証明済み：`demandClass_slotDemand`／`demandClass_matcherExpected`（非 ordinary 分岐は
slot 頭の expected を要求する），`DDAlign.slotDemand`／`DDAlign.matcherExpected`
（判断レベルの slot-demand 境界），prevailing replay（`ReplayExtends`＝chronological
delta 列による因子化，pattern 層 family と全整合関係を含む全 judgment），supply 単調性
（`SupplyExtends`，全 judgment；supply twin ごとの単調性補題込み），反射・単一束縛の
MGU witness（`PairedMGU.refl`／`varLeft`／`varRight`，`CapMGU.varLeft`／`varRight`，
`TargetMGU.varLeft`／`varRight` ほか），**no-guess 定理**（MGU 仕様の普遍性だけから：
`image_var_of_fixing_unifier`＝ある unifier が固定する変数は最汎解で必ず変数像を持つ，
`outside_image_var`＝制約外変数は高々リネーム，`outside_injective`＝相異なる制約外
変数は衝突しない — `CapMGU`／`TargetMGU` と `PairedMGU` の両 sort，
`PairedMGU.varConstraint_target_image_var`＝occurs-free な var-vs-type 制約では他の
変数は必ず変数像，対称性 `symm` 三種；補助に変数像からの逆進
`Cap.eq_var_of_apply_var`／`Ty.eq_var_of_applyTarget_var`／`Ty.eq_var_of_apply_var` と
`Ty.applyTarget_eq_of_ftv_agree`），空 binder scheme の instantiation 計算
（`instantiateScheme_noBinder_value`／`instantiateScheme_monoApplySubst_value`），
exact witness（`ExactCapMGU`／`ExactTargetMGU`／`ExactPairedMGU` の
`refl`／`varLeft`／`varRight`／`fnDiagonal`，および解決済み成分対 fresh 変数の
`fnFresh`と共有変数つき `fnSharedFresh`），**freshness 第一層**（供給有界性
`Cap.BoundedBy`／`Ty.BoundedBy`／`Subst.BoundedBy`＝counter 以上で恒等＋像有界，
`SupplyExtends` に沿う単調性，恒等の有界性，有界代入の apply／seq 閉包，exact delta の
`fixedAbove`＝有界制約の bound 以上で恒等；基盤に `Ty.ftv_applyCapability`＝等式・
`Ty.fcv_applyCapability`＝flatMap 等式・`Ty.mem_fcv_applyTarget`＝membership 形）．
像有界性は exactness の条項に採用した（`CapSubst.RangeWithin`／
`TySubst.RangeWithin`／`TySubst.CapRangeWithin` を `Exact*` に追加；paired 仕様の
canonical solver 完全性が未整備のため導出でなく条項）．その上に solve 層の有界性:
`Exact*.boundedBy`（有界制約の exact delta は `Subst.BoundedBy`），
`OneWayDelta.boundedBy`（`matchCapAcc_imagesWithin`＝binding 像は producer 変数内，
mutual・全 12 mismatch 行込み），`DDAlignTypes.boundedBy`／`DDAlign.boundedBy`
（recognizer は `productMatcherDuals?_sound` 系で成分へ分解），dual／dual-list／
target-list／binding／ctor-caps 整列の有界性．

その上で **freshness 不変量は完成**した．(i) evidence 射影の自由変数保存：
`Shape.Leaf.fcv`／`Shape.Evidence.fcv` を新設し，`ofCap` 埋め込みの保存
（`fcv_ofCap`／`fcvList_map_ofCap`）・exact merge（`merge_fcv`／`mergeAll_fcv`）・
finalization（`finalize_fcv` 三形）・shape 推論（`inferShape_fcv`）・certified
projection パイプライン全段（assignment 環境 `assignmentsFcv`／chunk 環境
`chunksFcv` 上の lookup／insert／merge／collect／canonical 集約／result 再構成，
`projectSignature_fcv`／`projectClauseSignature_fcv`）・骨格 evidence の変数自由性
（`ppatSkeletonEvidence_fcv`＝構文由来 skeleton は `fcv = []`，
`matcherSkeletonEvidence_fcv`）・actual clause evidence の hole 変数限定
（`clauseEvidenceGo_fcv`＝evidence と未消費 suffix の双方，`clauseEvidence_fcv`／
`collectClauseEvidence_fcv`）・fallback field demand の assignment 変数限定
（`patternCtorFieldDemands_fcv`）を証明した．(ii) supply-twin の有界性：
`freshTargetsSupply_boundedBy`・`freshenSkeletonSupply_boundedBy`（三 mutual，
`.known` leaf は入力有界性で通し fresh meta は消費区間内）・
`patternCtorAssignmentsSupply_fcv`・`fixMatcherPlaceholderSupply_boundedBy`
（skeleton は変数自由なので前提が退化）・`DDPatternCtorCap.boundedBy`
（exact-projection／shared-skeleton 両経路）．(iii) scheme／context 層：
`Scheme.BoundedBy`／`CtorScheme.BoundedBy`／`DualScheme.BoundedBy`（binder 外
自由変数の有界性）と instantiation の有界性（`instantiateBinders_apply_boundedBy`
＝量化変数は消費区間内・自由変数は元 counter 未満，三 instantiator 共有；
`instantiateScheme_boundedBy`／`instantiateCtorScheme_boundedBy`／
`instantiateDualScheme_boundedBy`），署名閉性 `FrozenSig.SchemesClosed`（frozen
lookup の全 scheme が binder 外自由変数を持たない；閉 scheme は任意 supply で有界），
`Context`／`MonoCtx`／`PatternCtx` の `BoundedBy` と cons／append／find?／
applySubst／toContext 閉包，`FrozenSig.generalize_boundedBy`．(iv) 9-family
sweep：閉署名と有界入力 state から，synthesis は出力 substitution と公開 raw 型，
pattern synthesis は dual と binding context，clause 層は hole ledger を，
すべて出力 supply で有界に返す（`DDSynth.boundedBy` ほか全 judgment，
式自由 family `DDDPat*`／`DDPPat*` 込み）．matcher 規則は terminal hole caps →
`collectClauseEvidence_fcv` → `inferShape_fcv` の連鎖で root capability の有界性を
閉じる．closed wrapper の系は `initialSupply_context_boundedBy`（初期 supply は
自 context を有界化する）と `DDTyping.published_boundedBy`（公開型は initialSupply
を拡張する終端 supply で有界）．
非主張：`HasTy` への忘却（freeze 側対応条件つきの形で段階 3-2；無条件形は
`capFreeze_forgetting_gap` により反証済み），`CoherentExpr` への変換，受理定理
（段階 3-2／3-3）．

### capability origin ledger と origin-aware paired solver

[`TypePM/CapabilityOrigin.lean`](../TypePM/CapabilityOrigin.lean) は capability
metavariable を `rigid`／`renameOnly`／`structuralFlexible` に分ける有限 ledger と，
ledger に対する admissible paired post を定義する．identity と cross-sort-aware な
`Subst.seq` による合成閉性，変数単位／ledger 全体の freeze，freeze 後に既存
`VariablePost` 境界へ入る bridge を証明している．`PhasedPost` は局所 structural post と
frozen residual post を分離し，後者だけを既存 `VariablePost` へ接続する．現段階の
`AdmissiblePost` が制約するのは capability component だけで，target component は
意図的に制約していない．これは constructor／primitive の局所 structural instantiation と
既存 producer の非強化を区別する代数的基礎である．

W の `InferState.capabilityOrigins` はこの ledger を solver policy として保持し，
一般 fresh capability と constructor／primitive image を `structuralFlexible`，context
scheme／pattern-function image と finalized matcher の visible producer を `renameOnly`
と記録する．`capEq`／`targetEq` acceptance は cut-local ledger に従い，legacy
`protectedCaps` は one-way `producerToSlot` と terminal audit の bridge にだけ残る．
この producer-freeze 用 ledger は coercion demand に別証人を要求する仕組みではない．

origin-aware orientation の kernel は
[`TypePM/PairedUnification.lean`](../TypePM/PairedUnification.lean) に機械化済み：
`solvePairedTy` は型構造を再帰しながら capability／target の二 sort を同時に解き，
matcher／slot 注釈は origin-oriented capability solver（`renameOnly` は構造化禁止・
rename 像は非 flexible 限定・`structuralFlexible` は occurs check 下で構造化許可・
未登録は rigid）へ送る．全成功は soundness と `AdmissiblePost` 準拠を運ぶ
proof-carrying certificate（`mguPairedTy_sound`／`mguPairedTy_admissible`）で，
capability／target 両 component の有限 support certificate も返す．二 sort 合成は
`Subst.seq` の閉性による．任意の admissible competitor が結果を吸収する
origin-relative factorization（`mguOrientedCap_universal`／`mguPairedTy_universal`）も
証明済みである．`mguTy` が rigid 比較で拒否する同じ注釈制約を flexible ledger の下で
解く対照回帰（`paired_solves_flexible_annotation`／`symmetric_still_rigid`）つき．
成功の fuel 単調性も `solveCap_success_mono`／`solvePairedTy_success_mono`
（各 list 版含む）として証明し，`mguOrientedCap_of_fuel_le`／`mguPairedTy_of_fuel_le`
が公開 bound 以下の成功を wrapper へ再生できる．この kernel の solvability
completeness と固定 bound の一般的十分性は非主張である．

W の `capEq`／`targetEq` はこの kernel へ接続済みで，各 `SolveStep` は cut-local
ledger snapshot を保持する．constructor／primitive 完了時には raw binder ではなく
prevailing image と exported payload の共通 structural leaf だけを freeze し，明示的
export event を残す．payload は expression result に加え，pattern result
capability／target／bindings，PPat の holes／bindings，DPat bindings まで含む．
`producerToSlot` も exact `CapMatch` substitution の finite support 上で
`admissibleCapPostCheck` を実行し，`solveResolvedWithLedger_admissible` は三 constraint
共通に cut-local `AdmissiblePost` を返す．これにより producer guard の freeze ギャップ
（`packProgram`）は解消した．`nestedCapProgram` の拒否は変えない．

## Unification kernel（対称 MGU）の証明状況

`Unification.lean` の proof-carrying kernel は `universal` field で「返された
substitution を任意の unifier が factor する」ことを構成し，
`mguCapFuel_universal`／`mguTyFuel_universal`（list・spec-level 版含む）が公開定理で
ある．fuel 単調性（成功が任意のより大きい fuel で同じ substitution のまま保存される
こと：`mguCapFuel_mono`／`mguTyFuel_mono` ほか list 版）と ∃fuel solvability
completeness（可解な制約はある fuel で成功すること：`mguCapFuel_complete`／
`mguTyFuel_complete` ほか list 版・可解性 iff 版）も機械化済みである．

branch 選択は fuel に依存しないので，単調性は fuel の直接帰納で fuel 非依存な行は
definitional equality により閉じる（kernel の非重複 match への再構成は不要だった）．
完全性は（残 budget 変数数，構造 weight）の辞書式 well-founded 帰納で，真に不等な
head の解が budget 変数を一つ消去することを kernel 成功 run の range／elimination
certificate（`solveCapPair_varCert`／`solveTyPair_varCert`）が供給する．

公開対称 wrapper は入力の残り変数 budget と構造に従って計算する
`mguCapCompleteFuel`／`mguTyCompleteFuel`（list 版含む）を使い，
`mguCap_complete`／`mguTy_complete`（list 版含む）が可解入力での公開 wrapper の成功を
証明し，`mguCap_isSome_iff_unifiable`／`mguTy_isSome_iff_unifiable`（list 版含む）が
公開成功と可解性を同値にする．旧構造 bound `capFuel`／`tyFuel` は origin-aware paired
kernel の実行にはまだ残り，そちらの fuel 十分性は非主張である．一意性／surface
completeness も open として扱う．

## W の実行不変量（trace-level factorization に向けて）

履歴側の語彙は [`TypePM/InferenceHistory.lean`](../TypePM/InferenceHistory.lean) に既設
（`InferState.HistoryPrefix` の refl／trans／`prevailing_eq`＝prevailing の replay
因子化と，各 traversal の prefix 補題群）．

[`TypePM/InferenceStateExtension.lean`](../TypePM/InferenceStateExtension.lean) は
history prefix，二つの fresh supply の単調性，`protectedCaps` 包含を束ねる強い
`InferState.StateExtension`，refl／trans，record／fresh／protect／instantiate／
export-freeze／単制約成功の extension 補題を持つ．origin ledger は freeze で policy が
変わるため，この global componentwise order には含めない．
[`TypePM/InferenceTraversalStateExtension.lean`](../TypePM/InferenceTraversalStateExtension.lean)
は alignment，freshening，expression／pattern／primitive/data pattern，arm／clause／
matcher の全相互再帰 helper をこの relation へ持ち上げ，最終 `inferRaw_stateExtension`
まで supply／producer 単調性を証明する．

[`TypePM/InferenceAdmissibleTrace.lean`](../TypePM/InferenceAdmissibleTrace.lean) は各
`SolveStep` の delta が保存済み ledger snapshot に admissible である invariant，solver
入力 ledger と snapshot の一致，raw／resolved 単制約実行の保存，history prefix への
制限と admissible suffix による拡張を持つ．
[`TypePM/InferenceTraversalAdmissibleTrace.lean`](../TypePM/InferenceTraversalAdmissibleTrace.lean)
はこれを alignment から expression／pattern／arm／clause／matcher／protected-result
filter まで持ち上げ，初期 empty state に対する `inferRaw_admissibleTrace` を証明する．

[`TypePM/InferenceLocalFactorization.lean`](../TypePM/InferenceLocalFactorization.lean)
は oriented Cap／paired target の relative universality と `CapMatch` の
support-restricted uniqueness を組み合わせ，`solveResolvedWithLedger` の三 branch
すべてに admissible competitor の局所因子化を与える．
[`TypePM/InferenceTraversalLocalFactorization.lean`](../TypePM/InferenceTraversalLocalFactorization.lean)
は各 `SolveStep` が自身の snapshot／resolved constraint／delta に対する
`HasLocalFactorization` を持つ `FactorizingTrace` を定義し，全 mutual traversal と
terminal protected-result filter へ持ち上げ，`inferRaw_factorizingTrace` まで証明する．
[`TypePM/InferenceRunInvariants.lean`](../TypePM/InferenceRunInvariants.lean) の
`inferRaw_runInvariants` は `StateExtension`／`AdmissibleTrace`／`FactorizingTrace` を
raw W 成功時の一つの証明書に束ねる．

[`TypePM/InferenceTraceFactorization.lean`](../TypePM/InferenceTraceFactorization.lean)
は `TraceFactorization` を定義し，prefix residual が次の ledger snapshot に admissible
でその resolved constraint を解くことを明示前提として，局所因子化を snoc／
`recordSolve`／`runResolvedConstraint`／`runConstraint` へ安全に合成する．
[`TypePM/InferenceFreezeTransport.lean`](../TypePM/InferenceFreezeTransport.lean) は
export で選択した leaf の residual 像が更新後 ledger で safe variable rename であると
いう正確な局所条件の下，選択的 `renameOnly` transition 後へ admissibility と scoped
trace factorization を同時に輸送する．現行 `FixesCapVars` はその強い十分条件として
接続済みである．legacy terminal guard はまだ緩めない．残るのは substitution
agreement-on-scope，次の residual の admissibility／solvability，export の safe-rename
条件を mutual traversal 全体で保存する証明である．

terminal validator の受理側では，
[`TypePM/DMTerminalAcceptance.lean`](../TypePM/DMTerminalAcceptance.lean) が多相 `let`
の具体証人 `let id = λx.x in (id id) 1` について，exact raw result への `inferRaw`
成功，`wBridgeCheck = true`，そこからの `WBridgeWF` 構成，結果型 `Int`，公開受理を
一本の nontrivial 境界として固定する．任意の DM raw 成功に対する validator 受理には，
instance／alignment／generalization check を通す trace invariant の一般証明がまだ
必要である．

## 受理ギャップと境界例

- **or pattern（解消済み・正例）**: 両分岐で同名を束縛する
  `matchAll 0 something ($x | $x) x` は，or の整合を raw binding context の構文的
  等価から binder 名の位置照合＋束縛型の単一化（`alignBindings`）へ改めたことで
  受理側になった．certificate 側は `PatternResolutionDeriv.or`／
  `ThreadedPatternResolution.or` を「左右の raw 結果 Δ＋prevailing 像の等価 premise」
  へ緩和した（結論は左の raw Δ・宣言的 `TerminalPatternResolution.or` は不変・忘却
  map は premise で輸送）．
- **nested matcher capability（恒久的境界例・意図された拒否）**: `nestedCapProgram`
  （`(fun f => (f something, f (something,something))) (fun m => m)`）と swapped 版．
  機械化済みなのは，λ 束縛 domain に `sharedSlot` を選び demand の無い位置で coercion
  を使う一つの宣言的 `HasTy` 導出と，公開推論器による拒否である．この対が広い前提の
  `WideAnnotationFree` を恒久反証する（`wideAnnotationFree_refuted`）．全 `HasTy`
  導出が同じ coercion に依存するという inversion は未証明で，将来も回帰の主張に
  含めない．一方 `nestedCapProgram` が `DDTyping` に導出を持たないことは inversion で
  機械化済みである（`nestedCapProgram_no_ddTyping`：最初の function alignment は
  no-guess 定理により fresh domain を高々変数へしか写せないので第一引数の check は
  ordinary alignment に限られ，それが共有 domain を matcher 頭へ固定し，第二引数の
  raw product-of-matchers は matcher 頭の期待に遭遇して `DDAlign` の全分岐が構成子
  衝突で閉じる；任意の published type・任意の最汎 delta 選択に対して成立し，swapped
  版は未）．`let` 多相化した
  `nestedCapLetProgram` は各利用が fresh domain instance を持つため受理される正例で，
  結果が三つの相異なる target 変数を持つ raw shape のままであること
  （`nestedCapLetProgram_raw_target_shape`）と raw solve trace に `producerToSlot` が
  無いこと（`nestedCapLetProgram_raw_has_no_producerToSlot`），さらに `DDTyping` 導出
  （`nestedCapLetProgram_ddTyping`）が同じ raw shape の型
  `prod [Matcher Any ?4, prod [Matcher Any ?8, Matcher Any ?9]]` で閉じることも
  固定する．
- **matcher-expected への product 渡し（恒久的境界例・意図された拒否）**:
  matcher 引数を宣言した署名 ctor や matcher 頭 domain の関数へ product-of-matchers を
  渡す形は，matcher expectation が slot demand でないため lift されず拒否される．
  `CertifiedInferenceRegression` の selector 検査（identity）と負の `#guard` で固定し，
  対応する宣言的 `HasTy` 導出（`ApplicationCoercionRegression` の
  `productMatcherArgumentApplication_surface_typed`）は wide 包絡の意図された受理
  ギャップとして維持する．なお raw `Matcher` を matcher-expected 位置へ渡す形
  （`Pack something` 等）は coercion ではなく通常単一化で従来どおり受理される．
  署名宣言済み matcher field での境界は `packProgram_accepted`（raw matcher・受理）と
  `packPairProgram_rejected`（matcher のタプル・拒否）の対で固定する．
- **capability freeze の忘却側境界（恒久的境界例）**: 量化 matcher producer
  `m : ∀κ α. Matcher κ α` を束縛した文脈上の
  `(λh. (h something, h m)) (λz. z)`．demand-directed 判断は第一利用が共有 domain を
  `Matcher Any ?4` へ固定した後，`m` の fresh instance capability `?κ₁` を ordinary
  matcher-pair の `ExactCapMGU` が `Any` へ構造化して
  `(Matcher Any ?4, Matcher Any ?4)` で閉じる（`capFreezeProgram_ddTyping`；exact
  MGU なので no-guess／exactness は全て遵守）．宣言側は同じ型を導出できない:
  value-flow instance は capability binder を変数へしか写せず（variable-only），
  `m` を matcher 頭で retype できる規則は T-VAR と COERCE-PRODUCT-MATCHER だけで
  前者は cap が変数・後者は cap が prod になり `Any` と構成子衝突する
  （`capFreezeProgram_not_hasTy`）．結合形 `capFreeze_forgetting_gap` が任意文脈の
  無条件忘却を反証し，段階 3-2 の忘却定理が freeze 側対応条件（段階 3-3 の
  `FreezeCompatible` の忘却版）を持つべきことを固定する．
- **capability freeze（受理側・解消済み・正例）**: `packProgram` = `Pack something`
  （`Pack : ∀κ α. Matcher κ α → Packed`）は宣言的には `κ := Any` の instance で
  型付き，推論器も受理する．fresh instance capability は局所 solve 中だけ
  `structuralFlexible`，export 時には prevailing result に生存する image leaf だけを
  `renameOnly` へ freeze する（この例では freeze leaf は空）．raw／public の受理，
  結果型 `Packed`，coherent reconstruction，flexible solve-cut snapshot，dead leaf を
  freeze しない export event，`κ₀ ↦ List κ₁` の生存 leaf `κ₁` だけを freeze して
  後続 strengthening を拒否する回帰，capability を scheme 側で `Any` に固定した
  `packMonoSignature` の control 受理を固定する．

## Runtime safety

runtime matcher value は，生成元の actual clause list と現在の clause cursor を別々に
保持する．suffix cursor は一つの atom dispatch の内部だけで使い，公開 state では
値・captured environment・tree・stack 全体に `Pristine` を要求する．`ValueTy` は
intrinsic capability，target，captured environment，source matcher derivation，coverage
を保持する．matching state の型付けは atom ごとの prevailing substitution，
pattern-function node の隔離された parameter context，残余 actual argument，内部 stack
を追跡する．

runtime の `CapabilityDemand` は，raw `DemandMatches` または検査済み matcher-to-slot
certificate から得られる，正規化済み endpoint compatibility の sound な忘却である．
raw consumer 構文や一つの substitution による共有相関そのものは保持しない．同じ
consumer variable の二度目を wildcard として扱わない strict check は忘却前の
`DemandMatches`／raw certificate が行い，`CapabilityDemand` から exact raw origin を
逆に復元する converse は主張しない．

Ordered dispatch は失敗済み clause prefix を `DispatchTrace` で追跡する．Frozen
signature の pattern-constructor capability 一意性と coverage-index coherence により，
structured pattern が先行する対応 clause をすべて飛ばして bare-hole catch-all へ到達する
不正な branch を排除する．

`CoreSafety` は次を個別に取り出せる形でまとめ，`core_safety` が concrete judgment 上の
証明を与える．

1. pristine な typed environment からの expression evaluation の preservation
2. matching state 一段の preservation
3. matching state の local progress
4. 到達可能な全 state の型付け
5. 成功した terminal match substitution の型付け
6. 上の終端性質としての matcher consistency

各 preservation／reachability／search 結論は，対象の concrete derivation に付随する
`*RuntimeSigAgrees` mirror と，source context に対する `RuntimeSigAgrees` を引数に
取る．任意の runtime signature を無条件に source signature と同一視する主張ではない．
[`TypePM/RuntimeAgreementBridge.lean`](../TypePM/RuntimeAgreementBridge.lean) は，
`∀ context, RuntimeSigAgrees signature context SF` という一つの global agreement から，
任意の concrete `Eval`／`PPM`／`MAtom`／`Step`／`Search`／`Reaches` 導出に対応する
mirror を，その導出の構造に沿って構成する．従って mirror family は実行導出を外部から
与える oracle ではない．

正当な match failure（後続 state が空）は stuck ではない．値パターン式が原子入力の
context で型付くことを表す局所 `CaptureAdm` は，clause の `PPatCoreOrder`，PP typing，
user-pattern typing，成功した `PPM` から `captureAdm_of_coreOrder` が導く．したがって
`OperationalCaptureAdm` のような caller-supplied premise は公開 safety surface にない．
一段の dispatch が必要とする局所評価・decode 結果だけを `StepReady` として progress に
明示し，一般の program termination は仮定しない．この local progress は古典的な
「型付けだけから一段を発見する」定理ではなく，規則ごとの局所的な実行証拠から concrete
`Step` を組み立てる境界である．

動的定理の唯一の global 条件 `FrozenSigWF` は，有限の実行可能検査 `frozenSigWFCheck`
の成功から構成する（`frozenSigWFCheck_sound`，
[`TypePM/SignatureChecker.lean`](../TypePM/SignatureChecker.lean)）．検査は保守的で
fail closed である．canonical な `nil`／`cons` 宣言が `ListSigWF` を witness し，data
constructor は構文的 data root と binder 被覆を検査して（instantiation の一意性は
substitution-agreement の逆補題から従う），pattern constructor は単一パラメータ
collection family（`nil`／`cons`／`join` 型）に限定して capability projection の明示的
inversion から uniqueness と index coherence を導出する．各 pattern constructor には
`constructorsByFormer` の対応 row と `(name, arity)` membership を必須とし，row 欠落は
fail closed で拒否する．この row は保守的 coverage index であり，追加 entry は許すが
coverage obligation を強めるだけである．primitive は canonical scheme との一致を検査
して delta preservation を operation ごと（`append`，`splits`）に一度証明する．関数値
field `armExhaustive = basicArmExhaustive` だけは signature 構成時の定義等式として
受け取る．具体 signature の `signature_wf` は `by decide` で立つ．

## Damas–Milner 断片

[`TypePM/DamasMilner.lean`](../TypePM/DamasMilner.lean) は，pattern を含まない
`λ`/`let`/direct-self `fix` 断片について，独立に定義した一 sort の Damas–Milner 体系
`DM.HasTy` を与える．その再帰規則は core と同じ `self ≠ argument` と
`DirectSelf.Holds self body` を要求し，**この制限体系のすべての導出が閉じた frozen
signature 上の二 sort 宣言体系へ埋め込まれる**こと（`DM.HasTy.emb`）を証明する．
埋め込みの下で capability sort は不活性である：capability binder は空，capability
substitution は自明に作用し（`STy.emb_fcv` = 空），`let` の一般化は二 sort generalizer
と可換（`generalize_emb`）．多相 `let` の証人 `let id = λx.x in (id id) 1` の DM 導出と
その埋め込みも固定する．DM の全型付けが coherent judgment へ入ること
（`Coherent.dm_coherent`）は宣言側の受理準備として証明済みである．逆方向
（conservativity）と一般の algorithmic acceptance（公開 `infer` が全 DM program を
受理すること）はまだ主張しない．

## Principality

[`TypePM/PrincipalityCounterexample.lean`](../TypePM/PrincipalityCounterexample.lean)
は，宣言体系の principality が**そのままの形では偽**であることを機械化された反例で
確定する．閉じた式 `(something, something)` は T-TUPLE で matcher の product 型に，
COERCE-PRODUCT-MATCHER で product matcher 型に型付き，両者の頭構成子（`prod` と
`matcher`）は異なる．tuple 式の導出可能型の頭は `prod`/`matcher`/`slot` に限られ
（`tuple_ty_head`），paired substitution は頭を保存するため，両方を instance に持つ
導出可能型は存在しない（`no_principal_type`）．失敗の原因は coercion の重なりそのもの
（使える product matcher の代価）であり，capability evidence とは独立である．制限
された principality 文はこの重なりを除外する必要がある．coercion を持たない
Damas–Milner 断片は影響を受けない．

一意性は residual substitution が異なる因子化（`α ↦ Slot Any Integer` に `refl`，
`α ↦ Matcher Any Integer` に `matcherToSlot`）を許すため plan kinds だけでは決まら
ない．方針は「∀ typing ∃θ plan の factorization 存在定理」を先に立て，
「substitution が coercible head を導入しない」等の canonical boundary を定義してから
条件付き一意性を扱う（README 段階 3-4）．proof-indexed な derivation property や
`ElaborableHasTy := ∃ CoreTyping` のような循環的定義で代用しない．なお slot-demand
一本化により demand 経路の synthesis は Matcher 終点の plan を生成しなくなるため，
この重なりの一方は demand 側では構造的に消える．

## 回帰一覧

executable regression とその正負境界．削るときは対応する設計判断ごと見直す．

- [`TypePM/CertifiedInferenceRegression.lean`](../TypePM/CertifiedInferenceRegression.lean):
  primitive-pattern pattern の core order を `inferRaw` と公開 `infer` の両方で検査する
  正順 accept／逆順 reject の対，および product-of-matchers／product-of-slots の
  selector 検査と domain-directed application の `#guard`（結果型・terminal alignment
  端点・componentwise coercion を行わない負例・empty-product matcher precedence 込み）．
  matcher-期待側は負例（selector は identity・application `#guard` は拒否）．
- [`TypePM/ApplicationCoercionRegression.lean`](../TypePM/ApplicationCoercionRegression.lean):
  domain-directed application の matcher product／matcher-to-slot／slot-tuple の明示
  surface 導出と，空 product の matcher-first 二段 `NormalPlan`．product-matcher
  application の宣言導出は wide 包絡の意図された受理ギャップ（公開 inference は拒否）．
- [`TypePM/DemandTypingRegression.lean`](../TypePM/DemandTypingRegression.lean):
  demand-directed judgment の具体導出と境界対．solve-free な `λx.x` の synthesis と
  wrapper，domain 整合＋引数 solve を伴う `(λx.x) 1 : Int` の `DDTyping`，多相 `let`
  証人 `let id = λx.x in (id id) 1 : Int` の `DDTyping`（`let` cut での一般化と，
  量化 scheme の supply-indexed な二重 fresh instantiation を行使），
  `(something, something)` を aggregate slot 期待で検査する product-matcher lift の
  正例（lift が両 `something` target を `Int` へ解決することも固定），同じ raw product
  に対する matcher 頭期待の checking cut 不在（`DDAlign` の全分岐反証）．pattern 層の
  旗艦二本：`AcceptanceGapRegression.orProgram` の `DDTyping`（両 or-alternative の
  独立 fresh dual を `DDAlignDual`＋`DDAlignBindings` で整合し，`something` を
  one-way producer-to-slot で slot 期待に合わせて `List Int` で閉じる），delegating
  matcher literal `[$ something [(v → matchAll 0 something $y y)]]` の `DDTyping`
  （hole slot の one-way 充足・arm body の `List Int ≐ List ?0` 整合・executable
  finalization 検査群の消費で `Matcher Any Int` で閉じる；`native_decide` による
  executable 受理 pin つき）．nested-capability 境界対：`nestedCapLetProgram` の
  `DDTyping`（利用ごとの fresh instance・両引数とも変数期待への ordinary demand-free
  solve・実行 raw result shape と同じ型で閉じる）と，`nestedCapProgram` の不在
  inversion `nestedCapProgram_no_ddTyping`（no-guess 定理で第一引数 check の coercion
  分岐を除外し，強制された matcher 頭期待への `prod`／`matcher` 構成子衝突で全分岐を
  閉じる；delta 選択に依存しない）．value-flow transport 境界
  `valueFlow_transport_needs_exactness`：`?1 ≐ Int` の最汎解でありながら無関係な
  `?3`／`?9` を交換する `swappingDelta` は正真の `PairedMGU`（un-swap で全 unifier が
  因子化）で，部分一般化 scheme `∀9. 9 → 3`（`capturedScheme`）の instance
  `Int → ?3` を，capture した `∀9. 9 → 9` の非 instance `Int → ?9` へ写す —
  bare 最汎性では宣言的 value flow が輸送できないことの固定で，判断の exactness
  強化の根拠．capability-freeze 忘却境界（`producerScheme`／`capFreezeProgram`／
  `capFreeze_forgetting_gap`）: 上記「受理ギャップと境界例」の項を参照．
- [`TypePM/ElaborationRegression.lean`](../TypePM/ElaborationRegression.lean): principality
  反例の product 型を canonical root synthesis として固定し，product matcher view を
  明示的 `CoercionPlan` として replay する．`let` を越えた変数利用位置への unary lift の
  宣言的導出つき．
- [`TypePM/AcceptanceGapRegression.lean`](../TypePM/AcceptanceGapRegression.lean):
  or-pattern の宣言的型付け `orProgram_typed` と受理固定（`orProgram_accepted`・異位置
  束縛の `orMixedProgram_accepted`・単一分岐 control）．`nestedCapProgram`／swapped 版の
  宣言的型付けと意図された拒否・同一 producer 二回の control 受理・`let` 多相化の受理
  control 一式・`wideAnnotationFree_refuted`．`packProgram` の受理側一式と
  `packMonoSignature` control．
- [`TypePM/RecursiveExamples.lean`](../TypePM/RecursiveExamples.lean): list／multiset
  direct-self 正例，coverage 不足 multiset 負例（`coverageCheck = false`・
  `¬ CoverageOK`・raw／公開 W 失敗），recursive list matcher を slot に適用して
  `cons $x $rest` の両束縛を body で使う静的な公開 inference 旗艦例（結果型 pin・
  `infer_success_sound` による `HasTy` 再構成・coherent instance
  `listMatcherMatchAll_coherent`；動的実行は非主張），量化 binder と自由 capability の
  番号衝突下での ordered instance／let generalization，非空 pattern-constructor 表への
  非空虚な `FrozenSigWF`（`listSignature_wf`／`multisetSignature_wf`）．
- [`TypePM/ProducerStrengtheningRegression.lean`](../TypePM/ProducerStrengtheningRegression.lean):
  polymorphic producer を公開 `infer` が拒否し，concrete producer の control twin が成功
  する対（成功側は結果型 `Int` pin と `HasTy` 再構成つき）．
- [`TypePM/PatternCtorCapabilityRegression.lean`](../TypePM/PatternCtorCapabilityRegression.lean):
  pattern-constructor capability fallback の exact projection 前後（独立な二 child
  consumer で旧 exact projection が失敗し，fallback 後は同じ fresh `kappa`／
  `List kappa` に zonk されて exact compatibility が成功する），protected-producer
  ledger 不変と全 solver delta の producer 固定，target は整合するが capability rigid
  head が衝突する pctor の公開拒否と capability だけ整合させた control twin の成功対，
  実際の protected child に対する fail-closed な rename-only origin solver
  （legacy symmetric unifier が作れる structural delta の拒否）．
- [`TypePM/DynamicSafetyRegression.lean`](../TypePM/DynamicSafetyRegression.lean):
  `SF = []` の concrete frozen signature と実際の `matchAll` 実行について，
  `FrozenSigWF`・global runtime agreement・評価・PPM・atom reduction・step・search・
  reachability と各 mirror を同時に構成し，`CoreSafety.evalPreservation` を実際に
  適用する end-to-end 例（結果は `List Int` に固定）．
- [`TypePM/DynamicCaptureRegression.lean`](../TypePM/DynamicCaptureRegression.lean):
  合法な `#$captured` clause について `PPM.pval`・`MAtom.matcher`・`Step`・`Search`・
  `Reaches` を具体接続し，`AtomTy.mk` からの初期 state へ
  `CoreSafety.stepPreservation` を適用する（`captureAdm_of_coreOrder` の value-pattern
  分岐が実際の matcher reduction で消費される）．
- [`TypePM/DynamicDispatchRegression.lean`](../TypePM/DynamicDispatchRegression.lean):
  具体的な `cons $x $rest` 実行で先行 `nil` clause の PP mismatch・`cons` clause 先頭
  arm の DP mismatch・次 arm の成功を順に通し，単一 kernel 導出内で
  `MAtom.matcherPPFail`／`matcherDPFail`／二 child の `PPM.ctor`／`MAtom.matcher` を
  発火させ，同じ失敗証拠から `DispatchTrace.nextClause`／`nextArm` も構成する．非再帰
  `Pair α` family の型付き fixture でも同じ三段の private cursor 遷移を発火させ，
  `frozenSigWFCheck`・公開 `infer`・全安全性フィールドの適用まで閉じる．
- [`TypePM/PatternFunctionSafetyRegression.lean`](../TypePM/PatternFunctionSafetyRegression.lean):
  closed nullary pattern function `unit := ptuple []` を非空 signature に置き，
  `∀ context, RuntimeSigAgrees` から必要な mirror を構成して `papp`→`mnode`→terminal
  まで実行し，`CoreSafety` の六フィールドをすべて具体適用する（search と matcher
  consistency には実際の `[] ∈ [[]]`）．非 nullary の
  `pass(parameter : Unit) := embed parameter` について，局所 scheme と固定 lookup
  scheme の value-flow 外延同値と `patfunEnter` step の `of_global` mirror も固定する．
- [`TypePM/DamasMilner.lean`](../TypePM/DamasMilner.lean)／
  [`TypePM/DMTerminalAcceptance.lean`](../TypePM/DMTerminalAcceptance.lean): DM 断片の
  宣言的埋め込みと，多相 `let` 証人の raw／terminal／public 受理境界．
- [`TypePM/PrincipalityCounterexample.lean`](../TypePM/PrincipalityCounterexample.lean):
  `(something, something)` の二重型付けと `no_principal_type`．
- [`TypePM/CoherentSurface.lean`](../TypePM/CoherentSurface.lean)／
  [`TypePM/CoherentTyping.lean`](../TypePM/CoherentTyping.lean): coherent 境界の
  judgment 群・forgetful map・reconstruction bridge・pval-free 吸収・match-free 全
  coherence・`dm_coherent`・反証済み境界命題 `WideAnnotationFree`．
- [`TypePM/ClauseEvidenceExamples.lean`](../TypePM/ClauseEvidenceExamples.lean)／
  [`TypePM/GeneralizationRegression.lean`](../TypePM/GeneralizationRegression.lean)／
  [`TypePM/InferenceRegression.lean`](../TypePM/InferenceRegression.lean): evidence・
  binder collision・W の基本回帰．
