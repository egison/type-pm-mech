# type-pm-mech — Egison core の型推論と安全性

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．型には matcher を生成する
`Matcher κ τ` と，matcher を必要とする消費位置を表す `MatcherSlot κ τ` がある．

source program の型付け可能性を定義する judgment は `SourceTyping` だけである．実行時安全性の
証明では，推論中の supply や substitution を消去した内部 invariant `TypingInvariant` を使う．
両者の役割は次の一方向に整理する．

```text
SourceTyping + FrozenSigWF.schemesClosed
              │ state erasure
              ▼
         TypingInvariant ──────────────┐
                                    ├─→ SourceTyping.SafeResult ──→ runtime safetyの各性質
FrozenSigWF ── core_safety ─→ CoreSafety
```

`TypingInvariant` は source acceptance を定義する第二の型システムではない．逆に
`TypingInvariant e τ` から `SourceTyping e τ` や推論成功を導くことも意図しない．

## SourceTyping

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
`renameOnly` へfreezeする．matcher literalは，最終capabilityに現れる全demand-owned explicit ledger
keyのstructural leafだけをfreezeする．これにはmatcher開始前に生成された `fixMatcher`
placeholderのowned leafも含まれる．ordinary equalityとone-way matcher-to-slot solveはいずれも，
そのcutの `Ω` に対してadmissibleなdeltaでなければならない．

```text
SourceTyping Σ Γ e τ  iff
  ∃ τraw q' S' Ω',
    initialSupply Σ Γ; id; ∅; Γ ⊢ e ⇒ τraw ⊣ q'; S'; Ω' ∧
    TerminalAudit S' ∧
    τ = S' τraw
```

この定義は `infer` の成功や `TypingInvariant` の存在を前提にしない．

## Synthesis，checking，coercion

`DemandCheck` は式を一度 synthesize し，その直後の cut で expected type と一度だけ align する．
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
matcher 引数と matcher clause の next-matcher も同じ `DemandCheck` を使う．

## TypingInvariant と安全性

[`TypePM/Source.lean`](TypePM/Source.lean) の `TypingInvariant` は，fresh supply，solver の実行順，
origin ledger を持たない state-free invariant である．closure と matcher value はその証明を保持し，
preservation はそれを `ValueTy` へ移す．
matcher-to-slot coercion も実行器の matching／MGU 成功証拠を保持せず，終端 capability 間の
`CapabilityDemand` だけを保持する．slot-to-slot solve は終端型の等しさへ消去される．実行用の
raw solver certificate は reconstruction がこの意味的証拠へ射影するまでの境界にだけ残る．

実行可能推論については次の経路が機械化済みである．

```text
infer Σ Γ e = some r
  → Reconstruction.ExprDeriv Σ (ResolvedContext r.state.prevailing Γ)
      e r.resolvedTarget
  → TypingInvariant Σ (ResolvedContext r.state.prevailing Γ)
      e r.resolvedTarget
```

中心となる定理は `infer_success_reconstruct` と `infer_success_typingInvariant` である．公開
`infer` は停止する `inferRaw` と有限の fail-closed terminal validator の合成であり，caller
が bridge certificate や `InferenceInputWF` を渡す必要はない．

`FrozenSigWF` の下では，`TypingInvariant` を持つ式の評価，matching state の一段保存，局所
progress，到達可能 state の保存，成功 branch の substitution typing を証明済みである．
`FrozenSigWF` はこれらの動的整合性に加えて，signature中の全schemeがbinder外の
metavariableを持たない `SchemesClosed` を含む．実行可能checker `frozenSigWFCheck` の成功から
`frozenSigWFCheck_sound` が，signature構築時に固定する
`armExhaustive = basicArmExhaustive` と合わせてこの単一のglobal条件を構成する．一般の program
termination は主張しない．

## 接続の現在地

`SourceTyping → TypingInvariant` の state erasure は完成している．public `SourceTyping` は
canonical initial supply，恒等置換，空 ledger から始まる raw derivation，構造が対応する
Origin certificate，終端 substitution での audit certificateを保持する．全 raw demand-directed
family で出力 substitution の idempotence を保存することと，各子の出力から根の終端までの
chronological factorization を使い，全14 family の相互 erasure から closed-program の
`TypingInvariant` を得る．`TypingInvariant` 自体の存在を `SourceTyping` の premise に置く循環はない．

`infer → SourceTyping` の executable soundness は完成している．公開定理
`Inference.infer_success_sourceTyping` は，成功した fuelled traversal を同じ cut 列を持つ raw demand-directed
derivationへ相互再構成し，validator が与える一つの終端 certificate から terminal audit を構成して，
報告された `resolvedTarget` の `SourceTyping` を返す．caller が `WBridgeWF` や history を渡す必要はない．

`SourceTyping` からの公開動的安全性も完成している．低レベルの `SourceTyping.typingInvariant` は
signature closednessを明示的に受け取るが，公開定理 `SourceTyping.safe` は
`FrozenSigWF.schemesClosed`からその証拠を内部で供給する．したがってclosed programについて

```text
SourceTyping signature [] e τ →
FrozenSigWF signature →
SourceTyping.SafeResult signature e τ SF
```

が成立する．`SourceTyping.SafeResult` は同じ公開型の `TypingInvariant` と，preservation／progress／
matching safetyを束ねた `CoreSafety` を保持する．`Inference.infer_closed_safe` はclosedな推論成功を
`infer → SourceTyping → safety` の公開経路へ接続する．

`SourceTyping → infer` の受理完全性も完成している．`SourceTyping` derivation と terminal audit を同時に再帰し，
exact solve，fresh allocation，context normalization，producer protectionを同じ executable traversalへ
再現する．各局所runが蓄積するvalidator event coverageをrootでterminal auditと合成し，有限の
`wBridgeCheck`を通す．公開定理はM4と同じglobal signature条件だけを受け取る．

```text
SourceTyping.infer_isSome :
  SourceTyping signature context e τ →
  FrozenSigWF signature →
  (infer signature context e).isSome = true
```

`RawSourceVisible`，`FreezeCompatible`，solver success，validator bridgeなどの実装向け条件は
caller premiseに残らない．`FrozenSigWF`はterminal factsを実行側の終端stateへ輸送する際の
scheme closednessとcanonical arm checkerを含み，M4とM5で共有する公開signature境界である．

以上の二方向を合成した受理同値も完成している．一般contextでは
`Inference.sourceTypable_iff_infer_isSome`，closed programでは
`Inference.annotation_freeness`として，`FrozenSigWF`の下で「ある型について `SourceTyping` が成立する」ことと
公開推論器の成功が同値になる．`inferType_success_sourceTyping`は`inferType`が実際に返した型の
`SourceTyping` derivationを与え，`sourceTypableDecidable`は同じ同値からsource typabilityの決定可能性を構成する．
任意に与えた`SourceTyping` derivationのtargetと返値型の構文的一致は一般には成立しないが，両者を含む任意の
二つの`SourceTyping` targetは，全residual metavariable上の局所的な二sort変数renamingにより同じ決定的な
実行targetへ写る．型のinstance preorder上のprincipalityはまだ主張しない．

`nestedCapProgram` と swapped 版は demand-directed で型付かず，推論器も拒否する意図された負例である．
一方，or-pattern，delegating matcher，let-polymorphic な matcher producer は維持すべき正例で
あり，public Origin certificate を伴う回帰で固定済みである．

未解決なlambda domainを共有する二つのuseはsource順序を観測しうる．`use`が先にdomainをslotへ
確定するclosed probeは受理され，raw matcherを渡す通常適用を先に置いた逆順は拒否される．これは
左から右のstate threadingとno-guess原則の現行帰結として正負回帰に固定するが，恒久的な言語境界
としてはまだ分類しない．

## Roadmap

roadmap は次の依存関係に従う．`TypingInvariant` を source typing に戻したり，その derivation の
存在を `SourceTyping` の premise に加えたりせず，`SourceTyping` derivation 自身が安全性と実行可能推論への
接続に必要な情報を持つ形を完成させる．

```text
[x] 1. freeze provenance と public 回帰
        │
        ▼
[x] 2. demand-directed state erasure ─────────→ [x] 4. SourceTyping の公開安全性

[x] 3. infer success → SourceTyping ─┐
                                 ├→ [x] 6. 受理同値と注釈不要性
[x] 5. SourceTyping → infer success ─┘
```

記号は `[x]` が完了，`[~]` が一部完了，`[ ]` が未完了を表す．

### 進捗サマリ

全7 milestoneを完了している．

| milestone | 状態 | 完了した中心部分 | 残る中心部分 |
|---|---|---|---|
| 0. 基盤 | 完了 | demand-directed判断，exact solve，typing invariant，既存動的安全性 | なし |
| 1. freeze provenance | 完了 | Origin ledger，public正例／負例回帰 | なし |
| 2. demand-directed state erasure | 完了 | canonical `Scheme`，全14 familyのfactorizationとidempotence，terminal audit，固定終端への相互erasure，closed-program公開定理 | なし |
| 3. infer success → SourceTyping | 完了 | 全 traversal family の exact-state 相互再構成，terminal audit，public中心定理と回帰 | なし |
| 4. SourceTypingの公開安全性 | 完了 | `FrozenSigWF`へのclosedness統合，`SourceTyping.safe`，closed inferenceからの公開安全性経路 | なし |
| 5. SourceTyping → infer success | 完了 | 全構文familyのaudited traversal完全性，validator event coverage，public `SourceTyping.infer_isSome` | なし |
| 6. 受理同値 | 完了 | 一般contextの受理同値，closed annotation-freeness，`inferType`返値soundness，source typabilityのdecidability | なし |

roadmapの中心定理はすべて公開APIまで接続済みである．さらに`SourceTyping` target一意性を，二つの公開型が
全residual capability／target metavariable上の局所renamingにより一つの共通実行targetへ写る形で
機械化済みである．initial supplyに既に存在する変数まで固定する強い形は一般contextでは偽であり，
二つのexact MGU orientationがそれぞれ異なる入力metaを公開する完全なdemand-directed回帰で境界を固定した．
今後principalityを扱う場合は，この一意性を基礎に型のinstance preorderを別途導入する．

`infer` 成功から `TypingInvariant` を再構成する既存定理は，引き続き内部 invariant への
独立した経路である．新しい source-facing 経路はまず `SourceTyping` を直接再構成する．一般 context
で両者を無条件に合成したとは主張せず，closed-program の `SourceTyping → TypingInvariant` は
milestone 2の定理を用いる．

### [x] 0. 現在の基盤

次は完成済みの出発点であり，後続 milestone で維持する不変量である．

- 全 expression／pattern／arm／clause form に `DemandSynth`／`DemandCheck` family がある．
- checking は synthesis 後の一 cut で一度だけ alignment を行う．
- 非恒等 coercion は slot-headed expected type に限られる．
- exact MGU，state replay，supply extension，boundedness が証明されている．
- `infer` の成功から reconstruction と `TypingInvariant` を構成できる．
- `TypingInvariant`，`ValueTy`，matching-state judgment 上の動的安全性が証明されている．

### [x] 1. Capability freeze provenance の public 回帰を完成する

core 実装は完了している．全 demand-directed family の raw derivation に構造を一致させた intrinsic Origin
certificateがあり，`q; S; Ω` を状態として追跡する．scheme／dual instance は binder imageを
`renameOnly`，constructor instanceとfresh consumerは `structuralFlexible` とし，exportとmatcher
finalizationは外へ残るstructural leafだけを選択的にfreezeする．ordinary equalityとone-way solveは
cutのledgerに対してadmissibleなdeltaだけを受理する．`let` certificateは終端 substitution 後にも
同じgeneralization schemeが得られる安定性を要求する．public wrapperも空ledgerから始める．

originを追跡しない局所導出で現れた反例は，public `SourceTyping` 全体の導出不能性まで閉じた
negative regressionとして固定されている．

完了条件：

- [x] ledger の extension，freeze，substitution replay に関する基本補題が全 demand-directed family で成り立つ
  （基本的な supply-scoped ledger 補題と transition 補題は実装済み）．
- [x] `capFreezeProgram` と `letCapFreezeProgram` が public `SourceTyping` では導出不能であることを証明する
  （問題となる局所導出，ledger-aware solveによる拒否，program全体のnegative regressionを実装済み）．
- [x] or-pattern，delegating matcher，let-polymorphic producer など既存の正例について public Origin
  certificate を構成する（実装済み）．
- [x] `nestedCapProgram`，matcher-expected product application など既存の負例は導出不能なままである．
- [x] public `SourceTyping` は canonical initial ledger から開始し，外部の freeze premise を要求しない．

### [x] 2. demand-directed state erasure を証明する

ledger-aware な demand-directed derivation から supply，prevailing substitution，origin ledger を消去し，
`TypingInvariant` proof を構成する相互証明は完了している．expression だけでなく，
expression list，checking，user／primitive／data pattern，arm，clause を含む全 family を
同じ根の終端 substitution へ射影する．

完了した構成は次のとおりである．

- [x] 全14 demand-directed familyの無前提 `StateFactorization` を構成する．
- [x] checking alignment全5分岐を終端 `InvariantAlignment` へ射影する．
- [x] solver metavariableとscheme bound variableを別datatypeにしたcanonical `Scheme`へ移行し，
  binder名，mask，`NoCapture` 条件を source scheme から除去する．
- [x] finiteなbound indexのopening，fresh allocation，generalization，substitution合成，
  variable value-flow transportを構成する．
- [x] exact solveがidempotentな入力 substitutionからidempotentな出力を作ることを，
  alignment familyとraw demand-directed全14 familyで証明する．
- [x] derivationと同じ形のterminal-audit treeを構成し，`let` generalization，
  matcher finalization，pattern-constructor compatibilityを根の終端 substitutionで固定する．
- [x] chronological factorizationとidempotenceを各子へ渡す固定終端の相互erasureを構成する．
- [x] closed signatureについて
  `SourceTyping.typingInvariant`，すなわち
  `SourceTyping signature [] e τ → TypingInvariant signature [] e τ` を公開定理として閉じる．

<details>
<summary>state erasureの設計</summary>

schemeのbound variableは有限なbound index，推論器のmetavariableは `CapVar`／`TyVar` であり，
構文レベルで異なる．ambient substitutionはbound occurrenceを生成できないため，旧来の
binder-name衝突，mask，`NoCapture` 保存条件は不要になった．generalizationは選んだmetavariableを
直ちにcanonical schemeへcloseし，instance生成はcaller-suppliedなfinite openingで行う．

消去証明は「任意の将来 suffix に対して各nodeが安定する」とは仮定しない．その主張は
`let` のgeneralized setが後続solveで変わり得るため強すぎる．代わりに公開 `SourceTyping` は，
raw derivationとOrigin certificateに加え，同じ木構造を持つterminal auditを公開終端
substitutionに対して保持する．auditは局所suffixで一般には保存されない三種類の事実を記録する：

- `let` が終端contextと終端value typeから同じschemeをgeneralizeすること．
- matcherの終端capabilityに対してshape，clause capability，exhaustiveness，coverageが成立すること．
- pattern constructorの引数capabilityと結果capabilityが終端でcompatibleであること．

各raw demand-directed familyはexact solveのidempotenceを保存する．また，各子の出力状態から根の終端状態への
`StateFactorization` がchronological substitutionを与える．相互erasureはこのfactorizationと
idempotenceを再帰的に渡し，variable opening，checking alignment，`let`，matcher／clause，
pattern constructorを含む各constructorを終端の `TypingInvariant` familyへ射影する．terminal
auditは `TypingInvariant` の存在を保持するoracleではなく，solverを含まない有限な代数的・
検査可能事実だけを保持する．

</details>

一般の内部定理は入力contextへ根の終端 substitutionを適用した `TypingInvariant` を構成する．
canonical initial stateと空contextに特殊化すると，公開した型をそのまま持つclosed-program
corollaryが得られる．これによりMilestone 2は，型付けderivationをpremiseに持つoracleや
blanketなcapability transportを追加せず完了した．

### [x] 3. 実行可能推論の demand-directed soundness を証明する

public `infer` の成功を唯一の前提として，報告された型の `SourceTyping` を再構成する定理は完成している．

```text
infer Σ Γ e = some r
  → exact-state mutual demand-directed reconstruction
  → terminal-audited certified run
  → SourceTyping Σ Γ e r.resolvedTarget
```

証明は三層に分けている．まず solver と checking alignment の成功を exact demand-directed transitionへ写し，
expression，pattern，arm，clauseを含む traversal 10 familyを fuel に関して相互再構成する．次に
append-only historyにより全 recursive callを同じroot終端へ接続し，validatorの `WBridgeWF` から
局所suffixでは保存されない `let`，matcher，pattern constructorの三事実だけをterminal auditへ
載せる．最後にcanonical initial stateのcertified runをpublic `SourceTyping`へ射影する．

中心定理は次である．

```text
Inference.infer_success_sourceTyping :
  infer signature context expression = some result →
  SourceTyping signature context expression result.resolvedTarget
```

`WBridgeWF` と `HistoryPrefix` は証明内部でのみ用いる．callerに追加のwell-formedness premiseや
typing certificateを要求しない．`fixMatcher`のsupply-indexed skeleton，`letE`の終端
generalization，matcher finalization，pattern constructor，`matchAll`を含む全分岐を同じ相互定理で
閉じ，terminal `let` とrecursive matcherをpublic APIの回帰で固定している．

#### 完了条件

中心定理：

```text
infer signature context e = some result →
  SourceTyping signature context e result.resolvedTarget
```

これにより，公開推論器の成功は唯一の source typing に対して sound である，という通常の API を
得る．空contextへ特殊化した場合は，`FrozenSigWF`が供給するclosednessの下でこの定理と
milestone 2を`Inference.infer_closed_safe`として合成できる．一般contextの
`infer_success_typingInvariant` は既存の独立したreconstruction経路を使う．

### [x] 4. SourceTyping から公開動的安全性を導く

`FrozenSigWF` に `SchemesClosed` を統合し，milestone 2のstate erasureが必要とするclosednessを
単一のglobal signature条件から取得する．実行可能checker `frozenSigWFCheck` は全signature
schemeのclosednessも有限に検査し，成功時に完全な `FrozenSigWF` を構成する．
function-valuedな`armExhaustive` fieldだけは，signature構築時の定義的等式をchecker soundnessへ渡す．

公開定理は次の形で完成している．

```text
SourceTyping signature [] e τ →
FrozenSigWF signature →
SourceTyping.SafeResult signature e τ SF
```

`SourceTyping.safe` は同じ型の内部 `TypingInvariant` と `CoreSafety` を返すため，expression evaluationと
matching machineの既存定理をこの入口から利用できる．`Inference.SafeResult` は推論成功から得た
source `SourceTyping` も保持し，`Inference.infer_closed_safe` はclosed inferenceを同じ`SourceTyping`入口へ通す．

### [x] 5. SourceTyping に対する推論器の受理完全性を証明する

`SourceTyping` derivationのOrigin treeとterminal auditを同時に左から右へ読み，対応する
fuelled traversalの成功を全expression，checking，pattern，arm，clause familyに対して再構成する．
demand-directedのexact solve witnessとexecutable solver resultはmutual factorizationで対応させ，
`StateBisimulation`，context normalization，supply boundednessをrecursive callの間で保存する．

各constructorは成功runに加えてordinary validator eventと三種のterminal-sensitive eventの
coverage extensionを返す．pattern constructorではdemand-directed導出が記録するdual／capabilityと実行trace中の
operandsを同一視せず，その間のbisimulationをpaired witnessとして保持する．rootでそれらを
`PairedRootCertifiedSynthesis`に束ね，pattern-constructor compatibilityはpaired witnessから直接，
`let` generalizationとmatcher finalizationもそれぞれのdemand-directed／実行operandを結ぶpaired witnessから，
producer protection，type／dual alignmentと合わせて`wBridgeCheck`の全条件へ射影する．
exact-state leafはこのpaired chronologyの対角な特別場合として埋め込む．Originとauditは`Prop`，
concrete runは`Type`に属するため，fuelに対するstrong recursionは各cutのpaired runを`Nonempty`で
返す．canonical initial cutで`PairedRootCertifiedSynthesis`へ束ね，公開facadeが受理命題の内部でだけ
その証明消去境界を開く．

中心定理：

```text
SourceTyping.infer_isSome :
  SourceTyping signature context e τ →
  FrozenSigWF signature →
  (infer signature context e).isSome = true
```

公開premiseはsource derivationとM4でも使う`FrozenSigWF`だけである．
`RawSourceVisible`，`FreezeCompatible`，solver success，caller-supplied bridge，既知のinference
successは残さない．これはvalidator単体が任意のraw runを受理するという無条件完全性ではなく，
terminal-audited `SourceTyping` fragmentから生成したtraceに対する相対的な完全性である．
recursive list matcher，multiset matcher，pattern constructorを含む`matchAll`の三例は，caller-supplied
paired rootなしでこの公開定理へ到達する回帰として固定している．

### [x] 6. 受理同値と注釈不要性を公開する

milestone 3 と 5 を合成し，一般contextについてsource typabilityと公開推論器の成功を
対応付ける．closed program版をannotation-freenessとして公開する．

```text
FrozenSigWF signature →
  ((∃ τ, SourceTyping signature context e τ) ↔
    (infer signature context e).isSome = true)
```

`Inference.annotation_freeness`は`context = []`に特殊化した公開名である．さらに
`Inference.inferType_success_sourceTyping`は

```text
inferType signature context e = some τ →
  SourceTyping signature context e τ
```

を与える．完全性側では，元の`SourceTyping` targetとの構文的一致を要求せず，`inferType`が返す何らかの型と
その型自身の`SourceTyping` derivationを同時に得る．`Inference.sourceTypableDecidable`は`FrozenSigWF`の証明を
受け取り，有限な公開推論を使って`∃ τ, SourceTyping ... τ`の`Decidable`を返す．

これに加え，`SourceTyping.target_unique_modulo_renaming`は同じsignature／context／expressionを持つ
任意の二導出のtargetを，同じ決定的な実行targetへの局所的な二sort変数renamingで結ぶ．open
contextでは入力metaの向きもexact MGUが選択しうるため，renaming scopeはinitial supply以後だけで
なく公開型に残る全metaを含む．従って構文的一致ではないが，closed programを含め
`inferType`の返値をrenaming同値類の決定的な代表として使える．型のinstance preorder上の
principalityは別課題であり，`TypingInvariant`全体のprincipality反例をSourceTypingへ流用しない．

## 機械化済みの主な性質

- `DemandCheck` の非恒等 branch は slot-headed expected type に限られる．
- matcher-headed expected type では ordinary equality しか起こらない．
- demand-directed family の supply は単調に進み，substitution は chronological delta replay に分解できる．
- exact solveと全14 raw demand-directed familyは substitution のidempotenceを保存する．
- demand-directed が公開する型，pattern dual，bindings，hole ledger は終端 supply で有界である．
- exact MGU は constraint 外の metavariable を推測しない．
- matcher literal は shape，catch-all order，data-arm exhaustiveness，binder 線形性，coverage
  evidence をすべて要求する．
- `infer signature context expression = some result` から
  `SourceTyping signature context expression result.resolvedTarget` を導く．
- `FrozenSigWF`の下で，ある型に対する`SourceTyping`の存在と`infer`／`inferType`の成功が同値である．
- `inferType`が返した型には`SourceTyping`導出があり，source typabilityは決定可能である．
- 同じsourceの任意の二つの`SourceTyping` targetは，全residual二sort metavariableの
  局所renamingを法として一意である．
- closed signature上で `SourceTyping signature [] e τ` から `TypingInvariant signature [] e τ` を導く．
- `FrozenSigWF` は全signature schemeのclosednessを含み，実行可能checkerがこの条件も検査する．
- `SourceTyping signature [] e τ` と `FrozenSigWF signature` から，同じ型の内部invariantと
  concrete safetyを束ねた `SourceTyping.SafeResult` を導く．
- `infer` の成功から reconstruction certificate と `TypingInvariant` を再構成できる．
- `FrozenSigWF` の下で concrete evaluation と matching machine の安全性が成り立つ．
- `sorry`，`admit`，project-defined `axiom` はない．

## モジュール案内

| 層 | 主な module | 役割 |
|---|---|---|
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| source typing | `DemandTyping`, `DemandTypingOrigin`, `DemandTypingInferenceSoundness*`, `DemandTypingErasure`, `DemandTypingRegression*` | demand-directed raw規則，intrinsic Origin certificate，推論成功からpublic `SourceTyping`への再構成，state erasureと回帰 |
| typing invariant | `Source`, `Reconstruction`, `CoherentSurface`, `CoherentTyping` | state-free invariant と再構成 |
| inference | `Inference*`, `BridgeChecks`, `CertifiedInference` | raw W，origin ledger，validator，成功時の再構成 |
| dynamics | `Semantics`, `Dynamic`, `Preservation`, `Safety`, `Soundness` | evaluation，matching machine，`SourceTyping.safe`による公開安全性入口 |
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
