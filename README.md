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

旧roadmapのmilestone 0--6はすべて完了したため，個別の進捗記録としては残さず，今後の
証明が依存する基盤として次に統合する．この基盤では `SourceTyping` が唯一のsource typingであり，
`TypingInvariant`はstate erasure後の内部invariantであるという役割分担を維持する．

### 完了済みの基盤

| 基盤 | 公開済みの主張 |
|---|---|
| demand-directed typing | 全source formを覆う`SourceTyping`，slot-demand coercion，Origin ledger，terminal auditが定義されている |
| state erasureと安全性 | closed programの`SourceTyping`から同じ型の`TypingInvariant`と`SourceTyping.SafeResult`を得る |
| executable soundness | `infer`が成功して返した型には`SourceTyping` derivationがある |
| acceptance completeness | `FrozenSigWF`の下で`SourceTyping` derivationを持つprogramを`infer`が受理する |
| 受理同値 | 一般contextのsource typabilityと`infer`／`inferType`の成功が同値であり，source typabilityは決定可能である |
| target一意性 | 同じsourceの任意の二つの`SourceTyping` targetは，全residual二sortmetaの局所renamingを法として一意である |

この基盤は今後のmilestoneの前提であり，再実装対象ではない．特にprincipalityは
`TypingInvariant`全体について述べず，必ず`SourceTyping`と公開推論器について述べる．DM断片との
接続でも，`DM.Typing → TypingInvariant`だけをsource acceptanceの代用にしない．

### 新しい依存関係

```text
[x] F. soundness・completeness・受理同値・target一意性
    │
    ├──→ [ ] P1. 二sort instance preorder
    │          └──→ [ ] P2. closed SourceTyping principality
    │                    └──→ [ ] P3. context相対principality
    │
    ├──→ [ ] D1. 全DM.Typingのexecutable acceptance
    │          └──→ [ ] D2. DM断片でのconservativity
    │
    └──→ [ ] O. source-order依存の設計判断
                 ├── 現状を採用 ─→ 安定した言語境界として仕様化
                 └── 規則を変更 ─→ Fと完了済みP／Dを再確立

P2 + D1 ──→ DM derivationの型とinferType返値のinstance関係
P3 + D2 ──→ open DM断片まで含むprincipal typeの一致
```

`P1`--`P3`と`D1`は完了済み基盤から独立に着手できる．ただし`O`でcalculus自体を変更する場合は
受理集合が変わるため，変更後の基盤に対してsoundness，completeness，受理同値，target一意性を
再確立してからprincipalityとDM接続を最終化する．現行の順序依存を採用する場合，`O`は既存の
正負回帰を恒久的な仕様境界として昇格するだけであり，他の枝を差し戻さない．

### [ ] P1. 二sort instance preorderを定義する

capability metavariableとtarget metavariableを同時に扱う型のinstance関係を定義する．単なる
「あるtotal substitutionで写る」ではなく，どの有限scopeを可変とし，その外を恒等に保つかを
明記する．少なくとも反射性と推移性，substitution合成との整合性を証明し，既存の
`TargetRenaming`が両方向のinstanceを与えることを接続する．

open contextでは，exact MGUの向きにより入力context由来のmetaのどちらが公開型へ残るかが変わる．
そのためP1では，closed target用のinstance関係と，contextとtargetを同時に比較する関係を区別する．
「contextを構文的に固定し，そのmetaもrigidとする」強い一般context版を暗黙に採用しない．

達成後に主張できること：

- renaming一意性を「任意の二つの`SourceTyping` targetは互いのinstanceである」と読み替えられる．
- `inferType`の返値と他の公開targetを，metavariable名ではなく一般性の順序で比較できる．
- principalityの定理文を，solver内部のfactorizationを公開せずに定式化できる．

### [ ] P2. closed `SourceTyping` のprincipalityを証明する

P1のinstance preorderを使い，空contextで`inferType`が返すtargetが最も一般的であることを証明する．
第一段階では返値中のresidual metavariableを暗黙に量化したprincipal monotypeとして述べる．必要なら
その後，signature外のresidual metaをcanonical `Scheme`へcloseしたprincipal scheme corollaryを加える．

目標となる主張は次である．

```text
FrozenSigWF signature →
inferType signature [] e = some principal →
SourceTyping signature [] e principal ∧
  ∀ target, SourceTyping signature [] e target →
    TypeInstance principal target
```

達成後に主張できること：

- typableなclosed source programにはprincipal typeが存在する．
- 公開推論器は単に何らかの型を返すだけでなく，`SourceTyping`に関する最も一般的な型を計算する．
- 既存のannotation-freenessを「注釈なしでtypabilityを判定し，principal typeを返す」まで強化できる．

### [ ] P3. context相対principalityを定式化して証明する

P2をopen contextへ拡張する．先に，context中のmetaを固定するのか，contextとtargetを同じsubstitutionで
同時にinstance化するのかを決める．既存のexact-MGU orientation回帰により，入力metaをすべて固定した
まま公開targetだけを比較する強い形は一般には成立しない．したがって有力な定式化は，
`(context, target)`の組に対する同時instance関係，またはcontextのrigid部分を明示した相対関係である．

達成後に主張できること：

- `inferType signature context e`が，明示したcontext可変性の下でprincipalである．
- open termとlibrary contextを含む推論結果の一般性を，MGUの任意の向きに依存せず比較できる．
- closed版P2が空contextへの特殊化として回収される．

### [ ] D1. 全`DM.Typing` derivationのexecutable acceptanceを証明する

現在の`DamasMilner`は，pattern-free・capability-inertなdirect-self DM derivationを
`TypingInvariant`へ埋め込むが，任意の導出に対する公開推論器の受理は未証明である．任意の
`DM.Typing context e target`から，埋込みcontext上で何らかの`SourceTyping` targetが存在することを示し，
完了済みの`SourceTyping.infer_isSome`へ接続する．DM derivationが選んだtargetはprincipal targetの
特殊化であり得るため，公開推論器が同じtargetを構文的に返すとは要求しない．

目標となる受理主張は次の形である．

```text
DM.Typing context e target →
FrozenSigWF signature →
signature.ftv = [] →
(infer signature context.emb e).isSome = true
```

実際のsignature条件は，DM fragmentが参照しないconstructor／primitive tableに不必要な制約を
課さない最小の形に整理する．P1またはP2と合成すると，`inferType`の返値が埋め込んだDM targetより
一般的であることも主張できる．

達成後に主張できること：

- direct-self DMで型付く全programを，terminal validatorを含む公開推論器が受理する．
- 現在のpolymorphic-identity一例だけの`DMTerminalAcceptance`を，一般定理の回帰へ置き換えられる．
- 二sort推論器が通常のpattern-free let-polymorphismを取りこぼさないことを示せる．

### [ ] O. source-order依存を恒久的な言語境界として分類する

未解決lambda domainを複数箇所で共有すると，左から右のchecking順序により受理結果が変わる．現行の
正負回帰は挙動を固定するが，設計として採用したわけではない．次の二案から一つを選ぶ．

1. 現状を採用する．no-guessとchronological state threadingの意図された帰結として仕様化し，
   source permutationでtypabilityが保存されるとは主張しない．
2. 規則を変更する．未解決headに対するconstraintまたはchecking obligationを遅延するなど，coercionの
   根拠を「通常単一化の失敗」に戻さずに，対象とするsource permutationで受理結果を不変にする．

達成後に主張できること：

- 案1では，現在の順序依存が偶然の実装挙動ではなく，明示されたsource typingの境界であると言える．
- 案2では，明示した独立部分式のクラスについて，順序を入れ替えてもtypabilityが変わらないと主張できる．
- どちらの場合も，今後のprincipalityやDM theoremが依存する受理集合を曖昧にしない．

案2はcalculus変更であり，`SourceTyping`，推論器，soundness，completeness，受理同値，target一意性，
形式仕様と全正負回帰を同時に更新する．一般のevaluation順序やprogram terminationまで主張する課題ではない．

### [ ] D2. DM断片に対するconservativityを証明する

まずpattern-free，capability-inert，direct-self recursionという対象構文を明示するfragment predicateを
定義する．D1の`DM.Typing → source typability`に加えて逆向きを証明し，内部`TypingInvariant`ではなく
唯一のsource typingである`SourceTyping`の存在を境界に使う．

目標となる主張は概ね次である．

```text
DMFragment e →
((∃ target, DM.Typing context e target) ↔
  (∃ target, SourceTyping signature context.emb e target))
```

達成後に主張できること：

- 二sort Egison coreは，指定したpattern-free断片ではdirect-self DMの保守的拡張である．
- core側で型付くDM fragmentのprogramには，対応するDM typing derivationが存在する．
- P2／P3と合成すると，公開推論器のprincipal typeとDM側のprincipal typeが，埋込みとinstance関係を
  通じて一致すると主張できる．

一般のprogram terminationは，direct-self `fix`を含む現行coreではこのroadmapの目標にしない．

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
