# type-pm-mech — Egison core の型推論と安全性

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．一言でいえば，Egison の
matcher（パターンマッチの「分解の流儀」を第一級の値にしたもの）に静的型を与え，型システムの
古典的な保証 — 注釈なしの型推論が仕様と一致して働くこと（推論の健全性・完全性），推論される型が最も一般的で
あること（主要型），型が付いたプログラムが実行時に型エラーを起こさないこと（型システムの健全性）— が成り立つ
ことを機械検証した．

型の中心は，matcherを生成する型 `Matcher κ τ`（τ 型の値を capability κ の流儀で分解する
matcher）と，matcherを必要とする消費位置の型 `MatcherSlot κ τ` の区別である．producer を
consumer に合わせる coercion（暗黙変換）は，消費側のdemandからだけ決める．

source programの型付け可能性を定義するjudgmentは`SourceTyping`だけである．公開推論器`infer`は，
well-formedなsignatureの下で`SourceTyping`の存在を正確に判定する．closed programについては，
このsource typingから評価とmatching machineの安全性まで接続済みである．

## 現在の到達点

中心となる接続は次の四つである．各行の右側のコメントが一般的な意味である．

```text
infer Σ Γ e = some r                       -- 推論器が型を返したなら
  ── soundness ──→ SourceTyping Σ Γ e r.resolvedTarget      -- その型付けは仕様どおり導出できる

SourceTyping Σ Γ e τ + FrozenSigWF Σ       -- 型が付くprogramは
  ── completeness ──→ (infer Σ Γ e).isSome = true           -- 推論器が必ず受理する

SourceTyping Σ [] e τ + FrozenSigWF Σ      -- closed programの型付けから
  ── state erasure / safety ──→ TypingInvariant Σ [] e τ + CoreSafety   -- 実行時安全性が従う

DM.Typing Γ e τ + FrozenSigWF Σ            -- 従来のDamas–Milnerで型が付くなら
  ── normalized Algorithm W replay ──→ inferenceSucceeds Σ Γ.emb e = true  -- 本推論器も受理する
```

したがって一般contextについて，次の受理同値と決定可能性が得られている．「型が付くこと」と
「推論器が成功すること」が同値なので，型注釈は不要である（annotation freeness）．

```text
FrozenSigWF Σ →
  ((∃ τ, SourceTyping Σ Γ e τ) ↔ (infer Σ Γ e).isSome = true)
```

なお「健全性（soundness）」という語は型システムの文献で二通りに使われるため，本READMEでは
区別して呼ぶ．

- **推論の健全性・完全性**（Damas–MilnerがAlgorithm Wについて言う意味）：アルゴリズム`infer`が
  宣言的仕様`SourceTyping`を正しく実装していること．上の図の一段目・二段目であり，「`infer`の
  受理と`SourceTyping`の存在が一致する」こと**だけ**を言う．実行時の話はまだ含まない．
- **型システムの健全性**（Milnerの “well-typed programs cannot go wrong”，型安全性とも呼ぶ）：
  型が付いたprogramは実行時に型エラーを起こさないこと．上の図の三段目であり，本READMEでは
  「実行時安全性」の節の定理群が担う．

両者を合成すると教科書的な意味の主張になる：`Inference.infer_closed_safe`は「型検査
（`infer`）を通ったclosed programは実行時安全性package（`CoreSafety`）を得る」を直接与える
（progressに残る条件は「実行時安全性」の節を参照）．

主な公開定理は[`TypePM/PublicTheorems.lean`](TypePM/PublicTheorems.lean)から参照できる．
以下，各定理を型システムの標準的な概念に対応させて説明する．

### 型推論の正確さ

「推論器の答えを信じてよい」こと，すなわち推論アルゴリズムが宣言的仕様`SourceTyping`と一致する
ことの二方向である．推論の健全性は誤検出がないこと（返した型付けは仕様どおり導出できる），
推論の完全性は見落としがないこと（仕様上型が付くのに拒否することはない）．両者を合わせると，
型付け可能性はアルゴリズムで決定できる．教科書でいう「型システムの健全性」（実行時エラーの
不在）はこの節ではなく「実行時安全性」の節の内容である．

| 定理 | 意味 |
|---|---|
| `Inference.infer_success_sourceTyping` | 推論の健全性：`infer`が型を返したら，その型の`SourceTyping`導出が必ず存在する |
| `SourceTyping.infer_isSome` | 推論の完全性：型付け可能なprogramを`infer`は必ず受理する |
| `Inference.sourceTypable_iff_infer_isSome` | 受理同値：「型が付く」＝「推論が成功する」．注釈不要性の根拠 |
| `Inference.sourceTypableDecidable` | 決定可能性：型が付くかどうかは計算して判定できる |

### 推論される型の質

MLのprincipal typeと同じ概念である：推論器が返す型は，そのprogramに付きうる型すべてを代入で
カバーする「最も一般的な型」である．さらに型は，残ったmeta変数の名前の付け替えを除いて一意に
決まる．

| 定理 | 意味 |
|---|---|
| `Inference.inferType_principal` | 主要型：返値はそのprogramに付きうる型の中で最も一般的 |
| `Inference.infer_relative_principal` | open termでも，文脈と型を同時に比較する意味で最も一般的 |
| `SourceTyping.target_unique_modulo_renaming` | 一意性：型はresidualな二sort metaのrenamingを除いて一意 |

### 実行時安全性

教科書で「型システムの健全性」（well-typed programs cannot go wrong）と呼ばれる性質に対応する
節である．すなわち「型付けされたprogramの実行は型を裏切らない」：評価が値を返せばその値は
報告された型を持ち（preservation），パターン変数にはmatcherが約束した型の値だけが束縛され
（matching consistency），実行は途中で詰まらない（progress）．progressはfuel付き参照
インタプリタ上の式層の定理として閉じている：型付きclosed programはどのfuelでも
`stuck`（適用できる規則がない状態）に到達しない．fuel切れは「そのfuelでは計算が
完了しなかった」ことを表し，それ自体を発散と同一視しない．adequacyとfuel完全性を
合わせると，全fuelでのfuel切れは「有限の関係的評価導出が存在しない」ことと一致する．
これを別に定義した余帰納的な発散判断と同一視する定理や，一般の停止性は主張しない．

| 定理 | 意味 |
|---|---|
| `SourceTyping.typingInvariant` | state erasure：推論の内部状態（fresh変数の割当・履歴）を消しても型付けの事実は残る．静的な型付けと実行時安全性をつなぐ橋 |
| `SourceTyping.safe` | 型安全性の束：closed programの型付けから，preservation・progress・matching consistencyを含む安全性package（`CoreSafety`）を一括で得る |
| `MStateTy.progress_of_evals` | progress（関係的semantics上の局所形）：typedなmatching状態は，埋め込まれた式の評価が停止する限り必ず一歩進める．デコード成功やディスパッチ先の存在は仮定ではなく型付けから導出される |
| `typed_never_stuck_runtime` | progress（式層の大域形）：source signatureと全contextで整合し，本体の式変数が閉じたruntime pattern-function表について，型付きclosed programはどのfuelでも`stuck`にならない．fuel上のstrong induction（`noStuck_master`）が式・atom・状態・探索・clause dispatch・header照合の全層を束ねる |
| `typed_never_stuck` | 上記の空runtime表への特殊化 |
| `SourceTyping.never_stuck_paper1` | 論文1断片のsource-facingな特殊化：`signature.patternFuns = []`を明示し，`runtimeSigAgrees_nil`で`∀ context, RuntimeSigAgrees signature context []`を導いてno-stuckを得る |
| `evalFuel_ok`／`evalFuel_eventually_ok` | adequacyとfuel完全性：`ok`なら有限の関係的評価導出があり，有限の関係的評価導出があれば十分大きいすべてのfuelで同じ値を返す |
| `typed_all_timeout_iff_no_finite_eval` | 型付きclosed programについて，全fuelでのtimeoutと有限の関係的評価の不在が同値であることを明示する．余帰納的な発散判断との同値ではない |
| `Inference.infer_closed_safe` | 合成：型検査（`infer`）を通ったclosed programは上記の安全性packageを得る．推論の健全性と型システムの健全性をつないだ，教科書的な意味での主張 |

### 既存理論との関係

Damas–MilnerはML/Haskellのlet多相型推論の標準理論である．パターンマッチを使わない断片では
本体系はDamas–Milnerと過不足なく一致する．すなわち既存の型推論の保守的拡張になっている
（DMで型が付くものは受理し，pattern-freeで型が付くものはDMでも型が付く）．

| 定理 | 意味 |
|---|---|
| `DM.sourceTyping_to_dm` | 保守性：pattern-freeなclosed programの型付けは型消去でDamas–Milnerの型付けに落ちる（本体系が勝手に多くを受理してはいない） |
| `DM.Typing.inferenceSucceeds` | DM全受理：Damas–Milnerで型が付く式は本推論器も必ず受理する（勝手に少なく受理してもいない） |

一般のprogram terminationは主張しない．Damas--Milner側の結果はexecutable acceptanceであり，
DM derivationが選ぶtargetと`inferType`返値の構文的一致は主張しない．

### Principality

型 τ が τ′ より一般的（τ ⪯ τ′）とは，代入によって τ から τ′ が得られることをいう．本体系は
capabilityと型の二sortを持つため，この「代入」は両sortを同時に動かすpaired substitutionで
定義する．以下はその形式化である．

`TypeInstance`はsource typeのfree capability／target metaだけを変更できる有限supportのpaired
substitutionでinstance関係を定める．`ScopedTypeInstance`は二つのscopeを明示する．restrictionが
型への作用を保つことと，chronological compositionを元scopeへ再restrictionすることにより，反射性と
推移性を証明済みである．局所二sort renamingは両方向の`TypeInstance`を与える．

`Inference.inferType_principal`は一般contextで次を与え，`inferType_closed_principal`が空contextへの
特殊化を公開する．

```text
FrozenSigWF Σ → inferType Σ [] e = some principal →
  SourceTyping Σ [] e principal ∧
  ∀ target, SourceTyping Σ [] e target → TypeInstance principal target
```

open contextではcontext由来のmetaをすべてrigidにした強い形を採らない．`ContextTargetInstance`は
normalized contextとtargetのfree metaの和を有限scopeとし，同じpaired substitutionを両方へ作用させる．
`SourceTyping.TerminalPair`は第二のsource judgmentではなく，既存のaudited derivationからその終端
substitutionで正規化したcontextと公開targetを取り出すviewである．`Inference.infer_relative_principal`は
成功runの`ResolvedContext`／`resolvedTarget`と，任意の`SourceTyping` derivationのterminal pairが
相互に`ContextTargetInstance`であることを証明する．closed specializationはcontext成分が空なので
`TypeInstance` principalityへ戻る．

### Damas--Milner acceptanceとconservativity

「パターンマッチを使わなければ普通のMLと同じ」ことの形式化である．方向は二つある：DMで型が
付くものは本推論器も受理する（DM全受理），本体系でpattern-freeに型が付くものはDMでも型が付く
（保守性）．

`DamasMilner`はpattern-free expression classifierとcapability-inert type decoderを持ち，埋込みの
像と単射性を証明する．`DamasMilnerAcceptance`は一sort substitutionの合成／restriction，monotype／
contextの一般性，canonical scheme openingのprincipalityとcore instantiationとの一致を証明する．
公開定理`DM.Typing.inferenceSucceeds`は次を与える．

```text
FrozenSigWF Σ → DM.Typing Γ e τ →
  Inference.inferenceSucceeds Σ Γ.emb e = true
```

証明はDM derivationをconstructorごとにAlgorithm Wの監査済みrunへ再生し，公開推論器のterminal
acceptanceへ接続する．結論はacceptanceだけである．DM derivationが選んだ`τ`は推論器のprincipal
targetの特殊化であり得るため，`inferType`の返値と`τ.emb`の構文的一致は主張しない．

逆方向の`DamasMilnerConservativity`では，`eraseTy`が関数・積を一sortへ構造的に写し，基本型を
DMの`Int`へ正規化して，matcher／slot wrapperとcapabilityを消去する．`ContextErases`はcore contextの
各scheme useとDM contextを関係づけ，`SchemeErases.generalize`がclosed signatureの下でlet
generalizationを保存する．`TypingInvariant.toDM`はpattern-free expressionの内部invariantを
DM derivationへ構造的に消去する．公開定理`DM.sourceTyping_to_dm`は次を与える．

```text
FrozenSigWF Σ → InFragmentExpr e → SourceTyping Σ [] e τ →
  ∃ τdm, DM.Typing [] e τdm
```

実際のwitnessは`eraseTy τ`である．必要な`TypingInvariant`は仮定ではなく，
`SourceTyping.typingInvariant`の監査済みclosed state erasureから得る．open contextのconverseは
主張しない．二つの定理を合わせると，指定したclosed fragmentではsourceからDMへの保守的な射影と，
得られたDM derivationの実行可能受理が成立する．型の比較はprincipality層に分離される．

### Source-order依存

同じ部分式の集まりでも，並び順によって受理・拒否が変わることがある．これはバグではなく，
「未解決の型変数から構造を推測しない（no-guess）」原則の帰結として意図した仕様である．

checking cutはその時点のprevailing substitutionを適用したexpected headだけを観測し，未解決変数を
slotへ先読みして構造化しない．listはsource順にstateを渡すため，既知のslot demandが先に現れる
programは受理されても，同じ要素を逆順にしたprogramは拒否され得る．
`AcceptanceGapRegression.source_order_affects_source_typability`はこの差を`SourceTyping`の存在と
非存在の組として固定する．pre-scan，子の並べ替え，checking obligationの遅延，source-order
permutation invarianceは現行仕様に含めない．

将来この境界を変更する場合も通常単一化の失敗をcoercionの根拠に戻してはならず，未解決headの
constraintまたはchecking obligationを遅延する別calculusとして設計する必要がある．それは受理集合を
変えるため，基盤とそのcalculusに依存するメタ定理を再確立する必要がある．

## judgmentの役割

「型付け」に見えるjudgmentが四層あるのは役割が違うからである．受理（どのprogramに型が付くか）
を定義するのは`SourceTyping`だけで，残りは証明をつなぐ内部の中継点である．

| 層 | 役割 |
|---|---|
| `SourceTyping` | source acceptanceを定義する唯一の公開judgment |
| `Reconstruction.ExprDeriv` | 成功した推論traceを再構成するproof-relevantな内部証明 |
| `TypingInvariant` | supply，substitution，origin ledgerを消去した動的メタ理論用の内部invariant |
| `ValueTy`／matching-state judgments | preservation，progress，matching safetyを記述するruntime側の型付け |

向きは`SourceTyping → TypingInvariant → runtime safety`である．`TypingInvariant`を第二のsource
type systemとして使ったり，その存在からsource acceptanceや推論成功を逆向きに導いたりしない．

`SourceTyping`は，canonical initial stateから始まるdemand-directed derivation，capabilityの由来を
追跡するOrigin certificate，終端substitutionで検査するterminal auditを束ねる．`infer`の成功や
`TypingInvariant`の存在を定義のpremiseには持たない．詳細は[`docs/details.md`](docs/details.md)を参照．

## demand-directed coercion

coercionとは，`Matcher`（producer）を`MatcherSlot`要求位置（consumer）へ合わせる暗黙変換で
ある．いつ挿入するかの判断基準は一つしかない：checkingは式を先にsynthesizeし，そのcutで解決した
expected typeのheadを一度だけ調べる．非恒等coercionはexpected headが`MatcherSlot`の場合に
限られる．

| resolved source | resolved expected | alignment |
|---|---|---|
| `Matcher κp τp` | `MatcherSlot κc τc` | matcher-to-slot |
| product of matchers | `MatcherSlot κc τc` | product liftの後にmatcher-to-slot |
| product of slots | `MatcherSlot κc τc` | slot-tuple lift |
| `MatcherSlot κp τp` | `MatcherSlot κc τc` | ordinary equality |
| その他 | その他 | ordinary equality |

expected typeが未解決変数ならordinary equalityだけを行う．coercionのために変数をslotへ推測せず，
ordinary equalityの失敗後に別branchを試すrollbackも行わない．solverはconstraint外のmetaを
構造化せず，capabilityのsubstitutionはOrigin ledgerが許す範囲に限られる．

この原則は`matchAll`専用ではない．たとえば`use : MatcherSlot κ τ → ρ`へ
`m : Matcher κ τ`を渡す場合も，関数適用のargument checking cutで同じalignmentを使う．

## 現在固定している境界

以下は未実装の穴ではなく，意図して固定した言語仕様である（正負の回帰で固定済み）．

- matcher literalはactual clause evidence，shape，catch-all order，data-arm exhaustiveness，
  binder線形性，coverageをすべて要求する．
- value-flow schemeのcapability binderはvariableにだけinstance化し，consumer demandに合わせて
  producer capabilityを後から構造化しない．
- recursionはsingleton direct-selfの単相`fix`だけをcoreに含む．alias，mutual recursion，
  higher-order originはfail closedとする．
- `nestedCapProgram`とswapped版は拒否し，or-pattern，delegating matcher，let-polymorphic matcher
  producerは受理する．これらは正負回帰で固定済みである．
- 未解決lambda domainを複数箇所で共有すると，左から右のchecking順序が受理結果に影響し得る．
  これはno-guessとchronological state threadingから生じる意図された言語境界であり，source
  typabilityの正負定理と実行回帰で固定する．source要素の順序不変性は主張しない．

回帰ごとの対応と内部証明の構成は[`docs/details.md`](docs/details.md)，論文形式の規則とメタ理論は
[`tex/main.tex`](tex/main.tex)に記載する．

## モジュール案内

| 層 | 主なmodule | 役割 |
|---|---|---|
| public index | `PublicTheorems` | 主要な公開定理の入口 |
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| source typing | `DemandTyping*` | raw規則，Origin，terminal audit，soundness／completeness，state erasure |
| inference | `Inference*`, `BridgeChecks`, `CertifiedInference` | raw W，trace，terminal validator |
| principality | `TypeInstance`, `SourcePrincipality`, `RelativePrincipality` | 二sort instance preorder，target principality，context相対principality |
| internal typing | `Source`, `Reconstruction`, `CoherentTyping` | `TypingInvariant`と成功traceの再構成 |
| dynamics | `Semantics`, `Dynamic`, `Preservation`, `Safety`, `Readiness`, `Interpreter`, `Interpreter*Safe`, `InterpreterNoStuck`, `Soundness` | evaluation，matching machine，readiness構成，fuel付き参照インタプリタとadequacy，層別no-stuck定理とfuel上のstrong induction，公開安全性 |
| fragments | `DamasMilner`, `DamasMilnerAcceptance`, `DamasMilnerAcceptanceMutual`, `DamasMilnerConservativity`, `DMTerminalAcceptance` | pattern-free DM断片，canonical opening代数，全DM typingの公開受理，closed sourceからDMへの保守性，受理回帰 |

全moduleのpublic import surfaceは[`TypePM.lean`](TypePM.lean)である．詳細なmodule対応，定理，回帰一覧は
[`docs/details.md`](docs/details.md)を参照．

## 検証

```sh
lake build
cd tex
make
```

形式仕様の出力は`tex/type-pm-mech.pdf`である．`sorry`，`admit`，project-defined `axiom`は使わない．
公開定理が標準3公理（`propext`・`Classical.choice`・`Quot.sound`）のみに依存することは，
[`TypePM/AxiomAudit.lean`](TypePM/AxiomAudit.lean)が`lake build`のたびに検査し，逸脱はビルドエラーになる．
