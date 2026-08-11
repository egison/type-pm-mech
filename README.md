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
     │ state erasure      未完成：capability freeze 情報の統合が必要
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
q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'       DDSynth
q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'  DDCheck
```

`q = (qκ, qτ)` は capability metavariable と target metavariable の次の番号を持つ fresh
supply，`S` はその cut までに得た paired substitution である．各規則は子を左から右へ調べ，
出力 `q'; S'` を次の子へ渡す．公開 wrapper は canonical initial supply と恒等置換から始め，
最後に `S' τraw` を公開する．

```text
DDTyping Σ Γ e τ  iff
  ∃ τraw q' S',
    DDSynth Σ (initialSupply Σ Γ) id Γ e τraw q' S' ∧
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
exact MGU または exact one-way solution であり，constraint 外の metavariable を構造化しない．

coercion の場所は `matchAll` や matcher literal に固定されない．たとえば
`use : MatcherSlot κ τ → ρ` へ `m : Matcher κ τ` を渡す場合，関数適用が domain を決め，
引数の checking cut で matcher producer と slot demand が対応付けられる．`matchAll` の
matcher 引数と matcher clause の next-matcher も同じ `DDCheck` を使う．

## RuntimeTyping と安全性

[`TypePM/Source.lean`](TypePM/Source.lean) の `RuntimeTyping` は，fresh supply，solver の実行順，
origin ledger を持たない state-free certificate である．closure と matcher value はこの
certificate を保持し，preservation はそれを `ValueTy` へ移す．

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

現在の主な未完成部分は二つである．

1. `DDTyping → RuntimeTyping` の state erasure
2. `DDTyping → infer` の受理完全性

一つ目には capability origin の freeze 情報が必要である．現行 `DDSynth` は `q` と `S` を
持つが origin ledger を持たないため，量化された matcher producer の capability を後続 solve
が構造化したことを derivation だけから排除できない．`capFreezeProgram` と
`letCapFreezeProgram` はこの不足を固定する回帰である．解決方針は，producer capability の
生成・instance・一般化・export に必要な freeze provenance を DD family 自体へ統合し，その
情報を用いて `RuntimeTyping` へ射影することである．`RuntimeTyping` の存在を `DDTyping` の
premise に埋め込む循環的な定義は採らない．

二つ目には，上記 freeze 統合に加え，現行 executable selector が product source の認識に
raw type を使う箇所を cut-resolved view と一致させる必要がある．最終目標は追加 premise の
ない次の定理である．

```text
DDTyping signature [] e τ →
  (infer signature [] e).isSome
```

`nestedCapProgram` と swapped 版は DD で型付かず，推論器も拒否する意図された負例である．
一方，or-pattern，delegating matcher，let-polymorphic な matcher producer は DD の正例である．

## Roadmap

roadmap は次の依存関係に従う．`RuntimeTyping` を source typing に戻したり，その derivation の
存在を `DDTyping` の premise に加えたりせず，DD derivation 自身が安全性と実行可能推論への
接続に必要な情報を持つ形を完成させる．

```text
現在の DDTyping／infer／runtime safety
              │
              ▼
1. freeze provenance を DD family へ統合
              │
        ┌─────┴──────────┐
        ▼                ▼
2. DD state erasure   3. infer success → DDTyping
        │                │
        ▼                ▼
4. DD の公開安全性    5. DDTyping → infer success
                         │
                         ▼
                    6. 受理同値と注釈不要性
```

### 0. 現在の基盤

次は完成済みの出発点であり，後続 milestone で維持する不変量である．

- 全 expression／pattern／arm／clause form に `DDSynth`／`DDCheck` family がある．
- checking は synthesis 後の一 cut で一度だけ alignment を行う．
- 非恒等 coercion は slot-headed expected type に限られる．
- exact MGU，state replay，supply extension，boundedness が証明されている．
- `infer` の成功から reconstruction と `RuntimeTyping` を構成できる．
- `RuntimeTyping`，`ValueTy`，matching-state judgment 上の動的安全性が証明されている．

### 1. Capability freeze provenance を DD family へ統合する

`q; S` に加えて capability-origin ledger を DD family の入出力 state に持たせる．fresh
capability の生成理由を `rigid`／`renameOnly`／`structuralFlexible` として記録し，scheme
instance，`let` generalization，producer export で必要な freeze transition を規則に含める．
`DDAlign` の ordinary solve と one-way solve は，その cut の ledger に対して admissible な
delta だけを受け入れる．

完了条件：

- ledger の extension，freeze，substitution replay に関する基本補題が全 DD family で成り立つ．
- `capFreezeProgram` と `letCapFreezeProgram` は新しい `DDTyping` では導出不能になる．
- or-pattern，delegating matcher，let-polymorphic producer など既存の正例は導出可能なままである．
- `nestedCapProgram`，matcher-expected product application など既存の負例は導出不能なままである．
- public `DDTyping` は canonical initial ledger から開始し，外部の freeze premise を要求しない．

### 2. DD state erasure を証明する

ledger-aware な DD derivation から，supply，prevailing substitution，origin ledger を消去して
`RuntimeTyping` certificate を構成する．expression だけを個別に処理せず，expression list，
user pattern，primitive pattern，data pattern，arm，clause の相互 family 全体について射影を
証明する．`let` では一般化 scheme の binder-local value-flow instance，matcher literalでは
共有 target と terminal hole capability の一致を回収する．

一般の context では終端 substitution を context に適用した `RuntimeTyping` を構成する．その
closed-program corollary が中心定理である：

```text
DDSynth signature q S context e raw q' S' →
  RuntimeTyping signature (context.applySubst S') e (S'.apply raw)

DDTyping signature [] e τ →
  RuntimeTyping signature [] e τ
```

完了条件は，型付け derivation を premise に持つ oracle や任意の capability transport を
追加せず，freeze 回帰を含む全例についてこの定理を適用できることである．

### 3. 実行可能推論の DD soundness を証明する

現在の `infer_success_runtimeTyping` より前に，successful trace そのものを ledger-aware DD
derivation へ再構成する．`inferRaw` の fresh allocation 順，solve cut，generalization，matcher
finalization を対応する DD constructor へ写し，terminal validator が確認した freeze event を
DD ledger へ反映する．

中心定理：

```text
infer signature context e = some result →
  DDTyping signature context e result.resolvedTarget
```

これにより，公開推論器の成功は唯一の source typing に対して sound である，という通常の API を
得る．`RuntimeTyping` はこの定理と milestone 2 の合成から内部的に回収できる．

### 4. DDTyping から公開動的安全性を導く

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

### 5. DDTyping に対する推論器の受理完全性を証明する

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

### 6. 受理同値と注釈不要性を公開する

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
| DD typing | `DemandTyping`, `DemandTypingRegression` | source typing，alignment，基本メタ理論と回帰 |
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
