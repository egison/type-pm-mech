# P2：`Matcher κ τ` による capability と target の分離

## 状態

中核方針・Coverage・D1--D4 設計方針決定，D5 の構文的正規化境界決定，
CAS pattern view の詳細設計・再構成未実施．

P2 の解決方針として，従来の一添字

```text
Matcher τ
```

を，構造的分解能力（capability）と実際の target 型を分離した

```text
Matcher κ τ
```

へ一貫して再構成する案を採用する．`MatcherSlot` も同じ二つの役割を持つ
consumer 型として，

```text
MatcherSlot κ τ
```

とする．

ここで重要なのは，単に同じ型を二回持つのではなく，

- `κ` は capability sort に属する
- `τ` は通常の type sort に属する
- capability 変数と通常型変数を別々に量化・改名・代入する
- 通常の Hindley--Milner target 代入は `κ` を変更しない

という分離を，型，スキーム，Algorithm W，値型付けまで貫くことである．

この文書は採用する中核設計，partial matcher に対する capability と Coverage の
境界，移行範囲を固定する．`ShapeCap` については，general／refinement clause から
partial evidence を集め，未観測を中立に exact agreement で合成する方針と，
parameter observability を capability-visible path の依存方程式の least fixpoint
として決める方針に加え，constructor field の evidence を fresh instantiate 後の
result argument slot へ signature-directed に投影する規則まで決定した．D1 はこの
calculus の形式化と証明が残る．D3 は provenance 付き `CapGen` を置かず，二種の
substitution を全体へ適用した後，capability 変数も通常の HM 規則で一般化し，
明示量化を rigid skolem として検査する方針に決定した．D4 は，再帰 binding 自体を
通常の単相 HM 規則で推論し，matcher literal 固有の `ShapeCap` 生成制約だけを
補助的な producer-flow summary で運び，別の least-evidence solver で解いてから
SCC 外で一般化する方針に決定した．
通常型付けと安全な部分集合の形式化は D2 で決定した．`CapTargetOK` の構文的な
正規化境界も D5 で決定したが，現行 CAS matcher の pattern signature と target
former を整列させる pattern-view signature の設計が残る．
論文，Egison 本体，Lean の実変更と，P2 に由来する capability-admissibility 仮定の
除去も完了していないため，P2 自体は未解決として残す．

## 一言でいうと

従来の `Matcher τ` は，一つの `τ` に次の二つの意味を重ねていた．

1. matcher 値が定義時に獲得した構造的分解能力
2. matcher が実際に消費し，次のパターンへ渡す target の型

通常の型代入で target 型を具体化すると，同じ代入が構造能力にも入り込み，
定義時には存在しなかった constructor 能力を後から付け加えられる．

新しい中心不変量は次である．

> target 型は通常どおり特殊化してよいが，matcher 値が定義時に獲得した
> capability を，target 代入や consumer 側の要求によって強化してはならない．

## 二つの添字

### capability `κ`

`κ` は，matcher が定義上公開する構造形状を表す．`ShapeCap` が認める general
constructor clause または constructor／tuple-headed refinement clause の証拠を
少なくとも一つ持ち，observable な全 parameter の evidence を確定できる partial
matcher にも structured capability を与える．したがって `κ` 単独は同じ型形成子の
全 constructor を処理できるという完全性の証明ではない．その全称的保証は，独立な
`CoverageOK` と組み合わせたときに得る．

役割を区別する箇所では，producer の capability を `κ_m`，pattern／slot の
要求を `κ_p`，hole の要求を `κ_l` と書く．通常型とは別 sort とし，
少なくとも次を持つ．

```text
κ ::= •                         constructor 能力なし
    | χ                         capability 変数
    | K κ₁ ... κₙ              型形成子 K に対応する構造能力
    | (κ₁, ..., κₙ)            product 能力
```

`•` は「任意の constructor を処理できる wildcard」ではない．
constructor 能力を持たない **producer capability** である．pattern 側の
「constructor 要求なし」は `•` ではなく，fresh な consumer capability 変数
（以下 `χ_d`）で表す．この区別により，structured matcher も `•` matcher も
変数・ワイルドカード・値パターンへ渡せる一方，`•` matcher を structured
pattern へ渡すことはできない．

構造要求との適合関係を `κ_m ⊑ κ_p` と書く．意図する主要な場合は次である．

- pattern 側が fresh consumer 変数 `χ_d` なら，任意の matcher 能力が適合し，
  witness が `χ_d` をその能力へ決める
- `•` は constructor-headed な要求には適合しない
- 同じ型形成子を持つ能力は，その引数能力を再帰的に検査する
- consumer 側 capability 変数を決めた witness は，全後続 occurrence へ必ず伝播する
- producer 側の既確定 capability を consumer 要求から具体化してはならない

正確な inductive 定義では，現在の one-way 構造関係を capability sort 上へ
移す．fresh rename は scheme instantiation で量化変数に一度だけ行い，
capability 構造内の同一変数の共有を保つ．単相な局所変数の lookup や
slot coercion では fresh rename せず，同じ meta-variable identity を維持する．

### target `τ`

`τ` は matcher が消費する値と，primitive-pattern-pattern の穴から
次 matcher へ渡す値の通常型である．役割を区別する箇所では，producer の
target を `τ_m`，pattern／slot の target を `τ_t`，hole の target を `τ_l`
と書く．

target 側には通常の HM 一般化・インスタンス化・単一化を許す．ただし，
その代入を capability 側へ適用しない．

### capability と target の整合

構造能力と target 型の対応は，すべての構文型を制限する formation condition
ではなく，**実際に構成された matcher 値の不変量**として扱う．概念的には
次の関係である．

```text
CapTargetOK • τ
CapTargetOK (K κ₁ ... κₙ) (K τ₁ ... τₙ)
  if CapTargetOK κᵢ τᵢ for every i
```

`•` は任意の target 型と組にできる．一方，実在する list-headed matcher 値の
target は list 型である．ただし，`Matcher p a` という型構文自体には独立な
`p : Cap` と `a : Type` を許す．対応しない組は値を持たない型になり得るだけで，
関数型の一般化を妨げない．

`T-MATCHER`，`T-SOME`，tuple matcher，標準 matcher combinator の値型付けから
`CapTargetOK` を導く．この選択により，

```text
∀p a. MatcherSlot p a -> Matcher (List p) (List a)
```

へ追加の `CapTargetOK p a` 制約は要求しない．一方，trusted primitive や外部環境が
対応しない組の matcher 値を直接導入してはならない．D5-core では closed
transparent alias と明示的な surface synonym だけを canonicalization に含め，
inductive semantic normalization や CAS ground equivalence を含めない．CAS の
pattern view は別の target-indexed signature として明示する．いずれの場合も，
target 型から capability を再計算してはならない．

## 代表的な型

採用案では，主要な matcher の型を次のように再構成する．

```text
something :
  ∀a : Type. Matcher • a

eq :
  ∀a : Type. {Eq a} => Matcher • a

mPoly :
  ∀a : Type. Matcher • a

f :
  ∀a : Type. a -> Matcher • a

list :
  ∀p : Cap. ∀a : Type.
  MatcherSlot p a -> Matcher (List p) (List a)

multiset :
  ∀p : Cap. ∀a : Type.
  MatcherSlot p a -> Matcher (List p) (List a)

maybe :
  ∀p : Cap. ∀a : Type.
  MatcherSlot p a -> Matcher (Maybe p) (Maybe a)

(m₁, ..., mₙ) :
  Matcher (p₁, ..., pₙ) (a₁, ..., aₙ)
  if mᵢ : Matcher pᵢ aᵢ
```

`something` の多相性は，任意の target 型に特殊化できるという意味である．
任意の constructor 能力を持つという意味ではない．`eq` は同じ capability を
持つが，target 側の `{Eq a}` 制約を別に維持する．

`list something` は，

```text
Matcher (List •) (List a)
```

となる．したがって outer cons は処理できるが，要素位置の constructor
パターンは処理できない．例えば，単純な `$x :: $xs` は受理できる一方，
要素 matcher に `Maybe` 能力を要求する `(Just $x) :: $xs` は拒否する．
`list (maybe integer)` なら後者も受理できる．

## `mPoly` と共有変数反例の解消

### `mPoly`

従来の反例は次である．

```egison
def mPoly {a} : Matcher a :=
  matcher
    | $ as something with
      | $tgt -> [tgt]
```

一添字では，通常のスキームインスタンス化により，

```text
∀a. Matcher a
```

を `Matcher [Integer]` にできる．その結果，定義時には catch-all しかない
matcher が cons 能力を持つように見える．

二添字では，この literal の capability は節構造から `•` に確定する．

```text
mPoly : ∀a. Matcher • a
```

`a := [Integer]` は target 側だけへ適用される．

```text
mPoly : Matcher • [Integer]
```

これは list target の変数パターンには安全に使えるが，cons site では
`• ⊑ List p` が失敗する．target の正当な特殊化を禁止せず，存在しない
constructor 能力だけを拒否できる．

無制限な型代入を許す現行 Lean の宣言的 `Scheme.Inst` には，この `mPoly`
反例が直接当てはまる．現行 Egison は lookup 時に fresh 変数へ改名するだけなので，
`mPoly` を直接 cons site へ渡す経路は既存の裸能力検査で拒否する．しかし，
その fresh 変数が通常引数と共有される次の `f` では，slot 到達前に具体化される．

### 共有型変数を通る `f`

現行 Egison で重要な反例は次である．

```egison
def f := \w ->
  matcher
    | $ as something with
      | $tgt -> [w]
```

一添字では，

```text
f : ∀a. a -> Matcher a
```

と推論される．`f [1, 2]` の通常 application が引数型から `a := [Integer]`
を決めるため，結果も `Matcher [Integer]` となり，cons 能力を偽造できる．

二添字では，

```text
f         : ∀a. a -> Matcher • a
f [1, 2] : Matcher • [Integer]
```

となる．`f [1, 2]` 自体を拒否する必要はない．

```egison
matchAll [9] as f [1, 2] with
  | $x -> x
```

は target と束縛型がともに `[Integer]` であり，型安全である．一方，

```egison
matchAll [9] as f [1, 2] with
  | $x :: $xs -> x
```

は list constructor 能力を要求するため，match site の capability 検査で
型エラーになる．

## target 整合性は別に維持する

二添字化は，primitive-pattern-pattern，decomposition body，next matcher の
target 整合性を取り除く案ではない．各 hole `l` について，

```text
primitive-pattern-pattern が与える hole target
= decomposition body の対応成分型
= next matcher slot の target 成分
```

を通常の伝播する等式と MGU で検査する．

outer target と各 next target を直接すべて等しくするわけではない．例えば cons
節では，outer target が `List a`，head hole が `a`，tail hole が `List a`
である．primitive-pattern-pattern の宣言型がこの対応を決める．

top-level の bare hole を持つ catch-all では，その一つの hole target が outer
target と同じになり，`τ_l = τ_t = τ` である．したがって catch-all の
decomposition body が `[τ_l] = [τ]` であることは，一般の hole／arm 規則から
導かれる．catch-all が最後で，
`$ as M with $tgt -> N` という形を持つという構文条件は残すが，target 型推論だけを
別経路にする必要はない．

## 採用する型規則の骨格

### パターンと hole

パターン型付けは，構造要求と target 型を分離する．

```text
Γ ; Δ ⊢ p : Pattern (κ_p ▷ τ_t) ; Δ'
```

matcher literal 内の primitive-pattern-pattern は，各 hole について，

```text
(κ_l ▷ τ_l)
```

を返す．`κ_l` は next matcher に要求する capability，`τ_l` はその matcher
が消費する target 型である．

`PAT-VAR`，`PAT-WILD`，constructor 分解を要求しない value pattern は，
producer capability `•` ではなく fresh consumer 変数 `χ_d` を構造要求として
生成する．同様に，top-level の `PP-Hole` は fresh consumer hole capability を
生成する．constructor の下にある hole では，pattern signature から得た
capability skeleton を要求する．この signature-directed lift は product と
capability-visible な型形成子の observable parameter 位置だけをたどり，
inductive pattern declaration を持たない opaque former と関数型を境界として止まる．
field evidence は fresh instantiate 後の result argument slot へ投影し，`unseen` は
何も寄与しない．投影が必要な path で既知の head／arity が一致しなければ，
`unseen` へ落とさず型エラーにする．observable でない parameter は skeleton 上でも
canonical `•` とする．

### `T-SOME`

```text
Γ ⊢ something : Matcher • α
```

ここで `α` は fresh な通常型変数である．capability 側に fresh な一般変数を
置いてはならない．それを量化すると，同じ P2 反例が capability sort 上で再発する．

### `T-MATCHER`

matcher literal の capability と target を別々に決める．

- capability は `ShapeCap` が証拠として認める primitive-pattern-pattern の
  constructor clause，product 構造，next matcher の capability から構成する
- target は primitive-pattern-pattern の宣言型，primitive data pattern，
  decomposition body，next matcher slot の target 成分から通常推論する
- primitive data pattern と arm body は capability を強化しない
- Coverage は capability 生成と独立に検査する
- target 代入を適用した後に capability や Coverage を再計算しない

matcher literal の root capability は，`ShapeCap` が証拠として認める constructor
clause と hole の capability から **shape capability** として合成する．同じ
型形成子 `K` の証拠 clause が少なくとも一つあり，合成後の observable な
parameter がすべて確定すれば，完全な Coverage がなくても `K κ₁ ... κₙ` を与える．
shape の証拠を持たない catch-all-only literal は必ず `•` になる．したがって
`ShapeCap` は「この matcher が `K` の構造を少なくとも一部観測する」という存在的な
may 近似であり，`K` の任意の constructor を安全に処理するという証明ではない．
principal 性の正確な主張は D1 で固定する．

general constructor／tuple clause と，constructor／tuple-headed refinement clause
を `ShapeCap` の証拠に数える．refinement は固定 prefix のため完全な capability
ではなく，`unseen` を含む partial evidence を与える．hole `$` は対応する next
matcher の capability，wildcard `_` と value-pattern-pattern `#$x` は `unseen`，
nested constructor／tuple はその head と内部の partial evidence を与える．bare-hole
catch-all と top-level value／wildcard clause は structured root evidence を与えない．

同じ capability 位置の証拠は，`unseen` を中立として variable-identity-preserving な exact
agreement で合成する．既に正当化された capability substitution の適用後に同じ
producer capability でなければ型エラーとし，この合成自体は producer 変数の
単一化や capability weakening を行わない．structured root を得た後，observable な
capability parameter 位置が `unseen` のままなら，target 型や annotation から補わず
型エラーとする．宣言全体で unobservable な parameter は canonical に `•` とする．
詳細な partial evidence，observability，signature-directed projection，合成規則は
下記 D1 に記す．

`CoverageOK` は target 型ではなく capability を基準にする独立な述語とする．

- `Matcher • τ` では constructor Coverage は空虚
- `Matcher (List p) (List a)` では，安全な部分集合に入るために List の全一般節を
  要求する
- user-defined product matcher literal では，全体に一つの一般 tuple 節
  `($, ..., $)` を要求する
- Coverage を満たさない `Matcher (List p) (List a)` も Egison の通常検査では
  受理でき，warning を有効にすれば不足を非致命的に報告できるが，安全性定理の
  対象外とする

tuple-of-matchers 値は各 component matcher から構成される producer であり，
matcher literal の clause Coverage は持たない．その capability と target は
componentwise に product へ持ち上げる．

各 hole の next matcher は，R12 で固定した成分境界に従い，完全な

```text
MatcherSlot κ_l τ_l
```

へ送る．0 hole または複数 hole では明示タプル，1 hole では式全体を一成分とし，
式が変数・application・lambda のどれかで判定を変えない．

### `COERCE-MATCHER-TO-SLOT`

producer matcher を consumer slot へ送る規則は，概念的に次となる．

```text
Γ ⊢ e : Matcher κ_m τ_m
matchCap(κ_m, κ_p) = S_κ
mgu(S_κ τ_m, S_κ τ_t) = S_τ
S = S_τ ∘ S_κ
--------------------------------
S Γ ⊢ e : MatcherSlot (S_κ κ_p) (S τ_t)
```

構造検査は capability 成分だけ，target 検査は通常型成分だけを見る．
`matchCap` は既知の producer head を consumer 要求で変更しないが，通常の推論で
導入した flexible capability meta-variable はどちら側に現れても制約で解ける．
明示量化から導入した skolem は解かない．`matchCap` が返す witness `S_κ` は局所的な
成功証拠ではなく Algorithm W が返して合成する capability substitution である．
期待 slot だけでなく，型付き式，関数結果，環境，残余制約にある同じ変数の全
occurrence へ **必ず**適用し，その後でだけ generalization を行う．`matchCap` が
内部で witness を得ても yes／no だけを返して捨てる checker は採用設計に含めない．

例えば `list` の fresh な `p` へ `something : Matcher • a` を渡すと，
`S_κ = {p ↦ •}` を結果型にも適用し，

```text
Matcher (List •) (List a)
```

を得る．正しい Algorithm W では，generalization が見る型に `p` はすでに存在せず，
通常の free-variable generalization の候補にならない．代入前の raw result
`Matcher (List p) (List a)` を一般化する経路は，`CapGen` で後から除外するのではなく，
Algorithm W の substitution-threading invariant に違反するものとして排除する．

target 側は独立した存在検査 `τ_m ∼ τ_t` ではなく，その occurrence の通常 HM
制約を prevailing MGU `S_τ` へ統合する．同じ単相 matcher target を異なる型へ
別々の witness で使うことを許してはならない．`S_τ` は surrounding target 型へ
伝播するが，capability へは侵入しない．

既存 `MatcherSlot κ' τ'` を期待 slot へ送る場合は，両者が consumer 要求なので，
capability 成分と target 成分をそれぞれの sort の通常 MGU で検査し，
得た代入を後続推論へ伝播する．

### producer 同士の等式

`Matcher` 同士の等式は，

- capability は capability sort 上の kind-correct equality／unification
- target は通常型の equality／unification

として分離する．異なる capability constructor は一致しない．通常の推論で導入した
flexible capability meta-variable は MGU で解けるが，明示 `forall` の skolem，
`•`，finalized constructor skeleton は rigid であり，別の constructor capability
へ変更できない．flexible meta-variable を structured capability に解くことは，
lambda 入力など未確定な型へ必要な能力を制約する操作であり，既に構成済みの producer
値を後から強化する操作ではない．

matcher literal の root head は D1 の finalization で `•` または structured
constructor に確定し，evidence-free な root meta-variable を外へ出さない．next
matcher／入力 evidence に支えられた child meta-variable は，同じ variable identity
を保って structured capability 内に残せる．したがって一般化可能性を入力 origin で
分類する provenance metadata は導入しない．ただし，D1 の partial evidence に対する
exact merge は Algorithm W の MGU とは別の部分演算であり，異なる evidence 変数を
merge のために単一化しない方針を維持する．

capability が同じなら target の正当な特殊化を許せるため，最終的には現在の
「`Matcher` 添字全体を完全一致させる」剛性を，capability mismatch と通常
target unification へ置き換えられる．

例えば，

```egison
def integer : Matcher • Integer := eq
```

は，`Integer` の `Eq` 制約が解消できるなら，`eq` の target だけを特殊化し
capability `•` を保存するので安全に受理できる．annotation は literal や既存
matcher の capability を作り出してはならず，capability 注釈は推論結果と
照合するだけとする．

## スキーム，一般化，代入

型スキームは capability 変数と通常型変数を別々に量化する．

```text
∀(χ₁ ... χ_m : Cap).
∀(α₁ ... α_n : Type).
τ
```

少なくとも次を二種対応にする．

- free variables
- fresh rename
- generalization
- scheme instantiation
- substitution application
- substitution composition
- occurs check
- kind checking

通常型代入 `S_τ` と capability 代入 `S_κ` は相互に侵入しない．

```text
S_τ (Matcher κ τ) = Matcher κ (S_τ τ)
S_κ (Matcher κ τ) = Matcher (S_κ κ) (S_κ τ)
S_τ (S_κ T) = S_κ (S_τ T)
```

ただし，型全体の入れ子にある各 `Matcher` occurrence には同じ規則を再帰的に
適用する．これにより matcher が関数結果，tuple，collection，ユーザー定義
データ，alias の内側へ入っても capability を失わない．

capability 変数の量化自体は禁止しない．例えば，

```text
list :
  ∀p a. MatcherSlot p a -> Matcher (List p) (List a)
```

では，引数 slot から得た `p` を結果 capability へ伝播する必要がある．
capability 変数の一般化にも provenance 付きの特別な `CapGen` は置かず，通常の
HM generalization を capability／type の二 sort へ拡張する．Algorithm W が返す
全 capability substitution `S_κ` と通常型 substitution `S_τ` を，型，環境，
残余制約へ先に適用した結果を `τ'`，`Γ'` とすると，概念的に

```text
Gen(Γ', τ') =
  ∀(ftv_Cap(τ') \ ftv_Cap(Γ') : Cap).
  ∀(ftv_Ty (τ') \ ftv_Ty (Γ') : Type).
  τ'
```

とする．二種 substitution は相互に侵入しないが，型全体の全 occurrence へ再帰的に
適用し，generalization は必ずその後に行う．したがって `list something` の
`p ↦ •` は結果型へ適用済みであり，`p` は generalization 候補に残らない．
ここで量化候補に数えるのは flexible meta-variable だけであり，rigid skolem は
量化せず，annotation checking の scope 外へ escape させない．
残余の型クラス制約がある場合も同じ二種 substitution を先に適用し，scheme に保持する
制約を含めた free variables から量化集合を計算する．

安全性には通常の HM 規則に加えて次の境界を置く．

- 推論中の未解決変数は flexible meta-variable，明示 `forall` の変数は rigid
  skolem として区別する
- matcher literal の root head は D1 の finalization で `•` または structured
  constructor に確定し，evidence-free な meta-variable を一般化点へ出さない．入力
  evidence と identity を共有する child variable は通常 generalization の対象にできる
- explicit capability parameter は skolem として本体を検査し，producer の既知能力を
  annotation に合わせて変更しない
- 再帰 binding は通常の HM 規則どおり SCC 内で単相に保ち，通常等式と D4 の
  `ShapeCap` 生成制約を解いて finalization した後，SCC の外側でだけ通常の
  HM generalization を行う

この規則では，

```text
bad : ∀p a. Matcher p a
bad = something
```

の `p` は rigid skolem なので，`something` の `•` と一致せず拒否される．一方，

```text
∀p a. Matcher p a -> Matcher p a
∀p a. MatcherSlot p a -> Matcher (List p) (List a)
```

は通常の parametric な関数型として一般化できる．annotation を持たない constant
producer から危険な `∀p. Matcher p a` が推論されないことは，literal finalization，
substitution threading，通常 generalization から Lean で導く．この簡潔な体系で
Algorithm W の健全性または能力非強化を証明できない反例が見つかった場合に限り，
必要な最小範囲の provenance／一般化制限を再検討する．

初期環境の primitive／foreign scheme は kind-correct であるだけでは足りない．
source typing から導出された scheme か，その全 instance で runtime matcher invariant
を満たす trusted declaration であることを `EnvTyped` の前提にする．外部環境から
根拠のない `∀p. Matcher p a` を公理として注入することは許さない．

## 現行仕様・実装との対応表

記号の意味は，`✓` が現行経路で実装済み，`△` が局所的，`✗` が未実装である．
「通常の match」は `matchAll` の matcher 利用位置，「next matcher」は
matcher 定義の各 hole へ送る式を指す．

| 項目 | 現行論文 | Egison 通常の match | Egison next matcher | 二添字案 |
|---|---|---|---|---|
| 1．固有能力と target の分離 | △ 単相 dual check で一時的に分離 | △ 一添字の freeze で近似 | △ 一添字の freeze で近似 | `Matcher κ τ` で恒久的に分離 |
| 2．各穴に完全な slot を構成 | ✓ `T-MATCHER`／Consistency (1a) | ✓ 完全な `MatcherSlot` | ✓ R12 で実装済み | 二種の添字を持つ slot として維持 |
| 3．producer の双対検査 | ✓ 構造と target を別判定 | ✓ 構造先行 coercion | ✓ freeze 済み能力で検査 | capability と target を別 sort で検査 |
| 4．既存 slot の両成分検査 | ✓ Step 3a | ✓ | ✓ R12 で実装済み | capability MGU と target MGU に分離 |
| 5．scheme instantiation の fresh rename | ✓ 記述済み | ✓ 局所 one-way | ✓ R12 で実装済み | 二 sort の量化変数だけを再帰的に改名し，単相 identity は保存 |
| 6．式構文形への非依存 | ✓ | ✓ | ✓ R12 で実装済み | 型に capability が残るため自然に維持 |
| 7．scheme lookup 後の能力保存 | ✗ P2 | ✗ 共有型変数経路 | ✗ 同じ scheme 経路 | 二種 Scheme／Subst，全 substitution 伝播，通常 HM generalization／skolemization を実装・証明する |

R12 が解決した成分境界，完全 slot 検査，構文形非依存という 2--4，6 の結果は
二添字化後も維持する．一方，5 の局所 fresh rename は，scheme instantiation だけを
fresh にし単相 identity を保つ D3 の規則へ置き換える．P2 の実装対象は，主に 1 と 7
を型表現・scheme・value flow 全体で閉じることである．表の二添字案は採用した目標で
あり，実装済み・証明済みという意味ではない．

## 一添字の代案を採用しない理由

### target 型と束縛型の一致だけを検査する案

この一致は target 整合性として必要だが，通常単一化では `f` の引数型と
matcher target が同じ変数になり，`f [1, 2]` では両方 `[Integer]` になる．
`mPoly` は定義時から input target と next target が同じなので必ず通る．
したがって P2 の構造能力強化を検出できない．

### 一添字を rigid に保存する案

定義時の裸変数を固定すれば反例を拒否できるが，その裸変数は実質的に
capability として働いている．target 特殊化まで同時に禁止すると，
`something` の安全な list target／変数パターン利用や，
`Matcher (List a)` の `a := Integer` まで過剰に拒否する．

定義時骨格を hidden metadata として保存する案は実装可能だが，その情報を
scheme，関数，tuple，データ格納の各 `Matcher` occurrence に通す必要がある．
これは内部的には二添字と同型であり，今回は論文・実装とも明示的な
`Matcher κ τ` とする．

### matcher 多相を一般化しない案

値制限に似た保守策は反例を閉じられるが，`something`，matcher combinator，
高階 matcher の正当な多相性と annotation-free HM-style inference を大きく失う．
最終設計には採用しない．

## 論文の再構成範囲

英語版と日本語版を同期して，少なくとも次を変更する必要がある．

1. 型文法に capability sort と `Matcher κ τ` を導入する．
2. `MatcherSlot` の第1添字を capability，第2添字を target と明記する．
3. 通常型／`Σ_P` signature から capability signature への signature-directed lift
   を定義する．lift は演算として全域的だが，opaque former／関数型では内部へ入らず，
   capability-visible path の observable parameter だけを fresh instantiate 後の
   result argument slot へ投影する．`unseen` は非寄与，既知 head mismatch は失敗，
   unobservable parameter は canonical `•` とする．その結果から pattern／
   primitive-pattern-pattern の構造成分を定義する．
4. `T-SOME`，`T-MATCHER`，tuple coercion，slot coercion を二添字化する．
5. `ShapeCap` 合成と独立な `CoverageOK` を定義し，matcher target
   ではなく capability に索引付けする．
6. catch-all の target 検査を一般 hole／arm 規則と同じ経路にする．
7. matcher rigidity 節を，capability 保存と通常 target 多相の分離として書き直す．
8. Scheme.Inst，二種 HM generalization，Algorithm W，主要性の instance relation を，
   二種代入，全 substitution 伝播，明示量化の skolem checking へ変更する．
9. 再帰 binding には通常の単相 HM 規則を用い，matcher literal が別に生成する
   `ShapeCap` obligation，producer-flow summary，binder–RHS generation knot，
   least-evidence 解，finalization 後の SCC 外 generalization を Algorithm W の
   補助 judgment として定義する．
10. runtime matcher typing，slot invariant，canonical forms を二添字化する．
11. `capability-admissible` を source typing から導き，P2 に由来する仮定を除く．
12. 全標準 matcher の型，本文例，付録の導出を新しい型へ更新する．

## Lean 機械化の再構成範囲

### `Syntax`

- capability の inductive syntax／sort
- `Ty.matcher : Cap -> Ty -> Ty`
- `Ty.matcherSlot : Cap -> Ty -> Ty`
- capability binder と通常型 binder を持つ `Scheme`
- 通常型／pattern signature から capability skeleton への signature-directed lift，
  fresh result-slot projection，product／capability-visible／opaque barrier，
  parameter observability の least fixpoint

### `TypeRel`

- `CapSubst` と通常 `TySubst`
- capability の free variables，apply，fresh rename，composition
- capability 上の one-way 構造関係
- 二種の変数を扱う `Scheme.Inst`
- flexible capability meta-variable と rigid skolem
- 全 substitution 適用後の二種 HM generalization
- kind preservation と二種代入の相互非干渉

### `Typing`

- `PatTy`／`PPTy` の構造成分を capability 化
- `ClauseTy`／`ArmsTy`／`ClausesTy` の二添字化
- `ShapeCap`，coverage 非依存の `MatcherWF`，`CoverageOK` を分離し，
  `ordinary`／`covered` の `CoverageReq` で再結合
- `HasTy.matcherE`，`something`，tuple／slot coercion の二添字化
- matcher literal の `ShapeCap` 合成と主要性境界
- 現行の単相 `HasTy.fixE` を通常の再帰型付け規則として維持し，matcher literal の
  `ShapeSolved` side judgment と algorithmic な生成制約解決を別に接続する
- variable／lambda／application／let／constructor に通常型付けと同じ構文再帰を持つ
  producer-flow summary judgment，first-order evidence への正規化，
  binder–RHS generation knot
- 現行構文の `Expr.fix f x e` に対する singleton 規則を先に機械化し，相互再帰版は
  構文を拡張するときまで定理の対象にしない

### `WellTyped` とメタ理論

- mode-indexed `ValueTy`／`EnvTyped`／`SubstTyped`，`MatcherOK`，`WTTree`，
  `WTStack`，`WTState` と covered-to-ordinary erasure
- `ValueTy.matcherV`，`something`，product matcher，derived slot typing が
  ambient `CapTargetOK` context と同じ mode を保存する規則
- target substitution が `ShapeCap`／`CoverageOK` を変えない補題
- capability substitution lemma と one-way の一意性
- `matchCap` witness を型・環境・制約の同一 meta-variable occurrence へ伝播する補題
- Algorithm W の返す二種 substitution が結果型，環境，残余制約の全 occurrence へ
  適用される不変量
- 二種 generalize／instantiate と明示量化の skolem checking の健全性
- 通常 HM generalization から closed constant producer の能力非強化を導く補題
- singleton `fix` に対する Algorithm W の健全性・完全性・主要性と，単相 lookup が
  placeholder identity を保存する補題
- 再帰 `ShapeCap` solver の停止性，健全性，完全性，最小性，決定性，seedless cycle の
  非生成，occurs check，clause／SCC 順序独立性
- 通常の capability substitution と `ShapeCap` solution の合成保存，
  generation node の non-escape，finalization-before-generalization
- producer-flow summary の expression typing に対する健全性，application substitution，
  first-order normalization の決定性・source preservation，trusted flow summary を
  含む `EnvTyped` preservation
- producer-flow path が指す full `Matcher κ τ` occurrence と context-relative
  `CapTargetOK` を保つ `FlowTargetOK`
- Structural-Hole Transfer の capability 版
- pattern typing／one-way head compatibility と
  `CoverageOK + CatchAllLast` から `DispatchOK` を導く補題
- R10 の `BaseAdm` 下での ordinary completed-evaluation partial correctness と
  `DispatchOK` 付き局所 matching-state Preservation
- covered mode の fundamental theorem，Preservation，constructor Progress，
  Type Safety
- `hgen` を二種一般化補題で放電する証明
- P2 に由来する capability-admissibility を安全性定理から除く証明
- Algorithm W の健全性・完全性・最汎二種代入

P1 の capture-admissibility，`StepTotal`，一般の停止性は P2 と独立なので，
二添字化だけでは除去されない．

## Egison 実装の再構成範囲

### 型表現

現行の

```haskell
TMatcher Type
TMatcherSlot Type Type
```

を概念的に，

```haskell
TMatcher Capability Type
TMatcherSlot Capability Type
```

へ変更する．capability 専用 ADT，または kind 付き変数のどちらを採る場合も，
通常 `Subst` が capability へ入らないことを型または API で保証する．

主な変更先は次である．

- `Type/Types.hs`：型構成子，free variables，変換，正規化，型注釈
- `Type/Subst.hs`：target substitution と capability substitution の分離
- `Type/Env.hs`：全 substitution 適用後の二種 generalize／instantiate，type scheme と
  parametric producer-flow summary の対
- `Type/Unify.hs`：capability equality，one-way，二成分 coercion
- `Type/Infer.hs`／`Type/Check.hs`：`something`，match site，matcher literal，
  tuple，二種 substitution threading，annotation skolem checking，
  producer-flow generation／application／first-order normalization
- `AST.hs`／`NonS.hs`／`Types.hs`：二添字 `TEMatcher`，capability binder，
  type-expression 変換
- parser／pretty printer／type error：二添字の表示，round-trip，変数改名，診断
- type-class expansion／declared-type concretization：capability 変数を通常型変数として
  扱わない監査
- standard library：全 matcher／slot annotation の移行

現在の

```haskell
applySubst s (TMatcher t) = TMatcher (applySubst s t)
```

に相当する処理は，一つの代入を両役割へ流すため廃止する．

現在の一引数 `MatcherSlot a` を `MatcherSlot a a` へ展開する sugar も廃止する．
別 sort 導入後に同じ変数を capability と target の両方へ複製することはできない．

### matcher literal

- pattern declaration 群から parameter observability を先に計算し，opaque／function
  内部と seed のない recursive-only parameter を canonical `•` にする
- primitive-pattern-pattern の hole ごとに最初から完全な
  `MatcherSlot κ_l τ_l` を構成する
- arm body は target tuple の collection として検査する
- next matcher は完全な期待 slot へ検査する
- outer capability は D1 で定める constructor 証拠と next matcher evidence を
  fresh instantiate 後の result argument slot へ投影し，field／clause 間で exact
  merge して `ShapeCap` として finalization する
- 形式用の `CoverageOK` は `ShapeCap` と独立に定義し，Egison では既存の
  target-based Coverage 診断を維持して，診断を有効にした場合は不足を warning
  として報告する
- outer target は primitive pattern，data pattern，arm，next target から推論する
- annotation は capability を生成せず，推論された capability を検証する

R12 で実装した明示タプル境界，構文形非依存，完全 slot 検査は維持する．

再帰 matcher でも式の型推論自体は通常の単相 HM 再帰規則を使う．それと並行して
matcher literal だけが SCC-local な `ShapeCap` 生成制約を集め，Coverage 診断とは
独立に least evidence を解く．再帰 occurrence は dependency node として既存 evidence
を伝播・検証するだけであり，consumer demand，結果注釈，自己参照から seed を作らない．
finalization 前には一般化せず，annotation は finalized capability に対する検査として
適用する．alias／高階 application では user-visible type scheme と対にした補助的な
producer-flow summary を適用し，first-order evidence へ正規化してから再帰 binder と
RHS summary を generation knot で結ぶ．この分離と処理順の詳細は D4 に固定する．

### 実行時

capability は静的情報なので，基本的な `UserMatcher` の実行時表現，
primitive-pattern-pattern の選択，decomposition の評価を変更する必要はない．
型付き中間表現に capability を残すか，型検査後に消去するかは実装上の選択である．

runtime の `something` が受理する一部の product pattern と，typed semantics が
明示 product matcher を要求する範囲に差がある場合は，後者を維持する意図的制限として
回帰に記録する．

### homogeneous target の境界

この二添字案でも，`τ` は current target と next target／pattern binding を
同じ通常型の関係に置く．例えば `sample/nishiwaki.egi` のように Bool target から
任意の `a` を束縛する type-transforming matcher は対象外である．その例を新しい
homogeneous 仕様へ変更するか，将来の第三の型軸として分離する必要がある．
これは capability と target の分離だけでは解決しない．

## Coverage と partial shape capability の設計判断

### 採用する境界

Coverage を structured capability の生成条件から分離する．ある型形成子 `K` について
`ShapeCap` が証拠として認める general または constructor／tuple-headed refinement
clause が少なくとも一つ観測され，observable な capability parameter が確定すれば，その
matcher は `K`-headed な shape capability を持つ．すべての constructor を扱わない
partial matcher も
`Matcher (K κ₁ ... κₙ) (K τ₁ ... τₙ)` として型付けでき，target 型を後から
特殊化してもこの capability は変化しない．

一方，`CoverageOK cls (K κ₁ ... κₙ)` は，matcher literal の root capability head
が `K` であるとき，結果型の head が `K` である全 pattern constructor に general
clause `c $...$` があることを表す独立な全称的条件とする．子の安全性は，対応する
next matcher の `ValueTy_covered` が担う．user matcher literal ならそこから自身の
`CoverageOK` を得て，`something`／product matcher なら各値規則の covered premise
を使う．`CoverageOK cls •` は空虚であり，product head では適切な arity の general
tuple clause を要求する．Coverage に数えるのは general clause だけであり，
refinement clause は数えない．

以下は依存する型付け context などを省略した概念図である．

```text
ShapeCap cls κ                 -- root head は存在的，子は全 evidence の exact consistency
CoverageOK cls κ               -- 全称的：全 general constructor clause
CoveredShape cls κ
  := ShapeCap cls κ ∧ CoverageOK cls κ
```

`ShapeCap` の推論結果は，Coverage warning の有効・無効によって変えてはならない．
形式的な `CoverageOK` は capability head に索引付けする一方，現行 Egison の診断は
target 型の head に宣言された全 constructor と general clause の集合を独立に比較し，
欠けている constructor を報告する．したがって，例えば
`Matcher • (List a)` は constructor pattern の利用を capability 検査で拒否するので
`CoverageOK` が空虚でも，catch-all-only の list target に対する既存 warning は
引き続き出せる．この target-based warning は advisory な診断であり，
`CoverageOK` の証拠ではない．

### 実装と安全性定理の境界

Egison の通常検査では partial matcher を structured capability のまま受理し，
Coverage warning を有効にした場合は不足を非致命的に報告する．これは，粗い一つの
式型に多数の pattern constructor を宣言し，互いに異なる部分集合だけを扱う数式
matcher 群を維持するためである．ここで緩めるのは primitive-pattern-pattern の
constructor Coverage だけであり，選択済み節内の primitive data pattern arm の
網羅性と catch-all の到達性・順序条件は従来どおり通常の型検査条件に残す．

未被覆 constructor のパターンも同じ `K`-headed capability の利用時検査を通るため，
この近似だけから no-stuck は導けない．現行意味論では，そのパターンが catch-all
から `something` へ委譲されると runtime error／stuck になり得る．これは
`matchAll` の空結果や表層 `match` の定義済み failure とは異なる．

したがって，型推論で受理する集合と，Progress／Preservation／Type Safety を主張する
集合を二層化する．後者は `CoverageOK` を含む完全な Matcher Consistency を満たす
matcher に限定する．warning が出なかったこと自体を定理の前提にはしない．現行 warning
は opt-in で，入れ子の matcher では抑制される場合があるため，定理は意味的な
`CoverageOK` を直接要求する．

P2 が取り除くのは scheme instantiation による capability-admissibility 仮定であり，
Coverage，P1 の capture-admissibility，`StepTotal` まで同時に取り除くものではない．

## 残る設計課題と形式化課題

### D1：principal `ShapeCap` の合成（設計方針決定済み）

**決定済みの証拠範囲．** general constructor／tuple clause に加えて，
constructor／tuple-headed refinement clause も `ShapeCap` の証拠に数える．
refinement は pattern constructor の一部の形だけを処理するため `CoverageOK` の
証拠にはならないが，partial matcher が実際に観測する shape の存在的証拠にはなる．
top-level の value-pattern-pattern，wildcard，bare-hole catch-all は structured
root evidence を与えない．

general clause だけに限定すると，例えば `headSlot` の `$ :: _` や
`assocMultiset` の `($, $) :: $` のような refinement-only の構造を失う．後者は
general clause が `[]` しかないため，要素 capability が最後まで未観測となり，
下記の未確定位置規則によって matcher literal 全体が型エラーになる．したがって，
既存の partial matcher と「必要な observable position が確定する限り，pattern
constructor を一つでも観測すれば capable」という方針を維持するには refinement の
partial evidence が必要である．

**partial evidence．** capability を直接集める代わりに，合成中だけ次の evidence
tree を用いる．

```text
e ::= unseen
    | •
    | χ
    | K e₁ ... eₙ
    | (e₁, ..., eₙ)
```

constructor／tuple-headed primitive-pattern-pattern の内部と，R12 で分離した next
matcher 成分から，概念的に次を抽出する．

```text
childEvidence($, m)              = capability(m)
childEvidence(_, -)              = unseen
childEvidence(#$x, -)            = unseen
childEvidence(C pp₁ ... ppₙ, ms) =
  lift_C(childEvidence(pp₁, ms|pp₁), ..., childEvidence(ppₙ, ms|ppₙ))
childEvidence((pp₁,...,ppₙ), ms) =
  (childEvidence(pp₁, ms|pp₁),...,childEvidence(ppₙ, ms|ppₙ))
```

ここで `_` と `#$x` は producer capability `•` ではない．それらは利用者の
wildcard／value pattern をその場で処理して successor pattern を作らないため，
next matcher の能力を何も観測しない．`C` は surface pattern constructor，`lift_C`
はその signature が与える結果型形成子 `K`，result argument slot，field 型式を用いる
下記の投影である．したがって `Nothing` と `Just` を capability head `Maybe` へ，
`[]` と `::` を `List` へ対応付けるのは surface constructor 名ではなく signature
である．nested constructor／tuple はこの対応を通して既知の capability head と
内部の partial evidence を与える．`ms|ppᵢ` は flatten 済み next matcher 成分 `ms`
のうち，`ppᵢ` の hole 数に対応する左から右への部分列であり，R12 の成分境界を
変えない．

`childEvidence` は constructor／tuple 内部の hole にだけ用いる．top-level の bare
hole `$` は catch-all であり，その next matcher が structured capability を持っても
matcher literal の structured root evidence にはしない．

**signature-directed projection．** pattern constructor signature を fresh
instantiate した結果を

```text
C : τ₁, ..., τᵣ -> K ρ₁ ... ρₙ
```

とする．`ρ₁, ..., ρₙ` は root capability `K e₁ ... eₙ` の位置に対応する
**result argument slot** である．各 field 型 `τⱼ` と，その primitive-pattern-pattern
から得た evidence `dⱼ` について，

```text
project_{ρ̄}(τⱼ, dⱼ) ⇓ (e₁, ..., eₙ)
```

を，長さ `n` の partial-evidence vector を返す部分 judgment として定義する．
投影は概念的に次の二段階で行う．

ここで fresh instantiation は signature binder を fresh rename して同一 parameter
の variable identity を保持する操作であり，通常 target substitution を capability へ
lift する操作ではない．例えば，

```text
Just : a -> Maybe a
target substitution = {a ↦ List Integer}
```

でも，field matcher capability が `•` なら結果 evidence は `Maybe •`，
`List •` なら `Maybe (List •)` である．target が `List Integer` になったという理由だけで
`List` capability を生成してはならない．

1. field 型式と evidence を同時にたどり，result argument に現れる fresh signature
   parameter への partial assignment `Θ` を集める．
2. `Θ` を result argument slot `ρ₁, ..., ρₙ` の順序と型式へ配置し直す．

第1段階の規則は次である．

```text
collect(τ, unseen) = ∅
collect(α, d) = {α ↦ d}                         α が result argument に現れる
collect((τ₁,...,τₘ), (d₁,...,dₘ))
  = collect(τ₁,d₁) ⊔ ... ⊔ collect(τₘ,dₘ)
collect(F τ₁...τₘ, F d₁...dₘ)
  = ⊔_{i | Obs_F(i)} collect(τᵢ,dᵢ)
```

ここで `⊔` は同じ signature parameter への assignment を下記の `merge` で合成する
部分演算である．product と capability-visible former は既知の head と arity が
一致するときだけ componentwise にたどる．`unseen` は head 検査より先に空 assignment
を返すため，他の clause の証拠に対して中立である．一方，result argument への
observable path をたどる必要があるのに evidence が `•` または異なる既知の
constructor／product head を持つ場合は，projection failure とする．これを
`unseen` に変換してはならない．別の理由で正当化された capability substitution は
projection より先に適用するが，必要な former head の位置に裸の `χ` が残る場合，
projection の exact merge だけで単一化せず，通常の Algorithm W へ head constraint
として返す．W は flexible meta-variable なら capability MGU で解き，rigid skolem
なら拒否する．返却 substitution を全体へ適用した後も literal root に未解決位置が
残れば，D1 の finalization で型エラーにする．

inductive pattern declaration を持たない opaque former と関数型は barrier とし，
内部へ入らない．result argument の parameter を含まない ground branch も root
evidence へ寄与せず，その branch の matcher capability と target の適合は通常の
slot／target judgment に任せる．recursive former は `Obs` が認める位置について
既に得た evidence を伝播・検証するだけであり，projection 自体を observability の
seed にはしない．独立な child matcher から得た既知の `K p` は recursive field を
通して `p` を伝播できるが，自己参照だけから生じる generation dependency
`g ← g` は D4 の least-evidence solver で `unseen` のままとする．これは通常の
capability 等式 `κ₁ ~ κ₂` ではなく，MGU へ渡して恒等等式として消してはならない．

第2段階では，assignment を各 `ρᵢ` の型式へ埋め込む．その slot へ届く assignment が
なければ vector 成分全体を `unseen` とする．届く assignment があれば product と
capability-visible former の構造を保存して evidence tree を作り，未割当の observable
leaf は `unseen`，ground／unobservable branch は canonical `•` とする．したがって，

```text
C : a -> b -> K b a
field evidence = p, q
project result = K q p

D : a -> K (a, Integer)
field evidence = p
project result = K (p, •)
```

となる．投影先を source declaration の変数順ではなく fresh instantiate 後の result
argument slot とするため，parameter の並べ替え，product，nested result argument を
同じ規則で扱える．fresh instantiation は，同じ signature parameter の identity を
保持してからこの投影を行う．

例えば，

```text
Cons : a -> List a -> List a
```

で head field の evidence が `p`，tail field が `List q` なら，両方を result の唯一の
parameter slot へ投影して `merge(p, q)` する．また，

```text
Wrap : List a -> Wrap a
```

で field evidence が `List p` なら `Wrap p` を得る．同じ field evidence が `•`
なら，必要な `List` head との既知 mismatch であり型エラーになる．`unseen` なら
この field は何も寄与せず，他の field／clause からも evidence が来なければ
finalization で observable parameter の未確定として型エラーになる．

一つの field 型内，同じ clause の複数 field，異なる clause，異なる入れ子深さから
同じ result slot へ届く evidence は，すべて同じ `merge` で合成する．投影用に別の
単一化や優先順位を導入しない．head equality の前に行う alias／normalization の
正確な境界だけは D5 に従う．

**exact merge．** 同じ capability 位置へ届く general／refinement の全 evidence は，
次の部分演算で合成する．

```text
merge(unseen, e) = e
merge(e, unseen) = e
merge(•, •) = •
merge(χ, χ) = χ                         -- 同じ variable identity の場合だけ
merge(K ē, K f̄) = K merge(ē, f̄)     -- 同じ head／arity
merge((ē), (f̄)) = (merge(ē, f̄))     -- 同じ arity
merge(e, f) = error                     -- その他
```

この比較は，別の理由ですでに得た capability substitution を適用した後に行う．
合成を成功させるために異なる producer capability 変数を単一化したり，強い
capability を `•` へ weakening したりしない．同じ型パラメータが一つの clause
内に複数回現れる場合も，複数 clause の場合と同じ merge を使う．したがって演算が
成功する範囲では clause の順序に依存せず，同じ exact evidence tree が得られる．

**parameter observability．** 型形成子 `K` の各 parameter 位置 `i` が capability
として観測可能かを，pattern constructor signature 全体から計算する．この判定は
選択された matcher clauses や target annotation ではなく宣言だけに依存する．
概念的には，各 capability-visible な型形成子 `F` に parameter observability mask
`Obs_F` を持たせ，constructor field 型の中を次のようにたどる．

- result parameter `α_i` へ直接到達すれば `i` の seed を得る
- product は全 component へ入る
- `List`，`Maybe` のように pattern 構造を公開する型形成子 `F` では，
  `Obs_F` が真の parameter 位置だけへ入る
- inductive pattern declaration を持たない opaque former と関数型の内側へは入らない
- 自身または相互再帰群の型形成子へ戻る辺は，その parameter の現在の
  observability を伝播するだけで seed を作らない

この有限な依存方程式の **least fixpoint** を `Obs_K` とする．したがって，

```text
Phantom a := tag Integer
```

の `a` は true phantom であり unobservable である．

```text
Hidden a := hidden (Opaque a)
```

で `Opaque` が inductive pattern declaration を持たない場合も，その内側の `a` は
unobservable である．opaque value 全体を variable／wildcard／value pattern で扱えても，
そのことから内側の capability を生成しない．

```text
Rose a := node (List (Rose a))
```

では observability 方程式が `o = o` だけになり，least solution は `false` である．
有限の `Rose a` 値のどこにも `a` の payload は現れないので，この recursive-only
parameter は再帰的に隠された phantom と同じく unobservable になる．一方，

```text
Tree a := leaf a | node (List (Tree a))
```

では `leaf a` が seed を与えるので `a` は observable である．`node` の recursive
occurrence はその evidence を伝播・検証するが，新しい capability を無から作らない．

structured root evidence が一つもなければ matcher literal の capability は `•` と
する．root `K` を観測した後，`Obs_K(i) = true` の位置が `unseen` のままなら型エラー
とし，`Obs_K(i) = false` の位置は canonical `•` で埋める．例えば `Maybe a` の `a`
は `Just a` により宣言上 observable なので，`Nothing` のように `a` を確定しない
constructor clause しかなければ，target 型や annotation から capability を作らず
拒否する．`Nothing` が `unseen`，`Just $` が `p` を与える場合は `unseen` が中立なので
`Maybe p` となる．一方，`Phantom a`，opaque 内部だけの `a`，seed のない
recursive-only `a` は canonical `•` となる．

**refinement interception．** refinement は general clause より前に選択され得るため，
合成から単に無視しても安全ではない．例えば general clause がある child 位置へ `p`
を公開する一方，先行 refinement が同じ位置の hole を `something : •` へ渡すと，
`p` が structured capability である利用時に refinement が pattern を先取りして
stuck し得る．exact merge は `p` と `•` の不一致としてこの定義を拒否する．
wildcard／value 固定位置には successor がないので `unseen` とし，他の証拠を
不必要に弱めない．

refinement が general の `p` に加えて固定 shape `K κ̄` だけを処理する場合，実際の
accepted-pattern language は `p` とその固定 shape の順序付きの和に近い．現在の
capability 文法には `p ∨ K κ̄` がなく，単純な union では nested path，複数 hole
間の相関，clause priority も表せない．初期版はこの場合を exact mismatch として
拒否する．したがって主要性は，runtime が処理できる全 pattern language に対する
完全な主要性ではなく，union を必要とする不一致を拒否するこの exact-evidence
calculus に相対的な一意性／主要性として述べる．

**Coverage との境界．** refinement-only clause は structured `ShapeCap` を生成できる
が，`CoverageOK` に数えるのは従来どおり general clauses だけである．例えば
`$ :: _` だけを持つ `headSlot` は `List •` を持てるが，general cons clause を
欠くため Coverage warning の対象であり，no-stuck を主張する安全な部分集合には
入らない．

**形式化・証明として残ること．**

- 上記 projection judgment と exact merge の Lean／論文上の帰納的定義
- projection と merge の決定性，clause／field 順序独立性，健全性
- exact-evidence calculus に相対的な一意性／主要性の定理
- D5 で決める signature normalization 境界を projection の head equality へ接続する

**完了条件．** signature-directed な投影を含む合成が決定的で，annotation や target
型から capability を作らず，catch-all-only が必ず `•` になり，observable position
の未確定と exact mismatch を拒否し，unobservable position を canonical `•` とし，
採用する相対的主要性命題を明示して示せること．

### D2：型付けと `CoverageOK` を運ぶ二層の形式化（設計方針決定済み）

**決定．** coverage だけを切り替える mode を置き，式，値，環境，matching state の
全判断へ同じ mode を通す．

```text
q ::= ordinary | covered

CoverageReq ordinary cls κ = True
CoverageReq covered  cls κ = CoverageOK cls κ
```

式を含む `HasTy_q`，`ClauseTy_q`，`ArmsTy_q`，`ClausesTy_q`，`PatTy_q`，
`PatTys_q`，`SigFWF_q` は同じ `q` で再帰する．式を含まない `PPTy` と `PDTy` は
mode 非依存のままとする．matcher literal の規則は概念的に次の形に分ける．

```text
MatcherWF_q Γ cls κ τ
CoverageReq q cls κ
────────────────────────────────────
Γ ⊢_q matcher cls : Matcher κ τ

MatcherWF_q Γ cls κ τ :=
  ClausesTy_q Γ cls κ τ
  ∧ ShapeCap cls κ
  ∧ CatchAllLast cls
  ∧ ArmExhaustive cls τ
  ∧ PPBindNodup cls
  ∧ ArmBindNodup cls
```

したがって `ordinary` は partial matcher を structured capability のまま受理し，
`covered` は同じ導出の全 matcher literal に `CoverageOK` を追加要求する．warning
の有効・無効はどちらの導出，capability，`CoverageOK` 証拠にも影響しない．
`covered` は，partial matcher を作るが実行しない branch も拒否する保守的な
syntactic subset とする．安全性定理へ高階の使用点解析を持ち込まないための
意図的な境界である．

**coverage 非依存の最終 catch-all．** 現行 Lean の `holeAfterGenerals` は
Coverage が要求する全 general clause を各 bare-hole より前に要求するため，mandatory
catch-all と組み合わせると partial matcher を受理できない．また，複数 bare-hole や
bare-hole 後の refinement を直接禁止していない．これを削除し，R3 の条件をそのまま
表す次の判断へ置き換える．

```text
CatchAllLast cls :=
  ∃ prefix M x N,
    cls = prefix ++ [(hole, M, [(var x, N)])]
    ∧ ∀ cl ∈ prefix, cl.pp ≠ hole
```

すなわち，単一変数 arm を持つ canonical bare-hole catch-all が唯一の bare-hole
かつ最終節である．`CoverageOK` と `CatchAllLast` から，必要な general clause が
bare-hole より前にあるという従来の順序補題を導く．arm exhaustiveness と二種の
`Nodup` も通常型付けから外さない．refinement が general clause より前で発火する
場合の successor 整合は D1 の exact merge が担う．

**`CoverageOK` の範囲．** `CoverageOK cls κ` はその literal の root coverage
だけを表す．

```text
CoverageOK cls •

CoverageOK cls (K κ₁ ... κₙ)
  iff K の canonical pattern signature に属する全 constructor c について
      general clause c $...$ が cls にある

CoverageOK cls (κ₁, ..., κₙ)
  iff 対応 arity の general tuple clause ($, ..., $) が cls にある
```

D1 finalization 後の literal root は `•`，既知 head，product のいずれかでなければ
ならないので，flexible root meta-variable の規則は置かない．`CoverageOK` は
capability の子へ再帰しない．分解後に得る next matcher 自身の covered value typing
が子の安全性を担う．refinement clause は従来どおり数えない．
`Matcher • (List a)` の `CoverageOK` は空虚でも，独立な target-based warning は
`List` の未被覆 constructor を引き続き報告できる．

**runtime への再帰的な輸送．** root matcher 値へ `CoverageOK` を一枚足すだけでは
不十分である．次の判断も mode-indexed にする．

```text
ValueTy_q
EnvTyped_q
SubstTyped_q
MatcherOK_q
WTTree_q
WTStack_q
WTState_q
```

`covered` では，data／tuple 内の全成分，product matcher の全成分，slot の元 matcher，
closure の body と captured environment，matcher literal の定義環境を再帰的に
covered とする．`something` は capability `•` なので covered である．
`EnvTyped_covered` は環境にある各 scheme の全 instance が `ValueTy_covered` を
満たすことを要求する．外部 primitive／trusted environment にも同じ certificate を
要求し，通常の `ValueTy` だけを covered derivation へ注入する規則は置かない．

例えば，外側の `list` matcher の root が fully covered でも，element slot に
`Nil` clause を欠く partial matcher を渡せば，分解後の `Nil` pattern がその matcher
へ届いて stuck する．したがって `MatcherOK` だけを強め，通常の `EnvTyped` や
slot-value invariant を再利用する案は採らない．

**通常層では matching-state Preservation も一般には成り立たない．** 二つの
nullary constructor `A`，`B` を持つ `T` に対し，

```text
partialT =
  matcher
    | A as () with
        | $tgt -> [()]
    | $ as something with
        | $tgt -> [tgt]
```

は `A` により `T`-headed `ShapeCap` を持つが，`B` の general clause を欠く．
`ordinary` では受理される．`B` pattern へ適用すると，`A` 節の失敗後に final
catch-all が成功し，

```text
⟨B-pattern, partialT, B-value⟩
  → ⟨B-pattern, something, B-value⟩
```

という一歩は存在する．しかし後続 atom では `something` の `•` が `T` constructor
要求を満たさず，well-typed state でなく，次の step もない．したがって通常層には
Progress だけでなく，無条件の matching-state Preservation も主張しない．

通常層に残す定理は，完了した big-step evaluation に対する partial correctness と，
既存 Lean の `ExclInv` に相当する局所条件を明示した次の保存である．以下の表示では
coverage だけの差を見せるため，R10 の非 Coverage 前提，すなわち P1 の
`CaptureAdm(D)`／型付き evaluation oracle，signature well-formedness，fresh-leaf
reachability，pattern-function／scheme instance／clause typing の輸送を
`BaseAdm` にまとめて書く．P2 が放電するのは従来の capability-admissibility であり，
これらを同時に無条件化するものではない．

```text
Γ ⊢_ordinary e : τ
ρ ⊨_ordinary Γ
Eval ρ e v
BaseAdm(Eval derivation)
────────────────────
ValueTy_ordinary v τ

Step s ss
WTState_ordinary s
DispatchOK s
BaseAdm(Step derivation)
────────────────────────────
∀ s' ∈ ss, WTState_ordinary s'
```

`DispatchOK` の matcher-atom case は，constructor／tuple pattern に対応する general
clause が現在の接尾辞で bare-hole より前に残ることを要求する．state-level では
step derivation を再帰して MNode 内部の現在の atom にも同じ局所条件を要求する．
これは既存 Lean の atom-level `ExclInv` を MNode step まで持ち上げる定義である．
普通の partial matcher でも，実際に covered な shape だけを通る局所 step には
この定理を使える．現在の
「全 step の型付き state 保存」を経由する big-step proof は通常層には使えないため，
完了した `Search` 導出へ直接帰納する partial-correctness proof に組み替える．

**安全層の定理．** pattern typing／one-way compatibility により現在の pattern head
が matcher capability から到達することを示した上で，
`CoverageOK + CatchAllLast` から `DispatchOK` を導く．runtime の covered invariant
から各 successor matcher の covered 性を得る．したがって，R10 の同じ
`BaseAdm` の下で次を `covered` だけに主張する．

```text
Step s ss
WTState_covered s
BaseAdm(Step derivation)
──────────────────────────
∀ s' ∈ ss, WTState_covered s'

WTState_covered s
s is nonterminal
CaptureAdm s
StepTotal s
BaseAdm(progress interfaces)
────────────────────
∃ ss, Step s ss
```

reachable-state safety，terminal substitution typing，Type Safety も covered
subset に限定する．P2 実装後は capability-admissibility を前提から除くが，P1 の
capture-admissibility と `StepTotal` は残る．branch list が空であることは従来どおり
正当な match failure である．

**実装・証明として残ること．**

- `covered` から `ordinary` への derivation erasure
- `CoverageOK` の決定性，target substitution 不変性，finalized root を保つ
  capability substitution での保存
- pattern typing／one-way head compatibility と `CoverageOK + CatchAllLast` から
  `DispatchOK` を導く補題
- mode-indexed fundamental theorem と全到達 matcher の covered 性
- ordinary completed-evaluation partial correctness と `DispatchOK` 付き局所保存
- covered state Preservation，Progress，Type Safety
- 上の `partialT` と，covered outer／partial child の Lean 回帰
- Egison の strict covered checker／certificate の soundness

現行 Egison は default ordinary checker として，Coverage を opt-in warning，
catch-all 後の clause と top-level arm 非網羅を hard error にしている．ただし
`inferInMatcherBody` 中では Coverage warning だけでなく arm exhaustiveness まで
抑制しているため，nested／generated matcher でも後者を通常 error に直す必要がある．
また，現在は bare-hole の存在と位置だけを検査しており，canonical
`CatchAllLast` の単一 variable arm 全体はまだ検査していない．warning の結果は
covered certificate として使わず，capability finalization 後の semantic
`CoverageOK` を全 nested literal へ hard condition として検査する．さらに，高階
引数，imported value，trusted primitive は literal 走査だけでは足りないので，
mode-indexed scheme／`EnvTyped_covered` certificate を module boundary で要求する．

**完了条件．** 上記二 mode，coverage 非依存の `MatcherWF`，再帰的 runtime
invariant，通常層の partial correctness／条件付き局所保存，covered 層の
Preservation／Progress／Type Safety が定義されていること．設計判断はここまでで
固定し，残りは形式化・実装課題とする．

### D3：二種 HM generalization と substitution threading（設計方針決定済み）

**決定．** capability 変数の一般化に provenance 付き `CapGen` は導入しない．
capability／type の sort を分けたまま，通常の HM generalization を両方へ適用する．
Algorithm W の各規則は `S_κ` と `S_τ` を返して合成し，結果型，環境，残余制約，
後続推論の全 occurrence へ適用した後にだけ `Gen` を行う．scheme instantiation は
量化変数を fresh flexible meta-variable にし，明示 `forall` annotation の本体検査は
fresh rigid skolem を用いて escape を禁止する．

matcher literal では，根拠のない observable `unseen` と evidence-free な root
meta-variable を D1 の finalization で拒否する．next matcher／入力の evidence に
支えられた capability 変数は同じ variable identity を保って structured root に残せる
ため，外側の関数で通常どおり一般化できる．再帰 binding は通常の HM 規則どおり
SCC 内で単相に保ち，D4 の generation solution と全 substitution を適用して
finalization した後，SCC の外側で一般化する．
D4 の producer-flow summary は generation dependency の経路を計算する補助 judgment
であり，量化候補を選別しない．SCC-local `Rec` node は finalization 前に消えるため，
一般化用 provenance を scheme へ残さないという本節の決定を変更しない．

`list something` で得る `p ↦ •` は Algorithm W の返却 substitution なので，
generalization 前に結果の全 occurrence へ適用される．したがって `p` は自由変数として
残らず，特別な `CapGen` で除外する必要はない．反対に，

```text
bad : ∀p a. Matcher p a
bad = something
```

は annotation の `p` が rigid skolem なので拒否される．matcher identity と
`∀p a. MatcherSlot p a -> Matcher (List p) (List a)` は，通常の parametric な
二種 HM scheme として一般化できる．

**Lean で検証すること．** 二種 substitution の kind preservation・合成・相互非干渉，
W が返す substitution の全 occurrence への伝播，二種 `Gen`／`Inst` の健全性，
annotation skolem の non-escape，`EnvTyped` が scheme の全 instance を満たすこと，
Algorithm W の健全性・完全性・最汎性を示す．そこから `mPoly`，`f`，
`list something`，let，高階関数，tuple，データ格納を通した到達可能な matcher value の
能力非強化と，P2 に由来する `capability-admissible` 仮定の除去を導く．

一般再帰による発散項が任意型を持ち得ても，matcher value を生成せず到達しない限り
能力偽造の反例ではない．主張するのは「危険に見える scheme が構文上まったく導出
不能」ではなく，「到達可能な matcher value が生成時の capability を超えない」
ことである．この簡潔な体系で Lean 証明が失敗する具体的反例が得られた場合に限り，
必要な最小範囲の provenance／一般化制限を再検討する．

**完了条件．** 上記の W／Gen／Inst／skolem の定義と証明により，正当な capability
多相を保ったまま全 value-flow 経路で到達可能な matcher value の能力強化を拒否し，
`capability-admissible` 仮定を除去できること．

### D4：再帰 matcher の capability 推論（設計方針決定済み）

**決定．** 再帰 binding 自体には，通常の HM の単相再帰規則をそのまま使う．
capability 注釈を必須にせず，多相再帰も導入しない．各 recursive binder は SCC 内で
一つの fresh な単相 full-type placeholder を持ち，lookup のたびに instantiate
し直さず同じ meta-variable identity を返す．全 RHS の通常型付け，通常等式の解決，
matcher literal 固有の `ShapeCap` finalization が終わるまで一般化せず，SCC の外側で
だけ D3 の通常の二種 HM generalization を行う．

D4 固有の追加物は再帰型推論規則ではなく，matcher literal が生成する一時的な
**Shape generation obligation** と，それを value flow に沿って運ぶ補助 summary である．
通常の capability 等式と generation dependency を次のように分離する．

```text
ordinary equality:       κ₁ ~ κ₂
Shape generation:        g ← d

g ::= producer-id × capability-path
d ::= unseen
    | Known κ
    | Ref g
    | K d₁ ... dₙ
    | (d₁, ..., dₙ)
    | join(d₁, ..., dₙ)
```

`ordinary equality` は通常の二種 MGU で解く．一方，`g ← d` は「producer/path `g` が
どの証拠から capability を生成したか」を表す向き付き制約であり，等式として MGU へ
渡さない．`Ref g` は同じ generation graph 内の producer/path への dependency，
`Known κ` は SCC の外から実際に渡された matcher 値，matcher-valued な trusted
scheme から instantiate した producer，非再帰 matcher，または現在の SCC 仮定に
依存せず構成済みの child matcher から来た evidence である．`join` は同じ位置へ
到達する複数の返却経路を D1 の exact merge で合成する．function-valued scheme は
下記の `Φ` を application して origin を決める．`Rec` は `Φ` の正規化前だけにある
SCC-local な印で，型，scheme，typed AST には残さない．したがって D3 で不採用とした
一般化用 provenance とは異なる．

各 matcher literal について，少なくとも root capability placeholder，D1 の
observability mask，evidence とその source を持つ obligation を作る．生成中の
root/path placeholder は protected node とする．consumer demand，RHS の期待型，
結果注釈を full type の構造に沿って分解し，**protected capability position を
具体化しようとする成分だけ**を deferred demand として記録する．target 成分，
protected でない capability 成分，rigid skolem の scope check は通常の W で直ちに
処理する．deferred demand を `Known` evidence に変換してはならない．finalization 後に
producer capability を固定し，その結果に対して deferred demand を通常の
one-way／capability equality で検査する．consumer 側の flexible variable はこの
最終検査で解いてよいが，finalized producer を consumer に合わせて強化してはならない．

constraint-generating judgment と解決順は，概念的に次の形へ固定する．

```text
Γ ; R ⊢ e ⇒ τ ; Φ ⊣ (Ceq, Gshape, Cresid)
S  = mgu₂(Ceq)
E  = μ_unseen(S · Gshape)
κ̄  = Finalize(E)
S' = check₂(S · Cresid[κ̄/ḡ])
```

`R` は現在の再帰仮定，`mgu₂`／`check₂` は capability／type の二種 solver，
`Φ` は下記の producer-flow summary，`Cresid` は protected node へ向いた demand である．
`S · Gshape` は `Known` 内の通常 meta-variable へ substitution を適用するが，
`Known`／`Ref` の区別と producer/path identity を消さない．宣言的な
`T-MATCHER` では，clause judgment が返す `Gshape` の least solution と finalization を
premise にして
`Matcher κ τ` を結論し，`T-FIX`／`T-REC` 自体は通常の単相規則のままとする．

**producer-flow summary と再帰 knot．** 型だけでは producer origin を復元できない．
例えば，

```text
chooseFirst  : Matcher p a -> Matcher p a -> Matcher p a
chooseSecond : Matcher p a -> Matcher p a -> Matcher p a
```

は同じ型を持ち得るが，結果が第1引数と第2引数のどちらに由来するかは異なる．
したがって「結果の `p` と同じ型変数を持つ全引数を seed に数える」という近似は，
無視された Known 引数から再帰結果へ偽の seed を注入し得るため採用しない．

通常の expression typing の各規則に，型とは別の補助出力 `Φ` を持たせる．`Φ` は
matcher-bearing な各結果位置について，概念的に次の producer flow を表す．

```text
φ ::= unseen
    | Arg(i, path)
    | Captured(x, path)
    | Known κ
    | Literal g
    | Rec b
    | K φ₁ ... φₙ
    | (φ₁, ..., φₙ)
    | join(φ₁, ..., φₙ)

Φ ::= φ | flow-lambda(ports, Φ)
```

`Φ` をそのまま `Gshape` の右辺には置かない．現在の再帰 node 集合 `R` と producer
port 環境 `Δ` に相対的な正規化 judgment

```text
R ; Δ ⊢ Φ(path) ⇓ d
```

を挟む．`Δ` は `Arg`／`Captured` を実引数の summary または
`external(κ)` port へ写す．実引数 summary は再帰的に代入し，外部 matcher input の
`external(κ)` は `Known κ`，`Rec b` は `Ref b`，`Literal g` は `Ref g` へ正規化する．
constructor／tuple／`join` は同じ構造を保って各 child を正規化する．`flow-lambda` は
application rule で実引数を代入してから正規化し，matcher-bearing な結果 path に
未適用の `flow-lambda` を残さない．これにより symbolic flow と solver が扱う
first-order evidence `d` の境界を固定する．

variable／lambda／application／let／tuple／constructor の `Φ` 規則は，それぞれの通常の
型推論規則と同じ構文再帰に置く．lambda は matcher-bearing な引数位置を symbolic
`Arg` port とする transformer を作り，application は実引数の `Φ` をその port へ
代入する．したがって `idM (f x)` は `Rec b`，`list (f x)` は
`List (Rec b)`，`chooseSecond (f x) m` は第2引数 `m` の origin になる．branch／複数の
返却経路は `join` として generation obligation へ送り，D1 の exact agreement で解く．
function-valued な引数 port は `flow-lambda` 自体を受け取り，高階 application でも同じ
substitution を再帰的に行う．

nonrecursive binding の型スキームには，user-visible な型を変えず，parametric な
flow transformer を compiler／形式化用環境で対にして保持する．type scheme と同じ
producer port identity を保って instantiate するが，`Φ` は量化候補の選別には使わない．
これは D3 で不採用とした `CapGen` ではない．trusted primitive／foreign function には
型スキームだけでなく，結果 producer がどの引数／既知 producer に由来するかを示す
trusted flow summary を要求し，`EnvTyped` でその summary の健全性を仮定・検証する．
current SCC の `Rec`／`Literal g` は解決後に `Known` または通常の symbolic port へ
置換し，generalization point から escape させない．

概念的な `FlowOK(σ, Φ)` は，`Φ` の各 port/path が `σ` の同じ full
`Matcher κ τ` occurrence を指すこと，結果の全 matcher-bearing path に flow があること，
量化された結果 capability を入力 port／captured producer／finalized literal の
いずれにも由来しない裸の `Known` として導入しないこと，`Rec`／未解決
`Literal g` が scheme scope へ出ないことを要求する．`K` transform は capability
側だけの印でなく，同じ canonical former transform を target occurrence にも適用した
pair として記録する．別補助条件 `FlowTargetOK(σ, Φ, Ξ)` は，各 port substitution 後の
`(κ,τ)` が D5 の context-relative `CapTargetOK` を満たすことを要求する．これにより
producer origin を保っても capability と対応 target の組を失わない．source definition
から得た summary には補助 judgment から `FlowOK` と `FlowTargetOK` を導き，
primitive の summary には mode-indexed `EnvTyped` の trusted premise として同じ条件を
要求する．`FlowTargetOK` は既に得た pair の整合を検証するだけで，target occurrence
から `Known κ` や Shape seed を生成しない．

recursive binder `xᵢ` の matcher-bearing な結果 path ごとに auxiliary node
`bᵢ,π` を置く．RHS の summary を `Φᵢ` とすると，まず

```text
R ; Δ ⊢ Φᵢ(π) ⇓ dᵢ,π
```

を求め，次を加える．

```text
bᵢ,π ← dᵢ,π
```

この制約を **generation copy／transform edge** として `Gshape` に加える．これは
placeholder と RHS の通常等式や deferred consumer demand ではない．再帰 lookup は
`Rec bᵢ,π` を返すため，`f = g`／`g = seededLiteral` の seed はこの knot を通って
`f` へ伝播する．binder node は補助 node であり，matcher literal に接続されない
`f = f` だけの cycle 自体には observable finalization obligation を課さない．
この binder-only cycle の least solution が `unseen` なら，外へ保存する `Φ` も
`unseen` に確定し，任意型へ一般化された発散項を後続 literal の seed として使えない．
通常型の HM generalization 自体は妨げない．

**何を seed と数えるか．** 現在の SCC の再帰名を lookup した結果は常に `Rec` であり，
直接の自己呼出しだけでなく，

```text
let g = f in ...
idM (f x)
```

のような alias，application，高階関数を通る場合も，同じ origin を capability
identity に沿って保存する．単に通常の型を最後に zonk して既知 head が現れたかを
調べる実装では，consumer demand で具体化された型を seed と誤認するため不十分である．
非再帰 combinator が再帰結果を包む場合は，例えば `List (Rec b)` のように，新しく
構成された外側の head と再帰 dependency を区別して保持する．

SCC 外の入力 `m : Matcher p a` を literal の hole に実際に渡せば，`Known p` という
正当な seed になる．`p` が flexible meta-variable でも，これは実行時に caller から
capability を持つ matcher 値を受け取るという evidence であり，finalization 後に外側で
通常どおり一般化できる．一方，結果へ `Matcher p a` と書いただけの annotation，
target 型，利用位置の constructor demand は matcher 値を提供しないので seed ではない．
明示された matcher 引数を本体で実際に使うことと，注釈だけで結果能力を宣言することを
区別する．

**Algorithm W との合成．** 現行 Lean core の singleton
`fix f x. e` では，概念的に次の規則を使う．

```text
α, β fresh
ΓR = Γ, x : mono α, f : mono (α -> β)
W_R(ΓR, e) = (S₀, τ, Φ, G, D)
U  = mguOrd(S₀ β, τ)
S₁ = U ∘ S₀
G₁ = G ∪ knot_{R,Δ}(b_f, Φ)
Q  = solveShape(S₁ G₁)
S₂ = checkFinal(S₁, Q, D)
------------------------------------------------------------
W(Γ, fix f x. e) =
  (S₂ ∘ S₁, (S₂ ∘ S₁)(α -> β))
```

ここで `G` は generation obligations，`D` は protected node へ向いた deferred
demands である．`mguOrd` は target と protected でない capability に通常の二種 MGU
を使い，protected root/path に触れる比較だけを `D` へ分離する．`W_R` の `R` は現在の
再帰仮定集合であり，`b_f` は `f` の matcher-bearing な結果 path の binder node，
`knot` は `Φ` を `R ; Δ ⊢ Φ ⇓ d` で正規化して作る上記の binder–RHS generation edge
である．型環境 `ΓR` と対になる flow 環境は `x` を symbolic `Arg` port，`f` の
matcher-bearing な結果 path を `Rec b_f` へ写す．`f` の lookup は fresh instantiate を
行わない．`fix` 規則の内部で `Gen` は行わない．宣言的には現行の単相
`HasTy.fixE` の形を維持し，matcher literal の型付けに finalized `ShapeSolved` side
judgment を接続する．型全体を capability 専用の別規則でもう一度推論する必要はない．

一般の相互再帰 binding 群 `x₁ = e₁, ..., xₙ = eₙ` は，同じ規則の SCC 版とする．

1. 実際の binding dependency graph を作り，SCC ごとに処理する．
2. SCC 内の全 binder に fresh な単相 full-type placeholder `β₁, ..., βₙ` を置く．
   明示 annotation があればここで一度だけ rigid skolem を導入し，target／protected
   でない capability 成分を通常制約へ，protected capability 成分だけを deferred
   demand へ送る．annotation から generation evidence は作らない．
3. 同じ単相環境の下で各 RHS を通常の W で推論し，producer-flow summary `Φᵢ` も得る．
   実装が逐次処理する場合は，先の RHS が返した二種 substitution を，次の RHS，
   placeholder 環境，flow summary，残余制約へ毎回 thread する．SCC 内では
   scheme instantiation／generalization を行わない．
4. `βᵢ` と RHS 型の通常部分を二種 MGU で解き，protected node に関する比較を保存する．
   各 matcher-bearing path で `R ; Δ ⊢ Φᵢ(π) ⇓ dᵢ,π` を求め，
   `bᵢ,π ← dᵢ,π` を generation obligations に加える．
5. 通常 substitution を型，環境，`G`，`D` の全 occurrence へ適用してから，SCC 全体の
   `G` を同時に least solution まで解く．
6. observable／unobservable mask に従って finalization し，finalized capability を
   placeholder，consumer demand，annotation に照合する．
7. 全 substitution を型，環境，残余制約，typed AST へ完全に適用した後，SCC の外側で
   各 binding を通常の HM 規則により一般化する．

この処理は型検査を二回行う規則ではない．実装がデバッグ用 assertion として
finalized typed AST を再検査することはできるが，W が集めた制約の健全性と全代入の
threading が正しければ必須の第2 pass は不要である．

**least-evidence solver．** 各 SCC-local `g` を初期値 `unseen` とし，`Ref g'` を
dependency edge，`Known κ` と非再帰に構成された head を incoming evidence として
D1 の exact merge を worklist で伝播する．通常 substitution を先に適用した後も，
`Known` 内の HM capability variable は Shape solver が勝手に単一化する flexible node
ではなく，exact merge 上の identity を持つ atom として扱う．独立な通常等式によって
すでに同一化済みの場合だけ同じ evidence になる．以下では `Ref`／`Known` を省略して
dependency と seed を簡記する．基本例は次である．

```text
g ← g                         => g = unseen
g ← p,  g ← g                => g = p
g₁ ← g₂, g₂ ← p              => g₁ = g₂ = p
g ← p,  g ← q                => exact mismatch
g ← List g                   => occurs-check error
```

最初の行は恒等等式を解いたという意味ではなく，seed のない generation cycle の
least solution が `unseen` だという意味である．その位置が宣言上 observable なら
finalization で型エラー，unobservable なら canonical `•` になる．2行目では
非再帰 `p` だけが seed で，自己参照は伝播辺にすぎない．4行目の `p` と `q` は
通常等式ですでに同じ identity になっていない限り不一致である．5行目のような
structural-growth cycle は有限な capability tree を持たないため occurs check で拒否する．
相互 alias cycle も同様に seed がなければ `unseen` のままであり，一方へ seed が入れば
全 dependency node へ伝播する．

初期実装では identity／copy edge の SCC を先に collapse し，残った dependency cycle が
constructor または product context を一つでも含めば expansive cycle として拒否する．
acyclic な constructor／projection transform は topological order で評価する．node 数と
入力 evidence の有限な subterm 集合に対する高さ有限の計算になるため，探索回数上限を
置かず停止する．`unseen` を bottom，同じ head を pointwise に並べ，exact merge が
定義される範囲では least solution は一意である．
canonical な producer/path ID，成功時に可換・結合的な exact merge，通常 MGU の
最汎性により，clause 順と SCC 内 binder 順に依存しない結果を要求する．この停止性，
最小性，決定性，順序独立性は実装上の探索上限ではなく定理として示す．

ここには二つの異なる least fixpoint がある．pattern declaration から計算する D1 の
parameter observability は Boolean dependency graph を解き，「その parameter が
宣言上観測可能か」を決める．D4 の solver はプログラム中の recursive matcher SCC
について partial evidence を解き，「実際の literal がどの capability を生成したか」を
決める．前者の再帰辺も後者の `Ref` 辺も単独では seed を作らないが，同じ解析ではない．

**annotation と通常の発散項の境界．** capability annotation は任意であり，明示
`forall` を D3 の rigid skolem として SCC 全体で一度検査し，再帰 lookup ごとに
instantiate しない．Shape finalization 後の推論結果を annotation へ照合するだけなので，
annotation あり／なしで producer capability は変わらない．annotation があれば受理される
seedless literal は作らない．structured root clause が一つもない literal は再帰側の
demand にかかわらず `•` であり，root `K` を観測した literal だけに D1 の
observable／unobservable finalization を適用する．

一方，

```text
let rec x = x
fix f x. f x
```

のように matcher literal を一つも生成しない通常の発散項には Shape obligation 自体が
ない．これは通常の HM 再帰として任意型を持ち得るが，到達可能な matcher value を
生成していないため seed 不足として拒否しない．seedless error を課すのは，実在する
matcher literal の structured root 以下で D1 が observable とした位置だけである．
到達不能な branch 内の matcher literal も，通常の静的型検査と同じく検査対象である．
Coverage warning の有効・無効も `G`，least solution，finalized capability を変更しない．

**Lean／Egison の境界．** Lean は現在 `Expr.fix f x e` という singleton の単相再帰だけを
持つため，まず上の singleton W 規則と solver の一般部分を機械化する．相互 SCC に
固有の定理は，Lean の式構文を拡張するまで要求しない．Egison では実際の dependency
graph から SCC を作り，同じ規則を複数 binding に適用する．現行
`inferIRecBindingsWithContext` の独立な `mapM` と後置的な substitution 合成は，
RHS 間へ substitution を thread する joint SCC inference に置き換える．matcher literal
だけを恒久的に単相化する分岐は削除し，Shape finalization 後は他の binding と同じ
generalization を使う．固定回数で代入を適用する `applySubstRecursively ... 5` は，
occurs check 済みの acyclic substitution を完全に zonk する処理へ置き換える．

**形式化・証明として残ること．**

- singleton `fix` に対する二種 W の健全性，完全性，主要性と mono lookup identity
- Shape solver の停止性，健全性，完全性，最小性，決定性，順序独立性
- seedless cycle の非生成，seed propagation，exact mismatch，structural occurs check
- target substitution に対する generation obligations の不変性，通常 capability
  substitution と Shape solution の合成保存
- protected node／`Rec` の non-escape，finalization-before-generalization，
  annotation／consumer demand の non-seeding
- well-formed／`FlowOK` な入力に対する producer-flow normalization
  `R ; Δ ⊢ Φ ⇓ d` の全域性，決定性，port substitution preservation，
  `Rec`／`Literal` から `Ref` への source preservation
- 再帰を含む到達可能な matcher value の capability 非強化

**完了条件．** 標準再帰 matcher の capability が D1 の exact-evidence calculus に
相対的に principal かつ annotation なしで一意に推論され，自己参照，結果注釈，
consumer demand から能力を循環的に捏造できず，annotation あり／なしの推論結果が
整合すること．Lean core の singleton 規則について上記性質を証明し，Egison の
相互再帰 SCC について同じ solver と回帰を実装すること．

### D5：`CapTargetOK` の正規化境界

#### D5-core：構文的 canonicalization（設計方針決定済み）

**決定．** `CapTargetOK`，capability constructor equality，`ShapeCap`，
`CoverageOK` は，同じ frozen canonical signature environment `Σ̂` を使う．
`CapTargetOK` と `ShapeCap` が比較するのは canonical **type-former ID と arity**，
`CoverageOK` が列挙するのは `Σ̂` がその former に対応付けた
**pattern-constructor ID** の集合であり，両 ID を混同しない．一般の unifier が行う
normalization を呼ばず，name／kind elaboration の一部として専用 allowlist
`reprNF_A` を解決し，Algorithm W と signature 登録を始める前に canonical form へ
落とす．`A` は compilation unit の全宣言を収集して検証済みの transparent alias
environment である．

`reprNF_A` に含めるのは次だけである．

1. closed，kind／arity-correct，acyclic な nullary transparent alias の完全展開
2. surface syntax が最初から同じ core constructor を表す固定 synonym の除去
3. 上記を型の引数へ再帰的に適用する純構文的 canonicalization

現在の Egison では，例えば list syntax を `TCollection`，`Vector`／`Matrix`／
`DiffForm` syntax を `TTensor`，builtin spelling を対応する固有 ADT node へ落とす
変換がこの allowlist に当たる．この表は明示的に管理し，既存の
`normalizeInductiveTypes` や unifier の normalization へ将来 rewrite が増えても
自動では拡張しない．`normalizeTensorType` の
`Tensor (Tensor a) ↦ Tensor a` も初期版には含めない．

次は `reprNF_A`，canonical head equality，`CapTargetOK` のいずれにも含めない．

- CAS `groundEquiv`
- `declare cas-subtype`，join，widening／narrowing，reshape
- type-class constraint や `Coerce` instance による同一視
- quotient，equational theory，semantic rewrite
- pattern signature との対応証明を持たない tensor／inductive normalization

これらを通常の「型として単一化できる」という事実から capability equality へ
持ち上げてはならない．同じ値表現または変換経路を共有することと，同じ pattern
constructor language を分解できることは別である．

capability sort 自体には surface type alias／`cas-type` alias を許さない．capability
constructor は `Σ̂` の canonical type-former ID だけを持つ．例えば target alias
`A = List Integer` は name／kind elaboration 中に signature と target から展開され，
capability 側では `A` という head を作らず，canonical `Collection` head を用いる．
imported scheme／signature も canonical form を保存し，後の alias 宣言で再解釈しない．

**alias environment の検証．** 現行 `resolveCasTypeAliases` の「置換が固定点になったら
成功」という条件だけでは，`A = A`，`A = B; B = A`，未宣言の `B` を残す定義を
安定な固定点として受理し得る．Algorithm W を始める前に alias dependency graph を
作り，DFS／SCC で自己 cycle と相互 cycle を拒否し，nullary alias body に未束縛の
型変数または未知 head が残らないことを検査する．nullary alias を引数へ適用する
`A τ` は arity error とする．builtin，data former，pattern former，nominal quotient
との名前衝突も拒否する．現行の nominal quotient 用
`Q ↦ TInductive Q []` は transparent alias と別 tag／namespace entry に分け，
alias SCC 検査で自己 cycle とみなさず，展開もしない．検証後に完全展開し，
`reprNF_A` の停止性，冪等性，kind 保存，**canonical range を持つ substitution**
との可換性を示す．alias 名と HM type variable を同じ未解決 `TVar` として推論へ
渡さない．

**open な `CapTargetOK`．** `CapTargetOK` はすべての型構文の formation condition
ではなく，到達可能な matcher／slot 値の不変量であるという既決定を維持する．
`list` のような open combinator を検査するため，入力の同じ mode で well-typed な
matcher／slot 値（`ordinary` でも `covered` でもよい）から得た対応を仮定集合 `Ξ`
に置く context-relative relation として定義する．

```text
(κ, τ) ∈ Ξ
────────────────
Ξ ⊢CT κ ≈ τ

────────────────
Ξ ⊢CT • ≈ τ

Ξ ⊢CT κᵢ ≈ τᵢ  for every i
────────────────────────────────
Ξ ⊢CT K κ₁ ... κₙ ≈ K τ₁ ... τₙ

Ξ ⊢CT κᵢ ≈ τᵢ  for every i
────────────────────────────────
Ξ ⊢CT (κ₁,...,κₙ) ≈ (τ₁,...,τₙ)
```

両側の `K` は `Σ̂` の同じ canonical ID である．裸の capability variable と target
variable を無条件に対応させる規則は置かない．`MatcherSlot p a` の実値が与える
証拠を `Ξ = {(p,a)}` として使えば，

```text
∀p : Cap. ∀a : Type.
  MatcherSlot p a -> Matcher (List p) (List a)
```

の本体を検査できるため，user-visible な `CapTargetOK p a` constraint を scheme へ
追加する必要はない．closed matcher literal と `something` は空 context の証拠を
得られ，全 component が空 context で整合する closed tuple／product も空 context で
合成できる．一方，`list` 本体の literal や slot 由来 component を含む
tuple／product は ambient `Ξ` を `ValueTy` の構成規則へ保存・合成する．
trusted primitive／foreign value は，`ordinary`／`covered` の双方で
`CapTargetOK` certificate を要求し，`covered` environment へ登録するときだけ
追加で D2 の Coverage certificate を要求する．

任意の独立な capability substitution `S_κ` と target substitution `S_τ` に対する
保存は偽である．例えば対応を仮定した `χ` と `α` を異なる structured head へ独立に
具体化できる．主張するのは，仮定を保つ **coupled substitution** に対する次の補題で
ある．

```text
Ξ ⊢CT κ ≈ τ
Ξ' ⊨ (S_κ, S_τ)(Ξ)
CanonicalRange_A(S_κ, S_τ)
────────────────────────────────────────
Ξ' ⊢CT S_κ(κ) ≈ reprNF_A(S_τ(τ))
```

ここで二番目の premise は，`Ξ` の各対へ二種 substitution を適用した結果が
`reprNF_A` した後に `Ξ'` で `CapTargetOK` を満たすことをいい，第三 premise は
capability range が canonical ID だけを，target range が alias-free canonical 型だけを
持つことをいう．closed／finalized matcher の target specialization，slot witness と
target MGU が作る整列済み substitution，同 mode の input 仮定を使う open combinator
をこの一つの補題の instance として示す．
通常 target substitution や consumer demand から capability を逆算する規則は
置かない．

**D5-core の実装・証明として残ること．**

- alias graph 検証と `reprNF_A` の停止性，冪等性，kind／arity 保存，可換性
- canonical signature environment の freeze と import 境界
- context-relative `CapTargetOK` の決定的な closed fragment
- coupled-substitution lemma と matcher／slot `ValueTy` からの証拠回収
- semantic normalization が canonical head equality へ混入しない回帰
- trusted environment certificate の検査

#### D5-CAS：target-indexed pattern-view signature（設計 blocker）

strict な D5-core は固定できるが，それだけでは現行 Egison standard library の全
matcher を移行できない．例えば `lib/math/expression.egi` の

```text
factor : Matcher Factor
term m : Matcher (Term a [..])
```

は，どちらも `inductive pattern MathValue` に宣言された constructor clause から
shape evidence を得る．現在の `groundEquiv` は `MathValue`，`Factor`，`Term` などを
slot matching で暗黙に同値扱いするが，これを capability equality に流用すると，
各 target が本当に処理できる pattern constructor 集合と child capability を区別
できない．

単純な directional relation `ViewHead MathValue Factor`／
`ViewHead MathValue (Term a)` を一枚追加しても不十分である．
`inductive pattern MathValue` の result は nullary `MathValue` なので，D1 の
result-slot projection は長さ 0 になる．そのため `term m` の coefficient matcher
capability `p` を result capability に保持できず，

```text
MatcherSlot p a -> Matcher (TermCap p) (Term a [..])
```

に相当する不変量を表せない．`TermCap` はここで必要になる view-specific capability
former の仮称である．target の `Term a atoms` は Type-kind の coefficient `a` と
SymbolSet-kind の `atoms` を持つが，現 capability grammar は Cap 引数しか持たない．
したがって view signature は target indices `(a, atoms)` から capability-visible
indices `(p)` への kind-aware projection も明示し，symbol-set index を capability
から消すか，mixed-kinded index を導入するかを決めなければならない．現行 field
signature も coefficient hole を
`MathValue` とするため，`term integer` の `integer : Matcher • Integer` と整列しない．

sound な最小拡張は，target-indexed な **virtual pattern signature** を canonical
signature environment に明示することである．概念的には，

```text
Term.term : a -> ... -> Term a atoms
Factor.symbol : ... -> Factor
```

のような view-specific signature を与え，D1 には通常どおり
`C : fields -> K ρ̄` を渡す．formal core と初期 Egison 移行では
view-qualified pattern-constructor ID を必須とし，unqualified spelling は `Σ̂` 上で
view が一意な場合だけ sugar とする．expected target や result annotation だけで
overload を選ばない．これにより annotation が capability の seed になることを防ぎ，
D1／D4 の annotation-free principality を保つ．field 型，constructor 集合，
Coverage，target-index projection は target-indexed signature table が決める．
各 entry には，runtime extraction が宣言 field 型を返す preservation certificate が
必要である．これは alias 展開や head normalization ではなく，CAS pattern signature
自体の再設計である．

初期案として次の境界までは固定する．

- `groundEquiv` または単純な `ViewHead` で穴を埋めない
- D5-core の canonical equality は strict なまま保つ
- `factor`／`term` など view mismatch を持つ CAS matcher は，証明付き
  target-indexed pattern signature が導入されるまで
  P2 の certified `ValueTy`／`EnvTyped`（ordinary／covered の双方）と
  trusted environment の外に置く．legacy runtime で動くことを型定理の証拠にしない
- 将来拡張は D1 の projection，D2 の Coverage，`CapTargetOK` の三者へ同じ
  canonical view signature を渡す

残る設計判断は，CAS 各 target の constructor 集合と field signature，Type／
SymbolSet など異 kind の target indices から capability-visible indices への projection，
現行の annotation-driven reshape から runtime extraction preservation をどう得るか
である．view-qualified ID という初期 resolution 境界は固定するが，この三点を決めずに
standard matcher 全体の `CapTargetOK` を主張することはできない．

**完了条件．** D5-core について上の normalization と coupled-substitution 性質を
形式化すること．D5-CAS について target-indexed signature interface，view-qualified
resolution，kind-aware index projection，`Factor`／`Term`／`Frac`／`Poly` の
signature instances と runtime preservation を定義し，standard matcher の全型が
strict canonical environment で
`CapTargetOK` と必要な `CoverageOK` を満たすこと．

### 実装時に選べる表現上の詳細

次は上記 D1--D4 と D5-core，および D5-CAS で既に固定した strict boundary を
変えない限り，P2 の意味論的な blocker ではない．

- capability syntax を専用 ADT にするか kind 付き型変数にするか
- capability binder／pretty-printer／エラー表示の表面構文
- 型付き中間表現に capability を残すか型検査後に消去するか
- current rigidity error を capability mismatch としてどう表示するか
- 二種 substitution／rename の内部データ構造
- SCC-local `ShapeVar`／`Ref` と正規化前の `Rec` origin を，明示 evidence node，
  origin tag，union-find のどれで保持するか
- finalized typed AST の再検査を debug assertion として実行するか

## 実装順

1. capability syntax／kind と二添字 `Matcher`／`MatcherSlot` を追加する．
2. free variables，二種 substitution，全代入適用後の generalize，scheme instantiate，
   annotation skolem checking の単体回帰を作る．
3. D5-core の alias graph 検証，allowlist `reprNF`，canonical type-former／
   pattern-constructor ID，frozen signature environment を実装する．
4. producer equality と `COERCE-MATCHER-TO-SLOT` を二成分化する．
5. 通常の `match`／`matchAll` と pattern binding を二成分化する．
6. tuple matcher と `COERCE-SLOT-TUPLE` を二成分化する．
7. D5-CAS の view-qualified target-indexed signature interface，kind-aware index
   projection，CAS concrete signatures と runtime certificate を実装する．
8. matcher literal の hole，arm，next matcher を二成分化し，signature-directed
   result-slot projection，exact merge，observability finalization の順で
   `ShapeCap` を合成する．
9. 形式用の `CoverageOK` を `ShapeCap` から独立に定義し，Egison では既存の
   target-based Coverage warning を維持する．
10. `CatchAllLast` と `ordinary`／`covered` の mode-indexed source／value／
    environment／state judgments，strict covered certificate checker を実装する．
11. 再帰 binding を通常の単相 HM SCC 推論へ統一し，RHS 間へ二種 substitution を
   thread する．producer-flow summary，first-order evidence への正規化，
   binder–RHS generation knot，matcher literal の protected generation node，
   least-evidence solver，finalization 後の demand／annotation checking を別に接続する．
12. standard library と全 example の型注釈／view-qualified pattern ID を移行する．
13. 旧一添字の freeze／rigidity workaround を削除する．
14. Lean の宣言規則と値型付けを移行し，補題を下から再証明する．
15. 論文英語版・日本語版を新規則と実装・Lean の到達点に同期する．

後方互換性のための一添字 `Matcher` shim は作らない．

## 必須回帰

### P2 の直接回帰

- `mPoly` の target を list へ特殊化しても capability が `•` のまま
- `mPoly` の list target／変数パターン利用を受理
- `mPoly` の cons 利用を拒否
- `f [1,2] : Matcher • [Integer]` を推論
- `f [1,2]` の変数パターン利用を受理
- `f [1,2]` の cons 利用を拒否
- alias，`let`，lambda，application，function result を介しても同じ

### D5 canonicalization と CAS view

- `A = List Integer` を target／signature で canonical `Collection Integer` へ展開するが，
  alias 展開自体を capability evidence／seed にしない
- capability 位置の `A` と nullary alias 適用 `A Bool` を kind／arity error にする
- direct cycle `A = A`，mutual cycle `A = B; B = A`，unknown head を残す alias を
  name／kind elaboration で拒否する
- nominal quotient の自己 entry は transparent alias と区別し，展開も cycle rejection
  もしない
- CAS `groundEquiv`，subtype／reshape，`Tensor (Tensor a) ↦ Tensor a` が
  capability head equality へ混入しない
- canonical range を持つ aligned substitution は context-relative `CapTargetOK` を
  保存し，異なる head を入れる独立 substitution を拒否する
- `list` 本体の parameterized matcher literal は空 `Ξ` でなく，slot argument の
  `ValueTy` が与える `(p,a)` を使い，ordinary／covered の同じ mode で証拠を合成する
- mismatched structured matcher を返す foreign／trusted value は ordinary
  `CapTargetOK` certificate を得られず，covered 登録にはさらに Coverage certificate
  が必要になる
- `mathValue` のように strict signature と target が整列する matcher は受理し，
  `factor`／`term` は view signature がない段階では ordinary／covered の双方で拒否する
- `Factor.symbol`／`Term.term` の view-qualified ID は clause 自体から capability
  evidence を与え，expected target／result annotation だけでは view を選ばない
- `Term.term` view は coefficient capability を `TermCap p` へ投影し，
  SymbolSet index の projection 方針を signature に明記する

### partial shape capability と Coverage

- D1 で証拠と認める同じ型形成子の constructor clause が一つだけでも，合成後の
  observable な parameter がすべて確定すれば structured `ShapeCap` を推論する
- 残りの general constructor clauses が欠けている場合，capability を `•` に
  落とさず不足 constructor の warning を出す
- Coverage warning の有効・無効で推論 capability が変わらない
- catch-all-only literal は Coverage の診断設定にかかわらず `•` のまま
- catch-all-only の structured target に対する既存の target-based warning を維持する
- full Coverage を持つ matcher が `CoverageOK` の安全な部分集合に入る
- partial matcher の未被覆 constructor 利用を，定義済みの空結果と誤認しない
- D2 の `partialT` は ordinary で受理し，`B` への一歩が
  `B-pattern × something` という ordinary 非整型 state を作る反例を固定する
- 同じ `partialT` を covered では拒否し，covered derivation erasure は ordinary
  derivation を返す
- root が covered な outer matcher でも partial child を slot／captured environment
  から返す定義を covered では拒否する
- nested／generated matcher の arm 非網羅は Coverage warning 設定にかかわらず
  ordinary error にする
- constructor／tuple-headed refinement-only clause からも partial `ShapeCap`
  evidence を得られる
- refinement の `_`／`#$x` は `•` でなく `unseen` を与え，他の証拠を弱めない
- `Nothing`／`Nil` のように型パラメータを確定しない clause しかない場合，
  capability を target 型や annotation から補わず型エラーにする
- true phantom，opaque／function 内部だけの parameter，seed のない recursive-only
  parameter は unobservable とし，canonical `•` にする
- observability は pattern signature の capability-visible path の依存方程式を
  least fixpoint で解き，再帰辺だけでは seed を作らない
- `Tree a` の `leaf a` のような非再帰 seed があれば observable とし，再帰 occurrence
  はその evidence の伝播・検証だけを行う
- `C : a -> b -> K b a` の field evidence `p, q` を source binder 順でなく
  result argument slot 順の `K q p` へ投影する
- `D : a -> K (a, Integer)` の evidence `p` を product slot の `K (p, •)` へ投影する
- `Just : a -> Maybe a` の target parameter を `List Integer` に特殊化しても
  capability を target から生成せず，field evidence `•` から `Maybe •` を得る
- `Wrap : List a -> Wrap a` の field evidence `List p` から `Wrap p` を得るが，
  field evidence `•` や異なる既知 head は `unseen` にせず projection error にする
- 同じ result slot への複数 occurrence は field 内／field 間／clause 間のすべてで
  exact merge し，同一 variable identity の `p, p` は受理，異なる identity の `p, q`
  や `p, •` は拒否する
- general／refinement の同じ capability 位置の evidence は exact agreement を要求し，
  不一致を型エラーにする
- refinement-only の shape evidence は `CoverageOK` の証拠にはならず，不足 general
  clause の warning と安全な部分集合の境界を維持する
- `headSlot` の `$ :: _` から `List •` を推論する
- `assocMultiset` の cons refinement 内の tuple holes から要素 capability を推論し，
  value 固定位置は `unseen` とする

### 再帰 matcher

- `Tree a` matcher で `Leaf m` が `p` を seed とし，`Node self` が同じ `p` を伝播する
- 宣言上 observable な `Tree a` の parameter に `Node self` しか evidence がない
  matcher literal を seedless error として拒否する
- `g ← p, g ← g` は `p`，`g₁ ← g₂, g₂ ← p` は両方 `p` になる
- 実際の matcher literal 内の `g ← g` は observable なら拒否し，unobservable なら
  canonical `•` にする
- `g ← List g` とその相互再帰版を occurs-check error として拒否する
- 相互再帰 literal 群の片側にだけ seed がある場合は全 dependency node へ伝播し，
  異なる `p`／`q` が届く場合は exact mismatch にする
- annotation または consumer demand だけでは seedless literal を受理できない
- `let g = f`，application，高階 identity combinator を通しても `Rec` origin を失わない
- 同じ型の `chooseFirst`／`chooseSecond` で，flow summary が指定する返却引数だけを
  origin とし，無視された Known 引数から seed を作らない
- flow normalization が `Rec b`／`Literal g` を `Ref b`／`Ref g` へ変換し，
  `Arg`／`Captured`／`flow-lambda` を solver input に残さない
- `f = g`／`g = seededLiteral` の binder–RHS knot で seed が `f` まで伝播する
- SCC 内の recursive lookup は同じ単相 placeholder identity を返し，多相再帰を許さない
- Shape finalization と全代入適用後は SCC 外で通常どおり一般化できる
- clause 順と SCC 内 binder 順を交換しても，型と diagnostic が fresh rename を除き同じ
- matcher literal を生成しない `let rec x = x`／`fix f x. f x` は通常の HM 再帰として
  扱い，Shape seed 不足では拒否しない
- その binder-only cycle を一般化して後続 literal の hole に置いても，flow summary は
  `unseen` であり seed にならない
- Coverage warning の有効・無効で再帰 Shape solution が変わらない

### capability combinator

- `list something` の単純 cons を受理
- `list something` の要素 constructor パターンを拒否
- `let lm = list something` では capability substitution `p := •` を結果型へ適用して
  から generalize し，`p` が scheme に残らず要素 constructor パターンを拒否
- `list (maybe integer)` の入れ子 `Just` パターンを受理
- `multiset`，`set`，`sortedList` でも capability が再帰的に伝播
- tuple producer が capability 積と target 積をともに保存
- matcher を collection／ユーザー定義データに格納しても capability を保存
- matcher／slot 入力の flexible capability meta-variable を利用位置の制約で解き，
  推論された関数入力型と結果型の同じ occurrence へ反映できる

### 不正な能力生成

- catch-all-only literal を annotation で list capability に変更できない
- `Matcher • a` と `Matcher (List p) (List a)` の異種 collection を拒否
- target 引数との共有変数から capability を具体化できない
- consumer demand から finalized producer の既知 capability head を変更できない
- Algorithm W の capability substitution が関数結果，環境，残余制約へ必ず伝播する
- `bad : ∀p a. Matcher p a` の `p` を rigid skolem として検査し，`something` の
  producer capability `•` を annotation に合わせて強化できない
- 同じ単相 matcher target を独立な target witness で異なる型に利用できない

### R12 回帰

- 1 hole では式全体を一成分として検査
- 0 hole／複数 hole では正確な arity の明示 tuple だけを受理
- 変数・application・lambda で next matcher 判定が変わらない
- 既存 slot の capability／target 両成分を検査
- capability の入れ子構造と共有変数を再帰的に保存

## 証明義務

- capability／target の二種代入の反射性，合成，改名不変性，相互非干渉
- capability one-way の健全性，完全性，一意性
- Algorithm W が返す `S_κ`／`S_τ` を結果型，環境，残余制約，後続推論へ適用する
  substitution-threading invariant
- 全 substitution 適用後の二種 `Gen`／`Inst` の健全性，instance relation の
  反射性・推移性，annotation skolem の non-escape
- signature-directed projection と exact merge の健全性，決定性，field／clause
  順序独立性，D1 の exact-evidence calculus に相対的な主要性
- 通常の単相再帰 W の健全性，完全性，主要性，SCC 内 mono lookup identity，
  SCC 外 generalization
- Shape generation solver の停止性，健全性，完全性，最小性，決定性，
  clause／SCC 順序独立性
- seedless recursive cycle の非生成，seed propagation，exact mismatch，
  structural-growth cycle の occurs-check rejection
- 通常 substitution と Shape solution の合成保存，protected generation node の
  non-escape，finalization-before-generalization，annotation／consumer demand の
  non-seeding
- producer-flow summary の expression typing に対する健全性，lambda／application の
  summary substitution，well-formed 入力上の `R ; Δ ⊢ Φ ⇓ d` の
  全域性・決定性・source preservation，binder–RHS knot の方向保存，
  trusted summary を持つ `EnvTyped` の健全性
- summary path が full `Matcher κ τ` occurrence を指し，port／`K` transform 後も
  context-relative `CapTargetOK` を保つ `FlowTargetOK`
- matcher 値についての context-relative `CapTargetOK`，allowlist `reprNF`，
  整列済み coupled substitution に対する preservation
- target substitution 下での `ShapeCap` と `CoverageOK` の不変性
- capability substitution 下での parameterized `ShapeCap`／`CoverageOK` の保存
- slot-value invariant と canonical forms
- Structural-Hole Transfer の capability 版
- `EnvTyped` が全二種 instance を満たす一般化補題
- Algorithm W の健全性，完全性，最汎性
- `mPoly`，`f`，`list something`，let，高階関数，tuple，データ格納を通した
  到達可能な matcher value の能力非強化
- covered-to-ordinary erasure と mode-indexed fundamental theorem
- pattern typing／one-way head compatibility と
  `CoverageOK + CatchAllLast` からの `DispatchOK`
- R10 の `BaseAdm` 下での ordinary completed-evaluation partial correctness，
  `DispatchOK` 付き局所保存，covered Preservation／Progress／Type Safety
- CAS target-indexed pattern-view signature の field typing，Coverage，
  runtime extraction preservation
- P2 に由来する `capability-admissible` 仮定の除去

## 今回固定したことと残る詳細

### 固定したこと

- `Matcher κ τ` を論文・Lean・Egison で明示する
- capability と target を別 sort・別代入にする
- catch-all-only 能力を `•` とする
- capability は matcher literal の general と constructor／tuple-headed refinement
  clause から partial evidence を集め，`unseen` を中立とする exact agreement で
  `ShapeCap` として合成する
- `_`／`#$x` は `unseen`，hole は next matcher capability を与え，不一致または
  structured root 以下の observable な最終 `unseen` は型エラーにする
- true phantom，opaque／function 内部，seed のない recursive-only parameter は
  least-fixpoint observability により unobservable とし，canonical `•` にする
- constructor field evidence は signature parameter の variable identity を保つ fresh
  instantiation の後，source binder 順でなく result argument slot へ投影する
- projection は direct occurrence，product，capability-visible former をたどり，
  opaque／function で止まる．`unseen` は非寄与，既知 head／arity mismatch は
  型エラー，重複 occurrence は exact merge とする
- projection は通常 target substitution から capability を生成せず，ground branch
  は root evidence に寄与しないまま通常の slot／target 検査へ残す
- refinement は `ShapeCap` の存在的証拠にはなるが `CoverageOK` には数えない
- partial matcher も structured `ShapeCap` を持ち，Coverage warning の有効・無効は
  capability を変更しない
- `CoverageOK` は `ShapeCap` と独立な安全性条件として capability 側で検査する
- `ordinary`／`covered` の mode-indexed typing を置き，`CoverageOK` は後者の
  全 matcher literal にだけ要求する
- coverage 非依存の clause 条件には，唯一の canonical bare-hole catch-all が最終に
  ある `CatchAllLast` を用い，Coverage 依存の `holeAfterGenerals` は削除する
- `ValueTy`，`EnvTyped`，slot，closure，data／tuple，matching state へ mode を
  再帰的に通し，covered な outer matcher が partial child を隠せないようにする
- 通常層には無条件の matching-state Preservation／Progress を主張せず，
  `DispatchOK` 付き局所保存と完了評価の partial correctness だけを置く
- Preservation，Progress，Type Safety は covered subset に限定する
- next matcher の構造検査は capability 側で行う
- data pattern，arm，next target の整合は target 側で行う
- `f [1,2]` 自体は許可し，constructor use site で拒否する
- standard matcher combinator は slot capability を結果 capability へ再帰的に伝播する
- Algorithm W が返す capability substitution を一般化前に型，環境，残余制約の
  全 occurrence へ必ず適用する
- capability 変数も全 substitution 適用後に通常の HM 規則で一般化し，特別な
  provenance／`CapGen` は要求しない
- scheme instantiation は flexible meta-variable，明示量化の本体検査は rigid
  skolem を用い，skolem escape を拒否する
- 高階フローでは各 `Matcher` occurrence の capability を型スキームに保持する
- 再帰 binding 自体は通常の単相 HM SCC 規則で推論し，多相再帰を導入しない
- 通常 capability 等式と matcher literal の向き付き Shape generation obligation を
  分離し，再帰 occurrence を seed でなく SCC-local dependency node として扱う
- Shape generation は `unseen` を bottom とする least-evidence solver で解き，
  observable な未解決を拒否し，unobservable な未解決を canonical `•` にする
- consumer demand，結果注釈，自己参照は seed にせず，finalized producer capability
  へ後から照合する
- 型と別の producer-flow summary を通常の expression rule と同じ構文再帰で計算し，
  alias／高階 application でも実際の producer origin を保存する
- producer-flow summary を first-order evidence へ決定的に正規化し，`Rec` と
  `Literal` を seed でなく generation `Ref` にする
- recursive binder と RHS の producer summary を generation knot で結び，相互再帰の
  seed を向き付き dependency として伝播する
- Shape finalization と全 substitution 適用後，SCC の外側で通常の二種 HM
  generalization を行う
- `CapTargetOK` と capability head equality は，closed acyclic alias 展開と明示的な
  surface synonym だけを含む frozen canonical signature environment 上で検査する
- CAS `groundEquiv`，subtype／join，reshape，typeclass，quotient，tensor idempotence
  は capability equality に含めない
- open combinator の `CapTargetOK` は実 slot 値由来の仮定 context で導き，
  任意の独立代入でなく仮定を保つ coupled substitution に対して保存する

### 残る設計判断

- D5-CAS：`Factor`／`Term` などへ target-indexed pattern-view signature を与える
  view-qualified constructor ID，kind-aware index projection，constructor／field
  signature，runtime preservation

D1 の projection／tuple／merge／observability，D3 の二種 HM generalization／
substitution threading／skolem checking，D4 の通常単相再帰／Shape generation
solver，D2 の二層判断，D5-core の strict normalization／coupled substitution の
設計判断は固定したが，形式化と証明は未実施である．D5-CAS は単純な head view や
`groundEquiv` では child capability を保存できず，pattern signature 自体の再設計が
必要な blocker として残る．各課題の現状，採用方針，完了条件は上の
「残る設計課題と形式化課題」に記録した．専用 ADT か kind 付き変数か，表面表示，
診断，型消去などは，これらを変えない表現上の詳細である．

## 受入条件

- [ ] capability sort と target type sort が形式的に定義されている．
- [ ] `Matcher κ τ`／`MatcherSlot κ τ` の kinding と，
      matcher 値の `CapTargetOK` 不変量が定義されている．
- [ ] matcher literal の `ShapeCap` 合成規則と主要性の主張範囲が定義されている．
- [ ] fresh instantiate 後の result argument slot への projection が direct
      occurrence，product，capability-visible former，opaque／function barrier，
      ground branch，重複 occurrence について定義され，`unseen` と既知 head
      mismatch を区別している．
- [ ] capability-visible path による parameter observability の least-fixpoint 規則，
      opaque／function barrier，recursive-only parameter と canonical `•` が
      signature-directed lift と `ShapeCap` finalization に反映されている．
- [ ] `CoverageOK` が `ShapeCap` と独立に定義され，partial matcher の受理，
      target-based warning，`ordinary`／`covered` の再帰的 runtime invariant，
      安全な部分集合の定理境界が固定されている．
- [ ] alias-free canonical signature environment，allowlist `reprNF`，
      context-relative `CapTargetOK`，coupled substitution preservation が
      定義されている．
- [ ] CAS target-indexed pattern-view signature と runtime extraction preservation
      が定義され，`Factor`／`Term` などの標準 matcher が strict D5-core と整合する．
- [ ] 二種 Scheme／Subst／Inst，全 substitution 適用後の通常 HM generalization，
      flexible meta／rigid skolem，witness 伝播を持つ Algorithm W が定義されている．
- [ ] 通常の単相再帰 W，別系統の Shape generation obligation／least-evidence solver，
      producer-flow summary とその first-order evidence への正規化，
      binder–RHS knot，finalization 後の
      demand／annotation checking，SCC 外 generalization が定義されている．
- [ ] `mPoly` と `f` の能力強化が全 value-flow 経路で拒否される．
- [ ] `f [1,2]` と `mPoly` の安全な変数パターン利用が受理される．
- [ ] `∀p a. MatcherSlot p a -> Matcher (List p) (List a)` が推論・利用できる．
- [ ] `something`／`eq` の target 多相性が維持される．
- [ ] tuple，高階関数，`let`，トップレベル定義，データ格納の正負回帰がある．
- [ ] 二種代入と scheme instance の代数的性質が Lean で証明される．
- [ ] runtime matcher capability と利用時型の対応が `ValueTy`／`EnvTyped` 上で証明される．
- [ ] Algorithm W の健全性・完全性・主要性の主張範囲が確定する．
- [ ] P2 に由来する capability-admissibility の仮定を安全性定理から除ける．
- [ ] `CoverageOK` を持つ部分集合について Progress／Preservation／Type Safety の
      正確な定理境界が固定されている．
- [ ] 論文の英語版・日本語版，Egison 実装，Lean，回帰テストが同期している．

## 参照ポインタ

- 論文：
  [`main.tex`](../../type-pm-paper/main.tex) の `sec:rigidity`,
  `sec:metatheory`, `thm:principal-type`, `app:algorithm-w`,
  `app:principal-type-proofs`, `app:proof-cases`
- 日本語版：
  [`ja/main.tex`](../../type-pm-paper/ja/main.tex) の同じラベル
- 型スキーム：
  [`TypePM/Syntax.lean`](../TypePM/Syntax.lean) の `Ty`, `Scheme`
- 宣言的インスタンス：
  [`TypePM/TypeRel.lean`](../TypePM/TypeRel.lean) の `Scheme.Inst`
- matcher 型付け：
  [`TypePM/Typing.lean`](../TypePM/Typing.lean) の `HasTy.matcherE`,
  `ClauseTy`, `ConsistentClauses`
- 値・環境型付け：
  [`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean) の `ValueTy`, `EnvTyped`
- 一般化 oracle：
  [`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean) の `hgen`
- 主要型の機械化境界：
  [`TypePM/Metatheory/Principal.lean`](../TypePM/Metatheory/Principal.lean)
- Egison の型表現：
  [`Type/Types.hs`](../../egison/hs-src/Language/Egison/Type/Types.hs)
- Egison の代入・環境：
  [`Type/Subst.hs`](../../egison/hs-src/Language/Egison/Type/Subst.hs),
  [`Type/Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs)
- Egison の単一化・推論：
  [`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs),
  [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs)
- next matcher の固定済み境界：
  [R12](resolved-next-matcher-slot-checking.md)
- 現行型エラーテスト：
  [`test/type-error/README.md`](../../egison/test/type-error/README.md)
