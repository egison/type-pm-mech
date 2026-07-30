# P2：`Matcher κ τ` による capability と target の分離

## 状態

中核方針・Coverage 方針決定，詳細設計・再構成未実施．

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
partial evidence を集め，未観測を中立に exact agreement で合成する方針まで決定した．
constructor signature から capability parameter 位置への正確な投影，tuple，
通常型付けと安全な部分集合の形式化，`CapGen`，再帰 matcher，`CapTargetOK` の
正規化境界には詳細設計が残る．論文，Egison 本体，Lean の実変更と，P2 に由来する
capability-admissibility 仮定の除去も完了していないため，P2 自体は未解決として残す．

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
少なくとも一つ持ち，shape-relevant な全 parameter の evidence を確定できる partial
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
移す．`fresh_rename` も capability 構造と同一変数の共有を保ったまま，
capability 変数だけを再帰的に改名する．

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
対応しない組の matcher 値を直接導入してはならない．inductive normalization や
CAS の ground equivalence を `CapTargetOK` にどう反映するかは，Egison 移行時に
明示的に定義する．いずれの場合も，target 型から capability を再計算してはならない．

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
capability skeleton を要求する．

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
型形成子 `K` の証拠 clause が少なくとも一つあり，合成後の shape-relevant な
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

同じ capability 位置の証拠は，`unseen` を中立として provenance-preserving な exact
agreement で合成する．既に正当化された capability substitution の適用後に同じ
producer capability でなければ型エラーとし，この合成自体は producer 変数の
単一化や capability weakening を行わない．structured root を得た後も shape-relevant
な capability parameter 位置が `unseen` のままなら，target 型や annotation から
補わず型エラーとする．詳細な partial evidence と合成規則，および残る投影問題は
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
fresh_rename(κ_m) = κ_m'
matchCap(κ_m', κ_p) = S_κ
mgu(S_κ τ_m, S_κ τ_t) = S_τ
S = S_τ ∘ S_κ
--------------------------------
S Γ ⊢ e : MatcherSlot (S_κ κ_p) (S τ_t)
```

構造検査は capability 成分だけ，target 検査は通常型成分だけを見る．
`matchCap` は producer 側を rigid に扱い，consumer 側 capability 変数だけを
束縛する witness `S_κ` を返す．この witness は期待 slot だけでなく，型付き式，
関数結果，環境，一般化前の型にある同じ consumer 変数の全 occurrence へ
**必ず**伝播する．未適用の consumer 変数を generalize してはならない．

例えば `list` の fresh な `p` へ `something : Matcher • a` を渡すと，
`S_κ = {p ↦ •}` を結果型にも適用し，

```text
Matcher (List •) (List a)
```

を得る．`p` を未解決のまま一般化すると，後から `p := Maybe •` として能力を
偽造できるため不健全である．

target 側は独立した存在検査 `τ_m ∼ τ_t` ではなく，その occurrence の通常 HM
制約を prevailing MGU `S_τ` へ統合する．同じ単相 matcher target を異なる型へ
別々の witness で使うことを許してはならない．`S_τ` は surrounding target 型へ
伝播するが，capability へは侵入しない．

既存 `MatcherSlot κ' τ'` を期待 slot へ送る場合は，両者が consumer 要求なので，
capability 成分と target 成分をそれぞれの sort の通常 MGU で検査し，
得た代入を後続推論へ伝播する．

### producer 同士の等式

`Matcher` 同士の等式は，

- capability は provenance を保存する capability equality
- target は通常型の equality／unification

として分離する．異なる capability constructor は一致しない．producer literal
由来の `•` や constructor skeleton，annotation skolem は rigid であり，
constructor capability へ単一化してはならない．capability 変数を解けるのは，
関数／matcher／slot 入力から同じ能力を返す parametric flow など，導出が
正当化した flexible 変数に限る．

この provenance 不変量と generalization 規則が value flow 全体で証明できるまで，
producer capability 同士は exact equality を要求する保守的規則を採る．
証明後は，安全な flexible capability 変数だけを単一化する規則へ広げられる．

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
S_κ (Matcher κ τ) = Matcher (S_κ κ) τ
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
安全性を担うのは「全 capability 変数を固定すること」ではなく，

- literal 由来の能力を `•` または固定された constructor 骨格へ確定する
- cap-polymorphic な注釈を skolem として本体検査する
- matcher／slot／関数入力から結果へ流れる parametric capability 変数を
  導出上追跡する
- producer を consumer demand から強化しない

という規則である．

二種 Scheme／Subst だけでは，危険な

```text
∀p : Cap. Matcher p a
```

の導入を排除できない．一般化には，capability 変数がどの入力または環境上の
抽象能力に由来し，producer occurrence までどのように流れたかを示す
`CapGen`（仮称）の導出／証拠を要求する．少なくとも，

- matcher literal の root に生じた未拘束 capability meta-variable は一般化しない
- explicit capability parameter は skolem として本体を検査する
- `∀p a. Matcher p a -> Matcher p a` のような matcher 恒等関数は許す
- `∀p a. MatcherSlot p a -> Matcher (List p) (List a)` の slot 依存を許す
- 入力・環境との依存を持たない `∀p. Matcher p a` の constant producer は拒否する
- one-way witness で解いた consumer 変数を未解決のまま一般化しない

ことが必要である．`CapGen` を Scheme に証拠として持たせるか，Algorithm W の
生成可能スキーム judgment とするかは形式化時に決めるが，この provenance 条件
自体は採用設計の中核であり，単なる実装最適化ではない．

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
| 5．再帰的な fresh rename | ✓ 記述済み | ✓ 局所 one-way | ✓ R12 で実装済み | capability だけを再帰的に改名 |
| 6．式構文形への非依存 | ✓ | ✓ | ✓ R12 で実装済み | 型に capability が残るため自然に維持 |
| 7．scheme lookup 後の能力保存 | ✗ P2 | ✗ 共有型変数経路 | ✗ 同じ scheme 経路 | 二種 Scheme／Subst，`CapGen`，witness 伝播を実装・証明する |

R12 が解決した 2--6 の固定単相 next-matcher 検査は，二添字化後も維持する．
P2 の実装対象は，主に 1 と 7 を型表現・scheme・value flow 全体で閉じることである．
表の二添字案は採用した目標であり，実装済み・証明済みという意味ではない．

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
3. 通常型／`Σ_P` signature から capability signature への全域的な lift を定義し，
   pattern／primitive-pattern-pattern の構造成分を capability として定義する．
4. `T-SOME`，`T-MATCHER`，tuple coercion，slot coercion を二添字化する．
5. `ShapeCap` 合成と独立な `CoverageOK` を定義し，matcher target
   ではなく capability に索引付けする．
6. catch-all の target 検査を一般 hole／arm 規則と同じ経路にする．
7. matcher rigidity 節を，capability 保存と通常 target 多相の分離として書き直す．
8. Scheme.Inst，`CapGen`，Algorithm W，主要性の instance relation を
   二種代入と witness 伝播へ変更する．
9. runtime matcher typing，slot invariant，canonical forms を二添字化する．
10. `capability-admissible` を source typing から導き，P2 に由来する仮定を除く．
11. 全標準 matcher の型，本文例，付録の導出を新しい型へ更新する．

## Lean 機械化の再構成範囲

### `Syntax`

- capability の inductive syntax／sort
- `Ty.matcher : Cap -> Ty -> Ty`
- `Ty.matcherSlot : Cap -> Ty -> Ty`
- capability binder と通常型 binder を持つ `Scheme`
- 通常型／pattern signature から capability skeleton への lift

### `TypeRel`

- `CapSubst` と通常 `TySubst`
- capability の free variables，apply，fresh rename，composition
- capability 上の one-way 構造関係
- 二種の変数を扱う `Scheme.Inst`
- capability provenance／生成可能スキームを表す `CapGen`
- kind preservation と二種代入の相互非干渉

### `Typing`

- `PatTy`／`PPTy` の構造成分を capability 化
- `ClauseTy`／`ArmsTy`／`ClausesTy` の二添字化
- `ShapeCap` と `CoverageOK` を分離し，`ConsistentClauses` の安全な部分集合へ
  `CoverageOK` を接続
- `HasTy.matcherE`，`something`，tuple／slot coercion の二添字化
- matcher literal の `ShapeCap` 合成と主要性境界

### `WellTyped` とメタ理論

- `ValueTy.matcherV`，`something`，product matcher，derived slot typing
- `MatcherOK`，`WTTree.atom`，runtime matcher invariant
- target substitution が `ShapeCap`／`CoverageOK` を変えない補題
- capability substitution lemma と one-way の一意性
- one-way witness を全 consumer occurrence へ伝播する補題
- Structural-Hole Transfer の capability 版
- `CoverageOK` を持つ安全な部分集合の constructor Progress
- `CoverageOK` の下で capability を保持し target だけを輸送する Preservation
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
- `Type/Env.hs`：二種 generalize／instantiate
- `Type/Unify.hs`：capability equality，one-way，二成分 coercion
- `Type/Infer.hs`／`Type/Check.hs`：`something`，match site，matcher literal，
  tuple，annotation
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

- primitive-pattern-pattern の hole ごとに最初から完全な
  `MatcherSlot κ_l τ_l` を構成する
- arm body は target tuple の collection として検査する
- next matcher は完全な期待 slot へ検査する
- outer capability は D1 で定める constructor 証拠と next matcher から
  `ShapeCap` として合成する
- 形式用の `CoverageOK` は `ShapeCap` と独立に定義し，Egison では既存の
  target-based Coverage 診断を維持して，診断を有効にした場合は不足を warning
  として報告する
- outer target は primitive pattern，data pattern，arm，next target から推論する
- annotation は capability を生成せず，推論された capability を検証する

R12 で実装した明示タプル境界，構文形非依存，完全 slot 検査は維持する．

再帰 matcher では，ShapeCap の収集と自己参照型の設定を Coverage 診断から分離し，
最終 capability と照合する checking／fixpoint 手続きが必要である．正確な初期案と
完了条件は D4 に記録する．capability が確定する前の再帰 binding を一般化しては
ならない．

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
clause が少なくとも一つ観測され，必要な capability parameter が確定すれば，その
matcher は `K`-headed な shape capability を持つ．すべての constructor を扱わない
partial matcher も
`Matcher (K κ₁ ... κₙ) (K τ₁ ... τₙ)` として型付けでき，target 型を後から
特殊化してもこの capability は変化しない．

一方，`CoverageOK cls (K κ₁ ... κₙ)` は，matcher literal の root capability head
が `K` であるとき，結果型の head が `K` である全 pattern constructor に general
clause `c $...$` があることを表す独立な全称的条件とする．子 capability の Coverage
は，対応する next matcher 値自身の `CoverageOK` が担う．`CoverageOK cls •` は
空虚であり，product head では適切な arity の general tuple clause を要求する．
Coverage に数えるのは general clause だけであり，refinement clause は数えない．

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

## 残る設計課題

### D1：principal `ShapeCap` の合成

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
はその signature が与える結果型形成子 `K` と field 型式を用いる未定義の投影である．
したがって `Nothing` と `Just` を capability head `Maybe` へ，`[]` と `::` を
`List` へ対応付けるのは surface constructor 名ではなく signature である．nested
constructor／tuple はこの対応を通して既知の capability head と内部の partial
evidence を与える．`ms|ppᵢ` は flatten 済み next matcher 成分 `ms` のうち，`ppᵢ`
の hole 数に対応する左から右への部分列であり，R12 の成分境界を変えない．その正確な
signature-directed 投影は下記の残件である．

`childEvidence` は constructor／tuple 内部の hole にだけ用いる．top-level の bare
hole `$` は catch-all であり，その next matcher が structured capability を持っても
matcher literal の structured root evidence にはしない．

**exact merge．** 同じ capability 位置へ届く general／refinement の全 evidence は，
次の部分演算で合成する．

```text
merge(unseen, e) = e
merge(e, unseen) = e
merge(•, •) = •
merge(χ, χ) = χ                         -- 同じ provenance の場合だけ
merge(K ē, K f̄) = K merge(ē, f̄)     -- 同じ head／arity
merge((ē), (f̄)) = (merge(ē, f̄))     -- 同じ arity
merge(e, f) = error                     -- その他
```

この比較は，別の理由ですでに得た capability substitution を適用した後に行う．
合成を成功させるために異なる producer capability 変数を単一化したり，強い
capability を `•` へ weakening したりしない．同じ型パラメータが一つの clause
内に複数回現れる場合も，複数 clause の場合と同じ merge を使う．したがって演算が
成功する範囲では clause の順序に依存せず，同じ exact evidence tree が得られる．

structured root evidence が一つもなければ matcher literal の capability は `•` と
する．一方，root `K` を観測した後も shape-relevant な capability parameter 位置が
`unseen` のままなら型エラーとする．例えば `Maybe a` の `Nothing` や `List a` の
`Nil` のように `a` を確定しない constructor clause しかなければ，target 型や
annotation から capability を作らず拒否する．`Nothing` が `unseen`，`Just $` が
`p` を与える場合は `unseen` が中立なので `Maybe p` となる．

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

**残ること．**

- pattern constructor signature の型式から，nested／recursive occurrence を含む
  capability parameter 位置へ partial evidence を投影する正確な規則
- 同じ型パラメータが複数 field／異なる深さに現れる場合の投影と merge の順序
- general／refinement tuple clause を同じ投影へ含める正確な product 規則
- true phantom position と shape-relevant だが未観測の位置を判別する境界
- 上記 merge の決定性，順序独立性，健全性，相対的主要性の定理

**完了条件．** signature-directed な投影を含む合成が決定的で，annotation や target
型から capability を作らず，catch-all-only が必ず `•` になり，observable position
の未確定と exact mismatch を拒否し，採用する相対的主要性命題を明示して示せること．

### D2：型付けと `CoverageOK` を運ぶ二層の形式化

**現状．** capability を推論する通常型付けと，`CoverageOK` を含む安全な部分集合を
二層化する方針は決定した．現行 Lean の `ConsistentClauses` は Coverage，
catch-all，`holeAfterGenerals`，arm exhaustiveness を一つに持ち，Progress と
Preservation は Coverage を直接使う．一方，Egison は Coverage 不足を非致命的に
受理する．

**決めること．** `HasTy`／clause shape judgment／`CoverageOK` をどの単位で分割するか，
runtime matcher と環境が `CoverageOK` の証拠を全到達 occurrence へどう運ぶか，
通常型付けだけの Preservation と安全な部分集合の Preservation をどう区別して述べるか
を固定する．

**採用方針．** catch-all の到達性・順序条件と arm exhaustiveness は今回緩めない．
未被覆 constructor を通常の空結果へ変える意味論変更も行わず，Coverage 不足の
matcher を含む実行の runtime error／stuck は安全性定理の外に置く．

**初期案．** 通常の `HasTy.matcherE` から constructor Coverage だけを分離し，
catch-all，bare-hole より後ろに節を置かない順序条件，arm exhaustiveness，
`ShapeCap` をまとめた coverage 非依存の clause judgment を置く．これと
`CoverageOK` を再結合した `SafeMatcher` judgment を runtime の `ValueTy`，
`MatcherOK`，`EnvTyped` へ運び，安全な state の全到達 matcher occurrence が
`SafeMatcher` を満たすことを不変量とする．

**完了条件．** partial matcher の受理 judgment，`CoverageOK` を保持する runtime
matcher／環境不変量，Progress／Preservation／Type Safety の正確な前提がそれぞれ
定義されていること．

### D3：capability provenance と `CapGen`

**現状．** capability 変数を別 sort で量化するだけでは，入力に由来しない危険な
`∀p. Matcher p a` を導入できる．入力 slot や環境上の抽象能力から producer へ流れる
変数だけを一般化できるという原則は決定済みだが，正式な judgment は未定義である．

**決めること．** rigid／flexible capability meta-variable の区別，origin の表現，
一般化可能性を Scheme の証拠に持たせるか Algorithm W の生成可能スキーム judgment
にするか，型クラス制約を解く順序を定める．

**初期案．** literal skeleton と annotation skolem は rigid，matcher／slot／関数入力
から流れる capability meta-variable は provenance 付き flexible とする．consumer
witness を一般化前の全 occurrence へ適用し，入力・環境との依存を持たない root
meta-variable は一般化しない．producer capability 同士は初期版では exact equality
を要求し，安全な parametric unification は将来拡張とする．通常型代入と capability
witness を型・制約全体へ適用した後，target 側の型クラス制約を解消済み／残余へ分け，
残余制約と通常型変数，`CapGen` が許す capability 変数を同じ scheme へ一般化する．

**完了条件．** `mPoly`，`f`，高階関数，tuple，データ格納の全 value-flow 経路で
能力強化を拒否しつつ，matcher identity と
`∀p a. MatcherSlot p a -> Matcher (List p) (List a)` を一般化できること．

### D4：再帰 matcher の capability 推論

**現状．** 再帰 binding の本体を検査するとき，自己参照へ暫定 capability を与える
必要があるが，ShapeCap は clause 全体を見て初めて確定する．

**決めること．** capability 注釈を必須にするか，least fixpoint／二段階 checking で
annotation-free な単相再帰を許すかを固定する．

**推奨案．** `ShapeCap` の証拠となる general と constructor／tuple-headed
refinement clauses を先に走査し，partial evidence と capability 等式を収集する．
得た暫定 ShapeCap を単相な自己参照型として置いた後，next matcher と arm body を
検査する二段階方式とする．第2段階で capability 等式を fixpoint まで解き，解が
安定して finalization 後の ShapeCap と一致するまで一般化しない．

**完了条件．** 標準再帰 matcher の capability が一意に推論され，自己参照から新しい
能力を循環的に捏造できず，annotation あり／なしの結果が整合すること．相互再帰を
許す場合は，再帰 binding 群について同じ性質を満たすこと．

### D5：`CapTargetOK` の正規化境界

**現状．** structured capability と target の head former を対応させる必要があるが，
Egison には type alias，inductive normalization，CAS の ground equivalence がある．

**決めること．** どの正規化までを `CapTargetOK` と capability constructor equality
の一部にし，どこからを型クラス／外部理論／将来拡張へ分離するかを固定する．

**推奨案．** 初期版では type alias の展開と，型表現が既に行う構文的 canonicalization
の後の型形成子 head の一致，およびその引数の再帰的 `CapTargetOK` だけを認める．
追加の inductive normalization，CAS ground equivalence，その他の意味的
normalization は初期版に含めず，capability を target から再計算しない別の明示的
拡張とする．

**完了条件．** standard matcher の全型で `CapTargetOK` が決定可能かつ代入で保存され，
trusted primitive／外部環境が不整合な matcher 値を導入できないこと．

### 実装時に選べる表現上の詳細

次は上記 D1--D5 を変えない限り，P2 の意味論的な blocker ではない．

- capability syntax を専用 ADT にするか kind 付き型変数にするか
- capability binder／pretty-printer／エラー表示の表面構文
- 型付き中間表現に capability を残すか型検査後に消去するか
- current rigidity error を capability mismatch としてどう表示するか
- 二種 substitution／rename の内部データ構造

## 実装順

1. capability syntax／kind と二添字 `Matcher`／`MatcherSlot` を追加する．
2. free variables，二種 substitution，generalize，instantiate の単体回帰を作る．
3. producer equality と `COERCE-MATCHER-TO-SLOT` を二成分化する．
4. 通常の `match`／`matchAll` と pattern binding を二成分化する．
5. tuple matcher と `COERCE-SLOT-TUPLE` を二成分化する．
6. matcher literal の hole，arm，next matcher と `ShapeCap` 合成を
   二成分化する．
7. 形式用の `CoverageOK` を `ShapeCap` から独立に定義し，Egison では既存の
   target-based Coverage warning を維持する．
8. D4 で採用する再帰 matcher checking と matcher annotation checking を
   capability 保存型へ変更する．
9. standard library と全 example の型注釈を移行する．
10. 旧一添字の freeze／rigidity workaround を削除する．
11. Lean の宣言規則と値型付けを移行し，補題を下から再証明する．
12. 論文英語版・日本語版を新規則と実装・Lean の到達点に同期する．

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

### partial shape capability と Coverage

- D1 で証拠と認める同じ型形成子の constructor clause が一つだけでも，合成後の
  shape-relevant な parameter がすべて確定すれば structured `ShapeCap` を推論する
- 残りの general constructor clauses が欠けている場合，capability を `•` に
  落とさず不足 constructor の warning を出す
- Coverage warning の有効・無効で推論 capability が変わらない
- catch-all-only literal は Coverage の診断設定にかかわらず `•` のまま
- catch-all-only の structured target に対する既存の target-based warning を維持する
- full Coverage を持つ matcher が `CoverageOK` の安全な部分集合に入る
- partial matcher の未被覆 constructor 利用を，定義済みの空結果と誤認しない
- constructor／tuple-headed refinement-only clause からも partial `ShapeCap`
  evidence を得られる
- refinement の `_`／`#$x` は `•` でなく `unseen` を与え，他の証拠を弱めない
- `Nothing`／`Nil` のように型パラメータを確定しない clause しかない場合，
  capability を target 型や annotation から補わず型エラーにする
- general／refinement の同じ capability 位置の evidence は exact agreement を要求し，
  不一致を型エラーにする
- refinement-only の shape evidence は `CoverageOK` の証拠にはならず，不足 general
  clause の warning と安全な部分集合の境界を維持する
- `headSlot` の `$ :: _` から `List •` を推論する
- `assocMultiset` の cons refinement 内の tuple holes から要素 capability を推論し，
  value 固定位置は `unseen` とする

### capability combinator

- `list something` の単純 cons を受理
- `list something` の要素 constructor パターンを拒否
- `let lm = list something` を挟んでも capability witness `p := •` が保存され，
  要素 constructor パターンを拒否
- `list (maybe integer)` の入れ子 `Just` パターンを受理
- `multiset`，`set`，`sortedList` でも capability が再帰的に伝播
- tuple producer が capability 積と target 積をともに保存
- matcher を collection／ユーザー定義データに格納しても capability を保存

### 不正な能力生成

- catch-all-only literal を annotation で list capability に変更できない
- `Matcher • a` と `Matcher (List p) (List a)` の異種 collection を拒否
- target 引数との共有変数から capability を具体化できない
- consumer slot の capability 変数を解く代入が producer capability を変更しない
- consumer witness が関数結果と一般化前の型へ必ず伝播する
- cap-polymorphic annotation の未検証 root capability を一般化できない
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
- matcher literal `ShapeCap` 合成の健全性，決定性，D1 で採用する主要性
- matcher 値についての `CapTargetOK` と，normalization／substitution preservation
- target substitution 下での `ShapeCap` と `CoverageOK` の不変性
- capability substitution 下での parameterized `ShapeCap`／`CoverageOK` の保存
- slot-value invariant と canonical forms
- Structural-Hole Transfer の capability 版
- scheme instance の反射性，推移性，代入合成
- `EnvTyped` が全二種 instance を満たす一般化補題
- Algorithm W の健全性，完全性，最汎性
- `CoverageOK` を持つ安全な部分集合の constructor Progress と Preservation
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
  structured root 以下の shape-relevant な最終 `unseen` は型エラーにする
- refinement は `ShapeCap` の存在的証拠にはなるが `CoverageOK` には数えない
- partial matcher も structured `ShapeCap` を持ち，Coverage warning の有効・無効は
  capability を変更しない
- `CoverageOK` は `ShapeCap` と独立な安全性条件として capability 側で検査する
- next matcher の構造検査は capability 側で行う
- data pattern，arm，next target の整合は target 側で行う
- `f [1,2]` 自体は許可し，constructor use site で拒否する
- standard matcher combinator は slot capability を結果 capability へ再帰的に伝播する
- one-way capability witness を一般化前の全 consumer occurrence へ必ず伝播する
- capability 変数の一般化には provenance／`CapGen` を要求する
- 高階フローでは各 `Matcher` occurrence の capability を型スキームに保持する

### 残る設計判断

- D1：constructor signature から capability parameter 位置への partial evidence の
  投影，tuple 規則，相対的主要性の形式化
- D2：partial matcher の通常型付けと `CoverageOK` を持つ安全な部分集合の形式化
- D3：`CapGen`，rigid／flexible provenance，一般化順序
- D4：再帰 matcher の ShapeCap 推論
- D5：`CapTargetOK` の alias／normalization／ground equivalence 境界

各課題の現状，推奨初期案，完了条件は上の「残る設計課題」に記録した．専用 ADT か
kind 付き変数か，表面表示，診断，型消去などは，これらを変えない表現上の詳細である．

## 受入条件

- [ ] capability sort と target type sort が形式的に定義されている．
- [ ] `Matcher κ τ`／`MatcherSlot κ τ` の kinding と，
      matcher 値の `CapTargetOK` 不変量が定義されている．
- [ ] matcher literal の `ShapeCap` 合成規則と主要性の主張範囲が定義されている．
- [ ] `CoverageOK` が `ShapeCap` と独立に定義され，partial matcher の受理，
      target-based warning，安全な部分集合の境界が固定されている．
- [ ] 二種 Scheme／Subst／Inst，`CapGen`，witness 伝播，Algorithm W が定義されている．
- [ ] 再帰 matcher の capability 推論／checking 手続きが定義されている．
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
