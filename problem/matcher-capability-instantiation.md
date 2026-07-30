# P2：`Matcher κ τ` による capability と target の分離

## 状態

採用方針決定・再構成未実施．

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

この文書は採用する中核設計と移行範囲を固定する．論文，Egison 本体，Lean の
実変更と，主要型・無条件の型安全性の証明はまだ完了していないため，P2 自体は
未解決として残す．

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

`κ` は，matcher がどの構造のパターンを安全に分解できるかを表す．
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

- capability は primitive-pattern-pattern の一般節，Coverage，product 構造，
  next matcher の capability から構成する
- target は primitive-pattern-pattern の宣言型，primitive data pattern，
  decomposition body，next matcher slot の target 成分から通常推論する
- primitive data pattern と arm body は capability を強化しない
- target 代入を適用した後に capability や Coverage を再計算しない

matcher literal の root capability は，一般節と hole の capability から
**最大の certified capability** として合成する．ここで「最大」とは，その
literal が安全に公開できる constructor 構造を最も精密に表すという意味であり，
能力順序，合成演算，principal な選択を形式的に定義する必要がある．単に最弱の
`•` を常に選ぶのでも，未拘束 root capability 変数を残すのでもない．
catch-all-only literal は必ず `•` になる．

初期の形式化では，異なる一般節／next matcher 証拠が同じ capability 位置に
両立しない構造を要求した場合，intersection や union を導入せず型エラーとする．
完全な Matcher Consistency と Coverage の下で，一意な exact skeleton を
合成できる範囲を先に定める．partial matcher の principal capability は
Coverage 方針と合わせて別途扱う．

Coverage は target 型ではなく capability を基準にする．

- `Matcher • τ` では constructor Coverage は空虚
- `Matcher (List p) (List a)` では List の一般節を要求する
- user-defined product matcher literal では，全体に一つの一般 tuple 節
  `($, ..., $)` を要求する

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
5. 最大の certified capability の合成と Coverage を定義し，matcher target
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
- `ConsistentClauses` と Coverage の capability index 化
- `HasTy.matcherE`，`something`，tuple／slot coercion の二添字化
- matcher literal の最大 certified capability 合成

### `WellTyped` とメタ理論

- `ValueTy.matcherV`，`something`，product matcher，derived slot typing
- `MatcherOK`，`WTTree.atom`，runtime matcher invariant
- target substitution が capability／Coverage を変えない補題
- capability substitution lemma と one-way の一意性
- one-way witness を全 consumer occurrence へ伝播する補題
- Structural-Hole Transfer の capability 版
- constructor Progress を capability Coverage から得る証明
- Preservation で capability を保持し target だけを輸送する証明
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
- outer capability は節と Coverage から最大の certified capability として合成する
- outer target は primitive pattern，data pattern，arm，next target から推論する
- annotation は capability を生成せず，推論された capability を検証する

R12 で実装した明示タプル境界，構文形非依存，完全 slot 検査は維持する．

再帰 matcher では，自己参照へ与える暫定 capability，Coverage 確定，最終
capability の照合を一つの checking／fixpoint 手続きにする必要がある．
capability が確定する前の再帰 binding を一般化してはならない．

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

## Coverage に残る設計判断

形式仕様で structured capability を与えるには，その capability が要求する
constructor Coverage を保証しなければならない．現行 Egison の Coverage は
warning-level の近似であり，ここは実装時に次の安全な方針から選ぶ必要がある．

1. typed matcher では Coverage を hard error にする
2. Coverage を証明できない matcher には保守的に `•` を与える
3. capability を constructor 集合まで精密化する

この選択は単なる診断レベルではなく，受理プログラム，推論される capability，
principal capability を変える．P2 の最小実装では 1 または 2 が必要である．
3 は表現力を高める拡張であり，二添字化の初期実装には必須としない．論文の
現在の Matcher Consistency をそのまま実装目標にするなら 1 が自然である．

## 実装順

1. capability syntax／kind と二添字 `Matcher`／`MatcherSlot` を追加する．
2. free variables，二種 substitution，generalize，instantiate の単体回帰を作る．
3. producer equality と `COERCE-MATCHER-TO-SLOT` を二成分化する．
4. 通常の `match`／`matchAll` と pattern binding を二成分化する．
5. tuple matcher と `COERCE-SLOT-TUPLE` を二成分化する．
6. matcher literal の hole，arm，next matcher，capability 合成を二成分化する．
7. matcher annotation checking を capability 保存型へ変更する．
8. standard library と全 example の型注釈を移行する．
9. 旧一添字の freeze／rigidity workaround を削除する．
10. Lean の宣言規則と値型付けを移行し，補題を下から再証明する．
11. 論文英語版・日本語版を新規則と実装・Lean の到達点に同期する．

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
- matcher literal capability 合成の健全性，最大性，一意性
- matcher 値についての `CapTargetOK` と，normalization／substitution preservation
- target substitution 下での Coverage と matcher consistency の保存
- capability substitution 下での parameterized matcher consistency の保存
- slot-value invariant と canonical forms
- Structural-Hole Transfer の capability 版
- scheme instance の反射性，推移性，代入合成
- `EnvTyped` が全二種 instance を満たす一般化補題
- Algorithm W の健全性，完全性，最汎性
- constructor Progress と Preservation
- P2 に由来する `capability-admissible` 仮定の除去

## 今回固定したことと残る詳細

### 固定したこと

- `Matcher κ τ` を論文・Lean・Egison で明示する
- capability と target を別 sort・別代入にする
- catch-all-only 能力を `•` とする
- capability は matcher literal の構造から最大の certified capability として合成する
- Coverage，next matcher の構造検査は capability 側で行う
- data pattern，arm，next target の整合は target 側で行う
- `f [1,2]` 自体は許可し，constructor use site で拒否する
- standard matcher combinator は slot capability を結果 capability へ再帰的に伝播する
- one-way capability witness を一般化前の全 consumer occurrence へ必ず伝播する
- capability 変数の一般化には provenance／`CapGen` を要求する
- 高階フローでは各 `Matcher` occurrence の capability を型スキームに保持する

### 残る設計判断・形式化詳細

- capability syntax を専用 ADT にするか kind 付き型変数にするか
- 通常型／`Σ_P` signature から capability skeleton への lift と，
  `CapTargetOK` における inductive normalization／ground equivalence
- certified capability の能力順序，最大性，exact skeleton 合成アルゴリズム
- capability の表面 binder／pretty-print 構文
- Egison の Coverage を hard error にするか，未証明 matcher を `•` に落とすか
- producer capability 同士を exact equality から安全な parametric unification へ
  広げる条件
- 型クラス制約と capability binder の generalization 順序
- current rigidity error を capability mismatch 診断へどう移行するか

これらは二添字化という中核方針を再検討する問題ではないが，受理プログラム，
principal capability，証明の形を変えるため，実装前に明示的に決定する．

## 受入条件

- [ ] capability sort と target type sort が形式的に定義されている．
- [ ] `Matcher κ τ`／`MatcherSlot κ τ` の kinding と，
      matcher 値の `CapTargetOK` 不変量が定義されている．
- [ ] matcher literal の最大 certified capability 合成規則が定義されている．
- [ ] 二種 Scheme／Subst／Inst，`CapGen`，witness 伝播，Algorithm W が定義されている．
- [ ] `mPoly` と `f` の能力強化が全 value-flow 経路で拒否される．
- [ ] `f [1,2]` と `mPoly` の安全な変数パターン利用が受理される．
- [ ] `∀p a. MatcherSlot p a -> Matcher (List p) (List a)` が推論・利用できる．
- [ ] `something`／`eq` の target 多相性が維持される．
- [ ] tuple，高階関数，`let`，トップレベル定義，データ格納の正負回帰がある．
- [ ] 二種代入と scheme instance の代数的性質が Lean で証明される．
- [ ] runtime matcher capability と利用時型の対応が `ValueTy`／`EnvTyped` 上で証明される．
- [ ] Algorithm W の健全性・完全性・主要性の主張範囲が確定する．
- [ ] P2 に由来する capability-admissibility の仮定を安全性定理から除ける．
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
