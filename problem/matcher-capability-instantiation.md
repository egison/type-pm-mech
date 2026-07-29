# P2：`Matcher` 添字の能力を保存するスキームインスタンス化

## 状態

設計判断待ち．

固定された単相導出の中では，matcher の固有型，`MatcherSlot` の一方向構造検査，
ターゲット単一化を分離できる．未解決なのは，`let` やトップレベル定義で
一般化された matcher 値を利用箇所でインスタンス化するとき，定義元の構造的能力を
強化しない形式的なインスタンス関係である．

この関係がないため，主要型は未解決義務であり，型安全性・進行性では
「値の流れ上の全スキームインスタンス化が能力を保存する」という
能力許容性を仮定している．

## 一言でいうと

通常の Hindley--Milner インスタンス化では，

```text
∀a. Matcher a
```

の `a` を `[Integer]` に置き換えられる．しかし，その値が実際には
「どんな構造も分解しない，裸変数位置だけの matcher」として定義されたなら，
型だけを `Matcher [Integer]` に変えることは，存在しない cons 分解能力を
後から付け加えることになる．

一方で，

```text
∀a. MatcherSlot a a -> Matcher [a]
```

という `list`／`multiset` 型の `a` を `Integer` にインスタンス化することは
許したい．この場合，定義時から結果 matcher の先頭能力はリストであり，
要素型だけがパラメータ化されている．

「危険な能力強化」と「正当な能力パラメータ化」を形式的に区別する必要がある．

## 固定済みの考え方

次の点は現在の論文で固定されている．

1. matcher 値には，`T-MATCHER` または `T-SOME` が与える固有型がある．
   matcher の実行時タプルには，`COERCE-TUPLE-MATCHER` の値レベル版が
   正準な積の固有型を与える．
2. 固有型の添字は，その値が定義時に獲得した構造的分解能力を表す．
3. 利用箇所では `MatcherSlot τp τt` が消費位置を表す．
4. `COERCE-MATCHER-TO-SLOT` は，固有添字の新鮮な改名 `τm'` について
   `τm' ⊑ τp` を検査し，別に `τm ∼ τt` を検査する．
5. 固定された単相導出の後続代入は，既に確定した構造的判定を
   遡って強化するために使わない．
6. `Matcher τ1` と `Matcher τ2` の通常の等式・単一化は剛的であり，
   `τ1 ≠ τ2` なら失敗する．
7. matcher リテラルをその定義注釈に対して検査する場合だけは，
   注釈で指定した能力において節本体を検査するため，別扱いとなる．
8. matcher 定義の複数穴に対する次マッチャーは明示タプルに限定し，分解後の
   各成分は変数・application・lambda などの構文形によらず，完全な推論型から
   期待 `MatcherSlot` に対して検査する（[R12](resolved-next-matcher-slot-checking.md)）．

未解決なのは，この剛性を型スキームの一般化・インスタンス化へどう持ち上げるかである．

## 論文・Egison 実装の対応表（最新版）

記号の意味は，`✓` が要求された一般経路を実装済み，`△` が局所的または
一部の経路だけ，`✗` が要求された一般経路を実装していない，である．
「通常の match」は `matchAll` の matcher 利用位置，「next matcher」は
matcher 定義の各 primitive-pattern-pattern ホールへ送る式を指す．

| 項目 | 論文 | Egison 通常の match | Egison next matcher |
|---|---|---|---|
| 1．固有型・固有能力の保存 | △ 固定単相導出では明記済み．scheme lookup 後の共有変数を通る特殊化は P2 | △ 直接の裸 matcher は保つが，高階・共有変数経路では失う | △ 一部の成分だけ単一化前の型を保存する構文依存処理 |
| 2．各穴に完全な slot を構成 | ✓ `T-MATCHER`／Consistency (1a) の宣言規則 | ✓ match site の完全な `MatcherSlot τp τt` を構成 | ✗ hole target と部分的 shape 情報に分かれ，完全な期待 slot へ一律に送らない |
| 3．`Matcher μ` の双対検査 | ✓ `fresh_rename(μ) ⊑ τp` と target 単一化を分離 | ✓ `coerceMatcherToSlot` が構造先行で検査 | ✗ eager／deferred の個別検査であり，既存 coercion へ一律に送らない |
| 4．既存 `MatcherSlot` の両成分検査 | ✓ Step 3a を伝播する等式と MGU に修正済み | ✓ slot--slot の構造・target 両成分を順に単一化 | ✗ `HCSlot` は両成分を期待 slot と比較せず通す |
| 5．型構造を保存する再帰的な変数改名 | ✓ `fresh_rename` を一文で再帰的に定義済み | △ 明示改名はせず，構造先行の one-way 検査を局所的な等価実装としている | △ matcher 側の `freshenTypeVars` は再帰的だが，hole 側の `freshLeavesOf` は入れ子構造を保存しない |
| 6．成分検査の式構文形への非依存 | ✓ 成分境界の決定後は完全な推論型だけで検査 | ✓ matcher 位置の任意の式を推論型から coercion へ送る | ✗ 変数・`something`・application などで登録・省略を分岐 |
| 7．scheme lookup 後の共有変数具体化を能力保存的に制限 | ✗ P2 の中心であり未規定 | ✗ fresh lookup 後に通常引数などから能力添字を具体化できる | ✗ 通常経路と同じ問題に加え，成分検査前の型情報欠落がある |

2--6 の next-matcher 列にある不足は，
[R12](resolved-next-matcher-slot-checking.md) で仕様が固定済みの**実装補修**であり，
追加の設計判断ではない．P2 として残る本質は，1 の scheme／高階フロー部分と
7，すなわち定義元の能力を通常の型代入から独立にどう保持するかである．

なお，単純な `mPoly : ∀a. Matcher a` の直接利用では，Egison の lookup は
`Matcher β` へ fresh 化するだけなので，cons slot に到達した時点の構造検査
`β' ⊑ [α]` が失敗する．現実装にも残る反例は，fresh 化後の `β` が通常引数などの
非 `Matcher` 位置と共有され，slot 到達前に `[Integer]` へ具体化される経路である．

## `mPoly` 反例

論文の反例は次の形である．

```egison
def mPoly {a} : Matcher a :=
  matcher
    | $ as something with
      | $tgt -> [tgt]
```

### 定義時

- 能力添字は裸変数 `a` である．
- `a` にはパターンコンストラクタの先頭型形成子がないため，Coverage は空虚である．
- 節は catch-all だけで，分解は `something` へ委譲される．
- したがって「変数・ワイルドカード・値パターンを処理する」という能力には整合する．

### 危険なインスタンス化

通常の HM と同様に `a := [Integer]` を許すと，利用箇所では
`mPoly : Matcher [Integer]` に見える．cons パターンの構造スロットも
リスト先頭なので，型だけを見た構造検査は成功してしまう．

しかし実行時 matcher 値には cons を扱う一般節がない．catch-all が選ばれ，
次 matcher `something` に cons パターンが渡されるため，次の原子で行き詰まる．

```text
($x :: $xs, something, v)
```

これは，剛的な `Matcher` 同士の直接単一化を禁止するだけでは不十分で，
スキームの量化変数を置換する経路にも能力保存条件が必要であることを示す．

この説明は，量化変数への任意の型代入を許す Lean の宣言的 `Scheme.Inst` には
直接当てはまる．一方，現行 Egison の Algorithm W は lookup 時には `a` を
新鮮な型変数 `β` へ置き換えるだけである．したがって `mPoly` を直接 cons site
へ渡す場合は，`Matcher β` に対する構造検査 `β' ⊑ [α]` が失敗し，型エラーになる．
現行実装で実際に剛性を迂回できるのは，次の共有型変数を通る経路である．

## 共有型変数経由の反例

```egison
def f := \w ->
  matcher
    | $ as something with
      | $tgt -> [w]
```

catch-all 節の分解結果 `[w]` により，引数 `w` の型と matcher の対象型が共有され，
`f` には概念的に次のスキームが推論される．

```text
f : ∀a. a -> Matcher a
```

この `f` を次のように利用する．

```egison
matchAll [1, 2] as f [1, 2] with
  | $x :: $xs -> x
```

型推論は次の順に進む．

1. `f` の lookup はスキームを `β -> Matcher β` へ fresh 化する．
2. 通常の関数適用が引数 `[1, 2] : [Integer]` と仮引数 `β` を単一化し，
   `β := [Integer]` を得る．
3. その結果，matcher 式 `f [1, 2]` の型は `Matcher [Integer]` になる．
4. この具体化では `Matcher β` と `Matcher [Integer]` を直接比較しないため，
   `Matcher`--`Matcher` の剛性規則は一度も発火しない．
5. cons site へ到達した時点では，構造検査は
   `[Integer] ⊑ [α]` となって成功する．

しかし，実行時の matcher 値は catch-all 節しか持たず，cons パターンを
`something` へ委譲するため，

```text
something can only match with a pattern variable
```

として行き詰まる．現行 Egison の strict type checking でも，この式が型エラーなく
実行へ進み，上記エラーに到達することを確認している．

この例は，P2 が単なる「lookup 時の fresh 化」や「`Matcher` 同士の直接剛性」では
解決しないことを示す．定義元では裸変数だった能力を，通常引数，関数結果，積の別成分
などから生じる後続代入とは独立に保持する必要がある．

## 許容すべきパラメータ化 matcher

```egison
def list {a}
  (m : MatcherSlot a a) : Matcher [a] := ...
```

この定義では，結果 matcher の能力の先頭は定義時から `List` である．
`a := Integer` としても，`Matcher [a]` が `Matcher [Integer]` になるだけで，
裸変数能力をリスト能力へ変更するわけではない．

ただし，単に「`Matcher` の直下にある変数は置換禁止」とすると，
`Matcher [a]` の `a` まで不必要に固定してしまう．逆に「型形成子の先頭だけ
同じならよい」とすると，入れ子の構造能力や積・パターンコンストラクタ引数の
依存を取りこぼす可能性がある．この境界が設計の中心である．

## なぜ主要型と型安全性に必要か

### `let` 一般化

環境型付けは，スキームで束縛された1つの実行時値が，許される全インスタンスで
型付くことを必要とする．通常の `Scheme.Inst` が `mPoly` の危険な
インスタンスを含むなら，同じ matcher 値を `Matcher [Integer]` で
型付けることはできない．

したがって，

```text
e1 ⇓ v
Γ ⊢ e1 : τ
let x = e1 で τ を一般化
```

から「`v` は一般化スキームの全インスタンスで型付く」という通常の
一般化補題は，matcher 添字について無条件には成り立たない．

### 主要型

主要型を述べるには，「他のすべての型付けは主要スキームのインスタンスである」
というインスタンス関係が必要である．危険な通常インスタンスを削除するだけでなく，
次を証明できる関係でなければならない．

- 恒等インスタンスがある．
- インスタンス化の合成が閉じている．
- 推論アルゴリズムが最汎インスタンスを計算する．
- `MatcherSlot a a -> Matcher [a]` のような正当な多相性を表せる．

このため，能力保存は局所的な安全性ガードだけでなく，型の一般性の順序そのものに
関わる．

## 設計に必要な要件

### 安全性

- スキームインスタンス化後も，実行時 matcher 値が定義時に持った
  `T-MATCHER`／`T-SOME` の構造的能力を強化しない．
- `mPoly : ∀a. Matcher a` から `Matcher [Integer]` への能力強化を拒否する．
- matcher が関数・積・データ構造の内側に格納されても，値フロー上の能力を
  追跡できる．
- `MatcherSlot` への消費時だけでなく，環境参照，関数引数・結果，データ構築，
  `let`，再帰定義を通じた流れを扱える．

### 表現力

- `∀a. MatcherSlot a a -> Matcher [a]` を許容する．
- `eq`／`something` のような裸変数能力を，変数・ワイルドカード・値パターンの
  スロットへ多相に供給できる．
- 積 matcher と `COERCE-SLOT-TUPLE` の成分ごとの多相性を保つ．
- 通常の matcher を含まない HM プログラムの一般化を変えない．
- 型クラス制約を含む `sortedList` の限定スキームへ将来拡張できる．

### 代数的性質

- 能力保存インスタンス関係の反射性と推移性が成り立つ．
- 型代入の合成と，matcher 能力の証人の合成が対応する．
- 改名に不変である．
- `MatcherSlot` の構造添字とターゲット添字で，どの変数がどの役割を持つか
  明確である．
- 固定単相導出における一方向マッチングの一意性と矛盾しない．

### 推論

- Algorithm W が能力情報を生成・一般化・インスタンス化できる．
- 「主要型」または「限定主要型」を形式的に述べられる．
- 失敗時に，「直接の matcher 剛性違反」「slot の構造不一致」
  「スキームによる能力強化」を区別して報告できる．
- 判定可能で，実装上 matcher 値の本体を利用箇所ごとに再検査する必要がない．

## 設計候補と主なトレードオフ

以下は比較対象であり，採用案ではない．

### A．型スキームに固有能力の骨格を別途記録する

スキームを，通常の本体型だけでなく，matcher 値の定義時能力を表す骨格・証明と
組にする．インスタンス化時には，通常型の置換と能力骨格の保存を同時に検査する．

長所：

- `mPoly` の「固有能力は裸変数」という由来を明示的に残せる．
- 利用箇所の `MatcherSlot` 検査と接続しやすい．
- 実行時値と定義時能力の対応を直接述べやすい．

課題：

- matcher を返す関数では，能力が値ではなく結果に潜るため，骨格の抽象化が必要である．
- 積，データ構造，高階関数を含む能力要約の文法が必要になる．
- 通常の型と能力骨格の整合性・主要性を証明しなければならない．

### B．能力変数と通常の型変数を分離する

`Matcher κ τ` のように，分解能力 `κ` とターゲット型 `τ` を別の添字・種で表す，
または現在の `Matcher τ` の内部で「剛的能力変数」と「置換可能な型変数」を
区別する．

長所：

- 裸変数能力と `List` 能力を型レベルで直接区別できる．
- `Matcher [a]` の `List` 能力を固定し，`a` だけを通常に量化しやすい．

課題：

- 現在1添字の `Matcher` と2添字の `MatcherSlot` を大きく再設計する可能性がある．
- 能力とターゲット型が共有する型変数の関係を別途表す必要がある．
- 表層注釈，型推論，論文全体への影響が大きい．

### C．極性・出現位置に基づく制限付き量化

一般化時に，`Matcher` 添字の能力を強化し得る変数は剛的にし，
データ型の固定された骨格の下にあるパラメータだけを量化する．

長所：

- 現在の型文法を保ったまま，構文的な判定として実装できる可能性がある．
- `Matcher a` と `Matcher [a]` を区別する直観に合う．

課題：

- 同じ変数 `a` が `MatcherSlot a a` と `Matcher [a]` の両方に現れる
  パラメータ化 matcher で，単純な出現位置規則では不十分な可能性がある．
- 関数の反変位置，積，型別名，入れ子 matcher の扱いが複雑になる．
- 構文的制限が意味的な能力保存と一致する証明が必要である．

### D．限定型の能力保存制約として表す

通常のスキームに「この置換は能力を保存する」という制約を付け，
利用箇所で解消する．

```text
∀a. PreserveCap κ a => Matcher ...
```

長所：

- 将来の型クラス制約と共通の限定型枠組みに載せられる可能性がある．
- 正当な多相性を残しつつ，危険なインスタンスだけを制約で拒否できる．

課題：

- 制約の意味論，含意，簡約，主要性を定義する必要がある．
- 能力証拠を静的に消去するか，辞書として運ぶかを決める必要がある．
- 制約解消が matcher 本体の再検査に退化しない設計が必要である．

### E．matcher を生成する `let` の一般化を制限する

値制限に似た規則で，matcher 値または matcher を含む型を持つ式を
一般化しない，あるいは明示注釈のある能力パラメータ化関数だけを一般化する．

長所：

- `mPoly` の危険な経路を単純に閉じられる．
- 初期実装・保守的な安全サブセットとして明確である．

課題：

- `let m = something` を異なる安全な裸変数スロットで使う matcher 多相まで
  失う可能性がある．
- 論文の annotation-free HM-style inference と主要型の目標を弱める．
- トップレベル定義，関数結果，データ格納を含む全経路に同じ制限が必要である．

### F．matcher 値へ生成時の能力証拠を実行時に付ける

実行時 matcher 値に能力タグ・節被覆の証拠を持たせ，インスタンス化または
slot 消費時に照合する．

長所：

- 値の由来を失わず，高階フローを直接扱える．
- 静的情報が不足する場合にも安全な動的検査へ落とせる．

課題：

- 純粋な静的主要型問題は解決しない可能性がある．
- 実行時表現と意味論を変更する．
- 型消去，別コンパイル，証拠の等価性に関する設計が必要である．

## 論文との対応

主な参照箇所は次である．

- `sec:rigidity`：matcher 剛性と `mPoly` 反例
- `sec:metatheory`：能力許容性と `Adm`
- `thm:principal-type`：未解決の主要型義務
- `app:algorithm-w`：候補 Algorithm W の型強制順序
- `app:principal-type-proofs`：固定済み補題と残るインスタンス関係
- `app:proof-cases`：固定単相導出の支配的代入と能力許容性の境界
- `sec:implementation`：実装が未解決義務を完全には強制しない旨

設計確定後は，スキームインスタンス関係，その合成補題，最汎性補題を追加し，
主要型を定理として復活できるかを改めて評価する必要がある．

## Egison 実装との対応

現行 Egison は，この問題の一部を複数の局所規則で近似している．

### 直接の matcher 剛性

[`Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs) の
`unifyG` は，`TMatcher t1` と `TMatcher t2` を `t1 == t2` の場合にだけ
受理し，それ以外を `MatcherRigidity` とする．

`TMatcher` と `TMatcherSlot` の組合せだけは `coerceMatcherToSlot` へ進み，
固有 matcher 添字に対する一方向構造検査と，ターゲット側単一化を分離する．

### 通常のスキームインスタンス化

[`Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs) の `instantiate` は，
`Forall` の全量化変数を通常の新鮮型変数へ置換する．ここには matcher 能力の
由来や能力保存関係は現れない．

[`Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs) は，

- 通常の `let` で matcher 型の値も一般化する
- `let m := something` の matcher 多相を意図的に許す
- 再帰グループ内の matcher リテラル自体は別理由で単相に保つ
- matcher リテラルを定義注釈に対して検査するときだけ剛性の例外を使う

という近似を実装している．これらの組合せは実用上のテストを通しているが，
能力保存インスタンス関係の形式化や主要型証明の代わりではない．

### 現在の回帰テストが主に覆うもの

[`test/type-error/README.md`](../../egison/test/type-error/README.md) の
50，51，53--56 は，異種 matcher コレクション，注釈による能力強化，
構造ホール，単相 matcher 引数の複数利用などを検査する．

設計後は，これらに加えて `mPoly` 型の「スキーム経由の能力強化」と，
`list`／`multiset`／`sortedList` 型の正当なインスタンス化を対にした
専用テストが必要である．

## Lean 機械化との対応

現在の Lean では，能力保存はインスタンス関係の中に表現されていない．

### 無制限の宣言的インスタンス

- [`TypeRel.lean`](../TypePM/TypeRel.lean) の `Scheme.Inst` は，
  量化変数上の任意の型代入でスキーム本体を得る通常の関係である．
- [`Typing.lean`](../TypePM/Typing.lean) の `HasTy.var` は，
  その `Scheme.Inst` をそのまま利用する．
- `HasTy.letE` は通常の自由変数量化を行う．

このため，宣言的関係だけでは `mPoly` の危険なインスタンス化を排除できない．

### 一般化補題が oracle になっている箇所

[`WellTyped.lean`](../TypePM/WellTyped.lean) の `EnvTyped` は，環境内の値が
スキームの全 `Scheme.Inst` について `ValueTy` を持つことを要求する．

[`TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean) の `hgen` は，
`let` で評価された値が一般化スキームの全インスタンスで型付くという補題を
前提として受け取る．ファイルの説明も，無制限な宣言的インスタンス化では
matcher 添字の剛性を失うため，この前提を将来の Algorithm W で放電する必要が
あると明記している．

### 主要型

[`Principal.lean`](../TypePM/Metatheory/Principal.lean) は，一方向マッチング
アルゴリズムの健全性・完全性など固定済みの局所部分を含むが，
能力保存つき Algorithm W と主要型全体は実装されていない．

また `ValueTy.matcherV` はある具体的な `Matcher τ` で matcher 値を型付けるが，
「この値を最初に構成した導出の能力」を通常の型とは別に保持していない．
採用設計によっては，値型付けや環境型付けにも由来証拠を追加する必要がある．

## 決定すべき質問

1. matcher の「固有能力」を何で表すか．型の骨格，別添字，制約，証明オブジェクト，
   または値の生成由来のいずれか．
2. `Matcher a` の `a` と `Matcher [a]` の内側の `a` を区別する一般原理は何か．
3. 同じ `a` が `MatcherSlot a a -> Matcher [a]` の入力と出力に現れるとき，
   どの量化・置換を許すか．
4. `something : ∀a. Matcher a` はどの意味で多相か．任意の裸変数能力の
   改名だけを許すのか，slot 消費時にターゲット型だけを合わせるのか．
5. matcher を関数・タプル・データ構造へ格納した場合，能力要約をどう合成するか．
6. 能力保存関係を通常の `Scheme.Inst` の置換とするか，別の
   インスタンス前順序とするか．
7. 関係は反射的・推移的・改名不変・代入合成可能であるか．
8. Algorithm W は能力変数または制約をどの時点で一般化し，利用時にどう新鮮化するか．
9. 型クラス制約を持つ `sortedList` では，能力制約とクラス制約を同じ
   限定スキームに載せるか．
10. 保守的な値制限を最終仕様とする余地があるか，それとも annotation-free な
    matcher 多相を維持することを必須とするか．
11. 既存 Egison の `instantiate`，`unifyG`，matcher リテラル検査例外のうち，
    どれを仕様として残し，どれを新関係へ置換するか．

## 受入条件

設計を「解決済み」とするには，少なくとも次を満たすこと．

- [ ] 能力保存スキームインスタンス関係が形式的に定義されている．
- [ ] `mPoly : ∀a. Matcher a` から `Matcher [Integer]` への危険な能力強化が
      導出できない．
- [ ] `f : ∀a. a -> Matcher a` の通常引数から matcher 添字を具体化する経路でも，
      定義元の裸変数能力が保存され，cons site が拒否される．
- [ ] `∀a. MatcherSlot a a -> Matcher [a]` の `a := Integer` が導出できる．
- [ ] `something`／`eq` の正当な裸変数スロット利用が受理される．
- [ ] 積 matcher，高階関数，`let`，トップレベル定義，データ格納を含む
      正負のテスト行列がある．
- [ ] インスタンス関係の反射性，推移性，改名不変性，代入合成補題が証明される．
- [ ] Algorithm W の一般化・インスタンス化手続きが決定可能で，健全である．
- [ ] 最汎インスタンス補題が証明され，主要型または限定主要型を正確に述べられる．
- [ ] Lean の `hgen` を oracle ではなく，能力保存つき一般化補題から供給できる．
- [ ] 実行時 matcher 値の定義元能力と，利用時のスキームインスタンスの対応が
      `ValueTy`／`EnvTyped` 上で証明される．
- [ ] 条件付き定理から能力許容性の仮定を除ける．
- [ ] 論文の英語版・日本語版，Egison 実装，Lean 定義，回帰テストが同期している．

## 参照ポインタ

- 論文：
  [`main.tex`](../../type-pm-paper/main.tex) の `sec:rigidity`,
  `sec:metatheory`, `thm:principal-type`, `app:algorithm-w`,
  `app:principal-type-proofs`, `app:proof-cases`
- 日本語版：
  [`ja/main.tex`](../../type-pm-paper/ja/main.tex) の同じラベル
- 型スキーム：
  [`TypePM/Syntax.lean`](../TypePM/Syntax.lean) の `Scheme`
- 宣言的インスタンス：
  [`TypePM/TypeRel.lean`](../TypePM/TypeRel.lean) の `Scheme.Inst`
- 変数参照・`let`：
  [`TypePM/Typing.lean`](../TypePM/Typing.lean) の `HasTy.var`, `HasTy.letE`
- 値・環境型付け：
  [`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean) の `ValueTy`, `EnvTyped`
- 一般化 oracle：
  [`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean) の `hgen`
- 主要型の機械化境界：
  [`TypePM/Metatheory/Principal.lean`](../TypePM/Metatheory/Principal.lean)
- Egison の剛性：
  [`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs) の
  `unifyG`, `coerceMatcherToSlot`
- Egison の通常インスタンス化：
  [`Type/Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs) の `instantiate`
- Egison の一般化：
  [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs) の
  `inferIBindingsWithContext`, `inferIRecBindingsWithContext`, `inferITopExpr`
- 現行の型エラーテスト一覧：
  [`test/type-error/README.md`](../../egison/test/type-error/README.md)
