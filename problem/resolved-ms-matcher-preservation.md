# R8：`MS-MATCHER` 保存性の全ケース

## 状態

- 状態：局所ケース分析と構造移送は解決済み
- 論文での表示：青字（`\new`）
- 最終定理：P1/P2 に由来する oracle の下で条件付き

## 問題

user-defined matcher の保存性を general constructor clause だけで説明すると，
実際の節選択と規則の全分岐を覆えない．少なくとも次がある．

- primitive-pattern pattern が失敗して次節へ進む
- data-pattern arm が失敗して次 arm へ進む
- general constructor/tuple clause
- nested constructor，wildcard，value-pattern を含む refinement clause
- `PPP-WILD`／`PPP-VAL` の zero-hole clause
- 最終 catch-all

さらに，primitive-pattern pattern の穴から抽出した利用者 sub-pattern の構造要求と，
matcher definition 側の hole slot の構造要求を接続する補題が欠けていた．
target 型の単一化だけでは structural witness を移送できない．

以前の catch-all 説明には，decomposition body `N` を `τ → [τ]` の関数のように
扱う誤りもあった．実際には `tgt : τ` を束縛した文脈で型 `[\tau]` を持つ式である．

## 固定した解決

### Structural-Hole Transfer

pp-match と，利用者 pattern／primitive-pattern pattern の型付けを同時に追う．
matcher definition の hole pair を `(κ_l ▷ λ_l)`，抽出された利用者 sub-pattern の
dual を `(σ_l ▷ τ_l)` とすると，構造側に

```text
κ_l ⊑ σ_l
```

を得る．証明は pp-match 導出の帰納であり，target substitution を構造側へ
混ぜない．constructor/tuple の fresh structural instantiation と，top-level
structural witness の制限・合成だけを使う．

### 全節ケース

保存証明は次を明示的に分ける．

1. PP failure：状態の型情報を変えず，後続節へ進む．
2. DP failure：選択済み節の型情報を保ったまま，後続 arm へ進む．
3. general/refinement：arm body と next matcher を prevailing target substitution
   の下で評価し，Structural-Hole Transfer と slot invariant で successor atoms を作る．
4. `PPP-VAL`：捕捉結果の型を評価保存 premise から得る．
5. `PPP-WILD`／zero-hole：空 tuple と `()` を正しく扱う．
6. catch-all：`tgt : τ` の下の `N : [τ]` と，一つの next matcher `M` を使う．

R2 の `matcher-dispatchable` と R3 の catch-all-last により，
catch-all ケースへ来るのは
変数，ワイルドカード，未捕捉の値パターンだけになる．

## 論文との対応

- Lemma “Structural-Hole Transfer”
- Conditional Type Safety part (b)
- Appendix の `MS-MATCHER-*` 全ケース
- `multiset` consistency example の catch-all 型付け

## Egison 実装との対応

R8 は主として論文と Lean の保存性証明の補修である．Egison の実行経路は
[`Core.hs`](../../egison/hs-src/Language/Egison/Core.hs) の
`inductiveMatch`／`primitivePatPatternMatch` と matcher arm 処理に対応する．

静的側では [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs) の
`inferDataClauseWithCheck` が decomposition body の返り値を
hole target tuple のリスト型へ単一化する．next matcher の構造検査は一般には
実装されるが，単一式が複数穴を供給する場合は完全な deferred component check が
skip される．先頭穴への eager guard と hole target consistency check は残る．
論文・Lean はこの場合に明示タプルを要求するので，skip は仕様上認めた代替経路
ではない．また明示タプルの各成分についても，現実装は式の構文分類により検査を
省略し得る．正確な補修条件は
[R12](resolved-next-matcher-slot-checking.md) に分離して記録する．

したがって R8 の紙上保存証明が，Egison checker による formal consistency 全条件の
完全強制を意味するわけではない．

## Lean 機械化との対応

[`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean) の
`type_safety_b_at`／`type_safety_b` は Step の全14分岐を証明する．
`MS-MATCHER` の再構成では，`buildAtom`／`buildAtoms`，slot inversion，
Coverage/ordering の排他不変量などを使う．

[`TypePM/Metatheory/Preservation.lean`](../TypePM/Metatheory/Preservation.lean) の
`ppp_core`／`ppp_list`／`ppp_preservation` が pp-match の抽出 pattern と
捕捉環境を運ぶ．Lean には論文と同名の独立した
`structural_hole_transfer` 定理はなく，`StructReaches` と atom 再構成の補題群へ
分解されている．

`type_safety_b` の Lean term は完成しているが，次の oracle を premise に持つ．

- `hevG`：評価結果の型付け。`PPP-VAL` では P1 の穴も覆う．
- `hclorc`：matcher clause typing の利用点への輸送。
- `hinstF`：pattern-function body derivation の利用点への輸送。

`hclorc` と一般化関連は主に P2 の境界である．`hinstF` は
pattern-function dual scheme と body derivation の輸送に関する，P2 とは独立した
機械化ギャップである．

## 保証範囲

R8 で解決したのは，必要な構造補題，節ごとの場合分け，catch-all の正しい型である．
次は含まない．

- `PPP-VAL` の評価型 premise を source typing だけから得ること（P1）
- next matcher の capability を scheme lookup 後も保つこと（P2）
- pattern-function dual scheme から利用点の body derivation を輸送すること
- Egison checker が形式条件を全 matcher に強制すること
- Lean の oracle interface を論文の `Adm` だけから導くこと

## 回帰確認

- refinement clause を general clause の証明へ暗黙に吸収しない．
- PP failure と DP failure を selected-clause success と別に扱う．
- catch-all body `N` を関数型にしない．
- structural witness と target unifier を混ぜない．
- `PPP-VAL` と next matcher capability の未放電 premise を明記する．
