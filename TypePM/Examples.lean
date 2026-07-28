import TypePM.Exec
import TypePM.Metatheory.Polymorphism
import TypePM.Metatheory.Adequacy

/-!
# 論文の実測例の機械検証

実行例(`Exec.lean` のインタプリタで `rfl` 検証):
* §2.1:`matchAll [1,2,3] as list something with $x :: $xs -> (x, xs)`
  ⇒ `[(1,[2,3])]`(決定的)
* §2.1:同じパターン・同じ標的で `multiset something`
  ⇒ `[(1,[2,3]), (2,[1,3]), (3,[1,2])]`(非決定的;**マッチャー多相性の実行面**)
* §2.4:`matchAll [1,1] as multiset something with pair $x [] -> x` ⇒ `[1,1]`
  (パターン関数・MNode 機構・非線形 #pat)
* 付録 A.1:`matchAll (1,2) as unorderedPair something with ($x, #1) -> x` ⇒ `[2]`
  (積型のユーザ定義マッチャー・PPP-TUPLE)

型付け例(導出を明示構成):
* `$x :: $xs` の双対判定:構造 [α'] ▷ 標的 [α]、Δ = {x : α, xs : [α]}
* 双対検査:cons パターンの構造添字は `something` を却下し、
  リスト型マッチャーを受理する(§4.4「The structural check」)
* `matchAll 3 as something with $x -> x : [Int]` の T-MATCHALL 完全導出
  (Theorem 5.1 `matcher_polymorphism` の適用実例)

マッチャーの元言語定義は論文 §2.3 の `multiset`(cons 節は
`matchAll tgt as list m with $hs ++ $x :: $ts -> (x, hs ++ ts)` そのまま)と
標準ライブラリの `list`・`unorderedPair`。multiset の ++ 節・#$val 節は
実行例に不要なので省く(README)。
-/

namespace TypePM
namespace Examples

/-! ## 元言語の構成補助 -/

/-- リスト式 [e₁, …, e_k] -/
def lst (es : List Expr) : Expr :=
  es.foldr (fun e acc => .ctor "cons" [e, acc]) (.ctor "nil" [])

/-- リスト値 -/
def lstV (vs : List Value) : Value := mkListV vs

/-- 空リスト式 -/
def nilE : Expr := .ctor "nil" []

/-- [()] (0 穴節の成功アーム本体) -/
def unitListE : Expr := .ctor "cons" [.tuple [], nilE]

/-! ## list マッチャー (論文 §2.3・付録 A) -/

/-- `def list {a} (m : MatcherSlot a a) : Matcher [a]`。
    nil 節・cons 節(決定的)・join 節(連続分割)・catch-all。 -/
def listM : Expr :=
  .fix "list" "m" (.matcher
    [ -- | [] as () with [] -> [()] | _ -> []
      (.ctor "nil" [], .tuple [],
        [(.ctor "nil" [], unitListE), (.wild, nilE)]),
      -- | $ :: $ as (m, list m) with $x :: $xs -> [(x, xs)] | [] -> []
      (.ctor "cons" [.hole, .hole],
        .tuple [.var "m", .app (.var "list") (.var "m")],
        [(.ctor "cons" [.var "x", .var "xs"],
            .ctor "cons" [.tuple [.var "x", .var "xs"], nilE]),
         (.ctor "nil" [], nilE)]),
      -- | $ ++ $ as (list m, list m) with $tgt -> splits tgt
      (.ctor "join" [.hole, .hole],
        .tuple [.app (.var "list") (.var "m"), .app (.var "list") (.var "m")],
        [(.var "tgt", .prim .splits [.var "tgt"])]),
      -- | $ as something with $tgt -> [tgt]
      (.hole, .something, [(.var "tgt", .ctor "cons" [.var "tgt", nilE])])])

/-! ## multiset マッチャー (論文 §2.3) -/

/-- `def multiset {a} (m : MatcherSlot a a) : Matcher [a]`。
    cons 節の分解関数は論文どおり
    `matchAll tgt as list m with $hs ++ $x :: $ts -> (x, hs ++ ts)`。 -/
def multisetM : Expr :=
  .fix "multiset" "m" (.matcher
    [ (.ctor "nil" [], .tuple [],
        [(.ctor "nil" [], unitListE), (.wild, nilE)]),
      (.ctor "cons" [.hole, .hole],
        .tuple [.var "m", .app (.var "multiset") (.var "m")],
        [(.var "tgt",
          .matchAll (.var "tgt") (.app (.var "list") (.var "m"))
            (.pctor "join" [.pvar "hs", .pctor "cons" [.pvar "x", .pvar "ts"]])
            (.tuple [.var "x", .prim .append [.var "hs", .var "ts"]]))]),
      (.hole, .something, [(.var "tgt", .ctor "cons" [.var "tgt", nilE])])])

/-! ## unorderedPair マッチャー (付録 A.1) -/

/-- 一般タプル節が対を両順で分解する(組み込みタプルパターンの
    ユーザ定義非決定的意味論)。 -/
def uoPairM : Expr :=
  .lam "m" (.matcher
    [ (.tuple [.hole, .hole], .tuple [.var "m", .var "m"],
        [(.tuple [.var "x", .var "y"],
          .ctor "cons" [.tuple [.var "x", .var "y"],
            .ctor "cons" [.tuple [.var "y", .var "x"], nilE]])]),
      (.hole, .something, [(.var "tgt", .ctor "cons" [.var "tgt", nilE])])])

/-! ## パターン関数 pair (論文 §2.4) -/

/-- `def pattern pair {a} (pat1 : a) (pat2 : [a]) : [a] :=
      ($pat & ~pat1) :: #pat :: ~pat2`
    記録された双対スキーム(§4.3):
    pair : ∀ a β. Pattern (β ▷ a) → Pattern ([β] ▷ [a]) → Pattern ([β] ▷ [a])
    (var 0 = a, var 1 = β)。 -/
def pairSig : PatFunSig where
  nparams  := 2
  params   := ["pat1", "pat2"]
  argDuals := [(.var 1, .var 0), (Ty.listT (.var 1), Ty.listT (.var 0))]
  resDual  := (Ty.listT (.var 1), Ty.listT (.var 0))
  body     := .pctor "cons"
    [.pand (.pvar "pat") (.embed "pat1"),
     .pctor "cons" [.pval (.var "pat"), .embed "pat2"]]

/-- 例で使う Σ_F -/
def SFex : SigF := [("pair", pairSig)]

/-- 例で使う Σ_P(inductive pattern [a] := [] | (::) a [a] | (++) [a] [a]) -/
def SPex : SigP :=
  [("nil",  ⟨1, [], Ty.listT (.var 0)⟩),
   ("cons", ⟨1, [.var 0, Ty.listT (.var 0)], Ty.listT (.var 0)⟩),
   ("join", ⟨1, [Ty.listT (.var 0), Ty.listT (.var 0)], Ty.listT (.var 0)⟩)]

/-- 例で使う Σ_D(data [a] := [] | (::) a [a]) -/
def SDex : SigD :=
  [("nil",  ⟨1, [], Ty.listT (.var 0)⟩),
   ("cons", ⟨1, [.var 0, Ty.listT (.var 0)], Ty.listT (.var 0)⟩)]

/-- 共通の定義環境:list・multiset・uoPair を束ねて本体 e を評価 -/
def withDefs (e : Expr) : Expr :=
  .letE "list" listM (.letE "multiset" multisetM (.letE "uoPair" uoPairM e))

/-! ## 実行例 1 (§2.1):list は決定的 -/

/-- `matchAll [1,2,3] as list something with $x :: $xs -> (x, xs)` -/
def ex1 : Expr := withDefs <|
  .matchAll (lst [.lit 1, .lit 2, .lit 3])
    (.app (.var "list") .something)
    (.pctor "cons" [.pvar "x", .pvar "xs"])
    (.tuple [.var "x", .var "xs"])

/-- ⇒ `[(1, [2,3])]`(**機械検証済み**) -/
example :
    evalF SFex 1000 [] ex1 =
      some (lstV [.tuple [.lit 1, lstV [.lit 2, .lit 3]]]) := by
  rfl

/-! ## 実行例 2 (§2.1):multiset は非決定的(マッチャー多相性の実行面) -/

/-- 同じパターン・同じ標的、マッチャーだけ multiset に替える -/
def ex2 : Expr := withDefs <|
  .matchAll (lst [.lit 1, .lit 2, .lit 3])
    (.app (.var "multiset") .something)
    (.pctor "cons" [.pvar "x", .pvar "xs"])
    (.tuple [.var "x", .var "xs"])

/-- ⇒ `[(1,[2,3]), (2,[1,3]), (3,[1,2])]`(**機械検証済み**、順序も論文どおり) -/
example :
    evalF SFex 1000 [] ex2 =
      some (lstV
        [.tuple [.lit 1, lstV [.lit 2, .lit 3]],
         .tuple [.lit 2, lstV [.lit 1, .lit 3]],
         .tuple [.lit 3, lstV [.lit 1, .lit 2]]]) := by
  rfl

/-! ## 実行例 3 (§2.4):パターン関数 pair(MNode・非線形 #pat) -/

/-- `matchAll [1,1] as multiset something with pair $x [] -> x` -/
def ex3 : Expr := withDefs <|
  .matchAll (lst [.lit 1, .lit 1])
    (.app (.var "multiset") .something)
    (.papp "pair" [.pvar "x", .pctor "nil" []])
    (.var "x")

/-- ⇒ `[1, 1]`(**機械検証済み**;
    MS-PATFUN-ENTER / MS-MNODE-VARPAT / MS-MNODE-DONE と
    θ_f 局所化(体内 $pat が外へ漏れない)の実行を含む) -/
example :
    evalF SFex 1000 [] ex3 = some (lstV [.lit 1, .lit 1]) := by
  rfl

/-! ## 実行例 4 (付録 A.1):unorderedPair(積型のユーザ定義マッチャー) -/

/-- `matchAll (1,2) as unorderedPair something with ($x, #1) -> x` -/
def ex4 : Expr := withDefs <|
  .matchAll (.tuple [.lit 1, .lit 2])
    (.app (.var "uoPair") .something)
    (.ptuple [.pvar "x", .pval (.lit 1)])
    (.var "x")

/-- ⇒ `[2]`(**機械検証済み**;交換分解 (2,1) 側だけが #1 を満たす) -/
example :
    evalF SFex 1000 [] ex4 = some (lstV [.lit 2]) := by
  rfl

/-! ## 型付け例 1:`$x :: $xs` の双対判定 (§4.2)

構造 [α'](α' = var 10)▷ 標的 [α](α = var 0)、Δ = {x : α, xs : [α]}。 -/

example :
    PatTy SDex SPex SFex [] [] []
      (.pctor "cons" [.pvar "x", .pvar "xs"])
      (Ty.listT (.var 10)) (Ty.listT (.var 0))
      [("x", .var 0), ("xs", Ty.listT (.var 0))] := by
  refine PatTy.pctor (ss := [.var 10]) (ts := [.var 0])
    (sig := ⟨1, [.var 0, Ty.listT (.var 0)], Ty.listT (.var 0)⟩)
    (duals := [(.var 10, .var 0), (Ty.listT (.var 10), Ty.listT (.var 0))])
    rfl ?_ rfl rfl
  exact PatTys.cons (PatTy.pvar (by simp))
    (PatTys.cons (PatTy.pvar (by simp)) PatTys.nil)

/-! ## 型付け例 2:双対検査の構造条件 (§4.4)

cons パターンの構造添字 [α'] は `something`(裸変数 Matcher β)を却下し、
リスト型マッチャー(Matcher [a])を受理する。 -/

/-- `something` の却下:Matcher β の任意の改名 τm' について τm' ⊑ [α'] は不成立
    (代入は積・構成子を変数に潰せない)。 -/
theorem something_rejected_at_cons {β : TyVar} :
    ∀ τm', RenamesTo (.var β) τm' → ¬ OneWay (Ty.listT (.var 10)) τm' := by
  rintro τm' ⟨r, -, hr⟩ ⟨θ, -, h⟩
  simp [Ty.applyRen] at hr
  subst hr
  simp [Ty.listT, Ty.applyTS, applyTSList] at h

/-- リスト型マッチャーの受理:[a] ⊑ [α'](witness {α' ↦ a}、Lemma 5.2 により一意) -/
theorem list_matcher_admitted :
    OneWay (Ty.listT (.var 10)) (Ty.listT (.var 0)) :=
  ⟨[(10, .var 0)], by simp [TySubst.dom, Ty.listT, Ty.ftv, ftvList], rfl⟩

/-- 変数パターン(構造添字が裸変数)ではどのマッチャーも構造条件を通る:
    something(改名後 Matcher β')も β' ⊑ α で受理。 -/
theorem something_admitted_at_var :
    OneWay (.var 0) (.var 6) :=
  ⟨[(0, .var 6)], by simp [TySubst.dom, Ty.ftv], rfl⟩

/-! ## 型付け例 3:T-MATCHALL の完全導出と Theorem 5.1 の適用実例

`matchAll 3 as something with $x -> x : [Int]`。
Theorem 5.1(`matcher_polymorphism`)をそのまま適用する:
パターン導出はマッチャーと独立に一度だけ与える。 -/

example :
    HasTy SDex SPex SFex []
      (.matchAll (.lit 3) .something (.pvar "x") (.var "x"))
      (Ty.listT .int) := by
  refine matcher_polymorphism
    (τp := .var 0) (τm := .var 5) (τm' := .var 6) (Δ := [("x", .int)])
    (PatTy.pvar (by simp)) HasTy.lit HasTy.something
    ⟨fun a => a + 1, fun _ _ h => Nat.add_right_cancel h, rfl⟩   -- fresh_rename
    something_admitted_at_var                       -- 構造:β' ⊑ α
    ⟨[(5, .int)], rfl⟩                              -- 標的:β ~ Int
    (HasTy.var rfl ⟨[], by simp [TySubst.dom], rfl⟩)

/-! ## 関係的意味論への持ち上げ

適切性 `evalF_sound`(Metatheory/Adequacy.lean、証明済み)により、
上の 4 実行例は関係的意味論 ⇓ の導出の存在まで機械的に保証される。 -/

example : Eval SFex [] ex1 (lstV [.tuple [.lit 1, lstV [.lit 2, .lit 3]]]) :=
  evalF_sound (n := 1000) (by rfl)

example : Eval SFex [] ex2 (lstV
    [.tuple [.lit 1, lstV [.lit 2, .lit 3]],
     .tuple [.lit 2, lstV [.lit 1, .lit 3]],
     .tuple [.lit 3, lstV [.lit 1, .lit 2]]]) :=
  evalF_sound (n := 1000) (by rfl)

example : Eval SFex [] ex3 (lstV [.lit 1, .lit 1]) :=
  evalF_sound (n := 1000) (by rfl)

example : Eval SFex [] ex4 (lstV [.lit 2]) :=
  evalF_sound (n := 1000) (by rfl)

end Examples
end TypePM
