import TypePM.TypeRel

/-!
# λ_PM の操作的意味論 (論文 §3.3, Fig 2・Fig 3)

* `Value.structEq` — 組み込み構造的等価 ≡(全域;closure/matcher 値上は常に false)
* `pdMatch` — primitive data pattern のマッチ(決定的・全域なので関数)
* `PPM` — pattern-on-pattern マッチ ≈(PPP-VAL が式評価を含むため関係)
* `MAtom` — 6 項関係 p ~^ρ_m v ⇓ [a⃗ᵢ]ᵢ, θ'
* `Step` — 状態簡約 s → [s₁,…,s_l](MS-REDUCE + Fig 3 の MNode 規則)
* `Search` — 探索 s ⇛ θ⃗
* `Eval` — 式評価 ρ, e ⇓ v(matchAll は有限リスト読み;論文の遅延ストリームの
  per-element 読み(§3.1 脚注・Fig 2 キャプション)に対応 — README 設計判断)

5 つの判断は MS-MATCHER(分解関数の評価)・EV-MATCHALL(探索)を介して
相互再帰するため、単一の mutual ブロックで定義する。
-/

namespace TypePM

/-! ## 組み込み構造的等価 ≡ (§3.3) -/

mutual
/-- 構造的等価 ≡:一階値上の構造再帰、closure・matcher 値上は false(全域)。 -/
def Value.structEq : Value → Value → Bool
  | .lit n,      .lit n'       => n == n'
  | .ctor c vs,  .ctor c' vs'  => c == c' && structEqList vs vs'
  | .tuple vs,   .tuple vs'    => structEqList vs vs'
  | _,           _             => false

def structEqList : List Value → List Value → Bool
  | [],      []        => true
  | v :: vs, v' :: vs' => v.structEq v' && structEqList vs vs'
  | _,       _         => false
end

/-! ## プリミティブの δ 規則 -/

/-- δ:`append` は ++、`splits` は連続分割 [(take i, drop i)]ᵢ の列挙。 -/
def primEval : PrimOp → List Value → Option Value
  | .append, [v₁, v₂] => do
      let l₁ ← listOfV v₁
      let l₂ ← listOfV v₂
      pure (mkListV (l₁ ++ l₂))
  | .splits, [v] => do
      let l ← listOfV v
      pure (mkListV ((List.range (l.length + 1)).map fun i =>
        .tuple [mkListV (l.take i), mkListV (l.drop i)]))
  | _, _ => none

/-! ## primitive data pattern マッチ (PDM-VAR/WILD/CON/TUPLE) -/

mutual
/-- dp ≈ v ⇓ ρ_d(決定的・全域なので Option 値関数;none = 失敗)。
    dp で外側・v で内側の入れ子照合(健全性証明の `split` を単純にする)。 -/
def pdMatch : DPat → Value → Option Env
  | .var z, v => some [(z, v)]
  | .wild, _ => some []
  | .ctor C dps, v =>
      match v with
      | .ctor C' vs => if C == C' then pdMatchList dps vs else none
      | _ => none
  | .tuple dps, v =>
      match v with
      | .tuple vs => pdMatchList dps vs
      | _ => none

def pdMatchList : List DPat → List Value → Option Env
  | [], vs =>
      match vs with
      | [] => some []
      | _ => none
  | dp :: dps, vs =>
      match vs with
      | v :: vs' => do
          let ρ₁ ← pdMatch dp v
          let ρ₂ ← pdMatchList dps vs'
          pure (ρ₁ ++ ρ₂)
      | _ => none
end

/-! ## pattern-on-pattern マッチの形状検査

PPM の失敗(MS-MATCHER-PP-FAIL の premise)は構文的形状のみで決まる。 -/

mutual
def ppShapeOK : PPat → Pattern → Bool
  | .hole,       _           => true
  | .wild,       .wild       => true
  | .pval _,     .pval _     => true
  | .ctor c pps, .pctor c' ps => c == c' && ppShapeOKList pps ps
  | .tuple pps,  .ptuple ps  => ppShapeOKList pps ps
  | _,           _           => false

def ppShapeOKList : List PPat → List Pattern → Bool
  | [],        []      => true
  | pp :: pps, p :: ps => ppShapeOK pp p && ppShapeOKList pps ps
  | _, _ => false
end

/-- 変数・ワイルドカード・値パターンか(MS-PROD-SOME の側条件) -/
def Pattern.isPrimForm : Pattern → Bool
  | .pvar _ => true
  | .wild   => true
  | .pval _ => true
  | _       => false

/-- マッチャー節照合の対象になるパターン形(MS-MATCHER 系規則の側条件)。
    and/or/パターン関数適用/~x は専用規則が構文主導で先に処理する
    (実装 `processMState'` のディスパッチ準拠;これが無いと例えば
    `(x::xs) & $y` が catch-all 節に捕まり、部分パターンの構成子が
    something に到達する行き詰まり分岐が生じる — 細部その 4(ii))。 -/
def Pattern.isClauseForm : Pattern → Bool
  | .pvar _    => true
  | .wild      => true
  | .pval _    => true
  | .pctor _ _ => true
  | .ptuple _  => true
  | _          => false

/-- クロージャ適用時の環境拡張(fix なら自己束縛を積む) -/
def pushArg (self : Option String) (ρ' : Env) (x : String) (eb : Expr) (v : Value) : Env :=
  match self with
  | none   => (x, v) :: ρ'
  | some f => (x, v) :: (f, .closure (some f) ρ' x eb) :: ρ'

/-! ## 意味論の相互帰納的判断 -/

mutual
/-- 式評価 ρ, e ⇓ v (Fig 2 上段;let/matcher/matchAll 以外は標準規則) -/
inductive Eval (SF : SigF) : Env → Expr → Value → Prop where
  | var {ρ x v} :
      ρ.find? x = some v →
      Eval SF ρ (.var x) v
  | lam {ρ x e} :
      Eval SF ρ (.lam x e) (.closure none ρ x e)
  | fix {ρ f x e} :
      Eval SF ρ (.fix f x e) (.closure (some f) ρ x e)
  | app {ρ e₁ e₂ self ρ' x eb v₂ v} :
      Eval SF ρ e₁ (.closure self ρ' x eb) →
      Eval SF ρ e₂ v₂ →
      Eval SF (pushArg self ρ' x eb v₂) eb v →
      Eval SF ρ (.app e₁ e₂) v
  | lit {ρ n} :
      Eval SF ρ (.lit n) (.lit n)
  | tuple {ρ es vs} :
      es.length = vs.length →
      (∀ pr ∈ es.zip vs, Eval SF ρ pr.1 pr.2) →
      Eval SF ρ (.tuple es) (.tuple vs)
  | ctor {ρ c es vs} :
      es.length = vs.length →
      (∀ pr ∈ es.zip vs, Eval SF ρ pr.1 pr.2) →
      Eval SF ρ (.ctor c es) (.ctor c vs)
  | prim {ρ op es vs v} :
      es.length = vs.length →
      (∀ pr ∈ es.zip vs, Eval SF ρ pr.1 pr.2) →
      primEval op vs = some v →
      Eval SF ρ (.prim op es) v
  | letE {ρ x e₁ e₂ v₁ v} :                                    -- EV-LET
      Eval SF ρ e₁ v₁ →
      Eval SF ((x, v₁) :: ρ) e₂ v →
      Eval SF ρ (.letE x e₁ e₂) v
  | something {ρ} :
      Eval SF ρ .something .something
  | matcher {ρ cls} :                                          -- EV-MATCHER
      Eval SF ρ (.matcher cls) (.matcherV ρ cls)
  | matchAll {ρ e_t e_m p body v_t v_m θs vs} :                -- EV-MATCHALL
      Eval SF ρ e_t v_t →
      Eval SF ρ e_m v_m →
      Search SF ⟨[.atom ⟨p, v_m, v_t⟩], ρ, []⟩ θs →
      θs.length = vs.length →
      (∀ pr ∈ θs.zip vs, Eval SF (pr.1 ++ ρ) body pr.2) →
      Eval SF ρ (.matchAll e_t e_m p body) (mkListV vs)

/-- pattern-on-pattern マッチ pp ≈^ρ p ⇓ (PPP-HOLE/WILD/VAL/CON/TUPLE)。
    結果 `none` は失敗(**fail**)。 -/
inductive PPM (SF : SigF) : Env → PPat → Pattern → Option (List Pattern × Env) → Prop where
  | hole {ρ p} :
      PPM SF ρ .hole p (some ([p], []))
  | wild {ρ} :
      PPM SF ρ .wild .wild (some ([], []))
  | pval {ρ y M v} :                                           -- PPP-VAL
      Eval SF ρ M v →
      PPM SF ρ (.pval y) (.pval M) (some ([], [(y, v)]))
  | ctor {ρ c pps ps rs} :                                     -- PPP-CON
      pps.length = ps.length →
      (pps.zip ps).length = rs.length →
      (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)) →
      PPM SF ρ (.ctor c pps) (.pctor c ps)
        (some ((rs.map (·.1)).flatten, (rs.map (·.2)).flatten))
  | tuple {ρ pps ps rs} :                                      -- PPP-TUPLE
      pps.length = ps.length →
      (pps.zip ps).length = rs.length →
      (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)) →
      PPM SF ρ (.tuple pps) (.ptuple ps)
        (some ((rs.map (·.1)).flatten, (rs.map (·.2)).flatten))
  | fail {ρ pp p} :
      ppShapeOK pp p = false →
      PPM SF ρ pp p none

/-- マッチング原子の簡約:p ~^ρ_m v ⇓ [a⃗ᵢ]ᵢ, θ'
    (MS-SOME-*/AND/OR/TUPLE/PROD-SOME と MS-MATCHER 系規則)。
    継続 [] は失敗、[ε] は成功。 -/
inductive MAtom (SF : SigF) : Env → Pattern → Value → Value →
    List (List Atom) → Subst → Prop where
  | someWC {ρ v} :                                             -- MS-SOME-WC
      MAtom SF ρ .wild .something v [[]] []
  | someVar {ρ x v} :                                          -- MS-SOME-VAR
      MAtom SF ρ (.pvar x) .something v [[]] [(x, v)]
  | someValEq {ρ e v ve} :                                     -- MS-SOME-VAL-EQ
      Eval SF ρ e ve →
      ve.structEq v = true →
      MAtom SF ρ (.pval e) .something v [[]] []
  | someValNeq {ρ e v ve} :                                    -- MS-SOME-VAL-NEQ
      Eval SF ρ e ve →
      ve.structEq v = false →
      MAtom SF ρ (.pval e) .something v [] []
  | and {ρ p₁ p₂ m v} :                                        -- MS-AND
      MAtom SF ρ (.pand p₁ p₂) m v [[⟨p₁, m, v⟩, ⟨p₂, m, v⟩]] []
  | or {ρ p₁ p₂ m v} :                                         -- MS-OR
      MAtom SF ρ (.por p₁ p₂) m v [[⟨p₁, m, v⟩], [⟨p₂, m, v⟩]] []
  | tuple {ρ ps ms vs} :                                       -- MS-TUPLE
      ps.length = ms.length →
      ms.length = vs.length →
      MAtom SF ρ (.ptuple ps) (.tuple ms) (.tuple vs)
        [(ps.zip (ms.zip vs)).map fun x => ⟨x.1, x.2.1, x.2.2⟩] []
  | prodSome {ρ p ms v} :                                      -- MS-PROD-SOME
      p.isPrimForm = true →
      MAtom SF ρ p (.tuple ms) v [[⟨p, .something, v⟩]] []
  | matcherPPFail {ρ ρm p v pp M arms cls conts θ'} :          -- MS-MATCHER-PP-FAIL
      p.isClauseForm = true →                                  -- 節適用形(細部その 4(ii))
      PPM SF ρ pp p none →
      MAtom SF ρ p (.matcherV ρm cls) v conts θ' →
      MAtom SF ρ p (.matcherV ρm ((pp, M, arms) :: cls)) v conts θ'
  | matcherDPFail {ρ ρm p v pp M dp N arms cls ps' ρp conts θ'} :  -- MS-MATCHER-DP-FAIL
      p.isClauseForm = true →
      PPM SF ρ pp p (some (ps', ρp)) →
      pdMatch dp v = none →
      MAtom SF ρ p (.matcherV ρm ((pp, M, arms) :: cls)) v conts θ' →
      MAtom SF ρ p (.matcherV ρm ((pp, M, (dp, N) :: arms) :: cls)) v conts θ'
  | matcher {ρ ρm p v pp M dp N arms cls ps' ρp ρd vN tuples vss vM ms} :  -- MS-MATCHER
      p.isClauseForm = true →
      PPM SF ρ pp p (some (ps', ρp)) →
      pdMatch dp v = some ρd →
      Eval SF (ρd ++ ρp ++ ρm) N vN →
      listOfV vN = some tuples →
      tuples.mapM (decodeTuple ps'.length) = some vss →
      Eval SF ρm M vM →
      decodeTuple ps'.length vM = some ms →
      MAtom SF ρ p (.matcherV ρm ((pp, M, (dp, N) :: arms) :: cls)) v
        (vss.map fun vs => (ps'.zip (ms.zip vs)).map fun x => ⟨x.1, x.2.1, x.2.2⟩) []

/-- 状態簡約 s → [s₁, …, s_l] (MS-REDUCE + Fig 3 の MNode 規則) -/
inductive Step (SF : SigF) : MState → List MState → Prop where
  | reduce {S ρ θ p m v conts θ'} :                            -- MS-REDUCE
      MAtom SF (θ ++ ρ) p m v conts θ' →
      Step SF ⟨.atom ⟨p, m, v⟩ :: S, ρ, θ⟩
        (conts.map fun as => ⟨as.map .atom ++ S, ρ, θ' ++ θ⟩)
  | patfunEnter {S ρ θ f qs m v sig} :                         -- MS-PATFUN-ENTER
      (List.find? (fun pr => pr.1 == f) SF) = some (f, sig) →
      sig.params.length = qs.length →
      Step SF ⟨.atom ⟨.papp f qs, m, v⟩ :: S, ρ, θ⟩
        [⟨.mnode [.atom ⟨sig.body, m, v⟩] ρ [] (sig.params.zip qs) :: S, ρ, θ⟩]
  | mnodeStep {S ρ θ t Srest ρf θf piE ss} :                   -- MS-MNODE-STEP
      -- 論文の規則は内側先頭が原子の場合のみだが、パターン関数のネスト適用で
      -- 内側先頭が MNode になる状態が生じるため任意の木 t に一般化する
      -- (README 設計判断・調査報告参照)。
      (∀ y m v, t = .atom ⟨.embed y, m, v⟩ →
        (List.find? (fun pr => pr.1 == y) piE) = none) →
      Step SF ⟨t :: Srest, ρf, θf⟩ ss →
      Step SF ⟨.mnode (t :: Srest) ρf θf piE :: S, ρ, θ⟩
        (ss.map fun s' => ⟨.mnode s'.S ρf s'.θ piE :: S, ρ, θ⟩)
  | mnodeVarpat {S ρ θ y q m v Srest ρf θf piE} :                -- MS-MNODE-VARPAT
      (List.find? (fun pr => pr.1 == y) piE) = some (y, q) →
      Step SF ⟨.mnode (.atom ⟨.embed y, m, v⟩ :: Srest) ρf θf piE :: S, ρ, θ⟩
        [⟨.atom ⟨q, m, v⟩ :: .mnode Srest ρf θf piE :: S, ρ, θ⟩]
  | mnodeDone {S ρ θ ρf θf piE} :                                -- MS-MNODE-DONE
      Step SF ⟨.mnode [] ρf θf piE :: S, ρ, θ⟩ [⟨S, ρ, θ⟩]

/-- 探索 s ⇛ θ⃗ (SEARCH-DONE / SEARCH-STEP) -/
inductive Search (SF : SigF) : MState → List Subst → Prop where
  | done {ρ θ} :
      Search SF ⟨[], ρ, θ⟩ [θ]
  | step {s ss θss} :
      Step SF s ss →
      ss.length = θss.length →
      (∀ pr ∈ ss.zip θss, Search SF pr.1 pr.2) →
      Search SF s θss.flatten
end

end TypePM
