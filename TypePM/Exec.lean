import TypePM.Semantics

/-!
# 実行可能意味論(fuel 付きインタプリタ)

`Semantics.lean` の関係的意味論を決定的に実装する(DFS、節・アームは宣言順)。
`Examples.lean` が論文の実測例をこのインタプリタ上で `rfl` 検証する。
全関数は fuel を毎呼び出しで 1 減らすので停止性は自明。

健全性(`evalF … = some v → Eval …` など)は
`Metatheory/Adequacy.lean` で **証明済み**。
-/

namespace TypePM

/-- MNode 先頭の木が「Π にヒットする変数パターン原子」かの判定
    (MS-MNODE-VARPAT の発火条件;適切性証明を単純にするための分離)。 -/
def piHit (piE : PiEnv) : Tree → Option (String × Pattern × Value × Value)
  | .atom a =>
      match a.p with
      | .embed y =>
          match List.find? (fun pr => pr.1 == y) piE with
          | some (_, q) => some (y, q, a.m, a.v)
          | none => none
      | _ => none
  | .mnode _ _ _ _ => none

/-- 原子のパターンが「Σ_F にヒットするパターン関数適用」かの判定
    (MS-PATFUN-ENTER の発火条件;適切性証明を単純にするための分離)。 -/
def pappHit (SF : SigF) : Pattern → Option (String × List Pattern × PatFunSig)
  | .papp f qs =>
      match List.find? (fun pr => pr.1 == f) SF with
      | some (_, sig) =>
          if sig.params.length == qs.length then some (f, qs, sig) else none
      | none => none
  | _ => none

mutual

/-- 式評価(EV-* 規則の実装) -/
def evalF (SF : SigF) : Nat → Env → Expr → Option Value
  | 0, _, _ => none
  | fuel+1, ρ, e =>
    match e with
    | .var x      => ρ.find? x
    | .lam x eb   => some (.closure none ρ x eb)
    | .fix f x eb => some (.closure (some f) ρ x eb)
    | .app e₁ e₂  => do
        let v₁ ← evalF SF fuel ρ e₁
        let v₂ ← evalF SF fuel ρ e₂
        match v₁ with
        | .closure self ρ' x eb => evalF SF fuel (pushArg self ρ' x eb v₂) eb
        | _ => none
    | .lit n      => some (.lit n)
    | .tuple es   => do pure (.tuple (← evalListF SF fuel ρ es))
    | .ctor c es  => do pure (.ctor c (← evalListF SF fuel ρ es))
    | .prim op es => do primEval op (← evalListF SF fuel ρ es)
    | .letE x e₁ e₂ => do
        let v₁ ← evalF SF fuel ρ e₁
        evalF SF fuel ((x, v₁) :: ρ) e₂
    | .something  => some .something
    | .matcher cls => some (.matcherV ρ cls)
    | .matchAll e_t e_m p body => do
        let v_t ← evalF SF fuel ρ e_t
        let v_m ← evalF SF fuel ρ e_m
        let θs ← searchF SF fuel ⟨[.atom ⟨p, v_m, v_t⟩], ρ, []⟩
        let vs ← evalBodiesF SF fuel ρ body θs
        pure (mkListV vs)

def evalListF (SF : SigF) : Nat → Env → List Expr → Option (List Value)
  | 0, _, _ => none
  | fuel+1, ρ, es =>
    match es with
    | []       => some []
    | e :: es' => do pure ((← evalF SF fuel ρ e) :: (← evalListF SF fuel ρ es'))

/-- matchAll の各 θᵢ について本体を評価 -/
def evalBodiesF (SF : SigF) : Nat → Env → Expr → List Subst → Option (List Value)
  | 0, _, _, _ => none
  | fuel+1, ρ, body, θs =>
    match θs with
    | []        => some []
    | θ :: θs'  => do
        pure ((← evalF SF fuel (θ ++ ρ) body) :: (← evalBodiesF SF fuel ρ body θs'))

/-- pattern-on-pattern マッチ(外 Option = 燃料切れ、内 Option = マッチ失敗) -/
def ppmF (SF : SigF) : Nat → Env → PPat → Pattern → Option (Option (List Pattern × Env))
  | 0, _, _, _ => none
  | fuel+1, ρ, pp, p =>
    match pp, p with
    | .hole, p'          => some (some ([p'], []))
    | .wild, .wild       => some (some ([], []))
    | .pval y, .pval M   => do pure (some ([], [(y, ← evalF SF fuel ρ M)]))
    | .ctor c pps, .pctor c' ps =>
        if c == c' && pps.length == ps.length then
          ppmListF SF fuel ρ pps ps
        else some none
    | .tuple pps, .ptuple ps =>
        if pps.length == ps.length then ppmListF SF fuel ρ pps ps else some none
    | pp', p' =>
        -- 残余の組は必ず形状不一致(健全性証明を単純にするための明示ガード)
        if ppShapeOK pp' p' then none else some none

def ppmListF (SF : SigF) : Nat → Env → List PPat → List Pattern →
    Option (Option (List Pattern × Env))
  | 0, _, _, _ => none
  | fuel+1, ρ, pps, ps =>
    match pps, ps with
    | [], [] => some (some ([], []))
    | pp :: pps', p :: ps' => do
        match ← ppmF SF fuel ρ pp p with
        | none => pure none
        | some (nexts, ρp) =>
          match ← ppmListF SF fuel ρ pps' ps' with
          | none => pure none
          | some (nexts', ρp') => pure (some (nexts ++ nexts', ρp ++ ρp'))
    | _, _ => some none

/-- マッチング原子の簡約(MS-* 規則の実装)。papp は `stepF` が扱う。 -/
def matomF (SF : SigF) : Nat → Env → Pattern → Value → Value →
    Option (List (List Atom) × Subst)
  | 0, _, _, _, _ => none
  | fuel+1, ρ, p, m, v =>
    match p, m with
    | .pand p₁ p₂, _ => some ([[⟨p₁, m, v⟩, ⟨p₂, m, v⟩]], [])
    | .por p₁ p₂, _  => some ([[⟨p₁, m, v⟩], [⟨p₂, m, v⟩]], [])
    | .wild, .something   => some ([[]], [])
    | .pvar x, .something => some ([[]], [(x, v)])
    | .pval e, .something => do
        let ve ← evalF SF fuel ρ e
        if ve.structEq v then pure ([[]], []) else pure ([], [])
    | .ptuple ps, .tuple ms =>
        match v with
        | .tuple vs =>
            if ps.length == ms.length && ms.length == vs.length then
              some ([(ps.zip (ms.zip vs)).map fun x => ⟨x.1, x.2.1, x.2.2⟩], [])
            else none
        | _ => none
    | _, .tuple _ =>
        if p.isPrimForm then some ([[⟨p, .something, v⟩]], []) else none
    | _, .matcherV ρm cls =>
        -- matcher 節へ dispatch 可能な形のみ節照合へ
        -- (MS-MATCHER 系規則の側条件と一致;
        -- and/or は上の行が先に処理し、papp/embed は stepF が扱う)
        if p.isMatcherDispatchable then clausesF SF fuel ρ ρm cls p v else none
    | _, _ => none

/-- MS-MATCHER-PP-FAIL:節を順に試す -/
def clausesF (SF : SigF) : Nat → Env → Env → List Clause → Pattern → Value →
    Option (List (List Atom) × Subst)
  | 0, _, _, _, _, _ => none
  | fuel+1, ρ, ρm, cls, p, v =>
    match cls with
    | [] => none      -- どの節も選ばれない(整型なら起こらない;catch-all)
    | (pp, M, arms) :: cls' => do
        match ← ppmF SF fuel ρ pp p with
        | none => clausesF SF fuel ρ ρm cls' p v
        | some (ps', ρp) => armsF SF fuel ρm ρp arms ps' M v

/-- MS-MATCHER-DP-FAIL / MS-MATCHER:選ばれた節のアームを順に試す -/
def armsF (SF : SigF) : Nat → Env → Env → List (DPat × Expr) → List Pattern →
    Expr → Value → Option (List (List Atom) × Subst)
  | 0, _, _, _, _, _, _ => none
  | fuel+1, ρm, ρp, arms, ps', M, v =>
    match arms with
    | [] => none      -- アーム切れ(整型なら arm exhaustiveness が排除)
    | (dp, N) :: arms' =>
        match pdMatch dp v with
        | none => armsF SF fuel ρm ρp arms' ps' M v
        | some ρd => do
            let vN ← evalF SF fuel (ρd ++ ρp ++ ρm) N
            let tuples ← listOfV vN
            let vss ← tuples.mapM (decodeTuple ps'.length)
            let vM ← evalF SF fuel ρm M
            let ms ← decodeTuple ps'.length vM
            pure (vss.map fun vs =>
              (ps'.zip (ms.zip vs)).map fun x => ⟨x.1, x.2.1, x.2.2⟩, [])

/-- 状態簡約(MS-REDUCE / MS-PATFUN-ENTER / MNode 規則) -/
def stepF (SF : SigF) : Nat → MState → Option (List MState)
  | 0, _ => none
  | fuel+1, s =>
    match s with
    | ⟨[], _, _⟩ => none    -- 終端状態は簡約しない
    | ⟨.atom ⟨p, m, v⟩ :: S, ρ, θ⟩ =>
        match pappHit SF p with
        | some (_, qs, sig) =>                        -- MS-PATFUN-ENTER
            some [⟨.mnode [.atom ⟨sig.body, m, v⟩] ρ [] (sig.params.zip qs) :: S, ρ, θ⟩]
        | none => do                                  -- MS-REDUCE
            let (conts, θ') ← matomF SF fuel (θ ++ ρ) p m v
            pure (conts.map fun as => ⟨as.map .atom ++ S, ρ, θ' ++ θ⟩)
    | ⟨.mnode [] _ _ _ :: S, ρ, θ⟩ => some [⟨S, ρ, θ⟩]
    | ⟨.mnode (t :: Srest) ρf θf piE :: S, ρ, θ⟩ =>
        match piHit piE t with
        | some (_, q, m, v) =>                        -- MS-MNODE-VARPAT
            some [⟨.atom ⟨q, m, v⟩ :: .mnode Srest ρf θf piE :: S, ρ, θ⟩]
        | none => do                                  -- MS-MNODE-STEP
            let ss ← stepF SF fuel ⟨t :: Srest, ρf, θf⟩
            pure (ss.map fun s' => ⟨.mnode s'.S ρf s'.θ piE :: S, ρ, θ⟩)

/-- 探索(SEARCH-DONE / SEARCH-STEP、DFS) -/
def searchF (SF : SigF) : Nat → MState → Option (List Subst)
  | 0, _ => none
  | fuel+1, s =>
    match s with
    | ⟨[], _, θ⟩ => some [θ]
    | s' => do
        let ss ← stepF SF fuel s'
        let θss ← searchListF SF fuel ss
        pure θss.flatten

def searchListF (SF : SigF) : Nat → List MState → Option (List (List Subst))
  | 0, _ => none
  | fuel+1, ss =>
    match ss with
    | [] => some []
    | s :: ss' => do
        pure ((← searchF SF fuel s) :: (← searchListF SF fuel ss'))

end

/-! ## one-way matching の実行可能アルゴリズム (Lemma 5.2 の計算可能性部分) -/

mutual
def Ty.beq : Ty → Ty → Bool
  | .var a, .var b => a == b
  | .int, .int => true
  | .bool, .bool => true
  | .data n ts, .data n' ts' => n == n' && Ty.beqList ts ts'
  | .prod ts, .prod ts' => Ty.beqList ts ts'
  | .fn a b, .fn a' b' => a.beq a' && b.beq b'
  | .matcher t, .matcher t' => t.beq t'
  | .slot a b, .slot a' b' => a.beq a' && b.beq b'
  | _, _ => false

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => t.beq t' && Ty.beqList ts ts'
  | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

mutual
/-- τm ⊑ τp の witness θ を計算する(θ(τp) = τm となる θ を τp の変数上で構成)。
    線形時間;witness の一意性は `oneWay_unique`(TypeRel.lean)。
    (外側で τp、内側で τm をマッチする入れ子構造:健全性証明の `split` を単純にする。) -/
def matchOneWay (τp τm : Ty) (acc : TySubst) : Option TySubst :=
  match τp with
  | .var a =>
      match List.find? (fun pr => pr.1 == a) acc with
      | some (_, t') => if τm.beq t' then some acc else none
      | none => some ((a, τm) :: acc)
  | .int =>
      match τm with
      | .int => some acc
      | _ => none
  | .bool =>
      match τm with
      | .bool => some acc
      | _ => none
  | .data n ts =>
      match τm with
      | .data n' ts' => if n == n' then matchOneWayList ts ts' acc else none
      | _ => none
  | .prod ts =>
      match τm with
      | .prod ts' => matchOneWayList ts ts' acc
      | _ => none
  | .fn a b =>
      match τm with
      | .fn a' b' =>
          match matchOneWay a a' acc with
          | some θ₁ => matchOneWay b b' θ₁
          | none => none
      | _ => none
  | .matcher t =>
      match τm with
      | .matcher t' => matchOneWay t t' acc
      | _ => none
  | .slot a b =>
      match τm with
      | .slot a' b' =>
          match matchOneWay a a' acc with
          | some θ₁ => matchOneWay b b' θ₁
          | none => none
      | _ => none

def matchOneWayList (ts ts' : List Ty) (acc : TySubst) : Option TySubst :=
  match ts with
  | [] =>
      match ts' with
      | [] => some acc
      | _ => none
  | t :: ts =>
      match ts' with
      | t' :: ts' =>
          match matchOneWay t t' acc with
          | some θ₁ => matchOneWayList ts ts' θ₁
          | none => none
      | _ => none
end

end TypePM
