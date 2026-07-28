import TypePM.Metatheory.Preservation

/-!
# Theorem 5.7:マッチャー整合性定理 (Matcher Consistency Theorem)

型安全性 (b) の反復から従う:完全なマッチング列は整型な束縛を生む。

`Reaches` は Step の枝選択つき反射推移閉包で、論文の
「Theorem 5.6(b) を反復する」(付録 C.4)をそのまま機械化した装置。
**`reaches_preservation`・`terminal_subst_typed`・`matcher_consistency` は
Theorem 5.6(b) を仮定 `hb` として受け取った上で証明済み**
(type-tensor-mech の `type_safety` 合成と同じ流儀)。
Search の要素と Reaches の対応 `search_mem_reaches` は未機械化
(相互帰納原理を要する;README ロードマップ)。
-/

namespace TypePM

/-- 状態 s から(毎ステップいずれかの後続を選んで)s' に到達する -/
inductive Reaches (SF : SigF) : MState → MState → Prop where
  | refl {s} : Reaches SF s s
  | step {s ss s' s''} :
      Step SF s ss → s' ∈ ss → Reaches SF s' s'' → Reaches SF s s''

/-- (b) の反復:到達可能な状態はすべて整型(**証明済み**、`hb` = Theorem 5.6(b))。 -/
theorem reaches_preservation
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Δgoal : BindCtx}
    (hb : ∀ {s ss}, Step SF s ss → WTState SD SP SF Γ s Δgoal →
      ∀ s' ∈ ss, WTState SD SP SF Γ s' Δgoal)
    {s s' : MState}
    (hr : Reaches SF s s') (hwt : WTState SD SP SF Γ s Δgoal) :
    WTState SD SP SF Γ s' Δgoal := by
  induction hr with
  | refl => exact hwt
  | step hstep hmem _ ih => exact ih (hb hstep hwt _ hmem)

/-- 終端状態の WT-STATE から:θ は Δ_goal で型付けられる(**証明済み**)。 -/
theorem terminal_subst_typed
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTState SD SP SF Γ ⟨[], ρ, θ⟩ Δgoal) :
    SubstTyped SD SP SF Δgoal θ := by
  obtain ⟨-, Δ₀, hθ, hstack⟩ := hwt
  cases hstack
  exact hθ

/-- 空代入は空文脈で型付けられる -/
theorem substTyped_nil {SD : SigD} {SP : SigP} {SF : SigF} :
    SubstTyped SD SP SF [] [] :=
  ⟨rfl, by intro pr h; cases h⟩

/-- **Theorem 5.7 (Matcher Consistency Theorem)**(**証明済み**、`hb` = Theorem 5.6(b))。
    整合的な m と双対検査を満たす match site から出発した評価が
    代入 θ で成功すれば、各 (x : τ') ∈ Δ について θ(x) : τ'。
    「成功」は初期 1 原子状態から終端状態への `Reaches` で表す
    (部分正当性;Theorem 5.6 と同様)。 -/
theorem matcher_consistency
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {ρ ρ' : Env} {θ : Subst} {p : Pattern} {m v : Value}
    {τ τp τt τm τm' : Ty} {Δ : BindCtx}
    (hb : ∀ {s ss}, Step SF s ss → WTState SD SP SF Γ s Δ →
      ∀ s' ∈ ss, WTState SD SP SF Γ s' Δ)
    (hρ : EnvTyped SD SP SF Γ ρ)
    (hp : PatTy SD SP SF Γ [] [] p τp τt Δ)              -- 双対判定
    (hm : ValueTy SD SP SF m (.matcher τm))              -- m の内在型
    (hren : RenamesTo τm τm')
    (hstr : OneWay τp τm')                               -- 構造条件 τm' ⊑ τp
    (htt : Unifiable τt τ)                               -- τt ~ τ
    (htm : Unifiable τm τ)
    (hok : MatcherOK SD SP m)                            -- m は整合(Def 4.2)
    (hv : ValueTy SD SP SF v τ)                          -- v : τ
    (hrun : Reaches SF ⟨[.atom ⟨p, m, v⟩], ρ, []⟩ ⟨[], ρ', θ⟩) :
    SubstTyped SD SP SF Δ θ := by
  have hinit : WTState SD SP SF Γ ⟨[.atom ⟨p, m, v⟩], ρ, []⟩ Δ :=
    ⟨hρ, [], substTyped_nil,
      WTStack.cons (WTTree.atom hp hm hren hstr htt htm hok hv) WTStack.nil⟩
  exact terminal_subst_typed (reaches_preservation hb hrun hinit)

/-! ## Search と Reaches の接続(相互帰納族の結合再帰子による証明) -/

theorem exists_mem_zip_right {α β} : ∀ {as : List α} {bs : List β},
    as.length = bs.length → ∀ {b}, b ∈ bs → ∃ a, (a, b) ∈ as.zip bs
  | [], [], _, _, hb => nomatch hb
  | [], _ :: _, hlen, _, _ => nomatch hlen
  | _ :: _, [], _, _, hb => nomatch hb
  | a :: as, b' :: bs, hlen, b, hb => by
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a, by simp [List.zip_cons_cons]⟩
      · obtain ⟨a', hz⟩ := exists_mem_zip_right (by simpa using hlen) hb
        exact ⟨a', by simp [List.zip_cons_cons, hz]⟩

theorem mem_left_of_zip {α β} : ∀ {as : List α} {bs : List β} {a : α} {b : β},
    (a, b) ∈ as.zip bs → a ∈ as
  | [], _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | a' :: as, b' :: bs, a, b, h => by
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · simp only [Prod.mk.injEq] at h
        simp [h.1]
      · simp [mem_left_of_zip h]

/-- Search の各解は Reaches の終端に対応する(EV-MATCHALL と Thm 5.7 の接続;
    **証明済み** — 相互帰納族の結合再帰子 `Search.rec` を他の 4 motive を
    自明にして適用する。Thm 5.6 の結合帰納法ルートの実証を兼ねる)。 -/
theorem search_mem_reaches
    {SF : SigF} {s : MState} {θs : List Subst}
    (hs : Search SF s θs) :
    ∀ θ ∈ θs, ∃ ρ', Reaches SF s ⟨[], ρ', θ⟩ := by
  refine Search.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun s θs _ => ∀ θ ∈ θs, ∃ ρ', Reaches SF s ⟨[], ρ', θ⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
    ?done ?step hs
  case done =>
    intro ρ θ θ' hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    exact ⟨ρ, Reaches.refl⟩
  case step =>
    intro s' ss θss hstep hlen hall _ihstep ih θ hθ
    obtain ⟨l, hl, hθl⟩ := List.mem_flatten.mp hθ
    obtain ⟨s'', hzip⟩ := exists_mem_zip_right hlen hl
    obtain ⟨ρ', hr⟩ := ih (s'', l) hzip θ hθl
    exact ⟨ρ', Reaches.step hstep (mem_left_of_zip hzip) hr⟩
  all_goals intros; trivial

end TypePM
