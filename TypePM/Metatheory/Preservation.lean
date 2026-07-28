import TypePM.WellTyped

/-!
# 保存系の補題と型安全性 (論文 §5.3–5.4・付録 C)

* Lemma 5.4 (PPP Type Preservation) — `ppp_preservation`(**証明済み**)
* Lemma C.2 (Matcher-Value Slot Invariant) — `matcher_slot_invariant`(**証明済み**;
  oracle 不要の核は `slot_value_inv`)
* Theorem 5.6 (Type Safety) は `Metatheory/TypeSafety.lean` に移設
  ((a) は oracle 分解で証明済み・(b) は sorry)

Lem 5.4・Lem C.2 は、論文の結合帰納法における (a) 部の帰納法の仮定を
明示の oracle 仮定(この ρ/この評価に対する評価型付け)として受け取る形で
述べ、その下で完全証明する(Thm 5.7 が (b) を仮定に取るのと同じ流儀)。

**機械化が浮かび上がらせた点(その 3;2026-07-28 最終設計)**:
pp の値パターンパターン #$y に捕捉された p 側 #M の M は、**節選択時に
原子の環境(MS-REDUCE の ρ∪θ)で先に**評価される(PPP-VAL)。
よって原子より前の束縛は使えるが、同じ原子内の左の穴の束縛は使えない。
この条件(**値パターンスコープ条件**)はパターン・マッチャー**対**の条件なので、
WT-ATOM の premise `VPScoped`(WellTyped.lean;論文 Fig 6 の vp-scoped)として定式化した。
Thm 5.6(b) の機械化では、この premise により #$y 捕捉時の M の型付け文脈が
原子入力文脈(= dom_typed θ で被覆)に収まることが oracle の討ち取りに使える
(後続原子への premise 伝播は不変量強化が要る;README ロードマップ)。
-/

namespace TypePM

/-! ## リスト・環境の補助補題 -/

theorem nodup_append_split {α} : ∀ {l₁ l₂ : List α}, (l₁ ++ l₂).Nodup →
    l₁.Nodup ∧ l₂.Nodup ∧ ∀ x ∈ l₁, x ∉ l₂
  | [], l₂, h => ⟨List.nodup_nil, h, by intro x hx; cases hx⟩
  | a :: l₁, l₂, h => by
      rw [List.cons_append] at h
      obtain ⟨hnotin, hrest⟩ := List.nodup_cons.mp h
      obtain ⟨h₁, h₂, hdisj⟩ := nodup_append_split hrest
      refine ⟨List.nodup_cons.mpr
        ⟨fun hmem => hnotin (List.mem_append.mpr (.inl hmem)), h₁⟩, h₂, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact fun hmem => hnotin (List.mem_append.mpr (.inr hmem))
      · exact hdisj x hx

theorem list_find?_append_some {α} {f : α → Bool} : ∀ {l₁ l₂ : List α} {a : α},
    List.find? f l₁ = some a → List.find? f (l₁ ++ l₂) = some a
  | [], _, _, h => nomatch h
  | b :: l₁, l₂, a, h => by
      rw [List.cons_append]
      simp only [List.find?] at h ⊢
      cases hb : f b
      · rw [hb] at h
        exact list_find?_append_some h
      · rw [hb] at h
        exact h

theorem list_find?_append_none {α} {f : α → Bool} : ∀ {l₁ l₂ : List α},
    List.find? f l₁ = none → List.find? f (l₁ ++ l₂) = List.find? f l₂
  | [], _, _ => rfl
  | b :: l₁, l₂, h => by
      rw [List.cons_append]
      simp only [List.find?] at h ⊢
      cases hb : f b
      · rw [hb] at h
        exact list_find?_append_none h
      · rw [hb] at h
        exact nomatch h

theorem Env.find?_append_left {ρ₁ ρ₂ : Env} {x : String} {v : Value}
    (h : Env.find? ρ₁ x = some v) : Env.find? (ρ₁ ++ ρ₂) x = some v := by
  simp only [Env.find?] at h ⊢
  cases hfind : List.find? (fun p => p.1 == x) ρ₁ with
  | none => rw [hfind] at h; exact nomatch h
  | some pr =>
      rw [list_find?_append_some hfind]
      rw [hfind] at h
      exact h

theorem Env.find?_append_right {ρ₁ ρ₂ : Env} {x : String}
    (h : ∀ pr ∈ ρ₁, pr.1 ≠ x) : Env.find? (ρ₁ ++ ρ₂) x = Env.find? ρ₂ x := by
  simp only [Env.find?]
  rw [list_find?_append_none]
  exact List.find?_eq_none.mpr fun pr hpr => by simp [h pr hpr]

/-- PatTys の長さ:パターン列と双対型列は同数 -/
theorem patTys_length {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {Φ : PatParamCtx} : ∀ {ps : List Pattern} {duals Δ Δ'},
    PatTys SD SP SF Γ Φ Δ ps duals Δ' → ps.length = duals.length
  | [], duals, _, _, h => by cases h; rfl
  | p :: ps, duals, _, _, h => by
      cases h with
      | cons hp hps => simp [patTys_length hps]

/-- PatTys の連結(Δ スレッディングを継いで結合) -/
theorem patTys_append {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {Φ : PatParamCtx} : ∀ {ps₁ : List Pattern} {duals₁ Δ Δ₁},
    PatTys SD SP SF Γ Φ Δ ps₁ duals₁ Δ₁ →
    ∀ {ps₂ duals₂ Δ₂}, PatTys SD SP SF Γ Φ Δ₁ ps₂ duals₂ Δ₂ →
    PatTys SD SP SF Γ Φ Δ (ps₁ ++ ps₂) (duals₁ ++ duals₂) Δ₂
  | [], duals₁, _, _, h₁, ps₂, duals₂, Δ₂, h₂ => by
      cases h₁
      simpa using h₂
  | p :: ps₁, duals₁, _, _, h₁, ps₂, duals₂, Δ₂, h₂ => by
      cases h₁ with
      | cons hp hps =>
        exact PatTys.cons hp (patTys_append hps h₂)

/-- refresh(PP-Con の「同じ頭・新しい葉」)は標的成分を保つ -/
theorem refresh_map_snd : ∀ {l l' : List (Ty × Ty)}, l.length = l'.length →
    (∀ pr ∈ l.zip l', pr.1.2 = pr.2.2 ∧ FreshLike pr.1.2 pr.2.1) →
    l'.map (·.2) = l.map (·.2)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', hlen, hall => by
      have hhead := hall (a, b) (by simp [List.zip_cons_cons])
      simp only [List.map_cons]
      rw [refresh_map_snd (by simpa using hlen)
        (fun pr hpr => hall pr (by simp [List.zip_cons_cons]; exact .inr hpr)),
        hhead.1]

/-! ## Lemma 5.4 (PPP Type Preservation) — 本体

pp の構造帰納(リスト版と相互)。PPM の反転(`cases`)で形を揃える。 -/

mutual

theorem ppp_core {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {Φ : PatParamCtx} {ρ : Env} :
    ∀ (pp : PPat) {p : Pattern} {ps' : List Pattern} {ρp : Env} {τ : Ty}
      {pairs : List (Ty × Ty)} {Δpp : BindCtx} {Δ₀ Δn : BindCtx} {τp₀ : Ty},
    SigPWF SP →
    (∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty},
       Eval SF ρ e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ') →
    PPTy SP pp τ pairs Δpp →
    PatTy SD SP SF Γ Φ Δ₀ p τp₀ τ Δn →
    PPM SF ρ pp p (some (ps', ρp)) →
    (∃ duals, PatTys SD SP SF Γ Φ Δ₀ ps' duals Δn ∧
       duals.map (·.2) = pairs.map (·.2)) ∧
    (∀ pr ∈ ρp, pr.1 ∈ Δpp.map (·.1)) ∧
    ((Δpp.map (·.1)).Nodup →
      ∀ pr ∈ Δpp, ∃ v, Env.find? ρp pr.1 = some v ∧ ValueTy SD SP SF v pr.2)
  | .hole, p, ps', ρp, τ, pairs, Δpp, Δ₀, Δn, τp₀, hwfP, heval, hpp, hp, hm => by
      cases hm
      cases hpp
      refine ⟨⟨[(τp₀, τ)], PatTys.cons hp PatTys.nil, rfl⟩, ?_, ?_⟩
      · intro pr hpr; cases hpr
      · intro _ pr hpr; cases hpr
  | .wild, p, ps', ρp, τ, pairs, Δpp, Δ₀, Δn, τp₀, hwfP, heval, hpp, hp, hm => by
      cases hm
      cases hpp
      cases hp
      refine ⟨⟨[], PatTys.nil, rfl⟩, ?_, ?_⟩
      · intro pr hpr; cases hpr
      · intro _ pr hpr; cases hpr
  | .pval y, p, ps', ρp, τ, pairs, Δpp, Δ₀, Δn, τp₀, hwfP, heval, hpp, hp, hm => by
      cases hm with
      | pval hev =>
        cases hpp
        cases hp with
        | pval hty =>
          refine ⟨⟨[], PatTys.nil, rfl⟩, ?_, ?_⟩
          · intro pr hpr
            simp only [List.mem_singleton] at hpr
            subst hpr
            simp
          · intro _ pr hpr
            simp only [List.mem_singleton] at hpr
            subst hpr
            exact ⟨_, by simp [Env.find?, List.find?], heval hev hty⟩
  | .ctor c pps, p, ps', ρp, τ, pairs, Δpp, Δ₀, Δn, τp₀, hwfP, heval, hpp, hp, hm => by
      cases hm with
      | ctor hl1 hl2 hall =>
        cases hpp with
        | ctor hfind₀ hpps hlenp hrefresh =>
          rename_i sig ts₀ pairs₀
          generalize hres : Ty.instSig ts₀ sig.res = τx at hp
          cases hp with
          | pctor hfind₁ hps hstr htgt =>
            rename_i sig₁ ss ts₁ duals₁
            -- 同じ c の Σ_P 検索は同じシグネチャを返す
            have hsig : sig = sig₁ :=
              congrArg (·.2) (Option.some.inj (hfind₀.symm.trans hfind₁))
            subst hsig
            -- 結果型のインスタンス一致から引数型のインスタンス一致(Def 4.1 整形性)
            have hwf := hwfP _ (List.mem_of_find?_eq_some hfind₀)
            have hagree := instSig_args_agree hwf hres
            have htgt' : duals₁.map (·.2) = sig.args.map (Ty.instSig ts₀) := by
              rw [htgt]
              exact (List.map_congr_left fun τa hτa => hagree τa hτa).symm
            obtain ⟨⟨duals, hd, hmap⟩, hdom, hbind⟩ :=
              ppp_list pps hwfP heval hpps hps htgt' hl1 hl2 hall
            refine ⟨⟨duals, hd, ?_⟩, hdom, hbind⟩
            rw [hmap, refresh_map_snd hlenp hrefresh]
  | .tuple pps, p, ps', ρp, τ, pairs, Δpp, Δ₀, Δn, τp₀, hwfP, heval, hpp, hp, hm => by
      cases hm with
      | tuple hl1 hl2 hall =>
        cases hpp with
        | tuple hpps hlenp hrefresh =>
          rename_i τs pairs₀
          generalize hres : Ty.prod τs = τx at hp
          cases hp with
          | ptuple hps =>
            rename_i duals₁
            -- 積型の成分一致:.prod τs = .prod (duals₁.map snd)
            have htgt' : duals₁.map (·.2) = τs := by
              injection hres with h
              exact h.symm
            obtain ⟨⟨duals, hd, hmap⟩, hdom, hbind⟩ :=
              ppp_list pps hwfP heval hpps hps htgt' hl1 hl2 hall
            refine ⟨⟨duals, hd, ?_⟩, hdom, hbind⟩
            rw [hmap, refresh_map_snd hlenp hrefresh]

theorem ppp_list {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {Φ : PatParamCtx} {ρ : Env} :
    ∀ (pps : List PPat) {ps : List Pattern} {rs : List (List Pattern × Env)}
      {τs : List Ty} {pairs : List (Ty × Ty)} {Δpp : BindCtx}
      {Δ₀ Δn : BindCtx} {duals₁ : List (Ty × Ty)},
    SigPWF SP →
    (∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty},
       Eval SF ρ e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ') →
    PPTys SP pps τs pairs Δpp →
    PatTys SD SP SF Γ Φ Δ₀ ps duals₁ Δn →
    duals₁.map (·.2) = τs →
    pps.length = ps.length →
    (pps.zip ps).length = rs.length →
    (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)) →
    (∃ duals, PatTys SD SP SF Γ Φ Δ₀ ((rs.map (·.1)).flatten) duals Δn ∧
       duals.map (·.2) = pairs.map (·.2)) ∧
    (∀ pr ∈ (rs.map (·.2)).flatten, pr.1 ∈ Δpp.map (·.1)) ∧
    ((Δpp.map (·.1)).Nodup →
      ∀ pr ∈ Δpp, ∃ v, Env.find? ((rs.map (·.2)).flatten) pr.1 = some v ∧
        ValueTy SD SP SF v pr.2)
  | [], ps, rs, τs, pairs, Δpp, Δ₀, Δn, duals₁,
      hwfP, heval, hpps, hps, hmap, hl1, hl2, hall => by
      cases hpps
      cases ps with
      | cons p ps => simp at hl1
      | nil =>
        cases hps
        cases rs with
        | cons r rs => simp at hl2
        | nil =>
          refine ⟨⟨[], PatTys.nil, rfl⟩, ?_, ?_⟩
          · intro pr hpr; simp at hpr
          · intro _ pr hpr; cases hpr
  | pp :: pps, ps, rs, τs, pairs, Δpp, Δ₀, Δn, duals₁,
      hwfP, heval, hpps, hps, hmap, hl1, hl2, hall => by
      cases ps with
      | nil => simp at hl1
      | cons p ps =>
        cases rs with
        | nil => simp [List.zip_cons_cons] at hl2
        | cons r rs =>
          cases hpps with
          | cons hpph hppt =>
            rename_i τh pairsh Δh τt pairst Δt
            cases hps with
            | cons hph hpst =>
              rename_i Δmid prh dualst
              simp only [List.map_cons, List.cons.injEq] at hmap
              obtain ⟨hmh, hmt⟩ := hmap
              obtain ⟨nexts, ρpc⟩ := r
              -- 先頭の PPM
              have hPPMh : PPM SF ρ pp p (some (nexts, ρpc)) :=
                hall ((pp, p), (nexts, ρpc)) (by simp [List.zip_cons_cons])
              -- 先頭に本体補題を適用(hph の標的添字を τh に書き換え)
              rw [hmh] at hph
              obtain ⟨⟨dualsh, hdh, hmaph⟩, hdomh, hbindh⟩ :=
                ppp_core pp hwfP heval hpph hph hPPMh
              -- 残りに再帰
              obtain ⟨⟨dualst', hdt, hmapt⟩, hdomt, hbindt⟩ :=
                ppp_list pps hwfP heval hppt hpst hmt
                  (by simpa using hl1)
                  (by simpa [List.zip_cons_cons] using hl2)
                  (fun tr htr => hall tr
                    (by simp [List.zip_cons_cons]; exact .inr htr))
              refine ⟨⟨dualsh ++ dualst', ?_, ?_⟩, ?_, ?_⟩
              · simpa [List.map_cons, List.flatten_cons] using
                  patTys_append hdh hdt
              · simp only [List.map_append, hmaph, hmapt]
              · -- ドメインの上界
                intro pr hpr
                simp only [List.map_cons, List.flatten_cons,
                  List.mem_append] at hpr
                simp only [List.map_append, List.mem_append]
                rcases hpr with hpr | hpr
                · exact .inl (hdomh pr hpr)
                · exact .inr (hdomt pr hpr)
              · -- 束縛の型付け(binder 相異のもとで)
                intro hnd pr hpr
                rw [List.map_append] at hnd
                obtain ⟨ndh, ndt, hdisj⟩ := nodup_append_split hnd
                simp only [List.map_cons, List.flatten_cons]
                rcases List.mem_append.mp hpr with hpr | hpr
                · obtain ⟨v, hfind, hty⟩ := hbindh ndh pr hpr
                  exact ⟨v, Env.find?_append_left hfind, hty⟩
                · have hnot : ∀ q ∈ ρpc, q.1 ≠ pr.1 := by
                    intro q hq heq
                    have h1 : q.1 ∈ Δh.map (·.1) := hdomh q hq
                    have h2 : pr.1 ∈ Δt.map (·.1) :=
                      List.mem_map_of_mem hpr
                    exact hdisj q.1 h1 (heq ▸ h2)
                  obtain ⟨v, hfind, hty⟩ := hbindt ndt pr hpr
                  exact ⟨v, (Env.find?_append_right hnot).trans hfind, hty⟩

end

/-- **Lemma 5.4 (PPP Type Preservation)**(**証明済み**)。
    pp 判定の穴対列 pairs と p の双対判定が与えられ pp ≈ p が成功したとき、
    取り出された次パターン列 ps' は pairs の標的成分で型付けられ
    (Δ は p の入力文脈から左→右に継がれ、出力は p のそれと一致)、
    ρp は pp の値パターン束縛 Δpp をその型の値で束縛する。

    仮定:`hwfP` = Σ_P 整形性(Def 4.1 の暗黙条件)、
    `heval` = この ρ での評価型付け oracle(結合帰納法の (a) 部;
    文脈量化はモジュールドキュメントの間隙その 3 を参照)、
    `hnd` = pp の値パターン束縛名の相異(⋃ᵢ Δᵢ が直和である暗黙条件)。 -/
theorem ppp_preservation
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {ρ : Env} {pp : PPat} {p : Pattern} {ps' : List Pattern} {ρp : Env}
    {τ τp₀ : Ty} {pairs : List (Ty × Ty)} {Δpp : BindCtx} {Δ₀ Δn : BindCtx}
    (hwfP : SigPWF SP)
    (heval : ∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty},
       Eval SF ρ e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ')
    (hnd : (Δpp.map (·.1)).Nodup)
    (hpp : PPTy SP pp τ pairs Δpp)
    (hp : PatTy SD SP SF Γ Φ Δ₀ p τp₀ τ Δn)
    (hm : PPM SF ρ pp p (some (ps', ρp))) :
    ps'.length = pairs.length ∧
    (∃ duals, PatTys SD SP SF Γ Φ Δ₀ ps' duals Δn ∧
      duals.map (·.2) = pairs.map (·.2)) ∧
    (∀ pr ∈ Δpp, ∃ v, Env.find? ρp pr.1 = some v ∧ ValueTy SD SP SF v pr.2) := by
  obtain ⟨⟨duals, hd, hmap⟩, hdom, hbind⟩ := ppp_core pp hwfP heval hpp hp hm
  refine ⟨?_, ⟨duals, hd, hmap⟩, hbind hnd⟩
  have h1 := patTys_length hd
  have h2 : duals.length = pairs.length := by
    have := congrArg List.length hmap
    simpa using this
  exact h1.trans h2

/-- スロット型の値の反転(Lem C.2 の核;oracle 不要の値レベル部分)。 -/
theorem slot_value_inv
    {SD : SigD} {SP : SigP} {SF : SigF} {m : Value} {τp τt : Ty}
    (hwfD : SigDWF SD)
    (hv : ValueTy SD SP SF m (.slot τp τt)) :
    (∃ τm τm', ValueTy SD SP SF m (.matcher τm) ∧
       RenamesTo τm τm' ∧ OneWay τp τm' ∧ Unifiable τm τt ∧
       MatcherOK SD SP m)
    ∨ (∃ (ms : List Value) (prs : List (Ty × Ty)), m = Value.tuple ms ∧
       τp = .prod (prs.map (·.1)) ∧ τt = .prod (prs.map (·.2)) ∧
       ms.length = prs.length ∧
       ∀ pr ∈ ms.zip prs, ValueTy SD SP SF pr.1 (.slot pr.2.1 pr.2.2)) := by
  generalize hτ : (Ty.slot τp τt : Ty) = τx at hv
  cases hv with
  | lit => cases hτ
  | ctor hfind hlen hall =>
      exfalso
      obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [hres] at hτ
      simp [Ty.instSig, Ty.applyTS] at hτ
  | tuple _ _ => cases hτ
  | closure Γ' _ _ _ _ => cases hτ
  | matcherV _ _ _ _ => cases hτ
  | something => cases hτ
  | prodMatcher _ _ => cases hτ
  | slotV hm hren how huni =>
      injection hτ with h1 h2
      subst h1
      subst h2
      exact .inl ⟨_, _, hm, hren, how, huni,
        matcherOK_of_valueTy hwfD hm _ rfl⟩
  | prodSlot hlen hcomp =>
      injection hτ with h1 h2
      exact .inr ⟨_, _, rfl, h1, h2, hlen, hcomp⟩

/-- **Lemma C.2 (Matcher-Value Slot Invariant)**(**証明済み**)。
    スロット型 MatcherSlot τp τt で消費される式 e_m の評価値 m は、
    (i) 自らの内在型 Matcher τm について双対検査の両条件を満たし
    WT-ATOM のマッチャー選言に入るか、
    (ii) 成分ごとにスロット型を満たすタプル(COERCE-SLOT-TUPLE の値、
    論文 C.2 後段の「積の構造 witness は成分 witness の直和」)である。
    仮定 `ha` は Thm 5.6(a)(結合帰納法での依存;Thm 5.7 と同じ流儀)。
    核は oracle 不要の `slot_value_inv`。 -/
theorem matcher_slot_invariant
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {ρ : Env} {e_m : Expr} {m : Value} {τp τt : Ty}
    (hwfD : SigDWF SD)
    (ha : ∀ {ρ' : Env} {Γ' : TyCtx} {e' : Expr} {v' : Value} {τ' : Ty},
       Eval SF ρ' e' v' → EnvTyped SD SP SF Γ' ρ' →
       HasTy SD SP SF Γ' e' τ' → ValueTy SD SP SF v' τ')
    (hρ : EnvTyped SD SP SF Γ ρ)
    (hty : HasTy SD SP SF Γ e_m (.slot τp τt))
    (hev : Eval SF ρ e_m m) :
    (∃ τm τm', ValueTy SD SP SF m (.matcher τm) ∧
       RenamesTo τm τm' ∧ OneWay τp τm' ∧ Unifiable τm τt ∧
       MatcherOK SD SP m)
    ∨ (∃ (ms : List Value) (prs : List (Ty × Ty)), m = Value.tuple ms ∧
       τp = .prod (prs.map (·.1)) ∧ τt = .prod (prs.map (·.2)) ∧
       ms.length = prs.length ∧
       ∀ pr ∈ ms.zip prs, ValueTy SD SP SF pr.1 (.slot pr.2.1 pr.2.2)) :=
  slot_value_inv hwfD (ha hev hρ hty)

end TypePM
