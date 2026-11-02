import Workspace.Impl.TermRecStepW

/-!
# T5, the case `ℓ + 1` of the recursion (item 5)

`tmRi_step_spec`: the function `b + 2` (`tmRiStepE`) on `[ℓ + 1, gens H, gens N, X, Y]`
returns a coset answer for `Iso_H(X, Y)`, given the recursion at fuel `ℓ` (`TmRiIH`) and the
glue (`TermGlueObjSpec` at `gObj`). This is the paper's step: compute `A = relDerived H N ℓ`
(the last derived subgroup above `N`), cut `X` and `Y` into `A`-orbit pieces, compute the table
of the transporters `Iso_H(S, T)` of the pieces with the recursion, form the profiles, transport
the profiles by one more recursive call on `(ℓ, H, A, Ŷ, X̂)`, and glue.

* The profile call meets its preconditions: `relDerived H A ℓ ≤ A` (`tmRi_fuel`), `A` fixes the
  profiles (`tmRiHat_fix`), the profiles are well formed (`tmRi_profs_ok`).
* If the profile call is empty, so is `Iso_H(X, Y)` (`tmRi_prof_empty`).
* Otherwise it returns `Iso_H(Ŷ, X̂) = v B`, so `Iso_H(X̂, Ŷ) = B v⁻¹` (`tmRi_iso_swap`), and
  the glue is called with `B` and `τ = v⁻¹`; its preconditions P1–P5 are `tmRi_glue_pre`.

The cost is `4 M³ T + T + tmRiStepO …`: at most `(2M)² · M` calls of the recursion in the
table, one profile call, and an own cost `tmRiStepO` that does not depend on `T`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open scoped Pointwise
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-- The generic bound of the small steps of one level. -/
def tmRiSQ (n M : ℕ) : ℕ := 10 ^ 5 * (tmRiVs n M + 1) ^ 2

/-- The cost of the profiles of one side, besides the small steps. -/
noncomputable def tmRiPrC (hmem : Membership) (n M : ℕ) : ℕ :=
  2 * M * tmRiProfC hmem n (3 * tmRiVs n M) + mapK * (2 * M + 1) * (tmRiVs n M + 2000 * tmRiB n M + 5) +
    8000 * (2 * M + 1) ^ 3

/-- **The own cost of one level** of the recursion: everything but the recursive calls. -/
noncomputable def tmRiStepO (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hmem : Membership) (Kg Dg n M : ℕ) : ℕ :=
  tmRiDerC (derivedSubgroupPrim hder) hmem n +
    2 * tmRiPcsC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) (tmRiVs n M) +
    4 * M ^ 3 * tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * (10 * tmRiVs n M + 20) + 10) +
    tmRiTabC hmem n M (2 * M) (tmRiVs n M) + 2 * tmRiPrC hmem n M +
    Kg * (tmRiVs n M + 1) ^ Dg + 10 * tmRiSQ n M + 10 * (700 * (n + 1) ^ 6 + 1)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The case `ℓ + 1`.** -/
theorem tmRi_step_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {Kg Dg : ℕ}
    (hglue : Iface.TermGlueObjSpec P Kg Dg gObj) {M ℓ T : ℕ} (ih : TmRiIH P b n M ℓ T)
    {σH σN : List (Perm (Fin n))} {X Y : List (TmRiO n)}
    (hsol : IsSolvable (gens σH)) (hNH : gens σN ≤ gens σH)
    (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN) (hℓ : ℓ + 1 ≤ n ^ 2 + 5)
    (hNX : Fixes (gens σN) (tmGlMs X)) (hNY : Fixes (gens σN) (tmGlMs Y))
    (hHl : σH.length ≤ n ^ 2) (hNl : σN.length ≤ n ^ 2) (hX : X.length ≤ M) (hY : Y.length ≤ M)
    (hok : TmRecObjOK M (X ++ Y)) :
    FunAll P (b + 2) (tmRecIn (ℓ + 1) σH σN X Y) (fun u cost =>
      CosetC n u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧
      cost ≤ 4 * M ^ 3 * T + T + tmRiStepO hsci hder hmem Kg Dg n M) := by
  -- the facts about the sizes
  obtain ⟨fB1, fB2, fB3, fB4, fB5⟩ := tmRiB_facts n M
  obtain ⟨fV1, fV2, fV3, fV4⟩ := tmRiVs_facts n M
  have hF1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn4 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnn : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hSQ : 10 ^ 5 * (tmRiVs n M + 1) ≤ tmRiSQ n M := by
    unfold tmRiSQ
    exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have hWoV : 700 * (n + 1) ^ 6 ≤ tmRiVs n M := by omega
  -- the input
  set Xv := X.map tmGlObjVal with hXv
  set Yv := Y.map tmGlObjVal with hYv
  set vs : List Val := [.nat (ℓ + 1), encGroup σH, encGroup σN, .list Xv, .list Yv] with hvs
  have hain : tmRecIn (ℓ + 1) σH σN X Y = .list vs := rfl
  rw [hain]
  have hokX : TmRiOK (2 * M) X := fun o ho =>
    ⟨(hok o (by simp [ho])).1, by have := (hok o (by simp [ho])).2.1; omega,
      fun o' ho' he => (hok o (by simp [ho])).2.2 o' (by simp [ho']) he⟩
  have hokY : TmRiOK (2 * M) Y := fun o ho =>
    ⟨(hok o (by simp [ho])).1, by have := (hok o (by simp [ho])).2.1; omega,
      fun o' ho' he => (hok o (by simp [ho])).2.2 o' (by simp [ho']) he⟩
  have hXw : (Val.list Xv).wt ≤ 2020 * tmRiB n M := tmRi_wt_side hX hokX
  have hYw : (Val.list Yv).wt ≤ 2020 * tmRiB n M := tmRi_wt_side hY hokY
  have hHw : (encGroup σH).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hHl
  have hNw : (encGroup σN).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hNl
  have hlw : (Val.nat (ℓ + 1)).wt ≤ (n + 1) ^ 6 + 8 := by have := wt_nat_le (ℓ + 1); omega
  have haw : (Val.list vs).wt ≤ 10 ^ 4 * tmRiB n M := by
    have := wt_list_le [.nat (ℓ + 1), encGroup σH, encGroup σN, .list Xv, .list Yv]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    show (Val.list [.nat (ℓ + 1), encGroup σH, encGroup σN, .list Xv, .list Yv]).wt ≤ _
    omega
  -- the output
  set R : Val → Prop := fun w => CosetC n w (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) with hR
  obtain ⟨Wo, hWo⟩ : ∃ w, w = 700 * (n + 1) ^ 6 := ⟨_, rfl⟩
  obtain ⟨Bud, hBud⟩ : ∃ B, B = 4 * M ^ 3 * T + T + tmRiStepO hsci hder hmem Kg Dg n M := ⟨_, rfl⟩
  rw [← hBud]
  have hBud' : Bud = 4 * M ^ 3 * T + T + tmRiDerC (derivedSubgroupPrim hder) hmem n +
      2 * tmRiPcsC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) (tmRiVs n M) +
      4 * M ^ 3 * tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * (10 * tmRiVs n M + 20) + 10) +
      tmRiTabC hmem n M (2 * M) (tmRiVs n M) + 2 * tmRiPrC hmem n M +
      Kg * (tmRiVs n M + 1) ^ Dg + 10 * tmRiSQ n M + 10 * (Wo + 1) := by
    rw [hBud, hWo]; unfold tmRiStepO; ring
  refine FunAll.intro hP.step (EvalAll.mono (Q := fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) ?_
    fun w c h => ⟨h.1, h.2.2⟩)
  -- `ℓ`
  have d1 := Det.arith' (op := .sub) (Det.arg' (P := P) (vs := vs) (rest := []) (j := 0)
    (v := .nat (ℓ + 1)) rfl) (Det.nat 1) (z := ℓ) (by simp [BinOp.eval])
  refine tmRi_letB d1 (fun _ _ h => h.2) (by omega) fun v1 c1 h1 => ?_
  obtain ⟨rfl, -⟩ := h1
  -- `A`
  have darg2 := Det.mk3 (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [.nat ℓ]) (j := 1)
      (v := encGroup σH) rfl) (Det.arg' (P := P) (vs := vs) (rest := [.nat ℓ]) (j := 2)
      (v := encGroup σN) rfl)) (Det.var' (P := P) (env := [.list vs, .nat ℓ]) (i := 1) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := [.nat ℓ]) (j := 1) (v := encGroup σH) rfl)
  have hder2 := EvalAll.call_funAll (f := b + 63) darg2 (Q := fun w c =>
      (∃ gs, w = encGroup gs ∧ gens gs = relDerived (gens σH) (gens σN) ℓ ∧ gs.length ≤ n ^ 2) ∧
      c ≤ tmRiDerC (derivedSubgroupPrim hder) hmem n + tmRiSQ n M) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (tmRi_der_spec hP hHl hNl ℓ (by omega)).mono fun w c h => ⟨h.1, ?_⟩
    obtain ⟨gs, rfl, -, hgl⟩ := h.1
    have := wt_encGroup_le_sq hgl
    have := wt_list2_le (encGroup σH) (encGroup σN)
    have := wt_list3_le (Val.list [encGroup σH, encGroup σN]) (.nat ℓ) (encGroup σH)
    have := wt_nat_le ℓ
    omega
  refine tmRi_letB hder2 (fun _ _ h => h.2) (by omega) fun v2 c2 h2 => ?_
  obtain ⟨⟨gs, rfl, hgs, hgsl⟩, -⟩ := h2
  have hAw : (encGroup gs).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hgsl
  have hAH : gens gs ≤ gens σH := hgs ▸ relDerived_le hNH ℓ
  have hAn : GI.Multicoset.Normalizes (gens σH) (gens gs) := hgs ▸ relDerived_normalizes hNn ℓ
  have hsolA : IsSolvable (gens gs) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hAH)
  have hNA : gens σN ≤ gens gs := hgs ▸ le_relDerived hNH ℓ
  -- the pieces
  set PX := tmRiPcsO (gens gs) X with hPX
  set PY := tmRiPcsO (gens gs) Y with hPY
  set Ps := tmRiPs (gens gs) X Y with hPs
  have hPsl : Ps.length ≤ 2 * M := by
    have := tmRiPs_length_le (gens gs) X Y; rw [← hPs] at this; omega
  have hPXl : PX.length ≤ M := (tmRiPcsO_length_le _ _).trans hX
  have hPYl : PY.length ≤ M := (tmRiPcsO_length_le _ _).trans hY
  have hPc : ∀ S ∈ Ps, TmRiPc gs σN M S ∧ ∀ o ∈ S, o ∈ X ++ Y := by
    intro S hS
    rcases List.mem_append.1 hS with hS | hS
    · obtain ⟨h1, h2⟩ := tmRiPcsO_pc (σA := gs) hX hNX hS
      exact ⟨h1, fun o ho => List.mem_append_left _ (h2 o ho)⟩
    · obtain ⟨h1, h2⟩ := tmRiPcsO_pc (σA := gs) hY hNY hS
      exact ⟨h1, fun o ho => List.mem_append_right _ (h2 o ho)⟩
  have hSw : ∀ S ∈ Ps, (tmGlObjsVal S).wt ≤ 2020 * tmRiB n M := by
    intro S hS
    rcases List.mem_append.1 hS with hS | hS
    · obtain ⟨o, -, rfl⟩ := tmRiPcsO_mem hS
      exact (tmRi_wt_objs_sub List.filter_sublist).trans hXw
    · obtain ⟨o, -, rfl⟩ := tmRiPcsO_mem hS
      exact (tmRi_wt_objs_sub List.filter_sublist).trans hYw
  have hPXw : (Val.list (PX.map tmGlObjsVal)).wt ≤ 9000 * ((M + 1) * tmRiB n M) :=
    tmRi_wt_pcsL (by omega) fun S hS => hSw S (List.mem_append_left _ hS)
  have hPYw : (Val.list (PY.map tmGlObjsVal)).wt ≤ 9000 * ((M + 1) * tmRiB n M) :=
    tmRi_wt_pcsL (by omega) fun S hS => hSw S (List.mem_append_right _ hS)
  have hPw : (Val.list (Ps.map tmGlObjsVal)).wt ≤ 9000 * ((M + 1) * tmRiB n M) :=
    tmRi_wt_pcsL hPsl hSw
  -- the pieces of `X`
  set e2 : List Val := [.list vs, .nat ℓ, encGroup gs] with he2
  have hinvV : invK * (n + 1) ^ 4 ≤ tmRiVs n M := by simp only [invK]; omega
  -- the pieces of `X`
  have hEX : (Val.list [encGroup gs, .list Xv]).wt ≤ tmRiVs n M := by
    have := wt_list2_le (encGroup gs) (.list Xv); omega
  have hpX := tmRi_pcs_spec hP hsolA hgsl hokX (E := tmRiVs n M) hEX
  rw [← tmRiPcsO_val, ← hPX] at hpX
  have d3 := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list vs, .nat ℓ, encGroup gs]) (i := 2)
    rfl) (Det.arg' (P := P) (vs := vs) (rest := [.nat ℓ, encGroup gs]) (j := 3) (v := .list Xv)
    rfl)) hpX
  refine tmRi_letB d3 (fun _ _ h => h.2) (by omega) fun v3 c3 h3 => ?_
  obtain ⟨rfl, -⟩ := h3
  -- the pieces of `Y`
  have hEY : (Val.list [encGroup gs, .list Yv]).wt ≤ tmRiVs n M := by
    have := wt_list2_le (encGroup gs) (.list Yv); omega
  have hpY := tmRi_pcs_spec hP hsolA hgsl hokY (E := tmRiVs n M) hEY
  rw [← tmRiPcsO_val, ← hPY] at hpY
  have d4 := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list vs, .nat ℓ, encGroup gs,
    .list (PX.map tmGlObjsVal)]) (i := 2) rfl) (Det.arg' (P := P) (vs := vs)
    (rest := [.nat ℓ, encGroup gs, .list (PX.map tmGlObjsVal)]) (j := 4) (v := .list Yv) rfl)) hpY
  refine tmRi_letB d4 (fun _ _ h => h.2) (by omega) fun v4 c4 h4 => ?_
  obtain ⟨rfl, -⟩ := h4
  -- all the pieces
  have happ := tmRi_append_det hP.app (PX.map tmGlObjsVal) (PY.map tmGlObjsVal)
  have eP : PX.map tmGlObjsVal ++ PY.map tmGlObjsVal = Ps.map tmGlObjsVal := by
    simp [hPs, hPX, hPY, tmRiPs]
  rw [eP] at happ
  have d5 := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list vs, .nat ℓ, encGroup gs,
    .list (PX.map tmGlObjsVal), .list (PY.map tmGlObjsVal)]) (i := 3) rfl)
    (Det.var' (P := P) (env := [.list vs, .nat ℓ, encGroup gs,
    .list (PX.map tmGlObjsVal), .list (PY.map tmGlObjsVal)]) (i := 4) rfl)) happ
  have hm5 : loopModK * ((PY.map tmGlObjsVal).length + 1) *
      ((Val.list [.list (PX.map tmGlObjsVal), .list (PY.map tmGlObjsVal)]).wt +
        (PY.map tmGlObjsVal).length + (Val.list (Ps.map tmGlObjsVal)).wt + 1) ≤
      5 * 10 ^ 4 * (tmRiVs n M + 1) ^ 2 := by
    have h1 := wt_list2_le (.list (PX.map tmGlObjsVal)) (.list (PY.map tmGlObjsVal))
    have h2 := length_lt_wt_list (PY.map tmGlObjsVal)
    rw [mul_assoc]
    calc _ ≤ loopModK * ((tmRiVs n M + 1) * (50 * (tmRiVs n M + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 5 * 10 ^ 4 * (tmRiVs n M + 1) ^ 2 := by simp only [loopModK]; ring
  have hSQ2 : tmRiSQ n M = 2 * (5 * 10 ^ 4 * (tmRiVs n M + 1) ^ 2) := by unfold tmRiSQ; ring
  have := wt_list2_le (.list (PX.map tmGlObjsVal)) (.list (PY.map tmGlObjsVal))
  refine tmRi_letB d5 (fun _ _ h => h.2) (by omega) fun v5 c5 h5 => ?_
  obtain ⟨rfl, -⟩ := h5
  -- the table
  set e5 : List Val := [.list vs, .nat ℓ, encGroup gs, .list (PX.map tmGlObjsVal),
    .list (PY.map tmGlObjsVal), .list (Ps.map tmGlObjsVal)] with he5
  have darg6 := Det.mk2 (Det.mk4 (Det.var' (P := P) (env := e5) (i := 1) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := e5.tail) (j := 1) (v := encGroup σH) rfl)
    (Det.var' (P := P) (env := e5) (i := 2) rfl) (Det.var' (P := P) (env := e5) (i := 5) rfl))
    (Det.var' (P := P) (env := e5) (i := 5) rfl)
  have hW6 : (Val.list [.list [.nat ℓ, encGroup σH, encGroup gs, .list (Ps.map tmGlObjsVal)],
      .list (Ps.map tmGlObjsVal)]).wt ≤ tmRiVs n M := by
    have := wt_list4_le (.nat ℓ) (encGroup σH) (encGroup gs) (.list (Ps.map tmGlObjsVal))
    have := wt_list2_le (.list [.nat ℓ, encGroup σH, encGroup gs, .list (Ps.map tmGlObjsVal)])
      (.list (Ps.map tmGlObjsVal))
    have := wt_nat_le ℓ
    omega
  have htab := EvalAll.call_funAll (f := b + 66) darg6 (Q := fun w c =>
      (∃ tab, w = .list tab ∧ TmRiTab (gens σH) Ps tab ∧ w.wt ≤ 12000 * ((M + 1) * tmRiB n M)) ∧
      c ≤ 4 * M ^ 3 * T + 4 * M ^ 3 * tmRiYC (solvableCosetIntersectionPrim hsci) n M
        (4 * (10 * tmRiVs n M + 20) + 10) + tmRiTabC hmem n M (2 * M) (tmRiVs n M) + tmRiSQ n M)
      fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (tmRi_table_spec hP ih hsol hHl hgsl hNH hNn hgs hfuel (by omega)
      (fun S hS => (hPc S hS).1) hok (fun S hS o ho => (hPc S hS).2 o ho) hW6).mono
      fun w c h => ?_
    obtain ⟨tab, rfl, ht, hw, hc⟩ := h
    have hw' := le_trans hw (tmRi_wt_tab hPsl)
    refine ⟨⟨tab, rfl, ht, hw'⟩, ?_⟩
    have hmul : Ps.length * Ps.length * (M * (T + tmRiYC (solvableCosetIntersectionPrim hsci) n M
        (4 * (10 * tmRiVs n M + 20) + 10))) ≤ 4 * M ^ 3 * T + 4 * M ^ 3 *
          tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * (10 * tmRiVs n M + 20) + 10) :=
      calc _ ≤ (2 * M) * (2 * M) * (M * (T + tmRiYC (solvableCosetIntersectionPrim hsci) n M
            (4 * (10 * tmRiVs n M + 20) + 10))) :=
            Nat.mul_le_mul (Nat.mul_le_mul hPsl hPsl) le_rfl
        _ = _ := by ring
    have hmono := tmRiTabC_mono hmem n M hPsl (tmRiVs n M)
    have := wt_nat_le ℓ
    have := wt_list4_le (.nat ℓ) (encGroup σH) (encGroup gs) (.list (Ps.map tmGlObjsVal))
    have := wt_list2_le (.list [.nat ℓ, encGroup σH, encGroup gs, .list (Ps.map tmGlObjsVal)])
      (.list (Ps.map tmGlObjsVal))
    omega
  refine tmRi_letB htab (fun _ _ h => h.2) (by omega) fun v6 c6 h6 => ?_
  obtain ⟨⟨tab, rfl, ht, htw⟩, -⟩ := h6
  have hPsXY : Ps.length = PX.length + PY.length := by simp [hPs, hPX, hPY, tmRiPs]
  have hlPX : (PX.map tmGlObjsVal).length = PX.length := List.length_map _
  have hlPY : (PY.map tmGlObjsVal).length = PY.length := List.length_map _
  have htabw : (Val.list tab).wt ≤ 12000 * ((M + 1) * tmRiB n M) := htw
  -- a bound on the cost of the profiles of one side
  have hprofC : ∀ m o : ℕ, m ≤ M → (Val.list [.list [encGroup gs, .list tab, .nat o],
      natList (List.range m)]).wt ≤ tmRiVs n M →
      m * tmRiProfC hmem n (3 * tmRiVs n M) + mapK * (m + 1) *
        ((Val.list [.list [encGroup gs, .list tab, .nat o], natList (List.range m)]).wt +
          m * (2 * (2 * Ps.length + 700 * (n + 1) ^ 6) + 1) + 5) + 8000 * (m + 1) ^ 3 ≤
      tmRiPrC hmem n M := by
    intro m o hm hw
    have h1 : m * tmRiProfC hmem n (3 * tmRiVs n M) ≤ 2 * M * tmRiProfC hmem n (3 * tmRiVs n M) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 := tmRi_wt_profs (n := n) hm hPsl
    have h3 : mapK * (m + 1) * ((Val.list [.list [encGroup gs, .list tab, .nat o],
        natList (List.range m)]).wt + m * (2 * (2 * Ps.length + 700 * (n + 1) ^ 6) + 1) + 5) ≤
        mapK * (2 * M + 1) * (tmRiVs n M + 2000 * tmRiB n M + 5) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h4 : 8000 * (m + 1) ^ 3 ≤ 8000 * (2 * M + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    unfold tmRiPrC
    omega
  have hrng : ∀ m : ℕ, m ≤ M → (natList (List.range m)).wt ≤ 4 * tmRiB n M + 4 := by
    intro m hm
    rw [range_eq_encPerm_one]
    have := wt_encPerm_le (1 : Perm (Fin m))
    have h : (m + 1) ^ 2 ≤ tmRiB n M + 1 := by
      have : (m + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (M + 1) ^ 2 = (M + 1) * (M + 1) := by ring
      have : (M + 1) * (M + 1) ≤ tmRiB n M := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  -- the profiles of `X`
  set e6 : List Val := e5 ++ [.list tab] with he6
  have dlen7 := Det.length (Det.var' (P := P) (env := e6) (i := 3) (v := .list (PX.map tmGlObjsVal)) rfl)
  rw [hlPX] at dlen7
  have drng7 := Det.call dlen7 (range_det hP.range PX.length)
  rw [← range_eq_encPerm_one] at drng7
  have darg7 := Det.mk2 (Det.mk3 (Det.var' (P := P) (env := e6) (i := 2) (v := encGroup gs) rfl)
    (Det.var' (P := P) (env := e6) (i := 6) (v := .list tab) rfl) (Det.nat 0)) drng7
  have hw7 : (Val.list [.list [encGroup gs, .list tab, .nat 0], natList (List.range PX.length)]).wt ≤
      tmRiVs n M := by
    have := wt_list3_le (encGroup gs) (.list tab) (.nat 0)
    have := wt_list2_le (.list [encGroup gs, .list tab, .nat 0]) (natList (List.range PX.length))
    have := hrng PX.length hPXl
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    omega
  have hprofX := EvalAll.call_funAll (f := b + 78) darg7 (Q := fun w c =>
      (∃ obs : List (TmRiO n), w = .list (obs.map tmGlObjVal) ∧ obs.length = PX.length ∧
        (∀ i (hi : i < obs.length), TmRiProfOut (gens σH) (gens gs) Ps (0 + i) obs[i]) ∧
        w.wt ≤ 2000 * tmRiB n M) ∧ c ≤ tmRiPrC hmem n M + tmRiSQ n M) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (tmRi_profs_spec hP hgsl ht (o := 0) (m := PX.length) (by omega) (Wa := tmRiVs n M)
      (by have := wt_list3_le (encGroup gs) (.list tab) (.nat 0); have : (Val.nat 0).wt ≤ 2 :=
        wt_nat_le 0; omega)).mono fun w c h => ?_
    obtain ⟨obs, rfl, hl, hpo, hww, hc⟩ := h
    have hww' := le_trans hww (tmRi_wt_profs (n := n) hPXl hPsl)
    refine ⟨⟨obs, rfl, hl, hpo, hww'⟩, ?_⟩
    have := hprofC PX.length 0 hPXl hw7
    have := wt_list3_le (encGroup gs) (.list tab) (.nat 0)
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have := hrng PX.length hPXl
    have := wt_nat_le PX.length
    have := wt_encPerm_le (1 : Perm (Fin PX.length))
    omega
  refine tmRi_letB hprofX (fun _ _ h => h.2) (by omega) fun v7 c7 h7 => ?_
  obtain ⟨⟨obsX, rfl, hlX, hpoX, hwX⟩, -⟩ := h7
  -- the profiles of `Y`
  set e7 : List Val := e6 ++ [.list (obsX.map tmGlObjVal)] with he7
  have dlen8 := Det.length (Det.var' (P := P) (env := e7) (i := 4) (v := .list (PY.map tmGlObjsVal)) rfl)
  rw [hlPY] at dlen8
  have drng8 := Det.call dlen8 (range_det hP.range PY.length)
  rw [← range_eq_encPerm_one] at drng8
  have dlen8' := Det.length (Det.var' (P := P) (env := e7) (i := 3) (v := .list (PX.map tmGlObjsVal)) rfl)
  rw [hlPX] at dlen8'
  have darg8 := Det.mk2 (Det.mk3 (Det.var' (P := P) (env := e7) (i := 2) (v := encGroup gs) rfl)
    (Det.var' (P := P) (env := e7) (i := 6) (v := .list tab) rfl) dlen8') drng8
  have hPXw' : (Val.nat PX.length).wt ≤ M + 2 := by have := wt_nat_le PX.length; omega
  have hw8 : (Val.list [.list [encGroup gs, .list tab, .nat PX.length],
      natList (List.range PY.length)]).wt ≤ tmRiVs n M := by
    have := wt_list3_le (encGroup gs) (.list tab) (.nat PX.length)
    have := wt_list2_le (.list [encGroup gs, .list tab, .nat PX.length]) (natList (List.range PY.length))
    have := hrng PY.length hPYl
    omega
  have hprofY := EvalAll.call_funAll (f := b + 78) darg8 (Q := fun w c =>
      (∃ obs : List (TmRiO n), w = .list (obs.map tmGlObjVal) ∧ obs.length = PY.length ∧
        (∀ i (hi : i < obs.length), TmRiProfOut (gens σH) (gens gs) Ps (PX.length + i) obs[i]) ∧
        w.wt ≤ 2000 * tmRiB n M) ∧ c ≤ tmRiPrC hmem n M + tmRiSQ n M) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (tmRi_profs_spec hP hgsl ht (o := PX.length) (m := PY.length) (by omega)
      (Wa := tmRiVs n M)
      (by have := wt_list3_le (encGroup gs) (.list tab) (.nat PX.length); omega)).mono
      fun w c h => ?_
    obtain ⟨obs, rfl, hl, hpo, hww, hc⟩ := h
    have hww' := le_trans hww (tmRi_wt_profs (n := n) hPYl hPsl)
    refine ⟨⟨obs, rfl, hl, hpo, hww'⟩, ?_⟩
    have := hprofC PY.length PX.length hPYl hw8
    have := wt_list3_le (encGroup gs) (.list tab) (.nat PX.length)
    have := hrng PY.length hPYl
    have := wt_nat_le PY.length
    have := wt_encPerm_le (1 : Perm (Fin PY.length))
    omega
  refine tmRi_letB hprofY (fun _ _ h => h.2) (by omega) fun v8 c8 h8 => ?_
  obtain ⟨⟨obsY, rfl, hlY, hpoY, hwY⟩, -⟩ := h8
  -- the profiles are `tmRiHat`
  have hr := tmRi_rep (H := gens σH) (Ps := Ps)
  have hXP : pieces (gens gs) (tmGlMs X) ⊆ tmRiPF Ps := tmRiPs_sub_left (gens gs) X Y
  have hYP : pieces (gens gs) (tmGlMs Y) ⊆ tmRiPF Ps := tmRiPs_sub_right (gens gs) X Y
  have hhatX : tmGlMs obsX = tmRiHat (gens σH) (gens gs) (tmRiCol (gens σH) Ps)
      (tmRiRepM (gens σH) Ps) (tmGlMs X) := tmRi_profs_hat_left hAn X Y hlX hpoX
  have hhatY : tmGlMs obsY = tmRiHat (gens σH) (gens gs) (tmRiCol (gens σH) Ps)
      (tmRiRepM (gens σH) Ps) (tmGlMs Y) := tmRi_profs_hat_right hAn X Y hlY hpoY
  -- the recursive call on `(ℓ, H, A, Ŷ, X̂)`
  have hokR : TmRecObjOK M (obsY ++ obsX) := tmRi_profs_ok hPsl fun ob hob => by
    rcases List.mem_append.1 hob with h | h
    · exact tmRi_profs_mem hpoY ob h
    · exact tmRi_profs_mem hpoX ob h
  have hfixY : Fixes (gens gs) (tmGlMs obsY) := by rw [hhatY]; exact tmRiHat_fix hAn _
  have hfixX : Fixes (gens gs) (tmGlMs obsX) := by rw [hhatX]; exact tmRiHat_fix hAn _
  have hfuelA : relDerived (gens σH) (gens gs) ℓ ≤ gens gs := by
    rw [hgs]; exact tmRi_fuel hNH ℓ
  have hrec := ih σH gs obsY obsX hsol hAH hAn hfuelA (by omega) hfixY hfixX hHl hgsl
    (by omega) (by omega) hokR
  set e8 : List Val := e7 ++ [.list (obsY.map tmGlObjVal)] with he8
  have hRw : (tmRecIn ℓ σH gs obsY obsX).wt ≤ tmRiVs n M := by
    have := wt_list_le [.nat ℓ, encGroup σH, encGroup gs, tmGlObjsVal obsY, tmGlObjsVal obsX]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have := wt_nat_le ℓ
    have e1 : (tmGlObjsVal obsY).wt = (Val.list (obsY.map tmGlObjVal)).wt := rfl
    have e2 : (tmGlObjsVal obsX).wt = (Val.list (obsX.map tmGlObjVal)).wt := rfl
    show (Val.list [.nat ℓ, encGroup σH, encGroup gs, tmGlObjsVal obsY, tmGlObjsVal obsX]).wt ≤ _
    omega
  have dml9 := Det.mkList (P := P) (env := e8) (c := 3 * tmRiVs n M + 20)
    [(.var 1, .nat ℓ), (arg 1, encGroup σH), (.var 2, encGroup gs),
      (.var 8, tmGlObjsVal obsY), (.var 7, tmGlObjsVal obsX)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have := wt_nat_le ℓ
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (Det.var' (P := P) (env := e8) (i := 1) rfl).mono (by omega)
    · exact (Det.arg' (P := P) (vs := vs) (rest := e8.tail) (j := 1) (v := encGroup σH) rfl).mono
        (by omega)
    · exact (Det.var' (P := P) (env := e8) (i := 2) rfl).mono (by omega)
    · exact (Det.var' (P := P) (env := e8) (i := 8) rfl).mono (by
        show (Val.list (obsY.map tmGlObjVal)).wt + 1 ≤ _; omega)
    · exact (Det.var' (P := P) (env := e8) (i := 7) rfl).mono (by
        show (Val.list (obsX.map tmGlObjVal)).wt + 1 ≤ _; omega))
  have hcall9 := EvalAll.call_funAll (f := b) dml9 (Q := fun u c =>
      CosetC n u (Iso (gens σH) (tmGlMs obsY) (tmGlMs obsX)) ∧ c ≤ T + tmRiSQ n M)
      fun v ca hv => by
    obtain ⟨hv, hca⟩ := hv
    have hv' : v = tmRecIn ℓ σH gs obsY obsX := hv
    subst hv'
    refine hrec.mono fun u cu h => ⟨h.1, ?_⟩
    have := tmRi_wt_ansC h.1
    have e : (Val.list ([(Expr.var 1, Val.nat ℓ), (arg 1, encGroup σH), (Expr.var 2, encGroup gs),
      (Expr.var 8, tmGlObjsVal obsY), (Expr.var 7, tmGlObjsVal obsX)].map Prod.snd)).wt =
      (tmRecIn ℓ σH gs obsY obsX).wt := rfl
    simp only [List.length_cons, List.length_nil] at hca
    omega
  refine tmRi_letB hcall9 (fun _ _ h => h.2) (by omega) fun ans c9 h9 => ?_
  obtain ⟨hans, -⟩ := h9
  set e9 : List Val := e8 ++ [ans] with he9
  have hansw := tmRi_wt_ansC hans
  rcases hans with ⟨rfl, hC⟩ | ⟨v, hs, rfl, hsl, hC⟩
  · -- the profile transporter is empty
    have dc := Det.length (Det.var' (P := P) (env := e9) (i := 9) (v := .list []) rfl)
    refine tmRi_iteB dc (by simp only [List.length_nil]; omega) (fun h => absurd rfl h) fun _ => ?_
    refine tmRi_detB (Det.nil (P := P) (env := e9)) (Or.inl ⟨rfl, ?_⟩) ?_ ?_
    · have he : Iso (gens σH) (tmRiHat (gens σH) (gens gs) (tmRiCol (gens σH) Ps)
          (tmRiRepM (gens σH) Ps) (tmGlMs X)) (tmRiHat (gens σH) (gens gs) (tmRiCol (gens σH) Ps)
          (tmRiRepM (gens σH) Ps) (tmGlMs Y)) = ∅ := by
        rw [← hhatX, ← hhatY]
        ext g
        rw [tmRi_mem_iso_inv, hC]
        simp
      exact tmRi_prof_empty hr hAn hXP hYP he
    · simp; omega
    · simp only [List.length_nil]; omega
  · -- `Iso_H(Ŷ, X̂) = v B`: the glue with `B` and `τ = v⁻¹`
    rw [hhatY, hhatX] at hC
    have hiso := tmRi_iso_swap hC
    obtain ⟨hAB, hP1, hP2, hP3, hP4, hP5⟩ := tmRi_glue_pre hr hAH hAn hXP hYP hiso
    have hτ : v⁻¹ ∈ gens σH := by
      have : v⁻¹ ∈ tmGlCoset (gens hs) v⁻¹ := ⟨1, (gens hs).one_mem, one_mul _⟩
      rw [← hiso] at this; exact this.1
    have hBH : gens hs ≤ gens σH := by
      intro g hg
      have : g * v⁻¹ ∈ tmGlCoset (gens hs) v⁻¹ := ⟨g, hg, rfl⟩
      rw [← hiso] at this
      simpa using (gens σH).mul_mem this.1 ((gens σH).inv_mem hτ)
    have hcomm : ∀ a ∈ gens gs, ∀ c ∈ gens gs, a * c * a⁻¹ * c⁻¹ ∈ gens σN := by
      intro a ha c hc
      rw [hgs] at ha hc
      simpa [commutatorElement_def] using relDerived_commutator_mem hfuel ha hc
    have hgl := hglue σH σN gs X Y hs v⁻¹ hsol hNA hAH hNn hAn hcomm hNX hNY hAB hBH hτ
      hP1 hP2 hP3 hP4 hP5
    have hu9 : (Val.list [encPerm v, encGroup hs]).wt ≤ 700 * (n + 1) ^ 6 := hansw
    have dc := Det.length (Det.var' (P := P) (env := e9) (i := 9)
      (v := .list [encPerm v, encGroup hs]) rfl)
    refine tmRi_iteB dc (by simp only [List.length_cons, List.length_nil]; omega)
      (fun _ => ?_) (fun h => absurd h (by simp))
    have hvw : (encPerm v).wt < (Val.list [encPerm v, encGroup hs]).wt := wt_le_wt_list (by simp)
    have hsw : (encGroup hs).wt < (Val.list [encPerm v, encGroup hs]).wt := wt_le_wt_list (by simp)
    have hiw := wt_encPerm_le v⁻¹
    have hGw : (tmGlIn σH σN gs X Y hs v⁻¹).wt ≤ tmRiVs n M := by
      have := wt_list_le [encGroup σH, encGroup σN, encGroup gs, tmGlObjsVal X, tmGlObjsVal Y,
        encGroup hs, encPerm v⁻¹]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this
      have e1 : (tmGlObjsVal X).wt = (Val.list Xv).wt := rfl
      have e2 : (tmGlObjsVal Y).wt = (Val.list Yv).wt := rfl
      show (Val.list [encGroup σH, encGroup σN, encGroup gs, tmGlObjsVal X, tmGlObjsVal Y,
        encGroup hs, encPerm v⁻¹]).wt ≤ _
      omega
    have dml := Det.mkList (P := P) (env := e9) (c := 3 * tmRiVs n M + 100)
      [(arg 1, encGroup σH), (arg 2, encGroup σN), (.var 2, encGroup gs), (arg 3, tmGlObjsVal X),
        (arg 4, tmGlObjsVal Y), (.get (.var 9) (.nat 1), encGroup hs),
        (.call (b + 21) (.get (.var 9) (.nat 0)), encPerm v⁻¹)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Det.arg' (P := P) (vs := vs) (rest := e9.tail) (j := 1) (v := encGroup σH) rfl).mono
          (by omega)
      · exact (Det.arg' (P := P) (vs := vs) (rest := e9.tail) (j := 2) (v := encGroup σN) rfl).mono
          (by omega)
      · exact (Det.var' (P := P) (env := e9) (i := 2) rfl).mono (by omega)
      · exact (Det.arg' (P := P) (vs := vs) (rest := e9.tail) (j := 3) (v := .list Xv) rfl).mono
          (by omega)
      · exact (Det.arg' (P := P) (vs := vs) (rest := e9.tail) (j := 4) (v := .list Yv) rfl).mono
          (by omega)
      · exact (Det.get' (Det.var' (P := P) (env := e9) (i := 9) rfl) (Det.nat 1)
          (v := encGroup hs) rfl).mono (by omega)
      · exact (Det.call (Det.get' (Det.var' (P := P) (env := e9) (i := 9) rfl) (Det.nat 0)
          (v := encPerm v) rfl) (inv_spec hP.inv v)).mono (by omega))
    have hglc := EvalAll.call_funAll (f := gObj) dml (Q := fun w c => R w ∧ w.wt ≤ Wo ∧
        c ≤ 3 * 10 ^ 4 * (tmRiVs n M + 1) + Kg * (tmRiVs n M + 1) ^ Dg) fun u ca hu => by
      obtain ⟨hu, hca⟩ := hu
      have hu' : u = tmGlIn σH σN gs X Y hs v⁻¹ := hu
      subst hu'
      refine hgl.mono fun w cw h => ?_
      have hw := tmRi_ansC_iff.1 h.1
      have hww := tmRi_wt_ansC hw
      have hpow : Kg * ((tmGlIn σH σN gs X Y hs v⁻¹).wt + 1) ^ Dg ≤ Kg * (tmRiVs n M + 1) ^ Dg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have e : (Val.list ([(arg 1, encGroup σH), (arg 2, encGroup σN), (Expr.var 2, encGroup gs),
        (arg 3, tmGlObjsVal X), (arg 4, tmGlObjsVal Y), (Expr.get (.var 9) (.nat 1), encGroup hs),
        (Expr.call (b + 21) (.get (.var 9) (.nat 0)), encPerm v⁻¹)].map Prod.snd)).wt =
        (tmGlIn σH σN gs X Y hs v⁻¹).wt := rfl
      simp only [List.length_cons, List.length_nil] at hca
      exact ⟨hw, by omega, by omega⟩
    exact hglc.mono fun w c h => ⟨h.1, h.2.1, by
      simp only [List.length_cons, List.length_nil] at *
      omega⟩

end GI.Impl
