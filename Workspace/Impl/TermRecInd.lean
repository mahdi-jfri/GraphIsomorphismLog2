import Workspace.Impl.TermRecPoly
import Workspace.Impl.TermRecSpec

/-!
# T5, the recursion of Theorem A.20 by induction on the fuel

The main function `b` of `tmRiFuns` looks at the fuel `ℓ`. For `ℓ = 0` it calls the base case
`b + 1` (`tmRi_base_spec`), and for `ℓ + 1` it calls the step `b + 2` (`tmRi_step_spec`), which
calls `b` again on fuel `ℓ`. One level spends at most the polynomial `tmRiOwnC n M` of its own
(`tmRiOwn_poly`) and makes at most `4M³ + 1` calls of the level below. So with
`a = 5 (M + 1)³ + 1` and `Q = tmRiOwnC n M`, the cost at fuel `ℓ` is at most `a^ℓ Q`
(`tmRi_ind`), because `(4M³ + 1) a^ℓ Q + Q ≤ a^(ℓ+1) Q`.

`tmRi_termRecSpec` is the result used later: `TermRecSpec` at `b`, for a program that holds
`tmRiFuns` at `b`, the three cited primitives, and a glue program that meets
`TermGlueObjSpec`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset GI.Algorithm GI.Assembly Equiv
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-- The weight of the input of one call. -/
theorem tmRi_in_wt {M ℓ : ℕ} {σH σN : List (Perm (Fin n))} {X Y : List (TmRiO n)}
    (hℓ : ℓ ≤ n ^ 2 + 5) (hHl : σH.length ≤ n ^ 2) (hNl : σN.length ≤ n ^ 2)
    (hX : X.length ≤ M) (hY : Y.length ≤ M) (hok : TmRecObjOK M (X ++ Y)) :
    (tmRecIn ℓ σH σN X Y).wt ≤ tmRiVs n M := by
  obtain ⟨fB1, fB2, fB3, fB4, fB5⟩ := tmRiB_facts n M
  obtain ⟨fV1, fV2, fV3, fV4⟩ := tmRiVs_facts n M
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnn : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hokX : TmRiOK (2 * M) X := fun o ho =>
    ⟨(hok o (by simp [ho])).1, by have := (hok o (by simp [ho])).2.1; omega,
      fun o' ho' he => (hok o (by simp [ho])).2.2 o' (by simp [ho']) he⟩
  have hokY : TmRiOK (2 * M) Y := fun o ho =>
    ⟨(hok o (by simp [ho])).1, by have := (hok o (by simp [ho])).2.1; omega,
      fun o' ho' he => (hok o (by simp [ho])).2.2 o' (by simp [ho']) he⟩
  have hXw : (tmGlObjsVal X).wt ≤ 2020 * tmRiB n M := tmRi_wt_side hX hokX
  have hYw : (tmGlObjsVal Y).wt ≤ 2020 * tmRiB n M := tmRi_wt_side hY hokY
  have hHw : (encGroup σH).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hHl
  have hNw : (encGroup σN).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hNl
  have hlw : (Val.nat ℓ).wt ≤ (n + 1) ^ 6 + 8 := by have := wt_nat_le ℓ; omega
  have := wt_list_le [.nat ℓ, encGroup σH, encGroup σN, tmGlObjsVal X, tmGlObjsVal Y]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  show (Val.list [.nat ℓ, encGroup σH, encGroup σN, tmGlObjsVal X, tmGlObjsVal Y]).wt ≤ _
  omega

/-- **The dispatch** `b`: fuel `0` goes to `b + 1`, fuel `ℓ + 1` to `b + 2`. -/
theorem tmRi_main_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {M ℓ T : ℕ}
    {σH σN : List (Perm (Fin n))} {X Y : List (TmRiO n)}
    (hw : (tmRecIn ℓ σH σN X Y).wt ≤ tmRiVs n M)
    (h0 : ℓ = 0 → FunAll P (b + 1) (tmRecIn ℓ σH σN X Y) (fun u c =>
      CosetC n u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧ c ≤ T))
    (h1 : ℓ ≠ 0 → FunAll P (b + 2) (tmRecIn ℓ σH σN X Y) (fun u c =>
      CosetC n u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧ c ≤ T)) :
    FunAll P b (tmRecIn ℓ σH σN X Y) (fun u c =>
      CosetC n u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧ c ≤ T + 10 * tmRiVs n M) := by
  obtain ⟨fV1, fV2, fV3, fV4⟩ := tmRiVs_facts n M
  set vs : List Val := [.nat ℓ, encGroup σH, encGroup σN, tmGlObjsVal X, tmGlObjsVal Y] with hvs
  have hain : tmRecIn ℓ σH σN X Y = .list vs := rfl
  rw [hain] at hw h0 h1 ⊢
  obtain ⟨Wo, hWo⟩ : ∃ w, w = 700 * (n + 1) ^ 6 := ⟨_, rfl⟩
  have hWoV : Wo ≤ tmRiVs n M := by omega
  refine FunAll.intro hP.main (EvalAll.mono (Q := fun w c =>
    CosetC n w (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧ w.wt ≤ Wo ∧ c ≤ T + 10 * tmRiVs n M) ?_
    fun w c h => ⟨h.1, h.2.2⟩)
  have dc := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := .nat ℓ) rfl
  have dv := Det.var' (P := P) (env := [Val.list vs]) (i := 0) (v := .list vs) rfl
  refine tmRi_iteB dc (by omega) (fun h => ?_) (fun h => ?_)
  · refine EvalAll.call_funAll dv fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (h1 h).mono fun w c hc => ⟨hc.1, hWo ▸ tmRi_wt_ansC hc.1, ?_⟩
    have := tmRi_wt_ansC hc.1
    omega
  · refine EvalAll.call_funAll dv fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (h0 h).mono fun w c hc => ⟨hc.1, hWo ▸ tmRi_wt_ansC hc.1, ?_⟩
    have := tmRi_wt_ansC hc.1
    omega

/-- The growth factor of one level. -/
def tmRiA (M : ℕ) : ℕ := 5 * (M + 1) ^ 3 + 1

/-- **The recursion at fuel `ℓ` costs at most `a^ℓ Q`**, with `a = 5 (M + 1)³ + 1` and `Q` the
own cost of one level. -/
theorem tmRi_ind {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {Kg Dg : ℕ}
    (hglue : Iface.TermGlueObjSpec P Kg Dg gObj) (M : ℕ) :
    ∀ ℓ, TmRiIH P b n M ℓ (tmRiA M ^ ℓ * tmRiOwnC hsci hder hmem Kg Dg n M) := by
  obtain ⟨Q, hQ⟩ : ∃ q, q = tmRiOwnC hsci hder hmem Kg Dg n M := ⟨_, rfl⟩
  rw [← hQ]
  have hQs : tmRiStepO hsci hder hmem Kg Dg n M + 10 * tmRiVs n M ≤ Q := by
    rw [hQ]; unfold tmRiOwnC; omega
  have hQb : tmRiBaseC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) n
      (tmRiVs n M) + 10 * tmRiVs n M ≤ Q := by
    rw [hQ]; unfold tmRiOwnC; omega
  intro ℓ
  induction ℓ with
  | zero =>
    intro σH σN X Y hsol hNH hNn hfuel hℓ hNX hNY hHl hNl hX hY hok
    have hw := tmRi_in_wt hℓ hHl hNl hX hY hok
    refine (tmRi_main_spec hP hw (T := tmRiBaseC (tmRiObjPC (solvableCosetIntersectionPrim hsci)
      n (2 * M)) n (tmRiVs n M)) (fun _ => tmRi_base_spec hP hfuel hNX hHl hok hw)
      (fun h => absurd rfl h)).mono fun u c h => ⟨h.1, ?_⟩
    simp only [pow_zero, one_mul]
    omega
  | succ ℓ ih =>
    intro σH σN X Y hsol hNH hNn hfuel hℓ hNX hNY hHl hNl hX hY hok
    have hw := tmRi_in_wt hℓ hHl hNl hX hY hok
    have hst := tmRi_step_spec hP hglue ih hsol hNH hNn hfuel hℓ hNX hNY hHl hNl hX hY hok
    refine (tmRi_main_spec hP hw (fun h => absurd h (by omega)) fun _ => hst).mono
      fun u c h => ⟨h.1, ?_⟩
    have hQ1 : Q ≤ tmRiA M ^ ℓ * Q := Nat.le_mul_of_pos_left _ (pow_pos (by
      unfold tmRiA; omega) _)
    have hA : 4 * M ^ 3 + 2 ≤ tmRiA M := by
      unfold tmRiA
      have : M ^ 3 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have : 1 ≤ (M + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have hgrow : 4 * M ^ 3 * (tmRiA M ^ ℓ * Q) + tmRiA M ^ ℓ * Q + Q ≤
        tmRiA M ^ (ℓ + 1) * Q := by
      calc _ ≤ 4 * M ^ 3 * (tmRiA M ^ ℓ * Q) + tmRiA M ^ ℓ * Q + tmRiA M ^ ℓ * Q := by omega
        _ = (4 * M ^ 3 + 2) * (tmRiA M ^ ℓ * Q) := by ring
        _ ≤ tmRiA M * (tmRiA M ^ ℓ * Q) := Nat.mul_le_mul_right _ hA
        _ = tmRiA M ^ (ℓ + 1) * Q := by ring
    omega

/-- **Theorem A.20 as a program**: `TermRecSpec` at `b`. The constants `K, D` depend only on the
cited algorithms and on the glue's constants `Kg, Dg`. -/
theorem tmRi_termRecSpec (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hmem : Membership) (Kg Dg : ℕ) :
    ∃ K D : ℕ, ∀ {P : Program} {b jsci jder jmem gObj : ℕ},
      TmRiAt P b jsci jder jmem gObj hsci hder hmem → Iface.TermGlueObjSpec P Kg Dg gObj →
      Iface.TermRecSpec P K D b := by
  obtain ⟨C, D, hC⟩ := tmRiOwn_poly hsci hder hmem Kg Dg
  refine ⟨C, D, fun {P b jsci jder jmem gObj} hP hglue => ?_⟩
  intro n M ℓ σH σN X Y hsol hNH hNn hfuel hℓ hNX hNY hHl hNl hX hY hok
  refine (tmRi_ind hP hglue M ℓ σH σN X Y hsol hNH hNn hfuel hℓ hNX hNY hHl hNl hX hY hok).mono
    fun u c h => ⟨tmRi_ansC_iff.2 h.1, ?_⟩
  have h1 : c ≤ tmRiA M ^ ℓ * (C * (n + M + 2) ^ D) :=
    h.2.trans (Nat.mul_le_mul_left _ (hC n M))
  have h2 : ((tmRiA M ^ ℓ * (C * (n + M + 2) ^ D) : ℕ) : ℝ) =
      (5 * ((M : ℝ) + 1) ^ 3 + 1) ^ ℓ * (C * (((n + M : ℕ) : ℝ) + 2) ^ D) := by
    unfold tmRiA; push_cast; ring
  rw [← h2]
  exact_mod_cast h1

end GI.Impl
