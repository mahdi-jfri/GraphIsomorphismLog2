import Workspace.Impl.TermGlueLabPOffL

/-!
# Reading the transporters for one `h`

Step 3 of the label program. Two facts connect the program of
`TermGlueLabPOffL` with the offsets of `TermGlueLabPOff`.

* `tmGLP_rows_nonempty`: when the residual set is not empty, every row of `x` has a nonempty
  stored coset `Iso_H(x_j, y_l)` for some `l`. This is the hypothesis of `tmGLPOff_spec`. The
  reason: an element `τ` of the residual set carries the types of `x` to the types of `y`, so
  `x_j^τ` lies in the `N`-orbit of some `y_l`.
* `tmGLP_off_item`: for `h` in `D = Aut_H(T)`, the search never fails, and its result
  `[j, s]` gives `rep(a)^h = rep(a^h)^s` for the type `a` of `x_i`, with the first rows as
  representatives. This is the hypothesis `hsr` of `tmGLP_u_rows`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- An `N`-type that lies in `types N x` is the type of a row. -/
theorem tmGLP_mem_types {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {a : Set Ω}
    (ha : a ∈ types N X) : ∃ j : Fin q, a = orbitN N (X j) := by
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp ha
  exact ⟨j, hj.symm⟩

/-- **Every row of `x` has a nonempty stored coset** when some `τ ∈ H` carries the types of `x`
to the types of `y`. -/
theorem tmGLP_rows_nonempty {H N : Subgroup (Perm (Fin n))} (hNH : N ≤ H)
    (hn : GI.Multicoset.Normalizes H N) {q : ℕ} {X Y : Fin q → Ω} {τ : Perm (Fin n)}
    (hτ : τ ∈ Iso H (types N X) (types N Y)) (j : Fin q) :
    ∃ l : Fin q, (Iso H (X j) (Y l)).Nonempty := by
  have hmem : orbitN N (X j) ↼ τ ∈ types N Y := by
    rw [← hτ.2]
    exact act_mem_act τ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val j))
  rw [orbitN_act hn hτ.1] at hmem
  obtain ⟨l, hl⟩ := tmGLP_mem_types hmem
  -- `x_j^τ` lies in the `N`-orbit of `y_l`
  have hx : X j ↼ τ ∈ orbitN N (Y l) := by rw [← hl]; exact tmGLP_self_mem N _
  obtain ⟨m, hm, hmx⟩ := hx
  refine ⟨l, τ * m⁻¹, H.mul_mem hτ.1 (H.inv_mem (hNH hm)), ?_⟩
  rw [← act_act, ← hmx, act_act, mul_inv_cancel, act_one]

/-- **One entry of the transporters for `h ∈ D`.** The search result for the representative
of the type of `x_i` is `[j, s]` with `s ∈ N`, `j` the first row of the type of
`rep(a)^h`, and `rep(a)^h = rep(a^h)^s`. -/
theorem tmGLP_off_item {H N : Subgroup (Perm (Fin n))} (hn : GI.Multicoset.Normalizes H N)
    {q : ℕ} {X : Fin q → Ω} (j0 : Fin q) {h : Perm (Fin n)} (hD : h ∈ Aut H (types N X)) {i : Fin q}
    {u : Val} (hu : TmGLPOItem N X h i u) :
    ∃ j : Fin q, ∃ s ∈ N, u = .list [.nat j, encPerm s] ∧
      TmGLPFirst N X (tmGLPRep N X j0 (orbitN N (X i)) ↼ h) j ∧
      tmGLPRep N X j0 (orbitN N (X i)) ↼ h =
        tmGLPRep N X j0 (orbitN N (X i) ↼ h) ↼ s := by
  obtain ⟨J, hJ, hf⟩ := hu
  have hhH := (mem_aut.mp hD).1
  have hrep : tmGLPRep N X j0 (orbitN N (X i)) = X J := tmGLP_rep_eq j0 hJ
  -- the type of `x_J^h` is a type of `x`
  have hmem : orbitN N (X J) ↼ h ∈ types N X := by
    rw [← (mem_aut.mp hD).2]
    exact act_mem_act h (Multiset.mem_map_of_mem _ (Finset.mem_univ_val J))
  rw [orbitN_act hn hhH] at hmem
  obtain ⟨j1, hj1⟩ := tmGLP_mem_types hmem
  have hin : X J ↼ h ∈ orbitN N (X j1) := by rw [← hj1]; exact tmGLP_self_mem N _
  rcases hf with ⟨-, hno⟩ | ⟨j, s, hs, rfl, hsZ, hmin⟩
  · obtain ⟨m, hm, hmx⟩ := hin
    exact absurd hmx (hno j1 m hm)
  have hfst : TmGLPFirst N X (X J ↼ h) j := tmGLP_first_of_find hs hsZ hmin
  refine ⟨j, s, hs, rfl, hrep ▸ hfst, ?_⟩
  rw [hrep, tmGLP_orbit_eq hJ.1, orbitN_act hn hhH, tmGLP_rep_eq j0 hfst, hsZ]

end GI.Impl
