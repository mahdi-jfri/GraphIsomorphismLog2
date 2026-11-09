module

public import Workspace.Degree.CaseData
public import Workspace.Degree.Drops
public import Workspace.Algorithm.Existence
public import Workspace.Algorithm.DispatchInv

@[expose] public section

/-!
# The children of the three cases

The child of an enumeration, a product or a normalization is a restriction of a state `R` with the
invariant. This file proves that a child has the invariant, a smaller measure, and the shape that
the spine asks for.

* `DGood.restrict`: the invariant passes to a restriction.
* `enumChild_facts`: the children of an enumeration. The kernel is intransitive.
* `prodChild_facts`: the children of a product. The rank `ρ` falls by `r - 1`.
* `two_mul_orb_le`: an orbit of a normal subgroup that is not the whole domain has at most `s / 2`
  points. No bound on the index is used.
* `normChild_giant`, `normChild_cont`: the children of a normalization.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly Equiv Equiv.Perm Real

variable {Ω C : Type}

/-- The invariant passes to a restriction with bounded caps. -/
theorem DGood.restrict {D Nm : ℕ} {S : State Ω C} (hd : DGood D Nm S) {K : Subgroup (Perm Ω)}
    (hK : K ≤ S.G) (x y : Ω → C) {l : List (Interval Ω)} (hinv : HierInv K S.dom l)
    (hc : ∀ I ∈ l, I.cap ≤ D) : DGood D Nm (S.restrict K hK x y l) := by
  have hco : CarrierOK K S.dom S.rows l := by
    rw [hd.rows]
    exact CarrierOK.none _ _ _
  refine hd.child rfl hd.size_le hK hinv ?_ ?_ ?_ hc
  · rw [State.restrict_rows_of _ _ _ _ _ _ hco]
    exact hd.rows
  · rw [State.restrict_floor_of _ _ _ _ _ _ hco]
    exact hd.floor
  · rw [State.restrict_h_of _ _ _ _ _ _ hco]
    exact hd.h

/-- A restriction has the facts of a `Continue` call. -/
theorem good_restrict {D Nm : ℕ} {S : State Ω C} (hd : DGood D Nm S) {K : Subgroup (Perm Ω)}
    (hK : K ≤ S.G) (x y : Ω → C) {l : List (Interval Ω)} (hinv : HierInv K S.dom l) :
    Good P₀ .cont (S.restrict K hK x y l) :=
  ⟨hd.N_gt, hd.size_le, hinv⟩

theorem rhoNat_le_of {l l' : List (Interval Ω)}
    (h : State.hierRho l ≤ State.hierRho l') : rhoNat l ≤ rhoNat l' := by
  have h1 : (rhoNat l : ℝ) ≤ rhoNat l' := by
    rw [rhoNat_cast, rhoNat_cast]
    exact h
  exact_mod_cast h1

/-- The caps of the exposed hierarchy stay at most `D`. -/
theorem caps_exposed {D : ℕ} {S : State Ω C} (Q : PrimitiveQuotient S)
    (hc : ∀ I ∈ S.hier, I.cap ≤ D) : ∀ I ∈ Q.pre ++ Q.top :: Q.post, I.cap ≤ D := by
  intro I hI
  rcases Q.from_old I hI with h | ⟨J, hJ, -, -, h, -⟩
  · exact hc I h
  · exact h.trans (hc J hJ)

section Enum

variable {D Nm : ℕ} {R : State Ω C} (Q : PrimitiveQuotient R)

/-- **The children of an enumeration.** -/
theorem enumChild_facts [Finite Ω] (hd : DGood D Nm R) (ht : R.Transitive) (h2 : 2 ≤ R.size)
    (x y : Ω → C) :
    let T := R.restrict Q.kernel Q.kernel_le x y (Q.pre ++ Q.top :: Q.post)
    DGood D Nm T ∧ Good P₀ .cont T ∧
      MLt (GI.Algorithm.measure P₀ .cont T) (GI.Algorithm.measure P₀ .cont R) ∧
      T.dres.s ≤ R.dres.s ∧ T.dres.psi + Real.log Q.d / 3 ≤ R.dres.psi ∧
      T.dres.rho ≤ R.dres.rho ∧ T.dres.Q ≤ R.dres.Q := by
  intro T
  have hinv : HierInv Q.kernel R.dom (Q.pre ++ Q.top :: Q.post) :=
    HierInv.mono Q.tower Q.kernel_le subset_rfl
  have hc := enum_child (T := T) ht Q.two_le Q.d_le_size Q.kernel_le subset_rfl
    (Q.kernel_orbit ht) (rhoNat_le_of Q.rho_le) Q.Q_le
  refine ⟨hd.restrict _ _ _ hinv (caps_exposed Q hd.caps), good_restrict hd _ _ _ hinv, ?_, hc⟩
  have hnt : ¬ T.Transitive := by
    intro htj
    obtain ⟨v, hv⟩ := exists_mem_dom (by omega : 1 ≤ R.size)
    have h1 := size_le_orb htj hv
    have h3 := Q.kernel_orbit ht v hv
    change R.size ≤ Nat.card (orb Q.kernel v) at h1
    have : 2 * R.size ≤ R.size := (Nat.mul_le_mul Q.two_le h1).trans h3
    omega
  have h0 := trInd_of_not _ hnt
  have h1' := trInd_of R ht
  have h3 : T.size = R.size := rfl
  have h4 : T.N = R.N := rfl
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
    false_or]
  omega

end Enum

section Product

variable {D Nm : ℕ} {R : State Ω C}

/-- **The children of a product**, for a dispatch step of the general algorithm of product kind. -/
theorem prodChild_facts [Finite Ω] (hd : DGood D Nm R) (ht : R.Transitive) (I : DispatchStep P₀ R)
    (hc : ∀ J ∈ I.hier', J.cap ≤ D) {r : ℕ} (hk : I.kind = .product r) (x y : Ω → C) :
    let T := R.restrict I.K I.K_le x y I.hier'
    DGood D Nm T ∧ Good P₀ .cont T ∧
      MLt (GI.Algorithm.measure P₀ .cont T) (GI.Algorithm.measure P₀ .cont R) ∧
      T.dres.s ≤ R.dres.s ∧ T.dres.psi ≤ R.dres.psi ∧
      T.dres.rho + ((r : ℝ) - 1) ≤ R.dres.rho ∧ T.dres.Q ≤ R.dres.Q := by
  intro T
  have hinv : HierInv I.K R.dom I.hier' := I.hierInv
  have hf := I.facts
  rw [hk] at hf
  obtain ⟨hr2, -, -, hρ⟩ := hf
  have hsh := product_child (T := T) I.K_le subset_rfl hρ I.Q_le
  refine ⟨hd.restrict _ _ _ hinv hc, good_restrict hd _ _ _ hinv, ?_, hsh⟩
  have hσ : T.sigma P₀.κ ≤ R.sigma P₀.κ :=
    State.sigma_le_of P₀_terminating.κ_five I.K_le le_rfl
  have htrj := trInd_le T
  have hρ' : rhoNat I.hier' + 1 ≤ rhoNat R.hier := by
    have h1 : (rhoNat I.hier' : ℝ) + 1 ≤ rhoNat R.hier := by
      rw [rhoNat_cast, rhoNat_cast]
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      linarith
    exact_mod_cast h1
  have h3 : T.size = R.size := rfl
  have h4 : T.N = R.N := rfl
  have h5 : rhoNat T.hier = rhoNat I.hier' := rfl
  have h6 := trInd_of R ht
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
    false_or]
  omega

end Product

/-- **An orbit of a normal subgroup that is not the whole domain has at most `s / 2` points.** Some
`g` in `G` moves `v` out of its orbit `O`. Then `g O` is another orbit, of the same size. -/
theorem two_mul_orb_le [Finite Ω] {S : State Ω C} (ht : S.Transitive) {H : Subgroup (Perm Ω)}
    (hH : H ≤ S.G) (hn : (H.subgroupOf S.G).Normal) (hnt : ¬ ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ H, g v = w)
    (v : Ω) (hv : v ∈ S.dom) : 2 * Nat.card (orb H v) ≤ S.size := by
  classical
  have hsub : orb H v ⊆ S.dom := by
    rintro _ ⟨g, hg, rfl⟩
    exact (S.dom_inv g (hH hg) v).2 hv
  -- A point of the domain outside the orbit.
  have hex : ∃ w ∈ S.dom, w ∉ orb H v := by
    by_contra hall
    push Not at hall
    refine hnt fun a ha b hb => ?_
    obtain ⟨g₁, hg₁, e₁⟩ := hall a ha
    obtain ⟨g₂, hg₂, e₂⟩ := hall b hb
    refine ⟨g₂ * g₁⁻¹, H.mul_mem hg₂ (H.inv_mem hg₁), ?_⟩
    rw [Perm.mul_apply, ← e₁, Perm.inv_apply_self, e₂]
  obtain ⟨w, hw, hwO⟩ := hex
  obtain ⟨g, hg, rfl⟩ := ht v hv w hw
  have hconj : ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
    intro h hh
    have := hn.conj_mem ⟨h, hH hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hdisj : Disjoint (orb H v) (g '' orb H v) := by
    rw [Set.disjoint_left]
    rintro _ ⟨h₁, hh₁, rfl⟩ ⟨_, ⟨h₂, hh₂, rfl⟩, e⟩
    refine hwO ⟨(g * h₂ * g⁻¹)⁻¹ * h₁, H.mul_mem (H.inv_mem (hconj h₂ hh₂)) hh₁, ?_⟩
    rw [Perm.mul_apply, ← e, Perm.inv_eq_iff_eq]
    simp [Perm.mul_apply]
  have hsub2 : g '' orb H v ⊆ S.dom := by
    rintro _ ⟨u, hu, rfl⟩
    exact (S.dom_inv g hg u).2 (hsub hu)
  have hcard := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ g.injective] at hcard
  have hle : (orb H v ∪ g '' orb H v).ncard ≤ S.dom.ncard :=
    Set.ncard_le_ncard (Set.union_subset hsub hsub2) (Set.toFinite _)
  rw [card_orb_eq]
  have e : S.size = S.dom.ncard := _root_.Nat.card_coe_set_eq _
  omega

section Norm

variable {D Nm : ℕ} {R : State Ω C} (N : NormAbove P₀ R)

theorem capSum_cases :
    rhoNat N.I.hier' ≤ rhoNat R.hier ∧
      (rhoNat N.I.hier' < rhoNat R.hier ∨ capSum N.I.hier' ≤ capSum R.hier) := by
  refine ⟨rhoNat_le_of N.I.rho_le, ?_⟩
  rcases N.I.drop with h | h
  · left
    have h1 : (rhoNat N.I.hier' : ℝ) < rhoNat R.hier := by
      rw [rhoNat_cast, rhoNat_cast]
      exact h
    exact_mod_cast h1
  · exact Or.inr h

/-- **The child of a normalization with a transitive group**: a call of `GiantStep`. -/
theorem normChild_giant [Finite Ω] (hd : DGood D Nm R) (ht : R.Transitive) (hNs : R.N = R.size)
    (h2 : 2 ≤ R.size) (hc : ∀ J ∈ N.I.hier', J.cap ≤ D)
    (hT : ∀ v ∈ R.dom, ∀ w ∈ R.dom, ∃ g ∈ N.I.G', g v = w) (j : Fin N.I.k) :
    DGood D Nm (N.child j) ∧ Good P₀ .giant (N.child j) ∧
      MLt (GI.Algorithm.measure P₀ .giant (N.child j)) (GI.Algorithm.measure P₀ .cont R) ∧
      (N.child j).dres.Le R.dres := by
  have hle : (N.child j).dres.Le R.dres :=
    le_child (T := N.child j) N.I.le subset_rfl (rhoNat_le_of N.I.rho_le) N.I.Q_le
  refine ⟨hd.restrict _ _ _ N.tower hc, ⟨hd.N_gt, hd.size_le, hT, ?_, N.tower,
    ⟨⟨N.childLabels j, N.q_large⟩⟩⟩, ?_, hle⟩
  · change (R.N : ℝ) ^ P₀.γ < R.size
    rw [hNs]
    have h2' : (1 : ℝ) < R.size := by exact_mod_cast h2
    have := Real.rpow_lt_rpow_of_exponent_lt h2' (show P₀.γ < 1 by rw [show P₀.γ = 9 / 10 from rfl]; norm_num)
    simpa using this
  · have htrj : trInd (N.child j) = 1 := trInd_of _ hT
    have htr1 := trInd_of R ht
    have hσ : (N.child j).sigma P₀.κ ≤ R.sigma P₀.κ :=
      State.sigma_le_of P₀_terminating.κ_five N.I.le le_rfl
    obtain ⟨hρ, hdrop⟩ := capSum_cases N
    rw [mlt_iff]
    simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
      false_or]
    have h1 : (N.child j).size = R.size := rfl
    have hNj : (N.child j).N = R.N := rfl
    have h2 : rhoNat (N.child j).hier = rhoNat N.I.hier' := rfl
    have hfl : (N.child j).floor = R.floor := State.restrict_floor_of _ _ _ _ _ _ N.keeps
    have h3 : flInd (N.child j) = flInd R := by simp only [flInd, hfl]
    have h4 : (N.child j).h = R.h := State.restrict_h_of _ _ _ _ _ _ N.keeps
    have h5 : capSum (N.child j).hier = capSum N.I.hier' := rfl
    omega

/-- **The child of a normalization with an intransitive group**: a call of `Continue`, and `ψ`
falls because each orbit has at most `s / 2` points. -/
theorem normChild_cont [Finite Ω] (hd : DGood D Nm R) (ht : R.Transitive) (h2 : 2 ≤ R.size)
    (hc : ∀ J ∈ N.I.hier', J.cap ≤ D)
    (hT : ¬ ∀ v ∈ R.dom, ∀ w ∈ R.dom, ∃ g ∈ N.I.G', g v = w) (j : Fin N.I.k) :
    DGood D Nm (N.child j) ∧ Good P₀ .cont (N.child j) ∧
      MLt (GI.Algorithm.measure P₀ .cont (N.child j)) (GI.Algorithm.measure P₀ .cont R) ∧
      (N.child j).dres.s ≤ R.dres.s ∧ (N.child j).dres.rho ≤ R.dres.rho ∧
      (N.child j).dres.Q ≤ R.dres.Q ∧ (N.child j).dres.psi + cZero ≤ R.dres.psi := by
  refine ⟨hd.restrict _ _ _ N.tower hc, ⟨hd.N_gt, hd.size_le, N.tower⟩, ?_,
    norm_child_cont (T := N.child j) ht h2 N.I.le subset_rfl
      (fun v hv => two_mul_orb_le ht N.I.le N.I.normal hT v hv) N.I.rho_le N.I.Q_le⟩
  have htrj : trInd (N.child j) = 0 := trInd_of_not _ hT
  have htr1 := trInd_of R ht
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
    false_or]
  have h1 : (N.child j).size = R.size := rfl
  have hNj : (N.child j).N = R.N := rfl
  omega

end Norm

end GI.Degree
