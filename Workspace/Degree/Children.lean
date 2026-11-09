module

public import Workspace.Degree.Reset
public import Workspace.Degree.RoundMass
public import Workspace.Impl.AggWin

@[expose] public section

/-!
# The children of a node

This file proves the shapes of `Workspace/Degree/Spine.lean`, at the level of states.

* `DGood.child`: the invariant of the recursion passes to a child.
* `Script.children`: the `Continue` calls of a script along the exact answers, as a list.
* `localChild_of_call`, `script_children_good`, `massOK_of_round`: the calls of a round are local
  children, with the invariant, and with the mass bound of Lemma 8.4.
* `overChild_of_capUpdate`: a continuation on an overcoset lowers `Q`.
* `enum_child`, `product_child`, `norm_child_*`, `orbit_child`: the other operations.
-/

namespace GI.Algorithm

variable {Ω C α : Type}

namespace Script

open GI.Degree

/-- The `Continue` calls of a script along the exact answers. -/
noncomputable def children : Script α → List Child
  | done _ => []
  | ask m S k =>
    (if m = .cont then [⟨_, _, S, false⟩] else []) ++ (k S.answer).children

theorem mass_eq_children : ∀ s : Script α,
    s.mass = ((s.children).map fun c => c.res.sz ^ 3).sum
  | done _ => by simp [mass, children]
  | ask m S k => by
    simp only [mass, children, List.map_append, List.sum_append]
    rw [mass_eq_children (k S.answer)]
    congr 1
    by_cases hm : m = .cont
    · have e : callMass m S = (max 1 (S.size : ℝ)) ^ 3 := if_pos hm
      rw [e, if_pos hm]
      simp [Child.res, State.dres, Res.sz]
    · have e : callMass m S = 0 := if_neg hm
      rw [e, if_neg hm]
      simp

theorem mem_children {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} :
    ∀ {s : Script α}, s.CallsExact p → ∀ c ∈ s.children, c.giant = false ∧ p .cont c.T
  | done _, _, c, hc => by simp [children] at hc
  | ask m S k, h, c, hc => by
    simp only [children, List.mem_append] at hc
    rcases hc with hc | hc
    · by_cases hm : m = .cont
      · subst hm
        rw [if_pos rfl, List.mem_singleton] at hc
        subst hc
        exact ⟨rfl, h.1⟩
      · rw [if_neg hm] at hc
        cases hc
    · exact mem_children h.2 c hc

end Script

end GI.Algorithm

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl Equiv Equiv.Perm Real

variable {Ω C C' : Type}

/-- **The invariant passes to a child** on the same positions, under a subgroup. -/
theorem DGood.child {D Nm : ℕ} {S : State Ω C} {T : State Ω C'} (h : DGood D Nm S)
    (hN : T.N = S.N) (hsz : T.size ≤ T.N) (hG : T.G ≤ S.G) (hinv : T.HierInv)
    (hr : T.rows = none) (hf : T.floor = false) (hh : T.h = 2) (hc : ∀ I ∈ T.hier, I.cap ≤ D) :
    DGood D Nm T :=
  ⟨h.finite, hN ▸ h.N_gt, hN ▸ h.N_le, hsz, hinv, hr, hf, hh, hc,
    GammaHat.of_injective (Subgroup.inclusion hG) (Subgroup.inclusion_injective hG) h.gamma⟩

section Round

variable {X : Ctx} {ks : Cst}

/-- A `Continue` call of a round is a local child with the invariant, below the round. -/
theorem localChild_of_call {q : ℕ} (hc₀ : ks.c₀ = cZero) {S : State Ω C} (hd : DGood X.D X.Nm S)
    (hg : Good P₀ .giant S) (h2 : 2 ≤ S.size) {Ω' C' : Type} {T : State Ω' C'}
    (h : AggCall P₀ S .cont T) (hr : RoundCall q .cont T) :
    Ctx.LocalChild ks S ⟨Ω', C', T, false⟩ ∧ X.Good ⟨Ω', C', T, false⟩ ∧
      MLt (measure P₀ .cont T) (measure P₀ .giant S) := by
  have hfin : Finite Ω := hd.finite
  rcases h with ⟨h, -⟩ | ⟨-, e, h⟩
  · cases h
  subst e
  replace h : ChargedCall P₀ S T := h
  obtain ⟨hgc, hlt⟩ := chargedCall_good_mlt hg h
  have hb : T.rows = none ∧ T.floor = false ∧ T.h = 2 := by
    rcases hr with ⟨h', -⟩ | ⟨-, h₁, h₂, h₃⟩
    · cases h'
    · exact ⟨h₁, h₂, h₃⟩
  have hgc' := hgc
  obtain ⟨-, hsN, hinv⟩ := hgc
  obtain ⟨hgN, -, htr, -⟩ := hg
  have hρ : T.dres.rho = S.dres.rho := by
    change (rhoNat T.hier : ℝ) = (rhoNat S.hier : ℝ)
    rw [h.hier_eq]
  have hQ : T.dres.Q = S.dres.Q := by
    change State.hierQ T.hier = State.hierQ S.hier
    rw [h.hier_eq]
  refine ⟨⟨rfl, ?_, hρ.le, hQ.le⟩, ⟨?_, hgc'⟩, hlt⟩
  · rw [hc₀]
    exact psi_drop_charged htr h2 h
  · exact hd.child h.N_eq hsN h.le hinv hb.1 hb.2.1 hb.2.2 fun I hI =>
      hd.caps I (h.hier_eq ▸ hI)

/-- The mass bound of a round, in the form of the weight: `Cm exp(am L) s³`. -/
theorem massOK_of_round {S : State Ω C} {L : GiantLabels S} (I : Aggregation P₀ S L)
    (hCm : ks.Cm = 4 * (P₀.κ.factorial : ℝ) + 11) (ham : ks.am = 2 * (P₀.κ : ℝ))
    (hs : 1 ≤ S.size) (hq1 : 1 ≤ L.q) (hqD : L.q ≤ X.D) :
    X.MassOK ks S I.script.children := by
  have hq1' : (1 : ℝ) ≤ L.q := by exact_mod_cast hq1
  have hκ := P₀_κ
  have e := Script.mass_eq_children I.script
  have hm := I.script_mass_le hs
  rw [e] at hm
  set Q : ℝ := (L.q : ℝ) ^ (2 * P₀.κ) with hQ
  have hch : ((L.q.choose P₀.κ : ℕ) : ℝ) ≤ Q := by
    have h1 : ((L.q.choose P₀.κ : ℕ) : ℝ) ≤ (L.q : ℝ) ^ P₀.κ := by
      exact_mod_cast Nat.choose_le_pow L.q P₀.κ
    exact h1.trans (pow_le_pow_right₀ hq1' (by omega))
  have hl : (L.q : ℝ) ^ I.ℓ ≤ Q := by
    refine pow_le_pow_right₀ hq1' ?_
    change P₀.κ + 1 ≤ 2 * P₀.κ
    omega
  have hf : (0 : ℝ) ≤ (P₀.κ.factorial : ℝ) := Nat.cast_nonneg _
  have hQ1 : 0 ≤ Q := by positivity
  have hsum : ((2 * L.q.choose P₀.κ * P₀.κ.factorial : ℕ) : ℝ) * 2 +
      ((4 * L.q ^ (2 * P₀.κ) : ℕ) : ℝ) * 2 + ((3 * L.q ^ I.ℓ : ℕ) : ℝ) ≤
      (4 * (P₀.κ.factorial : ℝ) + 11) * Q := by
    push_cast
    have := mul_le_mul_of_nonneg_right hch hf
    nlinarith
  have hqL : Q ≤ exp (ks.am * logD X.D) := by
    have hq0 : (0 : ℝ) < L.q := by linarith
    have hlog : Real.log L.q ≤ logD X.D := by
      have h1 : Real.log L.q ≤ Real.log ((X.D : ℝ) + 2) := Real.log_le_log hq0 (by
        have : (L.q : ℝ) ≤ X.D := by exact_mod_cast hqD
        linarith)
      unfold logD
      linarith
    have h2 : Q = exp (2 * (P₀.κ : ℝ) * Real.log L.q) := by
      have h3 := Real.exp_nat_mul (Real.log L.q) (2 * P₀.κ)
      rw [Real.exp_log hq0] at h3
      rw [hQ, ← h3]
      push_cast
      rfl
    rw [h2, ham]
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog (by positivity))
  have hsz : S.dres.sz = S.size := Res.sz_eq hs
  have hc3 : (0 : ℝ) ≤ (S.size : ℝ) ^ 3 := by positivity
  unfold Ctx.MassOK
  rw [hsz, hCm]
  have hX : 0 ≤ 4 * (P₀.κ.factorial : ℝ) + 11 := by positivity
  exact hm.trans (mul_le_mul_of_nonneg_right (hsum.trans (mul_le_mul_of_nonneg_left hqL hX)) hc3)

end Round

/-- A continuation on an overcoset lowers `Q`, and keeps the other resources. -/
theorem overChild_of_capUpdate {ks : Cst} (hδ : ks.δ = GI.Paper.cBeta P₀.β) {q : ℕ} (hq : 3 ≤ q)
    [Finite Ω] {S : State Ω C} {T : State Ω C'} (hG : T.G ≤ S.G) (hD : T.dom ⊆ S.dom)
    (h : CapUpdate P₀ S.hier q T.hier) :
    Ctx.OverChild ks S (Real.log q) ⟨Ω, C', T, false⟩ := by
  have e : P₀.β = 9 / 10 := rfl
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hρ := h.rho_eq
  rw [← rhoNat_cast, ← rhoNat_cast] at hρ
  refine ⟨rfl, size_le_of_subset hD, psi_mono hG hD, hρ.le, ?_⟩
  have := h.Q_drop (by rw [e]; norm_num) (by rw [e]; norm_num) (by rw [e]; linarith)
  rw [hδ]
  exact this

/-- The caps stay at most `D` under a cap update. -/
theorem caps_of_capUpdate {D q : ℕ} {l l' : List (Interval Ω)} (h : CapUpdate P₀ l q l')
    (hc : ∀ I ∈ l, I.cap ≤ D) : ∀ I ∈ l', I.cap ≤ D := by
  obtain ⟨i, -, -, rfl⟩ := h
  intro I hI
  rcases List.mem_or_eq_of_mem_set hI with h1 | rfl
  · exact hc I h1
  · exact (min_le_left _ _).trans (hc _ (List.getElem_mem _))

/-- A child in the enumeration: the kernel orbits lower `ψ`. -/
theorem enum_child [Finite Ω] {S : State Ω C} {T : State Ω C'} (ht : S.Transitive)
    {d : ℕ} (hd : 2 ≤ d) (hds : d ≤ S.size) (hG : T.G ≤ S.G) (hD : T.dom ⊆ S.dom)
    (h : ∀ v ∈ T.dom, d * Nat.card (orb T.G v) ≤ S.size)
    (hρ : rhoNat T.hier ≤ rhoNat S.hier) (hQ : State.hierQ T.hier ≤ State.hierQ S.hier) :
    T.dres.s ≤ S.dres.s ∧ T.dres.psi + Real.log d / 3 ≤ S.dres.psi ∧
      T.dres.rho ≤ S.dres.rho ∧ T.dres.Q ≤ S.dres.Q :=
  ⟨size_le_of_subset hD, psi_drop_kernel ht hd hds hG hD h, (Nat.cast_le (α := ℝ)).2 hρ, hQ⟩

/-- A child in the product: the split of the hierarchy lowers `ρ`. -/
theorem product_child [Finite Ω] {S : State Ω C} {T : State Ω C'} {r₁ : ℝ} (hG : T.G ≤ S.G)
    (hD : T.dom ⊆ S.dom) (hρ : State.hierRho T.hier + r₁ ≤ State.hierRho S.hier)
    (hQ : State.hierQ T.hier ≤ State.hierQ S.hier) :
    T.dres.s ≤ S.dres.s ∧ T.dres.psi ≤ S.dres.psi ∧ T.dres.rho + r₁ ≤ S.dres.rho ∧
      T.dres.Q ≤ S.dres.Q := by
  refine ⟨size_le_of_subset hD, psi_mono hG hD, ?_, hQ⟩
  change (rhoNat T.hier : ℝ) + r₁ ≤ (rhoNat S.hier : ℝ)
  rwa [rhoNat_cast, rhoNat_cast]

/-- A child of the single-factor case with an intransitive group. -/
theorem norm_child_cont [Finite Ω] {S : State Ω C} {T : State Ω C'} (ht : S.Transitive)
    (h2 : 2 ≤ S.size) (hG : T.G ≤ S.G) (hD : T.dom ⊆ S.dom)
    (h : ∀ v ∈ T.dom, 2 * Nat.card (orb T.G v) ≤ S.size)
    (hρ : State.hierRho T.hier ≤ State.hierRho S.hier)
    (hQ : State.hierQ T.hier ≤ State.hierQ S.hier) :
    T.dres.s ≤ S.dres.s ∧ T.dres.rho ≤ S.dres.rho ∧ T.dres.Q ≤ S.dres.Q ∧
      T.dres.psi + cZero ≤ S.dres.psi := by
  refine ⟨size_le_of_subset hD, ?_, hQ, psi_drop_of_orbits ht h2 hG hD fun v hv => ?_⟩
  · change (rhoNat T.hier : ℝ) ≤ (rhoNat S.hier : ℝ)
    rwa [rhoNat_cast, rhoNat_cast]
  · have := h v hv
    omega

/-- A child with no more resources: a transitive normalized group, or a part of the orbit chain. -/
theorem le_child [Finite Ω] {S : State Ω C} {T : State Ω C'} (hG : T.G ≤ S.G)
    (hD : T.dom ⊆ S.dom) (hρ : rhoNat T.hier ≤ rhoNat S.hier)
    (hQ : State.hierQ T.hier ≤ State.hierQ S.hier) : T.dres.Le S.dres :=
  ⟨size_le_of_subset hD, psi_mono hG hD, (Nat.cast_le (α := ℝ)).2 hρ, hQ⟩

end GI.Degree
