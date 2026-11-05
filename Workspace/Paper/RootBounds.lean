module

public import Workspace.Paper.TotalCost
public import Workspace.Paper.HereditaryBudget
public import Workspace.Paper.RunningTimeInequalities

@[expose] public section

/-!
# The root bounds of a fresh phase

The proof of Lemma 7.1 uses, at a phase root, "`ρ = O(log N)`, `σ = O(log(N+2))`,
`Q ≤ (log N)²`, and `h ≤ 2`" (`GI.Paper.RootBounds`). Here we prove these bounds for the
state of every fresh phase (`GI.Algorithm.State.FreshOf`):

* `ρ ≤ 2 log₂ s` by eq. `main-rho` (`GI.Paper.eq_main_rho`), since the ratios of the initial
  tower multiply to the size of an orbit, which is at most `s`
  (`GI.Algorithm.InitialTower.prod_ratio_le`);
* `Q ≤ (log s)²` by eq. `main-Q` (`GI.Paper.eq_main_Q`), since the initial bounds are
  `c_i = d_i`;
* `σ ≤ C log(s+2)` by Theorem A.9 (`GI.Paper.thm_hereditary_budget`), applied to the faithful
  image of the group on the orbit of each point of the domain (Lemma A.3,
  `GI.Paper.lem_budget_inheritance_orbit`), with the constant `C` of Theorem A.9;
* `h = 2`.

Then every run has root bounds (`GI.Algorithm.Run.rootsOK_all`), with `cσ = C`.

The only parameter hypothesis is `κ ≥ 64` (Theorem A.9 takes `κ_cert ≥ 64`; Section 7.5 fixes
`κ = κ_cert`).
-/

namespace GI.Paper

open GI.Algorithm Equiv Equiv.Perm

/-! ### `ρ` and `Q` of a tower -/

section Tower

variable {Ω : Type}

/-- Eq. `main-rho` for a hierarchy: if every ratio is at least one, then
`ρ ≤ 2 log₂ (d_1 ⋯ d_t)`. -/
theorem hierRho_le_logb (l : List (Interval Ω)) (hd : ∀ I ∈ l, 1 ≤ I.ratio) :
    State.hierRho l ≤ 2 * Real.logb 2 ((l.map Interval.ratio).prod : ℝ) := by
  have h := eq_main_rho (Finset.univ : Finset (Fin l.length)) (fun i => l[i].ratio)
    (fun i _ => hd _ (List.getElem_mem _))
  have e1 : State.hierRho l = ((∑ i : Fin l.length, GI.towerRank l[i].ratio : ℤ) : ℝ) := by
    unfold State.hierRho
    rw [← Fin.sum_univ_fun_getElem l (fun I => ((GI.towerRank I.ratio : ℤ) : ℝ))]
    push_cast
    rfl
  have e2 : (l.map Interval.ratio).prod = ∏ i : Fin l.length, l[i].ratio :=
    (Fin.prod_univ_fun_getElem l Interval.ratio).symm
  rw [e1, e2]
  exact h

/-- Eq. `main-Q` for a hierarchy: if every ratio is at least one and every bound is at most
its ratio, then `Q ≤ (log (d_1 ⋯ d_t))²`. -/
theorem hierQ_le_log_sq (l : List (Interval Ω)) (hd : ∀ I ∈ l, 1 ≤ I.ratio)
    (hc : ∀ I ∈ l, I.cap ≤ I.ratio) :
    State.hierQ l ≤ Real.log ((l.map Interval.ratio).prod : ℝ) ^ 2 := by
  have h := eq_main_Q (Finset.univ : Finset (Fin l.length)) (fun i => l[i].ratio)
    (fun i => l[i].cap) (fun i _ => hd _ (List.getElem_mem _))
    (fun i _ => hc _ (List.getElem_mem _))
  have e1 : State.hierQ l = ∑ i : Fin l.length,
      Real.log (l[i].ratio : ℝ) * Real.log (max (l[i].cap : ℝ) 2) := by
    unfold State.hierQ
    rw [← Fin.sum_univ_fun_getElem l
      (fun I => Real.log I.ratio * Real.log (max I.cap 2 : ℕ))]
    push_cast
    rfl
  have e2 : (l.map Interval.ratio).prod = ∏ i : Fin l.length, l[i].ratio :=
    (Fin.prod_univ_fun_getElem l Interval.ratio).symm
  rw [e1, e2]
  exact h

end Tower

/-! ### `σ` from Theorem A.9 -/

/-- **Theorem A.9 at a point of any finite action**: `σ(H, v) ≤ C log |V|`. By Lemma A.3,
`σ(H, v)` is the budget of the faithful image of `H` on the orbit `v^H`, which is transitive;
Theorem A.9 bounds it by `C log |v^H| ≤ C log |V|` (the term `-B` and the case `|v^H| ≤ 2` only
help). -/
theorem sigma_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : ℕ, 64 ≤ κ → ∀ (V : Type) [Fintype V] (H : Subgroup (Perm V)) (v : V),
      (GI.sigma κ v H : ℝ) ≤ C * Real.log (Fintype.card V) := by
  obtain ⟨C, B, hC, hB, h⟩ := thm_hereditary_budget
  refine ⟨C, by linarith, fun κ hκ V _ H v => ?_⟩
  classical
  -- Lemma A.3: pass to the faithful image on the orbit of `v`.
  rw [lem_budget_inheritance_orbit κ H v]
  haveI : MulAction.IsPretransitive (faithfulOrbitImage H v) (ActiveOrbit H v) :=
    ⟨fun x y => by
      obtain ⟨p, hp⟩ := faithfulOrbitImage_transitive H v x y
      exact ⟨p, hp⟩⟩
  have hA9 := h κ hκ (ActiveOrbit H v) (faithfulOrbitImage H v) inferInstance
    (activeOrbitBase H v)
  change (GI.sigma κ (activeOrbitBase H v) (faithfulOrbitImage H v) : ℝ) ≤ _ at hA9
  -- The orbit has at least one and at most `|V|` points.
  have hcard1 : 1 ≤ Fintype.card (ActiveOrbit H v) :=
    Fintype.card_pos_iff.2 ⟨activeOrbitBase H v⟩
  have hcard : Fintype.card (ActiveOrbit H v) ≤ Fintype.card V :=
    Fintype.card_le_of_injective _ Subtype.val_injective
  have hl0 : 0 ≤ Real.log (Fintype.card (ActiveOrbit H v) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hcard1)
  have hlle : Real.log (Fintype.card (ActiveOrbit H v) : ℝ) ≤ Real.log (Fintype.card V : ℝ) :=
    Real.log_le_log (by exact_mod_cast hcard1) (by exact_mod_cast hcard)
  have hA9' : (GI.sigma κ (activeOrbitBase H v) (faithfulOrbitImage H v) : ℝ) ≤
      C * Real.log (Fintype.card (ActiveOrbit H v) : ℝ) := by
    refine hA9.trans ?_
    split_ifs
    · exact mul_nonneg (by linarith) hl0
    · linarith
  exact hA9'.trans (mul_le_mul_of_nonneg_left hlle (by linarith))

/-! ### The root bounds of a fresh state -/

section Fresh

variable {P : Params} {Ω C : Type}

/-- **The root bounds of a fresh phase** (proof of Lemma 7.1: "At a phase root,
`ρ = O(log N)`, `σ = O(log(N+2))`, `Q ≤ (log N)²`, and `h ≤ 2`"). For the state `S'` of a
fresh phase on `s = |dom| > N₀` positions and the constant `C` of `sigma_le_log`, the domain is
finite and `S'` satisfies `RootBounds C N` with `N = s`. -/
theorem freshOf_rootBounds {cσ : ℝ}
    (hσ : ∀ (V : Type) [Fintype V] (H : Subgroup (Perm V)) (v : V),
      (GI.sigma P.κ v H : ℝ) ≤ cσ * Real.log (Fintype.card V))
    (hcσ : 0 ≤ cσ) {S : State Ω C} {S' : State S.dom C} (hs : P.N₀ < S.size)
    (hS' : S.FreshOf S') : Finite S.dom ∧ RootBounds cσ S'.N (S'.res P.κ) := by
  classical
  -- The domain is finite and nonempty, since `|dom| > N₀ ≥ 0`.
  have hpos : 0 < Nat.card S.dom := by change 0 < S.size; omega
  haveI hfin : Finite S.dom := (Nat.card_pos_iff.1 hpos).2
  letI : Fintype S.dom := Fintype.ofFinite _
  refine ⟨hfin, ?_⟩
  have hsz : S'.size = S.size := hS'.size_eq
  have hcardV : (Fintype.card S.dom : ℝ) = S.size := by
    rw [State.size, Nat.card_eq_fintype_card]
  have hs1 : (1 : ℝ) ≤ S.size := by exact_mod_cast (show 1 ≤ S.size by omega)
  -- The tower: ratios at least one, bounds equal to the ratios, product at most `s`.
  have htw := hS'.tower
  have hd := htw.one_le_ratio
  have hc : ∀ I ∈ S'.hier, I.cap ≤ I.ratio := fun I hI => (htw.2 I hI).le
  have hprod : (S'.hier.map Interval.ratio).prod ≤ S.size := by
    have := htw.prod_ratio_le S'.dom_inv
    rwa [← State.size, hsz] at this
  have hprod1 : 1 ≤ (S'.hier.map Interval.ratio).prod :=
    Nat.one_le_iff_ne_zero.2 fun h0 => by
      rw [List.prod_eq_zero_iff] at h0
      obtain ⟨I, hI, hI0⟩ := List.mem_map.1 h0
      have := hd I hI
      omega
  have hprodR : ((S'.hier.map Interval.ratio).prod : ℝ) ≤ S.size := by exact_mod_cast hprod
  have hprod1R : (1 : ℝ) ≤ (S'.hier.map Interval.ratio).prod := by exact_mod_cast hprod1
  refine
    { one_le_s := by change 1 ≤ S'.size; omega
      s_le_N := by change S'.size ≤ S'.N; rw [hsz, hS'.N_eq]
      ρ_nonneg := S'.rho_nonneg
      ρ_le := ?_
      σ_nonneg := Nat.cast_nonneg _
      σ_le := ?_
      Q_nonneg := S'.capMoment_nonneg
      Q_le := ?_
      h_le := by change S'.h ≤ 2; rw [hS'.h_eq] }
  · -- eq. `main-rho`
    change State.hierRho S'.hier ≤ 2 * Real.logb 2 (S'.size : ℝ)
    refine (hierRho_le_logb S'.hier hd).trans ?_
    rw [hsz]
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) hprodR
    linarith
  · -- Theorem A.9 on the faithful image `G|_dom`
    change ((S'.sigma P.κ : ℕ) : ℝ) ≤ cσ * Real.log ((S'.size : ℝ) + 2)
    rw [hsz]
    have hlog : Real.log (S.size : ℝ) ≤ Real.log ((S.size : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hb : ∀ v ∈ S'.dom, GI.sigma P.κ v S'.G ≤ ⌊cσ * Real.log (S.size : ℝ)⌋₊ := by
      intro v _
      apply Nat.le_floor
      have := hσ S.dom S'.G v
      rwa [hcardV] at this
    have h1 := State.sigma_le_of_forall hb
    have h2 : ((S'.sigma P.κ : ℕ) : ℝ) ≤ cσ * Real.log (S.size : ℝ) :=
      (Nat.cast_le.2 h1).trans (Nat.floor_le (mul_nonneg hcσ (Real.log_nonneg hs1)))
    exact h2.trans (mul_le_mul_of_nonneg_left hlog hcσ)
  · -- eq. `main-Q`
    change State.hierQ S'.hier ≤ Real.log (S'.size : ℝ) ^ 2
    refine (hierQ_le_log_sq S'.hier hd hc).trans ?_
    rw [hsz]
    have h0 : 0 ≤ Real.log ((S'.hier.map Interval.ratio).prod : ℝ) := Real.log_nonneg hprod1R
    exact pow_le_pow_left₀ h0 (Real.log_le_log (by linarith) hprodR) 2

end Fresh

end GI.Paper

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {P : Params}

/-- **Every run has root bounds** once every fresh state does: `Run.RootsOK` only asks for the
root bounds at the `fresh` nodes. -/
theorem Run.rootsOK_of {cσ : ℝ}
    (hroot : ∀ {Ω C : Type} (S : State Ω C) (S' : State S.dom C), P.N₀ < S.size →
      S.FreshOf S' → Finite S.dom ∧ GI.Paper.RootBounds cσ S'.N (S'.res P.κ))
    {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) :
    r.RootsOK cσ :=
  Run.rec (motive_1 := fun _ {_ _} _ _ _ r => r.RootsOK cσ)
    (motive_2 := fun _ _ e => e.RootsOK cσ)
    (direct := fun _ _ => trivial)
    (fresh := @fun _ _ S S' _ hs hS' _ ih =>
      ⟨(hroot S S' hs hS').1, (hroot S S' hs hS').2, ih⟩)
    (threshold := fun _ _ ih => ih)
    (orbitStop := fun _ _ _ _ _ _ _ _ ih => ih)
    (orbitChain := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => ⟨ih₁, ih₂⟩)
    (floorReset := fun _ _ _ _ _ _ _ _ _ _ ih => ih)
    (dispatch := fun _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (normalize := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (rowTerminal := fun _ _ _ _ _ _ ih => ih)
    (rowColumns := fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (aggregate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihe ih => ⟨ihe, ih⟩)
    (done := fun _ => trivial)
    (ask := fun _ _ ihr ihe => ⟨ihr, ihe⟩)
    r

/-- **Every run has root bounds** (`Run.RootsOK`), with the constant `cσ ≥ 0` of Theorem A.9,
for `κ ≥ 64`. -/
theorem Run.rootsOK_all (hκ : 64 ≤ P.κ) :
    ∃ cσ : ℝ, 0 ≤ cσ ∧ ∀ {m : Mode} {Ω C : Type} {S : State Ω C}
        {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
      (r : Run P m S L A), r.RootsOK cσ := by
  obtain ⟨cσ, hcσ, hσ⟩ := GI.Paper.sigma_le_log
  exact ⟨cσ, hcσ, fun r => Run.rootsOK_of (fun S S' hs hS' =>
    GI.Paper.freshOf_rootBounds (hσ P.κ hκ) hcσ hs hS') r⟩

end GI.Algorithm
