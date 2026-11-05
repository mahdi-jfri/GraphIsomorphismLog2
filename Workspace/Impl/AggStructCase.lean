module

public import Workspace.Algorithm.LabelOrbits
public import Workspace.Cited.AlgoPermGroups

@[expose] public section

/-!
# The case of the aggregation, by group orders

`aggCase H` asks whether `H = π(F_x)` has a dominant orbit `Φ` and whether `H` induces the full
alternating group on it (`GiantOn H Φ`). A program cannot list `Alt(Φ)`. It can compute two
group orders with the cited task **GroupOrder**: the order of `H` and the order of the pointwise
stabilizer `H_(Φ)` (from the cited task **PointwiseStab**). This file shows that they decide the
question:

`st_giantOn_iff`: for `Φ` invariant under `H`,
`GiantOn H Φ ↔ |Φ|! · |H_(Φ)| ≤ 2 · |H|`.

The reason: `H` acts on `Φ` with kernel `H_(Φ)`, so the image has `|H| / |H_(Φ)|` elements
(`st_card_eq`); `GiantOn H Φ` says the image contains `Alt(Φ)` (`st_giantOn_iff_le`); and a
subgroup of `Sym(Φ)` contains `Alt(Φ)` exactly when it has at least `|Φ|!/2` elements
(`st_alt_le_iff`): a subgroup of index two contains every square, hence every 3-cycle.

`st_aggCase_eq`: the case from the orbit sizes and this test.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm

/-! ### Subgroups of `Sym(α)` that contain `Alt(α)` -/

/-- **A subgroup of `Sym(α)` contains `Alt(α)` exactly when it has at least `|α|!/2`
elements.** -/
theorem st_alt_le_iff {α : Type} [Fintype α] [DecidableEq α] (K : Subgroup (Perm α)) :
    alternatingGroup α ≤ K ↔ (Fintype.card α).factorial ≤ 2 * Nat.card K := by
  have hK1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hperm : Nat.card (Perm α) = (Fintype.card α).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  constructor
  · intro h
    have hle : Nat.card (alternatingGroup α) ≤ Nat.card K := Subgroup.card_le_of_le h
    by_cases hn : 2 ≤ Fintype.card α
    · haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hc := two_mul_card_alternatingGroup (α := α)
      rw [Fintype.card_perm, ← Nat.card_eq_fintype_card] at hc
      omega
    · have : (Fintype.card α).factorial = 1 := by
        interval_cases h : Fintype.card α <;> rfl
      omega
  · intro h
    have hi := K.index_mul_card
    rw [hperm] at hi
    have hidx : K.index ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have : 3 * Nat.card K ≤ K.index * Nat.card K := Nat.mul_le_mul_right _ hlt
      omega
    have hpos : 0 < K.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rcases (show K.index = 1 ∨ K.index = 2 by omega) with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]; exact le_top
    · rw [← closure_three_cycles_eq_alternating]
      refine (Subgroup.closure_le K).2 fun c hc => ?_
      change c.IsThreeCycle at hc
      have h3 : c ^ 3 = 1 := by
        have := hc.orderOf
        rw [← this]; exact pow_orderOf_eq_one c
      have hc4 : (c ^ 2) ^ 2 = c := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, h3, one_mul]
      rw [← hc4]
      exact Subgroup.sq_mem_of_index_two h2 _

/-! ### The action on an invariant set -/

section Restrict

variable {q : ℕ} (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q))

/-- `Φ` is invariant under `H`. -/
def StInv : Prop := ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ

variable {H Φ}

theorem st_mem_iff (hinv : StInv H Φ) {h : Perm (Fin q)} (hh : h ∈ H) (x : Fin q) :
    h x ∈ Φ ↔ x ∈ Φ := by
  constructor
  · intro hx
    have := hinv h⁻¹ (H.inv_mem hh) _ hx
    simpa using this
  · exact hinv h hh x

/-- **The action of `H` on `Φ`.** -/
def stRes (hinv : StInv H Φ) : H →* Perm Φ where
  toFun h := (h : Perm (Fin q)).subtypePerm (st_mem_iff hinv h.2)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem stRes_apply (hinv : StInv H Φ) (h : H) (a : Φ) :
    (stRes hinv h a : Fin q) = (h : Perm (Fin q)) a := rfl

/-- The kernel of the action is the pointwise stabilizer of `Φ`. -/
theorem st_card_ker (hinv : StInv H Φ) :
    Nat.card (stRes hinv).ker = Nat.card (GI.Cited.pointwiseStab H Φ.toList) := by
  refine Nat.card_congr
    { toFun := fun h => ⟨h.1.1, h.1.2, fun i hi => ?_⟩
      invFun := fun h => ⟨⟨h.1, h.2.1⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · have := congrArg (fun σ : Perm Φ => (σ ⟨i, Finset.mem_toList.1 hi⟩ : Fin q)) h.2
    simpa [stRes_apply] using this
  · rw [MonoidHom.mem_ker]
    refine Equiv.ext fun ⟨a, ha⟩ => Subtype.ext ?_
    exact h.2.2 a (Finset.mem_toList.2 ha)

/-- **The image has `|H| / |H_(Φ)|` elements.** -/
theorem st_card_eq (hinv : StInv H Φ) :
    Nat.card (stRes hinv).range * Nat.card (GI.Cited.pointwiseStab H Φ.toList) =
      Nat.card H := by
  rw [← st_card_ker hinv, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (stRes hinv)).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

/-- **`GiantOn` says the image contains `Alt(Φ)`.** -/
theorem st_giantOn_iff_le (hinv : StInv H Φ) :
    GiantOn H Φ ↔ alternatingGroup Φ ≤ (stRes hinv).range := by
  classical
  constructor
  · intro hg τ hτ
    rw [mem_alternatingGroup] at hτ
    obtain ⟨h, hh, hagree⟩ := hg (ofSubtype τ) (by
      rw [mem_alternatingGroup, sign_ofSubtype, hτ]) (fun a ha => ofSubtype_apply_of_not_mem τ ha)
    refine ⟨⟨h, hh⟩, ?_⟩
    refine Equiv.ext fun ⟨a, ha⟩ => Subtype.ext ?_
    rw [stRes_apply, hagree a ha, ofSubtype_apply_of_mem τ ha]
  · intro hle σ hσ hfix
    have hmap : ∀ x, σ x ∈ Φ ↔ x ∈ Φ := by
      intro x
      constructor
      · intro hx
        by_contra hn
        have := hfix x hn
        rw [this] at hx
        exact hn hx
      · intro hx
        by_contra hn
        have h1 := hfix (σ x) hn
        have h2 : σ x = x := σ.injective h1
        rw [h2] at hn
        exact hn hx
    set τ := σ.subtypePerm hmap with hτ
    have hof : ofSubtype τ = σ := ofSubtype_subtypePerm hmap fun x hx => by
      by_contra hn; exact hx (hfix x hn)
    have hτa : τ ∈ alternatingGroup Φ := by
      rw [mem_alternatingGroup, ← sign_ofSubtype, hof]
      exact (mem_alternatingGroup).1 hσ
    obtain ⟨⟨h, hh⟩, he⟩ := hle hτa
    refine ⟨h, hh, fun a ha => ?_⟩
    have := congrArg (fun ρ : Perm Φ => (ρ ⟨a, ha⟩ : Fin q)) he
    simpa [stRes_apply, hτ] using this

/-- **The giant test by group orders**: for `Φ` invariant under `H`,
`GiantOn H Φ ↔ |Φ|! · |H_(Φ)| ≤ 2 · |H|`. -/
theorem st_giantOn_iff (hinv : StInv H Φ) :
    GiantOn H Φ ↔
      Φ.card.factorial * Nat.card (GI.Cited.pointwiseStab H Φ.toList) ≤ 2 * Nat.card H := by
  classical
  rw [st_giantOn_iff_le hinv, st_alt_le_iff, ← st_card_eq hinv]
  have hpos : 0 < Nat.card (GI.Cited.pointwiseStab H Φ.toList) := Nat.card_pos
  have hc : Fintype.card Φ = Φ.card := by simp
  rw [hc]
  constructor
  · intro h
    calc Φ.card.factorial * Nat.card (GI.Cited.pointwiseStab H Φ.toList)
        ≤ 2 * Nat.card (stRes hinv).range * Nat.card (GI.Cited.pointwiseStab H Φ.toList) :=
          Nat.mul_le_mul_right _ h
      _ = _ := by ring
  · intro h
    have : Φ.card.factorial * Nat.card (GI.Cited.pointwiseStab H Φ.toList) ≤
        (2 * Nat.card (stRes hinv).range) * Nat.card (GI.Cited.pointwiseStab H Φ.toList) := by
      rw [Nat.mul_assoc]; exact h
    exact Nat.le_of_mul_le_mul_right this hpos

end Restrict

/-! ### The case -/

section Case

variable {q : ℕ} (H : Subgroup (Perm (Fin q)))

/-- The dominant orbit is invariant. -/
theorem st_domSet_inv : StInv H (domSet H) := fun _ hh _ hb => apply_mem_domSet hh hb

open Classical in
/-- **The case from orbit sizes and two group orders.** -/
theorem st_aggCase_eq :
    aggCase H = if (domSet H).Nonempty then
        (if (domSet H).card.factorial * Nat.card (GI.Cited.pointwiseStab H (domSet H).toList) ≤
            2 * Nat.card H then .twoA else .twoB)
      else if q ≤ 2 * (suppSet H).card then .one else .three := by
  unfold aggCase
  simp only [st_giantOn_iff (st_domSet_inv H)]

end Case

end GI.Impl
