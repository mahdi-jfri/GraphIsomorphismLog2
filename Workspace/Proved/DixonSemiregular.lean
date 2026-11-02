import Workspace.Proved.SolvDerived

/-!
# Abelian normal subgroups of a group transitive on the nonidentity elements

Let `H` act faithfully by automorphisms on a commutative group `V`, transitively on `V \ {1}`.
Then every commutative normal subgroup `A` of `H` acts semiregularly on `V \ {1}`
(`GI.Proved.dixon_semiregular`).

*Proof.* For `v ∈ V` let `T(v) = A ∩ H_v`. Since `T(h v) = h T(v) h⁻¹`, all `T(v)` with `v ≠ 1`
have the same size, so `T(v) ≤ T(w)` forces `T(v) = T(w)`. Suppose `x ∈ T(v₁)`, `x ≠ 1`. As the
action is faithful, some `v₂` has `x v₂ ≠ v₂`, so `T(v₁) ≠ T(v₂)`. Let `u = v₁ v₂`, which is not
`1`. For `y ∈ T(u)` put `z = (y v₁) v₁⁻¹ = v₂ (y v₂)⁻¹`. As `A` is commutative, `T(v₁)` and
`T(v₂)` fix `z`. If `z ≠ 1` this gives `T(v₁) = T(z) = T(v₂)`, which is false. So `z = 1`, and
`y` fixes `v₁` and `v₂`. Hence `T(u) ≤ T(v₁)` and `T(u) ≤ T(v₂)`, so `T(v₁) = T(u) = T(v₂)`, a
contradiction.

We also prove the arithmetic step `dixon_solvL_add_three`: if `1 ≤ m` and `2 m ≤ n`, then
`solvL m + 3 ≤ solvL n`.
-/

namespace GI.Proved

open MulAction

/-- If `1 ≤ m` and `2 m ≤ n`, then `solvL m + 3 ≤ solvL n`, since
`3^{solvL m + 3} ≤ 27 m^5 ≤ (2 m)^5 ≤ n^5`. -/
theorem dixon_solvL_add_three {m n : ℕ} (hm : 1 ≤ m) (h : 2 * m ≤ n) :
    solvL m + 3 ≤ solvL n := by
  unfold solvL
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 3 ^ (Nat.log 3 (m ^ 5) + 3) = 3 ^ Nat.log 3 (m ^ 5) * 27 := by rw [pow_add]; norm_num
    _ ≤ m ^ 5 * 27 := Nat.mul_le_mul_right _ (Nat.pow_log_le_self 3 (by positivity))
    _ ≤ m ^ 5 * 32 := Nat.mul_le_mul_left _ (by norm_num)
    _ = (2 * m) ^ 5 := by ring
    _ ≤ n ^ 5 := Nat.pow_le_pow_left h 5

variable {H V : Type*} [Group H] [CommGroup V] [MulDistribMulAction H V] [FaithfulSMul H V]

/-- The stabilizer of `v` in `A`. -/
def dixonT (A : Subgroup H) (v : V) : Subgroup H := A ⊓ stabilizer H v

omit [FaithfulSMul H V] in
theorem mem_dixonT {A : Subgroup H} {v : V} {y : H} : y ∈ dixonT A v ↔ y ∈ A ∧ y • v = v := by
  rw [dixonT, Subgroup.mem_inf, mem_stabilizer_iff]

omit [FaithfulSMul H V] in
theorem dixonT_smul (A : Subgroup H) [A.Normal] (h : H) (v : V) :
    dixonT A (h • v) = (dixonT A v).map (MulAut.conj h).toMonoidHom := by
  ext y
  rw [mem_dixonT, Subgroup.mem_map]
  constructor
  · rintro ⟨hyA, hy⟩
    refine ⟨h⁻¹ * y * h, mem_dixonT.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa using (inferInstance : A.Normal).conj_mem y hyA h⁻¹
    · rw [mul_smul, mul_smul, hy, inv_smul_smul]
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxA, hxv⟩ := mem_dixonT.mp hx
    refine ⟨(inferInstance : A.Normal).conj_mem x hxA h, ?_⟩
    change (h * x * h⁻¹) • h • v = h • v
    rw [mul_smul, mul_smul, inv_smul_smul, hxv]

/-- **Semiregularity.** If `H` is transitive on `V \ {1}`, a commutative normal subgroup acts
semiregularly on `V \ {1}`. -/
theorem dixon_semiregular [Finite H]
    (htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ h : H, h • v = w)
    (A : Subgroup H) [A.Normal] (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {x : H} (hx : x ∈ A) {v : V} (hv : v ≠ 1) (hxv : x • v = v) : x = 1 := by
  have hcard : ∀ v w : V, v ≠ 1 → w ≠ 1 → Nat.card (dixonT A v) = Nat.card (dixonT A w) := by
    intro v w hv hw
    obtain ⟨h, rfl⟩ := htr v w hv hw
    rw [dixonT_smul]
    exact (Subgroup.card_map_of_injective (MulAut.conj h).injective).symm
  have heq : ∀ v w : V, v ≠ 1 → w ≠ 1 → dixonT A v ≤ dixonT A w → dixonT A v = dixonT A w :=
    fun v w hv hw hle => Subgroup.eq_of_le_of_card_ge hle (hcard v w hv hw).ge
  by_contra hx1
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : V, x • v₂ ≠ v₂ := by
    by_contra hall
    push Not at hall
    exact hx1 (eq_of_smul_eq_smul (α := V) fun w => by rw [one_smul]; exact hall w)
  have hv₂1 : v₂ ≠ 1 := by
    rintro rfl
    exact hv₂ (smul_one x)
  have hne : dixonT A v ≠ dixonT A v₂ := by
    intro h
    have : x ∈ dixonT A v₂ := h ▸ mem_dixonT.mpr ⟨hx, hxv⟩
    exact hv₂ (mem_dixonT.mp this).2
  have key : ∀ z : V, dixonT A v ≤ dixonT A z → dixonT A v₂ ≤ dixonT A z → z = 1 := by
    intro z h1 h2
    by_contra hz
    exact hne ((heq v z hv hz h1).trans (heq v₂ z hv₂1 hz h2).symm)
  have hu : v * v₂ ≠ 1 := by
    intro h
    have h' : v₂ = v⁻¹ := eq_inv_of_mul_eq_one_right h
    apply hv₂
    rw [h', smul_inv', hxv]
  have hfix : ∀ y ∈ dixonT A (v * v₂), y • v = v ∧ y • v₂ = v₂ := by
    intro y hy
    obtain ⟨hyA, hyu⟩ := mem_dixonT.mp hy
    rw [smul_mul'] at hyu
    have hz2 : (y • v) * v⁻¹ = v₂ * (y • v₂)⁻¹ := by
      calc (y • v) * v⁻¹ = (y • v * y • v₂) * (y • v₂)⁻¹ * v⁻¹ := by rw [mul_inv_cancel_right]
        _ = v₂ * (y • v₂)⁻¹ := by
          rw [hyu, mul_right_comm, mul_comm v v₂, mul_inv_cancel_right]
    have hz : (y • v) * v⁻¹ = 1 := by
      apply key
      · intro r hr
        obtain ⟨hrA, hrv⟩ := mem_dixonT.mp hr
        refine mem_dixonT.mpr ⟨hrA, ?_⟩
        rw [smul_mul', smul_inv', hrv, ← mul_smul, hA r hrA y hyA, mul_smul, hrv]
      · intro r hr
        obtain ⟨hrA, hrv⟩ := mem_dixonT.mp hr
        refine mem_dixonT.mpr ⟨hrA, ?_⟩
        rw [hz2, smul_mul', smul_inv', hrv, ← mul_smul, hA r hrA y hyA, mul_smul, hrv]
    have h1 : y • v = v := mul_inv_eq_one.mp hz
    refine ⟨h1, ?_⟩
    rw [h1] at hyu
    exact mul_left_cancel hyu
  have hle1 : dixonT A (v * v₂) ≤ dixonT A v := fun y hy =>
    mem_dixonT.mpr ⟨(mem_dixonT.mp hy).1, (hfix y hy).1⟩
  have hle2 : dixonT A (v * v₂) ≤ dixonT A v₂ := fun y hy =>
    mem_dixonT.mpr ⟨(mem_dixonT.mp hy).1, (hfix y hy).2⟩
  exact hne ((heq _ _ hu hv hle1).symm.trans (heq _ _ hu hv₂1 hle2))

end GI.Proved
