import Workspace.MulticosetModel
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The derived series of an acting quotient `H/N`, inside the cover

The recursion of Theorem A.20 inducts on the derived length of the acting quotient
`H/N`. We keep the cover: the derived series of `H/N` is described by the subgroups
`relDerived H N i` of `G`, with `relDerived H N 0 = H` and
`relDerived H N (i+1) = [D_i, D_i] N`. Their images in `H/N` are the derived series of
`H/N`. When `relDerived H N (ℓ+1) ≤ N`, the subgroup `A = relDerived H N ℓ` is the
paper's "last nontrivial derived subgroup" (or `N`, if the derived length is smaller):
it is normalized by `H` and `A/N` is abelian.
-/

namespace GI.Multicoset

variable {G : Type*} [Group G]

open scoped commutatorElement

/-- The preimage in `H` of the `i`-th derived subgroup of `H/N`. -/
def relDerived (H N : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | i + 1 => ⁅relDerived H N i, relDerived H N i⁆ ⊔ N

@[simp] theorem relDerived_zero (H N : Subgroup G) : relDerived H N 0 = H := rfl

theorem relDerived_succ (H N : Subgroup G) (i : ℕ) :
    relDerived H N (i + 1) = ⁅relDerived H N i, relDerived H N i⁆ ⊔ N := rfl

theorem commutator_self_le (D : Subgroup G) : ⁅D, D⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)

theorem relDerived_succ_le {H N : Subgroup G} (hNH : N ≤ H) (i : ℕ) :
    relDerived H N (i + 1) ≤ relDerived H N i := by
  induction i with
  | zero => exact sup_le (commutator_self_le H) hNH
  | succ i ih =>
    exact sup_le (commutator_self_le _) le_sup_right

theorem relDerived_anti {H N : Subgroup G} (hNH : N ≤ H) {i j : ℕ} (hij : i ≤ j) :
    relDerived H N j ≤ relDerived H N i := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact (relDerived_succ_le hNH _).trans ih

theorem relDerived_le {H N : Subgroup G} (hNH : N ≤ H) (i : ℕ) : relDerived H N i ≤ H :=
  relDerived_anti hNH (Nat.zero_le i)

theorem le_relDerived {H N : Subgroup G} (hNH : N ≤ H) : ∀ i, N ≤ relDerived H N i
  | 0 => hNH
  | _ + 1 => le_sup_right

/-! ### Normality -/

theorem normalizes_iff_map {H K : Subgroup G} :
    Normalizes H K ↔ ∀ h ∈ H, K.map (MulAut.conj h).toMonoidHom ≤ K := by
  constructor
  · rintro hn h hh _ ⟨k, hk, rfl⟩
    exact hn h hh k hk
  · intro hm h hh k hk
    exact hm h hh ⟨k, hk, rfl⟩

theorem Normalizes.commutator {H A B : Subgroup G} (hA : Normalizes H A) (hB : Normalizes H B) :
    Normalizes H ⁅A, B⁆ := by
  rw [normalizes_iff_map] at hA hB ⊢
  intro h hh
  rw [Subgroup.map_commutator]
  exact Subgroup.commutator_mono (hA h hh) (hB h hh)

theorem Normalizes.sup {H A B : Subgroup G} (hA : Normalizes H A) (hB : Normalizes H B) :
    Normalizes H (A ⊔ B) := by
  rw [normalizes_iff_map] at hA hB ⊢
  intro h hh
  rw [Subgroup.map_sup]
  exact sup_le_sup (hA h hh) (hB h hh)

theorem relDerived_normalizes {H N : Subgroup G} (hn : Normalizes H N) :
    ∀ i, Normalizes H (relDerived H N i)
  | 0 => normalizes_self H
  | i + 1 => ((relDerived_normalizes hn i).commutator (relDerived_normalizes hn i)).sup hn

/-- `A/N` is abelian for `A = relDerived H N ℓ`, once `relDerived H N (ℓ+1) ≤ N`:
every commutator of two elements of `A` lies in `N`. -/
theorem relDerived_commutator_mem {H N : Subgroup G} {ℓ : ℕ}
    (hℓ : relDerived H N (ℓ + 1) ≤ N) {a b : G} (ha : a ∈ relDerived H N ℓ)
    (hb : b ∈ relDerived H N ℓ) : ⁅a, b⁆ ∈ N :=
  hℓ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hb))

/-- The series is monotone in the group and in the kernel, as long as the new kernel stays
inside the old series. This gives "every such call has quotient derived length at most
`ℓ - 1`" for both kinds of recursive call. -/
theorem relDerived_mono {H N K M : Subgroup G} (hNH : N ≤ H) (hKH : K ≤ H) {ℓ : ℕ}
    (hM : M ≤ relDerived H N ℓ) : ∀ i, i ≤ ℓ → relDerived K M i ≤ relDerived H N i
  | 0, _ => hKH
  | i + 1, hi => by
    have ih := relDerived_mono hNH hKH hM i (by omega)
    rw [relDerived_succ]
    refine sup_le ((Subgroup.commutator_mono ih ih).trans
      (by rw [relDerived_succ]; exact le_sup_left)) ?_
    exact hM.trans (relDerived_anti hNH hi)

/-! ### Comparison with the derived series of the quotient group `H/N` -/

open Classical in
/-- The derived length of a solvable group: the least `n` with `G^{(n)} = 1`. -/
noncomputable def derivedLength (Q : Type*) [Group Q] [h : IsSolvable Q] : ℕ :=
  Nat.find h.solvable

open Classical in
theorem derivedSeries_derivedLength (Q : Type*) [Group Q] [IsSolvable Q] :
    derivedSeries Q (derivedLength Q) = ⊥ :=
  Nat.find_spec (IsSolvable.solvable (G := Q))

open Classical in
theorem derivedLength_le_of_eq_bot {Q : Type*} [Group Q] [IsSolvable Q] {n : ℕ}
    (h : derivedSeries Q n = ⊥) : derivedLength Q ≤ n :=
  Nat.find_min' (IsSolvable.solvable (G := Q)) h

theorem comap_commutator_le {Q R : Type*} [Group Q] [Group R] (f : Q →* R) (A : Subgroup R) :
    ⁅A.comap f, A.comap f⁆ ≤ (⁅A, A⁆).comap f := by
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
  exact Subgroup.commutator_mono (Subgroup.map_comap_le f A) (Subgroup.map_comap_le f A)

/-- The subgroups `relDerived H N i` lie in the preimages of the derived subgroups of `H/N`. -/
theorem relDerived_le_preimage {H N : Subgroup G} (hNH : N ≤ H) [(N.subgroupOf H).Normal] :
    ∀ i, relDerived H N i ≤
      ((derivedSeries (H ⧸ N.subgroupOf H) i).comap (QuotientGroup.mk' _)).map H.subtype
  | 0 => by
    rw [derivedSeries_zero, Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact le_rfl
  | i + 1 => by
    have ih := relDerived_le_preimage hNH i
    rw [relDerived_succ]
    refine sup_le ?_ ?_
    · refine (Subgroup.commutator_mono ih ih).trans ?_
      rw [← Subgroup.map_commutator, derivedSeries_succ]
      exact Subgroup.map_mono (comap_commutator_le _ _)
    · intro n hn
      refine ⟨⟨n, hNH hn⟩, ?_, rfl⟩
      change (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hn⟩ ∈
        derivedSeries (H ⧸ N.subgroupOf H) (i + 1)
      have : (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hn⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hn
      rw [this]
      exact Subgroup.one_mem _

/-- If `H/N` has derived length at most `ℓ`, then `relDerived H N ℓ ≤ N`. -/
theorem relDerived_le_of_derivedSeries {H N : Subgroup G} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    {ℓ : ℕ} (h : derivedSeries (H ⧸ N.subgroupOf H) ℓ = ⊥) : relDerived H N ℓ ≤ N := by
  refine (relDerived_le_preimage hNH ℓ).trans ?_
  rw [h, MonoidHom.comap_bot, QuotientGroup.ker_mk', Subgroup.subgroupOf_map_subtype]
  exact inf_le_left

end GI.Multicoset
