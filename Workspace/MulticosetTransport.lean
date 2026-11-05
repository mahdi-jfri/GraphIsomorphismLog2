module

public import Workspace.MulticosetSolvable
public import Workspace.MulticosetSupplement
public import Workspace.Cited.DixonDerivedLength
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Theorem A.20 at top level: recursion and the derived-length bound via Lemma A.19

`solvableTransport H N X Y` is the procedure of the proof of Theorem A.20:
the recursion `proc` runs on `(H, N)` with fuel the derived length of the acting quotient
`H/N` (`quotLength H N`).

By Lemma A.19 (`exists_solvable_supplement_descent`), `H` has a solvable subgroup `S ≤ H`
with `S N = H`, so `S` surjects onto `H/N`. The count of calls is at most `(4M³ + 2)^ℓ`,
and Dixon's bound on `S` gives `ℓ ≤ 5 log₃ b + 1` (`GI.Cited.DixonDerivedLength`), so the
count is `exp(O(log(b+M+2) log(b+2)))`.
-/

namespace GI.Multicoset

open Classical

universe u

variable {G : Type u} [Group G]

/-! ### Solvability of `H/N` in the cover -/

theorem normal_of_normalizes {H N : Subgroup G} (hn : Normalizes H N) :
    (N.subgroupOf H).Normal :=
  ⟨fun n hn' g => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simpa using hn g g.2 n hn'⟩

theorem normalizes_of_normal {H N : Subgroup G} (hNH : N ≤ H) [h : (N.subgroupOf H).Normal] :
    Normalizes H N := by
  intro g hg n hn
  have := h.conj_mem ⟨n, hNH hn⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

/-- The derived series of `H/N` lies below the image of the series `relDerived H N`. -/
theorem derivedSeries_quot_le {H N : Subgroup G} [(N.subgroupOf H).Normal] :
    ∀ i, derivedSeries (H ⧸ N.subgroupOf H) i ≤
      ((relDerived H N i).comap H.subtype).map (QuotientGroup.mk' _)
  | 0 => by
    rw [derivedSeries_zero, relDerived_zero]
    show ⊤ ≤ Subgroup.map _ (H.subgroupOf H)
    rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  | i + 1 => by
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono (derivedSeries_quot_le i) (derivedSeries_quot_le i)).trans ?_
    rw [← Subgroup.map_commutator]
    refine Subgroup.map_mono ((comap_commutator_le _ _).trans (Subgroup.comap_mono ?_))
    rw [relDerived_succ]; exact le_sup_left

/-- "`H/N` is solvable" in the cover: some `relDerived H N ℓ ≤ N`. -/
theorem isSolvable_quot_of_relDerived {H N : Subgroup G} [(N.subgroupOf H).Normal] {ℓ : ℕ}
    (h : relDerived H N ℓ ≤ N) : Group.IsSolvable (H ⧸ N.subgroupOf H) := by
  refine ⟨⟨ℓ, eq_bot_iff.mpr ((derivedSeries_quot_le ℓ).trans ?_)⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mpr (h hx)

theorem exists_relDerived_of_isSolvable {H N : Subgroup G} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] [Group.IsSolvable (H ⧸ N.subgroupOf H)] :
    ∃ ℓ, relDerived H N ℓ ≤ N :=
  ⟨_, relDerived_le_of_derivedSeries hNH (derivedSeries_derivedLength _)⟩

/-! ### The procedure -/

/-- The derived length of the acting quotient `H/N`, computed in the cover. -/
noncomputable def quotLength (H N : Subgroup G) : ℕ :=
  if h : ∃ ℓ, relDerived H N ℓ ≤ N then Nat.find h else 0

theorem quotLength_spec {H N : Subgroup G} (h : ∃ ℓ, relDerived H N ℓ ≤ N) :
    relDerived H N (quotLength H N) ≤ N := by
  rw [quotLength, dif_pos h]; exact Nat.find_spec h

theorem quotLength_le {H N : Subgroup G} {k : ℕ} (h : relDerived H N k ≤ N) :
    quotLength H N ≤ k := by
  rw [quotLength, dif_pos ⟨k, h⟩]; exact Nat.find_min' _ h

/-- The solvable supplement of Lemma A.19 (any `S ≤ H`, solvable, with `S N = H`). -/
noncomputable def supplement (H N : Subgroup G) : Subgroup G :=
  if h : ∃ S : Subgroup G, S ≤ H ∧ Group.IsSolvable S ∧ S ⊔ N = H then h.choose else H

/-- **The procedure of Theorem A.20.** Run the recursion on `(H, N)` with fuel the derived
length of `H/N`. -/
noncomputable def solvableTransport {Ω : Type u} [RAct G Ω] (H N : Subgroup G)
    (X Y : Multiset Ω) : Out G :=
  proc (quotLength H N) H N X Y

theorem supplement_spec [Finite G] {H N : Subgroup G} (hNH : N ≤ H) (hn : Normalizes H N)
    (hsolv : ∃ ℓ, relDerived H N ℓ ≤ N) :
    supplement H N ≤ H ∧ Group.IsSolvable (supplement H N) ∧ supplement H N ⊔ N = H := by
  haveI := normal_of_normalizes hn
  obtain ⟨ℓ, hℓ⟩ := hsolv
  haveI := isSolvable_quot_of_relDerived hℓ
  have hex := exists_solvable_supplement_descent hNH hn
  rw [supplement, dif_pos hex]
  exact hex.choose_spec

/-- **Correctness of Theorem A.20's procedure**: it returns the full transporter
`Iso_H(X, Y)`, for a kernel `N ◁ H` with `H/N` solvable fixing every listed object. -/
theorem solvableTransport_set [Finite G] {Ω : Type u} [RAct G Ω] {H N : Subgroup G}
    (hNH : N ≤ H) (hn : Normalizes H N) (hsolv : ∃ ℓ, relDerived H N ℓ ≤ N)
    {X Y : Multiset Ω} (hX : Fixes N X) (hY : Fixes N Y) :
    (solvableTransport H N X Y).set = Iso H X Y :=
  proc_set (quotLength H N) H N X Y hNH hn (quotLength_spec hsolv) hX hY

/-! ### The count -/

/-- Derived series of a solvable group of permutations of any finite set, from Dixon's bound
for `Fin n`. -/
theorem dixon_perm (dixon : GI.Cited.DixonDerivedLength) {B : Type u} [Fintype B]
    [DecidableEq B] (S : Subgroup (Equiv.Perm B)) [Group.IsSolvable S] (k : ℕ)
    (hk : 5 * Real.logb 3 (Fintype.card B) ≤ k) : derivedSeries S k = ⊥ := by
  let e := (Fintype.equivFin B).permCongrHom
  let S' := S.map e.toMonoidHom
  let f : S ≃* S' := S.equivMapOfInjective e.toMonoidHom e.injective
  have hS' : Group.IsSolvable S' := Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
  have h' := dixon (Fintype.card B) S' hS' k hk
  have := map_derivedSeries_eq (f := f.symm.toMonoidHom) f.symm.surjective k
  rw [h', Subgroup.map_bot] at this
  exact this.symm

theorem relDerived_le_of_supplement {H N S : Subgroup G} (hNH : N ≤ H) (hSH : S ≤ H)
    (hn : Normalizes H N) (hSN : S ⊔ N = H) {k : ℕ} (h : derivedSeries S k = ⊥) :
    relDerived H N k ≤ N := by
  haveI := normal_of_normalizes hn
  apply relDerived_le_of_derivedSeries hNH
  let ψ : S →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion hSH)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) q
    obtain ⟨n, hnN, s, hsS, rfl⟩ := exists_kernel_mul_of_sup_eq (hn.mono hSH) hSN x hx
    refine ⟨⟨s, hsS⟩, ?_⟩
    change QuotientGroup.mk' (N.subgroupOf H) ⟨s, hSH hsS⟩ =
      QuotientGroup.mk' (N.subgroupOf H) ⟨n * s, hx⟩
    have hmul : (⟨n * s, hx⟩ : H) = ⟨n, hNH hnN⟩ * ⟨s, hSH hsS⟩ := rfl
    have hn1 : QuotientGroup.mk' (N.subgroupOf H) ⟨n, hNH hnN⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hnN
    rw [hmul, map_mul, hn1, one_mul]
  rw [← map_derivedSeries_eq hψ k, h, Subgroup.map_bot]

/-- The recursion depth: `ℓ ≤ 5 log₃ b + 1`, from Dixon's bound for the solvable supplement. -/
theorem solvableTransport_depth {B : Type u} [Fintype B] [DecidableEq B]
    (dixon : GI.Cited.DixonDerivedLength) {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H)
    (hn : Normalizes H N) (hsolv : ∃ ℓ, relDerived H N ℓ ≤ N) :
    (quotLength H N : ℝ) ≤
      5 * Real.logb 3 (Fintype.card B) + 1 := by
  obtain ⟨hSH, hS, hSN⟩ := supplement_spec hNH hn hsolv
  set k := ⌈5 * Real.logb 3 (Fintype.card B)⌉₊
  have hk := dixon_perm dixon (supplement H N) k (Nat.le_ceil _)
  have hle := quotLength_le (relDerived_le_of_supplement hNH hSH hn hSN hk)
  calc (quotLength H N : ℝ) ≤ k := by exact_mod_cast hle
    _ ≤ _ := (Nat.ceil_lt_add_one (by
        have h0 : 0 ≤ Real.logb 3 (Fintype.card B : ℝ) := by
          rcases Nat.eq_zero_or_pos (Fintype.card B) with h | h
          · simp [h]
          · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)
        positivity)).le

end GI.Multicoset
