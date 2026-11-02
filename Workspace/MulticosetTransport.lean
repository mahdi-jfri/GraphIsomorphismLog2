import Workspace.MulticosetSolvable
import Workspace.MulticosetSupplement
import Workspace.Cited.DixonDerivedLength
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Theorem A.20 at top level: supplement, recursion, final lift, and the bound

`solvableTransport H N X Y` is the procedure of the proof of Theorem A.20:
"Apply Lemma A.19, replace `(H, N)` by `(S, S ∩ N)`, and remember the old kernel for the
final lift". The recursion `proc` runs with fuel the derived length of the acting quotient
`S/(S ∩ N)` (`quotLength`), and the answer is multiplied by `N` ("adjoining `N` recovers the
full transporter in `H`").

The count of calls is at most `(4M³ + 2)^ℓ`, and Dixon's bound gives `ℓ ≤ 5 log₃ b + 1`
(`GI.Cited.DixonDerivedLength`), so the count is `exp(O(log(b+M+2) log(b+2)))`.
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
    (h : relDerived H N ℓ ≤ N) : IsSolvable (H ⧸ N.subgroupOf H) := by
  refine ⟨⟨ℓ, eq_bot_iff.mpr ((derivedSeries_quot_le ℓ).trans ?_)⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mpr (h hx)

theorem exists_relDerived_of_isSolvable {H N : Subgroup G} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] [IsSolvable (H ⧸ N.subgroupOf H)] :
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
  if h : ∃ S : Subgroup G, S ≤ H ∧ IsSolvable S ∧ S ⊔ N = H then h.choose else H

/-- **The procedure of Theorem A.20.** Restrict to the solvable supplement `S`, run the
recursion with kernel `S ∩ N`, and adjoin `N`. -/
noncomputable def solvableTransport {Ω : Type u} [RAct G Ω] (H N : Subgroup G)
    (X Y : Multiset Ω) : Out G :=
  let S := supplement H N
  let r := proc (quotLength S (S ⊓ N)) S (S ⊓ N) X Y
  ⟨{h | ∃ n ∈ N, ∃ s ∈ r.set, h = n * s}, r.calls⟩

theorem supplement_spec [Finite G] {H N : Subgroup G} (hNH : N ≤ H) (hn : Normalizes H N)
    (hsolv : ∃ ℓ, relDerived H N ℓ ≤ N) :
    supplement H N ≤ H ∧ IsSolvable (supplement H N) ∧ supplement H N ⊔ N = H := by
  haveI := normal_of_normalizes hn
  obtain ⟨ℓ, hℓ⟩ := hsolv
  haveI := isSolvable_quot_of_relDerived hℓ
  have hex := exists_solvable_supplement_descent hNH hn
  rw [supplement, dif_pos hex]
  exact hex.choose_spec

/-- The recursion on `(S, S ∩ N)` is set up correctly. -/
theorem supplement_relDerived [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hn : Normalizes H N) (hsolv : ∃ ℓ, relDerived H N ℓ ≤ N) :
    relDerived (supplement H N) (supplement H N ⊓ N)
      (quotLength (supplement H N) (supplement H N ⊓ N)) ≤ supplement H N ⊓ N := by
  obtain ⟨hSH, _, _⟩ := supplement_spec hNH hn hsolv
  apply quotLength_spec
  obtain ⟨ℓ, hℓ⟩ := hsolv
  refine ⟨ℓ, le_inf (relDerived_le inf_le_left ℓ) ?_⟩
  exact (relDerived_mono hNH hSH (inf_le_right.trans (le_relDerived hNH ℓ)) ℓ le_rfl).trans hℓ

/-- **Correctness of Theorem A.20's procedure**: it returns the full transporter
`Iso_H(X, Y)`, for a kernel `N ◁ H` with `H/N` solvable fixing every listed object. -/
theorem solvableTransport_set [Finite G] {Ω : Type u} [RAct G Ω] {H N : Subgroup G}
    (hNH : N ≤ H) (hn : Normalizes H N) (hsolv : ∃ ℓ, relDerived H N ℓ ≤ N)
    {X Y : Multiset Ω} (hX : Fixes N X) (hY : Fixes N Y) :
    (solvableTransport H N X Y).set = Iso H X Y := by
  obtain ⟨hSH, _, hSN⟩ := supplement_spec hNH hn hsolv
  set S := supplement H N
  have hrec := proc_set (quotLength S (S ⊓ N)) S (S ⊓ N) X Y inf_le_left
    ((normalizes_self S).inf (hn.mono hSH)) (supplement_relDerived hNH hn hsolv)
    (hX.mono inf_le_right) (hY.mono inf_le_right)
  show {h | ∃ n ∈ N, ∃ s ∈ (proc (quotLength S (S ⊓ N)) S (S ⊓ N) X Y).set, h = n * s} = _
  rw [hrec, iso_eq_kernel_mul_supplement hNH hSH
    (exists_kernel_mul_of_sup_eq (hn.mono hSH) hSN) hX]

/-! ### The count -/

/-- Derived series of a solvable group of permutations of any finite set, from Dixon's bound
for `Fin n`. -/
theorem dixon_perm (dixon : GI.Cited.DixonDerivedLength) {B : Type u} [Fintype B]
    [DecidableEq B] (S : Subgroup (Equiv.Perm B)) [IsSolvable S] (k : ℕ)
    (hk : 5 * Real.logb 3 (Fintype.card B) ≤ k) : derivedSeries S k = ⊥ := by
  let e := (Fintype.equivFin B).permCongrHom
  let S' := S.map e.toMonoidHom
  let f : S ≃* S' := S.equivMapOfInjective e.toMonoidHom e.injective
  haveI : IsSolvable S' := solvable_of_surjective (f := f.toMonoidHom) f.surjective
  have h' := dixon (Fintype.card B) S' inferInstance k hk
  have := map_derivedSeries_eq (f := f.symm.toMonoidHom) f.symm.surjective k
  rw [h', Subgroup.map_bot] at this
  exact this.symm

theorem relDerived_le_of_solvable {S M : Subgroup G} (hMS : M ≤ S) (hn : Normalizes S M) {k : ℕ}
    (h : derivedSeries S k = ⊥) : relDerived S M k ≤ M := by
  haveI := normal_of_normalizes hn
  apply relDerived_le_of_derivedSeries hMS
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (M.subgroupOf S)) k, h,
    Subgroup.map_bot]

/-- The recursion depth: `ℓ ≤ 5 log₃ b + 1`, from Dixon's bound for the solvable supplement. -/
theorem solvableTransport_depth {B : Type u} [Fintype B] [DecidableEq B]
    (dixon : GI.Cited.DixonDerivedLength) {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H)
    (hn : Normalizes H N) (hsolv : ∃ ℓ, relDerived H N ℓ ≤ N) :
    (quotLength (supplement H N) (supplement H N ⊓ N) : ℝ) ≤
      5 * Real.logb 3 (Fintype.card B) + 1 := by
  obtain ⟨_, hS, _⟩ := supplement_spec hNH hn hsolv
  set k := ⌈5 * Real.logb 3 (Fintype.card B)⌉₊
  have hk := dixon_perm dixon (supplement H N) k (Nat.le_ceil _)
  have hle := quotLength_le (relDerived_le_of_solvable inf_le_left
    ((normalizes_self _).inf (hn.mono (supplement_spec hNH hn hsolv).1)) hk)
  calc (quotLength (supplement H N) (supplement H N ⊓ N) : ℝ) ≤ k := by exact_mod_cast hle
    _ ≤ _ := (Nat.ceil_lt_add_one (by
        have h0 : 0 ≤ Real.logb 3 (Fintype.card B : ℝ) := by
          rcases Nat.eq_zero_or_pos (Fintype.card B) with h | h
          · simp [h]
          · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)
        positivity)).le

end GI.Multicoset
