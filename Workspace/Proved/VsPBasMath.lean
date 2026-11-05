module

public import Workspace.Impl.VsPBas
public import Workspace.Proved.VStabLinMath
public import Workspace.Proved.VsWBasic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# The greedy basis spans the orbit keys

Read a key `κ` (a list of numbers below `r`) as the vector `vsF r κ`. The greedy basis
`vsPBasis r O` keeps an element when its key is outside the span of the keys kept so far.
So the kept keys span the same space as all keys of `O`, and each kept key raises the dimension
by one. Hence the number of kept elements is the dimension of that span (`vsPBasis_math`).
-/

namespace GI.Proved

open GI.Impl Equiv Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {n r : ℕ} [hr : Fact r.Prime] {kf : Perm (Fin n) → List ℕ} {k : ℕ}

/-- The span of the keys `kf c`, `c ∈ cs`. -/
def vsPKSpan (r : ℕ) (kf : Perm (Fin n) → List ℕ) (cs : List (Perm (Fin n))) :
    Submodule (ZMod r) (ℕ → ZMod r) :=
  Submodule.span (ZMod r) {v | ∃ c ∈ cs, v = vsF r (kf c)}

theorem vsPKSpan_append (cs : List (Perm (Fin n))) (c : Perm (Fin n)) :
    vsPKSpan r kf (cs ++ [c]) = vsPKSpan r kf cs ⊔ Submodule.span (ZMod r) {vsF r (kf c)} := by
  unfold vsPKSpan
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [List.mem_append, List.mem_singleton, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c', hc' | rfl, rfl⟩
    · exact Or.inl ⟨c', hc', rfl⟩
    · exact Or.inr rfl
  · rintro (⟨c', hc', rfl⟩ | rfl)
    · exact ⟨c', Or.inl hc', rfl⟩
    · exact ⟨c, Or.inr rfl, rfl⟩

omit hr in
theorem vsPKSpan_nil : vsPKSpan r kf ([] : List (Perm (Fin n))) = ⊥ :=
  Submodule.span_eq_bot.2 fun v hv => by simp at hv

instance vsPKSpan_fd (cs : List (Perm (Fin n))) : FiniteDimensional (ZMod r) (vsPKSpan r kf cs) := by
  unfold vsPKSpan
  have : {v | ∃ c ∈ cs, v = vsF r (kf c)} = (fun c => vsF r (kf c)) '' {c | c ∈ cs} := by
    ext v; simp [eq_comm]
  rw [this]
  exact FiniteDimensional.span_of_finite _ ((List.finite_toSet cs).image _)

/-- Adding a vector outside a finite-dimensional subspace raises the dimension by one. -/
theorem vsP_finrank_sup_singleton {W : Submodule (ZMod r) (ℕ → ZMod r)} [FiniteDimensional (ZMod r) W]
    {v : ℕ → ZMod r} (hv : v ∉ W) :
    finrank (ZMod r) (W ⊔ Submodule.span (ZMod r) {v} : Submodule (ZMod r) (ℕ → ZMod r)) =
      finrank (ZMod r) W + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ W.zero_mem)
  have hd : Disjoint W (Submodule.span (ZMod r) {v}) := (Submodule.disjoint_span_singleton' hv0).2 hv
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span (ZMod r) {v})
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hv0] at h
  exact h

/-- The invariant of the greedy basis after a prefix `L` of the pairs. -/
structure VsPBasInv (r k : ℕ) (kf : Perm (Fin n) → List ℕ) (L : List (Perm (Fin n) × List ℕ))
    (acc : List VsRow × List (Perm (Fin n))) : Prop where
  ech : VsEch r acc.1
  len : ∀ x ∈ acc.1, x.x.length = k ∧ x.t.length = 0
  span : vsSpan r acc.1 = vsPKSpan r kf acc.2
  all : vsPKSpan r kf acc.2 = vsPKSpan r kf (L.map Prod.fst)
  rank : finrank (ZMod r) (vsPKSpan r kf acc.2) = acc.2.length
  sub : ∀ c ∈ acc.2, c ∈ L.map Prod.fst

theorem vsPGStep_inv {L : List (Perm (Fin n) × List ℕ)} {acc : List VsRow × List (Perm (Fin n))}
    (h : VsPBasInv r k kf L acc) {p : Perm (Fin n) × List ℕ}
    (hp : p.2 = kf p.1 ∧ (∀ x ∈ p.2, x < r) ∧ p.2.length = k) :
    VsPBasInv r k kf (L ++ [p]) (vsPGStep r acc p) := by
  have hr0 := hr.out.pos
  have hb : VsBelow r (p.2, []) := hp.2.1
  have hs : VsShort (p.2, []) acc.1 := fun x hx => by
    rw [(h.len x hx).1, (h.len x hx).2, hp.2.2]; simp
  have hall' : vsPKSpan r kf ((L ++ [p]).map Prod.fst) =
      vsPKSpan r kf (L.map Prod.fst) ⊔ Submodule.span (ZMod r) {vsF r (kf p.1)} := by
    rw [List.map_append, List.map_singleton, vsPKSpan_append]
  unfold vsPGStep
  split_ifs with hk
  · obtain ⟨he, hsp, -⟩ := vsInsert_new hr.out h.ech hb hs hk
    have hnot : vsF r (kf p.1) ∉ vsPKSpan r kf acc.2 := by
      rw [← hp.1, ← h.span, ← vsSift_eq_zero_iff hr0 h.ech hb hs]
      exact (vsNzIdx_lt_iff (vsSift_below hr0 acc.1 hb)).1 hk
    refine ⟨he, fun x hx => ?_, ?_, ?_, ?_, fun c hc => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact h.len x hx
      · simp at hx; subst hx
        obtain ⟨l1, l2⟩ := vsSift_length r acc.1 (p.2, [])
        simp [vsNewRow, vsLin_length, l1, l2, hp.2.2]
    · rw [hsp, vsPKSpan_append, h.span, hp.1]
    · rw [vsPKSpan_append, hall', h.all]
    · rw [vsPKSpan_append, vsP_finrank_sup_singleton hnot, h.rank, List.length_append,
        List.length_singleton]
    · rcases List.mem_append.mp hc with hc | hc
      · rw [List.map_append]; exact List.mem_append_left _ (h.sub c hc)
      · simp at hc; subst hc; simp
  · obtain ⟨hin, -⟩ := vsInsert_rel hr0 h.ech hb hs hk
    rw [h.span, hp.1] at hin
    refine ⟨h.ech, h.len, h.span, ?_, h.rank, fun c hc => ?_⟩
    · rw [hall', ← h.all]
      exact (sup_eq_left.2 ((Submodule.span_le).2 (Set.singleton_subset_iff.2 hin))).symm
    · rw [List.map_append]; exact List.mem_append_left _ (h.sub c hc)

/-- **The greedy basis.** For pairs `(z, kf z)` whose keys have entries below `r` and length
`k`, the kept elements come from the list, their keys span the keys of the whole list, and their
number is the dimension of that span. -/
theorem vsPBasis_math {O : List (Perm (Fin n) × List ℕ)}
    (hO : ∀ p ∈ O, p.2 = kf p.1 ∧ (∀ x ∈ p.2, x < r) ∧ p.2.length = k) :
    (∀ c ∈ (vsPBasis r O).2, c ∈ O.map Prod.fst) ∧
      vsPKSpan r kf (vsPBasis r O).2 = vsPKSpan r kf (O.map Prod.fst) ∧
      finrank (ZMod r) (vsPKSpan r kf (O.map Prod.fst)) = (vsPBasis r O).2.length := by
  have key : ∀ (L M : List (Perm (Fin n) × List ℕ)) acc, (∀ p ∈ M, p.2 = kf p.1 ∧ (∀ x ∈ p.2, x < r) ∧ p.2.length = k) →
      VsPBasInv r k kf L acc → VsPBasInv r k kf (L ++ M) (M.foldl (vsPGStep r) acc) := by
    intro L M
    induction M generalizing L with
    | nil => intro acc _ h; simpa using h
    | cons p M ih =>
      intro acc hM h
      have := ih (L ++ [p]) _ (fun q hq => hM q (by simp [hq])) (vsPGStep_inv h (hM p (by simp)))
      simpa using this
  have h0 : VsPBasInv r k kf [] (([] : List VsRow), ([] : List (Perm (Fin n)))) :=
    ⟨trivial, by simp, by simp [vsSpan, vsPKSpan], by simp, by rw [vsPKSpan_nil, finrank_bot]; rfl,
      by simp⟩
  have h := key [] O _ hO h0
  rw [List.nil_append] at h
  exact ⟨h.sub, h.all, by rw [← h.all]; exact h.rank⟩

/-- **Few kept elements.** If the keys have length `k`, at most `k` elements are kept. -/
theorem vsPBasis_length_le {O : List (Perm (Fin n) × List ℕ)}
    (hO : ∀ p ∈ O, p.2 = kf p.1 ∧ (∀ x ∈ p.2, x < r) ∧ p.2.length = k) :
    (vsPBasis r O).2.length ≤ k := by
  obtain ⟨-, -, hrank⟩ := vsPBasis_math hO
  rw [← hrank]
  have hle : vsPKSpan r kf (O.map Prod.fst) ≤ LinearMap.range (vsWE r k) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have hm : vsF r (kf p.1) ∈ vsWSupp r k := vsF_mem_vsWSupp (by rw [← (hO p hp).1, (hO p hp).2.2])
    exact ⟨vsWR r k (vsF r (kf p.1)), vsWE_vsWR hm⟩
  calc Module.finrank (ZMod r) (vsPKSpan r kf (O.map Prod.fst))
      ≤ Module.finrank (ZMod r) (LinearMap.range (vsWE r k)) := Submodule.finrank_mono hle
    _ ≤ Module.finrank (ZMod r) (Fin k → ZMod r) := LinearMap.finrank_range_le _
    _ = k := Module.finrank_fin_fun _

end GI.Proved
