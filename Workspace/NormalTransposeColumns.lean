import Workspace.Paper.RowNormalFormDefs
import Workspace.RowTransfers
import Workspace.CleanRowSubdirect

/-! The column partition in the proof of Lemma A.14, from a supplied clean row
normal form (`GI.Paper.IsRowNormalForm`).

The paper: "The `𝓜`-orbits are `{i} × Δ_j`, where `Δ_j` ranges over the
`N`-orbits. The normal subgroup `J = 𝓜 R₀` has orbits `[m] × Δ_j`. The
diagonal quotient ensures that the local actions on the different rows induce
the same permutation of the `Δ_j`, so these are invariant columns."

Here `𝓜 = M` and `R₀ = s(Alt(m))`. The column of a point `e (b, i)` is the
`N`-orbit of `b`. -/

namespace GI.NormalTranspose

open Equiv GI.Paper

variable {V B I : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Perm V)} {K : Subgroup G} {e : B × I ≃ V}
variable {s : alternatingGroup I →* G} {i0 : I}
variable {N Nstar : Subgroup (cleanLocalGroup G e i0)} [N.Normal] [Nstar.Normal]

/-- The column label of a point: the `N`-orbit of its in-block coordinate. -/
def colOf (e : B × I ≃ V) (N : Subgroup (cleanLocalGroup G e i0)) (v : V) :
    Quotient (MulAction.orbitRel N B) :=
  Quotient.mk _ (e.symm v).1

omit [Fintype I] [DecidableEq I] [N.Normal] in
theorem colOf_apply (b : B) (i : I) : colOf e N (e (b, i)) = Quotient.mk _ b := by
  simp [colOf]

omit [Fintype I] in
/-- A product over an enumeration of a tuple with entries `a` at `i`, `a⁻¹` at
`i'`, and `1` elsewhere is `1`. -/
theorem transfer_list_prod {Q : Type*} [Group Q] (l : List I) (hl : l.Nodup) {i i' : I}
    (hii' : i ≠ i') (hi : i ∈ l) (hi' : i' ∈ l) (a : Q) :
    (l.map (fun r => if r = i then a else if r = i' then a⁻¹ else 1)).prod = 1 := by
  set q : I → Q := fun r => if r = i then a else if r = i' then a⁻¹ else 1
  have hval : ∀ r, q r = a ∨ q r = a⁻¹ ∨ q r = 1 := by
    intro r
    simp only [q]
    split_ifs <;> simp
  have hc : ∀ r r', Commute (q r) (q r') := by
    intro r r'
    rcases hval r with h | h | h <;> rcases hval r' with h' | h' | h' <;> rw [h, h'] <;>
      simp [Commute.refl, Commute.one_left, Commute.one_right]
  have hi'e : i' ∈ l.erase i := (List.mem_erase_of_ne (Ne.symm hii')).mpr hi'
  have hperm : List.Perm l (i :: i' :: (l.erase i).erase i') :=
    (List.perm_cons_erase hi).trans (List.Perm.cons i (List.perm_cons_erase hi'e))
  have hpw : (l.map q).Pairwise Commute := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (R := fun _ _ => True) (fun _ _ _ => hc _ _)
      (List.pairwise_of_forall (fun _ _ => trivial))
  rw [(hperm.map q).prod_eq' hpw]
  have hrest : ∀ r ∈ (l.erase i).erase i', q r = 1 := by
    intro r hr
    have hr1 := (hl.erase i).mem_erase_iff.mp hr
    have hr2 := hl.mem_erase_iff.mp hr1.2
    simp [q, hr1.1, hr2.1]
  have hone : (((l.erase i).erase i').map q).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact hrest r hr
  simp only [List.map_cons, List.prod_cons, hone, mul_one]
  simp [q, Ne.symm hii']

omit [Fintype I] [DecidableEq I] in
theorem cleanLift_apply (H : Subgroup (Perm B)) (x : I → H) (b : B) (i : I) :
    cleanLift e H x (e (b, i)) = e ((x i).val b, i) :=
  cleanRowPerm_apply e _ b i

variable (hRNF : IsRowNormalForm G K e i0 s N Nstar)
include hRNF

/-- The `M`-orbits are the cells `{i} × Δ` with `Δ` an `N`-orbit. -/
theorem m_orbit_iff (b b' : B) (i i' : I) (hcard : 2 ≤ Fintype.card I) :
    (∃ g ∈ rowNormalM G K e i0 N, g.val (e (b, i)) = e (b', i')) ↔
      i = i' ∧ ∃ n : N, n • b = b' := by
  classical
  constructor
  · rintro ⟨g, ⟨_, x, hx, hxg⟩, hgv⟩
    have hxg' : cleanLift e _ x = g.val := hxg
    rw [← hxg', cleanLift_apply] at hgv
    have h := e.injective hgv
    simp only [Prod.mk.injEq] at h
    exact ⟨h.2, ⟨⟨x i, hx i⟩, h.1⟩⟩
  · rintro ⟨rfl, n, hn⟩
    obtain ⟨ψ, hψ, _, hrange⟩ := hRNF.zero_sum
    -- A second row `i'`.
    obtain ⟨i', hii'⟩ : ∃ i', i ≠ i' := by
      obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card I)
      by_cases ha : a = i
      · exact ⟨b, fun h => hab (ha.trans h)⟩
      · exact ⟨a, fun h => ha h.symm⟩
    let q : I → cleanLocalGroup G e i0 ⧸ Nstar := fun r =>
      if r = i then (n.val : cleanLocalGroup G e i0 ⧸ Nstar)
      else if r = i' then (n.val : cleanLocalGroup G e i0 ⧸ Nstar)⁻¹ else 1
    have hq : q ∈ rowZeroSum N Nstar := by
      refine ⟨fun r => ?_, ?_⟩
      · simp only [q]
        split_ifs
        · exact ⟨n.val, n.property, rfl⟩
        · exact ⟨n.val⁻¹, N.inv_mem n.property, by simp⟩
        · exact Subgroup.one_mem _
      · exact transfer_list_prod _ (Finset.nodup_toList _) hii' (by simp) (by simp) _
    rw [← hrange] at hq
    obtain ⟨g, hg⟩ := hq
    obtain ⟨hgK, x, hxN, hxg0⟩ := g.property
    have hxg : cleanLift e _ x = g.val.val := hxg0
    have hqi := congrFun (hg.symm.trans (hψ g x hxg)) i
    simp only [q, if_pos rfl] at hqi
    -- `x i ≡ n` modulo `N*`; correct row `i` by an element of `M* = (N*)^m`.
    have hcorr : (x i)⁻¹ * n.val ∈ Nstar := by
      have := QuotientGroup.eq.mp hqi.symm
      exact this
    let y : I → cleanLocalGroup G e i0 := fun r => if r = i then (x i)⁻¹ * n.val else 1
    have hyNstar : y ∈ rowPower Nstar := by
      intro r
      simp only [y]
      split_ifs
      · exact hcorr
      · exact Nstar.one_mem
    have hyG : cleanLift e _ y ∈ G := hRNF.mstar_le_G ⟨y, hyNstar, rfl⟩
    have hyM : (⟨cleanLift e _ y, hyG⟩ : G) ∈ rowNormalM G K e i0 N :=
      hRNF.mstar_le_m ⟨y, hyNstar, rfl⟩
    refine ⟨g.val * ⟨cleanLift e _ y, hyG⟩, (rowNormalM G K e i0 N).mul_mem g.property hyM, ?_⟩
    change g.val.val (cleanLift e _ y (e (b, i))) = e (b', i)
    rw [cleanLift_apply, ← hxg, cleanLift_apply]
    congr 2
    simp only [y, if_pos rfl]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, Perm.apply_inv_self]
    exact hn

/-- The subgroup of elements of `G` that fix every column label. -/
def columnFixer : Subgroup G where
  carrier := {g | ∀ v, colOf e N (g.val v) = colOf e N v}
  one_mem' := fun v => rfl
  mul_mem' := by
    intro g h hg hh v
    change colOf e N (g.val (h.val v)) = _
    rw [hg, hh]
  inv_mem' := by
    intro g hg v
    have h := hg (g⁻¹.val v)
    rw [show g.val (g⁻¹.val v) = v by simp] at h
    exact h.symm

omit hRNF [Fintype I] [DecidableEq I] [N.Normal] in
theorem mem_columnFixer_of_M (g : G) (hg : g ∈ rowNormalM G K e i0 N) :
    g ∈ columnFixer (e := e) (N := N) := by
  obtain ⟨_, x, hx, hxg0⟩ := hg
  have hxg : cleanLift e _ x = g.val := hxg0
  intro v
  obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective v
  rw [← hxg, cleanLift_apply, colOf_apply, colOf_apply]
  apply Quotient.sound
  exact ⟨⟨x i, hx i⟩, rfl⟩

omit hRNF [N.Normal] in
theorem mem_columnFixer_of_pure (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    (p : alternatingGroup I) : s p ∈ columnFixer (e := e) (N := N) := by
  intro v
  obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective v
  rw [hpure, colOf_apply, colOf_apply]

/-- The `J`-orbits, `J = M R₀`, are the columns `[m] × Δ`. -/
theorem j_orbit_iff (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    (hcard : 4 ≤ Fintype.card I) (v w : V) :
    (∃ g ∈ rowNormalM G K e i0 N ⊔ s.range, g.val v = w) ↔ colOf e N v = colOf e N w := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hle : rowNormalM G K e i0 N ⊔ s.range ≤ columnFixer (e := e) (N := N) := by
      apply sup_le
      · exact fun g hg => mem_columnFixer_of_M g hg
      · rintro _ ⟨p, rfl⟩
        exact mem_columnFixer_of_pure hpure p
    exact (hle hg v).symm
  · intro hvw
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective v
    obtain ⟨⟨b', i'⟩, rfl⟩ := e.surjective w
    rw [colOf_apply, colOf_apply] at hvw
    obtain ⟨n, hn⟩ := Quotient.exact hvw
    obtain ⟨g, hgM, hgv⟩ := (m_orbit_iff hRNF b b' i i (by omega)).mpr
      ⟨rfl, n⁻¹, by rw [← hn]; exact inv_smul_smul n b'⟩
    obtain ⟨p, hp, hpi⟩ := GI.even_perm_maps_point hcard i i'
    refine ⟨s ⟨p, hp⟩ * g, Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨⟨p, hp⟩, rfl⟩)
      (Subgroup.mem_sup_left hgM), ?_⟩
    change (s ⟨p, hp⟩).val (g.val (e (b, i))) = _
    rw [hgv, hpure]
    simp [hpi]

/-- The columns are invariant: `G` permutes them, because they are the orbits
of the normal subgroup `J = M R₀`. -/
theorem columns_invariant (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    (hcard : 4 ≤ Fintype.card I) (g : G) (v w : V) (hvw : colOf e N v = colOf e N w) :
    colOf e N (g.val v) = colOf e N (g.val w) := by
  obtain ⟨j, hj, rfl⟩ := (j_orbit_iff hRNF hpure hcard v w).mpr hvw
  apply (j_orbit_iff hRNF hpure hcard _ _).mp
  haveI := hRNF.mr_normal
  refine ⟨g * j * g⁻¹, (inferInstance : (rowNormalM G K e i0 N ⊔ s.range).Normal).conj_mem j hj g, ?_⟩
  simp

omit hRNF [N.Normal] in
/-- The old `Alt(m)` acts inside the columns. -/
theorem complement_in_columns (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    (p : alternatingGroup I) (v : V) : colOf e N ((s p).val v) = colOf e N v :=
  mem_columnFixer_of_pure hpure p v

omit hRNF [DecidableEq I] [N.Normal] in
/-- A column `[m] × Δ` has `m |Δ|` points. -/
theorem column_card [Fintype B] [Fintype V] [DecidableEq (Quotient (MulAction.orbitRel N B))]
    (C : Quotient (MulAction.orbitRel N B)) :
    Fintype.card {v : V // colOf e N v = C} =
      Fintype.card I * Fintype.card {b : B // Quotient.mk _ b = C} := by
  classical
  have h : {v : V // colOf e N v = C} ≃ {b : B // Quotient.mk _ b = C} × I :=
    { toFun := fun v => (⟨(e.symm v.val).1, v.property⟩, (e.symm v.val).2)
      invFun := fun p => ⟨e (p.1.val, p.2), by rw [colOf_apply]; exact p.1.property⟩
      left_inv := by
        rintro ⟨v, hv⟩
        apply Subtype.ext
        simp
      right_inv := by
        rintro ⟨⟨b, hb⟩, i⟩
        simp }
  rw [Fintype.card_congr h, Fintype.card_prod, mul_comm]

omit hRNF [Fintype I] [DecidableEq I] [N.Normal] in
/-- There are at most `b` columns. -/
theorem column_count_le [Fintype B] [Fintype (Quotient (MulAction.orbitRel N B))] :
    Fintype.card (Quotient (MulAction.orbitRel N B)) ≤ Fintype.card B :=
  Fintype.card_le_of_surjective _ Quotient.mk_surjective

end GI.NormalTranspose
