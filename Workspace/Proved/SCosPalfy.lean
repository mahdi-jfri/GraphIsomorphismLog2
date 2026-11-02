import Workspace.Proved.SCosMath
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Solvable

/-!
# Few coset representatives for the kernel on a minimal block system

In the transitive case of [LM, Proposition 3.9] the algorithm runs once for each coset of the
kernel of the action on a minimal block system. The time is polynomial because there are
few such cosets: the group acts on the `m` blocks as a primitive solvable group, and such a
group has order at most `(m + 1)^c` by the Pálfy–Wolf bound ([LM, Theorem 3.8], the
Babai–Cameron–Pálfy bound, specialized to solvable groups).

The bound is a hypothesis here (`ScosPalfyBound`). Its body is, word for word, the statement
`GI.Proved.PalfyBound` proved in `Proved/Palfy.lean`. It has its own
name so that the two files do not clash.

Main result: `scos_palfy_classes`. Let `H ≤ Sym(k)` be solvable and transitive, and let `lab`
be a minimal block system of `H` (`GI.Cited.IsMinimalBlocks`). Then any set of elements of `H`
that act pairwise differently on the `m` blocks has at most `(m + 1)^c` elements.

The proof builds the action on the classes `ScosCls lab` (the values of `lab`), shows that
it is primitive (`scos_isPreprimitive`: a block `B` of it gives a coarser invariant labeling,
"lie in a common translate of `B`", and minimality of `lab` makes `B` trivial), and moves it to
`Fin m` by a bijection.
-/

namespace GI.Proved

open Equiv GI.Cited
open scoped Pointwise

/-- The Pálfy–Wolf bound ([LM, Theorem 3.8] for solvable groups): a primitive solvable
permutation group of degree `n` has order at most `(n + 1)^c`. The body is the statement
`GI.Proved.PalfyBound` of `Proved/Palfy.lean`. -/
def ScosPalfyBound : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))), IsSolvable G →
    MulAction.IsPreprimitive G (Fin n) → Nat.card G ≤ (n + 1) ^ c

section Classes

variable {k : ℕ} (lab : Fin k → ℕ)

/-- The classes of a labeling: its values. -/
def ScosCls : Type := {v : ℕ // ∃ i, lab i = v}

/-- The class of a point. -/
def scosCls (i : Fin k) : ScosCls lab := ⟨lab i, i, rfl⟩

/-- A point of a class. -/
noncomputable def scosRep (q : ScosCls lab) : Fin k := q.2.choose

theorem scosCls_rep (q : ScosCls lab) : scosCls lab (scosRep lab q) = q :=
  Subtype.ext q.2.choose_spec

theorem scosCls_eq_iff {i j : Fin k} : scosCls lab i = scosCls lab j ↔ lab i = lab j :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem scosRep_injective : Function.Injective (scosRep lab) := fun q q' h => by
  rw [← scosCls_rep lab q, ← scosCls_rep lab q', h]

noncomputable instance : Fintype (ScosCls lab) :=
  have : Finite (ScosCls lab) := Finite.of_injective _ (scosRep_injective lab)
  Fintype.ofFinite _

theorem scosCls_card_le : Fintype.card (ScosCls lab) ≤ k := by
  simpa using Fintype.card_le_of_injective _ (scosRep_injective lab)

/-- The action of a permutation on the classes, through a point of the class. -/
noncomputable def scosAct (h : Perm (Fin k)) (q : ScosCls lab) : ScosCls lab :=
  scosCls lab (h (scosRep lab q))

variable {lab} {H : Subgroup (Perm (Fin k))}

theorem scosAct_cls (hinv : InvariantLabeling H lab) {h : Perm (Fin k)} (hh : h ∈ H)
    (i : Fin k) : scosAct lab h (scosCls lab i) = scosCls lab (h i) := by
  unfold scosAct
  rw [scosCls_eq_iff, hinv h hh, ← scosCls_eq_iff, scosCls_rep]

theorem scosAct_mul (hinv : InvariantLabeling H lab) {g h : Perm (Fin k)} (hg : g ∈ H)
    (hh : h ∈ H) (q : ScosCls lab) :
    scosAct lab (g * h) q = scosAct lab g (scosAct lab h q) := by
  rw [← scosCls_rep lab q, scosAct_cls hinv (H.mul_mem hg hh), scosAct_cls hinv hh,
    scosAct_cls hinv hg, Perm.mul_apply]

theorem scosAct_one (q : ScosCls lab) : scosAct lab 1 q = q := by
  simp [scosAct, scosCls_rep]

/-- The action of an element of `H` on the classes, as a permutation. -/
noncomputable def scosPerm (hinv : InvariantLabeling H lab) (h : H) : Perm (ScosCls lab) where
  toFun := scosAct lab h
  invFun := scosAct lab (h⁻¹ : H)
  left_inv q := by
    rw [← scosAct_mul hinv (h⁻¹ : H).2 h.2]; simp [scosAct_one]
  right_inv q := by
    rw [← scosAct_mul hinv h.2 (h⁻¹ : H).2]; simp [scosAct_one]

/-- The action of `H` on the classes, as a homomorphism. -/
noncomputable def scosHom (hinv : InvariantLabeling H lab) : H →* Perm (ScosCls lab) :=
  MonoidHom.mk' (scosPerm hinv) fun g h => by
    ext q : 1
    exact scosAct_mul hinv g.2 h.2 q

theorem scosHom_apply (hinv : InvariantLabeling H lab) (h : H) (i : Fin k) :
    scosHom hinv h (scosCls lab i) = scosCls lab (h.1 i) :=
  scosAct_cls hinv h.2 i

/-- The relation "the classes of `i` and `j` lie in a common translate of `B`". -/
def scosRel (hinv : InvariantLabeling H lab) (B : Set (ScosCls lab)) (i j : Fin k) : Prop :=
  ∃ r : (scosHom hinv).range, scosCls lab i ∈ r • B ∧ scosCls lab j ∈ r • B

/-- **The action on the classes is primitive**, for a transitive `H` and a minimal block
system `lab`. -/
theorem scos_isPreprimitive (hinv : InvariantLabeling H lab)
    (htr : ∀ i j : Fin k, ∃ h ∈ H, h i = j) (hmin : IsMinimalBlocks H lab) :
    MulAction.IsPreprimitive (scosHom hinv).range (ScosCls lab) := by
  classical
  -- The range acts transitively, since `H` does.
  have hpt : MulAction.IsPretransitive (scosHom hinv).range (ScosCls lab) := by
    refine ⟨fun q q' => ?_⟩
    obtain ⟨h, hh, he⟩ := htr (scosRep lab q) (scosRep lab q')
    refine ⟨⟨scosHom hinv ⟨h, hh⟩, ⟨h, hh⟩, rfl⟩, ?_⟩
    change scosHom hinv ⟨h, hh⟩ q = q'
    conv_lhs => rw [← scosCls_rep lab q]
    rw [scosHom_apply]
    simp only [he, scosCls_rep]
  refine { toIsPretransitive := hpt, isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  rcases B.eq_empty_or_nonempty with hB0 | ⟨b₀, hb₀⟩
  · exact Or.inl (by rw [hB0]; exact Set.subsingleton_empty)
  -- Every class lies in a translate of `B`.
  have hcover : ∀ q : ScosCls lab, ∃ r : (scosHom hinv).range, q ∈ r • B := by
    intro q
    obtain ⟨r, hr⟩ := hpt.exists_smul_eq b₀ q
    exact ⟨r, ⟨b₀, hb₀, hr⟩⟩
  -- Two translates that meet are equal.
  have hmeet : ∀ (r r' : (scosHom hinv).range) (q : ScosCls lab), q ∈ r • B → q ∈ r' • B →
      r • B = r' • B := by
    intro r r' q h1 h2
    rcases hB.smul_eq_smul_or_disjoint r r' with he | hd
    · exact he
    · exact absurd (Set.disjoint_left.mp hd h1) (not_not.mpr h2)
  let R := scosRel hinv B
  have hrefl : ∀ i, R i i := fun i => by
    obtain ⟨r, hr⟩ := hcover (scosCls lab i)
    exact ⟨r, hr, hr⟩
  have hsymm : ∀ i j, R i j → R j i := fun i j ⟨r, h1, h2⟩ => ⟨r, h2, h1⟩
  have htrans : ∀ i j l, R i j → R j l → R i l := by
    rintro i j l ⟨r, h1, h2⟩ ⟨r', h3, h4⟩
    refine ⟨r, h1, ?_⟩
    rw [hmeet r r' _ h2 h3]
    exact h4
  -- The relation, as a labeling: the least point related to `i`.
  let lab' : Fin k → ℕ := fun i =>
    ((Finset.univ.filter (fun j => R i j)).min' ⟨i, by simp [hrefl i]⟩ : ℕ)
  have hlab' : ∀ i j, lab' i = lab' j ↔ R i j := by
    intro i j
    have hset : ∀ i j, R i j →
        Finset.univ.filter (fun l => R i l) = Finset.univ.filter (fun l => R j l) := by
      intro i j hij
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => htrans _ _ _ (hsymm _ _ hij) h, fun h => htrans _ _ _ hij h⟩
    constructor
    · intro he
      have hi := Finset.min'_mem (Finset.univ.filter (fun l => R i l)) ⟨i, by simp [hrefl i]⟩
      have hj := Finset.min'_mem (Finset.univ.filter (fun l => R j l)) ⟨j, by simp [hrefl j]⟩
      have he' : (Finset.univ.filter (fun l => R i l)).min' ⟨i, by simp [hrefl i]⟩ =
          (Finset.univ.filter (fun l => R j l)).min' ⟨j, by simp [hrefl j]⟩ := Fin.ext he
      rw [he'] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact htrans _ _ _ hi (hsymm _ _ hj)
    · intro hij
      simp only [lab']
      have key : ∀ (A B : Finset (Fin k)) (ha : A.Nonempty) (hb : B.Nonempty), A = B →
          A.min' ha = B.min' hb := by
        rintro A B ha hb rfl; rfl
      rw [key _ _ _ _ (hset i j hij)]
  -- The relation is invariant.
  have hRinv : ∀ h ∈ H, ∀ i j, R (h i) (h j) ↔ R i j := by
    intro h hh i j
    let r₀ : (scosHom hinv).range := ⟨scosHom hinv ⟨h, hh⟩, ⟨h, hh⟩, rfl⟩
    have hcls : ∀ l, scosCls lab (h l) = r₀ • scosCls lab l := fun l =>
      (scosHom_apply hinv ⟨h, hh⟩ l).symm
    constructor
    · rintro ⟨r, h1, h2⟩
      refine ⟨r₀⁻¹ * r, ?_, ?_⟩
      · rw [mul_smul, ← Set.smul_mem_smul_set_iff (a := r₀), smul_inv_smul, ← hcls]; exact h1
      · rw [mul_smul, ← Set.smul_mem_smul_set_iff (a := r₀), smul_inv_smul, ← hcls]; exact h2
    · rintro ⟨r, h1, h2⟩
      refine ⟨r₀ * r, ?_, ?_⟩
      · rw [hcls, mul_smul, Set.smul_mem_smul_set_iff]; exact h1
      · rw [hcls, mul_smul, Set.smul_mem_smul_set_iff]; exact h2
  have hinv' : InvariantLabeling H lab' := fun h hh i j => by
    rw [hlab', hlab', hRinv h hh]
  have hcoarse : ∀ i j, lab i = lab j → lab' i = lab' j := by
    intro i j he
    rw [hlab']
    obtain ⟨r, hr⟩ := hcover (scosCls lab i)
    refine ⟨r, hr, ?_⟩
    rw [← (scosCls_eq_iff lab).mpr he]
    exact hr
  have hB1 : (1 : (scosHom hinv).range) • B = B := one_smul _ _
  rcases hmin.2.2 lab' hinv' hcoarse with hsame | hall
  · -- The translates are the classes: `B` has one class.
    left
    intro q hq q' hq'
    have hR : R (scosRep lab q) (scosRep lab q') :=
      ⟨1, by rw [hB1, scosCls_rep]; exact hq, by rw [hB1, scosCls_rep]; exact hq'⟩
    rw [← hlab', hsame, ← scosCls_eq_iff, scosCls_rep, scosCls_rep] at hR
    exact hR
  · -- One translate covers everything: `B` is everything.
    right
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨r, h1, h2⟩ := (hlab' (scosRep lab q) (scosRep lab b₀)).mp
      (hall (scosRep lab q) (scosRep lab b₀))
    rw [scosCls_rep] at h1 h2
    have := hmeet r 1 b₀ h2 (by rw [hB1]; exact hb₀)
    rw [this, hB1] at h1
    exact h1

end Classes

/-- The classes of `lab` are as many as its values. -/
theorem scosCls_card_eq {k : ℕ} (lab : Fin k → ℕ) : Fintype.card (ScosCls lab) = (Finset.univ.image lab).card := by
  classical
  rw [← Set.toFinset_range, Set.toFinset_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun v => by simp [Set.mem_range])

/-- **Few coset representatives.** Under the Pálfy–Wolf bound, there is `c` such that for
every solvable transitive `H ≤ Sym(k)` and minimal block system `lab` of `H` with `m` classes,
a set of elements of `H` that act pairwise differently on the classes has at most `(m + 1)^c`
elements. -/
theorem scos_palfy_classes (hP : ScosPalfyBound) : ∃ c : ℕ, ∀ (k : ℕ)
    (H : Subgroup (Perm (Fin k))) (lab : Fin k → ℕ), IsSolvable H →
    (∀ i j : Fin k, ∃ h ∈ H, h i = j) → IsMinimalBlocks H lab →
    ∀ S : Finset (Perm (Fin k)), (∀ s ∈ S, s ∈ H) →
      (∀ s ∈ S, ∀ t ∈ S, (∀ i, lab (s i) = lab (t i)) → s = t) →
        S.card ≤ ((Finset.univ.image lab).card + 1) ^ c := by
  classical
  obtain ⟨c, hc⟩ := hP
  refine ⟨c, fun k H lab hsol htr hmin S hSH hSinj => ?_⟩
  have hinv := hmin.1
  let ψ := scosHom hinv
  let m := Fintype.card (ScosCls lab)
  let e : ScosCls lab ≃ Fin m := Fintype.equivFin _
  let E : Perm (ScosCls lab) ≃* Perm (Fin m) := e.permCongrHom
  let G' : Subgroup (Perm (Fin m)) := ψ.range.map E.toMonoidHom
  let φ : ψ.range →* G' := MonoidHom.mk' (fun x => ⟨E x.1, Subgroup.mem_map_of_mem _ x.2⟩)
    fun a b => Subtype.ext (map_mul E a.1 b.1)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  -- `G'` is solvable: an image of `H`.
  have hsol' : IsSolvable G' := by
    have : IsSolvable ψ.range := solvable_of_surjective ψ.rangeRestrict_surjective
    exact solvable_of_surjective hφ
  -- `G'` is primitive: the bijection `e` carries the primitive action on the classes.
  have hpre : MulAction.IsPreprimitive ψ.range (ScosCls lab) :=
    scos_isPreprimitive hinv htr hmin
  let f : ScosCls lab →ₑ[φ] Fin m :=
    { toFun := e
      map_smul' := fun r q => by
        change e ((r : Perm (ScosCls lab)) q) = (E r.1) (e q)
        simp [E, Equiv.permCongrHom, Equiv.permCongr_apply] }
  have hpre' : MulAction.IsPreprimitive G' (Fin m) :=
    MulAction.IsPreprimitive.of_surjective (f := f) e.surjective
  have hcard : Nat.card G' ≤ ((Finset.univ.image lab).card + 1) ^ c := by
    have h1 := hc m G' hsol' hpre'
    have h2 : m = (Finset.univ.image lab).card := scosCls_card_eq lab
    exact h1.trans (le_of_eq (by rw [h2]))
  -- `S` injects into `G'`.
  let F : Perm (Fin k) → Perm (Fin m) := fun s =>
    if hs : s ∈ H then E (ψ ⟨s, hs⟩) else 1
  have hF : ∀ s ∈ S, F s ∈ (G' : Set (Perm (Fin m))).toFinset := by
    intro s hs
    simp only [F, dif_pos (hSH s hs), Set.mem_toFinset, SetLike.mem_coe]
    exact Subgroup.mem_map_of_mem _ ⟨⟨s, hSH s hs⟩, rfl⟩
  have hFinj : Set.InjOn F S := by
    intro s hs t ht hst
    simp only [F, dif_pos (hSH s hs), dif_pos (hSH t ht)] at hst
    have h1 : ψ ⟨s, hSH s hs⟩ = ψ ⟨t, hSH t ht⟩ := E.injective hst
    refine hSinj s hs t ht fun i => ?_
    have h2 := congrArg (fun σ : Perm (ScosCls lab) => σ (scosCls lab i)) h1
    simp only [ψ, scosHom_apply] at h2
    exact (scosCls_eq_iff lab).mp h2
  calc S.card ≤ (G' : Set (Perm (Fin m))).toFinset.card :=
        Finset.card_le_card_of_injOn F hF hFinj
    _ = Nat.card G' := by
        rw [Set.toFinset_card, Nat.card_eq_fintype_card]; rfl
    _ ≤ ((Finset.univ.image lab).card + 1) ^ c := hcard

end GI.Proved
