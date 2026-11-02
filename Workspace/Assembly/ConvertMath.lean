import Workspace.Assembly.BuildMath

/-!
# Reading the answer of Algorithm 1

The answer of the pair state `graphState G H` is the image of the graph isomorphisms under the
diagonal map `pairHom n` (`graph_reduction_answer`). If it is a coset `x · K`, given by a
representative `x` and generators `gs` of `K` on the positions `Fin (n * n)`, then:

* `x = pairHom p` for an isomorphism `p` from `G` to `H` (`coset_rep`);
* `K` is the image of `Aut(G)` (`coset_group`);
* the vertex permutation of an element `g = pairHom q` is read off the diagonal:
  `q i = g (i, i) / n` (`proj_pairHom`);
* so the projections `unPair g` of the generators `1, gs` generate `Aut(G)`
  (`closure_unPair`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {n : ℕ}

/-- The graph isomorphisms from `G` to `H`, as vertex permutations. -/
def isoSet (G H : SimpleGraph (Fin n)) : Set (Perm (Fin n)) :=
  {p | ∀ u v, G.Adj u v ↔ H.Adj (p u) (p v)}

/-- The image of the answer of the pair state on the positions. -/
theorem answer_image (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    toFin (pairEnum n) '' (graphState G H).answer = pairHom n '' isoSet G H := by
  rw [graph_reduction_answer, Set.image_image]
  rfl

theorem isEmpty_of_answer_empty (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : (graphState G H).answer = ∅) : IsEmpty (G ≃g H) := by
  rw [graph_reduction_answer, Set.image_eq_empty] at h
  refine ⟨fun e => ?_⟩
  have : (e.toEquiv : Perm (Fin n)) ∈ isoSet G H := fun u v => e.map_rel_iff.symm
  rw [isoSet, h] at this
  exact this

/-- An isomorphism `p` as a graph isomorphism. -/
def isoOf {G H : SimpleGraph (Fin n)} {p : Perm (Fin n)} (hp : p ∈ isoSet G H) : G ≃g H :=
  ⟨p, fun {u v} => (hp u v).symm⟩

theorem isoOf_toEquiv {G H : SimpleGraph (Fin n)} {p : Perm (Fin n)} (hp : p ∈ isoSet G H) :
    (isoOf hp).toEquiv = p := rfl

theorem iso_inv_mul {G H : SimpleGraph (Fin n)} {p q : Perm (Fin n)} (hp : p ∈ isoSet G H)
    (hq : q ∈ isoSet G H) : p⁻¹ * q ∈ GI.Statement.autGroup G := by
  intro u v
  rw [hp, Perm.mul_apply, Perm.mul_apply, Perm.apply_inv_self, Perm.apply_inv_self]
  exact (hq u v).symm

theorem iso_mul_aut {G H : SimpleGraph (Fin n)} {p a : Perm (Fin n)} (hp : p ∈ isoSet G H)
    (ha : a ∈ GI.Statement.autGroup G) : p * a ∈ isoSet G H := by
  intro u v
  rw [Perm.mul_apply, Perm.mul_apply, ← hp]
  exact (ha u v).symm

/-- **The representative of a coset answer** is the image of an isomorphism. -/
theorem coset_rep {G H : SimpleGraph (Fin n)} {x : Perm (Fin (n * n))}
    {K : Subgroup (Perm (Fin (n * n)))}
    (h : pairHom n '' isoSet G H = x • (K : Set (Perm (Fin (n * n))))) :
    ∃ p ∈ isoSet G H, pairHom n p = x := by
  have hx : x ∈ x • (K : Set (Perm (Fin (n * n)))) :=
    ⟨1, K.one_mem, mul_one x⟩
  rw [← h] at hx
  exact hx

/-- **The group of a coset answer** is the image of `Aut(G)`. -/
theorem coset_group {G H : SimpleGraph (Fin n)} {x : Perm (Fin (n * n))}
    {K : Subgroup (Perm (Fin (n * n)))}
    (h : pairHom n '' isoSet G H = x • (K : Set (Perm (Fin (n * n))))) :
    K = (GI.Statement.autGroup G).map (pairHom n) := by
  obtain ⟨p, hp, rfl⟩ := coset_rep h
  ext g
  constructor
  · intro hg
    have : pairHom n p * g ∈ pairHom n '' isoSet G H := by
      rw [h]; exact ⟨g, hg, rfl⟩
    obtain ⟨q, hq, hqg⟩ := this
    refine ⟨p⁻¹ * q, iso_inv_mul hp hq, ?_⟩
    rw [map_mul, hqg, map_inv, inv_mul_cancel_left]
  · rintro ⟨a, ha, rfl⟩
    have : pairHom n (p * a) ∈ pairHom n p • (K : Set (Perm (Fin (n * n)))) := by
      rw [← h]; exact ⟨_, iso_mul_aut hp ha, rfl⟩
    rw [map_mul] at this
    exact (Set.smul_mem_smul_set_iff).mp this

/-! ### Reading a vertex permutation off the diagonal -/

/-- The number `g (i, i) / n`: for `g = pairHom q` it is `q i`. -/
def proj (g : Perm (Fin (n * n))) (i : Fin n) : ℕ := (g (pairEnum n (i, i)) : ℕ) / n

theorem proj_pairHom (q : Perm (Fin n)) (i : Fin n) : proj (pairHom n q) i = q i := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; exact i.elim0
  unfold proj
  rw [pairHom_apply]
  show ((pairEnum n (diagonalHom (Fin n) q ((pairEnum n).symm (pairEnum n (i, i)))) :
    Fin (n * n)) : ℕ) / n = _
  rw [Equiv.symm_apply_apply, diagonalHom_apply, pairEnum_val]
  rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (q i).isLt, Nat.zero_add]

theorem proj_le (g : Perm (Fin (n * n))) (i : Fin n) : proj g i ≤ n := by
  unfold proj
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have := (g (pairEnum n (i, i))).isLt
    exact (Nat.div_le_div_right this.le).trans (by rw [Nat.mul_div_cancel _ h])

open Classical in
/-- The vertex permutation of a diagonal permutation (the identity otherwise). -/
noncomputable def unPair (g : Perm (Fin (n * n))) : Perm (Fin n) :=
  if h : g ∈ (pairHom n).range then Classical.choose h else 1

theorem pairHom_unPair {g : Perm (Fin (n * n))} (h : g ∈ (pairHom n).range) :
    pairHom n (unPair g) = g := by
  rw [unPair, dif_pos h]; exact Classical.choose_spec h

theorem proj_eq_unPair {g : Perm (Fin (n * n))} (h : g ∈ (pairHom n).range) (i : Fin n) :
    proj g i = unPair g i := by
  conv_lhs => rw [← pairHom_unPair h]
  exact proj_pairHom _ i

/-- **The projected generators generate `Aut(G)`.** If `gs` generates the image of `Aut(G)`,
the projections of `1, gs` generate `Aut(G)`. -/
theorem closure_unPair {G : SimpleGraph (Fin n)} {gs : List (Perm (Fin (n * n)))}
    (h : gens gs = (GI.Statement.autGroup G).map (pairHom n)) :
    Subgroup.closure {a | a ∈ (1 :: gs).map unPair} = GI.Statement.autGroup G := by
  have hr : ∀ g ∈ 1 :: gs, g ∈ (pairHom n).range := by
    intro g hg
    have : g ∈ gens (1 :: gs) := Subgroup.subset_closure hg
    rw [gens_one_cons, h] at this
    obtain ⟨a, -, rfl⟩ := this
    exact ⟨a, rfl⟩
  refine Subgroup.map_injective (pairHom_injective (n := n)) ?_
  rw [MonoidHom.map_closure, ← h, ← gens_one_cons, gens]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨g', hg', rfl⟩, rfl⟩
    rw [pairHom_unPair (hr g' hg')]; exact hg'
  · intro hg
    exact ⟨_, ⟨g, hg, rfl⟩, pairHom_unPair (hr g hg)⟩

end GI.Assembly
