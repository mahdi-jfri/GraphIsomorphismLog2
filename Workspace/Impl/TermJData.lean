module

public import Workspace.Impl.TermJAlg

@[expose] public section

/-!
# The data of the `J`-step from the tables (mathematics)

* `tmJ_coset_of_subgroup`: a subgroup written as a left coset `x ⟨gs⟩` is `⟨gs⟩`, and `x` lies in
  it. The stored answers `Aut_N(x_a) = Iso_N(x_a, x_a)` of the `N`-test table are of this form.
* `tmJ_wreath_gens`: generators of `N ≀ Sym(q)`: `(n at a; 1)` for `n` in a generating list of
  `N`, and the pure transpositions `(1; (a a'))` (`tmJ_young_eq` for a constant string).
* `tmJ_ansC_of`: the output value on `Fin (m q)`: if the piece is `t₀ ⟨S⟩` on `Fin m × [q]` and
  `gs` generates the image of `⟨S⟩` under the numbering `finProdFinEquiv`, then
  `[t₀, gs]` is a canonical answer for `tmJSet` of the piece.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

/-- **A subgroup written as a left coset of a generated subgroup is that subgroup.** -/
theorem tmJ_coset_of_subgroup {G : Type} [Group G] {A K : Subgroup G} {x : G}
    (h : (A : Set G) = (x * ·) '' (K : Set G)) : K = A ∧ x ∈ A := by
  have hxA : x ∈ A := by
    have : x * 1 ∈ (x * ·) '' (K : Set G) := ⟨1, K.one_mem, rfl⟩
    rw [← h, mul_one] at this; exact this
  have hx1 : x⁻¹ ∈ K := by
    have : (1 : G) ∈ (x * ·) '' (K : Set G) := by rw [← h]; exact A.one_mem
    obtain ⟨k, hk, he⟩ := this
    have : x⁻¹ = k := by simp only at he; exact (eq_inv_of_mul_eq_one_right he).symm
    rw [this]; exact hk
  refine ⟨?_, hxA⟩
  ext g
  constructor
  · intro hg
    have : x * g ∈ (A : Set G) := by rw [h]; exact ⟨g, hg, rfl⟩
    have := A.mul_mem (A.inv_mem hxA) this
    rwa [inv_mul_cancel_left] at this
  · intro hg
    have : x * (x⁻¹ * g) ∈ (A : Set G) := by rw [mul_inv_cancel_left]; exact hg
    rw [h] at this
    obtain ⟨k, hk, he⟩ := this
    simp only [mul_right_inj] at he
    have : g = x * k := by rw [he]; group
    rw [this]; exact K.mul_mem (K.inv_mem hx1 |> fun h => by simpa using h) hk

variable {B : Type} {q : ℕ}

/-- **Generators of `N ≀ Sym(q)`**: `σN` at each coordinate and the pure transpositions. -/
theorem tmJ_wreath_gens (N : Subgroup (Perm B)) (σN : List (Perm B))
    (hN : Subgroup.closure {s | s ∈ σN} = N) :
    Subgroup.closure ({σ | ∃ a, ∃ g ∈ σN, σ = tmJLoc (q := q) a g} ∪
      {σ | ∃ a a' : Fin q, σ = tmJP ((1 : Fin q → Perm B), swap a a')}) = tmJW N := by
  have hY := tmJ_young_eq N (fun (_ : Fin q) (_ : B) => (0 : ℕ)) (fun _ => σN)
    (fun _ => by
      rw [hN]; ext s
      exact ⟨fun hs => ⟨hs, rfl⟩, fun hs => hs.1⟩)
    ((List.finRange q).flatMap fun a => (List.finRange q).map fun a' => (a, a', 1))
    (by
      intro t ht
      simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at ht
      obtain ⟨a, a', rfl⟩ := ht
      exact ⟨N.one_mem, rfl⟩)
    (by
      intro a a' _ _ _
      exact ⟨1, by simp⟩)
  have hstab : tmJStab (tmJStr (fun (_ : Fin q) (_ : B) => (0 : ℕ))) = ⊤ := by
    ext σ; simp only [Subgroup.mem_top, iff_true]; rfl
  rw [hstab, inf_top_eq] at hY
  rw [← hY]
  congr 1
  ext σ
  simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨a, a', rfl⟩
    refine ⟨(a, a', 1), ⟨a, a', rfl⟩, ?_⟩
    simp only [tmJSw, tmJSwD]
    congr 2
    funext i
    simp only [Function.update_apply, inv_one]
    split_ifs <;> simp [Pi.mulSingle_apply]
  · rintro ⟨t, ⟨a, a', rfl⟩, rfl⟩
    refine ⟨a, a', ?_⟩
    simp only [tmJSw, tmJSwD]
    congr 2
    funext i
    simp only [Function.update_apply, inv_one]
    split_ifs <;> simp [Pi.mulSingle_apply]

/-- **The output value.** -/
theorem tmJ_ansC_of {m : ℕ} {T : Set ((Fin q → Perm (Fin m)) × Perm (Fin q))}
    {t0 : Perm (Fin m × Fin q)} {S : Set (Perm (Fin m × Fin q))}
    (hT : tmJP '' T = (t0 * ·) '' (Subgroup.closure S : Set (Perm (Fin m × Fin q))))
    (gs : List (Perm (Fin (m * q))))
    (hgs : gens gs = (Subgroup.closure S).map (toFin finProdFinEquiv).toMonoidHom)
    (hl : gs.length ≤ (m * q) ^ 2) :
    AnsC (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
      (.list [encPerm (toFin finProdFinEquiv t0), encGroup gs]) (tmJSet T) := by
  refine Or.inr ⟨_, gs, rfl, hl, ?_⟩
  rw [tmJSet_eq_image, hT, hgs]
  ext τ
  simp only [Set.mem_image, Set.mem_smul_set, SetLike.mem_coe, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, (map_mul _ _ _).symm⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, map_mul _ _ _⟩

end GI.Impl
