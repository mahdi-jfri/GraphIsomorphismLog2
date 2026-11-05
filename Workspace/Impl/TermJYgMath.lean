module

public import Workspace.Impl.TermJData

@[expose] public section

/-!
# The generators of `Aut_{N ≀ Sym(q)}(X)` read off the `N`-test table

The `N`-test table stores, for rows `a, a'` of `x`, the coset `Iso_N(x_a, x_{a'})`: empty, or
`b ⟨gs⟩`. We record this as `O a a' : Option (Perm B × List (Perm B))`. The program
(`TermJProgYg.lean`) outputs `tmJYgList O`:

* for every row `a`, with `O a a = some (r, gs)`: `(s⁻¹ at a; 1)` for `s ∈ 1 :: gs`;
* for every `t < q²`, with `a = t / q`, `a' = t % q`: the lifted transposition `tmJSw a a' b`
  if `O a a' = some (b, _)`, else `1`.

`tmJYgList_closure`: these generate `Aut_{N ≀ Sym(q)}(X)` (from `tmJ_young_eq`; the extra
identities and the inverses do not change the closure).
-/

namespace GI.Impl

open Equiv Equiv.Perm

variable {B : Type} {q : ℕ}

/-- The locals of row `a`. -/
def tmJYgLoc (O : Fin q → Fin q → Option (Perm B × List (Perm B))) (a : Fin q) :
    List (Perm (B × Fin q)) :=
  match O a a with
  | some (_, gs) => (1 :: gs).map fun s => tmJLoc a s⁻¹
  | none => []

/-- The first index of `t < q²`: `t / q`. -/
def tmJFst (t : Fin (q * q)) : Fin q :=
  ⟨t / q, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (by rintro rfl; exact t.elim0))).2 t.2⟩

/-- The second index of `t < q²`: `t % q`. -/
def tmJSnd (t : Fin (q * q)) : Fin q :=
  ⟨t % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact t.elim0))⟩

/-- The lifted transposition of the index `t`, or `1`. -/
def tmJYgSw (O : Fin q → Fin q → Option (Perm B × List (Perm B))) (t : Fin (q * q)) :
    Perm (B × Fin q) :=
  match O (tmJFst t) (tmJSnd t) with
  | some (b, _) => tmJSw (tmJFst t) (tmJSnd t) b
  | none => 1

/-- The generators read off the table. -/
def tmJYgList (O : Fin q → Fin q → Option (Perm B × List (Perm B))) : List (Perm (B × Fin q)) :=
  ((List.finRange q).map (tmJYgLoc O)).flatten ++ (List.finRange (q * q)).map (tmJYgSw O)

variable {C : Type} (N : Subgroup (Perm B)) (x : Fin q → B → C)

/-- **The generators read off the table generate `Aut_{N ≀ Sym(q)}(X)`.** -/
theorem tmJYgList_closure (O : Fin q → Fin q → Option (Perm B × List (Perm B)))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs) ∧
      Subgroup.closure {s | s ∈ gs} = tmJRowAut N (x a))
    (hsome : ∀ a a' b gs, O a a' = some (b, gs) → b ∈ N ∧ x a ∘ b = x a')
    (hnone : ∀ a a', O a a' = none → ∀ b ∈ N, x a ∘ b ≠ x a') :
    Subgroup.closure {σ | σ ∈ tmJYgList O} = tmJW N ⊓ tmJStab (tmJStr x) := by
  choose r gs hO hgs using hloc
  -- the data of `tmJ_young_eq`
  set ls : Fin q → List (Perm B) := fun a => (gs a).map (·⁻¹) with hls
  have hls' : ∀ a, Subgroup.closure {s | s ∈ ls a} = tmJRowAut N (x a) := by
    intro a
    have : {s | s ∈ ls a} = ({g | g ∈ gs a} : Set (Perm B))⁻¹ := by
      ext s; simp only [hls, List.mem_map, Set.mem_setOf_eq, Set.mem_inv]
      constructor
      · rintro ⟨g, hg, rfl⟩; simpa using hg
      · intro hs; exact ⟨s⁻¹, hs, inv_inv s⟩
    rw [this, Subgroup.closure_inv, hgs]
  have hq0 : ∀ t : Fin (q * q), 0 < q := fun t => Nat.pos_of_ne_zero (by rintro rfl; exact t.elim0)
  set trs : List (Fin q × Fin q × Perm B) := (List.finRange q).flatMap fun a =>
    (List.finRange q).filterMap fun a' => (O a a').map fun p => (a, a', p.1) with htrs
  have mem_trs : ∀ a a' b, (a, a', b) ∈ trs ↔ ∃ gs', O a a' = some (b, gs') := by
    intro a a' b
    simp only [htrs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
      Option.map_eq_some_iff]
    constructor
    · rintro ⟨a1, a2, ⟨b', gs'⟩, h, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨gs', h⟩
    · rintro ⟨gs', h⟩
      exact ⟨a, a', ⟨b, gs'⟩, h, rfl⟩
  have hY := tmJ_young_eq N x ls hls' trs
    (by
      rintro ⟨a, a', b⟩ ht
      obtain ⟨gs', h⟩ := (mem_trs a a' b).1 ht
      exact hsome a a' b gs' h)
    (by
      intro a a' b hb hx
      cases h : O a a' with
      | none => exact absurd hx (hnone a a' h b hb)
      | some p => exact ⟨p.1, (mem_trs a a' p.1).2 ⟨p.2, by rw [h]⟩⟩)
  rw [← hY]
  -- the two generating sets differ by identities
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro σ hσ
    simp only [tmJYgList, List.mem_append, List.mem_flatten, List.mem_map, List.mem_finRange,
      true_and] at hσ
    rcases hσ with ⟨l, ⟨a, rfl⟩, hσ⟩ | ⟨t, rfl⟩
    · unfold tmJYgLoc at hσ
      rw [hO a] at hσ
      simp only [List.map_cons, List.mem_cons, List.mem_map] at hσ
      rcases hσ with rfl | ⟨s, hs, rfl⟩
      · simp only [inv_one]
        have : tmJLoc a (1 : Perm B) = 1 := by
          unfold tmJLoc; rw [Pi.mulSingle_one]; exact tmJP_one
        rw [this]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Or.inl ⟨a, s⁻¹, List.mem_map.2 ⟨s, hs, rfl⟩, rfl⟩)
    · unfold tmJYgSw
      split
      · next b gs' h =>
        exact Subgroup.subset_closure (Or.inr ⟨_, (mem_trs _ _ b).2 ⟨gs', h⟩, rfl⟩)
      · exact Subgroup.one_mem _
  · rw [Subgroup.closure_le]
    rintro σ (⟨a, g, hg, rfl⟩ | ⟨⟨a, a', b⟩, ht, rfl⟩)
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      refine Subgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq, tmJYgList, List.mem_append, List.mem_flatten, List.mem_map,
        List.mem_finRange, true_and]
      refine Or.inl ⟨tmJYgLoc O a, ⟨a, rfl⟩, ?_⟩
      unfold tmJYgLoc
      rw [hO a]
      exact List.mem_map.2 ⟨s, List.mem_cons_of_mem _ hs, rfl⟩
    · obtain ⟨gs', h⟩ := (mem_trs a a' b).1 ht
      refine Subgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq, tmJYgList, List.mem_append, List.mem_flatten, List.mem_map,
        List.mem_finRange, true_and]
      have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0)
      refine Or.inr ⟨⟨a * q + a', by nlinarith [a.2, a'.2]⟩, ?_⟩
      have h1 : (a * q + a') / q = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt a'.2, zero_add]
      have h2 : (a * q + a') % q = a' := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a'.2]
      have e1 : tmJFst (⟨a * q + a', by nlinarith [a.2, a'.2]⟩ : Fin (q * q)) = a := Fin.ext h1
      have e2 : tmJSnd (⟨a * q + a', by nlinarith [a.2, a'.2]⟩ : Fin (q * q)) = a' := Fin.ext h2
      unfold tmJYgSw
      rw [e1, e2, h]

end GI.Impl
