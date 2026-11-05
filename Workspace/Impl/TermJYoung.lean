module

public import Workspace.Impl.TermJCoset

@[expose] public section

/-!
# Generators of `Aut_{K ≀ Sym(q)}(X)` (the even-Young part of `Aut_J(x)`)

Theorem A.23: "It also constructs `Aut_J(x)`: use the local `N*`-stabilizers, the kernel of the
sum map on the product of local stabilizer images, and lifted generators of the even Young
group on equal-type fibers." The `J`-step builds `Aut_J(x)` from these pieces, with the
zero-sum and parity conditions (`tmJ_autJ_gens`). This file gives generators of
`Aut_{K ≀ Sym(q)}(X)` for a subgroup `K` from local data:

* the **local stabilizers**: `(s at a; 1)` for `s` in a generating list of `Aut_K(x_a)`;
* the **lifted transpositions**: for rows `a, a'` of the same `K`-type with `x_a^b = x_{a'}`,
  `b ∈ K`, the pair `(b at a, b⁻¹ at a'; (a a'))`.

`tmJ_young_eq`: these generate `Aut_{K ≀ Sym(q)}(X)` when every pair of rows of the same type
has a transposition. The proof is the usual one for the Young group: multiply by a lifted
transposition `(a, π a)` to shrink the support of the top permutation, and at the end the pair
is a product of local stabilizers.
-/

namespace GI.Impl

open Equiv Equiv.Perm

variable {B : Type} {q : ℕ}

/-- A local generator: `(g at a; 1)`. -/
def tmJLoc (a : Fin q) (g : Perm B) : Perm (B × Fin q) := tmJP (Pi.mulSingle a g, 1)

/-- The coordinates of a lifted transposition: `b` at `a`, `b⁻¹` at `a'`. -/
def tmJSwD (a a' : Fin q) (b : Perm B) : Fin q → Perm B :=
  Function.update (Pi.mulSingle a b) a' b⁻¹

/-- A lifted transposition: `(b at a, b⁻¹ at a'; (a a'))`. For `a = a'` it is `(b⁻¹ at a; 1)`. -/
def tmJSw (a a' : Fin q) (b : Perm B) : Perm (B × Fin q) :=
  tmJP (tmJSwD a a' b, swap a a')

variable {C : Type} (K : Subgroup (Perm B)) (x : Fin q → B → C)

/-- The `K`-stabilizer of one row. -/
def tmJRowAut (z : B → C) : Subgroup (Perm B) where
  carrier := {s | s ∈ K ∧ z ∘ s = z}
  one_mem' := ⟨K.one_mem, rfl⟩
  mul_mem' := by
    rintro s t ⟨hs, hzs⟩ ⟨ht, hzt⟩
    refine ⟨K.mul_mem hs ht, ?_⟩
    change z ∘ (s ∘ t) = z
    rw [← Function.comp_assoc, hzs, hzt]
  inv_mem' := by
    rintro s ⟨hs, hzs⟩
    refine ⟨K.inv_mem hs, ?_⟩
    change z ∘ ⇑(s⁻¹) = z
    conv_lhs => rw [← hzs]
    funext c; simp

/-- **Generators of `Aut_{K ≀ Sym(q)}(X)`.** `ls a` generates `Aut_K(x_a)`; `trs` lists triples
`(a, a', b)` with `b ∈ K` and `x_a^b = x_{a'}`, at least one for every pair of rows of the same
`K`-type. -/
theorem tmJ_young_eq (ls : Fin q → List (Perm B))
    (hls : ∀ a, Subgroup.closure {s | s ∈ ls a} = tmJRowAut K (x a))
    (trs : List (Fin q × Fin q × Perm B))
    (htr : ∀ t ∈ trs, t.2.2 ∈ K ∧ x t.1 ∘ t.2.2 = x t.2.1)
    (hcomp : ∀ a a', ∀ b ∈ K, x a ∘ b = x a' → ∃ b', (a, a', b') ∈ trs) :
    Subgroup.closure ({σ | ∃ a, ∃ g ∈ ls a, σ = tmJLoc a g} ∪
      {σ | ∃ t ∈ trs, σ = tmJSw t.1 t.2.1 t.2.2}) =
      tmJW K ⊓ tmJStab (tmJStr x) := by
  set Gen := {σ | ∃ a, ∃ g ∈ ls a, σ = tmJLoc (B := B) a g} ∪
      {σ | ∃ t ∈ trs, σ = tmJSw (B := B) t.1 t.2.1 t.2.2}
  have hstab : ∀ p : (Fin q → Perm B) × Perm (Fin q),
      tmJP p ∈ tmJStab (tmJStr x) ↔ ∀ i, x i ∘ p.1 i = x (p.2 i) := fun p => tmJ_mem_iso x x p
  have hrowK : ∀ a, ∀ g ∈ ls a, g ∈ K ∧ x a ∘ g = x a := by
    intro a g hg
    have : g ∈ tmJRowAut K (x a) := by rw [← hls]; exact Subgroup.subset_closure hg
    exact this
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro σ (⟨a, g, hg, rfl⟩ | ⟨⟨a, a', b⟩, ht, rfl⟩)
    · obtain ⟨hgK, hxg⟩ := hrowK a g hg
      refine ⟨⟨_, fun i => ?_, rfl⟩, (hstab _).2 fun i => ?_⟩
      · by_cases hi : i = a
        · subst hi; simpa using hgK
        · simp [Pi.mulSingle_eq_of_ne hi, K.one_mem]
      · by_cases hi : i = a
        · subst hi; simpa using hxg
        · simp [Pi.mulSingle_eq_of_ne hi]
    · obtain ⟨hbK, hxb⟩ := htr _ ht
      simp only at hbK hxb
      refine ⟨⟨_, fun i => ?_, rfl⟩, (hstab _).2 fun i => ?_⟩
      · simp only [tmJSwD, Function.update_apply]
        split_ifs with h1
        · exact K.inv_mem hbK
        · by_cases hi : i = a
          · subst hi; simpa using hbK
          · simp [Pi.mulSingle_eq_of_ne hi, K.one_mem]
      · simp only [tmJSwD, Function.update_apply]
        split_ifs with h1
        · subst h1
          rw [swap_apply_right, ← hxb]
          funext c; simp
        · by_cases hi : i = a
          · subst hi; simpa [swap_apply_left] using hxb
          · simp [Pi.mulSingle_eq_of_ne hi, swap_apply_of_ne_of_ne hi h1]
  · -- the pairs with trivial top permutation
    have hψ : ∀ d : Fin q → Perm B, (∀ i, d i ∈ tmJRowAut K (x i)) →
        tmJP (d, 1) ∈ Subgroup.closure Gen := by
      let ψ : (Fin q → Perm B) →* Perm (B × Fin q) :=
        { toFun := fun d => tmJP (d⁻¹, 1)
          map_one' := by simpa using tmJP_one (B := B) (q := q)
          map_mul' := fun d d' => by
            rw [tmJP_mul]; congr 1 }
      have hle : Subgroup.pi Set.univ (fun i => tmJRowAut K (x i)) ≤
          (Subgroup.closure Gen).comap ψ := by
        rw [Subgroup.pi_le_iff]
        intro i
        rw [← hls i, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨g, hg, rfl⟩
        change ψ (Pi.mulSingle i g) ∈ Subgroup.closure Gen
        have hgen : tmJLoc i g ∈ Subgroup.closure Gen :=
          Subgroup.subset_closure (Or.inl ⟨i, g, hg, rfl⟩)
        have : ψ (Pi.mulSingle i g) = (tmJLoc i g)⁻¹ := by
          change tmJP ((Pi.mulSingle i g)⁻¹, 1) = (tmJP (Pi.mulSingle i g, 1))⁻¹
          rw [tmJP_inv]; congr 1
        rw [this]; exact Subgroup.inv_mem _ hgen
      intro d hd
      have hd' : d⁻¹ ∈ Subgroup.pi Set.univ (fun i => tmJRowAut K (x i)) :=
        fun i _ => (tmJRowAut K (x i)).inv_mem (hd i)
      have := Subgroup.mem_comap.1 (hle hd')
      change tmJP ((d⁻¹)⁻¹, 1) ∈ _ at this
      rwa [inv_inv] at this
    -- induction on the support of the top permutation
    suffices h : ∀ n, ∀ p : (Fin q → Perm B) × Perm (Fin q), p.2.support.card = n →
        (∀ i, p.1 i ∈ K) → (∀ i, x i ∘ p.1 i = x (p.2 i)) → tmJP p ∈ Subgroup.closure Gen by
      rintro σ ⟨⟨p, hpK, rfl⟩, hσ⟩
      exact h _ p rfl hpK ((hstab p).1 hσ)
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro ⟨d, π⟩ hn hK hx
      simp only at hn hK hx
      by_cases hπ : π = 1
      · subst hπ
        exact hψ d fun i => ⟨hK i, by simpa using hx i⟩
      · obtain ⟨a, ha⟩ : ∃ a, π a ≠ a := by
          by_contra hcon; push Not at hcon; exact hπ (Equiv.ext hcon)
        obtain ⟨b, hb⟩ := hcomp a (π a) (d a) (hK a) (hx a)
        obtain ⟨hbK, hxb⟩ := htr _ hb
        simp only at hbK hxb
        set τ := tmJSw (B := B) a (π a) b
        have hτ : τ ∈ Subgroup.closure Gen :=
          Subgroup.subset_closure (Or.inr ⟨_, hb, rfl⟩)
        -- `τ σ` has top permutation `(a, π a) π`, with a smaller support
        have hprod : τ * tmJP (d, π) = tmJP (fun i => d i *
            (tmJSwD a (π a) b) (π i), swap a (π a) * π) := by
          simp only [τ, tmJSw]; rw [tmJP_mul]
        have hτK : ∀ i, (tmJSwD a (π a) b) i ∈ K := by
          intro i
          simp only [tmJSwD, Function.update_apply]
          split_ifs with h1
          · exact K.inv_mem hbK
          · by_cases hi : i = a
            · subst hi; simpa using hbK
            · simp [Pi.mulSingle_eq_of_ne hi, K.one_mem]
        have hτX : ∀ i, x i ∘ (tmJSwD a (π a) b) i =
            x (swap a (π a) i) := by
          intro i
          simp only [tmJSwD, Function.update_apply]
          split_ifs with h1
          · subst h1
            rw [swap_apply_right, ← hxb]
            funext c; simp
          · by_cases hi : i = a
            · subst hi; simpa [swap_apply_left] using hxb
            · simp [Pi.mulSingle_eq_of_ne hi, swap_apply_of_ne_of_ne hi h1]
        have hrest : tmJP (fun i => d i *
            (tmJSwD a (π a) b) (π i), swap a (π a) * π) ∈
            Subgroup.closure Gen := by
          refine ih _ ?_ _ rfl (fun i => K.mul_mem (hK i) (hτK _)) (fun i => ?_)
          · rw [← hn]; exact card_support_swap_mul ha
          · simp only [Perm.mul_apply]
            rw [coe_mul, ← Function.comp_assoc, hx i, hτX]
        have : tmJP (d, π) = τ⁻¹ * (τ * tmJP (d, π)) := by group
        rw [this, hprod]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hτ) hrest

end GI.Impl
