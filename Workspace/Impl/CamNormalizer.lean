import Workspace.Cited.MarotiPrimitive
import Workspace.AltAutConjugation

/-!
# The normalizer fact for `Alt(m)` on `k`-sets

Step 10 of the reduction of `camProg` (`CamProg.lean`) needs: for `m ≥ 5`, `m ≠ 6` and `2k < m`,
every permutation `β` of the `k`-sets that normalizes the action of `Alt(m)` comes from a
permutation of `Fin m`. The proof has two steps. First, `β` induces an automorphism of `Alt(m)`,
which is conjugation by some `σ` (`GI.AlternatingAutomorphism.exists_perm_conj`). Second,
`β ∘ σ⁻¹` commutes with `Alt(m)`, and only the identity does (`cam_centralizer_eq_one`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {m k : ℕ}

theorem cam_kSetPerm_apply (h : Perm (Fin m)) (S : {A : Finset (Fin m) // A.card = k}) :
    (kSetPerm h S).1 = S.1.map h.toEmbedding := rfl

theorem cam_kSetPerm_mul (a b : Perm (Fin m)) :
    (kSetPerm (a * b) : Perm {A : Finset (Fin m) // A.card = k}) = kSetPerm a * kSetPerm b := by
  ext S : 1
  apply Subtype.ext
  show S.1.map (a * b).toEmbedding = (S.1.map b.toEmbedding).map a.toEmbedding
  rw [Finset.map_map]
  rfl

theorem cam_kSetPerm_one : (kSetPerm 1 : Perm {A : Finset (Fin m) // A.card = k}) = 1 := by
  ext S x
  simp [cam_kSetPerm_apply]

/-- The action on `k`-sets is faithful for `1 ≤ k < m`. -/
theorem cam_kSetPerm_injective (hk : 1 ≤ k) (hkm : k < m) :
    Function.Injective (kSetPerm (m := m) (k := k)) := by
  intro a b hab
  ext x
  by_contra hne
  set y := b.symm (a x)
  have hxy : x ≠ y := fun h => hne (by
    have hb : b y = a x := b.apply_symm_apply _
    rw [← h] at hb
    rw [hb])
  have hsub : ({x} : Finset (Fin m)) ⊆ Finset.univ.erase y := by
    simpa using hxy
  obtain ⟨s, hxs, hsy, hcard⟩ := Finset.exists_subsuperset_card_eq hsub (by simpa using hk)
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega)
  have hS := congrArg Subtype.val
    (congrArg (fun p : Perm {A : Finset (Fin m) // A.card = k} => p ⟨s, hcard⟩) hab)
  simp only [cam_kSetPerm_apply] at hS
  have h1 : a x ∈ s.map a.toEmbedding := Finset.mem_map_of_mem _ (hxs (Finset.mem_singleton_self _))
  rw [hS, Finset.mem_map_equiv] at h1
  exact (Finset.mem_erase.mp (hsy h1)).1 rfl

/-- Only the identity commutes with the action of `Alt(m)` on `k`-sets, when `2k < m` and
`m ≥ k + 3`. If `γ S = S' ≠ S`, pick `a ∈ S' \ S`, `c ∉ S ∪ S'` and `d ∉ S` with `d ≠ a, c`.
The even permutation `(a d)(a c)` fixes `S` and moves `a` to `c ∉ S'`, so it does not fix `S'`. -/
theorem cam_centralizer_eq_one (hk : 2 * k < m) (hk3 : k + 3 ≤ m)
    (γ : Perm {A : Finset (Fin m) // A.card = k})
    (hγ : ∀ h ∈ alternatingGroup (Fin m), γ * kSetPerm h = kSetPerm h * γ) : γ = 1 := by
  ext S x
  change x ∈ (γ S).1 ↔ x ∈ S.1
  suffices hS : γ S = S by rw [hS]
  by_contra hne
  set S' := γ S
  -- `a ∈ S' \ S`
  obtain ⟨a, haS', haS⟩ : ∃ a ∈ S'.1, a ∉ S.1 := by
    by_contra hall
    push Not at hall
    exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hall (by rw [S.2, S'.2])))
  -- `c ∉ S ∪ S'`
  obtain ⟨c, hc⟩ : ∃ c, c ∉ S.1 ∪ S'.1 := by
    by_contra hall
    push Not at hall
    have h1 : (Finset.univ : Finset (Fin m)) ⊆ S.1 ∪ S'.1 := fun y _ => hall y
    have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
    rw [Finset.card_univ, Fintype.card_fin, S.2, S'.2] at h2
    omega
  rw [Finset.mem_union, not_or] at hc
  have hac : a ≠ c := fun h => hc.2 (h ▸ haS')
  -- `d ∉ S ∪ {a, c}`
  obtain ⟨d, hd⟩ : ∃ d, d ∉ insert a (insert c S.1) := by
    by_contra hall
    push Not at hall
    have h1 : (Finset.univ : Finset (Fin m)) ⊆ insert a (insert c S.1) := fun y _ => hall y
    have h2 := (Finset.card_le_card h1).trans
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _)))
    rw [Finset.card_univ, Fintype.card_fin, S.2] at h2
    omega
  simp only [Finset.mem_insert, not_or] at hd
  obtain ⟨hda, hdc, hdS⟩ := hd
  set h : Perm (Fin m) := swap a d * swap a c
  have hh : h ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hda),
      Equiv.Perm.sign_swap hac]
    rfl
  have hfix : ∀ y ∈ S.1, h y = y := by
    intro y hy
    have hya : y ≠ a := fun e => haS (e ▸ hy)
    have hyc : y ≠ c := fun e => hc.1 (e ▸ hy)
    have hyd : y ≠ d := fun e => hdS (e ▸ hy)
    simp [h, swap_apply_of_ne_of_ne hya hyc, swap_apply_of_ne_of_ne hya hyd]
  have hhS : kSetPerm h S = S := by
    apply Subtype.ext
    ext y
    rw [cam_kSetPerm_apply, Finset.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : h z = z := hfix z hz
      simpa [this] using hz
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  have hhS' : kSetPerm h S' = S' := by
    have := congrArg (fun p : Perm _ => p S) (hγ h hh)
    simp only [Equiv.Perm.mul_apply, hhS] at this
    exact this.symm
  have hca : h a = c := by
    simp [h, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hdc)]
  have : c ∈ (kSetPerm h S').1 := by
    rw [cam_kSetPerm_apply]
    exact hca ▸ Finset.mem_map_of_mem _ haS'
  rw [hhS'] at this
  exact hc.2 this

/-- **The normalizer fact** (step 10 of `camProg`). For `m = 5` or `m ≥ 7`, and
`1 ≤ k`, `2k < m`, every permutation `β` of the `k`-sets that conjugates each element of
`Alt(m)` to an element of `Alt(m)` is the action of a permutation of `Fin m`. -/
theorem cam_normalizer (hm : m = 5 ∨ 7 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m)
    (β : Perm {A : Finset (Fin m) // A.card = k})
    (hβ : ∀ h ∈ alternatingGroup (Fin m), ∃ h' ∈ alternatingGroup (Fin m),
      β * kSetPerm h * β⁻¹ = kSetPerm h') :
    ∃ σ : Perm (Fin m), β = kSetPerm σ := by
  have hkm : k < m := by omega
  have hinj := cam_kSetPerm_injective (m := m) hk1 hkm
  choose f hfA hf using fun h : alternatingGroup (Fin m) => hβ h.1 h.2
  let F : alternatingGroup (Fin m) →* alternatingGroup (Fin m) :=
    { toFun := fun h => ⟨f h, hfA h⟩
      map_one' := by
        apply Subtype.ext
        apply hinj
        show kSetPerm (f 1) = kSetPerm ((1 : alternatingGroup (Fin m)) : Perm (Fin m))
        rw [← hf]
        simp [cam_kSetPerm_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        apply hinj
        show kSetPerm (f (a * b)) = kSetPerm (f a * f b)
        rw [cam_kSetPerm_mul, ← hf, ← hf, ← hf, Subgroup.coe_mul, cam_kSetPerm_mul]
        group }
  have hFinj : Function.Injective F := by
    intro a b hab
    have hab' : f a = f b := congrArg Subtype.val hab
    apply Subtype.ext
    apply hinj
    have ha := hf a
    have hb := hf b
    rw [hab', ← hb] at ha
    have := congrArg (fun p => β⁻¹ * p * β) ha
    simpa [mul_assoc] using this
  let Faut : MulAut (alternatingGroup (Fin m)) :=
    MulEquiv.ofBijective F ⟨hFinj, Finite.surjective_of_injective hFinj⟩
  obtain ⟨σ, hσ⟩ := GI.AlternatingAutomorphism.exists_perm_conj (by simpa using hm) Faut
  refine ⟨σ, ?_⟩
  have hγ := cam_centralizer_eq_one hk (by omega) ((kSetPerm σ)⁻¹ * β) fun h hh => by
    have e1 := hf ⟨h, hh⟩
    have e2 : f ⟨h, hh⟩ = σ * h * σ⁻¹ := hσ ⟨h, hh⟩
    rw [e2, cam_kSetPerm_mul, cam_kSetPerm_mul] at e1
    have hσinv : (kSetPerm σ⁻¹ : Perm {A : Finset (Fin m) // A.card = k}) = (kSetPerm σ)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← cam_kSetPerm_mul, inv_mul_cancel, cam_kSetPerm_one]
    rw [hσinv] at e1
    -- `β ρ(h) β⁻¹ = ρ(σ) ρ(h) ρ(σ)⁻¹`
    calc (kSetPerm σ)⁻¹ * β * kSetPerm h
        = (kSetPerm σ)⁻¹ * (β * kSetPerm h * β⁻¹) * β := by group
      _ = (kSetPerm σ)⁻¹ * (kSetPerm σ * kSetPerm h * (kSetPerm σ)⁻¹) * β := by rw [e1]
      _ = kSetPerm h * ((kSetPerm σ)⁻¹ * β) := by group
  rw [inv_mul_eq_one] at hγ
  exact hγ.symm

end GI.Impl
