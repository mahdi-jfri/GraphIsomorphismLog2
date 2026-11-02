import Workspace.Impl.CamJohnsonUnique
import Workspace.Impl.CamDefs

/-!
# The Johnson promise for one factor, and combining the coordinates

Steps 9–10 of the reduction of `camProg` (`CamProg.lean`). Fix a Maróti identification `e₀`, a
coordinate `i` and a base point `x₀`. The orbit `O_i` of `x₀` under the factor `camProd e₀ {i}` is
the set of points that agree with `x₀` outside coordinate `i`. Number `O_i` by an injection
`ν : Fin n' → Fin n` and restrict the factor to it; call the result `H`.

* `cam_johnson_promise`: `H` is `Alt(m)` on `k`-sets, through `w ↦ e₀ (ν w) i`. This is the promise
  of `JohnsonInst`.
* `cam_combine`: if, for every `i`, `ι i` is any Johnson identification of `H i` (the output of the
  cited task), then reading each point `x` coordinate by coordinate through `ι i` (at the point of
  `O_i` with the same `i`-th coordinate as `x`) gives an identification `e` with a Maróti
  structure. The proof: `ι i` differs from the promise identification by some `σ i ∈ Sym(m)`
  (`cam_johnson_unique`), so `e` is `e₀` followed by `σ i` in each coordinate
  (`cam_maroti_transport`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ}

theorem cam_mem_camProd_single (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (i : Fin r) {h : Perm (Fin m)} (hh : h ∈ alternatingGroup (Fin m)) :
    camHom e (Pi.mulSingle i h) ∈ camProd e {i} := by
  refine ⟨Pi.mulSingle i h, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_pi]
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using hh
  · simp [hj, Pi.mulSingle_eq_of_ne hj]

/-- **The Johnson promise for one factor on one orbit.** -/
theorem cam_johnson_promise (e₀ : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (i : Fin r) (x₀ : Fin n) {n' : ℕ} (ν : Fin n' → Fin n) (hνi : Function.Injective ν)
    (hν : ∀ y, (∃ w, ν w = y) ↔ ∀ j, j ≠ i → e₀ y j = e₀ x₀ j)
    {H : Subgroup (Perm (Fin n'))}
    (hH : ∀ g, g ∈ H ↔ ∃ t ∈ camProd e₀ {i}, ∀ w, ν (g w) = t (ν w)) :
    ∃ ι₀ : Fin n' ≃ {A : Finset (Fin m) // A.card = k},
      (∀ w, ι₀ w = e₀ (ν w) i) ∧ IsJohnsonId H ι₀ := by
  have hout : ∀ w j, j ≠ i → e₀ (ν w) j = e₀ x₀ j := fun w => (hν (ν w)).mp ⟨w, rfl⟩
  have hinj : Function.Injective fun w => e₀ (ν w) i := by
    intro w w' hw
    apply hνi
    apply e₀.injective
    funext j
    by_cases hj : j = i
    · subst hj; exact hw
    · rw [hout w j hj, hout w' j hj]
  have hsurj : Function.Surjective fun w => e₀ (ν w) i := by
    intro A
    obtain ⟨w, hw⟩ := (hν (e₀.symm (Function.update (e₀ x₀) i A))).mpr fun j hj => by
      simp [Function.update_of_ne hj]
    exact ⟨w, by simp [hw]⟩
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun w => rfl, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨t, ⟨h, hh, rfl⟩, ht⟩ := (hH g).mp hg
    refine ⟨h i, ?_, fun w => ?_⟩
    · have := (Subgroup.mem_pi Set.univ).mp hh i (Set.mem_univ _)
      simpa using this
    · show e₀ (ν (g w)) i = kSetPerm (h i) (e₀ (ν w) i)
      rw [ht w, camHom_apply]
  · rintro ⟨h, hh, hgh⟩
    refine (hH g).mpr ⟨_, cam_mem_camProd_single e₀ i hh, fun w => ?_⟩
    apply e₀.injective
    rw [camHom_apply]
    funext j
    by_cases hj : j = i
    · subst hj
      simpa using hgh w
    · rw [hout _ j hj, Pi.mulSingle_eq_of_ne hj, cam_kSetPerm_one, hout w j hj]
      rfl

/-- **Combining the coordinates.** -/
theorem cam_combine {G : Subgroup (Perm (Fin n))}
    {e₀ : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hM : MarotiStructure G e₀)
    (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) (h6 : m = 6 → k = 1) (x₀ : Fin n)
    (n' : Fin r → ℕ) (ν : ∀ i, Fin (n' i) → Fin n) (hνi : ∀ i, Function.Injective (ν i))
    (hν : ∀ i y, (∃ w, ν i w = y) ↔ ∀ j, j ≠ i → e₀ y j = e₀ x₀ j)
    (H : ∀ i, Subgroup (Perm (Fin (n' i))))
    (hH : ∀ i g, g ∈ H i ↔ ∃ t ∈ camProd e₀ {i}, ∀ w, ν i (g w) = t (ν i w))
    (ι : ∀ i, Fin (n' i) ≃ {A : Finset (Fin m) // A.card = k}) (hι : ∀ i, IsJohnsonId (H i) (ι i))
    (E : Fin n → Fin r → {A : Finset (Fin m) // A.card = k})
    (hE : ∀ x i w, e₀ (ν i w) i = e₀ x i → E x i = ι i w) :
    ∃ e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}),
      (∀ x, e x = E x) ∧ MarotiStructure G e := by
  have hσ : ∀ i, ∃ σ : Perm (Fin m), ∀ w, ι i w = kSetPerm σ (e₀ (ν i w) i) := by
    intro i
    obtain ⟨ι₀, hι₀, hJ⟩ := cam_johnson_promise e₀ i x₀ (ν i) (hνi i) (hν i) (hH i)
    obtain ⟨σ, hσ⟩ := cam_johnson_unique hm hk1 hk h6 hJ (hι i)
    exact ⟨σ, fun w => by rw [hσ, hι₀]⟩
  choose σ hσ using hσ
  refine ⟨e₀.trans (Equiv.piCongrRight fun i => kSetPerm (σ i)), fun x => ?_,
    cam_maroti_transport σ hM⟩
  funext i
  obtain ⟨w, hw⟩ := (hν i (e₀.symm (Function.update (e₀ x₀) i (e₀ x i)))).mpr fun j hj => by
    simp [Function.update_of_ne hj]
  have hwi : e₀ (ν i w) i = e₀ x i := by simp [hw]
  rw [hE x i w hwi, hσ, hwi]
  rfl

end GI.Impl
