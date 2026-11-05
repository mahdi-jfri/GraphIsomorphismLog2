module

public import Workspace.Impl.AggItemCiCfgMo

@[expose] public section

/-!
# The configuration query: extending a map of the fibers

For two pair configurations `X`, `Y` with fibers of the same size `n`:
* `itciE0 X Y`: the permutation of `Fin q` that maps the `i`-th point of the fiber of `X` to the
  `i`-th point of the fiber of `Y` (in increasing order), and entry `k` of the outer points of
  `X` by color (`itciFo X`) to entry `k` of `itciFo Y`. When the outer classes can be aligned
  (`ItciAl X Y`), this maps each outer class of `X` onto the class of `Y` with the same color;
* `itciLift X a`: the permutation `a` of `Fin n` acting on the fiber of `X` through its
  numbering, and fixing the other points (a group homomorphism);
* `itciExt X Y hc p = itciE0 X Y * itciLift X p`: maps the `i`-th point of the fiber of `X` to
  the `p i`-th point of the fiber of `Y`. It maps `X` to `Y` (`PairCfg.Maps`) when `p` keeps the
  pair colors and the outer classes can be aligned (`itci_ext_maps`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

noncomputable section

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset

variable {q : ℕ}

/-! ### The fiber, then the other points -/

/-- The points of the fiber of `X` in increasing order, then the outer points by color. -/
def itciL (X : PairCfg q) : List (Fin q) := itciFl X.fiber ++ itciFo X

theorem itciL_length (X : PairCfg q) : (itciL X).length = q := by
  rw [itciL, List.length_append, itciFl_length, itciFo_length, Finset.card_add_card_compl,
    Fintype.card_fin]

theorem itciL_nodup (X : PairCfg q) : (itciL X).Nodup := by
  refine List.Nodup.append (itciFl_nodup _) (itciFo_nodup _) ?_
  intro a ha hb
  rw [itci_mem_fl] at ha
  rw [itci_mem_fo] at hb
  exact hb ha

/-- The enumeration `t ↦ (itciL X)[t]` as a permutation. -/
def itciEnum (X : PairCfg q) : Perm (Fin q) :=
  Equiv.ofBijective (fun t : Fin q => (itciL X)[t.1]'(by rw [itciL_length]; exact t.2))
    (Finite.injective_iff_bijective.1 fun t t' h =>
      Fin.ext ((List.Nodup.getElem_inj_iff (itciL_nodup X)).1 h))

theorem itciEnum_apply (X : PairCfg q) (t : Fin q) :
    itciEnum X t = (itciL X)[t.1]'(by rw [itciL_length]; exact t.2) := rfl

/-- Entry `t` of `itciL X` lies in the fiber exactly when `t < n`. -/
theorem itciL_mem_fiber (X : PairCfg q) (t : ℕ) (ht : t < (itciL X).length) :
    (itciL X)[t] ∈ X.fiber ↔ t < X.fiber.card := by
  have hl := itciFl_length X.fiber
  by_cases h : t < (itciFl X.fiber).length
  · simp only [itciL]; rw [List.getElem_append_left h]
    have := List.getElem_mem h
    rw [itci_mem_fl] at this
    exact ⟨fun _ => hl ▸ h, fun _ => this⟩
  · simp only [itciL]; rw [List.getElem_append_right (by omega)]
    have := List.getElem_mem (l := itciFo X) (n := t - (itciFl X.fiber).length)
      (by have := itciL_length X; rw [itciL, List.length_append] at ht; omega)
    rw [itci_mem_fo] at this
    exact ⟨fun h' => absurd h' this, fun h' => by omega⟩

theorem itciEnum_fiber (X : PairCfg q) (t : Fin q) :
    itciEnum X t ∈ X.fiber ↔ t.1 < X.fiber.card :=
  itciL_mem_fiber X t.1 _

theorem itciEnum_emb (X : PairCfg q) {n : ℕ} (h : X.fiber.card = n) (i : Fin n) :
    itciEnum X ⟨i.1, by have := X.fiber.card_le_univ; simp at this; omega⟩ = X.emb h i := by
  rw [itciEnum_apply, itci_emb_eq]
  have hi : i.1 < (itciFl X.fiber).length := by rw [itciFl_length, h]; exact i.2
  simp only [itciL]
  exact List.getElem_append_left hi

/-- Entry `n + k` of the enumeration, with `n` the size of the fiber, is entry `k` of
`itciFo X`. -/
theorem itciEnum_out (X : PairCfg q) (t : Fin q) (k : ℕ) (hk : X.fiber.card + k = t.1) :
    itciEnum X t = (itciFo X)[k]'(by
      have := itciL_length X; rw [itciL, List.length_append, itciFl_length] at this; omega) := by
  rw [itciEnum_apply]
  simp only [itciL]
  rw [List.getElem_append_right (by rw [itciFl_length]; omega)]
  simp only [itciFl_length, ← hk, Nat.add_sub_cancel_left]

/-! ### Mapping the fiber in order -/

/-- The order-preserving map of the fibers and of the other points. -/
def itciE0 (X Y : PairCfg q) : Perm (Fin q) := itciEnum Y * (itciEnum X)⁻¹

theorem itciE0_emb {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card) (i : Fin X.fiber.card) :
    itciE0 X Y (X.emb rfl i) = Y.emb hc.symm i := by
  have hq : X.fiber.card ≤ q := by have := X.fiber.card_le_univ; simpa using this
  rw [itciE0, Perm.mul_apply, ← itciEnum_emb X rfl i, Perm.inv_apply_self,
    itciEnum_emb Y hc.symm i]

theorem itciE0_fiber {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card) (a : Fin q) :
    itciE0 X Y a ∈ Y.fiber ↔ a ∈ X.fiber := by
  rw [itciE0, Perm.mul_apply, itciEnum_fiber, ← hc]
  conv_rhs => rw [← Perm.apply_inv_self (itciEnum X) a]
  rw [itciEnum_fiber]

/-! ### Lifting a permutation of the fiber -/

/-- The numbering of the fiber, as an equivalence. -/
def itciFE (X : PairCfg q) : Fin X.fiber.card ≃ {a // a ∈ X.fiber} :=
  (X.fiber.orderIsoOfFin rfl).toEquiv

/-- **The lift of a permutation of the fiber**: it acts on the fiber of `X` through the
numbering and fixes the other points. -/
def itciLift (X : PairCfg q) : Perm (Fin X.fiber.card) →* Perm (Fin q) :=
  Perm.ofSubtype.comp (permCongrHom (itciFE X)).toMonoidHom

theorem itciLift_emb (X : PairCfg q) (a : Perm (Fin X.fiber.card)) (i : Fin X.fiber.card) :
    itciLift X a (X.emb rfl i) = X.emb rfl (a i) := by
  show Perm.ofSubtype ((itciFE X).permCongr a) ((itciFE X i : {a // a ∈ X.fiber}) : Fin q) =
    ((itciFE X (a i) : {a // a ∈ X.fiber}) : Fin q)
  rw [Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem itciLift_out (X : PairCfg q) (a : Perm (Fin X.fiber.card)) {b : Fin q}
    (hb : b ∉ X.fiber) : itciLift X a b = b := by
  simp only [itciLift, MonoidHom.coe_comp, Function.comp_apply]
  exact Perm.ofSubtype_apply_of_not_mem _ hb

theorem itciLift_fiber (X : PairCfg q) (a : Perm (Fin X.fiber.card)) (b : Fin q) :
    itciLift X a b ∈ X.fiber ↔ b ∈ X.fiber := by
  by_cases hb : b ∈ X.fiber
  · obtain ⟨i, rfl⟩ := X.exists_emb rfl hb
    rw [itciLift_emb]; exact ⟨fun _ => X.emb_mem rfl i, fun _ => X.emb_mem rfl _⟩
  · rw [itciLift_out X a hb]

/-! ### Extending a map of the fibers -/

/-- **The extension of a map `p` of the fibers**. -/
def itciExt (X Y : PairCfg q) (p : Perm (Fin X.fiber.card)) : Perm (Fin q) :=
  itciE0 X Y * itciLift X p

theorem itciExt_emb {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card)
    (p : Perm (Fin X.fiber.card)) (i : Fin X.fiber.card) :
    itciExt X Y p (X.emb rfl i) = Y.emb hc.symm (p i) := by
  rw [itciExt, Perm.mul_apply, itciLift_emb, itciE0_emb hc]

theorem itciExt_fiber {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card)
    (p : Perm (Fin X.fiber.card)) (a : Fin q) :
    itciExt X Y p a ∈ Y.fiber ↔ a ∈ X.fiber := by
  rw [itciExt, Perm.mul_apply, itciE0_fiber hc, itciLift_fiber]

/-- `p` keeps the pair colors from `X` to `Y` (the answer of the pair-structure call). -/
def ItciKeeps (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card)
    (p : Perm (Fin X.fiber.card)) : Prop :=
  ∀ i k, Y.col (Y.emb hc.symm (p i)) (Y.emb hc.symm (p k)) = X.col (X.emb rfl i) (X.emb rfl k)

/-- **The extension maps `X` to `Y`**: on the fiber by `p`, and each outer class of `X` onto
the class of `Y` with the same color ("align those classes", Lemma A.12). -/
theorem itci_ext_maps {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card)
    {p : Perm (Fin X.fiber.card)} (hp : ItciKeeps X Y hc p) (hal : ItciAl X Y) :
    PairCfg.Maps X Y (itciExt X Y p) := by
  refine ⟨itciExt_fiber hc p, fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨i, rfl⟩ := X.exists_emb rfl ha
    obtain ⟨k, rfl⟩ := X.exists_emb rfl hb
    rw [itciExt_emb hc, itciExt_emb hc]
    exact hp i k
  · -- `a` is entry `k` of `itciFo X`, and it goes to entry `k` of `itciFo Y`
    have hat : itciEnum X ((itciEnum X)⁻¹ a) = a := Perm.apply_inv_self _ a
    have hle : X.fiber.card ≤ ((itciEnum X)⁻¹ a).1 := by
      by_contra h
      exact ha (hat ▸ (itciEnum_fiber X _).2 (by omega))
    have e1 := itciEnum_out X ((itciEnum X)⁻¹ a) _ (Nat.add_sub_cancel' hle)
    have e2 := itciEnum_out Y ((itciEnum X)⁻¹ a) (((itciEnum X)⁻¹ a).1 - X.fiber.card)
      (by rw [← hc]; exact Nat.add_sub_cancel' hle)
    rw [itciExt, Perm.mul_apply, itciLift_out X p ha, itciE0, Perm.mul_apply, e2]
    conv_rhs => rw [← hat, e1]
    exact itci_al_get hal _ _ _

end

end GI.Impl
