module

public import Workspace.Impl.VsQInd
public import Workspace.Lang.Prims.PermGroups

@[expose] public section

/-!
# The stabilizer from an orbit list

Let `H = ⟨gs⟩ ≤ K` act on `Y` through `α` (an action of `K`), and let `L` list the orbit of
`y₀` without repeats, `L[0] = (y₀, 1)`. Number the orbit points by their positions in `L`;
then `H` acts on `Fin m` (`m = |L|`) by `π`. The graph map
`ρ h = h ⊕ π(h)` (on `Fin (n + m)`) is an injective homomorphism, and `ρ h` fixes the point `n`
exactly when `h` fixes `y₀`. So the stabilizer of `n` in `⟨ρ gs⟩` (one call of the pointwise
stabilizer task) is `ρ(H_{y₀})`, and the first `n` entries of its generators generate `H_{y₀}`
(`vsQ_stab_gens`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

variable {n : ℕ} {Y : Type} {K : Subgroup (Perm (Fin n))} {α : Perm (Fin n) → Y → Y}
  {gs : List (Perm (Fin n))} {y₀ : Y}

/-- The orbit list. -/
structure VsQOrbL (α : Perm (Fin n) → Y → Y) (gs : List (Perm (Fin n))) (y₀ : Y)
    (L : List (Y × Perm (Fin n))) : Prop where
  nodup : (L.map Prod.fst).Nodup
  mem : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ vsQOrb α gs y₀
  pr : ∀ p ∈ L, p.2 ∈ genGroup gs ∧ α p.2 y₀ = p.1
  hd : L.head? = some (y₀, 1)

section

variable (hα : VsQPAct K α) (hK : genGroup gs ≤ K) {L : List (Y × Perm (Fin n))}
  (hL : VsQOrbL α gs y₀ L)
include hα hK

theorem vsQOrb_act {h : Perm (Fin n)} (hh : h ∈ genGroup gs) {y : Y}
    (hy : y ∈ vsQOrb α gs y₀) : α h y ∈ vsQOrb α gs y₀ := by
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨h * g, (genGroup gs).mul_mem hh hg, hα.mul _ (hK hh) _ (hK hg) _⟩

include hL

/-- The position of an orbit point. -/
def vsQPos (L : List (Y × Perm (Fin n))) [DecidableEq Y] (y : Y) : ℕ := (L.map Prod.fst).idxOf y

theorem vsQPos_lt [DecidableEq Y] {y : Y} (hy : y ∈ vsQOrb α gs y₀) : vsQPos L y < L.length := by
  have := List.idxOf_lt_length_iff.mpr ((hL.mem y).mpr hy)
  simpa [vsQPos] using this

theorem vsQPos_get [DecidableEq Y] (i : Fin L.length) : vsQPos L (L[i]).1 = i := by
  unfold vsQPos
  have := hL.nodup.idxOf_getElem i (by simp)
  simpa using this

theorem vsQ_get_mem (i : Fin L.length) : (L[i]).1 ∈ vsQOrb α gs y₀ :=
  (hL.mem _).mp (List.mem_map.mpr ⟨L[i], List.getElem_mem _, rfl⟩)

theorem vsQ_get_pos [DecidableEq Y] {y : Y} (hy : y ∈ vsQOrb α gs y₀) :
    (L[vsQPos L y]'(vsQPos_lt hα hK hL hy)).1 = y := by
  have h1 : (L.map Prod.fst)[vsQPos L y]'(by simpa using vsQPos_lt hα hK hL hy) = y :=
    List.getElem_idxOf _
  simpa using h1

theorem vsQ_inv_act {h : Perm (Fin n)} (hh : h ∈ K) (y : Y) : α h⁻¹ (α h y) = y := by
  rw [← hα.mul _ (K.inv_mem hh) _ hh, inv_mul_cancel, hα.one]

open Classical in
/-- The map of positions induced by `h`. -/
noncomputable def vsQPiF (h : genGroup gs) (i : Fin L.length) : Fin L.length :=
  ⟨vsQPos L (α h (L[i]).1), vsQPos_lt hα hK hL (vsQOrb_act hα hK h.2 (vsQ_get_mem hα hK hL i))⟩

theorem vsQPiF_get (h : genGroup gs) (i : Fin L.length) :
    (L[(vsQPiF hα hK hL h i : ℕ)]).1 = α h (L[i]).1 := by
  classical
  exact vsQ_get_pos hα hK hL (vsQOrb_act hα hK h.2 (vsQ_get_mem hα hK hL i))

theorem vsQPiF_mul (a b : genGroup gs) (i : Fin L.length) :
    vsQPiF hα hK hL (a * b) i = vsQPiF hα hK hL a (vsQPiF hα hK hL b i) := by
  classical
  apply Fin.ext
  show vsQPos L (α (a * b : genGroup gs) (L[i]).1) =
    vsQPos L (α a (L[(vsQPiF hα hK hL b i : ℕ)]).1)
  rw [vsQPiF_get hα hK hL b i, Subgroup.coe_mul, hα.mul _ (hK a.2) _ (hK b.2)]

theorem vsQPiF_one (i : Fin L.length) : vsQPiF hα hK hL 1 i = i := by
  classical
  apply Fin.ext
  simp only [vsQPiF, OneMemClass.coe_one, hα.one]
  exact vsQPos_get hα hK hL i

/-- The permutation of positions, as a homomorphism. -/
noncomputable def vsQPi : genGroup gs →* Perm (Fin L.length) where
  toFun h := {
    toFun := vsQPiF hα hK hL h
    invFun := vsQPiF hα hK hL h⁻¹
    left_inv := fun i => by rw [← vsQPiF_mul, inv_mul_cancel, vsQPiF_one]
    right_inv := fun i => by rw [← vsQPiF_mul, mul_inv_cancel, vsQPiF_one] }
  map_one' := by ext i; simp [vsQPiF_one]
  map_mul' a b := by ext i; simp [vsQPiF_mul, Perm.mul_apply]

theorem vsQPi_apply (h : genGroup gs) (i : Fin L.length) :
    vsQPi hα hK hL h i = vsQPiF hα hK hL h i := rfl

theorem vsQ_hd_zero (hpos : 0 < L.length) : (L[0]'hpos).1 = y₀ := by
  have := hL.hd
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at this
  simp only [Option.some.injEq] at this
  rw [this]

/-- `π(h)` fixes the position `0` exactly when `h` fixes `y₀`. -/
theorem vsQPi_fix (h : genGroup gs) (hpos : 0 < L.length) :
    vsQPi hα hK hL h ⟨0, hpos⟩ = ⟨0, hpos⟩ ↔ α h y₀ = y₀ := by
  classical
  rw [vsQPi_apply]
  constructor
  · intro he
    have := vsQPiF_get hα hK hL h ⟨0, hpos⟩
    rw [Fin.ext_iff] at he
    have h0 : (L[(⟨0, hpos⟩ : Fin L.length)]).1 = y₀ := vsQ_hd_zero hα hK hL hpos
    simp only [he] at this
    rw [h0] at this
    rw [this.symm, vsQ_hd_zero hα hK hL hpos]
  · intro he
    apply Fin.ext
    simp only [vsQPiF]
    show vsQPos L (α h (L[0]'hpos).1) = 0
    rw [vsQ_hd_zero hα hK hL hpos, he]
    have := vsQPos_get hα hK hL ⟨0, hpos⟩
    simpa [vsQ_hd_zero hα hK hL hpos] using this

theorem sumToFin_mul' {m : ℕ} (a b : Perm (Fin n ⊕ Fin m)) :
    sumToFin (a * b) = sumToFin a * sumToFin b := by
  ext x; simp [sumToFin, Perm.mul_apply]

/-- The graph map `h ↦ h ⊕ π(h)`. -/
noncomputable def vsQRho : genGroup gs →* Perm (Fin (n + L.length)) where
  toFun h := sumToFin (Equiv.sumCongr (h : Perm (Fin n)) (vsQPi hα hK hL h))
  map_one' := by
    rw [(vsQPi hα hK hL).map_one]
    ext x; simp [sumToFin]
  map_mul' a b := by
    rw [← sumToFin_mul' hα hK hL, Equiv.Perm.sumCongr_mul, (vsQPi hα hK hL).map_mul a b]; rfl

theorem vsQRho_injective : Function.Injective (vsQRho hα hK hL) := by
  intro a b hab
  have := sumToFin_injective hab
  apply Subtype.ext
  ext i
  have := congrArg (fun σ : Perm (Fin n ⊕ Fin L.length) => σ (Sum.inl i)) this
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] at this
  rw [this]

theorem vsQRho_fix (h : genGroup gs) (hpos : 0 < L.length) :
    vsQRho hα hK hL h (Fin.natAdd n (⟨0, hpos⟩ : Fin L.length)) = Fin.natAdd n (⟨0, hpos⟩ : Fin L.length) ↔ α h y₀ = y₀ := by
  rw [← vsQPi_fix hα hK hL h hpos]
  rw [← finSumFinEquiv_apply_right]
  simp only [vsQRho, MonoidHom.coe_mk, OneHom.coe_mk, sumToFin, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inr]
  exact (finSumFinEquiv.injective.eq_iff).trans (by simp)

/-- The stabilizer of `y₀` in `H`. -/
def vsQStabG (hα : VsQPAct K α) (hK : genGroup gs ≤ K) (y₀ : Y) : Subgroup (Perm (Fin n)) where
  carrier := {h | h ∈ genGroup gs ∧ α h y₀ = y₀}
  one_mem' := ⟨(genGroup gs).one_mem, hα.one y₀⟩
  mul_mem' := by
    rintro a b ⟨ha, hay⟩ ⟨hb, hby⟩
    exact ⟨(genGroup gs).mul_mem ha hb, by rw [hα.mul _ (hK ha) _ (hK hb), hby, hay]⟩
  inv_mem' := by
    rintro a ⟨ha, hay⟩
    refine ⟨(genGroup gs).inv_mem ha, ?_⟩
    conv_lhs => rw [← hay]
    rw [← hα.mul _ (hK ((genGroup gs).inv_mem ha)) _ (hK ha), inv_mul_cancel, hα.one]

/-- The generators of the graph group. -/
noncomputable def vsQDs : List (Perm (Fin (n + L.length))) :=
  gs.attach.map fun g => vsQRho hα hK hL ⟨g.1, Subgroup.subset_closure g.2⟩

theorem vsQ_gens_ds : gens (vsQDs hα hK hL) = (⊤ : Subgroup (genGroup gs)).map (vsQRho hα hK hL) := by
  rw [← Subgroup.closure_closure_coe_preimage (k := {g | g ∈ gs}), MonoidHom.map_closure]
  unfold gens vsQDs
  congr 1
  ext σ
  simp only [List.mem_map, List.mem_attach, true_and, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_preimage, Subtype.exists]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, Subgroup.subset_closure hg, hg, rfl⟩
  · rintro ⟨g, hg1, hg2, rfl⟩
    exact ⟨g, hg2, rfl⟩

theorem vsQ_pstab_mem (hpos : 0 < L.length) {σ : Perm (Fin (n + L.length))} :
    σ ∈ pointwiseStab (gens (vsQDs hα hK hL)) [Fin.natAdd n (⟨0, hpos⟩ : Fin L.length)] ↔
      ∃ h : genGroup gs, α h y₀ = y₀ ∧ vsQRho hα hK hL h = σ := by
  rw [vsQ_gens_ds]
  constructor
  · rintro ⟨⟨h, -, rfl⟩, hfix⟩
    exact ⟨h, (vsQRho_fix hα hK hL h hpos).mp (hfix _ (by simp)), rfl⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, trivial, rfl⟩, ?_⟩
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact (vsQRho_fix hα hK hL h hpos).mpr hh

/-- **The stabilizer from the graph group.** If `ρ(hs)` generates the stabilizer of the point
`n` in `⟨ρ(gs)⟩`, then `hs` generates the stabilizer of `y₀` in `H`. -/
theorem vsQ_stab_gens (hpos : 0 < L.length) (hs : List (genGroup gs))
    (hw : gens (hs.map (vsQRho hα hK hL)) =
      pointwiseStab (gens (vsQDs hα hK hL)) [Fin.natAdd n (⟨0, hpos⟩ : Fin L.length)]) :
    gens (hs.map Subtype.val) = vsQStabG hα hK y₀ := by
  apply le_antisymm
  · apply Subgroup.closure_le _ |>.mpr
    intro x hx
    simp only [List.mem_map, Set.mem_setOf_eq] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    have : vsQRho hα hK hL h ∈ gens (hs.map (vsQRho hα hK hL)) :=
      Subgroup.subset_closure (List.mem_map_of_mem hh)
    rw [hw, vsQ_pstab_mem hα hK hL hpos] at this
    obtain ⟨h', hh', he⟩ := this
    rw [vsQRho_injective hα hK hL he] at hh'
    exact ⟨h.2, hh'⟩
  · rintro x ⟨hx, hxy⟩
    have hm : vsQRho hα hK hL ⟨x, hx⟩ ∈ gens (hs.map (vsQRho hα hK hL)) := by
      rw [hw, vsQ_pstab_mem hα hK hL hpos]; exact ⟨⟨x, hx⟩, hxy, rfl⟩
    have e1 : gens (hs.map (vsQRho hα hK hL)) =
        (Subgroup.closure {h : genGroup gs | h ∈ hs}).map (vsQRho hα hK hL) := by
      rw [MonoidHom.map_closure]; unfold gens; congr 1; ext; simp
    rw [e1] at hm
    obtain ⟨y, hy, hye⟩ := hm
    rw [vsQRho_injective hα hK hL hye] at hy
    have e2 : gens (hs.map Subtype.val) =
        (Subgroup.closure {h : genGroup gs | h ∈ hs}).map (genGroup gs).subtype := by
      rw [MonoidHom.map_closure]; unfold gens; congr 1; ext; simp
    rw [e2]
    exact ⟨⟨x, hx⟩, hy, rfl⟩

end

end GI.Impl
