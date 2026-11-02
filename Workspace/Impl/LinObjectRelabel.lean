import Workspace.Impl.LinLeftGroup
import Workspace.Impl.TermRecProgPcs

/-! Extend the finite color renaming to a global equivariant embedding. Unused
classes have a separate tag, so the extension is injective even off the input. -/
namespace GI.Impl
open GI.Multicoset GI.Cited

noncomputable def linColorIndex {α : Type*} (ps : List α) (p : α) : ℕ := by
  classical
  exact ps.findIdx (fun q => decide (p = q))

private theorem linColorIndex_lt {α : Type*} {ps : List α} {p : α} (hp : p ∈ ps) :
    linColorIndex ps p < ps.length := by
  classical
  exact List.findIdx_lt_length_of_exists ⟨p, hp, by simp⟩

private theorem linColorIndex_inj {α : Type*} {ps : List α} {p q : α}
    (hp : p ∈ ps) (hq : q ∈ ps) (he : linColorIndex ps p = linColorIndex ps q) : p = q := by
  classical
  have h₁ : p = ps[linColorIndex ps p]'(linColorIndex_lt hp) :=
    of_decide_eq_true (List.findIdx_getElem (p := fun a => decide (p = a)) (w := linColorIndex_lt hp))
  have h₂ : q = ps[linColorIndex ps q]'(linColorIndex_lt hq) :=
    of_decide_eq_true (List.findIdx_getElem (p := fun a => decide (q = a)) (w := linColorIndex_lt hq))
  have hi : (⟨linColorIndex ps p, linColorIndex_lt hp⟩ : Fin ps.length) =
      ⟨linColorIndex ps q, linColorIndex_lt hq⟩ := Fin.ext he
  exact h₁.trans ((congrArg ps.get hi).trans h₂.symm)

noncomputable def linColorCode {α : Type*} (ps : List α) (p : α) : Sum ℕ α := by
  classical
  exact if p ∈ ps then Sum.inl (linColorIndex ps p) else Sum.inr p

theorem linColorCode_injective {α : Type*} (ps : List α) : Function.Injective (linColorCode ps) := by
  classical
  intro p q he
  by_cases hp : p ∈ ps <;> by_cases hq : q ∈ ps
  · simp only [linColorCode, if_pos hp, if_pos hq, Sum.inl.injEq] at he
    exact linColorIndex_inj hp hq he
  · simp [linColorCode, hp, hq] at he
  · simp [linColorCode, hp, hq] at he
  · simpa [linColorCode, hp, hq] using he

def linObjectPair {n : ℕ} (o : TmRiO n) : ℕ × Subgroup (Equiv.Perm (Fin n)) :=
  (o.1, gens o.2.1)

noncomputable def linObjectCoded {n : ℕ} (Z : List (TmRiO n)) :
    linActEmbedding (G := Equiv.Perm (Fin n)) (Ω := CObj ℕ (Equiv.Perm (Fin n)))
      (Ψ := CObj (Sum ℕ (ℕ × Subgroup (Equiv.Perm (Fin n)))) (Equiv.Perm (Fin n))) where
  toFun o := ⟨linColorCode (Z.map linObjectPair) (o.tag, linLeftGroup o.coset), o.coset⟩
  injective := by
    intro o o' he
    have ht := linColorCode_injective (Z.map linObjectPair) (congrArg CObj.tag he)
    apply CObj.ext
    · exact congrArg Prod.fst ht
    · exact congrArg (fun o : CObj (Sum ℕ (ℕ × Subgroup (Equiv.Perm (Fin n)))) _ => o.coset) he
  act o g := by
    apply CObj.ext
    · simp only [cobj_act_tag, cobj_act_coset, linLeftGroup_right]
    · rfl

def linObjectInl {G α : Type*} [Group G] :
    linActEmbedding (G := G) (Ω := CObj ℕ G) (Ψ := CObj (Sum ℕ α) G) where
  toFun o := ⟨Sum.inl o.tag, o.coset⟩
  injective := by
    intro o o' he
    apply CObj.ext
    · exact Sum.inl.inj (congrArg CObj.tag he)
    · exact congrArg (fun o : CObj (Sum ℕ α) G => o.coset) he
  act o g := rfl

open Classical in
theorem linObjectColor_index {n : ℕ} (Z : List (TmRiO n)) (o : TmRiO n) :
    linObjectColor Z o = linColorIndex (Z.map linObjectPair) (linObjectPair o) := by
  classical
  unfold linObjectColor linColorIndex
  rw [List.findIdx_map]
  congr 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, linObjectColorEq, linObjectPair, Prod.mk.injEq]

theorem linObjectCoded_norm {n : ℕ} (Z : List (TmRiO n)) {o : TmRiO n} (ho : o ∈ Z) :
    (linObjectCoded Z).toFun (tmRiObj o) =
      linObjectInl.toFun (tmRiObj (linObjectNorm (linObjectColor Z) o)) := by
  classical
  have hm : linObjectPair o ∈ Z.map linObjectPair := List.mem_map.mpr ⟨o, ho, rfl⟩
  apply CObj.ext
  · change linColorCode (Z.map linObjectPair) (o.1, linLeftGroup ((fun l => l * o.2.2) '' (gens o.2.1 : Set _))) = _
    rw [linLeftGroup_coset]
    change linColorCode (Z.map linObjectPair) (linObjectPair o) = Sum.inl (linObjectColor Z o)
    rw [linObjectColor_index]
    simp only [linColorCode, if_pos hm]
  · change (fun l => l * o.2.2) '' (gens o.2.1 : Set _) =
      (fun l => l * o.2.2) '' (gens (GI.Lang.keepList o.2.1) : Set _)
    rw [GI.Lang.gens_keepList]

theorem linObjectCoded_map {n : ℕ} (Z X : List (TmRiO n)) (hX : ∀ x ∈ X, x ∈ Z) :
    (linObjectCoded Z).map (tmGlMs X) =
      linObjectInl.map (tmGlMs (X.map (linObjectNorm (linObjectColor Z)))) := by
  simp only [linActEmbedding.map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, tmGlMs,
    Multiset.map_coe, List.map_map, Function.comp_def]
  apply congrArg (@Multiset.ofList (CObj (Sum ℕ (ℕ × Subgroup (Equiv.Perm (Fin n)))) (Equiv.Perm (Fin n))))
  apply List.map_congr_left
  intro o ho
  exact linObjectCoded_norm Z (hX o ho)

/-- The supplied profile transporter remains a profile transporter after normalization. -/
theorem linObjectNorm_conf_act {n : ℕ} (Z X Y : List (TmRiO n))
    (hX : ∀ x ∈ X, x ∈ Z) (hY : ∀ y ∈ Y, y ∈ Z)
    (A : Subgroup (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)) :
    Conf A (tmGlMs (Y.map (linObjectNorm (linObjectColor Z))))
      (tmGlMs (X.map (linObjectNorm (linObjectColor Z))) ↼ g) ↔
    Conf A (tmGlMs Y) (tmGlMs X ↼ g) := by
  let e := linObjectInl (G := Equiv.Perm (Fin n)) (α := ℕ × Subgroup (Equiv.Perm (Fin n)))
  rw [← e.conf, e.map_act, ← linObjectCoded_map Z Y hY,
    ← linObjectCoded_map Z X hX, ← (linObjectCoded Z).map_act, (linObjectCoded Z).conf]

theorem linObjectNorm_iso_in {n : ℕ} (Z X Y : List (TmRiO n))
    (hX : ∀ x ∈ X, x ∈ Z) (hY : ∀ y ∈ Y, y ∈ Z) (H : Subgroup (Equiv.Perm (Fin n))) :
    Iso H (tmGlMs (X.map (linObjectNorm (linObjectColor Z))))
      (tmGlMs (Y.map (linObjectNorm (linObjectColor Z)))) = Iso H (tmGlMs X) (tmGlMs Y) := by
  let e := linObjectInl (G := Equiv.Perm (Fin n)) (α := ℕ × Subgroup (Equiv.Perm (Fin n)))
  rw [← e.iso, ← linObjectCoded_map Z X hX, ← linObjectCoded_map Z Y hY, (linObjectCoded Z).iso]

theorem linObjectNorm_fixes {n : ℕ} (Z X : List (TmRiO n)) (hX : ∀ x ∈ X, x ∈ Z)
    (N : Subgroup (Equiv.Perm (Fin n))) :
    Fixes N (tmGlMs (X.map (linObjectNorm (linObjectColor Z)))) ↔ Fixes N (tmGlMs X) := by
  let e := linObjectInl (G := Equiv.Perm (Fin n)) (α := ℕ × Subgroup (Equiv.Perm (Fin n)))
  rw [← e.fixes, ← linObjectCoded_map Z X hX, (linObjectCoded Z).fixes]

/-- The normalized input meets the existing orbit-partition helpers' exact
well-formedness hypotheses, with colors bounded by the number of occurrences. -/
theorem linObjectNorm_ok {n : ℕ} (Z : List (TmRiO n)) :
    TmRiOK Z.length (Z.map (linObjectNorm (linObjectColor Z))) := by
  intro o ho
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
  refine ⟨GI.Lang.length_keepList_le _, (linObjectColor_lt hx).le, ?_⟩
  intro o' ho' he
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho'
  have hh := (linObjectColor_eq_iff Z x y hx hy).mp he
  simpa only [linObjectNorm, GI.Lang.gens_keepList] using hh.2

end GI.Impl
