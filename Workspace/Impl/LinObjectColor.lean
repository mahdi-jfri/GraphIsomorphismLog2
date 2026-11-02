import Workspace.Impl.LinObjectMath
import Mathlib.Data.List.Perm.Basic

/-! Canonical first-occurrence labels for (old color, underlying subgroup).
The normalization is safe even on the unrestricted object-glue input contract. -/
namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset Equiv

def linObjectColorEq {n : ℕ} (o o' : TmRiO n) : Prop :=
  o.1 = o'.1 ∧ gens o.2.1 = gens o'.2.1

noncomputable def linObjectColor {n : ℕ} (Z : List (TmRiO n)) (o : TmRiO n) : ℕ := by
  classical
  exact Z.findIdx (fun o' => decide (linObjectColorEq o o'))

theorem linObjectColor_lt {n : ℕ} {Z : List (TmRiO n)} {o : TmRiO n} (ho : o ∈ Z) :
    linObjectColor Z o < Z.length := by
  classical
  exact List.findIdx_lt_length_of_exists ⟨o, ho, by simp [linObjectColorEq]⟩

theorem linObjectColor_eq_iff {n : ℕ} (Z : List (TmRiO n)) (o o' : TmRiO n)
    (ho : o ∈ Z) (ho' : o' ∈ Z) :
    linObjectColor Z o = linObjectColor Z o' ↔ linObjectColorEq o o' := by
  classical
  constructor
  · intro he
    have hp : linObjectColorEq o (Z[linObjectColor Z o]'(linObjectColor_lt ho)) := by
      have hh := List.findIdx_getElem (xs := Z) (p := fun z => decide (linObjectColorEq o z))
        (w := linObjectColor_lt ho)
      exact of_decide_eq_true hh
    have hp' : linObjectColorEq o' (Z[linObjectColor Z o']'(linObjectColor_lt ho')) := by
      have hh := List.findIdx_getElem (xs := Z) (p := fun z => decide (linObjectColorEq o' z))
        (w := linObjectColor_lt ho')
      exact of_decide_eq_true hh
    have hi : (⟨linObjectColor Z o, linObjectColor_lt ho⟩ : Fin Z.length) =
        ⟨linObjectColor Z o', linObjectColor_lt ho'⟩ := Fin.ext he
    have hv := congrArg Z.get hi
    change (Z[linObjectColor Z o]'(linObjectColor_lt ho)) =
      (Z[linObjectColor Z o']'(linObjectColor_lt ho')) at hv
    rw [← hv] at hp' 
    exact ⟨hp.1.trans hp'.1.symm, hp.2.trans hp'.2.symm⟩
  · rintro ⟨he, hg⟩
    unfold linObjectColor
    congr 1
    funext z
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, linObjectColorEq, he, hg]

/-- Map a permutation of lists through any pointwise implication of equality.
The two source lists may have different element types. -/
theorem linMapPerm_transfer {α β γ δ : Type*} (X : List α) (Y : List β)
    (f : α → γ) (g : β → γ) (f' : α → δ) (g' : β → δ)
    (hr : ∀ x ∈ X, ∀ y ∈ Y, f x = g y → f' x = g' y)
    (hp : List.Perm (X.map f) (Y.map g)) : List.Perm (X.map f') (Y.map g') := by
  have hex : ∃ ys, X.map f = ys.map g ∧ List.Perm ys Y := by
    change Relation.Comp (fun a b => a = List.map g b) List.Perm (X.map f) Y
    rw [List.eq_map_comp_perm]
    exact hp
  obtain ⟨ys, he, hys⟩ := hex
  have hl : X.length = ys.length := by simpa using congrArg List.length he
  have he' : X.map f' = ys.map g' := by
    apply List.ext_getElem (by simpa using hl)
    intro k hk hk'
    simp only [List.length_map] at hk hk'
    simp only [List.getElem_map]
    have hval := congrArg (fun xs : List γ => xs[k]?) he
    dsimp only at hval
    rw [List.getElem?_map, List.getElem?_map,
      List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk'] at hval
    apply hr _ (List.getElem_mem hk) _ (hys.mem_iff.mp (List.getElem_mem hk'))
    exact Option.some.inj hval
  rw [he']
  exact hys.map g'

/-- Simultaneous renaming and compression preserves the entire multiset transporter. -/
theorem linObjectNorm_iso {n : ℕ} (X Y : List (TmRiO n)) (H : Subgroup (Perm (Fin n))) :
    Iso H (tmGlMs (X.map (linObjectNorm (linObjectColor (X ++ Y)))))
      (tmGlMs (Y.map (linObjectNorm (linObjectColor (X ++ Y))))) = Iso H (tmGlMs X) (tmGlMs Y) := by
  ext g
  simp only [mem_iso, tmGlMs, multiset_act_def, Multiset.map_coe, List.map_map, Function.comp_def]
  apply and_congr_right
  intro hg
  rw [Multiset.coe_eq_coe, Multiset.coe_eq_coe]
  constructor
  · apply linMapPerm_transfer
    intro o ho o' ho' he
    exact (linObjectNorm_transport _ o o'
      (linObjectColor_eq_iff _ o o' (List.mem_append_left _ ho) (List.mem_append_right _ ho')) g).mp he
  · apply linMapPerm_transfer
    intro o ho o' ho' he
    exact (linObjectNorm_transport _ o o'
      (linObjectColor_eq_iff _ o o' (List.mem_append_left _ ho) (List.mem_append_right _ ho')) g).mpr he

end GI.Impl
