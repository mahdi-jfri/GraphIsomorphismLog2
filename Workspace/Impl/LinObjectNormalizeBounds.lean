module

public import Workspace.Impl.LinObjectNormalize

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectColor_append_left {n : ℕ} (Y X : List (TmRiO n)) (o : TmRiO n) (ho : o ∈ Y) :
    linObjectColor (Y++X) o = linObjectColor Y o := by
  classical
  unfold linObjectColor
  have hl := linObjectColor_lt ho
  unfold linObjectColor at hl
  rw [List.findIdx_append,if_pos hl]

theorem linObjectNorm_rec_ok {n : ℕ} (Z : List (TmRiO n)) :
    TmRecObjOK Z.length (Z.map (linObjectNorm (linObjectColor Z))) := by
  intro o ho
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ho
  have hh := linObjectNorm_ok Z (linObjectNorm (linObjectColor Z) a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  refine ⟨hh.1,?_,hh.2.2⟩
  change linObjectColor Z a < 2*Z.length
  have hl := linObjectColor_lt ha
  omega

theorem linObjectNorm_prefix_ok {n : ℕ} (Y X : List (TmRiO n)) :
    TmRecObjOK Y.length (Y.map (linObjectNorm (linObjectColor (Y++X)))) := by
  have he : Y.map (linObjectNorm (linObjectColor (Y++X))) = Y.map (linObjectNorm (linObjectColor Y)) := by
    apply List.map_congr_left
    intro o ho
    simp only [linObjectNorm,linObjectColor_append_left Y X o ho]
  rw [he]
  exact linObjectNorm_rec_ok Y

end GI.Impl
