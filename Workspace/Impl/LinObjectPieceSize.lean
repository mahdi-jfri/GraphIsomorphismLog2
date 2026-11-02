import Workspace.Impl.LinObjectMovedMath

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped BigOperators

theorem linObjectReference_ms {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) :
    tmGlMs (tmRiPcsO A Y).flatten = tmGlMs Y := by
  rw [linObjectMs_flatten]
  have he := congrArg Multiset.sum (tmRiPcsO_ms A Y)
  simp only [Multiset.sum_coe,Finset.sum_val] at he
  exact he.trans (sum_pieces A (tmGlMs Y))

theorem linObjectReference_length {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) :
    (tmRiPcsO A Y).flatten.length = Y.length := by
  have he := congrArg Multiset.card (linObjectReference_ms A Y)
  simpa only [tmGlMs,Multiset.coe_card,List.length_map] using he

theorem linObjectPieces_wt {n : ℕ} (Ps : List (List (TmRiO n))) :
    Ps.flatten.length ≤ (Val.list (Ps.map tmGlObjsVal)).wt := by
  have hb : (Ps.map List.length).sum ≤ (Ps.map (fun S => (tmGlObjsVal S).wt)).sum := by
    apply List.sum_le_sum
    intro S hS
    have hh := length_lt_wt_list (S.map tmGlObjVal)
    simpa only [List.length_map] using hh.le
  have hs := sum_wt_lt_wt_list (Ps.map tmGlObjsVal)
  simp only [List.map_map,Function.comp_def] at hs
  rw [List.length_flatten]
  omega

theorem linObjectWordPieces_length {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    (linObjectWordPieces as Y z).flatten.length = Y.length := by
  rw [List.length_flatten]
  simp only [linObjectWordPieces,List.map_ofFn,Function.comp_apply,List.length_map,List.sum_ofFn]
  have he := congrArg (fun xs : List (List (TmRiO n)) => (xs.map List.length).sum)
    (List.ofFn_get (tmRiPcsO (gens as) Y))
  simp only [List.map_ofFn,Function.comp_apply,List.sum_ofFn] at he
  rw [he,← List.length_flatten,linObjectReference_length]

theorem linObjectMovedPieces_length {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) (g : Equiv.Perm (Fin n)) :
    (linObjectMovedPieces as Y z g).flatten.length = Y.length := by
  rw [List.length_flatten]
  simp only [linObjectMovedPieces,List.map_map,Function.comp_def,List.length_map]
  rw [← List.length_flatten,linObjectWordPieces_length]

theorem linObjectOffsets_size {n : ℕ} (as ns : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) (g : Equiv.Perm (Fin n)) :
    2 * Y.length ≤ (Val.list [encGroup as,encGroup ns,
      .list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),
      .list ((linObjectMovedPieces as Y z g).map tmGlObjsVal)]).wt := by
  have hr := linObjectPieces_wt (tmRiPcsO (gens as) Y)
  have ht := linObjectPieces_wt (linObjectMovedPieces as Y z g)
  rw [linObjectReference_length] at hr
  rw [linObjectMovedPieces_length] at ht
  have hs := sum_wt_lt_wt_list [encGroup as,encGroup ns,
    .list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),
    .list ((linObjectMovedPieces as Y z g).map tmGlObjsVal)]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hs
  omega

end GI.Impl
