import Workspace.Impl.AggItemCfSpec
import Workspace.Impl.AggStructDesMath

/-!
# Reading the design object from lists

The scan uses the vertex counts and pair tests of the source-tuple test.
The result keeps the input colors. The dominant color read at its first
vertex equals the least dominant color used by `designAt`, since there is
only one dominant color.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv

/-- The indicator rows of the classes of a list of vertex colors. -/
def itCfDBlocks (V : List ℕ) (q : ℕ) : Val :=
  .list ((List.range q).map fun a => natList ((List.range q).map fun b =>
    if V.getD b 0 = V.getD a 0 then 1 else 0))

/-- The pair table read at a prefix, with its original colors. -/
def itCfDTable (dl tl : List ℕ) (q κ m : ℕ) : Val :=
  .list ((List.range q).map fun a => natList ((List.range q).map fun b =>
    stDCol dl tl q κ m a b))

/-- Read outcome (a), or outcome (b), at a prefix known to be a hit. -/
def itCfDAt (dl tl : List ℕ) (q κ m : ℕ) : Val :=
  let V := stDV dl tl q κ m
  if stDBal V q then
    .list [.nat 1, itCfDBlocks V q, natList V]
  else
    .list [.nat 2, .list [itCfDTable dl tl q κ m,
      .nat (V.getD (stDZ V q) 0), .nat (tl.getD κ 0)]]

/-- Scan the prefixes in order and return the object at the first hit. -/
def itCfDOut (dl tl : List ℕ) (q κ : ℕ) : Val :=
  if κ < tl.length then
    let m := (List.range κ).findIdx (stDHit dl tl q κ)
    if m < κ then itCfDAt dl tl q κ m else .list [.nat 0]
  else .list [.nat 0]

theorem itCfDBlocks_eq {q : ℕ} (f : Fin q → ℕ) :
    itCfDBlocks ((List.finRange q).map f) q = itCfBlkV (classPart f) := by
  classical
  have hv (z : Fin q) : ((List.finRange q).map f).getD z 0 = f z := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  unfold itCfDBlocks itCfBlkV
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  unfold natList encFun
  simp only [List.map_map, Function.comp_apply]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, hv, classPart, classOf, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem itCfDTable_eq {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ)
    (t : Fin ℓ → Fin q) (h0 : 0 < ℓ) {m : ℕ} (hm : m ≤ ℓ) (j : ℕ) :
    itCfDTable (stDL c) (stL fun i => (t i : ℕ)) q κ m =
      rcColVal (skelCfg c (preT t h0 m) j) := by
  unfold itCfDTable rcColVal
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  unfold natList encFun
  simp only [List.map_map, Function.comp_apply]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, stDCol_eq c t h0 hm, skelCfg]

theorem itCfDAt_eq {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ)
    (t : Fin ℓ → Fin q) (hkl : κ < ℓ) (hq : 0 < q) {m : ℕ}
    (hhit : Hit c t (by omega) m) :
    itCfDAt (stDL c) (stL fun i => (t i : ℕ)) q κ m =
      itCfOutV (designAt c t hkl m) := by
  classical
  have h0 : 0 < ℓ := by omega
  have hm : m ≤ ℓ := by have := hhit.1; omega
  have hbal := stDBal_iff c t h0 hm hq
  unfold itCfDAt designAt
  dsimp only
  by_cases hb : Balanced c (preT t h0 m)
  · rw [if_pos ((hbal).2 hb), if_pos hb]
    simp only [itCfOutV, stDV_eq c t h0 hm, itCfDBlocks_eq]
    simp only [natList, encFun, classPart, List.map_map, Function.comp_def]
  · have hbf : stDBal (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q = false :=
      Bool.eq_false_iff.2 (fun h => hb (hbal.1 h))
    simp only [hbf, Bool.false_eq_true, ↓reduceIte, hb]
    have hd : ∃ j, Dominant c (preT t h0 m) j := by
      obtain ⟨_, j, hj, _⟩ := hhit.2.resolve_left hb
      exact ⟨j, hj⟩
    rw [dif_pos hd]
    have hdom := (stDDom_first c t h0 hm hbf).2
    have hj := dominant_unique hq hdom (Nat.find_spec hd)
    have ht : (stL fun i => (t i : ℕ)).getD κ 0 = t ⟨κ, hkl⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp [stL]; omega)]
      simp [stL]
    simp only [itCfOutV, rcCertIn]
    rw [itCfDTable_eq c t h0 hm (Nat.find hd), ht]
    change _ = Val.list [Val.nat 2, Val.list [_, Val.nat (Nat.find hd), _]]
    rw [← hj]
    rfl

/-- The list scan returns exactly the model's design object, for arbitrary colors. -/
theorem itCfDOut_eq {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ)
    (t : Fin ℓ → Fin q) :
    itCfDOut (stDL c) (stL fun i => (t i : ℕ)) q κ =
      itCfOutV (designOut c t) := by
  classical
  have htlen : (stL fun i => (t i : ℕ)).length = ℓ := by simp [stL]
  unfold itCfDOut designOut
  rw [htlen]
  by_cases hkl : κ < ℓ
  swap
  · rw [if_neg hkl, dif_neg hkl]
    rfl
  rw [if_pos hkl, dif_pos hkl]
  have h0 : 0 < ℓ := by omega
  have hq : 0 < q := (t ⟨0, h0⟩).isLt.trans_le' (Nat.zero_le _)
  have hhit := stDHit_iff c t h0 hkl.le hq
  by_cases hex : ∃ m, Hit c t h0 m
  · have heq := st_findIdx_range_eq (fun m (hm : Hit c t h0 m) => hm.1)
        (fun m _ => hhit m) hex
    rw [dif_pos hex, heq, if_pos (Nat.find_spec hex).1]
    exact itCfDAt_eq c t hkl hq (Nat.find_spec hex)
  · have hn : ¬ (List.range κ).findIdx
        (stDHit (stDL c) (stL fun i => (t i : ℕ)) q κ) < κ := by
      intro h
      have hh := List.findIdx_getElem (p := stDHit (stDL c) (stL fun i => (t i : ℕ)) q κ)
        (w := (by simpa using h : _ < (List.range κ).length))
      rw [List.getElem_range] at hh
      exact hex ⟨_, (hhit _).1 hh⟩
    rw [dif_neg hex, if_neg hn]
    rfl

end GI.Impl
