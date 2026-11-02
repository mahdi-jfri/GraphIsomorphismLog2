import Workspace.Impl.CamPIndex
import Workspace.Impl.CamRestrict

/-!
# Step 7 of `camProg`: restricting a permutation to an invariant list

For a list `O` of distinct points that a permutation `t` maps into itself, the restriction of `t`
to `O` is the permutation `g` of the positions `Fin O.length` with `O[g w] = t O[w]`
(`cam_restrict_exists`). The function `camResF` computes it on `[natList O, encPerm t]`: it reads
the points `t O[w]` (`gather`), then their positions in `O` (`camIdx`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp len len_le_self)

variable {n : ℕ}

/-- In a list without repeats, the first entry equal to entry `i` is entry `i`. -/
theorem cam_findIdx_nodup {L : List ℕ} (hL : L.Nodup) (i : ℕ) (hi : i < L.length) :
    L.findIdx (fun x => decide (x = L[i])) = i := by
  rw [List.findIdx_eq hi]
  refine ⟨by simp, fun j hj => ?_⟩
  simp only [decide_eq_false_iff_not]
  intro h
  have := (List.Nodup.getElem_inj_iff hL (hi := by omega) (hj := hi)).mp h
  omega

/-- **The restriction exists.** -/
theorem cam_restrict_exists (O : List (Fin n)) (hO : O.Nodup) (t : Perm (Fin n))
    (ht : ∀ u ∈ O, t u ∈ O) : ∃ g : Perm (Fin O.length), ∀ w, O.get (g w) = t (O.get w) := by
  have hex : ∀ w : Fin O.length, ∃ w' : Fin O.length, O.get w' = t (O.get w) := fun w =>
    List.mem_iff_get.mp (ht _ (List.get_mem O w))
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro w₁ w₂ h
    have h1 : t (O.get w₁) = t (O.get w₂) := by rw [← hf, ← hf, h]
    exact (List.Nodup.get_inj_iff hO).mp (t.injective h1)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

/-- The restriction, or `1` when `t` does not map `O` into itself. -/
noncomputable def camRes (O : List (Fin n)) (hO : O.Nodup) (t : Perm (Fin n)) :
    Perm (Fin O.length) := by
  classical
  exact if ht : ∀ u ∈ O, t u ∈ O then (cam_restrict_exists O hO t ht).choose else 1

theorem camRes_spec (O : List (Fin n)) (hO : O.Nodup) (t : Perm (Fin n))
    (ht : ∀ u ∈ O, t u ∈ O) : ∀ w, O.get (camRes O hO t w) = t (O.get w) := by
  classical
  unfold camRes
  rw [dif_pos ht]
  exact (cam_restrict_exists O hO t ht).choose_spec

/-- The value of the restriction: positions of the points `t O[w]`. -/
theorem cam_res_val (O : List (Fin n)) (hO : O.Nodup) (t : Perm (Fin n))
    (ht : ∀ u ∈ O, t u ∈ O) :
    natList ((O.map fun u => ((t u : Fin n) : ℕ)).map fun v =>
        (O.map Fin.val).findIdx fun x => decide (x = v)) = encPerm (camRes O hO t) := by
  have hN : (O.map Fin.val).Nodup := hO.map Fin.val_injective
  simp only [natList, encPerm, List.map_map]
  congr 1
  refine List.ext_getElem (by simp) fun w h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply, Val.nat.injEq]
  have hg := camRes_spec O hO t ht ⟨w, by simpa using h2⟩
  simp only [List.get_eq_getElem] at hg
  rw [← hg]
  have hi : (camRes O hO t ⟨w, by simpa using h2⟩ : ℕ) < (O.map Fin.val).length := by simp
  have := cam_findIdx_nodup hN _ hi
  simp only [List.getElem_map] at this
  rw [this]
  rfl

/-! ### The program -/

/-- On `[natList O, encPerm t]`: the positions in `O` of the points `t O[w]`. -/
def camResF (gather idx : ℕ) : Expr := .call idx (mk2 (arg 0) (.call gather (mk2 (arg 1) (arg 0))))

/-- `camRes`, at base `b` (thirteen functions). -/
def camResFuns (b : ℕ) : List Expr := [camResF (b + 1) (b + 5)] ++ gatherFuns (b + 1) ++
  camIdxFuns (b + 5)

def camResK : ℕ := 10 ^ 12

/-- **Restriction to an invariant list.** -/
theorem camRes_det {P : Program} {b : ℕ} (h : P.HasAt b (camResFuns b)) (O : List (Fin n))
    (hO : O.Nodup) (t : Perm (Fin n)) (ht : ∀ u ∈ O, t u ∈ O) :
    FunDet P b (.list [natList (O.map Fin.val), encPerm t]) (encPerm (camRes O hO t))
      (camResK * (n + 1) ^ 6) := by
  simp only [camResFuns] at h
  have hentry : P.funs[b]? = some (camResF (b + 1) (b + 5)) := h.left.left.single
  have hgat : P.HasAt (b + 1) (gatherFuns (b + 1)) := h.left.right
  have hidx : P.HasAt (b + 5) (camIdxFuns (b + 5)) := by
    simpa [gatherFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right
  have hlen : O.length ≤ n := by
    have := hO.length_le_card
    simpa using this
  set Ov := O.map Fin.val with hOv
  set A := Val.list [natList Ov, encPerm t] with hA
  have hwO : (natList Ov).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (B := n) (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega)
      (by simpa [hOv] using hlen)
  have hwt := wt_encPerm_le t
  -- gather
  have hgi : ∀ i ∈ Ov, i < ((List.finRange n).map fun i => Val.nat (t i)).length := by
    intro i hi; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hi; simp
  have dg := gather_spec hgat hgi
  have hval : (Ov.map fun i => ((List.finRange n).map fun i => Val.nat (t i)).getD i (.nat 0)) =
      (O.map fun u => ((t u : Fin n) : ℕ)).map Val.nat := by
    simp only [hOv, List.map_map]
    refine List.map_congr_left fun u _ => ?_
    simp [List.getD_eq_getElem?_getD]
  rw [hval] at dg
  have dA1 := Det.arg' (P := P) (vs := [natList Ov, encPerm t]) (rest := []) (j := 1) rfl
  have dA0 := Det.arg' (P := P) (vs := [natList Ov, encPerm t]) (rest := []) (j := 0) rfl
  have dG := Det.call (Det.mk2 dA1 dA0) dg
  have dI := Det.call (Det.mk2 dA0 dG) (camIdx_spec hidx (B := n)
    (O := Ov) (vs := O.map fun u => ((t u : Fin n) : ℕ))
    (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega)
    (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega)
    (by simpa [hOv] using hlen) (by simpa using hlen))
  rw [cam_res_val O hO t ht] at dI
  refine FunDet.intro hentry (dI.mono ?_)
  clear dI dG dg dA0 dA1 hentry hgat hidx h
  have hwg := wt_encPerm_le (camRes O hO t)
  have hlen' : O.length + 1 ≤ n + 1 := by omega
  have hg2 : (O.length + 1) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left hlen' 2
  have hwr : (natList ((O.map fun u => ((t u : Fin n) : ℕ)))).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (B := n) (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega)
      (by simpa using hlen)
  have e1 : (natList ((O.map fun u => ((t u : Fin n) : ℕ)))).wt =
      (Val.list ((O.map fun u => ((t u : Fin n) : ℕ)).map Val.nat)).wt := rfl
  have hd1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have w1 := wt_list2_le (encPerm t) (natList Ov)
  have w1' : (Val.list [.list ((List.finRange n).map fun i => Val.nat (t i)), natList Ov]).wt ≤
      2 * ((encPerm t).wt + (natList Ov).wt) + 6 := w1
  have w2 := wt_list2_le (natList Ov) (natList ((O.map fun u => ((t u : Fin n) : ℕ))))
  have w2' : (Val.list [natList Ov, .list ((O.map fun u => ((t u : Fin n) : ℕ)).map Val.nat)]).wt
      ≤ 2 * ((natList Ov).wt + (natList ((O.map fun u => ((t u : Fin n) : ℕ)))).wt) + 6 := w2
  have w3 := wt_list2_le (natList Ov) (encPerm t)
  have hA1 : (Val.list [.list ((List.finRange n).map fun i => Val.nat (t i)), natList Ov]).wt + 1
      ≤ 30 * (n + 1) ^ 2 := by omega
  have hA3 := Nat.pow_le_pow_left hA1 3
  have e3 : (30 * (n + 1) ^ 2) ^ 3 = 27000 * (n + 1) ^ 6 := by ring
  rw [e3] at hA3
  have hn24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have k1 := Nat.mul_le_mul_left gatherK hA3
  simp only [camResK, camIdxK, gatherK] at *
  rw [e1] at hwr
  clear_value Ov A
  generalize (n + 1) ^ 6 = Q6 at *
  generalize (n + 1) ^ 4 = Q4 at *
  generalize (n + 1) ^ 2 = Q2 at *
  omega

end GI.Impl
