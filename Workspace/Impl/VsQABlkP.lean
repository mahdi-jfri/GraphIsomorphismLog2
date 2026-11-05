module

public import Workspace.Impl.VsQATblP

@[expose] public section

/-!
# The program for the block sums

On `[pieces, labels]` the program `vsQABlksE` returns the nonempty block sums `vsQABlks`
(`vsQABlks_spec`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

/-- Piece `i` if its label is `c`, else nothing. -/
def vsQABlkI (Pcs : List (List (List ℕ))) (labL : List ℕ) (c i : ℕ) : List (List ℕ) :=
  if labL.getD i 0 = c then Pcs.getD i [] else []

theorem vsQABlk_eq (Pcs : List (List (List ℕ))) (labL : List ℕ) (c : ℕ) :
    vsQABlk Pcs labL c = ((List.range Pcs.length).map (vsQABlkI Pcs labL c)).flatten := rfl

/-- On `[[[pieces, labels], c], i]`: piece `i` if its label is `c`, else `[]`. -/
def vsQABlkIE : Expr :=
  .ite (.arith .eq (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 1)))
    (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 1)) .nil

/-- On `[[pieces, labels], c]`: the block with label `c`. -/
def vsQABlkE (rng mpi cat : ℕ) : Expr :=
  .call cat (.call mpi (mk2 (mk2 (arg 0) (arg 1)) (.call rng (.length (.get (arg 0) (.nat 0))))))

/-- On `[0, x]`: is `x` nonempty? -/
def vsQANonE : Expr := .arith .lt (.nat 0) (.length (arg 1))

/-- On `[pieces, labels]`: the nonempty blocks. -/
def vsQABlksE (rng mpo flt : ℕ) : Expr :=
  .letE (.call rng (.length (arg 0)))
  (.letE (.call mpo (mk2 (mk2 (arg 0) (arg 1)) (.var 1)))
    (.call flt (mk2 (.nat 0) (.var 2))))

/-- The layout of the block program. -/
structure VsQABlksAt (P : Program) (f rng mpo fo mpi fi cat flt fn : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQABlksE rng mpo flt)
  hrng : P.HasAt rng (rangeFuns rng)
  hmpo : P.HasAt mpo (mapFuns mpo fo)
  hfo : P.funs[fo]? = some (vsQABlkE rng mpi cat)
  hmpi : P.HasAt mpi (mapFuns mpi fi)
  hfi : P.funs[fi]? = some vsQABlkIE
  hcat : P.HasAt cat (vsWFlatFuns cat)
  hflt : P.HasAt flt (filterFuns flt fn)
  hfn : P.funs[fn]? = some vsQANonE

theorem vsQ_wt_mats_le {N : ℕ} {Pcs : List (List (List ℕ))} (hb : ∀ Q ∈ Pcs, VsWBnd N Q ∧ Q.length ≤ N)
    (hl : Pcs.length ≤ N) : (vsFMatsVal Pcs).wt ≤ 40 * (N + 1) ^ 4 := by
  have hw := vs_wt_list_le_of (Pcs.map fun M => Val.list (M.map natList)) (c := 11 * (N + 1) ^ 3 + 4) (by
    intro v hv
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hv
    exact wt_vsWVs_le (hb Q hQ).1 (by have := (hb Q hQ).2; omega))
  rw [List.length_map] at hw
  have h1 : Pcs.length * (2 * (11 * (N + 1) ^ 3 + 4) + 1) ≤ (N + 1) * (31 * (N + 1) ^ 3) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 3 (N + 1) (by omega); omega)
  have e : (N + 1) * (31 * (N + 1) ^ 3) = 31 * (N + 1) ^ 4 := by ring
  have := Nat.one_le_pow 4 (N + 1) (by omega)
  exact hw.trans (by omega)

section

variable {Pcs : List (List (List ℕ))} {labL : List ℕ} {N : ℕ}

/-- The size hypotheses of the block program. -/
structure VsQABlkSz (Pcs : List (List (List ℕ))) (labL : List ℕ) (N : ℕ) : Prop where
  bnd : ∀ Q ∈ Pcs, VsWBnd N Q
  sum : (Pcs.map List.length).sum ≤ N
  len : Pcs.length ≤ N
  lab : labL.length = Pcs.length
  labb : ∀ x ∈ labL, x ≤ N

theorem VsQABlkSz.qlen (H : VsQABlkSz Pcs labL N) {Q : List (List ℕ)} (hQ : Q ∈ Pcs) : Q.length ≤ N :=
  (List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hQ)).trans H.sum

theorem VsQABlkSz.wP (H : VsQABlkSz Pcs labL N) : (vsFMatsVal Pcs).wt ≤ 40 * (N + 1) ^ 4 :=
  vsQ_wt_mats_le (fun Q hQ => ⟨H.bnd Q hQ, H.qlen hQ⟩) H.len

theorem VsQABlkSz.wL (H : VsQABlkSz Pcs labL N) : (natList labL).wt ≤ 5 * (N + 1) ^ 2 :=
  wt_natList_le_sq H.labb (by rw [H.lab]; exact H.len)

end

section

variable {Pcs : List (List (List ℕ))} {labL : List ℕ} {N : ℕ}

theorem vsQABlkI_spec {P : Program} {fi : ℕ} (hfi : P.funs[fi]? = some vsQABlkIE)
    (H : VsQABlkSz Pcs labL N) {c i : ℕ} (hc : c ≤ N) (hi : i < Pcs.length) :
    FunDet P fi (.list [.list [.list [vsFMatsVal Pcs, natList labL], .nat c], .nat i])
      (vsWVs (vsQABlkI Pcs labL c i)) (10 ^ 4 * (N + 1) ^ 4) := by
  have hil : i < labL.length := by rw [H.lab]; exact hi
  set li := labL[i]
  set Qi := Pcs[i]
  have hli_mem : li ∈ labL := List.getElem_mem hil
  have hQi_mem : Qi ∈ Pcs := List.getElem_mem hi
  set PV := vsFMatsVal Pcs
  set LV := natList labL
  set X := [Val.list [Val.list [PV, LV], .nat c], .nat i]
  have g0 := Det.arg' (P := P) (rest := []) (vs := X) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := X) (j := 1) rfl
  have d00 := Det.get' g0 (Det.nat 0) (show [Val.list [PV, LV], .nat c][0]? = some (.list [PV, LV]) from rfl)
  have dc := Det.get' g0 (Det.nat 1) (show [Val.list [PV, LV], .nat c][1]? = some (.nat c) from rfl)
  have dL := Det.get' d00 (Det.nat 1) (show [PV, LV][1]? = some LV from rfl)
  have dP := Det.get' d00 (Det.nat 0) (show [PV, LV][0]? = some PV from rfl)
  have dLi := Det.get' dL g1 (show (labL.map Val.nat)[i]? = some (.nat li) by simp [hil, li])
  have dPi := Det.get' dP g1 (show (Pcs.map fun M => Val.list (M.map natList))[i]? =
    some (vsWVs Qi) by simp [hi, vsWVs, Qi])
  have deq := Det.arith' (op := BinOp.eq) dLi dc rfl
  have dite := Det.ite' deq dPi (Det.nil (P := P) (env := [Val.list X]))
  have ev : (if BinOp.eval .eq li c = 0 then Val.list [] else vsWVs Qi) =
      vsWVs (vsQABlkI Pcs labL c i) := by
    simp only [vsQABlkI, GI.Machine.BinOp.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil,
      List.getElem?_eq_getElem hi, Option.getD_some, li, Qi]
    by_cases h : labL[i] = c <;> simp [h, vsWVs]
  rw [ev] at dite
  refine FunDet.intro hfi (dite.mono ?_)
  clear g0 g1 d00 dc dL dP dLi dPi deq dite hfi
  have wP : PV.wt ≤ 40 * (N + 1) ^ 4 := H.wP
  have wL : LV.wt ≤ 5 * (N + 1) ^ 2 := H.wL
  have wQ : (vsWVs Qi).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
    wt_vsWVs_le (H.bnd _ hQi_mem) (by have := H.qlen hQi_mem; omega)
  have wQ' : (vsWVs (vsQABlkI Pcs labL c i)).wt ≤ 11 * (N + 1) ^ 3 + 4 := by
    rw [← ev]; split_ifs
    · simp
    · exact wQ
  have hli : li ≤ N := H.labb _ hli_mem
  have := wt_nat_le c; have := wt_nat_le i; have := wt_nat_le li; have := wt_nat_le 0
  have := wt_nat_le 1; have := wt_nat_le (BinOp.eval .eq li c)
  have he : BinOp.eval .eq li c ≤ 1 := by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  have w1 := wt_list2_le PV LV
  have w2 := wt_list2_le (.list [PV, LV]) (.nat c)
  have w3 := wt_list2_le (.list [.list [PV, LV], .nat c]) (.nat i)
  have eX : (Val.list X).wt = (Val.list [Val.list [Val.list [PV, LV], .nat c], .nat i]).wt := rfl
  have wn : (Val.list []).wt ≤ 10 := (wt_list_le []).trans (by simp)
  have hiN : i ≤ N := by have := H.len; omega
  clear H ev
  clear_value li Qi PV LV X
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end

section

variable {Pcs : List (List (List ℕ))} {labL : List ℕ} {N : ℕ}

theorem vsQABlkI_sub {c i : ℕ} : ∀ u ∈ vsQABlkI Pcs labL c i, ∃ Q ∈ Pcs, u ∈ Q := by
  intro u hu
  unfold vsQABlkI at hu
  split_ifs at hu
  · rw [List.getD_eq_getElem?_getD] at hu
    rcases h : Pcs[i]? with _ | Q
    · rw [h] at hu; simp at hu
    · rw [h] at hu
      exact ⟨Q, List.mem_of_getElem? h, by simpa using hu⟩
  · simp at hu

theorem vsQABlkI_len (c i : ℕ) : (vsQABlkI Pcs labL c i).length ≤ (Pcs.getD i []).length := by
  unfold vsQABlkI; split_ifs <;> simp

theorem vsQ_sum_getD_len : ((List.range Pcs.length).map fun i => (Pcs.getD i []).length).sum =
    (Pcs.map List.length).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp at h1
  simp [List.getD_eq_getElem?_getD, h1]

theorem vsQABlk_len (c : ℕ) : (vsQABlk Pcs labL c).length ≤ (Pcs.map List.length).sum := by
  rw [vsQABlk_eq, List.length_flatten, List.map_map, ← vsQ_sum_getD_len]
  exact List.sum_le_sum fun i _ => vsQABlkI_len c i

theorem VsQABlkSz.blk (H : VsQABlkSz Pcs labL N) (c : ℕ) :
    VsWBnd N (vsQABlk Pcs labL c) ∧ (vsQABlk Pcs labL c).length ≤ N := by
  refine ⟨fun u hu => ?_, (vsQABlk_len c).trans H.sum⟩
  rw [vsQABlk_eq, List.mem_flatten] at hu
  obtain ⟨_, hl, hu⟩ := hu
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
  obtain ⟨Q, hQ, huQ⟩ := vsQABlkI_sub u hu
  exact H.bnd Q hQ u huQ

theorem vsQABlk_spec {P : Program} {fo rng mpi fi cat : ℕ}
    (hfo : P.funs[fo]? = some (vsQABlkE rng mpi cat)) (hrng : P.HasAt rng (rangeFuns rng))
    (hmpi : P.HasAt mpi (mapFuns mpi fi)) (hfi : P.funs[fi]? = some vsQABlkIE)
    (hcat : P.HasAt cat (vsWFlatFuns cat))
    (H : VsQABlkSz Pcs labL N) {c : ℕ} (hc : c ≤ N) :
    FunDet P fo (.list [.list [vsFMatsVal Pcs, natList labL], .nat c])
      (vsWVs (vsQABlk Pcs labL c)) (10 ^ 9 * (N + 1) ^ 6) := by
  set PV := vsFMatsVal Pcs
  set LV := natList labL
  set X := [Val.list [PV, LV], .nat c]
  have g0 := Det.arg' (P := P) (rest := []) (vs := X) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := X) (j := 1) rfl
  have dP := Det.get' g0 (Det.nat 0) (show [PV, LV][0]? = some PV from rfl)
  have dm := Det.length dP
  rw [List.length_map] at dm
  -- the range
  have hr : FunDet P rng (.nat Pcs.length) (natList (List.range Pcs.length))
      (loopModK * (Pcs.length + 1) * ((Val.nat Pcs.length).wt + Pcs.length +
        (natList (List.range Pcs.length)).wt + 1)) :=
    (range_spec hrng Pcs.length).mono fun w c h => by obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩
  have dr := Det.call dm hr
  -- the map
  have hmap := vsQ_map hmpi (c := .list [.list [PV, LV], .nat c]) (List.range Pcs.length) Val.nat
    (fun i => vsWVs (vsQABlkI Pcs labL c i)) (fun a b h => by simpa using h)
    (fun i hi => vsQABlkI_spec hfi H hc (List.mem_range.1 hi))
  have dmap := Det.call (Det.mk2 (Det.mk2 g0 g1) dr) hmap
  -- the join
  set xss := (List.range Pcs.length).map fun i => (vsQABlkI Pcs labL c i).map natList
  have ex : Val.list ((List.range Pcs.length).map fun i => vsWVs (vsQABlkI Pcs labL c i)) =
      Val.list (xss.map Val.list) := by simp [xss, vsWVs, List.map_map, Function.comp_def]
  rw [ex] at dmap
  have hb := H.blk c
  have eo : Val.list xss.flatten = vsWVs (vsQABlk Pcs labL c) := by
    simp [xss, vsWVs, vsQABlk_eq, List.map_flatten, List.map_map, Function.comp_def]
  have wo : (vsWVs (vsQABlk Pcs labL c)).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsWVs_le hb.1 (by omega)
  have wi : (Val.list (xss.map Val.list)).wt ≤ 40 * (N + 1) ^ 4 := by
    have : Val.list (xss.map Val.list) = vsFMatsVal ((List.range Pcs.length).map (vsQABlkI Pcs labL c)) := by
      simp [xss, vsFMatsVal, List.map_map, Function.comp_def]
    rw [this]
    refine vsQ_wt_mats_le (fun Q hQ => ?_) (by simp [H.len])
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hQ
    refine ⟨fun u hu => ?_, ?_⟩
    · obtain ⟨Q, hQ, huQ⟩ := vsQABlkI_sub u hu
      exact H.bnd Q hQ u huQ
    · refine (vsQABlkI_len c i).trans ?_
      rw [List.getD_eq_getElem?_getD]
      rcases h : Pcs[i]? with _ | Q
      · simp
      · simpa using H.qlen (List.mem_of_getElem? h)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have dcat := Det.call dmap (vsWConcat_spec hcat (N := N) xss (by simp [xss, H.len])
    (fun xs hxs => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hxs
      rw [List.length_map]
      refine (vsQABlkI_len c i).trans ?_
      rw [List.getD_eq_getElem?_getD]
      rcases h : Pcs[i]? with _ | Q
      · simp
      · simpa using H.qlen (List.mem_of_getElem? h))
    (by rw [eo]; omega) (by omega))
  rw [eo] at dcat
  refine FunDet.intro hfo (dcat.mono ?_)
  clear g0 g1 dP dm hr dr hmap dmap dcat hfo hrng hmpi hfi hcat hb ex eo
  have wP : PV.wt ≤ 40 * (N + 1) ^ 4 := H.wP
  have wL : LV.wt ≤ 5 * (N + 1) ^ 2 := H.wL
  have wR : (natList (List.range Pcs.length)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by have := List.mem_range.1 hy; have := H.len; omega) (by simp [H.len])
  have := wt_nat_le c; have := wt_nat_le Pcs.length; have := wt_nat_le 0; have := wt_nat_le 1
  have w1 := wt_list2_le PV LV
  have w2 := wt_list2_le (.list [PV, LV]) (.nat c)
  have eX : (Val.list X).wt = (Val.list [Val.list [PV, LV], .nat c]).wt := rfl
  have w3 := wt_list2_le (.list [.list [PV, LV], .nat c]) (natList (List.range Pcs.length))
  have lr : (List.range Pcs.length).length = Pcs.length := List.length_range
  rw [lr]
  have hm := H.len
  clear H
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q56 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hR : loopModK * (Pcs.length + 1) * ((Val.nat Pcs.length).wt + Pcs.length +
      (natList (List.range Pcs.length)).wt + 1) ≤ 1000 * (N + 1) * (10 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eR : 1000 * (N + 1) * (10 * (N + 1) ^ 2) = 10000 * (N + 1) ^ 3 := by ring
  have hM1 : Pcs.length * (10 ^ 4 * (N + 1) ^ 4) ≤ (N + 1) * (10 ^ 4 * (N + 1) ^ 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have eM1 : (N + 1) * (10 ^ 4 * (N + 1) ^ 4) = 10 ^ 4 * (N + 1) ^ 5 := by ring
  have hM2 : mapK * (Pcs.length + 1) * ((Val.list [Val.list [Val.list [PV, LV], Val.nat c],
      Val.list ((List.range Pcs.length).map Val.nat)]).wt + (Val.list (xss.map Val.list)).wt + 1) ≤
      1000 * (N + 1) * (500 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by
      have e : Val.list ((List.range Pcs.length).map Val.nat) = natList (List.range Pcs.length) := rfl
      rw [e]; omega)
  have eM2 : 1000 * (N + 1) * (500 * (N + 1) ^ 4) = 500000 * (N + 1) ^ 5 := by ring
  have mk : mapK = 1000 := rfl
  have mk2 : loopModK = 1000 := rfl
  have e : Val.list ((List.range Pcs.length).map Val.nat) = natList (List.range Pcs.length) := rfl
  rw [e] at hM2 ⊢
  clear_value PV LV X xss
  omega

end

/-- The nonempty test on a value. -/
def vsQANonQ : Val → Bool
  | .list l => decide (0 < l.length)
  | _ => false

theorem vsQANon_spec {P : Program} {fn : ℕ} (hfn : P.funs[fn]? = some vsQANonE) (xs : List Val) :
    FunDet P fn (.list [.nat 0, .list xs]) (boolVal (vsQANonQ (.list xs)))
      (4 * (Val.list [.nat 0, .list xs]).wt + 30) := by
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.nat 0, .list xs]) (j := 1) rfl
  have d := Det.arith' (op := BinOp.lt) (Det.nat (P := P) (env := [Val.list [.nat 0, .list xs]]) 0)
    (Det.length g1) rfl
  have e : (Val.nat (BinOp.eval .lt 0 xs.length)) = boolVal (vsQANonQ (.list xs)) := by
    simp only [GI.Machine.BinOp.eval, vsQANonQ, boolVal]
    split_ifs with h <;> simp [h]
  rw [e] at d
  refine FunDet.intro hfn (d.mono ?_)
  have := wt_nat_le 0
  have := wt_nat_le xs.length
  have hl := length_lt_wt_list xs
  have hx : (Val.list xs).wt < (Val.list [.nat 0, .list xs]).wt := wt_le_wt_list (by simp)
  have hb : BinOp.eval .lt 0 xs.length ≤ 1 := by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  omega

/-- The cost of the block program. -/
def vsQABlksCost (N : ℕ) : ℕ := 10 ^ 11 * (N + 1) ^ 7

/-- **The block program.** -/
theorem vsQABlks_spec {P : Program} {f rng mpo fo mpi fi cat flt fn : ℕ}
    (L : VsQABlksAt P f rng mpo fo mpi fi cat flt fn) {Pcs : List (List (List ℕ))} {labL : List ℕ} {N : ℕ}
    (H : VsQABlkSz Pcs labL N) :
    FunDet P f (.list [vsFMatsVal Pcs, natList labL]) (vsFMatsVal (vsQABlks Pcs labL)) (vsQABlksCost N) := by
  set PV := vsFMatsVal Pcs
  set LV := natList labL
  have g0 := Det.arg' (P := P) (rest := []) (vs := [PV, LV]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [PV, LV]) (j := 1) rfl
  have dm := Det.length g0
  rw [List.length_map] at dm
  have hr : FunDet P rng (.nat Pcs.length) (natList (List.range Pcs.length))
      (loopModK * (Pcs.length + 1) * ((Val.nat Pcs.length).wt + Pcs.length +
        (natList (List.range Pcs.length)).wt + 1)) :=
    (range_spec L.hrng Pcs.length).mono fun w c h => by obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩
  have dr := Det.call dm hr
  set RV := natList (List.range Pcs.length)
  set E1 := [Val.list [PV, LV], RV]
  have g0' := Det.arg' (P := P) (rest := [RV]) (vs := [PV, LV]) (j := 0) rfl
  have g1' := Det.arg' (P := P) (rest := [RV]) (vs := [PV, LV]) (j := 1) rfl
  have hmap := vsQ_map L.hmpo (c := .list [PV, LV]) (List.range Pcs.length) Val.nat
    (fun c => vsWVs (vsQABlk Pcs labL c)) (fun a b h => by simpa using h)
    (fun c hc => vsQABlk_spec L.hfo L.hrng L.hmpi L.hfi L.hcat H
      (by have := List.mem_range.1 hc; have := H.len; omega))
  have dmap := Det.call (Det.mk2 (Det.mk2 g0' g1') (Det.var' (P := P) (env := E1) (i := 1) rfl)) hmap
  set XS := (List.range Pcs.length).map fun c => vsWVs (vsQABlk Pcs labL c)
  set E2 := [Val.list [PV, LV], RV, Val.list XS]
  have hflt := filter_spec L.hflt (c := .nat 0) (xs := XS) (q := vsQANonQ)
    (B := fun v => 4 * (Val.list [.nat 0, v]).wt + 30) (fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact vsQANon_spec L.hfn _)
  have ef : Val.list (XS.filter vsQANonQ) = vsFMatsVal (vsQABlks Pcs labL) := by
    simp only [XS, vsQABlks, vsFMatsVal, List.filter_map, List.map_map]
    congr 1
    congr 1
    refine List.filter_congr fun c _ => ?_
    simp [vsQANonQ, vsWVs]
  have hflt' : FunDet P flt (.list [.nat 0, .list XS]) (vsFMatsVal (vsQABlks Pcs labL))
      ((XS.map fun v => 4 * (Val.list [.nat 0, v]).wt + 30).sum +
        loopModK * (XS.length + 1) * ((Val.list [.nat 0, .list XS]).wt + XS.length +
          (vsFMatsVal (vsQABlks Pcs labL)).wt + 1)) :=
    hflt.mono fun w c h => by obtain ⟨rfl, h2⟩ := h; rw [ef] at h2 ⊢; exact ⟨rfl, h2⟩
  have dflt := Det.call (Det.mk2 (Det.nat (P := P) (env := E2) 0) (Det.var' (P := P) (env := E2) (i := 2) rfl))
    hflt'
  refine FunDet.intro L.hf ((Det.letE dr (Det.letE dmap dflt)).mono ?_)
  clear g0 g1 dm hr dr g0' g1' hmap dmap hflt ef hflt' dflt L
  have hm := H.len
  have wP : PV.wt ≤ 40 * (N + 1) ^ 4 := H.wP
  have wL : LV.wt ≤ 5 * (N + 1) ^ 2 := H.wL
  have wR : RV.wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by have := List.mem_range.1 hy; omega) (by simp; omega)
  have hblk : ∀ b ∈ (List.range Pcs.length).map (vsQABlk Pcs labL), VsWBnd N b ∧ b.length ≤ N := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
    exact H.blk c
  have wXS : (Val.list XS).wt ≤ 40 * (N + 1) ^ 4 := by
    have e : Val.list XS = vsFMatsVal ((List.range Pcs.length).map (vsQABlk Pcs labL)) := by
      simp [XS, vsFMatsVal, vsWVs, List.map_map, Function.comp_def]
    rw [e]; exact vsQ_wt_mats_le hblk (by simp; omega)
  have wO : (vsFMatsVal (vsQABlks Pcs labL)).wt ≤ 40 * (N + 1) ^ 4 :=
    vsQ_wt_mats_le (fun b hb => hblk b (List.mem_of_mem_filter hb))
      ((List.length_filter_le _ _).trans (by simp; omega))
  clear H hblk
  have hXl : XS.length = Pcs.length := by simp [XS]
  have hsum : (XS.map fun v => 4 * (Val.list [.nat 0, v]).wt + 30).sum ≤ XS.length * (400 * (N + 1) ^ 4) := by
    have := List.sum_le_card_nsmul (XS.map fun v => 4 * (Val.list [.nat 0, v]).wt + 30) (400 * (N + 1) ^ 4) (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      have hvx : v.wt < (Val.list XS).wt := wt_le_wt_list hv
      have := wt_list2_le (.nat 0) v
      have := wt_nat_le 0
      have q4 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega)
    simpa using this
  have := wt_nat_le 0; have := wt_nat_le Pcs.length
  have w1 := wt_list2_le PV LV
  have w2 := wt_list2_le (.list [PV, LV]) RV
  have w3 := wt_list2_le (.nat 0) (.list XS)
  have lr : (List.range Pcs.length).length = Pcs.length := List.length_range
  rw [lr]
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q57 : (N + 1) ^ 5 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have q67 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hR : loopModK * (Pcs.length + 1) * ((Val.nat Pcs.length).wt + Pcs.length + RV.wt + 1) ≤
      1000 * (N + 1) * (10 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eR : 1000 * (N + 1) * (10 * (N + 1) ^ 2) = 10000 * (N + 1) ^ 3 := by ring
  have hM1 : Pcs.length * (10 ^ 9 * (N + 1) ^ 6) ≤ (N + 1) * (10 ^ 9 * (N + 1) ^ 6) :=
    Nat.mul_le_mul_right _ (by omega)
  have eM1 : (N + 1) * (10 ^ 9 * (N + 1) ^ 6) = 10 ^ 9 * (N + 1) ^ 7 := by ring
  have e : Val.list ((List.range Pcs.length).map Val.nat) = RV := rfl
  rw [e]
  have hM2 : mapK * (Pcs.length + 1) * ((Val.list [Val.list [PV, LV], RV]).wt + (Val.list XS).wt + 1) ≤
      1000 * (N + 1) * (500 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eM2 : 1000 * (N + 1) * (500 * (N + 1) ^ 4) = 500000 * (N + 1) ^ 5 := by ring
  have hS : XS.length * (400 * (N + 1) ^ 4) ≤ (N + 1) * (400 * (N + 1) ^ 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have eS : (N + 1) * (400 * (N + 1) ^ 4) = 400 * (N + 1) ^ 5 := by ring
  have hF : loopModK * (XS.length + 1) * ((Val.list [.nat 0, .list XS]).wt + XS.length +
      (vsFMatsVal (vsQABlks Pcs labL)).wt + 1) ≤ 1000 * (N + 1) * (200 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eF : 1000 * (N + 1) * (200 * (N + 1) ^ 4) = 200000 * (N + 1) ^ 5 := by ring
  have mk : mapK = 1000 := rfl
  have mk2 : loopModK = 1000 := rfl
  unfold vsQABlksCost
  clear_value PV LV RV E1 XS E2
  omega

end GI.Impl
