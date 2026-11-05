module

public import Workspace.Impl.VsQABlkM
public import Workspace.Impl.VsQTItem
public import Workspace.Impl.VsQTKeyP

@[expose] public section

/-!
# The tables of the pieces

For each stored local matrix `A` of `1 :: hs`, the table lists, for each piece `P_i`, the index of
the piece `A P_i`. Pieces are compared by their marked keys (`vsQTKeyM`).

* `vsQATb`: the table of `A`.
* `vsQATb_eq`: for `A` the local matrix of `g ∈ H`, the table is the permutation `vsQAPiG g`.
* `vsQATbl_spec'`: the program `vsQATblE` on `[[p, D], pieces, matrices]` returns
  `[m, tables]`.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- The marked keys of the pieces. -/
noncomputable def vsQAKM (s : VsQSt I) (Lb : List (List (List ℕ))) : List (List ℕ) :=
  (vsQAPcs s Lb).map fun P => vsQTKeyM (vsWSp I.p (vsQD s) P)

/-- The table of a stored matrix `A`: the index of the piece `A P_i`, for each `i`. -/
noncomputable def vsQATb (s : VsQSt I) (Lb : List (List (List ℕ))) (A : List (List ℕ)) : List ℕ :=
  (vsQAPcs s Lb).map fun P => (vsQAKM s Lb).findIdx fun k =>
    decide (vsQTKeyM ((vsWSp I.p (vsQD s) P).map (vsWLin I.p (vsQD s) A)) = k)

theorem vsQ_natList_inj : Function.Injective natList := by
  intro a b h
  simp only [natList, Val.list.injEq] at h
  exact List.map_injective_iff.mpr (fun x y e => by simpa using e) h

/-- **The table of `g` is its permutation of the pieces.** -/
theorem vsQATb_eq [Fact I.p.Prime] {hs : VsQStOK s} {as : List (Perm (Fin I.n))}
    {Lb : List (List (List ℕ))} (h : VsQAHyp hs as Lb) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    natList (vsQATb s Lb (vsPLocL I s.ws' (vsQCs s) g)) = encPerm (vsQAPiG h g) := by
  rw [encPerm, natList]
  congr 1
  apply List.ext_getElem (by simp [vsQATb])
  intro i h1 h2
  have hi : i < (vsQAPcs s Lb).length := by simpa [vsQATb] using h1
  simp only [vsQATb, List.getElem_map, List.getElem_finRange, Val.nat.injEq]
  set j := vsQAPiG h g ⟨i, hi⟩
  have hmap : (vsWSp I.p (vsQD s) (vsQAPcs s Lb)[i]).map (vsWLin I.p (vsQD s)
      (vsPLocL I s.ws' (vsQCs s) g)) = vsQAU s Lb j := by
    have := vsQAPi_map h ⟨vsPRho hs g, vsPRho_mem_vsPBar hs hg hg⟩ ⟨i, hi⟩
    rw [vsQAPi_eq h hg] at this
    rw [← this]
    simp only [vsPRho_of hs hg, vsQRho_eq_toLin' hs hg]
    rfl
  rw [hmap]
  have hjl : (j : ℕ) < (vsQAKM s Lb).length := by simp [vsQAKM]
  have hkj : (vsQAKM s Lb)[(j : ℕ)] = vsQTKeyM (vsQAU s Lb j) := by simp [vsQAKM, vsQAU]
  have hlt : (vsQAKM s Lb).findIdx (fun k => decide (vsQTKeyM (vsQAU s Lb j) = k)) <
      (vsQAKM s Lb).length := List.findIdx_lt_length_of_exists ⟨_, List.getElem_mem hjl, by simp [hkj]⟩
  have hget := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at hget
  have hkl : (vsQAKM s Lb).length = (vsQAPcs s Lb).length := by simp [vsQAKM]
  have e1 : (vsQAKM s Lb)[(vsQAKM s Lb).findIdx (fun k => decide (vsQTKeyM (vsQAU s Lb j) = k))] = vsQTKeyM (vsQAU s Lb ⟨_, hkl ▸ hlt⟩) := by simp [vsQAKM, vsQAU]
  rw [e1] at hget
  have e2 := vsQAU_inj h (vsQTKeyM_injective hget)
  exact congrArg Fin.val e2.symm

/-! ### The programs -/

/-- The inner item, on `[[[p, D, A], keys], key]`: the index of the key of the image. -/
def vsQATbInE (item fnd : ℕ) : Expr :=
  .call fnd (mk2 (.call item (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.get (arg 0) (.nat 1)))

/-- The outer item, on `[[[p, D], keys], A]`: the table of `A`. -/
def vsQATbOutE (mpi : ℕ) : Expr :=
  .call mpi (mk2 (mk2 (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))
    (arg 1)) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 1)))

/-- The tables, on `[[p, D], pieces, matrices]`: `[m, tables]`. -/
def vsQATblE (mpk mpo : ℕ) : Expr :=
  .letE (.call mpk (mk2 (arg 0) (arg 1)))
  (.letE (.call mpo (mk2 (mk2 (arg 0) (.var 1)) (arg 2)))
    (mk2 (.length (arg 1)) (.var 2)))

/-- The layout of the table program. -/
structure VsQATblAt (P : Program) (f mpk ki key cat appd mpo fo mpi fi it tl chk ker img key' cat' appd'
    fnd eq : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQATblE mpk mpo)
  hmpk : P.HasAt mpk (mapFuns mpk ki)
  HK : VsQTKeyItemAt P ki key cat appd
  hmpo : P.HasAt mpo (mapFuns mpo fo)
  hfo : P.funs[fo]? = some (vsQATbOutE mpi)
  hmpi : P.HasAt mpi (mapFuns mpi fi)
  hfi : P.funs[fi]? = some (vsQATbInE it fnd)
  HI : VsQTItemAt P it tl chk ker img key' cat' appd'
  hfnd : P.HasAt fnd (findFuns fnd eq)
  heq : P.HasAt eq (eqNatsFuns eq)

theorem vsQ_keyM_wt {N : ℕ} (hpN : I.p ≤ N) (hDN : vsQD s * vsQD s + 1 ≤ N)
    (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    (natList (vsQTKeyM U)).wt ≤ 5 * (N + 1) ^ 2 := by
  have hK := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas U)
  refine wt_natList_le_sq (fun y hy => ?_) (by rw [vsQTKeyM_len]; omega)
  rcases List.mem_cons.mp hy with rfl | hy
  · omega
  · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
    exact ((hK r hr).1 y hy).le.trans hpN

theorem vsQ_keysM_wt {N : ℕ} (hpN : I.p ≤ N) (hDN : vsQD s * vsQD s + 1 ≤ N)
    (l : List (Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p))) (hl : l.length ≤ N) :
    (Val.list (l.map fun U => natList (vsQTKeyM U))).wt ≤ 20 * (N + 1) ^ 3 := by
  have h := vs_wt_list_le_of (l.map fun U => natList (vsQTKeyM U)) (c := 5 * (N + 1) ^ 2) (by
    intro v hv
    obtain ⟨U, -, rfl⟩ := List.mem_map.1 hv
    exact vsQ_keyM_wt hpN hDN U)
  rw [List.length_map] at h
  have h1 : l.length * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
  have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
  have h2 := Nat.one_le_pow 3 (N + 1) (by omega)
  omega

set_option maxHeartbeats 4000000 in
open Classical in
theorem vsQATbIn_spec {P : Program} {fi it tl chk ker img key cat appd fnd eq : ℕ}
    (hfi : P.funs[fi]? = some (vsQATbInE it fnd)) (HI : VsQTItemAt P it tl chk ker img key cat appd)
    (hfnd : P.HasAt fnd (findFuns fnd eq)) (heq : P.HasAt eq (eqNatsFuns eq))
    {N : ℕ} (hpN : I.p ≤ N) (hDN : vsQD s * vsQD s + 1 ≤ N) {A : List (List ℕ)}
    (hA : VsWSq I.p (vsQD s) A) (l : List (Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)))
    (hl : l.length ≤ N) (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    FunDet P fi (.list [.list [.list [.nat I.p, .nat (vsQD s), vsWVs A],
        .list (l.map fun V => natList (vsQTKeyM V))], natList (vsQTKeyM U)])
      (.nat ((l.map vsQTKeyM).findIdx fun k => decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k)))
      (10 ^ 12 * (N + 1) ^ 6) := by
  set c := Val.list [.nat I.p, .nat (vsQD s), vsWVs A]
  set KV := Val.list (l.map fun V => natList (vsQTKeyM V))
  set x := natList (vsQTKeyM U)
  set t := vsQTKeyM (U.map (vsWLin I.p (vsQD s) A))
  have g0 := Det.arg' (P := P) (rest := []) (vs := [.list [c, KV], x]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.list [c, KV], x]) (j := 1) rfl
  have dc := Det.get' g0 (Det.nat 0) (show [c, KV][0]? = some c from rfl)
  have dK := Det.get' g0 (Det.nat 1) (show [c, KV][1]? = some KV from rfl)
  -- the item
  have hK : VsWFit I.p (vsQD s) (vsQTKeyU U) := vsWKey_fit I.prime.one_lt _
  have hKl : (vsQTKeyU U).length = vsQD s := vsWKey_length _ _
  have hit := vsQTItem_spec HI I.prime hpN hDN hA hK hKl
  rw [vsQTItemL_eq hA U] at hit
  have dit := Det.call (Det.mk2 dc g1) hit
  -- the search
  set q : Val → Bool := fun v => decide (natList t = v)
  have hq : ∀ v ∈ l.map (fun V => natList (vsQTKeyM V)), FunDet P eq (.list [natList t, v]) (boolVal (q v))
      (loopModK * (N + 1) * (30 * (N + 1) ^ 2 + N + 10)) := by
    intro v hv
    obtain ⟨V, -, rfl⟩ := List.mem_map.1 hv
    have e : q (natList (vsQTKeyM V)) = decide (t = vsQTKeyM V) := by
      simp only [q, decide_eq_decide]
      exact ⟨fun h => vsQ_natList_inj h, fun h => h ▸ rfl⟩
    rw [e]
    refine (eqNats_spec heq t (vsQTKeyM V)).mono ?_
    have w1 := vsQ_keyM_wt hpN hDN (U.map (vsWLin I.p (vsQD s) A))
    have w2 := vsQ_keyM_wt hpN hDN V
    have w3 := wt_list2_le (natList t) (natList (vsQTKeyM V))
    have hlt : t.length + 1 ≤ N + 1 := by simp only [t]; rw [vsQTKeyM_len]; omega
    exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hlt) (by simp only [t] at *; omega)
  have dfd := Det.call (Det.mk2 dit dK) (find_spec hfnd hq)
  have efd : (l.map fun V => natList (vsQTKeyM V)).findIdx q =
      (l.map vsQTKeyM).findIdx fun k => decide (t = k) := by
    rw [List.findIdx_map, List.findIdx_map]
    congr 1
    funext V
    simp only [Function.comp_apply, q, decide_eq_decide]
    exact ⟨fun h => vsQ_natList_inj h, fun h => h ▸ rfl⟩
  rw [efd] at dfd
  refine FunDet.intro hfi (dfd.mono ?_)
  -- weights
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at *
  have wt1 : (natList t).wt ≤ 5 * (N + 1) ^ 2 := vsQ_keyM_wt hpN hDN (U.map (vsWLin I.p (vsQD s) A))
  have wx : x.wt ≤ 5 * (N + 1) ^ 2 := vsQ_keyM_wt hpN hDN U
  have wKV : KV.wt ≤ 20 * (N + 1) ^ 3 := vsQ_keysM_wt hpN hDN l hl
  have hDN' : vsQD s ≤ N := by nlinarith
  have wA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hDN') (by rw [hA.2]; omega)
  have wc := wt_list3_le (.nat I.p) (.nat (vsQD s)) (vsWVs A)
  have := wt_nat_le I.p; have := wt_nat_le (vsQD s); have := wt_nat_le 0; have := wt_nat_le 1
  have w2 := wt_list2_le c KV
  have w3 := wt_list2_le (.list [c, KV]) x
  have w4 := wt_list2_le c x
  have w5 := wt_list2_le (natList t) KV
  have hfl : (l.map vsQTKeyM).findIdx (fun k => decide (t = k)) ≤ l.length := by
    have := List.findIdx_le_length (p := fun k => decide (t = k)) (xs := l.map vsQTKeyM)
    simpa using this
  have wf := wt_nat_le ((l.map vsQTKeyM).findIdx fun k => decide (t = k))
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q36 : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q46 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hB1 : l.length * (loopModK * (N + 1) * (30 * (N + 1) ^ 2 + N + 10)) ≤
      (N + 1) * (1000 * (N + 1) * (40 * (N + 1) ^ 2)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (le_refl _) (by omega))
  have eB1 : (N + 1) * (1000 * (N + 1) * (40 * (N + 1) ^ 2)) = 40000 * (N + 1) ^ 4 := by ring
  have hB2 : loopModK * (l.length + 1) * ((Val.list [natList t, KV]).wt + 2 * l.length + 3) ≤
      1000 * (N + 1) * (100 * (N + 1) ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eB2 : 1000 * (N + 1) * (100 * (N + 1) ^ 3) = 100000 * (N + 1) ^ 4 := by ring
  have mk : loopModK = 1000 := rfl
  rw [show vsQTKeyM (Submodule.map (vsWLin I.p (vsQD s) A) U) = t from rfl]
  rw [show Val.list (List.map (fun V => natList (vsQTKeyM V)) l) = KV from rfl]
  have ec : c.wt = (Val.list [Val.nat I.p, Val.nat (vsQD s), vsWVs A]).wt := rfl
  clear_value c KV x t
  omega

theorem vsQ_keyM_enc_inj :
    Function.Injective fun V : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p) => natList (vsQTKeyM V) :=
  fun _ _ h => vsQTKeyM_injective (vsQ_natList_inj h)

set_option maxHeartbeats 4000000 in
theorem vsQATbOut_spec {P : Program} {fo mpi fi it tl chk ker img key cat appd fnd eq : ℕ}
    (hfo : P.funs[fo]? = some (vsQATbOutE mpi)) (hmpi : P.HasAt mpi (mapFuns mpi fi))
    (hfi : P.funs[fi]? = some (vsQATbInE it fnd)) (HI : VsQTItemAt P it tl chk ker img key cat appd)
    (hfnd : P.HasAt fnd (findFuns fnd eq)) (heq : P.HasAt eq (eqNatsFuns eq))
    {N : ℕ} (hpN : I.p ≤ N) (hDN : vsQD s * vsQD s + 1 ≤ N) {A : List (List ℕ)}
    (hA : VsWSq I.p (vsQD s) A) (l : List (Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)))
    (hl : l.length ≤ N) :
    FunDet P fo (.list [.list [.list [.nat I.p, .nat (vsQD s)], .list (l.map fun V => natList (vsQTKeyM V))],
        vsWVs A])
      (natList (l.map fun U => (l.map vsQTKeyM).findIdx fun k =>
        decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k)))
      (10 ^ 14 * (N + 1) ^ 7) := by
  set c := Val.list [.nat I.p, .nat (vsQD s)]
  set KV := Val.list (l.map fun V => natList (vsQTKeyM V))
  have g0 := Det.arg' (P := P) (rest := []) (vs := [.list [c, KV], vsWVs A]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.list [c, KV], vsWVs A]) (j := 1) rfl
  have dc := Det.get' g0 (Det.nat 0) (show [c, KV][0]? = some c from rfl)
  have dK := Det.get' g0 (Det.nat 1) (show [c, KV][1]? = some KV from rfl)
  have dp := Det.get' dc (Det.nat 0) (show [Val.nat I.p, .nat (vsQD s)][0]? = some (.nat I.p) from rfl)
  have dD := Det.get' dc (Det.nat 1) (show [Val.nat I.p, .nat (vsQD s)][1]? = some (.nat (vsQD s)) from rfl)
  have hmap := vsQ_map hmpi (c := .list [.list [.nat I.p, .nat (vsQD s), vsWVs A], KV]) l
    (fun V => natList (vsQTKeyM V))
    (fun U => .nat ((l.map vsQTKeyM).findIdx fun k => decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k)))
    vsQ_keyM_enc_inj (fun U _ => vsQATbIn_spec hfi HI hfnd heq hpN hDN hA l hl U)
  have dm := Det.call (Det.mk2 (Det.mk2 (Det.mk3 dp dD g1) dK) dK) hmap
  have eo : Val.list (l.map fun U => Val.nat ((l.map vsQTKeyM).findIdx fun k =>
      decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k))) =
      natList (l.map fun U => (l.map vsQTKeyM).findIdx fun k =>
        decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k)) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [eo] at dm
  refine FunDet.intro hfo (dm.mono ?_)
  -- weights
  have wKV : KV.wt ≤ 20 * (N + 1) ^ 3 := vsQ_keysM_wt hpN hDN l hl
  have hDN' : vsQD s ≤ N := by nlinarith
  have wA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hDN') (by rw [hA.2]; omega)
  have := wt_nat_le I.p; have := wt_nat_le (vsQD s); have := wt_nat_le 0; have := wt_nat_le 1
  have wc := wt_list2_le (.nat I.p) (.nat (vsQD s))
  have ec : c.wt = (Val.list [Val.nat I.p, Val.nat (vsQD s)]).wt := rfl
  have w3 := wt_list3_le (.nat I.p) (.nat (vsQD s)) (vsWVs A)
  have w2 := wt_list2_le c KV
  have w2' := wt_list2_le (.list [c, KV]) (vsWVs A)
  have w4 := wt_list2_le (.list [.nat I.p, .nat (vsQD s), vsWVs A]) KV
  have w5 := wt_list2_le (.list [.list [.nat I.p, .nat (vsQD s), vsWVs A], KV]) KV
  have wo : (natList (l.map fun U => (l.map vsQTKeyM).findIdx fun k =>
      decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k))).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      obtain ⟨U, -, rfl⟩ := List.mem_map.1 hy
      have := List.findIdx_le_length (p := fun k => decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k))
        (xs := l.map vsQTKeyM)
      simp only [List.length_map] at this
      omega) (by simp; omega)
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q67 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have q47 : (N + 1) ^ 4 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hB1 : l.length * (10 ^ 12 * (N + 1) ^ 6) ≤ (N + 1) * (10 ^ 12 * (N + 1) ^ 6) :=
    Nat.mul_le_mul_right _ (by omega)
  have eB1 : (N + 1) * (10 ^ 12 * (N + 1) ^ 6) = 10 ^ 12 * (N + 1) ^ 7 := by ring
  have hB2 : mapK * (l.length + 1) * ((Val.list [Val.list [Val.list [Val.nat I.p, Val.nat (vsQD s),
      vsWVs A], KV], KV]).wt + (natList (l.map fun U => (l.map vsQTKeyM).findIdx fun k =>
      decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k))).wt + 1) ≤
      1000 * (N + 1) * (1000 * (N + 1) ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eB2 : 1000 * (N + 1) * (1000 * (N + 1) ^ 3) = 10 ^ 6 * (N + 1) ^ 4 := by ring
  have mk : mapK = 1000 := rfl
  rw [show Val.list (List.map (fun V => natList (vsQTKeyM V)) l) = KV from rfl] at *
  clear_value c KV
  omega

/-- The cost of the table program. -/
def vsQATblCost (N : ℕ) : ℕ := 10 ^ 16 * (N + 1) ^ 8

theorem vsQATb_eq_map (Lb : List (List (List ℕ))) (A : List (List ℕ)) :
    vsQATb s Lb A = ((vsQAPcs s Lb).map (vsWSp I.p (vsQD s))).map fun U =>
      (((vsQAPcs s Lb).map (vsWSp I.p (vsQD s))).map vsQTKeyM).findIdx fun k =>
        decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k) := by
  simp [vsQATb, vsQAKM, List.map_map, Function.comp_def]

set_option maxHeartbeats 4000000 in
/-- **The table program.** -/
theorem vsQATbl_spec' {P : Program} {f mpk ki key cat appd mpo fo mpi fi it tl chk ker img key' cat' appd'
    fnd eq : ℕ} (L : VsQATblAt P f mpk ki key cat appd mpo fo mpi fi it tl chk ker img key' cat' appd' fnd eq)
    {N : ℕ} (hpN : I.p ≤ N) (hDN : vsQD s * vsQD s + 1 ≤ N) (Lb : List (List (List ℕ)))
    (hPf : ∀ Q ∈ vsQAPcs s Lb, VsWFit I.p (vsQD s) Q ∧ Q.length ≤ N) (hPl : (vsQAPcs s Lb).length ≤ N)
    {Ms : List (List (List ℕ))} (hMs : ∀ A ∈ Ms, VsWSq I.p (vsQD s) A) (hMl : Ms.length ≤ N) :
    FunDet P f (.list [.list [.nat I.p, .nat (vsQD s)], vsFMatsVal (vsQAPcs s Lb), vsFMatsVal Ms])
      (.list [.nat (vsQAPcs s Lb).length, .list (Ms.map fun A => natList (vsQATb s Lb A))])
      (vsQATblCost N) := by
  set c := Val.list [.nat I.p, .nat (vsQD s)]
  set Pcs := vsQAPcs s Lb
  set l := Pcs.map (vsWSp I.p (vsQD s))
  set vs := [c, vsFMatsVal Pcs, vsFMatsVal Ms]
  have g0 := Det.arg' (P := P) (rest := []) (vs := vs) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := vs) (j := 1) rfl
  -- the keys
  have hk := vsQ_map L.hmpk (c := c) Pcs (fun M => Val.list (M.map natList))
    (fun Q => natList (vsQTKeyM (vsWSp I.p (vsQD s) Q))) vsQ_mats_inj
    (fun Q hQ => vsQTKeyItem_spec L.HK hpN hDN (hPf Q hQ).1 (hPf Q hQ).2)
  have dk := Det.call (Det.mk2 g0 g1) hk
  have ek : Val.list (Pcs.map fun Q => natList (vsQTKeyM (vsWSp I.p (vsQD s) Q))) =
      Val.list (l.map fun V => natList (vsQTKeyM V)) := by simp [l, List.map_map, Function.comp_def]
  rw [ek] at dk
  set KV := Val.list (l.map fun V => natList (vsQTKeyM V))
  -- the tables
  set E1 := [Val.list vs, KV]
  have h0 := Det.arg' (P := P) (rest := [KV]) (vs := vs) (j := 0) rfl
  have h2 := Det.arg' (P := P) (rest := [KV]) (vs := vs) (j := 2) rfl
  have hl : l.length ≤ N := by simp [l]; omega
  have ho := vsQ_map L.hmpo (c := .list [c, KV]) Ms (fun M => Val.list (M.map natList))
    (fun A => natList (l.map fun U => (l.map vsQTKeyM).findIdx fun k =>
        decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k))) vsQ_mats_inj
    (fun A hA => by
      have := vsQATbOut_spec L.hfo L.hmpi L.hfi L.HI L.hfnd L.heq hpN hDN (hMs A hA) l hl
      exact this)
  have dt := Det.call (Det.mk2 (Det.mk2 h0 (Det.var' (P := P) (env := E1) (i := 1) rfl)) h2) ho
  have et : Val.list (Ms.map fun A => natList (l.map fun U => (l.map vsQTKeyM).findIdx fun k =>
      decide (vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) = k))) =
      Val.list (Ms.map fun A => natList (vsQATb s Lb A)) := by
    congr 1; refine List.map_congr_left fun A _ => ?_; rw [vsQATb_eq_map]
  rw [et] at dt
  set TV := Val.list (Ms.map fun A => natList (vsQATb s Lb A))
  set E2 := [Val.list vs, KV, TV]
  have a1 := Det.arg' (P := P) (rest := [KV, TV]) (vs := vs) (j := 1) rfl
  have dlen := Det.length a1
  have dout := Det.mk2 dlen (Det.var' (P := P) (env := E2) (i := 2) rfl)
  simp only [List.length_map] at dout
  refine FunDet.intro L.hf ((Det.letE dk (Det.letE dt dout)).mono ?_)
  -- weights
  have hDN' : vsQD s ≤ N := by nlinarith
  have wPcs : (vsFMatsVal Pcs).wt ≤ 40 * (N + 1) ^ 4 := by
    have hw := vs_wt_list_le_of (Pcs.map fun M => Val.list (M.map natList)) (c := 11 * (N + 1) ^ 3 + 4) (by
      intro v hv
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hv
      exact wt_vsWVs_le (VsWFit.bnd (hPf Q hQ).1 hpN hDN') (by have := (hPf Q hQ).2; omega))
    rw [List.length_map] at hw
    have h1 : Pcs.length * (2 * (11 * (N + 1) ^ 3 + 4) + 1) ≤ (N + 1) * (31 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 3 (N + 1) (by omega); omega)
    have e : (N + 1) * (31 * (N + 1) ^ 3) = 31 * (N + 1) ^ 4 := by ring
    have := Nat.one_le_pow 4 (N + 1) (by omega)
    exact hw.trans (by omega)
  have wMs : (vsFMatsVal Ms).wt ≤ 40 * (N + 1) ^ 4 :=
    wt_vsFMatsVal_le hpN hDN' (fun A hA => vsFSq_of_wSq (hMs A hA)) (by omega)
  have wKV : KV.wt ≤ 20 * (N + 1) ^ 3 := vsQ_keysM_wt hpN hDN l hl
  have wTV : TV.wt ≤ 20 * (N + 1) ^ 3 := by
    have hw := vs_wt_list_le_of (Ms.map fun A => natList (vsQATb s Lb A)) (c := 5 * (N + 1) ^ 2) (by
      intro v hv
      obtain ⟨A, -, rfl⟩ := List.mem_map.1 hv
      refine wt_natList_le_sq (fun y hy => ?_) (by simp [vsQATb]; omega)
      simp only [vsQATb, List.mem_map] at hy
      obtain ⟨Q, -, rfl⟩ := hy
      have := List.findIdx_le_length (xs := vsQAKM s Lb)
        (p := fun k => decide (vsQTKeyM ((vsWSp I.p (vsQD s) Q).map (vsWLin I.p (vsQD s) A)) = k))
      have hl2 : (vsQAKM s Lb).length = Pcs.length := by simp [vsQAKM, Pcs]
      omega)
    rw [List.length_map] at hw
    have h1 : Ms.length * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
    have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    have := Nat.one_le_pow 3 (N + 1) (by omega)
    exact hw.trans (by omega)
  have := wt_nat_le I.p; have := wt_nat_le (vsQD s); have := wt_nat_le Pcs.length
  have wc := wt_list2_le (.nat I.p) (.nat (vsQD s))
  have ec : c.wt = (Val.list [Val.nat I.p, Val.nat (vsQD s)]).wt := rfl
  have wvs := wt_list3_le c (vsFMatsVal Pcs) (vsFMatsVal Ms)
  have evs : (Val.list vs).wt = (Val.list [c, vsFMatsVal Pcs, vsFMatsVal Ms]).wt := rfl
  have w1 := wt_list2_le c (vsFMatsVal Pcs)
  have w2 := wt_list2_le c KV
  have w3 := wt_list2_le (.list [c, KV]) (vsFMatsVal Ms)
  have w4 := wt_list2_le (.nat Pcs.length) TV
  have eP : Val.list (List.map (fun M => Val.list (List.map natList M)) Pcs) = vsFMatsVal Pcs := rfl
  have eM : Val.list (List.map (fun M => Val.list (List.map natList M)) Ms) = vsFMatsVal Ms := rfl
  rw [eP, eM]
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q58 : (N + 1) ^ 5 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have q78 : (N + 1) ^ 7 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have q67 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hA1 : Pcs.length * (10 ^ 9 * (N + 1) ^ 6) ≤ (N + 1) * (10 ^ 9 * (N + 1) ^ 6) :=
    Nat.mul_le_mul_right _ (by omega)
  have eA1 : (N + 1) * (10 ^ 9 * (N + 1) ^ 6) = 10 ^ 9 * (N + 1) ^ 7 := by ring
  have hA2 : mapK * (Pcs.length + 1) * ((Val.list [c, vsFMatsVal Pcs]).wt + KV.wt + 1) ≤
      1000 * (N + 1) * (200 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eA2 : 1000 * (N + 1) * (200 * (N + 1) ^ 4) = 200000 * (N + 1) ^ 5 := by ring
  have hB1 : Ms.length * (10 ^ 14 * (N + 1) ^ 7) ≤ (N + 1) * (10 ^ 14 * (N + 1) ^ 7) :=
    Nat.mul_le_mul_right _ (by omega)
  have eB1 : (N + 1) * (10 ^ 14 * (N + 1) ^ 7) = 10 ^ 14 * (N + 1) ^ 8 := by ring
  have hB2 : mapK * (Ms.length + 1) * ((Val.list [Val.list [c, KV], vsFMatsVal Ms]).wt + TV.wt + 1) ≤
      1000 * (N + 1) * (400 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eB2 : 1000 * (N + 1) * (400 * (N + 1) ^ 4) = 400000 * (N + 1) ^ 5 := by ring
  have mk : mapK = 1000 := rfl
  unfold vsQATblCost
  clear_value c KV TV
  omega

end GI.Impl
