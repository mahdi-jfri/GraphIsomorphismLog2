module

public import Workspace.Impl.VsQTAct
public import Workspace.Impl.VsWProgKey
public import Workspace.Impl.VsWProgImg
public import Workspace.Impl.VsWProgKer
public import Workspace.Impl.VsWProgMC
public import Workspace.Impl.VsWProgEig
public import Workspace.Lang.Lib.LinIntTail

@[expose] public section

/-!
# The image of one subspace given by its key

On `[[p, D, A], 1 :: K]` with `K` the flattened key of a subspace `U` and `A` a stored matrix,
the program returns `1 :: K'` with `K'` the flattened key of the image of `U` by `A`: cut `K`
into `D` rows, take the kernel (it spans `U`, `vsWKey_ker`), take the images, take the key.

* `vsQTItemE`, `vsQTItem_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved

theorem vsQT_chunk_natList (k m : ℕ) (xs : List ℕ) :
    (vsQChunk (Val.nat 0) k m (xs.map Val.nat)).map Val.list = (vsQChunk 0 k m xs).map natList := by
  simp only [vsQChunk, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, natList, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i * k + j]? <;> rfl

theorem vsQT_flatten_natList (xss : List (List ℕ)) :
    Val.list (xss.map fun x => x.map Val.nat).flatten = natList xss.flatten := by
  simp [natList, List.map_flatten]

/-- The image of one subspace, on `[[p, D, A], 1 :: K]`. -/
def vsQTItemE (tl chk ker img key cat appd : ℕ) : Expr :=
  .letE (.call chk (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 1)) (.call tl (arg 1))))
  (.letE (.call ker (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
  (.letE (.call img (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (.var 2)))
  (.letE (.call key (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.var 3)))
  (.call appd (mk2 (mk1 (.nat 1)) (.call cat (.var 4)))))))

/-- The layout of the item program. -/
structure VsQTItemAt (P : Program) (f tl chk ker img key cat appd : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQTItemE tl chk ker img key cat appd)
  htl : P.HasAt tl (linTailFuns tl)
  hchk : P.HasAt chk (vsQChunkFuns chk)
  hker : P.HasAt ker (vsWKerFuns ker)
  himg : P.HasAt img (vsWImgFuns img)
  hkey : P.HasAt key (vsWKeyFuns key)
  hcat : P.HasAt cat (vsWFlatFuns cat)
  happd : P.HasAt appd (appendFuns appd)

/-- What the item computes. -/
noncomputable def vsQTItemL (p D : ℕ) (A K : List (List ℕ)) : List ℕ :=
  1 :: (vsWKey p D (vsWImg p D A (vsWKer p K))).flatten

set_option maxHeartbeats 8000000 in
/-- **The item program.** -/
theorem vsQTItem_spec {P : Program} {f tl chk ker img key cat appd : ℕ}
    (H : VsQTItemAt P f tl chk ker img key cat appd) {p N D : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hDN : D * D + 1 ≤ N) {A K : List (List ℕ)} (hA : VsWSq p D A) (hK : VsWFit p D K)
    (hKl : K.length = D) :
    FunDet P f (.list [.list [.nat p, .nat D, vsWVs A], natList (1 :: K.flatten)])
      (natList (vsQTItemL p D A K)) (10 ^ 11 * (N + 1) ^ 6) := by
  have hp1 := hp.one_lt
  have hDN' : D ≤ N := by nlinarith
  set c := Val.list [.nat p, .nat D, vsWVs A]
  set x := natList (1 :: K.flatten)
  have g0 := Det.arg' (P := P) (rest := []) (vs := [c, x]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, x]) (j := 1) rfl
  have rc : ∀ rest k v, [Val.nat p, .nat D, vsWVs A][k]? = some v →
      Det P (.list [c, x] :: rest) (.get (arg 0) (.nat k)) v _ := fun rest k v hv =>
    Det.get' (Det.arg' (P := P) (rest := rest) (vs := [c, x]) (j := 0) rfl) (Det.nat k) hv
  have hKf : K.flatten.length = D * D := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => D) fun r hr => (hK r hr).2]
    simp [hKl]
  -- weights
  have wK : (natList (1 :: K.flatten)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
        exact ((hK r hr).1 y hy).le.trans hpN) (by simp [hKf]; omega)
  have wA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hDN') (by rw [hA.2]; omega)
  -- the tail
  have dtl := Det.call g1 (linTail_spec H.htl ((1 :: K.flatten).map Val.nat))
  have etl : Val.list (List.drop 1 ((1 :: K.flatten).map Val.nat)) = .list (K.flatten.map Val.nat) := rfl
  rw [etl] at dtl
  -- the rows of the key
  have dch := Det.call (Det.mk3 (rc [] 1 _ rfl) (rc [] 1 _ rfl) dtl)
    (vsQChunk_spec H.hchk (k := D) (m := D) (N := N) (vs := K.flatten.map Val.nat) (W := 5 * (N + 1) ^ 2)
      (by rw [List.length_map, hKf]) hDN' hDN' (by
        have := wt_natList_le_sq (B := N) (xs := K.flatten) (fun y hy => by
          obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
          exact ((hK r hr).1 y hy).le.trans hpN) (by omega)
        exact this))
  rw [vsQT_chunk_natList] at dch
  have hKc : vsQChunk 0 D D K.flatten = K := by
    have := vsQChunk_flatten (0 : ℕ) D K fun r hr => (hK r hr).2
    rwa [hKl] at this
  rw [hKc] at dch
  have eK : Val.list (K.map natList) = vsWVs K := rfl
  rw [eK] at dch
  -- the kernel
  set X := Val.list [c, x]
  have hKer := vsWKer_fit hp1 hK
  rw [hKl] at hKer
  have hKerl := vsWKer_length_le hp1 (N := N) hpN (by nlinarith) hK (by omega)
  have dker := Det.call (Det.mk2 (rc [vsWVs K] 0 _ rfl) (Det.var' (P := P) (env := [X, vsWVs K]) (i := 1) rfl))
    (vsWKer_spec H.hker hp1 hpN hDN' hK (by omega))
  -- the images
  set Kr := vsWKer p K
  have dimg := Det.call (Det.mk4 (rc [vsWVs K, vsWVs Kr] 0 _ rfl) (rc [vsWVs K, vsWVs Kr] 1 _ rfl)
      (rc [vsWVs K, vsWVs Kr] 2 _ rfl) (Det.var' (P := P) (env := [X, vsWVs K, vsWVs Kr]) (i := 2) rfl))
    (vsWImg_spec H.himg hp.pos hpN hDN' hA.1 (by rw [hA.2]; exact hDN') (by rw [hA.2]; exact hKer)
      (by omega))
  set Im := vsWImg p D A Kr
  have hIm : VsWFit p D Im := vsWImg_fit hp.pos hA Kr
  have hIml : Im.length ≤ N := by simp [Im, vsWImg]; omega
  -- the key
  have dkey := Det.call (Det.mk3 (rc [vsWVs K, vsWVs Kr, vsWVs Im] 0 _ rfl)
      (rc [vsWVs K, vsWVs Kr, vsWVs Im] 1 _ rfl) (Det.var' (P := P) (env := [X, vsWVs K, vsWVs Kr, vsWVs Im]) (i := 3) rfl))
    (vsWKey_spec H.hkey hp1 hpN hDN' hIm hIml)
  set Ky := vsWKey p D Im
  have hKy : VsWFit p D Ky := vsWKey_fit hp1 Im
  have hKyl : Ky.length = D := vsWKey_length D Im
  -- flatten and mark
  set E4 := [X, vsWVs K, vsWVs Kr, vsWVs Im, vsWVs Ky]
  have hKyf : Ky.flatten.length = D * D := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => D) fun r hr => (hKy r hr).2]
    simp [hKyl]
  have wKyf : (natList Ky.flatten).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      exact ((hKy r hr).1 y hy).le.trans hpN) (by omega)
  have wKy := wt_vsWVs_le (VsWFit.bnd hKy hpN hDN') (by omega)
  have e1 : Val.list ((Ky.map fun r => r.map Val.nat).map Val.list) = vsWVs Ky := by
    simp [vsWVs, natList, List.map_map, Function.comp_def]
  have dv : Det P E4 (.var 4) (vsWVs Ky) _ := Det.var' (P := P) (env := E4) (i := 4) rfl
  rw [← e1] at dv
  have dcat := Det.call dv
    (vsWConcat_spec H.hcat (N := N) (Ky.map fun r => r.map Val.nat) (by simp; omega)
      (fun xs hxs => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hxs
        simp [(hKy r hr).2]; omega)
      (by rw [vsQT_flatten_natList]; have : 5 * (N + 1) ^ 2 ≤ 1000 * (N + 1) ^ 4 := by
            have := Nat.pow_le_pow_right (show 1 ≤ N + 1 by omega) (show 2 ≤ 4 by norm_num); omega
          omega)
      (by
        have e : Val.list ((Ky.map fun r => r.map Val.nat).map Val.list) = vsWVs Ky := by
          simp [vsWVs, natList, List.map_map, Function.comp_def]
        rw [e]; have : 11 * (N + 1) ^ 3 + 4 ≤ 1000 * (N + 1) ^ 4 := by
            have := Nat.pow_le_pow_right (show 1 ≤ N + 1 by omega) (show 3 ≤ 4 by norm_num)
            have := Nat.one_le_pow 3 (N + 1) (by omega); omega
        omega))
  rw [vsQT_flatten_natList] at dcat
  have kap : FunDet P appd (.list [.list [.nat 1], natList Ky.flatten]) (natList (1 :: Ky.flatten))
      (10 ^ 6 * (N + 1) ^ 3) := by
    refine (append_spec H.happd [.nat 1] (Ky.flatten.map Val.nat)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have w2 := wt_list2_le (.list [.nat 1]) (natList Ky.flatten)
    have w1 : (Val.list [.nat 1]).wt ≤ 10 := by decide
    have wo : (natList (1 :: Ky.flatten)).wt ≤ 5 * (N + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
          exact ((hKy r hr).1 y hy).le.trans hpN) (by rw [List.length_cons, hKyf]; omega)
    have e2 : (Val.list ([Val.nat 1] ++ Ky.flatten.map Val.nat)).wt = (natList (1 :: Ky.flatten)).wt := rfl
    have e3 : (Val.list [Val.list [Val.nat 1], Val.list (Ky.flatten.map Val.nat)]).wt =
      (Val.list [.list [.nat 1], natList Ky.flatten]).wt := rfl
    have hll : (Ky.flatten.map Val.nat).length = D * D := by rw [List.length_map, hKyf]
    have hl : (Ky.flatten.map Val.nat).length + 1 ≤ N + 1 := by omega
    have h4 : ((Ky.flatten.map Val.nat).length + 1) *
        ((Val.list [Val.list [Val.nat 1], Val.list (Ky.flatten.map Val.nat)]).wt +
          (Ky.flatten.map Val.nat).length + (Val.list ([Val.nat 1] ++ Ky.flatten.map Val.nat)).wt + 1) ≤
        (N + 1) * (100 * (N + 1) ^ 2) := Nat.mul_le_mul hl (by
          have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
          omega)
    have e : (N + 1) * (100 * (N + 1) ^ 2) = 100 * (N + 1) ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * ((Ky.flatten.map Val.nat).length + 1) * _ = 1000 * (((Ky.flatten.map Val.nat).length + 1) *
          ((Val.list [Val.list [Val.nat 1], Val.list (Ky.flatten.map Val.nat)]).wt +
          (Ky.flatten.map Val.nat).length + (Val.list ([Val.nat 1] ++ Ky.flatten.map Val.nat)).wt + 1)) := by
            ring
      _ ≤ _ := by omega
  have dap := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := E4) 1)) dcat) kap
  have dall := Det.letE dch (Det.letE dker (Det.letE dimg (Det.letE dkey dap)))
  refine FunDet.intro H.hf (dall.mono ?_)
  -- the cost
  have wKr := wt_vsWVs_le (VsWFit.bnd hKer hpN hDN') (by omega)
  have wIm := wt_vsWVs_le (VsWFit.bnd hIm hpN hDN') (by omega)
  have wKv := wt_vsWVs_le (VsWFit.bnd hK hpN hDN') (by omega)
  have wo : (natList (1 :: Ky.flatten)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
        exact ((hKy r hr).1 y hy).le.trans hpN) (by rw [List.length_cons, hKyf]; omega)
  have wc := wt_list3_le (.nat p) (.nat D) (vsWVs A)
  have wX := wt_list2_le c x
  have := wt_nat_le p; have := wt_nat_le D; have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have wtl : linTailCost (Val.list ((1 :: K.flatten).map Val.nat)).wt ≤ 10 ^ 4 * (6 * (N + 1) ^ 2) ^ 3 := by
    unfold linTailCost
    have e : (Val.list ((1 :: K.flatten).map Val.nat)).wt = (natList (1 :: K.flatten)).wt := rfl
    rw [e]
    have h1 : (natList (1 :: K.flatten)).wt + 1 ≤ 6 * (N + 1) ^ 2 := by
      have := Nat.one_le_pow 2 (N + 1) (by omega); omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
  have e6 : (6 * (N + 1) ^ 2) ^ 3 = 216 * (N + 1) ^ 6 := by ring
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q56 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have ech : 10 ^ 8 * (N + 1) ^ 4 * (5 * (N + 1) ^ 2 + (N + 1) ^ 2) = 6 * 10 ^ 8 * (N + 1) ^ 6 := by ring
  have eKf : (Val.list (K.flatten.map Val.nat)).wt = (natList K.flatten).wt := rfl
  have wKf : (natList K.flatten).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      exact ((hK r hr).1 y hy).le.trans hpN) (by omega)
  have eKy : (Val.list ((Ky.map fun r => r.map Val.nat).map Val.list)).wt = (vsWVs Ky).wt := by rw [e1]
  have eo : (natList (vsQTItemL p D A K)).wt = (natList (1 :: Ky.flatten)).wt := rfl
  have w2 := wt_list2_le (Val.list [.nat 1]) (natList Ky.flatten)
  have w1 : (Val.list [.nat 1]).wt ≤ 10 := by decide
  have w3 := wt_list3_le (.nat p) (.nat D) (vsWVs K)
  have w2' := wt_list2_le (.nat p) (vsWVs K)
  have w4 := wt_list4_le (.nat p) (.nat D) (vsWVs A) (vsWVs Kr)
  have w3' := wt_list3_le (.nat p) (.nat D) (vsWVs Im)
  have w3c := wt_list3_le (.nat D) (.nat D) (.list (K.flatten.map Val.nat))
  have ecx : X.wt = (Val.list [c, x]).wt := rfl
  have eccc : c.wt = (Val.list [.nat p, .nat D, vsWVs A]).wt := rfl
  have exx : x.wt = (natList (1 :: K.flatten)).wt := rfl
  clear_value c x X Kr Im Ky E4
  omega

variable {I : VecStabInst}

/-- **What the item computes**, on subspaces: the marked key of the image. -/
theorem vsQTItemL_eq {s : VsQSt I} {A : List (List ℕ)} (hA : VsWSq I.p (vsQD s) A)
    (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    vsQTItemL I.p (vsQD s) A (vsQTKeyU U) = vsQTKeyM (U.map (vsWLin I.p (vsQD s) A)) := by
  have hp := I.prime
  have hK : VsWFit I.p (vsQD s) (vsQTKeyU U) := vsWKey_fit hp.one_lt _
  have hKl : (vsQTKeyU U).length = vsQD s := vsWKey_length _ _
  have hKer : VsWFit I.p (vsQD s) (vsWKer I.p (vsQTKeyU U)) := by
    have := vsWKer_fit hp.one_lt hK; rwa [hKl] at this
  have hsp1 : vsWSp I.p (vsQD s) (vsWKer I.p (vsQTKeyU U)) = U := by
    rw [vsQTKeyU, vsWKey_ker hp (vsQTBas_fit U), vsQTBas_span]
  have hIm := vsWImg_fit hp.pos hA (vsWKer I.p (vsQTKeyU U))
  have hsp2 : vsWSp I.p (vsQD s) (vsWImg I.p (vsQD s) A (vsWKer I.p (vsQTKeyU U))) =
      U.map (vsWLin I.p (vsQD s) A) := by
    rw [vsWImg_span hA, hsp1]
  have hkey : vsWKey I.p (vsQD s) (vsWImg I.p (vsQD s) A (vsWKer I.p (vsQTKeyU U))) =
      vsQTKeyU (U.map (vsWLin I.p (vsQD s) A)) := by
    rw [vsQTKeyU]
    exact (vsWKey_eq_iff hp hIm (vsQTBas_fit _)).2 (by rw [hsp2, vsQTBas_span])
  rw [vsQTItemL, hkey]
  rfl

end GI.Impl
