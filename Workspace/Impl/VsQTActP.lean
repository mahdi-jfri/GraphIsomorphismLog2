import Workspace.Impl.VsQTItem
import Workspace.Impl.VsBFldAP
import Workspace.Impl.VsWProgComp

/-!
# The action program on tuples of local subspaces

On `[[[Γ, fr], p, D], g, 0 :: key(ys)]` the program returns `0 :: key(Λ(g) ys)`: the local matrix
of `g`, the tail, the pieces of the key (one per subspace), the image of each piece
(`vsQTItem_spec`), joined, with `0` in front.

* `vsQTActE`, `vsQTAct_spec`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The context of the action. -/
noncomputable def vsQTCtx (s : VsQSt I) : Val :=
  .list [.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)], .nat I.p, .nat (vsQD s)]

/-- The action, on `[ctx, g, 0 :: key]`. -/
def vsQTActE (itm tl chk mp cat appd : ℕ) : Expr :=
  .letE (.call itm (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
  (.letE (.call tl (arg 2))
  (.letE (.call chk (mk3
      (.arith .add (.arith .mul (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 2))) (.nat 1))
      (.arith .div (.length (.var 2))
        (.arith .add (.arith .mul (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 2))) (.nat 1)))
      (.var 2)))
  (.call appd (mk2 (mk1 (.nat 0))
    (.call cat (.call mp (mk2 (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (.var 1)) (.var 3))))))))

/-- The layout of the action program. -/
structure VsQTActAt (P : Program) (f itm loc phi tl chk mp fI tl' chk' ker img key cat appd : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQTActE itm tl chk mp cat appd)
  hitm : P.funs[itm]? = some (vsQLCItemE phi loc)
  hloc : P.HasAt loc (vsWLocFuns loc)
  htl : P.HasAt tl (linTailFuns tl)
  hchk : P.HasAt chk (vsQChunkFuns chk)
  hmp : P.HasAt mp (mapFuns mp fI)
  hI : VsQTItemAt P fI tl' chk' ker img key cat appd
  hcat : P.HasAt cat (vsWFlatFuns cat)
  happd : P.HasAt appd (appendFuns appd)

set_option maxHeartbeats 16000000 in
/-- **The action program.** -/
theorem vsQTAct_spec {P : Program} {f itm loc phi tl chk mp fI tl' chk' ker img key cat appd Cφ S Tm : ℕ}
    (H : VsQTActAt P f itm loc phi tl chk mp fI tl' chk' ker img key cat appd)
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    {ys : VsQTup s} (hb : ys.length ≤ S) :
    FunDet P f (.list [vsQTCtx s, encPerm g, natList (0 :: vsQTKey ys)])
      (natList (0 :: vsQTKey (vsQTAct s g ys))) (Cφ + 10 ^ 15 * (S ^ 3 + 1) ^ 7) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hpS := hS.p
  set N := S ^ 3
  have hS3 : S ≤ N := Nat.le_self_pow (by norm_num) _
  have hS23 : S ^ 2 ≤ N := Nat.pow_le_pow_right hS1 (by norm_num)
  have hDD : vsQD s * vsQD s + 1 ≤ N := by
    have h1 : vsQD s + 1 ≤ S := by omega
    have h2 := Nat.mul_le_mul h1 h1
    have e : (vsQD s + 1) * (vsQD s + 1) = vsQD s * vsQD s + 2 * vsQD s + 1 := by ring
    have h3 : S * S ≤ N := by rw [← sq]; exact hS23
    omega
  set A := Val.list [vsQTCtx s, encPerm g, natList (0 :: vsQTKey ys)]
  have g1 := Det.arg' (P := P) (rest := []) (vs := [vsQTCtx s, encPerm g, natList (0 :: vsQTKey ys)]) (j := 1) rfl
  have rc : ∀ rest k v, [Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)], .nat I.p, .nat (vsQD s)][k]? =
      some v → Det P (A :: rest) (.get (arg 0) (.nat k)) v _ := fun rest k v hv =>
    Det.get' (Det.arg' (P := P) (rest := rest) (vs := [vsQTCtx s, encPerm g, natList (0 :: vsQTKey ys)])
      (j := 0) rfl) (Det.nat k) hv
  -- the local matrix of `g`
  have ditm := Det.call (Det.mk2 (rc [] 0 _ rfl) g1) (vsB_item_spec H.hitm H.hloc hphi hS hs hg)
  rw [vsB_loc_eq] at ditm
  set Am := vsQL (vsQLam s g)ᵀ
  have hAm : VsWSq I.p (vsQD s) Am := by
    have := vsQL_sq (p := I.p) (vsQLam s g)ᵀ; exact ⟨this.2, this.1⟩
  -- the key without `0`
  have dtl := Det.call (Det.arg' (P := P) (rest := [vsWVs Am])
    (vs := [vsQTCtx s, encPerm g, natList (0 :: vsQTKey ys)]) (j := 2) rfl)
    (linTail_spec H.htl ((0 :: vsQTKey ys).map Val.nat))
  have etl : Val.list (List.drop 1 ((0 :: vsQTKey ys).map Val.nat)) = natList (vsQTKey ys) := rfl
  rw [etl] at dtl
  -- the pieces of the key
  set E2 := [A, vsWVs Am, natList (vsQTKey ys)]
  have dD := rc [vsWVs Am, natList (vsQTKey ys)] 2 _ rfl
  have dk := Det.arith (op := .add) (Det.arith (op := .mul) dD dD) (Det.nat 1)
  have dlen := Det.length (Det.var' (P := P) (env := E2) (i := 2) rfl)
  have dm := Det.arith (op := .div) dlen dk
  simp only [GI.Machine.BinOp.eval, List.length_map, vsQTKey_length] at dk dm
  rw [Nat.mul_div_cancel _ (by omega)] at dm
  have hkl : (vsQTKey ys).length = ys.length * (vsQD s * vsQD s + 1) := vsQTKey_length ys
  have hkb : ∀ y ∈ vsQTKey ys, y ≤ N := by
    intro y hy
    simp only [vsQTKey, List.mem_flatMap, vsQTKeyM, List.mem_cons] at hy
    obtain ⟨U, -, hy⟩ := hy
    rcases hy with rfl | hy
    · omega
    · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      have := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas U)
      exact (((this r hr).1 y hy).le.trans hpS).trans hS3
  have hkN : (vsQTKey ys).length ≤ N := by
    rw [hkl]
    have : ys.length * (vsQD s * vsQD s + 1) ≤ S * (S * S) := Nat.mul_le_mul hb (by
      have h1 : vsQD s + 1 ≤ S := by omega
      have h2 := Nat.mul_le_mul h1 h1
      have e : (vsQD s + 1) * (vsQD s + 1) = vsQD s * vsQD s + 2 * vsQD s + 1 := by ring
      omega)
    have e : S * (S * S) = S ^ 3 := by ring
    omega
  have wkey := wt_natList_le_sq hkb hkN
  have dchk := Det.call (Det.mk3 dk dm (Det.var' (P := P) (env := E2) (i := 2) rfl))
    (vsQChunk_spec H.hchk (k := vsQD s * vsQD s + 1) (m := ys.length) (N := N)
      (vs := (vsQTKey ys).map Val.nat) (W := 5 * (N + 1) ^ 2) (by rw [List.length_map, hkl, Nat.mul_comm])
      (by omega) (by omega) wkey)
  rw [vsQT_chunk_natList, vsQTKey_chunk, List.map_map] at dchk
  -- the images of the pieces
  set E3 := [A, vsWVs Am, natList (vsQTKey ys), Val.list (ys.map (natList ∘ vsQTKeyM))]
  have hlin : vsWLin I.p (vsQD s) Am = Matrix.toLin' (vsQLam s g) := by
    rw [vsWLin, vsWM, vsFMatrix_vsQL, transpose_transpose]
  have hitem : ∀ U ∈ ys, FunDet P fI (.list [.list [.nat I.p, .nat (vsQD s), vsWVs Am], natList (vsQTKeyM U)])
      (natList (vsQTKeyM (U.map (Matrix.toLin' (vsQLam s g))))) (10 ^ 11 * (N + 1) ^ 6) := by
    intro U _
    have := vsQTItem_spec H.hI I.prime (N := N) (hpS.trans hS3) hDD hAm (K := vsQTKeyU U)
      (vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas U)) (vsWKey_length _ _)
    rw [vsQTItemL_eq hAm U, hlin] at this
    exact this
  have hinj : Function.Injective fun U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p) => natList (vsQTKeyM U) :=
    fun U V he => vsQTKeyM_injective (vsQ_natList_injective he)
  have dmp := Det.call (Det.mk2 (Det.mk3 (rc [vsWVs Am, natList (vsQTKey ys), Val.list (ys.map (natList ∘ vsQTKeyM))] 1 _ rfl)
      (rc [vsWVs Am, natList (vsQTKey ys), Val.list (ys.map (natList ∘ vsQTKeyM))] 2 _ rfl)
      (Det.var' (P := P) (env := E3) (i := 1) rfl)) (Det.var' (P := P) (env := E3) (i := 3) rfl))
    (vsQ_map H.hmp ys (fun U => natList (vsQTKeyM U))
      (fun U => natList (vsQTKeyM (U.map (Matrix.toLin' (vsQLam s g))))) hinj hitem)
  -- joining
  set zs := vsQTAct s g ys
  set xss := zs.map fun V => (vsQTKeyM V).map Val.nat
  have e1 : Val.list (ys.map fun U => natList (vsQTKeyM (U.map (Matrix.toLin' (vsQLam s g))))) =
      Val.list (xss.map Val.list) := by
    simp only [xss, zs, vsQTAct, List.map_map]; rfl
  rw [e1] at dmp
  have e2 : Val.list xss.flatten = natList (vsQTKey zs) := by
    simp only [xss, natList, vsQTKey, List.flatMap, List.map_flatten, List.map_map]; rfl
  have hzl : zs.length = ys.length := List.length_map _
  have hzk := vsQTKey_length zs
  have hzb : ∀ y ∈ vsQTKey zs, y ≤ N := by
    intro y hy
    simp only [vsQTKey, List.mem_flatMap, vsQTKeyM, List.mem_cons] at hy
    obtain ⟨U, -, hy⟩ := hy
    rcases hy with rfl | hy
    · omega
    · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      have := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas U)
      exact (((this r hr).1 y hy).le.trans hpS).trans hS3
  have hzN : (vsQTKey zs).length ≤ N := by rw [hzk, hzl, ← hkl]; exact hkN
  have wz := wt_natList_le_sq hzb hzN
  have wxi : ∀ v ∈ xss.map Val.list, v.wt ≤ 5 * (N + 1) ^ 2 := by
    intro v hv
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hv
    obtain ⟨V, -, rfl⟩ := List.mem_map.mp hxs
    exact wt_natList_le_sq (B := N) (xs := vsQTKeyM V) (fun y hy => by
      simp only [vsQTKeyM, List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
        have := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas V)
        exact (((this r hr).1 y hy).le.trans hpS).trans hS3) (by rw [vsQTKeyM_len]; omega)
  have wxl := wt_list_le_of (xss.map Val.list) wxi
  have hxl : (xss.map Val.list).length ≤ N := by simp [xss, hzl]; omega
  have q24 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q13 : (N + 1) * (N + 1) ^ 2 = (N + 1) ^ 3 := by ring
  have dcat := Det.call dmp (vsWConcat_spec H.hcat (N := N) xss (by simp [xss, hzl]; omega)
    (fun xs hxs => by
      obtain ⟨V, -, rfl⟩ := List.mem_map.mp hxs
      rw [List.length_map, vsQTKeyM_len]; omega)
    (by rw [e2]; omega)
    (by
      have := Nat.one_le_pow 2 (N + 1) (by omega)
      have : (xss.map Val.list).length * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
      have := Nat.one_le_pow 3 (N + 1) (by omega)
      omega))
  rw [e2] at dcat
  have hN2 : (N + 1 + 1) ^ 2 ≤ 4 * (N + 1) ^ 2 := by
    have h1 : (N + 1 + 1) ^ 2 ≤ (2 * (N + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (2 * (N + 1)) ^ 2 = 4 * (N + 1) ^ 2 := by ring
    omega
  have wo : (natList (0 :: vsQTKey zs)).wt ≤ 20 * (N + 1) ^ 2 := by
    have := wt_natList_le_sq (B := N + 1) (xs := 0 :: vsQTKey zs) (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact (hzb y hy).trans (by omega)) (by simp; omega)
    omega
  have kap : FunDet P appd (.list [.list [.nat 0], natList (vsQTKey zs)]) (natList (0 :: vsQTKey zs))
      (10 ^ 6 * (N + 1) ^ 3) := by
    refine (append_spec H.happd [.nat 0] ((vsQTKey zs).map Val.nat)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have w2 := wt_list2_le (.list [.nat 0]) (natList (vsQTKey zs))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have e2' : (Val.list ([Val.nat 0] ++ (vsQTKey zs).map Val.nat)).wt = (natList (0 :: vsQTKey zs)).wt := rfl
    have e3 : (Val.list [Val.list [Val.nat 0], Val.list ((vsQTKey zs).map Val.nat)]).wt =
      (Val.list [.list [.nat 0], natList (vsQTKey zs)]).wt := rfl
    have hll : ((vsQTKey zs).map Val.nat).length ≤ N := by rw [List.length_map]; exact hzN
    have h4 : (((vsQTKey zs).map Val.nat).length + 1) *
        ((Val.list [Val.list [Val.nat 0], Val.list ((vsQTKey zs).map Val.nat)]).wt +
          ((vsQTKey zs).map Val.nat).length + (Val.list ([Val.nat 0] ++ (vsQTKey zs).map Val.nat)).wt + 1) ≤
        (N + 1) * (100 * (N + 1) ^ 2) := Nat.mul_le_mul (by omega) (by
          have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
          omega)
    have e : (N + 1) * (100 * (N + 1) ^ 2) = 100 * (N + 1) ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (((vsQTKey zs).map Val.nat).length + 1) * _ = 1000 * ((((vsQTKey zs).map Val.nat).length + 1) *
          ((Val.list [Val.list [Val.nat 0], Val.list ((vsQTKey zs).map Val.nat)]).wt +
          ((vsQTKey zs).map Val.nat).length + (Val.list ([Val.nat 0] ++ (vsQTKey zs).map Val.nat)).wt + 1)) := by
            ring
      _ ≤ _ := by omega
  have dap := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := E3) 0)) dcat) kap
  have dall := Det.letE ditm (Det.letE dtl (Det.letE dchk dap))
  refine FunDet.intro H.hf (dall.mono ?_)
  -- the cost
  have wfr := vsQ_wt_fr hS hs
  have wΓ := hS.g
  have wg := hS.wt_perm g
  have wk0 : (natList (0 :: vsQTKey ys)).wt ≤ 20 * (N + 1) ^ 2 := by
    have := wt_natList_le_sq (B := N + 1) (xs := 0 :: vsQTKey ys) (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact (hkb y hy).trans (by omega)) (by simp; omega)
    omega
  have wctx : (vsQTCtx s).wt ≤ 10 ^ 6 * S ^ 3 := by
    have w1 := wt_list2_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s))
    have w2 := wt_list3_le (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]) (.nat I.p) (.nat (vsQD s))
    have := wt_nat_le I.p; have := wt_nat_le (vsQD s)
    have : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
    show (Val.list _).wt ≤ _
    omega
  have wA : A.wt ≤ 10 ^ 7 * S ^ 3 + 100 * (N + 1) ^ 2 := by
    have := wt_list3_le (vsQTCtx s) (encPerm g) (natList (0 :: vsQTKey ys))
    have : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
    show (Val.list _).wt ≤ _
    omega
  have wAm := wt_vsWVs_le (VsWFit.bnd hAm.1 (hpS.trans hS3) (by omega : vsQD s ≤ N)) (by rw [hAm.2]; omega)
  have wkey' := wkey
  have wch : (Val.list (ys.map (natList ∘ vsQTKeyM))).wt ≤ 1000 * (N + 1) ^ 3 := by
    have := wt_list_le_of (ys.map (natList ∘ vsQTKeyM)) (c := 5 * (N + 1) ^ 2) (by
      intro v hv
      obtain ⟨V, -, rfl⟩ := List.mem_map.mp hv
      exact wt_natList_le_sq (B := N) (xs := vsQTKeyM V) (fun y hy => by
        simp only [vsQTKeyM, List.mem_cons] at hy
        rcases hy with rfl | hy
        · omega
        · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
          have := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas V)
          exact (((this r hr).1 y hy).le.trans hpS).trans hS3) (by rw [vsQTKeyM_len]; omega))
    have := Nat.one_le_pow 2 (N + 1) (by omega)
    have h2 : (ys.map (natList ∘ vsQTKeyM)).length * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by simp; omega) (by omega)
    have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    have := Nat.one_le_pow 3 (N + 1) (by omega)
    omega
  have wout : (Val.list (xss.map Val.list)).wt ≤ 1000 * (N + 1) ^ 3 := by
    have := Nat.one_le_pow 2 (N + 1) (by omega)
    have h2 : (xss.map Val.list).length * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    have := Nat.one_le_pow 3 (N + 1) (by omega)
    omega
  have wc3 := wt_list3_le (.nat I.p) (.nat (vsQD s)) (vsWVs Am)
  have wcm := wt_list2_le (.list [.nat I.p, .nat (vsQD s), vsWVs Am]) (.list (ys.map (natList ∘ vsQTKeyM)))
  have := wt_nat_le I.p; have := wt_nat_le (vsQD s); have := wt_nat_le 0; have := wt_nat_le 1
  have := wt_nat_le 2
  have q16 : 1 ≤ (N + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have q36 : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q26 : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q67 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have tW : (Val.list [.list [.nat I.p, .nat (vsQD s), vsWVs Am], .list (ys.map (natList ∘ vsQTKeyM))]).wt ≤
      10 ^ 5 * (N + 1) ^ 3 := by
    have : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have wch' := wch
    omega
  have k1 := vsW_mapCost (N := N) (n := ys.length) (B := 10 ^ 11 * (N + 1) ^ 6) (c := 10 ^ 11) (k := 6)
    (W := (Val.list [.list [.nat I.p, .nat (vsQD s), vsWVs Am], .list (ys.map fun U => natList (vsQTKeyM U))]).wt +
      (Val.list (xss.map Val.list)).wt)
    (by omega) le_rfl (by
      have ew : (Val.list (ys.map fun U => natList (vsQTKeyM (U.map (Matrix.toLin' (vsQLam s g)))))).wt =
        (Val.list (xss.map Val.list)).wt := by rw [e1]
      have ew2 : (Val.list [.list [.nat I.p, .nat (vsQD s), vsWVs Am], .list (ys.map fun U => natList (vsQTKeyM U))]).wt
        = (Val.list [.list [.nat I.p, .nat (vsQD s), vsWVs Am], .list (ys.map (natList ∘ vsQTKeyM))]).wt := rfl
      omega)
  have e7 : (N + 1) ^ (6 + 1) = (N + 1) ^ 7 := rfl
  rw [e7] at k1
  have ew : (Val.list (ys.map fun U => natList (vsQTKeyM (U.map (Matrix.toLin' (vsQLam s g)))))).wt =
    (Val.list (xss.map Val.list)).wt := by rw [e1]
  have ew2 : (Val.list [.list [.nat I.p, .nat (vsQD s), vsWVs Am], .list (ys.map fun U => natList (vsQTKeyM U))]).wt
    = (Val.list [.list [.nat I.p, .nat (vsQD s), vsWVs Am], .list (ys.map (natList ∘ vsQTKeyM))]).wt := rfl
  have wtl : linTailCost (Val.list ((0 :: vsQTKey ys).map Val.nat)).wt ≤ 10 ^ 4 * (21 * (N + 1) ^ 2) ^ 3 := by
    unfold linTailCost
    have e : (Val.list ((0 :: vsQTKey ys).map Val.nat)).wt = (natList (0 :: vsQTKey ys)).wt := rfl
    rw [e]
    have h1 : (natList (0 :: vsQTKey ys)).wt + 1 ≤ 21 * (N + 1) ^ 2 := by
      have := Nat.one_le_pow 2 (N + 1) (by omega); omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
  have e21 : (21 * (N + 1) ^ 2) ^ 3 = 9261 * (N + 1) ^ 6 := by ring
  have ech : 10 ^ 8 * (N + 1) ^ 4 * (5 * (N + 1) ^ 2 + (N + 1) ^ 2) = 6 * 10 ^ 8 * (N + 1) ^ 6 := by ring
  have hS5 : S ^ 5 ≤ (N + 1) ^ 7 := by
    have : S ^ 5 ≤ S ^ 9 := Nat.pow_le_pow_right hS1 (by norm_num)
    have e : S ^ 9 = N ^ 3 := by simp only [N]; ring
    have : N ^ 3 ≤ (N + 1) ^ 7 := (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hS3' : S ^ 3 ≤ (N + 1) ^ 7 := by
    have : N ≤ (N + 1) ^ 7 := (Nat.le_succ N).trans (Nat.le_self_pow (by norm_num) _)
    simp only [N] at this; omega
  have ekv : (Val.list ((vsQTKey ys).map Val.nat)).wt = (natList (vsQTKey ys)).wt := rfl
  have w3c := wt_list3_le (.nat (vsQD s * vsQD s + 1)) (.nat ys.length) (natList (vsQTKey ys))
  have := wt_nat_le (vsQD s * vsQD s + 1); have := wt_nat_le ys.length
  have := wt_nat_le (vsQD s * vsQD s)
  have := wt_nat_le (ys.length * (vsQD s * vsQD s + 1))
  have w2a := wt_list2_le (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]) (encPerm g)
  have w2b := wt_list2_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s))
  have eA : A.wt = (Val.list [vsQTCtx s, encPerm g, natList (0 :: vsQTKey ys)]).wt := rfl
  have wch2 := wch
  have wtl2 := wtl
  clear_value A Am E2 E3 zs xss N
  have t1 : (natList (vsQTKey zs)).wt ≤ 5 * (N + 1) ^ 2 := by omega
  have t2 : (Val.list (List.map (natList ∘ vsQTKeyM) ys)).wt ≤ 1000 * (N + 1) ^ 3 := by omega
  have t3 : (Val.list [vsQTCtx s, encPerm g, natList (0 :: vsQTKey ys)]).wt ≤ 10 ^ 7 * S ^ 3 + 100 * (N + 1) ^ 2 := by
    omega
  have t4 : S ^ 3 ≤ (N + 1) ^ 7 := by omega
  have t5 : (N + 1) ^ 2 ≤ (N + 1) ^ 7 := by omega
  have t6 : (N + 1) * (N + 1) ^ 2 ≤ (N + 1) ^ 7 := by omega
  have t7 : (Val.list (List.map (fun U => natList (vsQTKeyM (Submodule.map (toLin' (vsQLam s g)) U))) ys)).wt ≤
    1000 * (N + 1) ^ 3 := by omega
  have t8 : linTailCost (Val.list (List.map Val.nat (0 :: vsQTKey ys))).wt ≤ 10 ^ 8 * (N + 1) ^ 7 := by omega
  have t9 : (vsWVs Am).wt ≤ 20 * (N + 1) ^ 7 := by omega
  have t10 : (Val.list [Val.list [Val.nat 0], natList (vsQTKey zs)]).wt ≤ 100 * (N + 1) ^ 7 := by
    have := wt_list2_le (Val.list [Val.nat 0]) (natList (vsQTKey zs))
    have : (Val.list [Val.nat 0]).wt ≤ 10 := by decide
    omega
  have t11 : S ^ 5 ≤ (N + 1) ^ 7 := hS5
  have e7b : (N + 1) ^ (6 + 1) = (N + 1) ^ 7 := rfl
  have k1' := k1
  rw [e7b] at k1'
  have w0 : (Val.list [Val.nat 0]).wt ≤ 10 := by decide
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have u1 : (Val.list [Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)], encPerm g]).wt ≤ 10 ^ 9 * (N + 1) ^ 7 := by omega
  have u2 : (Val.nat (vsQD s * vsQD s)).wt ≤ (N + 1) ^ 7 := by omega
  have u3 : (Val.list [Val.nat (vsQD s * vsQD s + 1), Val.nat (List.length ys), natList (vsQTKey ys)]).wt ≤ 100 * (N + 1) ^ 7 := by omega
  have u4 : (Val.list [Val.nat I.p, Val.nat (vsQD s), vsWVs Am]).wt ≤ 100 * (N + 1) ^ 7 := by omega
  have u5 : (Val.list [Val.list [Val.nat I.p, Val.nat (vsQD s), vsWVs Am], Val.list (List.map (natList ∘ vsQTKeyM) ys)]).wt ≤ 10 ^ 4 * (N + 1) ^ 7 := by omega
  have u6 : List.length ys * (10 ^ 11 * (N + 1) ^ 6) + mapK * (List.length ys + 1) *
      ((Val.list [Val.list [Val.nat I.p, Val.nat (vsQD s), vsWVs Am],
        Val.list (List.map (fun U => natList (vsQTKeyM U)) ys)]).wt + (Val.list (List.map Val.list xss)).wt + 1)
      ≤ 1001 * 10 ^ 11 * (N + 1) ^ 7 := by omega
  have u7 : (natList (vsQTKey zs)).wt ≤ 5 * (N + 1) ^ 7 := by omega
  omega
