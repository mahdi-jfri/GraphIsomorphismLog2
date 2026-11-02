import Workspace.Impl.VsPFin
import Workspace.Impl.VsQAnaBase
import Workspace.Impl.VsWProgBas
import Workspace.Impl.VsWProgImg

/-!
# The input and the context

The input of step 4 is `vsPIn s as Lb ccs tcs = [vsQLCV s, ⟨as⟩, Lb, ⟨ccs⟩, tcs]`. The context
program (`vsPCtxP_spec`) builds `vsPCtx I s.ws' (vsQCs s) rows s.hs` with
`rows = vsWRows p (Lb.map flatten)`: it flattens the matrices of `Lb`, computes the echelon rows,
and the zero vector of length `D²`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- The input of step 4. -/
noncomputable def vsPIn (s : VsQSt I) (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ)))
    (ccs tcs : List (Perm (Fin I.n))) : Val :=
  .list [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs, .list (tcs.map encPerm)]

/-- The rows of `Lb`. -/
def vsPRows (p : ℕ) (Lb : List (List (List ℕ))) : List VsRow := vsWRows p (Lb.map List.flatten)

/-- A list of seven values. -/
def vsPMk7 (a b c d e f g : Expr) : Expr := .snoc (.snoc (.snoc (mk4 a b c d) e) f) g

theorem Det.vsPMk7 {P : Program} {env : List Val} {a b c d e f g : Expr}
    {va vb vc vd ve vf vg : Val} {ca cb cc cd ce cf cg : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) (hc : Det P env c vc cc) (hd : Det P env d vd cd)
    (he : Det P env e ve ce) (hf : Det P env f vf cf) (hg : Det P env g vg cg) :
    Det P env (vsPMk7 a b c d e f g) (.list [va, vb, vc, vd, ve, vf, vg])
      (ca + cb + cc + cd + ce + cf + cg + 7 * (Val.list [va, vb, vc, vd, ve, vf, vg]).wt + 20) := by
  have h1 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, ve, vf, vg] from ⟨[ve, vf, vg], rfl⟩)
  have h2 := wt_list_mono (show [va, vb, vc, vd, ve] <+: [va, vb, vc, vd, ve, vf, vg] from ⟨[vf, vg], rfl⟩)
  have h3 := wt_list_mono (show [va, vb, vc, vd, ve, vf] <+: [va, vb, vc, vd, ve, vf, vg] from ⟨[vg], rfl⟩)
  exact (Det.snoc (Det.snoc (Det.snoc (Det.mk4 ha hb hc hd) he) hf) hg).mono
    (by simp only [List.cons_append, List.nil_append]; omega)

/-- The item of the flattening map, on `[c, M]`. -/
def vsPFlItemE (fl : ℕ) : Expr := .call fl (arg 1)

/-- On the input: the context. -/
def vsPCtxE (flm rws rep : ℕ) : Expr :=
  .letE (.call flm (mk2 (.nat 0) (arg 2)))
    (.letE (.call rws (mk2 (.get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 0)) (.var 1)))
      (.letE (.call rep (mk2 (.arith .mul (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 2))) (.nat 0)))
        (vsPMk7 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (arg 0) (.nat 1))
          (.get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 0)) (.var 2) (.var 3)
          (.get (.get (arg 0) (.nat 0)) (.nat 1))
          (.get (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0)) (.nat 0)))))

theorem vsP_flatten_fit {p D : ℕ} {M : List (List ℕ)} (hM : VsWSq p D M) :
    (∀ y ∈ M.flatten, y < p) ∧ M.flatten.length = D * D := by
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨a, ha, hy⟩ := List.mem_flatten.1 hy
    exact (hM.1 a ha).1 y hy
  · rw [List.length_flatten]
    have : M.map List.length = M.map (fun _ => D) := List.map_congr_left fun a ha => (hM.1 a ha).2
    rw [this, List.map_const', List.sum_replicate, hM.2, smul_eq_mul]

/-- The cost of the context program. -/
def vsPCtxPCost (N W : ℕ) : ℕ :=
  (N + 1) * (2 * 10 ^ 6 * (N + 1) ^ 4) + 4 * 10 ^ 7 * (N + 1) ^ 5 + 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3)

set_option maxHeartbeats 4000000 in
/-- **The context program.** -/
theorem vsPCtxP_spec {P : Program} {f flm it fl rws rep : ℕ} (hf : P.funs[f]? = some (vsPCtxE flm rws rep))
    (hflm : P.HasAt flm (mapFuns flm it)) (hit : P.funs[it]? = some (vsPFlItemE fl))
    (hfl : P.HasAt fl (vsWFlatFuns fl)) (hrws : P.HasAt rws (vsWRowsFuns rws))
    (hrep : P.HasAt rep (replicateFuns rep))
    {s : VsQSt I} (hs : VsQStOK s) {N W : ℕ} (hpN : I.p ≤ N) (hDD : vsQD s * vsQD s ≤ N)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs : List (Perm (Fin I.n))}
    (hLb : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (hLbl : Lb.length ≤ N)
    (hW : (vsPIn s as Lb ccs tcs).wt ≤ W) :
    FunDet P f (vsPIn s as Lb ccs tcs) (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs)
      (vsPCtxPCost N W) := by
  have hp0 := I.prime.pos
  set D := vsQD s
  set fr := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set st := vsQStV I s
  set vs := [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs, Val.list (tcs.map encPerm)]
  have eA : vsPIn s as Lb ccs tcs = .list vs := rfl
  rw [eA] at hW ⊢
  have a0 : Det P [Val.list vs] (arg 0) (.list [st, fr, .nat D, vsFMatsVal (vsQMs s)]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a2 : Det P [Val.list vs] (arg 2) (.list (Lb.map vsWVs)) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  -- flattening
  have hDN : D ≤ N := (Nat.le_mul_self D).trans hDD
  have hitem : ∀ M ∈ Lb, FunDet P it (.list [.nat 0, vsWVs M]) (natList M.flatten)
      (2 * 10 ^ 6 * (N + 1) ^ 4) := by
    intro M hM
    have d1 := Det.arg' (P := P) (vs := [Val.nat 0, vsWVs M]) (rest := []) (j := 1) rfl
    have dc := Det.call d1 (vsWFlat_spec hfl hpN hDD (hLb M hM))
    refine FunDet.intro hit (dc.mono ?_)
    have wM : (vsWVs M).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
      wt_vsWVs_le (fun u hu => ⟨fun y hy => ((hLb M hM).1 u hu).1 y hy |>.le.trans hpN,
        by rw [((hLb M hM).1 u hu).2]; exact hDN⟩) (by rw [(hLb M hM).2]; omega)
    have hfit := vsP_flatten_fit (hLb M hM)
    have wF := wt_natList_le_sq (B := N) (xs := M.flatten) (fun y hy => (hfit.1 y hy).le.trans hpN)
      (by rw [hfit.2]; exact hDD)
    have w2 := wt_list2_le (Val.nat 0) (vsWVs M)
    have := wt_nat_le 0
    have q1 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q2 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hmap := vsQ_map hflm (c := .nat 0) Lb vsWVs (fun M => natList M.flatten) vsWVs_injective hitem
  have eF : Val.list (Lb.map fun M => natList M.flatten) = vsWVs (Lb.map List.flatten) := by
    rw [vsWVs, List.map_map]; rfl
  rw [eF] at hmap
  have dF := Det.call (Det.mk2 (Det.nat (P := P) (env := [Val.list vs]) 0) a2) hmap
  -- rows
  set us := Lb.map List.flatten
  have hus : VsWFit I.p (D * D) us := by
    intro u hu
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hu
    exact vsP_flatten_fit (hLb M hM)
  have hul : us.length ≤ N := by rw [List.length_map]; exact hLbl
  set E1 := [Val.list vs, vsWVs us]
  have b0 : Det P E1 (arg 0) (.list [st, fr, .nat D, vsFMatsVal (vsQMs s)]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [vsWVs us]) (j := 0) rfl
  have bfr : Det P E1 (.get (arg 0) (.nat 1)) fr _ := Det.get' b0 (Det.nat 1) rfl
  have bf0 : Det P E1 (.get (.get (arg 0) (.nat 1)) (.nat 0))
      (.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]) _ :=
    Det.get' bfr (Det.nat 0) rfl
  have bp : Det P E1 (.get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 0)) (.nat I.p) _ :=
    Det.get' bf0 (Det.nat 0) rfl
  have dR := Det.call (Det.mk2 bp (Det.var' (P := P) (env := E1) (i := 1) rfl))
    (vsWRows_spec hrws hp0 hpN hDD hus hul)
  -- zeros
  set E2 := [Val.list vs, vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val)]
  have c0 : Det P E2 (arg 0) (.list [st, fr, .nat D, vsFMatsVal (vsQMs s)]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val)])
      (j := 0) rfl
  have cD : Det P E2 (.get (arg 0) (.nat 2)) (.nat D) _ := Det.get' c0 (Det.nat 2) rfl
  have cDD := Det.arith' (op := .mul) cD cD rfl
  have dZ := vsWZero_det hrep cDD (N := N) (by simp only [BinOp.eval]; exact hDD)
  -- the context
  set E3 := [Val.list vs, vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val),
    natList (vsWZ (BinOp.eval .mul D D))]
  have e0 : Det P E3 (arg 0) (.list [st, fr, .nat D, vsFMatsVal (vsQMs s)]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val),
      natList (vsWZ (BinOp.eval .mul D D))]) (j := 0) rfl
  have est : Det P E3 (.get (arg 0) (.nat 0))
      (.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]) _ :=
    Det.get' e0 (Det.nat 0) rfl
  have eG : Det P E3 (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.list [encGroup I.gs, vsQTable I, vsQE I.p I.d (vsQExp I) 1]) _ := Det.get' est (Det.nat 0) rfl
  have eH : Det P E3 (.get (.get (arg 0) (.nat 0)) (.nat 1)) (encGroup s.hs) _ :=
    Det.get' est (Det.nat 1) rfl
  have eFr : Det P E3 (.get (arg 0) (.nat 1)) fr _ := Det.get' e0 (Det.nat 1) rfl
  have eF0 : Det P E3 (.get (.get (arg 0) (.nat 1)) (.nat 0))
      (.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]) _ :=
    Det.get' eFr (Det.nat 0) rfl
  have eP : Det P E3 (.get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 0)) (.nat I.p) _ :=
    Det.get' eF0 (Det.nat 0) rfl
  have eGs : Det P E3 (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0))
      (.list [.nat I.n, .list ((1 :: I.gs).map encPerm)]) _ := Det.get' eG (Det.nat 0) rfl
  have eN : Det P E3 (.get (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0)) (.nat 0))
      (.nat I.n) _ := Det.get' eGs (Det.nat 0) rfl
  have eG' : Det P E3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (vsQGam I) _ := eG
  have dC := Det.vsPMk7 eG' eFr eP (Det.var' (P := P) (env := E3) (i := 2) rfl)
    (Det.var' (P := P) (env := E3) (i := 3) rfl) eH eN
  have eC : Val.list [vsQGam I, fr, .nat I.p, Val.list ((vsWRows I.p us).map VsRow.val),
      natList (vsWZ (BinOp.eval .mul D D)), encGroup s.hs, .nat I.n] =
      vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs := rfl
  rw [eC] at dC
  have dAll := Det.letE dF (Det.letE dR (Det.letE dZ dC))
  refine FunDet.intro hf (dAll.mono ?_)
  -- weights of the parts of the input
  set LC4 := Val.list [st, fr, .nat D, vsFMatsVal (vsQMs s)]
  set Gm := Val.list [encGroup I.gs, vsQTable I, vsQE I.p I.d (vsQExp I) 1]
  set St := Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]
  set F4 := Val.list [Val.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]
  set G2 := Val.list [Val.nat I.n, Val.list ((1 :: I.gs).map encPerm)]
  have w1 : LC4.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_cons_self (a := LC4) (l := vs.tail))
  have w2 : (Val.list (Lb.map vsWVs)).wt < (Val.list vs).wt := wt_le_wt_list (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self (a := Val.list (Lb.map vsWVs)) (l := vs.tail.tail.tail))))
  have w3 : St.wt < LC4.wt := wt_le_wt_list (by simp [St, st, vsQStV])
  have w4 : fr.wt < LC4.wt := wt_le_wt_list (by simp)
  have w5 : Gm.wt < St.wt := wt_le_wt_list (by simp [St, Gm, vsQGam])
  have w6 : (encGroup s.hs).wt < St.wt := wt_le_wt_list (by simp [St])
  have w7 : F4.wt < fr.wt := wt_le_wt_list (by simp [fr, F4, vsWFrVal])
  have w8 : G2.wt < Gm.wt := wt_le_wt_list (by simp [Gm, G2, encGroup, encPerms])
  have w9 : (Val.nat I.p).wt < F4.wt := wt_le_wt_list (by simp [F4])
  have w10 : (Val.nat I.n).wt < G2.wt := wt_le_wt_list (by simp [G2])
  have w11 : (Val.nat D).wt < LC4.wt := wt_le_wt_list (by simp)
  have eSt : st.wt = St.wt := rfl
  have eGm : (vsQGam I).wt = Gm.wt := rfl
  have eG2 : (encGroup I.gs).wt = G2.wt := rfl
  -- weights of the computed parts
  have hRf := vsWRows_fits hp0 hpN hDD hus
  have wR : (Val.list ((vsWRows I.p us).map VsRow.val)).wt ≤ 81 * (N + 1) ^ 3 + 4 :=
    wt_vsRows_le hRf.rows (by
      have := hRf.nrows
      have e : (vsWRows I.p us).length = (vsInsertAll I.p (vsWPairs us)).1.length := rfl
      omega)
  have hUB : VsWBnd N us := fun u hu => ⟨fun y hy => ((hus u hu).1 y hy).le.trans hpN,
    by rw [(hus u hu).2]; exact hDD⟩
  have wU : (vsWVs us).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsWVs_le hUB (by omega)
  have wZ : (natList (vsWZ (BinOp.eval .mul D D))).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ, BinOp.eval]; omega)
  have hDDv : BinOp.eval .mul D D ≤ N := by simp only [BinOp.eval]; exact hDD
  have w7l := wt_list_le [vsQGam I, fr, .nat I.p, Val.list ((vsWRows I.p us).map VsRow.val),
      natList (vsWZ (BinOp.eval .mul D D)), encGroup s.hs, .nat I.n]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w7l
  have eCtx : (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs).wt =
      (Val.list [vsQGam I, fr, .nat I.p, Val.list ((vsWRows I.p us).map VsRow.val),
        natList (vsWZ (BinOp.eval .mul D D)), encGroup s.hs, .nat I.n]).wt := rfl
  have w0l := wt_list2_le (Val.nat 0) (Val.list (Lb.map vsWVs))
  have wpu := wt_list2_le (Val.nat I.p) (vsWVs us)
  have wDD := wt_nat_le (BinOp.eval .mul D D)
  have wz0 := wt_nat_le 0
  have hLbM : Lb.length * (2 * 10 ^ 6 * (N + 1) ^ 4) ≤ (N + 1) * (2 * 10 ^ 6 * (N + 1) ^ 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  set Y := (N + 1) * (W + 100 * (N + 1) ^ 3)
  have hY1 : W + 100 * (N + 1) ^ 3 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hM : mapK * (Lb.length + 1) * ((Val.list [Val.nat 0, Val.list (Lb.map vsWVs)]).wt +
      (vsWVs us).wt + 1) ≤ 1000 * (2 * Y) := by
    have hA : (Val.list [Val.nat 0, Val.list (Lb.map vsWVs)]).wt + (vsWVs us).wt + 1 ≤
        2 * (W + 100 * (N + 1) ^ 3) := by omega
    have e1 : (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) = 2 * Y := by simp only [Y]; ring
    calc mapK * (Lb.length + 1) * ((Val.list [Val.nat 0, Val.list (Lb.map vsWVs)]).wt +
          (vsWVs us).wt + 1) ≤ mapK * (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hA
      _ = 1000 * (2 * Y) := by rw [mul_assoc, e1]; rfl
  have eY : 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) = 10 ^ 4 * Y := by rw [mul_assoc]
  unfold vsPCtxPCost
  rw [eY]
  omega

/-- The size of step 4: `N = 4 S²`. -/
def vsPN (S : ℕ) : ℕ := 4 * S ^ 2

theorem vsP_pow_N {S : ℕ} (hS : 1 ≤ S) (k : ℕ) : (vsPN S + 1) ^ k ≤ 5 ^ k * S ^ (2 * k) := by
  have : vsPN S + 1 ≤ 5 * S ^ 2 := by unfold vsPN; have := Nat.one_le_pow 2 S hS; omega
  calc (vsPN S + 1) ^ k ≤ (5 * S ^ 2) ^ k := Nat.pow_le_pow_left this k
    _ = 5 ^ k * S ^ (2 * k) := by rw [mul_pow, ← pow_mul]

set_option maxHeartbeats 2000000 in
/-- **The context is valid** at `N = 4 S²` and weight `10^8 S^6`. -/
theorem vsPCtx_ok {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (hLbl : Lb.length ≤ vsPN S) :
    VsPCtxOK I (vsPN S) (10 ^ 8 * S ^ 6) s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs := by
  have hS1 := hS.one_le
  have hSn := hS.n; have hSd := hS.d; have hSp := hS.p
  have hD := vsQD_le hs
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hN : 4 * S ≤ vsPN S := by unfold vsPN; omega
  have hDD : vsQD s * vsQD s ≤ vsPN S := by
    have : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
    unfold vsPN; nlinarith
  have hfr := vsQ_frOK hS hs
  have hsz : VsQSz I.p I.d (vsQExp I) (vsPN S) := by
    refine ⟨by omega, by omega, ?_, I.prime.pos⟩
    have h1 := hS.g
    have h2 : (Val.nat (vsQExp I)).wt < (vsQE I.p I.d (vsQExp I) 1).wt :=
      wt_le_wt_list (show Val.nat (vsQExp I) ∈ [Val.nat I.p, natList (List.replicate I.d 0),
        .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)]
        by simp)
    have h3 : (vsQE I.p I.d (vsQExp I) 1).wt < (vsQGam I).wt :=
      wt_le_wt_list (show vsQE I.p I.d (vsQExp I) 1 ∈ [encGroup I.gs, vsQTable I,
        vsQE I.p I.d (vsQExp I) 1] by simp)
    omega
  set us := Lb.map List.flatten
  have hus : VsWFit I.p (vsQD s * vsQD s) us := by
    intro u hu
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hu
    exact vsP_flatten_fit (hLb M hM)
  have hRf := vsWRows_fits I.prime.pos (show I.p ≤ vsPN S by omega) hDD hus
  have hRl : (vsPRows I.p Lb).length ≤ vsPN S := by
    have := hRf.nrows
    have e : (vsPRows I.p Lb).length = (vsInsertAll I.p (vsWPairs us)).1.length := rfl
    rw [List.length_map] at this; omega
  refine ⟨hsz, hS.g.trans (by omega), by omega,
    ⟨hfr.hp, by omega, by omega, hfr.h', hfr.hc, by have := hfr.hl; omega⟩, hDD, hRf.rows, hRl, ?_⟩
  -- the weight
  have wR : (Val.list ((vsPRows I.p Lb).map VsRow.val)).wt ≤ 81 * (vsPN S + 1) ^ 3 + 4 :=
    wt_vsRows_le hRf.rows (by omega)
  have wZ : (natList (vsWZ ((vsQCs s).length * (vsQCs s).length))).wt ≤ 5 * (vsPN S + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; exact hDD)
  have wF := vsQ_wt_fr hS hs
  have wH := hS.wt_group hs.hsl
  have wG := hS.g
  have wp := wt_nat_le I.p
  have wn := wt_nat_le I.n
  have w7 := wt_list_le [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      Val.list ((vsPRows I.p Lb).map VsRow.val), natList (vsWZ ((vsQCs s).length * (vsQCs s).length)),
      encGroup s.hs, .nat I.n]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w7
  have e : (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs).wt =
    (Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      Val.list ((vsPRows I.p Lb).map VsRow.val), natList (vsWZ ((vsQCs s).length * (vsQCs s).length)),
      encGroup s.hs, .nat I.n]).wt := rfl
  have p3 := vsP_pow_N hS1 3
  have p2 := vsP_pow_N hS1 2
  have s3 : S ^ 3 ≤ S ^ 6 := hS.pow_le (by omega)
  have s4 : S ^ 4 ≤ S ^ 6 := hS.pow_le (by omega)
  have s1 : S ≤ S ^ 6 := by have := hS.pow_le (show 1 ≤ 6 by omega); simpa using this
  norm_num at p3 p2
  omega

end GI.Impl
