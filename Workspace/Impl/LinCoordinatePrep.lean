import Workspace.Impl.LinPermChain
import Workspace.Impl.LinPermPow
import Workspace.Impl.LinAssign

/-! Deterministic preparation of one cyclic relation, from permutation inputs. -/
namespace GI.Impl
open GI.Cited GI.Lang

structure linPrepIndices where
  order : ℕ
  pf : ℕ
  ratio : ℕ
  tail : ℕ
  take : ℕ
  append : ℕ
  power : ℕ
  comp : ℕ
  assign : ℕ
  rep : ℕ
  units : ℕ
  basis : ℕ
  encode : ℕ
  bits : ℕ

structure linPrepAt (P : Program) (I : linPrepIndices) (jo : ℕ) (ho : GroupOrder) : Prop where
  order : P.funs[I.order]? = some (linPrefixOrderF I.pf I.ratio)
  pf : P.funs[I.pf]? = some (linPrefixF I.tail I.take I.append)
  ratio : P.funs[I.ratio]? = some (linOrderRatioF jo)
  tail : P.HasAt I.tail (linTailFuns I.tail)
  take : P.HasAt I.take (linTakeFuns I.take)
  append : P.HasAt I.append (appendFuns I.append)
  power : P.funs[I.power]? = some (linPermPowF I.power I.comp)
  comp : P.HasAt I.comp (composeFuns I.comp)
  assign : P.funs[I.assign]? = some (linAssignF I.rep I.units)
  rep : P.HasAt I.rep (replicateFuns I.rep)
  units : P.HasAt I.units (linAssignUnitFuns I.units I.basis)
  basis : P.HasAt I.basis (linBasisFuns I.basis)
  encode : P.funs[I.encode]? = some (linIntEncodeF I.bits)
  bits : P.funs[I.bits]? = some (linBitsEncodeF I.bits)
  ordPrim : P.prims[jo]? = some (groupOrderPrim ho)

def linPrepCountE (j : ℕ) : Expr :=
  .arith .sub (.length (.get (arg j) (.nat 1))) (.nat 1)

def linCoordinatePrepF (I : linPrepIndices) : Expr :=
  [.call I.order (.var 0), .call I.pf (.var 0),
    .call I.power (mk3 (.get (.get (arg 1) (.nat 1)) (.arith .add (arg 2) (.nat 1)))
      (.var 1) (.get (.get (arg 1) (.nat 1)) (.nat 0))),
    .call I.assign (mk3 (linPrepCountE 1) (linPrepCountE 0) (arg 2)),
    .call I.encode (mk2 (.var 1) (.nat 0))].foldr Expr.letE
    (mk3 (mk2 (.var 2) (.var 3)) (.var 4) (.var 5))

noncomputable def linCoordinateMemberInst {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (i : Fin as.length) : MemberInst :=
  ⟨n, ns ++ as.take i.val, as[i.val] ^ linCyclicOrders (gens ns) as i⟩

noncomputable def linCoordinatePrepVal {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (i : Fin as.length) : Val :=
  .list [memberInput (linCoordinateMemberInst ns as i),
    .list [.list ((linPrefixVectors as.length ns.length i.val).map linVecVal), linVecVal (0 : Fin as.length → ℤ)],
    encInt (linCyclicOrders (gens ns) as i)]

def linCoordinatePrepWith {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (i : Fin as.length) (e : ℕ) : Val :=
  .list [.list [encGroup (ns ++ as.take i.val), encPerm (as[i.val] ^ e)],
    .list [.list ((linPrefixVectors as.length ns.length i.val).map linVecVal), linVecVal (0 : Fin as.length → ℤ)],
    encInt (e : ℤ)]

noncomputable def linCoordinatePrepCost (h : GroupOrder) (W n ns t i : ℕ) : ℕ :=
  let E := linPrefixOrderCost h W n
  10000 * (W + n + ns + t + (n + 1) ^ 2 + E + linPrefixCost W +
    linPermPowCost n E + linAssignCost (10 * (W + 1)) t ns i +
    linIntCodecCost (10 * (E + 1)) + 1)

theorem linPermPowCost_mono {L K : ℕ} (h : L ≤ K) (n : ℕ) :
    linPermPowCost n L ≤ linPermPowCost n K := by
  unfold linPermPowCost linPermPowUnit
  gcongr

theorem linAssignCost_mono {W V : ℕ} (h : W ≤ V) (t ns i : ℕ) :
    linAssignCost W t ns i ≤ linAssignCost V t ns i := by
  have hr0 : linAssignRepCost W t 100 ≤ linAssignRepCost V t 100 := by unfold linAssignRepCost; gcongr
  have hrn : linAssignRepCost W ns (linAssignZeroWt t) ≤ linAssignRepCost V ns (linAssignZeroWt t) := by
    unfold linAssignRepCost; gcongr
  have hu := linAssignUnitCost_mono
    (show linAssignUnitsArg W t ns ≤ linAssignUnitsArg V t ns by unfold linAssignUnitsArg; omega) t i
  unfold linAssignCost
  omega

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 4000 in
private theorem linCoordinatePrep_core (ho : GroupOrder) {P : Program} {f jo : ℕ} {I : linPrepIndices}
    (h : linPrepAt P I jo ho) (hf : P.funs[f]? = some (linCoordinatePrepF I))
    {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (i : Fin as.length) (e : ℕ)
    (he : FunDet P I.order (.list [encGroup ns, encGroup as, .nat i.val]) (.nat e)
      (linPrefixOrderCost ho (Val.list [encGroup ns, encGroup as, .nat i.val]).wt n)) :
    FunDet P f (.list [encGroup ns, encGroup as, .nat i.val]) (linCoordinatePrepWith ns as i e)
      (linCoordinatePrepCost ho (Val.list [encGroup ns, encGroup as, .nat i.val]).wt n ns.length as.length i.val) := by
  let ag : Equiv.Perm (Fin n) := as[i.val]
  have hp0 : FunDet P I.power (.list [encPerm ag, .nat e, encPerm (1 : Equiv.Perm (Fin n))])
      (encPerm (ag ^ e * 1)) (linPermPowCost n e.bits.length) :=
    linPermPow_spec (P := P) (f := I.power) (comp := I.comp) (n := n) h.power h.comp e (ag) (1 : Equiv.Perm (Fin n))
  let a := Val.list [encGroup ns, encGroup as, .nat i.val]
  let W := a.wt
  let g := encGroup (ns ++ as.take i.val)
  let x : Equiv.Perm (Fin n) := ag ^ e
  let av := Val.list [.list ((linPrefixVectors as.length ns.length i.val).map linVecVal), linVecVal (0 : Fin as.length → ℤ)]
  let E := linPrefixOrderCost ho W n
  let F := linPrefixCost W
  let Q := linPermPowCost n E
  let A := linAssignCost (10 * (W + 1)) as.length ns.length i.val
  let C := linIntCodecCost (10 * (E + 1))
  have wns : (encGroup ns).wt < W := wt_le_wt_list (by simp)
  have was : (encGroup as).wt < W := wt_le_wt_list (by simp)
  have wi : (Val.nat i.val).wt < W := wt_le_wt_list (by simp)
  have waInner : (Val.list ((1 :: as).map encPerm)).wt < W :=
    (wt_le_wt_list (by simp : Val.list ((1 :: as).map encPerm) ∈ [.nat n, .list ((1 :: as).map encPerm)])).trans was
  have wnInner : (Val.list ((1 :: ns).map encPerm)).wt < W :=
    (wt_le_wt_list (by simp : Val.list ((1 :: ns).map encPerm) ∈ [.nat n, .list ((1 :: ns).map encPerm)])).trans wns
  have hta : as.length < W := by
    have hh := (length_lt_wt_list ((1 :: as).map encPerm)).trans waInner
    simp only [List.length_map, List.length_cons] at hh
    omega
  have htn : ns.length < W := by
    have hh := (length_lt_wt_list ((1 :: ns).map encPerm)).trans wnInner
    simp only [List.length_map, List.length_cons] at hh
    omega
  have we : (Val.nat e).wt ≤ E := he.wt_lt.le
  have heb : e.bits.length ≤ E := by rw [wt_nat, linLenBits] at we; omega
  have hg := linPrefix_spec h.pf h.tail h.take h.append ns as i.val i.isLt.le
  have wg : g.wt ≤ F := hg.wt_lt.le
  have hpow := FunDet.mono hp0 (linPermPowCost_mono (L := e.bits.length) (K := E) heb n)
  simp only [mul_one] at hpow
  have wx := wt_encPerm_le (n := n) x
  have hid := wt_encPerm_le (n := n) (1 : Equiv.Perm (Fin n))
  have hgen := wt_encPerm_le (n := n) (ag)
  have countIn := wt_list3_le (.nat as.length) (.nat ns.length) (.nat i.val)
  have wta := wt_nat_le as.length
  have wtn := wt_nat_le ns.length
  have countBound : (Val.list [.nat as.length, .nat ns.length, .nat i.val]).wt ≤ 10 * (W + 1) := by omega
  have hass := (linAssign_spec h.assign h.rep h.units h.basis as.length ns.length i.val i.isLt.le).mono
    (linAssignCost_mono countBound as.length ns.length i.val)
  have wav : av.wt ≤ A := hass.wt_lt.le
  have parts : linIntParts (e : ℤ) = .list [.nat e, .nat 0] := by simp [linIntParts]
  have hpw := wt_list2_le (.nat e) (.nat 0)
  have w0 : (Val.nat 0).wt = 2 := rfl
  have partsBound : (linIntParts (e : ℤ)).wt ≤ 10 * (E + 1) := by rw [parts]; omega
  have henc := (linIntEncode_spec h.encode h.bits (e : ℤ)).mono (linIntCodecCost_mono partsBound)
  rw [parts] at henc
  have wenc : (encInt (e : ℤ)).wt ≤ C := henc.wt_lt.le
  have darg (j : ℕ) (rest : List Val) {v : Val} (hv : [encGroup ns, encGroup as, .nat i.val][j]? = some v) :=
    Det.arg' (P := P) (vs := [encGroup ns, encGroup as, .nat i.val]) (rest := rest) (j := j) hv
  have de := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) he
  have dg := Det.call (Det.var' (P := P) (env := [a, .nat e]) (i := 0) rfl) hg
  have das := Det.get' (darg 1 [.nat e, g] rfl) (Det.nat 1) rfl
  have didx := Det.arith (op := .add) (darg 2 [.nat e, g] rfl) (Det.nat 1)
  simp only [GI.Machine.BinOp.eval_add] at didx
  have dag := Det.get' das didx (show ((1 :: as).map encPerm)[i.val + 1]? = some (encPerm ag) by simp [ag])
  have dai := Det.get' das (Det.nat 0) rfl
  have dnat := Det.var' (P := P) (env := [a, .nat e, g]) (i := 1) rfl
  have dp := Det.call (Det.mk3 dag dnat dai) hpow
  have cta := Det.arith (op := .sub) (Det.length
    (Det.get' (darg 1 [.nat e, g, encPerm x] rfl) (Det.nat 1) rfl)) (Det.nat 1)
  have ctn := Det.arith (op := .sub) (Det.length
    (Det.get' (darg 0 [.nat e, g, encPerm x] rfl) (Det.nat 1) rfl)) (Det.nat 1)
  simp only [GI.Machine.BinOp.eval_sub, List.length_map, List.length_cons, Nat.add_sub_cancel] at cta ctn
  have da := Det.call (Det.mk3 cta ctn (darg 2 [.nat e, g, encPerm x] rfl)) hass
  have dc := Det.call (Det.mk2
    (Det.var' (P := P) (env := [a, .nat e, g, encPerm x, av]) (i := 1) rfl) (Det.nat 0)) henc
  have dv (j : ℕ) {v : Val} (hv : [a, .nat e, g, encPerm x, av, encInt (e : ℤ)][j]? = some v) :=
    Det.var' (P := P) (env := [a, .nat e, g, encPerm x, av, encInt (e : ℤ)]) (i := j) hv
  have dout := Det.mk3 (Det.mk2 (dv 2 rfl) (dv 3 rfl)) (dv 4 rfl) (dv 5 rfl)
  have wmb := wt_list2_le g (encPerm x)
  have wout := wt_list3_le (.list [g, encPerm x]) av (encInt (e : ℤ))
  have wpo := wt_list3_le (encPerm (n := n) ag) (.nat e) (encPerm (n := n) (1 : Equiv.Perm (Fin n)))
  have hiNat : i.val < as.length := i.isLt
  have wip := wt_nat_le (i.val + 1)
  have w1 : (Val.nat 1).wt = 3 := rfl
  have w0' : (Val.nat 0).wt = 2 := rfl
  have wcA := wt_nat_le (as.length + 1)
  have wcN := wt_nat_le (ns.length + 1)
  let B := W + n + ns.length + as.length + (n + 1) ^ 2 + E + F + Q + A + C + 1
  simp only [W, a, E, F, Q, A, C, g, x, av, ag] at wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
  have de' := de.mono (c' := 1000 * B) (by
      dsimp only [B, W, a, E, F, Q, A, C, g, x, av, ag]
      clear * - wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
      generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
      generalize linPrefixOrderCost ho Wp n = Op at *
      generalize linPrefixCost Wp = Fp at *
      generalize linPermPowCost n Op = Qp at *
      generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
      generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
      nlinarith only [wns, was, wi, waInner, wnInner, hta, htn, we, wg, wx, hid, hgen, countIn, wta, wtn, countBound, wav, hpw, w0, wenc, wmb, wout, wpo, wip, w1, wcA, wcN, hiNat])
  have dg' := dg.mono (c' := 1000 * B) (by
      dsimp only [B, W, a, E, F, Q, A, C, g, x, av, ag]
      clear * - wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
      generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
      generalize linPrefixOrderCost ho Wp n = Op at *
      generalize linPrefixCost Wp = Fp at *
      generalize linPermPowCost n Op = Qp at *
      generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
      generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
      nlinarith only [wns, was, wi, waInner, wnInner, hta, htn, we, wg, wx, hid, hgen, countIn, wta, wtn, countBound, wav, hpw, w0, wenc, wmb, wout, wpo, wip, w1, wcA, wcN, hiNat])
  have dp' := dp.mono (c' := 1000 * B) (by
      dsimp only [B, W, a, E, F, Q, A, C, g, x, av, ag]
      clear * - wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
      generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
      generalize linPrefixOrderCost ho Wp n = Op at *
      generalize linPrefixCost Wp = Fp at *
      generalize linPermPowCost n Op = Qp at *
      generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
      generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
      nlinarith only [wns, was, wi, waInner, wnInner, hta, htn, we, wg, wx, hid, hgen, countIn, wta, wtn, countBound, wav, hpw, w0, wenc, wmb, wout, wpo, wip, w1, wcA, wcN, hiNat])
  have da' := da.mono (c' := 1000 * B) (by
      dsimp only [B, W, a, E, F, Q, A, C, g, x, av, ag]
      clear * - wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
      generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
      generalize linPrefixOrderCost ho Wp n = Op at *
      generalize linPrefixCost Wp = Fp at *
      generalize linPermPowCost n Op = Qp at *
      generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
      generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
      nlinarith only [wns, was, wi, waInner, wnInner, hta, htn, we, wg, wx, hid, hgen, countIn, wta, wtn, countBound, wav, hpw, w0, wenc, wmb, wout, wpo, wip, w1, wcA, wcN, hiNat])
  have dc' := dc.mono (c' := 1000 * B) (by
      dsimp only [B, W, a, E, F, Q, A, C, g, x, av, ag]
      clear * - wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
      generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
      generalize linPrefixOrderCost ho Wp n = Op at *
      generalize linPrefixCost Wp = Fp at *
      generalize linPermPowCost n Op = Qp at *
      generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
      generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
      nlinarith only [wns, was, wi, waInner, wnInner, hta, htn, we, wg, wx, hid, hgen, countIn, wta, wtn, countBound, wav, hpw, w0, wenc, wmb, wout, wpo, wip, w1, wcA, wcN, hiNat])
  have dout' := dout.mono (c' := 1000 * B) (by
      dsimp only [B, W, a, E, F, Q, A, C, g, x, av, ag]
      clear * - wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
      generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
      generalize linPrefixOrderCost ho Wp n = Op at *
      generalize linPrefixCost Wp = Fp at *
      generalize linPermPowCost n Op = Qp at *
      generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
      generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
      nlinarith only [wns, was, wi, waInner, wnInner, hta, htn, we, wg, wx, hid, hgen, countIn, wta, wtn, countBound, wav, hpw, w0, wenc, wmb, wout, wpo, wip, w1, wcA, wcN, hiNat])
  have wo' : (Val.list [.list [g, encPerm x], av, encInt (e : ℤ)]).wt ≤ 100 * B := by
    dsimp only [B, W, a, E, F, Q, A, C, g, x, av, ag]
    clear * - wns was wi waInner wnInner hta htn we heb wg wx hid hgen countIn wta wtn countBound wav hpw w0 partsBound wenc wmb wout wpo wip w1 w0' wcA wcN hiNat
    generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
    generalize linPrefixOrderCost ho Wp n = Op at *
    generalize linPrefixCost Wp = Fp at *
    generalize linPermPowCost n Op = Qp at *
    generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
    generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
    nlinarith only [wns, was, wi, waInner, wnInner, hta, htn, we, wg, wx, hid, hgen, countIn, wta, wtn, countBound, wav, hpw, w0, wenc, wmb, wout, wpo, wip, w1, wcA, wcN, hiNat]
  simp only [B, W, a, E, F, Q, A, C, g, x, av, ag] at wo'
  apply FunDet.intro hf
  refine (Det.letE de' (Det.letE dg' (Det.letE dp' (Det.letE da' (Det.letE dc' dout'))))).mono ?_
  change _ ≤ linCoordinatePrepCost ho W n ns.length as.length i.val
  unfold linCoordinatePrepCost
  dsimp only [W, a, E, F, Q, A, C, g, x, av, ag, B, linCoordinatePrepWith]
  clear * - wo'
  generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
  generalize linPrefixOrderCost ho Wp n = Op at *
  generalize linPrefixCost Wp = Fp at *
  generalize linPermPowCost n Op = Qp at *
  generalize linAssignCost (10 * (Wp + 1)) as.length ns.length i.val = Ap at *
  generalize linIntCodecCost (10 * (Op + 1)) = Cp at *
  nlinarith only [wo']

/-- Preparation computes the actual cyclic index and powered permutation. -/
theorem linCoordinatePrep_spec (ho : GroupOrder) {P : Program} {f jo : ℕ} {I : linPrepIndices}
    (h : linPrepAt P I jo ho) (hf : P.funs[f]? = some (linCoordinatePrepF I))
    {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (i : Fin as.length) :
    FunDet P f (.list [encGroup ns, encGroup as, .nat i.val]) (linCoordinatePrepVal ns as i)
      (linCoordinatePrepCost ho (Val.list [encGroup ns, encGroup as, .nat i.val]).wt n ns.length as.length i.val) := by
  exact linCoordinatePrep_core ho h hf ns as i (linCyclicOrders (gens ns) as i)
    (linPrefixOrder_spec ho h.order h.pf h.tail h.take h.append h.ratio h.ordPrim ns as i.val i.isLt)

end GI.Impl
