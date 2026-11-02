import Workspace.Impl.TermJHProg
import Workspace.Impl.LinPermPow
import Workspace.Impl.TermJProgTl

/-!
# The transporter of one label: the correction programs

* `tmJHPowF`, on `[encPerm g, encInt c, encPerm 1]`: the permutation `(g^c)⁻¹` of `Fin m`, by
  binary powering of `g` or `g⁻¹` (`tmJH_pow_spec`). The exponent is read off the bits of
  `|c|` (`linBitsDecodeF`), and the power is `linPermPowF`.
* `tmJHLamF`, on `[lgV, cv, lc]` with `lgV = tmJLgVal lg` and `cv = linVecVal c`: the local
  product `tmJLam lg c` on `Fin (m q)` (`tmJH_lam_spec`). A fold multiplies, for `k = 0, 1, …`,
  the local element `(g_k^{c_k} at a_k; 1)` on the left (`tmJHLamDi_succ`).
* `tmJHCorrF`, on `[tmJTlVal Tl, lc, k, encPerm λ]`: the first lifted transposition of `Tl` if
  `k ≠ 0`, times `λ` (`tmJH_corr_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens encInt)

variable {m q : ℕ}

/-! ### Integer powers -/

/-- On `[encPerm g, encInt c, encPerm 1]`: `(g^c)⁻¹`, that is `g^|c|` if `c < 0` and
`(g⁻¹)^|c|` otherwise. -/
def tmJHPowF (dc pp iv : ℕ) : Expr :=
  .letE (.call dc (mk2 (.get (arg 1) (.nat 1)) (.nat 0)))
    (.ite (.get (arg 1) (.nat 0)) (.call pp (mk3 (arg 0) (.var 1) (arg 2)))
      (.call pp (mk3 (.call iv (arg 0)) (.var 1) (arg 2))))

/-- The cost of `tmJHPowF`, in `U = m + wt (encInt c) + 2`. -/
def tmJHPowK (U : ℕ) : ℕ := 10 ^ 9 * U ^ 5

theorem tmJH_encInt_bits (c : ℤ) :
    encInt c = .list [.nat (if c < 0 then 1 else 0), linBitsVal c.natAbs.bits] := rfl

theorem tmJH_bits_le (c : ℤ) : c.natAbs.bits.length + 1 ≤ (encInt c).wt := by
  rw [tmJH_encInt_bits]
  have h1 : (linBitsVal c.natAbs.bits).wt < (Val.list [.nat (if c < 0 then 1 else 0),
      linBitsVal c.natAbs.bits]).wt := wt_le_wt_list (by simp)
  have h2 := length_lt_wt_list (c.natAbs.bits.map fun b => Val.nat (linBit b))
  simp only [List.length_map] at h2
  change c.natAbs.bits.length < (linBitsVal c.natAbs.bits).wt at h2
  omega

theorem tmJH_pow_spec {P : Program} {f dc pp comp iv : ℕ}
    (hf : P.funs[f]? = some (tmJHPowF dc pp iv)) (hdc : P.funs[dc]? = some (linBitsDecodeF dc))
    (hpp : P.funs[pp]? = some (linPermPowF pp comp)) (hcomp : P.HasAt comp (composeFuns comp))
    (hiv : P.HasAt iv (invFuns iv)) (g : Perm (Fin m)) (c : ℤ) :
    FunDet P f (.list [encPerm g, encInt c, encPerm (1 : Perm (Fin m))]) (encPerm (g ^ c)⁻¹)
      (tmJHPowK (m + (encInt c).wt + 2)) := by
  refine FunDet.intro hf ?_
  unfold tmJHPowF
  set inp := [encPerm g, encInt c, encPerm (1 : Perm (Fin m))] with hinp
  have a1 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 1) (v := encInt c) rfl
  have b1 := Det.get' a1 (Det.nat 1) (vs := [.nat (if c < 0 then 1 else 0),
    linBitsVal c.natAbs.bits]) (v := linBitsVal c.natAbs.bits) rfl
  have hD := linBitsDecode_spec hdc c.natAbs.bits 0 (Nat.zero_le _)
  rw [List.drop_zero, linBitsNat_bits] at hD
  have c1 := Det.call (Det.mk2 b1 (Det.nat 0)) hD
  set env := [Val.list inp, Val.nat c.natAbs] with henv
  have u0 := Det.arg' (P := P) (vs := inp) (rest := [.nat c.natAbs]) (j := 0) (v := encPerm g) rfl
  have u1 := Det.arg' (P := P) (vs := inp) (rest := [.nat c.natAbs]) (j := 1) (v := encInt c) rfl
  have u2 := Det.arg' (P := P) (vs := inp) (rest := [.nat c.natAbs]) (j := 2)
    (v := encPerm (1 : Perm (Fin m))) rfl
  have v1 := Det.var' (P := P) (env := env) (i := 1) (v := .nat c.natAbs) rfl
  have s0 := Det.get' u1 (Det.nat 0) (vs := [.nat (if c < 0 then 1 else 0),
    linBitsVal c.natAbs.bits]) (v := .nat (if c < 0 then 1 else 0)) rfl
  have hp1 := linPermPow_spec hpp hcomp c.natAbs g 1
  have hp2 := linPermPow_spec hpp hcomp c.natAbs g⁻¹ 1
  rw [mul_one] at hp1 hp2
  have t1 := Det.call (Det.mk3 u0 v1 u2) hp1
  have ci := Det.call u0 (inv_spec hiv g)
  have t2 := Det.call (Det.mk3 ci v1 u2) hp2
  have hite := tmJ_det_ite s0 t1 t2
  have hval : (if (if c < 0 then 1 else 0) = 0 then encPerm (g⁻¹ ^ c.natAbs)
      else encPerm (g ^ c.natAbs)) = encPerm (g ^ c)⁻¹ := by
    rw [tmJH_pow_inv]; by_cases hc : c < 0 <;> simp [hc]
  rw [hval] at hite
  refine (Det.letE c1 hite).mono ?_
  -- the cost
  generalize hU : m + (encInt c).wt + 2 = U at *
  have hL := tmJH_bits_le c
  generalize hLd : c.natAbs.bits.length = L at *
  have hU1 : 1 ≤ U := by omega
  have hLU : L + 1 ≤ U := by omega
  have hmU : m + 1 ≤ U := by omega
  have hmL : m + L + 2 ≤ 2 * U := by omega
  have hU2 : U ≤ U ^ 2 := Nat.le_self_pow (by norm_num) _
  have hU23 : U ^ 2 ≤ U ^ 3 := Nat.pow_le_pow_right hU1 (by norm_num)
  have hU34 : U ^ 3 ≤ U ^ 4 := Nat.pow_le_pow_right hU1 (by norm_num)
  have hU45 : U ^ 4 ≤ U ^ 5 := Nat.pow_le_pow_right hU1 (by norm_num)
  have hm2 : (m + 1) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hmU 2
  have hm4 : (m + 1) ^ 4 ≤ U ^ 4 := Nat.pow_le_pow_left hmU 4
  have wg := wt_encPerm_le g
  have wgi := wt_encPerm_le g⁻¹
  have w1 := wt_encPerm_le (1 : Perm (Fin m))
  have wout := wt_encPerm_le (g ^ c)⁻¹
  have wo1 := wt_encPerm_le (g ^ c.natAbs)
  have wo2 := wt_encPerm_le (g⁻¹ ^ c.natAbs)
  have win := wt_list3_le (encPerm g) (encInt c) (encPerm (1 : Perm (Fin m)))
  have wn := wt_nat_le c.natAbs
  have wbits := linBitsVal_wt c.natAbs.bits
  rw [hLd] at wbits
  have wn' : (Val.nat c.natAbs).wt = L + 2 := by rw [wt_nat, linLenBits, hLd]
  have w3a := wt_list3_le (encPerm g) (Val.nat c.natAbs) (encPerm (1 : Perm (Fin m)))
  have w3b := wt_list3_le (encPerm g⁻¹) (Val.nat c.natAbs) (encPerm (1 : Perm (Fin m)))
  have w2 := wt_list2_le (linBitsVal c.natAbs.bits) (.nat 0)
  have hpow : linPermPowCost m L ≤ 10 ^ 6 * 16 * U ^ 5 := by
    unfold linPermPowCost linPermPowUnit
    have h4 : (m + L + 2) ^ 4 ≤ (2 * U) ^ 4 := Nat.pow_le_pow_left hmL 4
    have e : (2 * U) ^ 4 = 16 * U ^ 4 := by ring
    calc (L + 1) * (10 ^ 6 * (m + L + 2) ^ 4) ≤ U * (10 ^ 6 * (16 * U ^ 4)) :=
          Nat.mul_le_mul hLU (Nat.mul_le_mul_left _ (e ▸ h4))
      _ = 10 ^ 6 * 16 * U ^ 5 := by ring
  have hdec : linBitsDecodeCost L 0 ≤ 1000 * U ^ 3 := by
    unfold linBitsDecodeCost
    have h2 : (L + 1) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hLU 2
    calc (L - 0 + 1) * (1000 * (L + 1) ^ 2) ≤ U * (1000 * U ^ 2) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h2)
      _ = 1000 * U ^ 3 := by ring
  have hinv : invK * (m + 1) ^ 4 ≤ 100000 * U ^ 4 := by unfold invK; omega
  have r0 : (Val.list inp).wt = (Val.list [encPerm g, encInt c, encPerm (1 : Perm (Fin m))]).wt :=
    rfl
  have w0 := wt_nat_le 0
  have ws : (Val.nat (if c < 0 then 1 else 0)).wt ≤ 3 := by split <;> decide
  show _ ≤ 10 ^ 9 * U ^ 5
  omega

/-! ### The local product -/

/-- The fold step: on `[[lgV, cv, lc], acc, k]`, with `lgV[k] = [a, g]`, the product
`(g^{c_k} at a; 1) * acc`. -/
def tmJHLamSF (pw locA comp : ℕ) : Expr :=
  .letE (.get (.get (arg 0) (.nat 0)) (arg 2))
    (.call comp (mk2 (.call locA (mk2 (mk2 (.get (arg 0) (.nat 2)) (.get (.var 1) (.nat 0)))
        (.call pw (mk3 (.get (.var 1) (.nat 1)) (.get (.get (arg 0) (.nat 1)) (arg 2))
          (.get (.get (arg 0) (.nat 2)) (.nat 0))))))
      (arg 1)))

/-- On `[lgV, cv, lc]`: fold the step over `k < |lg|`, from the identity of `Fin (m q)`. -/
def tmJHLamF (fld rg : ℕ) : Expr :=
  .call fld (mk3 (.var 0) (.call rg (.length (arg 0)))
    (.call rg (.arith .mul (.get (arg 2) (.nat 3)) (.get (arg 2) (.nat 2)))))

/-- The cost of one step, in `Z = wt [lgV, cv, lc] + (m + 1) (q + 1)`. -/
def tmJHLamSK (Z : ℕ) : ℕ := 10 ^ 16 * Z ^ 8

/-- The cost of `tmJHLamF`, in `Z`. -/
def tmJHLamK (Z : ℕ) : ℕ := 10 ^ 17 * Z ^ 9

/-- Where the pieces of the local product sit. -/
structure TmJHLamAt (P : Program) (f fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte : ℕ) :
    Prop where
  hf : P.funs[f]? = some (tmJHLamF fld rg)
  hfld : P.HasAt fld (foldlFuns fld st)
  hst : P.funs[st]? = some (tmJHLamSF pw locA comp)
  hpw : P.funs[pw]? = some (tmJHPowF dc pp iv)
  hdc : P.funs[dc]? = some (linBitsDecodeF dc)
  hpp : P.funs[pp]? = some (linPermPowF pp comp)
  hcomp : P.HasAt comp (composeFuns comp)
  hiv : P.HasAt iv (invFuns iv)
  hlocA : P.funs[locA]? = some (tmJLocAF dsA pr)
  hds : P.funs[dsA]? = some (tmJDsAF rg tbA)
  hrg : P.HasAt rg (rangeFuns rg)
  htb : P.HasAt tbA (mapFuns tbA tbe)
  htbe : P.funs[tbe]? = some tmJDsAEF
  hpr : TmJPairAt P pr prg prt prte

theorem tmJH_lgVal_get? (lg : List (Fin q × Perm (Fin m))) {i : ℕ} (hi : i < lg.length) :
    (lg.map fun p => Val.list [.nat p.1, encPerm p.2])[i]? =
      some (.list [.nat (lg.get ⟨i, hi⟩).1, encPerm (lg.get ⟨i, hi⟩).2]) := by
  simp [hi]

theorem tmJH_vecVal_get? {n : ℕ} (c : Fin n → ℤ) {i : ℕ} (hi : i < n) :
    ((List.finRange n).map fun j => encInt (c j))[i]? = some (encInt (c ⟨i, hi⟩)) := by
  simp [hi]

theorem tmJH_wt_vec_entry {n : ℕ} (c : Fin n → ℤ) (k : Fin n) :
    (encInt (c k)).wt < (linVecVal c).wt :=
  wt_le_wt_list (List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩)

set_option maxHeartbeats 1000000 in
theorem tmJH_lamS_spec {P : Program} {f fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte : ℕ}
    (hA : TmJHLamAt P f fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte)
    (lg : List (Fin q × Perm (Fin m))) (c : Fin lg.length → ℤ) {i : ℕ} (hi : i < lg.length) :
    FunDet P st (.list [.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q],
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (tmJHLamDi lg c i, 1))),
        .nat i])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP (tmJHLamDi lg c (i + 1), 1))))
      (tmJHLamSK ((Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hst ?_
  unfold tmJHLamSF
  set k : Fin lg.length := ⟨i, hi⟩ with hk
  set cx := Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q] with hcx
  set acc := encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP (tmJHLamDi lg c i, 1))) with hacc
  set inp := [cx, acc, .nat i] with hinp
  have a0 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 0) (v := cx) rfl
  have a2 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 2) (v := .nat i) rfl
  have l0 := Det.get' a0 (Det.nat 0) (vs := [tmJLgVal lg, linVecVal c, tmJLocCtx m q])
    (v := tmJLgVal lg) rfl
  have c1 := Det.get' l0 a2 (tmJH_lgVal_get? lg hi)
  set e := Val.list [.nat (lg.get k).1, encPerm (lg.get k).2] with he
  set env := [Val.list inp, e] with henv
  have b0 := Det.arg' (P := P) (vs := inp) (rest := [e]) (j := 0) (v := cx) rfl
  have b1 := Det.arg' (P := P) (vs := inp) (rest := [e]) (j := 1) (v := acc) rfl
  have b2 := Det.arg' (P := P) (vs := inp) (rest := [e]) (j := 2) (v := .nat i) rfl
  have v1 := Det.var' (P := P) (env := env) (i := 1) (v := e) rfl
  have ea := Det.get' v1 (Det.nat 0) (vs := [.nat (lg.get k).1, encPerm (lg.get k).2])
    (v := .nat (lg.get k).1) rfl
  have eg := Det.get' v1 (Det.nat 1) (vs := [.nat (lg.get k).1, encPerm (lg.get k).2])
    (v := encPerm (lg.get k).2) rfl
  have lc := Det.get' b0 (Det.nat 2) (vs := [tmJLgVal lg, linVecVal c, tmJLocCtx m q])
    (v := tmJLocCtx m q) rfl
  have cvv := Det.get' b0 (Det.nat 1) (vs := [tmJLgVal lg, linVecVal c, tmJLocCtx m q])
    (v := linVecVal c) rfl
  have ck := Det.get' cvv b2 (tmJH_vecVal_get? c hi)
  have one := Det.get' lc (Det.nat 0) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encPerm (1 : Perm (Fin m))) rfl
  have cp := Det.call (Det.mk3 eg ck one) (tmJH_pow_spec hA.hpw hA.hdc hA.hpp hA.hcomp hA.hiv
    (lg.get k).2 (c k))
  have cl := Det.call (Det.mk2 (Det.mk2 lc ea) cp) (tmJ_locA_spec hA.hlocA hA.hds hA.hrg hA.htb
    hA.htbe hA.hpr (lg.get k).1 ((lg.get k).2 ^ c k)⁻¹)
  rw [inv_inv] at cl
  have cc := Det.call (Det.mk2 cl b1) (compose_spec hA.hcomp
    (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc (lg.get k).1 ((lg.get k).2 ^ c k)))
    (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (tmJHLamDi lg c i, 1))))
  rw [← map_mul, tmJHLamDi_succ lg c hi] at cc
  refine (Det.letE c1 cc).mono ?_
  -- the cost
  have wcx : (encInt (c k)).wt < (linVecVal c).wt := tmJH_wt_vec_entry c k
  have wlv : (linVecVal c).wt < cx.wt := wt_le_wt_list (by simp [hcx])
  have wlg : (tmJLgVal lg).wt < cx.wt := wt_le_wt_list (by simp [hcx])
  have wlc : (tmJLocCtx m q).wt < cx.wt := wt_le_wt_list (by simp [hcx])
  have we : e.wt < (tmJLgVal lg).wt := wt_le_wt_list (by
    rw [he]; exact List.mem_of_getElem? (tmJH_lgVal_get? lg hi))
  have hil : i < (tmJLgVal lg).wt := by
    have := length_lt_wt_list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])
    simp only [List.length_map] at this
    change lg.length < (tmJLgVal lg).wt at this
    omega
  generalize hZ : cx.wt + (m + 1) * (q + 1) = Z at *
  generalize hV : (m + 1) * (q + 1) = V at *
  have hm1 : m + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ V := by rw [← hV]; nlinarith
  have hVZ : V ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have hZ3 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hZ5 : Z ^ 3 ≤ Z ^ 5 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hZ8 : Z ^ 5 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hmq2 : (m * q + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (hmq.trans hVZ) 2
  have hmq3 : (m * q + 1) ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left (hmq.trans hVZ) 3
  have hm2 : (m + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (hm1.trans hVZ) 2
  have hU : m + (encInt (c k)).wt + 2 ≤ Z := by omega
  have hpw : tmJHPowK (m + (encInt (c k)).wt + 2) ≤ 10 ^ 9 * Z ^ 8 := by
    unfold tmJHPowK
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hU 5).trans hZ8)
  have hloc : tmJLocK V ≤ 10 ^ 14 * Z ^ 8 := by
    unfold tmJLocK; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hVZ 8)
  have wacc := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP (tmJHLamDi lg c i, 1)))
  have wacc' := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP (tmJHLamDi lg c (i + 1), 1)))
  have wloc := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJLoc (lg.get k).1 ((lg.get k).2 ^ c k)))
  have wpw := wt_encPerm_le ((lg.get k).2 ^ c k)⁻¹
  have wg := wt_encPerm_le (lg.get k).2
  have w1 := wt_encPerm_le (1 : Perm (Fin m))
  have wi := wt_nat_le i
  have wa := wt_nat_le ((lg.get k).1 : ℕ)
  have ha := ((lg.get k).1).2
  have wq := wt_nat_le q
  have hqZ : q ≤ Z := by omega
  have win := wt_list3_le cx acc (.nat i)
  have w3 := wt_list3_le (encPerm (lg.get k).2) (encInt (c k)) (encPerm (1 : Perm (Fin m)))
  have w2 := wt_list2_le (tmJLocCtx m q) (.nat (lg.get k).1)
  have w2' := wt_list2_le (Val.list [tmJLocCtx m q, .nat (lg.get k).1])
    (encPerm ((lg.get k).2 ^ c k)⁻¹)
  have w2'' := wt_list2_le (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJLoc (lg.get k).1 ((lg.get k).2 ^ c k)))) acc
  have hperm : permK * (m * q + 1) ^ 3 ≤ 30000 * Z ^ 3 := by unfold permK; omega
  have r0 : (Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]).wt = cx.wt := rfl
  have r1 : (Val.list inp).wt = (Val.list [cx, acc, .nat i]).wt := rfl
  have r2 : acc.wt = (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP (tmJHLamDi lg c i, 1)))).wt := rfl
  have r3 : (encInt (c ⟨i, hi⟩)).wt = (encInt (c k)).wt := rfl
  have r4 : (Val.list [encPerm (lg.get k).2, encInt (c ⟨i, hi⟩), encPerm (1 : Perm (Fin m))]).wt =
    (Val.list [encPerm (lg.get k).2, encInt (c k), encPerm (1 : Perm (Fin m))]).wt := rfl
  show _ ≤ 10 ^ 16 * Z ^ 8
  omega

theorem tmJH_lam_spec {P : Program} {f fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte : ℕ}
    (hA : TmJHLamAt P f fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte)
    (lg : List (Fin q × Perm (Fin m))) (c : Fin lg.length → ℤ) :
    FunDet P f (.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLam lg c)))
      (tmJHLamK ((Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJHLamF
  have v0 := Det.var' (P := P) (env := [Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]])
    (i := 0) (v := Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]) rfl
  have a0 := Det.arg' (P := P) (vs := [tmJLgVal lg, linVecVal c, tmJLocCtx m q]) (rest := [])
    (j := 0) (v := tmJLgVal lg) rfl
  have a2 := Det.arg' (P := P) (vs := [tmJLgVal lg, linVecVal c, tmJLocCtx m q]) (rest := [])
    (j := 2) (v := tmJLocCtx m q) rfl
  have hlen : (lg.map fun p => Val.list [.nat p.1, encPerm p.2]).length = lg.length := by simp
  have dl := Det.length a0 (vs := lg.map fun p => Val.list [.nat p.1, encPerm p.2])
  rw [hlen] at dl
  have rn := Det.call dl (tmJ_range_det hA.hrg lg.length)
  have g3 := Det.get' a2 (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have g2 := Det.get' a2 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have dmq := Det.arith' (op := .mul) g3 g2 (z := m * q) rfl
  have rmq := Det.call dmq (tmJ_range_det hA.hrg (m * q))
  rw [tmJ_encFun_id_eq (m * q)] at rmq
  have hxl : ((List.finRange lg.length).map fun i : Fin lg.length => Val.nat (i : ℕ)).length =
      lg.length := by simp
  have hxi : ∀ i (hi : i < ((List.finRange lg.length).map fun i : Fin lg.length =>
      Val.nat (i : ℕ)).length),
      ((List.finRange lg.length).map fun i : Fin lg.length => Val.nat (i : ℕ))[i] = .nat i := by
    intro i hi; simp
  have hF := foldl_spec hA.hfld (c := Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q])
    (xs := (List.finRange lg.length).map fun i : Fin lg.length => Val.nat (i : ℕ))
    (acc0 := encPerm (1 : Perm (Fin (m * q))))
    (Inv := fun i acc => acc = encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
      (tmJP (tmJHLamDi lg c i, 1))))
    (M := 4 * (m * q + 1) ^ 2)
    (B := fun _ => tmJHLamSK ((Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]).wt +
      (m + 1) * (q + 1)))
    (by beta_reduce; rw [tmJHLamDi_zero, tmJP_one, map_one])
    (fun i acc _ h => by rw [h]; exact wt_encPerm_le _)
    (fun i acc hi h => by
      rw [h, hxi i hi]
      rw [hxl] at hi
      exact FunAll.mono (tmJH_lamS_spec (P := P) (st := st) hA lg c hi) fun w cost hw =>
        ⟨hw.1, hw.2⟩)
  rw [hxl] at hF
  have hF' : FunDet P fld (.list [Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q],
      .list ((List.finRange lg.length).map fun i : Fin lg.length => Val.nat (i : ℕ)),
      encPerm (1 : Perm (Fin (m * q)))])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLam lg c)))
      (∑ i ∈ Finset.range lg.length, tmJHLamSK ((Val.list [tmJLgVal lg, linVecVal c,
        tmJLocCtx m q]).wt + (m + 1) * (q + 1)) + loopModK * (lg.length + 1) *
        ((Val.list [Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q],
          .list ((List.finRange lg.length).map fun i : Fin lg.length => Val.nat (i : ℕ)),
          encPerm (1 : Perm (Fin (m * q)))]).wt + lg.length + 4 * (m * q + 1) ^ 2 + 1)) := by
    refine FunAll.mono hF fun w cost hw => ⟨?_, hw.2⟩
    rw [hw.1, tmJHLamDi_full]
    rfl
  have hids : (encFun fun i : Fin lg.length => (i : ℕ)) =
      .list ((List.finRange lg.length).map fun i : Fin lg.length => Val.nat (i : ℕ)) := rfl
  rw [hids] at rn
  have cf := Det.call (Det.mk3 v0 rn rmq) hF'
  refine cf.mono ?_
  -- the cost
  have wlg : (tmJLgVal lg).wt < (Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]).wt :=
    wt_le_wt_list (by simp)
  have wlc : (tmJLocCtx m q).wt < (Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]).wt :=
    wt_le_wt_list (by simp)
  have hnl : lg.length < (tmJLgVal lg).wt := by
    have := length_lt_wt_list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])
    simp only [List.length_map] at this
    exact this
  have wids := wt_ids_le lg.length
  rw [hids] at wids
  have wid1 := wt_ids_le (m * q)
  rw [tmJ_encFun_id_eq] at wid1
  have w3 := wt_list3_le (Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q])
    (.list ((List.finRange lg.length).map fun i : Fin lg.length => Val.nat (i : ℕ)))
    (encPerm (1 : Perm (Fin (m * q))))
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLam lg c))
  have wm := wt_nat_le m
  have wq := wt_nat_le q
  have wmq := wt_nat_le (m * q)
  have wlen := wt_nat_le lg.length
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  generalize hX : (Val.list [tmJLgVal lg, linVecVal c, tmJLocCtx m q]).wt = X at *
  generalize hV : (m + 1) * (q + 1) = V at *
  have hm1 : m + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ V := by rw [← hV]; nlinarith
  generalize hZ : X + V = Z at *
  have hVZ : V ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have hZ3 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hZ9 : Z ^ 3 ≤ Z ^ 9 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hmq2 : (m * q + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (hmq.trans hVZ) 2
  have hmq3 : (m * q + 1) ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left (hmq.trans hVZ) 3
  have hn1 : (lg.length + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (lg.length + 1) ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have l1 : lg.length * tmJHLamSK Z ≤ 10 ^ 16 * Z ^ 9 := by
    unfold tmJHLamSK
    calc lg.length * (10 ^ 16 * Z ^ 8) ≤ Z * (10 ^ 16 * Z ^ 8) := Nat.mul_le_mul (by omega) le_rfl
      _ = 10 ^ 16 * Z ^ 9 := by ring
  have l2 : loopModK * (lg.length + 1) * ((Val.list [Val.list [tmJLgVal lg, linVecVal c,
      tmJLocCtx m q], .list ((List.finRange lg.length).map fun i : Fin lg.length =>
        Val.nat (i : ℕ)), encPerm (1 : Perm (Fin (m * q)))]).wt +
      lg.length + 4 * (m * q + 1) ^ 2 + 1) ≤ 1000 * Z * (100 * Z ^ 2) := by
    unfold loopModK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : 1000 * Z * (100 * Z ^ 2) = 100000 * Z ^ 3 := by ring
  have hr1 : 10000 * (lg.length + 1) ^ 3 ≤ 10000 * Z ^ 3 := Nat.mul_le_mul_left _ hn3
  have hr2 : 10000 * (m * q + 1) ^ 3 ≤ 10000 * Z ^ 3 := Nat.mul_le_mul_left _ hmq3
  show _ ≤ 10 ^ 17 * Z ^ 9
  omega

/-! ### The correction -/

/-- On `[TlV, lc, k, encPerm λ]`: the first lifted transposition of `Tl` (if `k ≠ 0`), or `1`,
times `λ`. -/
def tmJHCorrF (swS rg comp : ℕ) : Expr :=
  .call comp (mk2 (.ite (arg 2)
      (.call swS (mk4 (.get (.get (arg 0) (.nat 0)) (.nat 2)) (arg 1)
        (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))))
      (.call rg (.arith .mul (.get (arg 1) (.nat 3)) (.get (arg 1) (.nat 2)))))
    (arg 3))

/-- The cost of `tmJHCorrF`, in `Z = wt [TlV, lc, k, encPerm λ] + (m + 1) (q + 1)`. -/
def tmJHCorrK (Z : ℕ) : ℕ := 10 ^ 16 * Z ^ 8

/-- Where the pieces of the correction sit. -/
structure TmJHCorrAt (P : Program) (f swS rg comp iv tbD swDE tbP swPE pr prg prt prte : ℕ) :
    Prop where
  hf : P.funs[f]? = some (tmJHCorrF swS rg comp)
  hswS : P.funs[swS]? = some (tmJSwSF iv tbD tbP pr)
  hiv : P.HasAt iv (invFuns iv)
  htbD : P.HasAt tbD (mapFuns tbD swDE)
  hswDE : P.funs[swDE]? = some tmJSwDEF
  htbP : P.HasAt tbP (mapFuns tbP swPE)
  hswPE : P.funs[swPE]? = some tmJSwPEF
  hpr : TmJPairAt P pr prg prt prte
  hrg : P.HasAt rg (rangeFuns rg)
  hcomp : P.HasAt comp (composeFuns comp)

theorem tmJH_corr_spec {P : Program} {f swS rg comp iv tbD swDE tbP swPE pr prg prt prte : ℕ}
    (hA : TmJHCorrAt P f swS rg comp iv tbD swDE tbP swPE pr prg prt prte)
    (Tl : List (Fin q × Fin q × Perm (Fin m))) (k : ℕ) (hne : k ≠ 0 → Tl ≠ [])
    (lam : Perm (Fin m × Fin q)) :
    FunDet P f (.list [tmJTlVal Tl, tmJLocCtx m q, .nat k,
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        ((if k = 0 then 1 else tmJSw0 Tl) * lam)))
      (tmJHCorrK ((Val.list [tmJTlVal Tl, tmJLocCtx m q, .nat k,
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]).wt +
          (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJHCorrF
  have a0 := Det.arg' (P := P) (vs := [tmJTlVal Tl, tmJLocCtx m q, .nat k,
    encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]) (rest := []) (j := 0)
    (v := tmJTlVal Tl) rfl
  have a1 := Det.arg' (P := P) (vs := [tmJTlVal Tl, tmJLocCtx m q, .nat k,
    encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]) (rest := []) (j := 1)
    (v := tmJLocCtx m q) rfl
  have a2 := Det.arg' (P := P) (vs := [tmJTlVal Tl, tmJLocCtx m q, .nat k,
    encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]) (rest := []) (j := 2)
    (v := .nat k) rfl
  have a3 := Det.arg' (P := P) (vs := [tmJTlVal Tl, tmJLocCtx m q, .nat k,
    encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]) (rest := []) (j := 3)
    (v := encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)) rfl
  obtain ⟨W, hW⟩ : ∃ W, W = (Val.list [tmJTlVal Tl, tmJLocCtx m q, .nat k,
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]).wt := ⟨_, rfl⟩
  have wl : (tmJLocCtx m q).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wTl : (tmJTlVal Tl).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wk : (Val.nat k).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wlv : (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)).wt < W :=
    hW ▸ wt_le_wt_list (by simp)
  have hloc : tmJLocK ((m + 1) * (q + 1)) = 10 ^ 14 * ((m + 1) * (q + 1)) ^ 8 := rfl
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have hmqV : m * q ≤ (m + 1) * (q + 1) := by nlinarith
  have hmV : m ≤ (m + 1) * (q + 1) := by nlinarith
  have hqV : q ≤ (m + 1) * (q + 1) := by nlinarith
  have hV1 : 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have h3 : (m * q + 1) ^ 3 ≤ ((m + 1) * (q + 1)) ^ 3 := Nat.pow_le_pow_left hmq 3
  have h38 : ((m + 1) * (q + 1)) ^ 3 ≤ ((m + 1) * (q + 1)) ^ 8 :=
    Nat.pow_le_pow_right hV1 (by norm_num)
  have hV8 : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 8 := Nat.le_self_pow (by norm_num) _
  obtain ⟨sw, hsw⟩ : ∃ sw, sw = toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
      (if k = 0 then 1 else tmJSw0 Tl) := ⟨_, rfl⟩
  have wsw := wt_encPerm_le sw
  have hT : k ≠ 0 → Det P [Val.list [tmJTlVal Tl, tmJLocCtx m q, .nat k,
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]]
      (.call swS (mk4 (.get (.get (arg 0) (.nat 0)) (.nat 2))
      (arg 1) (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))))
      (encPerm sw) (100 * W + tmJLocK ((m + 1) * (q + 1)) + 10 * (encPerm sw).wt + 100) := by
    intro hk
    obtain ⟨t, Tr, rfl⟩ := List.exists_cons_of_ne_nil (hne hk)
    have ht := Det.get' a0 (Det.nat 0) (vs := (t :: Tr).map tmJTrVal) (v := tmJTrVal t) rfl
    have tb := Det.get' ht (Det.nat 2) (vs := [.nat t.1, .nat t.2.1, encPerm t.2.2])
      (v := encPerm t.2.2) rfl
    have ta := Det.get' ht (Det.nat 0) (vs := [.nat t.1, .nat t.2.1, encPerm t.2.2])
      (v := .nat t.1) rfl
    have ta' := Det.get' ht (Det.nat 1) (vs := [.nat t.1, .nat t.2.1, encPerm t.2.2])
      (v := .nat t.2.1) rfl
    have cs := Det.call (Det.mk4 tb a1 ta ta') (tmJ_swS_spec hA.hswS hA.hiv hA.htbD hA.hswDE
      hA.htbP hA.hswPE hA.hpr t.1 t.2.1 t.2.2)
    have esw : toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJSw t.1 t.2.1 t.2.2) = sw := by
      rw [hsw, if_neg hk]; rfl
    rw [esw] at cs
    refine cs.mono ?_
    have wt0 : (tmJTrVal t).wt < (tmJTlVal (t :: Tr)).wt :=
      wt_le_wt_list (by simp [tmJTlVal])
    have w0 : (encPerm t.2.2).wt < (tmJTrVal t).wt := wt_le_wt_list (by simp [tmJTrVal])
    have w1 : (Val.nat t.1).wt < (tmJTrVal t).wt := wt_le_wt_list (by simp [tmJTrVal])
    have w2 : (Val.nat t.2.1).wt < (tmJTrVal t).wt := wt_le_wt_list (by simp [tmJTrVal])
    have w4 := wt_list4_le (encPerm t.2.2) (tmJLocCtx m q) (.nat t.1) (.nat t.2.1)
    omega
  have hE : k = 0 → Det P [Val.list [tmJTlVal Tl, tmJLocCtx m q, .nat k,
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam)]]
      (.call rg (.arith .mul (.get (arg 1) (.nat 3)) (.get (arg 1) (.nat 2))))
      (encPerm sw) (100 * W + tmJLocK ((m + 1) * (q + 1)) + 10 * (encPerm sw).wt + 100) := by
    intro hk
    have g3 := Det.get' a1 (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
    have g2 := Det.get' a1 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
    have dmq := Det.arith' (op := .mul) g3 g2 (z := m * q) rfl
    have rmq := Det.call dmq (tmJ_range_det hA.hrg (m * q))
    have esw : encFun (fun i : Fin (m * q) => (i : ℕ)) = encPerm sw := by
      rw [hsw, if_pos hk, map_one]; rfl
    rw [esw] at rmq
    refine rmq.mono ?_
    have wm := wt_nat_le m
    have wq := wt_nat_le q
    have wmq := wt_nat_le (m * q)
    omega
  have hite := Det.ite (v := encPerm sw) a2 hT hE
  rw [max_self] at hite
  have cc := Det.call (Det.mk2 hite a3) (compose_spec hA.hcomp sw
    (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam))
  rw [hsw, ← map_mul] at cc
  refine cc.mono ?_
  -- the cost
  rw [← hsw] at ⊢
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    ((if k = 0 then 1 else tmJSw0 Tl) * lam))
  have w2 := wt_list2_le (encPerm sw)
    (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) lam))
  rw [← hW]
  generalize hV : (m + 1) * (q + 1) = V at *
  generalize hZ : W + V = Z at *
  have hVZ : V ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have hZ3 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hZ8 : Z ^ 3 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hmq2 : (m * q + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (hmq.trans hVZ) 2
  have hmq3 : (m * q + 1) ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left (hmq.trans hVZ) 3
  have hVZ8 : V ^ 8 ≤ Z ^ 8 := Nat.pow_le_pow_left hVZ 8
  have hperm : permK * (m * q + 1) ^ 3 ≤ 30000 * Z ^ 3 := by unfold permK; omega
  show _ ≤ 10 ^ 16 * Z ^ 8
  omega

end GI.Impl
