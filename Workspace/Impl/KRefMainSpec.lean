import Workspace.Impl.KRefMain

/-!
# What the whole program computes

`kref_main_det`: on the input `[0^n, c, c']`, the program `krefProg k` returns the state of
`krefIter c c' (2 n^k)`, at cost at most `krefMainK * (krefZ n k + 1) ^ 9`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp len)

variable {n k : ℕ}

def krefMainK : ℕ :=
  30 * (loopModK * (krefRoundK + 20) + krefNbsK + krefTausK + krefRhosMK + loopModK * 320 * 27 +
    3000) + 1000000

theorem kref_iter0 (c c' : (Fin k → Fin n) → ℕ) :
    krefSt (krefIter c c' 0) = .list [encKColoring c, encKColoring c'] := by
  rw [kref_St_eq]; simp [krefIter, krefJoin]

set_option maxHeartbeats 1000000 in
/-- **The whole program.** -/
theorem kref_main_det (c c' : (Fin k → Fin n) → ℕ) (hc : ∀ x, c x ≤ n ^ k)
    (hc' : ∀ x, c' x ≤ n ^ k) :
    FunDet (krefProg k) 0
      (.list [.list (List.replicate n (.nat 0)), encKColoring c, encKColoring c'])
      (krefSt (krefIter c c' (2 * n ^ k))) (krefMainK * (krefZ n k + 1) ^ 9) := by
  obtain ⟨hR, hPW, hMT, hDG, hMR, hRH, hNB, -, -, -, hIT, hG, -⟩ := kref_layout k
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  have hnX := @n_le_krefX n k
  have hkX := @k_le_krefX n k
  have hNX := @N_le_krefX n k
  have hkkX := @kk_le_krefX n k
  have hMX := kref_M_le (col := krefIter c c' 0) (krefIter_small c c' hc hc' 0)
  -- weights
  have wZ0 := kref_wt_zeros n
  have wC := kref_wt_encK hc
  have wC' := kref_wt_encK hc'
  have wpw := kref_wt_pw (n := n) (k := k)
  have wpwk := kref_wt_pwk (n := n) (k := k)
  have wtau := kref_wt_taus (n := n) (k := k)
  have wrho := kref_wt_rhos (n := n) (k := k)
  have wnbs := kref_wt_nbs (n := n) (k := k)
  have wRC := kref_wt_RCtx (n := n) (k := k)
  have wrk := kref_wt_range (n := n) (k := k) (m := k) (by omega)
  have wrkk := kref_wt_range (n := n) (k := k) (m := k ^ k) (by omega)
  have wrn := kref_wt_range (n := n) (k := k) (m := n) (by omega)
  have wrN := kref_wt_range (n := n) (k := k) (m := n ^ k) (by omega)
  have wrM := kref_wt_range (n := n) (k := k) (m := krefM n k) hMX
  have wS0 := kref_wt_St (krefIter_small c c' hc hc' 0)
  have wSf := kref_wt_St (krefIter_small c c' hc hc' (2 * n ^ k))
  have eT : krefTausV k = .list ((krefTups k k).map fun τ => natList (krefDig τ)) := by
    simp [krefTausV, List.map_map, Function.comp_def]
  have wtau' : (krefTausV k).wt ≤ 30 * krefX n k ^ 3 := by rw [eT]; exact wtau
  have hWI : (Val.list [.list (List.replicate n (.nat 0)), encKColoring c,
      encKColoring c']).wt ≤ 50 * krefX n k ^ 2 := by
    have := wt_list3_le (.list (List.replicate n (.nat 0))) (encKColoring c) (encKColoring c')
    omega
  -- the module calls
  have cpw := kref_pows hPW (m := n) (e := k) (Z := krefZ n k) (by omega) (by omega) (by omega)
  have cpwk := kref_pows hPW (m := k) (e := k) (Z := krefZ n k) (by omega) (by omega) (by omega)
  have ctau := kref_taus (n := n) (k := k) hMT hDG
  have crho := kref_rhosM (n := n) (k := k) hMR hRH
  have cnbs := kref_nbs hNB (kref_at_nbAt k) (n := n) (k := k)
  have crk := kref_range hR (m := k) (Z := krefZ n k) (by omega) (by omega)
  have crkk := kref_range hR (m := k ^ k) (Z := krefZ n k) (by omega) (by omega)
  have crn := kref_range hR (m := n) (Z := krefZ n k) (by omega) (by omega)
  have crN := kref_range hR (m := n ^ k) (Z := krefZ n k) (by omega) (by omega)
  have crM := kref_range hR (m := krefM n k) (Z := krefZ n k) (by omega) (by omega)
  have cit := kref_iter hIT (c := krefRCtx n k) (n := 2 * n ^ k)
    (accs := fun i => krefSt (krefIter c c' i)) (Y := krefZ n k) (K := krefRoundK) (d := 7)
    (fun i hi => kref_roundG hG (kref_at_roundAt k) (krefIter_small c c' hc hc' i) (by omega))
    (fun i _ => by beta_reduce; have := kref_wt_St (krefIter_small c c' hc hc' i); omega)
    (by omega) (by omega)
  beta_reduce at cit
  rw [kref_iter0] at cit
  replace cit : FunDet (krefProg k) 48 (.list [krefRCtx n k, .nat (2 * n ^ k),
      .list [encKColoring c, encKColoring c']]) (krefSt (krefIter c c' (2 * n ^ k)))
      (loopModK * (krefRoundK + 20) * (krefZ n k + 1) ^ 9) := cit
  -- the environment
  set V : List Val := [.list (List.replicate n (.nat 0)), encKColoring c, encKColoring c'] with hV
  have d1 : Det (krefProg k) [.list V] (.length (arg 0)) (.nat n)
      (2 * (Val.list V).wt + 0 + 5 + n + 3) := by
    have := Det.length (Det.arg' (P := krefProg k) (vs := V) (rest := []) (j := 0) rfl)
    rwa [List.length_replicate] at this
  have d2 : Det (krefProg k) [.list V, .nat n] (.length (arg 1)) (.nat (n ^ k))
      (2 * (Val.list V).wt + 1 + 5 + n ^ k + 3) := by
    have := Det.length (Det.arg' (P := krefProg k) (vs := V) (rest := [.nat n]) (j := 1)
      (v := .list ((List.finRange (n ^ k)).map fun j => .nat (c (finFunctionFinEquiv.symm j))))
      rfl)
    rwa [List.length_map, List.length_finRange] at this
  set E2 : List Val := [.list V, .nat n, .nat (n ^ k)] with hE2
  have d3 := Det.call (P := krefProg k) (env := E2) (Det.mk3 (Det.var' (i := 1) (v := .nat n) rfl)
    (Det.nat k) Det.nil) cpw
  set E3 : List Val := E2 ++ [natList (krefPowList n k)] with hE3
  have d4 := Det.call (P := krefProg k) (env := E3) (Det.mk3 (Det.nat k) (Det.nat k) Det.nil) cpwk
  set E4 : List Val := E3 ++ [natList (krefPowList k k)] with hE4
  have d5 := Det.call (P := krefProg k) (env := E4)
    (Det.mk2 (Det.mk2 (Det.var' (i := 4) (v := natList (krefPowList k k)) rfl) (Det.nat k))
      (Det.call (Det.nat (k ^ k)) crkk)) ctau
  set E5 : List Val := E4 ++ [krefTausV k] with hE5
  have d6 := Det.call (P := krefProg k) (env := E5)
    (Det.mk2 (Det.mk2 (Det.call (Det.nat k) crk) (Det.nat k)) (Det.call (Det.nat k) crk)) crho
  set E6 : List Val := E5 ++ [.list ((krefRhos k).map natList)] with hE6
  have d7a := Det.snoc (Det.mk4 (P := krefProg k) (env := E6)
    (Det.var' (i := 3) (v := natList (krefPowList n k)) rfl) (Det.var' (i := 1) (v := .nat n) rfl)
    (Det.var' (i := 5) (v := krefTausV k) rfl)
    (Det.var' (i := 6) (v := .list ((krefRhos k).map natList)) rfl))
    (Det.call (Det.var' (i := 1) (v := .nat n) rfl) crn)
  have d7 := Det.call (Det.mk2 d7a (Det.call (Det.var' (i := 2) (v := .nat (n ^ k)) rfl) crN)) cnbs
  set E7 : List Val := E6 ++ [krefNbs n k] with hE7
  have u1 : Det (krefProg k) E7 (.var 1) (.nat n) ((Val.nat n).wt + 1) := Det.var' rfl
  have u2 : Det (krefProg k) E7 (.var 2) (.nat (n ^ k)) ((Val.nat (n ^ k)).wt + 1) := Det.var' rfl
  have u7 : Det (krefProg k) E7 (.var 7) (krefNbs n k) ((krefNbs n k).wt + 1) := Det.var' rfl
  have a1 := Det.arith (op := .mul) (Det.nat (P := krefProg k) (env := E7) 2) u2
  have a2 := Det.arith (op := .add) a1 u1
  have a3 := Det.arith (op := .add) a2 (Det.nat k)
  have a4 := Det.arith (op := .add) a3 (Det.nat 2)
  have m1 := Det.arith (op := .mul) (Det.nat (P := krefProg k) (env := E7) 2) u2
  have m2 := Det.arith (op := .mul) m1 u1
  have n2 := Det.arith (op := .mul) (Det.nat (P := krefProg k) (env := E7) 2) u2
  simp only [BinOp.eval] at a1 a2 a3 a4 m1 m2 n2
  have eB : 2 * n ^ k + n + k + 2 = krefB n k := rfl
  have eM : 2 * n ^ k * n = krefM n k := rfl
  rw [eB] at a4
  rw [eM] at m2
  have gC : Det (krefProg k) E7 (arg 1) (encKColoring c) (2 * (Val.list V).wt + 1 + 5) :=
    Det.arg' rfl
  have gC' : Det (krefProg k) E7 (arg 2) (encKColoring c') (2 * (Val.list V).wt + 2 + 5) :=
    Det.arg' rfl
  have d8 := Det.call (Det.mk3 (Det.mk3 u7 a4 (Det.call m2 crM)) n2 (Det.mk2 gC gC')) cit
  have hall := Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6
    (Det.letE d7 d8))))))
  refine FunDet.intro (kref_at_main k) (hall.mono ?_)
  -- the cost
  have := wt_nat_le n
  have := wt_nat_le (n ^ k)
  have := wt_nat_le k
  have := wt_nat_le (k ^ k)
  have := wt_nat_le 2
  have := wt_nat_le (2 * n ^ k)
  have := wt_nat_le (2 * n ^ k + n)
  have := wt_nat_le (2 * n ^ k + n + k)
  have := wt_nat_le (krefB n k)
  have := wt_nat_le (krefM n k)
  have hBX : krefB n k ≤ 2 * krefX n k := by unfold krefB krefX; omega
  have h0 := wt_list_le ([] : List Val)
  simp only [List.map_nil, List.sum_nil, List.length_nil] at h0
  have := wt_list3_le (.nat n) (.nat k) (.list [])
  have := wt_list3_le (.nat k) (.nat k) (.list [])
  have := wt_list2_le (natList (krefPowList k k)) (.nat k)
  have := wt_list2_le (.list [natList (krefPowList k k), .nat k]) (natList (List.range (k ^ k)))
  have := wt_list2_le (natList (List.range k)) (.nat k)
  have := wt_list2_le (.list [natList (List.range k), .nat k]) (natList (List.range k))
  have := wt_list4_le (natList (krefPowList n k)) (.nat n) (krefTausV k)
    (.list ((krefRhos k).map natList))
  have := wt_list_snoc_le [natList (krefPowList n k), .nat n, krefTausV k,
    .list ((krefRhos k).map natList)] (natList (List.range n))
  have := wt_list2_le (.list ([natList (krefPowList n k), .nat n, krefTausV k,
    .list ((krefRhos k).map natList)] ++ [natList (List.range n)])) (natList (List.range (n ^ k)))
  have := wt_list3_le (krefNbs n k) (.nat (krefB n k)) (natList (List.range (krefM n k)))
  have := wt_list2_le (encKColoring c) (encKColoring c')
  have := wt_list3_le (.list [krefNbs n k, .nat (krefB n k), natList (List.range (krefM n k))])
    (.nat (2 * n ^ k)) (.list [encKColoring c, encKColoring c'])
  have eR : (Val.list [krefNbs n k, .nat (krefB n k), natList (List.range (krefM n k))]).wt =
      (krefRCtx n k).wt := rfl
  have hT : krefZ n k + 1 ≤ (krefZ n k + 1) ^ 9 := kref_le_pow (by norm_num)
  have p2 : (krefZ n k + 1) ^ 2 ≤ (krefZ n k + 1) ^ 9 := kref_pow_mono (by norm_num)
  have p3 : loopModK * 320 * 27 * (krefZ n k + 1) ^ 3 ≤ loopModK * 320 * 27 * (krefZ n k + 1) ^ 9 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have p5 : krefTausK * (krefZ n k + 1) ^ 5 ≤ krefTausK * (krefZ n k + 1) ^ 9 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have p5' : krefRhosMK * (krefZ n k + 1) ^ 5 ≤ krefRhosMK * (krefZ n k + 1) ^ 9 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have e : krefMainK * (krefZ n k + 1) ^ 9 =
      30 * (loopModK * (krefRoundK + 20) * (krefZ n k + 1) ^ 9) +
      30 * (krefNbsK * (krefZ n k + 1) ^ 9) + 30 * (krefTausK * (krefZ n k + 1) ^ 9) +
      30 * (krefRhosMK * (krefZ n k + 1) ^ 9) +
      30 * (loopModK * 320 * 27 * (krefZ n k + 1) ^ 9) + 90000 * (krefZ n k + 1) ^ 9 +
      1000000 * (krefZ n k + 1) ^ 9 := by
    unfold krefMainK; ring
  have e2 : 3000 * (krefZ n k + 1) ^ 2 ≤ 3000 * (krefZ n k + 1) ^ 9 := Nat.mul_le_mul_left _ p2
  rw [e]
  omega

end GI.Impl
