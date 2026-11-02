import Workspace.Impl.VsPKey
import Workspace.Proved.VsPPairMath

/-!
# Words `∏ g_i ^ a_i` as a program

`vsPWordFuns`: on `[[gs, a, 1], k]` (with `k = |gs| = |a|`) the permutation
`vsPW gs a = g_0^{a_0} ⋯ g_{k-1}^{a_{k-1}}` (`vsPWord_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem vsPW_take_succ {G : Type*} [Group G] (gs : List G) (a : List ℕ) (i : ℕ)
    (hi : i < gs.length) (ha : i < a.length) :
    vsPW (gs.take (i + 1)) (a.take (i + 1)) = vsPW (gs.take i) (a.take i) * gs[i] ^ a[i] := by
  unfold vsPW
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem ha, Option.toList_some, Option.toList_some, List.zipWith_append
      (by simp; omega)]
  simp

/-- The step, on `[[gs, a, 1], i, acc]`: `acc * g_i ^ a_i`. -/
def vsPWStepE' (comp pow : ℕ) : Expr :=
  .call comp (mk2 (arg 2) (.call pow (mk4 (.nat 0) (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 2)))))

/-- The word program at base `b` (4 functions; `comp`, `pow` external). -/
def vsPWordFuns (b comp pow : ℕ) : List Expr := iterFuns b (b + 3) ++ [vsPWStepE' comp pow]

/-- The cost of a word. -/
def vsPWordCost (n N : ℕ) : ℕ := (N + 1) * (10 ^ 7 * (N + 1) ^ 5) + 10 ^ 6 * (N + 1) * (N + 1) ^ 4

set_option maxHeartbeats 4000000 in
theorem vsPWord_spec {P : Program} {b comp pow n N : ℕ} (h : P.HasAt b (vsPWordFuns b comp pow))
    (hcomp : P.HasAt comp (composeFuns comp)) (hpow : P.HasAt pow (vsPPowFuns pow))
    (hnN : n ≤ N) {gs : List (Perm (Fin n))} {a : List ℕ} (hl : a.length = gs.length)
    (hgl : gs.length ≤ N) (ha : ∀ x ∈ a, x ≤ N) :
    FunDet P b (.list [.list [.list (gs.map encPerm), natList a, encPerm (1 : Perm (Fin n))],
      .nat gs.length, encPerm (1 : Perm (Fin n))]) (encPerm (vsPW gs a)) (vsPWordCost n N) := by
  have hit : P.HasAt b (iterFuns b (b + 3)) := h.block 0 rfl
  have hst : P.funs[b + 3]? = some (vsPWStepE' comp pow) := h.get (j := 3) (by simp [vsPWordFuns, iterFuns, loopFuns])
  set c := Val.list [.list (gs.map encPerm), natList a, encPerm (1 : Perm (Fin n))]
  have hM : ∀ i acc, i ≤ gs.length → acc = encPerm (vsPW (gs.take i) (a.take i)) →
      acc.wt ≤ 4 * (N + 1) ^ 2 := by
    rintro i acc - rfl
    exact (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hstep : ∀ i acc, i < gs.length → acc = encPerm (vsPW (gs.take i) (a.take i)) →
      FunAll P (b + 3) (.list [c, .nat i, acc]) (fun w cost =>
        w = encPerm (vsPW (gs.take (i + 1)) (a.take (i + 1))) ∧ cost ≤ 10 ^ 7 * (N + 1) ^ 5) := by
    rintro i acc hi rfl
    have hia : i < a.length := by omega
    set vs := [c, Val.nat i, encPerm (vsPW (gs.take i) (a.take i))]
    have a0 : Det P [.list vs] (arg 0) (.list [.list (gs.map encPerm), natList a,
        encPerm (1 : Perm (Fin n))]) _ := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
    have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
    have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
    have dgs := Det.get' a0 (Det.nat 0) (show [Val.list (gs.map encPerm), natList a,
      encPerm (1 : Perm (Fin n))][0]? = some (.list (gs.map encPerm)) from rfl)
    have da := Det.get' a0 (Det.nat 1) (show [Val.list (gs.map encPerm), natList a,
      encPerm (1 : Perm (Fin n))][1]? = some (.list (a.map Val.nat)) from rfl)
    have d1 := Det.get' a0 (Det.nat 2) (show [Val.list (gs.map encPerm), natList a,
      encPerm (1 : Perm (Fin n))][2]? = some (encPerm (1 : Perm (Fin n))) from rfl)
    have dg := Det.get' dgs a1 (show (gs.map encPerm)[i]? = some (encPerm gs[i]) by simp [hi])
    have dai := Det.get' da a1 (show (a.map Val.nat)[i]? = some (.nat a[i]) by simp [hia])
    have dp := Det.call (Det.mk4 (Det.nat 0) dg dai d1) (vsPPow_spec hpow gs[i] 1 a[i])
    rw [mul_one] at dp
    have dc := Det.call (Det.mk2 a2 dp) (compose_spec hcomp _ _)
    rw [← vsPW_take_succ gs a i hi hia] at dc
    refine FunAll.intro hst ((dc.post fun c' hc' => ⟨rfl, ?_⟩))
    have wgs : (Val.list (gs.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := by
      have h1 := vs_wt_list_le_of (gs.map encPerm) (c := 4 * (N + 1) ^ 2) (by
        intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.mp hv
        exact (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
      rw [List.length_map] at h1
      have : gs.length * (2 * (4 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (9 * (N + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
      have e : (N + 1) * (9 * (N + 1) ^ 2) = 9 * (N + 1) ^ 3 := by ring
      have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have wa : (natList a).wt ≤ 5 * (N + 1) ^ 2 := wt_natList_le_sq ha (by omega)
    have w1 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (N + 1) ^ 2 :=
      (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
      (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have wacc := hp2 (vsPW (gs.take i) (a.take i))
    have wg := hp2 gs[i]
    have wgp := hp2 (gs[i] ^ a[i])
    have wnew := hp2 (vsPW (gs.take (i + 1)) (a.take (i + 1)))
    have wc := wt_list3_le (.list (gs.map encPerm)) (natList a) (encPerm (1 : Perm (Fin n)))
    have wvs := wt_list3_le c (.nat i) (encPerm (vsPW (gs.take i) (a.take i)))
    have ec : c.wt = (Val.list [.list (gs.map encPerm), natList a, encPerm (1 : Perm (Fin n))]).wt :=
      rfl
    have ea : (natList a).wt = (Val.list (a.map Val.nat)).wt := rfl
    have wi := wt_nat_le i
    have hai : a[i] ≤ N := ha _ (List.getElem_mem _)
    have wai := wt_nat_le a[i]
    have w4 := wt_list4_le (.nat 0) (encPerm gs[i]) (.nat a[i]) (encPerm (1 : Perm (Fin n)))
    have w2 := wt_list2_le (encPerm (vsPW (gs.take i) (a.take i))) (encPerm (gs[i] ^ a[i]))
    have hpc := vsPPowCost_le (n := n) (e := a[i]) (k := N) (by have := vsP_bits_le a[i]; omega)
    have hn3 : (n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hpc' : 10 ^ 6 * (N + 1) ^ 2 * (n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 5 := by
      calc 10 ^ 6 * (N + 1) ^ 2 * (n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 2 * (N + 1) ^ 3 :=
            Nat.mul_le_mul_left _ hn3
        _ = 10 ^ 6 * (N + 1) ^ 5 := by ring
    have hpk : permK * (n + 1) ^ 3 ≤ 30000 * (N + 1) ^ 3 := by
      rw [show permK = 30000 from rfl]; omega
    have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have w0 : (Val.nat 0).wt = 2 := rfl
    have ev : (Val.list vs).wt =
        (Val.list [c, Val.nat i, encPerm (vsPW (List.take i gs) (List.take i a))]).wt := rfl
    omega
  have hit' := iter_spec hit (c := c) (k := gs.length) (acc0 := encPerm (1 : Perm (Fin n)))
    (Inv := fun i acc => acc = encPerm (vsPW (gs.take i) (a.take i))) (M := 4 * (N + 1) ^ 2)
    (B := fun _ => 10 ^ 7 * (N + 1) ^ 5) (by simp [vsPW]) hM hstep
  refine FunAll.mono hit' fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, List.take_length, List.take_of_length_le (by omega)]
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have h1 : gs.length * (10 ^ 7 * (N + 1) ^ 5) ≤ (N + 1) * (10 ^ 7 * (N + 1) ^ 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have wgs : (Val.list (gs.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := by
      have h1 := vs_wt_list_le_of (gs.map encPerm) (c := 4 * (N + 1) ^ 2) (by
        intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.mp hv
        exact (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
      rw [List.length_map] at h1
      have : gs.length * (2 * (4 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (9 * (N + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
      have e : (N + 1) * (9 * (N + 1) ^ 2) = 9 * (N + 1) ^ 3 := by ring
      have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have wa : (natList a).wt ≤ 5 * (N + 1) ^ 2 := wt_natList_le_sq ha (by omega)
    have w1 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (N + 1) ^ 2 :=
      (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have wc := wt_list3_le (.list (gs.map encPerm)) (natList a) (encPerm (1 : Perm (Fin n)))
    have ec : c.wt = (Val.list [.list (gs.map encPerm), natList a, encPerm (1 : Perm (Fin n))]).wt :=
      rfl
    have w3 := wt_list3_le c (.nat gs.length) (encPerm (1 : Perm (Fin n)))
    have wk := wt_nat_le gs.length
    have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have hl2 : loopModK * (gs.length + 1) * ((Val.list [c, .nat gs.length,
        encPerm (1 : Perm (Fin n))]).wt + gs.length + 4 * (N + 1) ^ 2 + 1) ≤
        10 ^ 6 * (N + 1) * (N + 1) ^ 4 := by
      have h2 : (Val.list [c, .nat gs.length, encPerm (1 : Perm (Fin n))]).wt + gs.length +
          4 * (N + 1) ^ 2 + 1 ≤ 1000 * (N + 1) ^ 4 := by omega
      calc loopModK * (gs.length + 1) * _ ≤ 1000 * (N + 1) * (1000 * (N + 1) ^ 4) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega)) h2
        _ = 10 ^ 6 * (N + 1) * (N + 1) ^ 4 := by ring
    unfold vsPWordCost
    omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The context of the radical search: `[ctx, gs, 1, k]`. -/
def vsPRc (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (hs gs : List (Perm (Fin I.n))) : Val :=
  .list [vsPCtx I ws' cs rows hs, .list (gs.map encPerm), encPerm (1 : Perm (Fin I.n)),
    .nat gs.length]

/-- On `[rc, a]`: `1` if the word `∏ g_i ^ a_i` is not in `L`. -/
def vsPRadPredE (word nt : ℕ) : Expr :=
  .call nt (mk2 (.get (arg 0) (.nat 0))
    (.call word (mk3 (mk3 (.get (arg 0) (.nat 1)) (arg 1) (.get (arg 0) (.nat 2)))
      (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 2)))))

/-- The cost of the test. -/
def vsPRadPredCost (Cφ N W : ℕ) : ℕ :=
  vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2 + vsPWordCost 0 N + 1000 * W +
    1000 * (N + 1) ^ 2

set_option maxHeartbeats 4000000 in
theorem vsPRadPred_spec {P : Program} {f word comp pow nt inl phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPRadPredE word nt))
    (hword : P.HasAt word (vsPWordFuns word comp pow)) (hcomp : P.HasAt comp (composeFuns comp))
    (hpow : P.HasAt pow (vsPPowFuns pow)) (hnt : P.funs[nt]? = some (vsPNotInE inl))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) (hgs : ∀ g ∈ gs, g ∈ gens I.gs) (hgl : gs.length ≤ N)
    (hrc : (vsPRc I ws' cs rows hs gs).wt ≤ W) {a : List ℕ} (hal : a.length = gs.length)
    (ha : ∀ x ∈ a, x ≤ N) :
    FunDet P f (.list [vsPRc I ws' cs rows hs gs, natList a])
      (boolVal (vsPQN (vsPInLB I ws' cs rows) (encPerm (vsPW gs a)))) (vsPRadPredCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set rcv := [C, .list (gs.map encPerm), encPerm (1 : Perm (Fin I.n)), .nat gs.length] with hrcv
  set A := Val.list [vsPRc I ws' cs rows hs gs, natList a]
  have a0 : Det P [A] (arg 0) (.list rcv) _ :=
    Det.arg' (P := P) (vs := [vsPRc I ws' cs rows hs gs, natList a]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [vsPRc I ws' cs rows hs gs, natList a]) (rest := []) (j := 1) rfl
  have d0 := Det.get' a0 (Det.nat 0) (show rcv[0]? = some C from rfl)
  have d1 := Det.get' a0 (Det.nat 1) (show rcv[1]? = some (.list (gs.map encPerm)) from rfl)
  have d2 := Det.get' a0 (Det.nat 2) (show rcv[2]? = some (encPerm (1 : Perm (Fin I.n))) from rfl)
  have d3 := Det.get' a0 (Det.nat 3) (show rcv[3]? = some (.nat gs.length) from rfl)
  have dw := Det.call (Det.mk3 (Det.mk3 d1 a1 d2) d3 d2)
    (vsPWord_spec hword hcomp hpow H.n hal hgl ha)
  have hwg : vsPW gs a ∈ gens I.gs := vsPW_mem hgs a
  have dn := Det.call (Det.mk2 d0 dw) (vsPNotIn_spec hnt hinl hphi H hwg)
  refine FunDet.intro hf (dn.mono ?_)
  have hn := H.n
  have erc : (vsPRc I ws' cs rows hs gs).wt = (Val.list rcv).wt := rfl
  have wC : C.wt ≤ W := by
    have := wt_le_wt_list (show C ∈ rcv by simp [hrcv]); omega
  have wgs : (Val.list (gs.map encPerm)).wt ≤ W := by
    have := wt_le_wt_list (show Val.list (gs.map encPerm) ∈ rcv by simp [hrcv]); omega
  have w1 : (encPerm (1 : Perm (Fin I.n))).wt ≤ W := by
    have := wt_le_wt_list (show encPerm (1 : Perm (Fin I.n)) ∈ rcv by simp [hrcv]); omega
  have wk : (Val.nat gs.length).wt ≤ W := by
    have := wt_le_wt_list (show Val.nat gs.length ∈ rcv by simp [hrcv]); omega
  have wa : (natList a).wt ≤ 5 * (N + 1) ^ 2 := wt_natList_le_sq ha (by omega)
  have ww := wt_encPerm_le (vsPW gs a)
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wA := wt_list2_le (vsPRc I ws' cs rows hs gs) (natList a)
  have eA : A.wt = (Val.list [vsPRc I ws' cs rows hs gs, natList a]).wt := rfl
  have w3 := wt_list3_le (.list (gs.map encPerm)) (natList a) (encPerm (1 : Perm (Fin I.n)))
  have w3' := wt_list3_le (.list [.list (gs.map encPerm), natList a, encPerm (1 : Perm (Fin I.n))])
    (.nat gs.length) (encPerm (1 : Perm (Fin I.n)))
  have w2 := wt_list2_le C (encPerm (vsPW gs a))
  have wb := wt_boolVal_le (vsPQN (vsPInLB I ws' cs rows) (encPerm (vsPW gs a)))
  have ewc : vsPWordCost I.n N = vsPWordCost 0 N := rfl
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold vsPRadPredCost
  omega

end GI.Impl
