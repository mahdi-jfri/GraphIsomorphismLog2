module

public import Workspace.Impl.SNFCoef

@[expose] public section

/-!
# One pair step as a program (Smith form)

Function `225` takes `[[n], k, [H, P, Q]]`. With `p = k / n` and `q = k % n`, if `p < q` it reads
`H p p` and `H q q`, gets the two block contexts from function `226`, builds `L` and `R` with the
block table at `169`, and returns `[L H R, L P, Q R]`. Otherwise it returns the state. This is
`snfFixK` (`snfPairStep_spec`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-- One pair step. -/
def snfPairE : Expr :=
  .letE (.arith .div (arg 1) snfNE)
  (.letE (.arith .mod (arg 1) snfNE)
  (.ite (.arith .lt (.var 1) (.var 2))
    (.letE (.get (arg 2) (.nat 0))
    (.letE (.call 226 (mk4 (.get (.get (.var 3) (.var 1)) (.var 1))
      (.get (.get (.var 3) (.var 2)) (.var 2)) (.var 1) (.var 2)))
    (.letE (.call 169 (mk3 (.get (.var 4) (.nat 0)) snfNE snfNE))
    (.letE (.call 169 (mk3 (.get (.var 4) (.nat 1)) snfNE snfNE))
    (.letE (.call 186 (mk2 (mk2 snfNE (.var 3)) (.var 5)))
      (mk3 (.call 186 (mk2 (mk2 snfNE (.var 6)) (.var 7)))
        (.call 186 (mk2 (mk2 snfNE (.get (arg 2) (.nat 1))) (.var 5)))
        (.call 186 (mk2 (mk2 snfNE (.var 6)) (.get (arg 2) (.nat 2))))))))))
    (arg 2)))

/-- Where the pair step and its pieces are. -/
structure snfPairAt (P : Program) : Prop where
  hnf : hnfMainAt P
  et : hnfTabAt P 169 185
  ecell : P.funs[185]? = some snfEmbCellF
  mul : linDenseMulAt P 186
  coef : P.funs[226]? = some snfCoefE
  pair : P.funs[225]? = some snfPairE

/-- The cost of one pair step. -/
def snfPairCost (K D Y : ℕ) : ℕ := 100000 * snfG K D 7 (10 * Y + 100)

theorem snfPairCost_mono {K D Y Y' : ℕ} (h : Y ≤ Y') : snfPairCost K D Y ≤ snfPairCost K D Y' := by
  unfold snfPairCost; have := snfG_mono (K := K) (D := D) 7 (show 10 * Y + 100 ≤ 10 * Y' + 100 by omega)
  omega

theorem snfFixK_pos {n : ℕ} {s : SnfSt n} {k : ℕ} (hk : k < n * n) (hlt : k / n < k % n) :
    snfFixK s k = ⟨snfL s.H ⟨k / n, Nat.div_lt_of_lt_mul hk⟩ ⟨k % n, Nat.mod_lt _ (snf_pos_of_lt hk)⟩ *
      s.H * snfR s.H ⟨k / n, Nat.div_lt_of_lt_mul hk⟩ ⟨k % n, Nat.mod_lt _ (snf_pos_of_lt hk)⟩,
      snfL s.H ⟨k / n, Nat.div_lt_of_lt_mul hk⟩ ⟨k % n, Nat.mod_lt _ (snf_pos_of_lt hk)⟩ * s.P,
      s.Q * snfR s.H ⟨k / n, Nat.div_lt_of_lt_mul hk⟩ ⟨k % n, Nat.mod_lt _ (snf_pos_of_lt hk)⟩⟩ := by
  rw [snfFixK, dif_pos hk, snfPair, if_pos (show (⟨k / n, _⟩ : Fin n) < ⟨k % n, _⟩ from hlt)]

theorem snfFixK_neg {n : ℕ} {s : SnfSt n} {k : ℕ} (hk : k < n * n) (hlt : ¬ k / n < k % n) :
    snfFixK s k = s := by
  rw [snfFixK, dif_pos hk, snfPair, if_neg (show ¬ (⟨k / n, _⟩ : Fin n) < ⟨k % n, _⟩ from hlt)]

set_option maxHeartbeats 16000000 in
/-- **One pair step.** -/
theorem snfPairStep_spec {P : Program} (h : snfPairAt P) {K D : ℕ} (hE : SnfEnv K D) {n : ℕ}
    (s : SnfSt n) (hpos : ∀ l, 0 < s.H l l) {k : ℕ} (hk : k < n * n) {Y : ℕ}
    (hY : (snfStVal s).wt ≤ Y) (hnY : n ≤ Y) (hkY : k ≤ Y) :
    FunDet P 225 (.list [.list [.nat n], .nat k, snfStVal s]) (snfStVal (snfFixK s k))
      (snfPairCost K D Y) := by
  set vs : List Val := [.list [.nat n], .nat k, snfStVal s] with hvs
  set Z := 10 * Y + 100 with hZ
  set G4 := snfG K D 4 Z with hG4
  set G5 := snfG K D 5 Z with hG5
  set G6 := snfG K D 6 Z with hG6
  set G7 := snfG K D 7 Z with hG7
  have s4 : 1000000 * G4 + 1000000 ≤ G5 := snfG_succB hE 4 Z
  have s5 : 1000000 * G5 + 1000000 ≤ G6 := snfG_succB hE 5 Z
  have s6 : 1000000 * G6 + 1000000 ≤ G7 := snfG_succB hE 6 Z
  have s0 : Z ≤ G4 := snfG_le hE (Nat.zero_le 4) Z
  have wn := wt_nat_le n
  have wk := wt_nat_le k
  have wn1 := wt_list_le [Val.nat n]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wn1
  have wa : (Val.list vs).wt ≤ 8 * Y + 40 := by
    have := wt_list3_le (.list [.nat n]) (.nat k) (snfStVal s)
    rw [← hvs] at this; omega
  have wsv : (snfStVal s).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have wH : (encIntMatrix s.H).wt < (snfStVal s).wt := wt_le_wt_list (by simp [snfStVal])
  have wP : (encIntMatrix s.P).wt < (snfStVal s).wt := wt_le_wt_list (by simp [snfStVal])
  have wQ : (encIntMatrix s.Q).wt < (snfStVal s).wt := wt_le_wt_list (by simp [snfStVal])
  have dn : ∀ rest : List Val, Det P (Val.list vs :: rest) snfNE (.nat n) (3 * (Val.list vs).wt + 20) := by
    intro rest
    have d := Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n][0]? = some (.nat n) from rfl)
    refine d.mono ?_
    have : (Val.list [Val.nat n]).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
    have : (Val.nat n).wt < (Val.list [Val.nat n]).wt := wt_le_wt_list (by simp)
    omega
  have dst : ∀ (rest : List Val) (j : ℕ) (v : Val), j ≤ 2 →
      [encIntMatrix s.H, encIntMatrix s.P, encIntMatrix s.Q][j]? = some v →
      Det P (Val.list vs :: rest) (.get (arg 2) (.nat j)) v (3 * (Val.list vs).wt + 20) := by
    intro rest j v hj hv
    have d := Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 2) rfl) (Det.nat j) hv
    refine d.mono ?_
    have : v.wt < (snfStVal s).wt := wt_le_wt_list (List.mem_of_getElem? hv)
    omega
  -- `p` and `q`
  have dk : Det P [Val.list vs] (arg 1) (.nat k) (2 * (Val.list vs).wt + 6) := Det.arg' rfl
  have d1 := Det.arith' (op := .div) dk (dn []) rfl
  have dk' : Det P [Val.list vs, .nat (k / n)] (arg 1) (.nat k) (2 * (Val.list vs).wt + 6) :=
    Det.arg' rfl
  have d2 := Det.arith' (op := .mod) dk' (dn [.nat (k / n)]) rfl
  have hkn : k / n ≤ k := Nat.div_le_self k n
  have hpn : k / n < n := Nat.div_lt_of_lt_mul hk
  have hqn : k % n < n := Nat.mod_lt _ (snf_pos_of_lt hk)
  set e2 : List Val := [Val.list vs, .nat (k / n), .nat (k % n)] with he2
  have dp : Det P e2 (.var 1) (.nat (k / n)) ((Val.nat (k / n)).wt + 1) := Det.var' rfl
  have dq : Det P e2 (.var 2) (.nat (k % n)) ((Val.nat (k % n)).wt + 1) := Det.var' rfl
  have wpn := wt_nat_le (k / n)
  have wqn := wt_nat_le (k % n)
  -- the branch that changes the state
  have dthen : k / n < k % n → Det P e2
      (.letE (.get (arg 2) (.nat 0))
      (.letE (.call 226 (mk4 (.get (.get (.var 3) (.var 1)) (.var 1))
        (.get (.get (.var 3) (.var 2)) (.var 2)) (.var 1) (.var 2)))
      (.letE (.call 169 (mk3 (.get (.var 4) (.nat 0)) snfNE snfNE))
      (.letE (.call 169 (mk3 (.get (.var 4) (.nat 1)) snfNE snfNE))
      (.letE (.call 186 (mk2 (mk2 snfNE (.var 3)) (.var 5)))
        (mk3 (.call 186 (mk2 (mk2 snfNE (.var 6)) (.var 7)))
          (.call 186 (mk2 (mk2 snfNE (.get (arg 2) (.nat 1))) (.var 5)))
          (.call 186 (mk2 (mk2 snfNE (.var 6)) (.get (arg 2) (.nat 2))))))))))
      (snfStVal (snfFixK s k)) (5000 * G7) := by
    intro hlt
    set p : Fin n := ⟨k / n, hpn⟩ with hp
    set q : Fin n := ⟨k % n, hqn⟩ with hq
    rw [snfFixK_pos hk hlt]
    set a := s.H p p with ha
    set b := s.H q q with hb
    have ha0 : a ≠ 0 := (hpos p).ne'
    -- `H`
    have d3 := dst [.nat (k / n), .nat (k % n)] 0 _ (by omega) rfl
    set e3 := e2 ++ [encIntMatrix s.H] with he3
    have dH : Det P e3 (.var 3) (encIntMatrix s.H) ((encIntMatrix s.H).wt + 1) := Det.var' rfl
    have dp3 : Det P e3 (.var 1) (.nat (k / n)) ((Val.nat (k / n)).wt + 1) := Det.var' rfl
    have dq3 : Det P e3 (.var 2) (.nat (k % n)) ((Val.nat (k % n)).wt + 1) := Det.var' rfl
    have da := Det.get' (Det.get' dH dp3 (hnf_mat_get s.H p)) dp3 (hnf_vec_get (s.H p) p)
    have db := Det.get' (Det.get' dH dq3 (hnf_mat_get s.H q)) dq3 (hnf_vec_get (s.H q) q)
    have wrp := hnf_row_wt_lt s.H p
    have wrq := hnf_row_wt_lt s.H q
    have wea : (encInt a).wt < (linVecVal (s.H p)).wt := linVecEntryWt (s.H p) p
    have web : (encInt b).wt < (linVecVal (s.H q)).wt := linVecEntryWt (s.H q) q
    have erp : (Val.list ((List.finRange n).map fun j => encInt (s.H p j))).wt =
      (linVecVal (s.H p)).wt := rfl
    have erq : (Val.list ((List.finRange n).map fun j => encInt (s.H q j))).wt =
      (linVecVal (s.H q)).wt := rfl
    -- the coefficients
    set cv := [encInt a, encInt b, Val.nat (k / n), Val.nat (k % n)] with hcv
    have wcv : (Val.list cv).wt ≤ Z := by
      have := wt_list_le cv
      simp only [hcv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this ⊢
      omega
    have sc := (snfCoef_spec h.hnf h.coef hE a b ha0 (k / n) (k % n)).mono
      (show 1000 * snfG K D 4 (Val.list cv).wt ≤ 1000 * G4 from
        Nat.mul_le_mul_left _ (snfG_mono 4 wcv))
    have d4 := Det.call (Det.mk4 da db dp3 dq3) sc
    set v4 := snfCoefVal a b (k / n) (k % n) with hv4
    have wv4 : v4.wt < 1000 * G4 := sc.wt_lt
    set e4 := e3 ++ [v4] with he4
    -- `L` and `R`
    set cL := snfEmbCtx (k / n) (k % n) (snfBx a b) (snfBy a b) (-(b / snfBg a b)) (a / snfBg a b)
      with hcL
    set cR := snfEmbCtx (k / n) (k % n) 1 (-(snfBy a b * (b / snfBg a b))) 1
      (snfBx a b * (a / snfBg a b)) with hcR
    have wcL : (Val.list cL).wt < v4.wt := wt_le_wt_list (by simp [hv4, snfCoefVal, hcL])
    have wcR : (Val.list cR).wt < v4.wt := wt_le_wt_list (by simp [hv4, snfCoefVal, hcR])
    have dv4 : ∀ env : List Val, env[4]? = some v4 → ∀ j (c : List Val), j ≤ 1 →
        [Val.list cL, Val.list cR][j]? = some (.list c) →
        Det P env (.get (.var 4) (.nat j)) (.list c) (v4.wt + (Val.list c).wt + 6) := by
      intro env hv j c hj hc
      have : (Val.list c).wt < (Val.list [Val.list cL, Val.list cR]).wt :=
        wt_le_wt_list (List.mem_of_getElem? hc)
      have e : (Val.list [Val.list cL, Val.list cR]).wt = v4.wt := rfl
      have e' : (Val.list
        [Val.list (snfEmbCtx (k / n) (k % n) (snfBx a b) (snfBy a b) (-(b / snfBg a b)) (a / snfBg a b)),
          Val.list (snfEmbCtx (k / n) (k % n) 1 (-(snfBy a b * (b / snfBg a b))) 1
            (snfBx a b * (a / snfBg a b)))]).wt = v4.wt := rfl
      exact (Det.get' (Det.var' (P := P) hv) (Det.nat j) hc).mono (by omega)
    have wtab : ∀ c : List Val, (Val.list c).wt < v4.wt →
        (Val.list [.list c, .nat n, .nat n]).wt ≤ 1000000 * G4 + 1000000 := by
      intro c hc; have := wt_list3_le (.list c) (.nat n) (.nat n); omega
    have tL := (snfEmbTab_spec (n := n) h.et h.ecell (k / n) (k % n) _ _ _ _ (wtab cL wcL)
      (by omega)).mono ((hE.emb _).trans (snfG_stepB (le_refl _)))
    have tR := (snfEmbTab_spec (n := n) h.et h.ecell (k / n) (k % n) _ _ _ _ (wtab cR wcR)
      (by omega)).mono ((hE.emb _).trans (snfG_stepB (le_refl _)))
    set L := snfL s.H p q with hL
    set R := snfR s.H p q with hR
    have tL' : FunDet P 169 (.list [.list cL, .nat n, .nat n]) (encIntMatrix L) G5 := tL
    have tR' : FunDet P 169 (.list [.list cR, .nat n, .nat n]) (encIntMatrix R) G5 := tR
    have wL : (encIntMatrix L).wt < G5 := tL'.wt_lt
    have wR : (encIntMatrix R).wt < G5 := tR'.wt_lt
    have d5 := Det.call (Det.mk3 (dv4 e4 rfl 0 cL (by omega) rfl) (dn _) (dn _)) tL'
    set e5 := e4 ++ [encIntMatrix L] with he5
    have d6 := Det.call (Det.mk3 (dv4 e5 rfl 1 cR (by omega) rfl) (dn _) (dn _)) tR'
    set e6 := e5 ++ [encIntMatrix R] with he6
    -- the products
    have hmul : ∀ (A B : _root_.Matrix (Fin n) (Fin n) ℤ) (j : ℕ),
        (encIntMatrix A).wt ≤ 1000 * snfG K D j Z → (encIntMatrix B).wt ≤ 1000 * snfG K D j Z →
        FunDet P 186 (.list [.list [.nat n, encIntMatrix B], encIntMatrix A]) (encIntMatrix (A * B))
          (snfG K D (j + 1) Z) := by
      intro A B j hA hB
      have w1 := wt_list2_le (.nat n) (encIntMatrix B)
      have w2 := wt_list2_le (.list [.nat n, encIntMatrix B]) (encIntMatrix A)
      have hnB := hnf_rows_lt_wt B
      have h1 : (encIntMatrix B).wt < (Val.list [.nat n, encIntMatrix B]).wt := wt_le_wt_list (by simp)
      have h2 : (Val.list [.nat n, encIntMatrix B]).wt <
        (Val.list [.list [.nat n, encIntMatrix B], encIntMatrix A]).wt := wt_le_wt_list (by simp)
      have h3 := wt_nat_le n
      exact (linDenseMul_spec h.mul A B).mono ((hE.mul n _ (by omega)).trans
        (snfG_stepB (by omega)))
    have g45 : G4 ≤ G5 := by omega
    have m7 := hmul L s.H 5 (by omega) (by omega)
    have wLH : (encIntMatrix (L * s.H)).wt < G6 := m7.wt_lt
    have dv : ∀ (env : List Val) (i : ℕ) (v : Val), env[i]? = some v → Det P env (.var i) v (v.wt + 1) :=
      fun env i v hv => Det.var' hv
    have d7 := Det.call (Det.mk2 (Det.mk2 (dn _) (dv e6 3 _ rfl)) (dv e6 5 _ rfl)) m7
    set e7 := e6 ++ [encIntMatrix (L * s.H)] with he7
    have m8 := hmul (L * s.H) R 6 (by omega) (by omega)
    have m9 := hmul L s.P 6 (by omega) (by omega)
    have m10 := hmul s.Q R 6 (by omega) (by omega)
    have w8 : (encIntMatrix (L * s.H * R)).wt < G7 := m8.wt_lt
    have w9 : (encIntMatrix (L * s.P)).wt < G7 := m9.wt_lt
    have w10 : (encIntMatrix (s.Q * R)).wt < G7 := m10.wt_lt
    have d8 := Det.call (Det.mk2 (Det.mk2 (dn _) (dv e7 6 _ rfl)) (dv e7 7 _ rfl)) m8
    have d9 := Det.call (Det.mk2 (Det.mk2 (dn _) (dst _ 1 _ (by omega) rfl)) (dv e7 5 _ rfl)) m9
    have d10 := Det.call (Det.mk2 (Det.mk2 (dn _) (dv e7 6 _ rfl)) (dst _ 2 _ (by omega) rfl)) m10
    have dall := Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6 (Det.letE d7
      (Det.mk3 d8 d9 d10)))))
    refine dall.mono ?_
    have o1 := wt_list3_le (encIntMatrix (L * s.H * R)) (encIntMatrix (L * s.P))
      (encIntMatrix (s.Q * R))
    have o2 := wt_list_le [encInt a, encInt b, Val.nat (k / n), Val.nat (k % n)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at o2
    have o3 := wt_list3_le (.list cL) (.nat n) (.nat n)
    have o4 := wt_list3_le (.list cR) (.nat n) (.nat n)
    have o5 := wt_list2_le (.nat n) (encIntMatrix s.H)
    have o6 := wt_list2_le (.list [.nat n, encIntMatrix s.H]) (encIntMatrix L)
    have o7 := wt_list2_le (.nat n) (encIntMatrix R)
    have o8 := wt_list2_le (.list [.nat n, encIntMatrix R]) (encIntMatrix (L * s.H))
    have o9 := wt_list2_le (.nat n) (encIntMatrix s.P)
    have o10 := wt_list2_le (.list [.nat n, encIntMatrix s.P]) (encIntMatrix L)
    have o11 := wt_list2_le (.list [.nat n, encIntMatrix R]) (encIntMatrix s.Q)
    have ev : (snfStVal (⟨L * s.H * R, L * s.P, s.Q * R⟩ : SnfSt n)).wt =
      (Val.list [encIntMatrix (L * s.H * R), encIntMatrix (L * s.P), encIntMatrix (s.Q * R)]).wt := rfl
    have f1 : (encInt (s.H p p)).wt = (encInt a).wt := rfl
    have f2 : (encInt (s.H q q)).wt = (encInt b).wt := rfl
    have f3 : (Val.list [encInt (s.H p p), encInt (s.H q q), Val.nat (k / n), Val.nat (k % n)]).wt =
      (Val.list cv).wt := rfl
    have f4 : snfG K D (5 + 1) Z = G6 := rfl
    have f5 : snfG K D (6 + 1) Z = G7 := rfl
    clear_value G4 G5 G6 G7 v4 L R a b e3 e4 e5 e6 e7
    omega
  have delse : ¬ k / n < k % n → Det P e2 (arg 2) (snfStVal (snfFixK s k)) (2 * (Val.list vs).wt + 7) := by
    intro hlt
    rw [snfFixK_neg hk hlt]
    exact Det.arg' rfl
  have dite := hnf_det_ite_lt dp dq dthen delse
  have dall := Det.letE d1 (Det.letE d2 dite)
  apply FunDet.intro h.pair
  refine dall.mono ?_
  have wout : (snfStVal (snfFixK s k)).wt < 5000 * G7 + 2 * (Val.list vs).wt + 7 := by
    by_cases hlt : k / n < k % n
    · have := (dthen hlt).wt_lt; omega
    · have := (delse hlt).wt_lt; omega
  have ediv : GI.Machine.BinOp.div.eval k n = k / n := rfl
  have emod : GI.Machine.BinOp.mod.eval k n = k % n := rfl
  unfold snfPairCost
  rw [← hZ, ← hG7]
  clear_value G4 G5 G6 G7
  omega

end GI.Impl
