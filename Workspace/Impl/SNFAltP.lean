module

public import Workspace.Impl.SNFEnv
public import Workspace.Proved.SNFSize

@[expose] public section

/-!
# One alternation step as a program (Smith form)

The program of the Smith form is `hnfFuns` (the Hermite program, main function `151`) followed by
the functions of the Smith form. This file fixes the first of them:

* `152`–`167`: a table (`hnfTabFuns 152 168`), cell `168` the transpose cell;
* `169`–`184`: a table (`hnfTabFuns 169 185`), cell `185` the block cell `snfEmbCellF`;
* `186`–`217`: the dense product `linDenseMulFuns 186`;
* `221`: one alternation step `snfAltE`.

On `[[n], i, [H, P, Q]]`, `snfAltE` computes `Hᵀ`, the Hermite program on it gives `[U, H']`,
then `U Qᵀ` and `Pᵀ`; the output is `[H', U Qᵀ, Pᵀ]`, which is `snfStep` (`snfAlt_spec`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-- The value of a state. -/
def snfStVal {n : ℕ} (s : SnfSt n) : Val := .list [encIntMatrix s.H, encIntMatrix s.P, encIntMatrix s.Q]

/-- The envelope `K (w + 2)^D`. -/
def snfF (K D w : ℕ) : ℕ := K * (w + 2) ^ D

theorem snfF_mono {K D w w' : ℕ} (h : w ≤ w') : snfF K D w ≤ snfF K D w' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)

theorem snfF_ge {K D w : ℕ} (hK : 1 ≤ K) (hD : 1 ≤ D) : w ≤ snfF K D w := by
  unfold snfF
  have h : w + 2 ≤ (w + 2) ^ D := Nat.le_self_pow (by omega) _
  nlinarith

/-- `n`, the first entry of the context `[n]`. -/
def snfNE : Expr := .get (arg 0) (.nat 0)

/-- One alternation step. -/
def snfAltE : Expr :=
  .letE (.call 152 (mk3 (mk1 (.get (arg 2) (.nat 0))) snfNE snfNE))
  (.letE (.call 151 (mk3 snfNE snfNE (.var 1)))
  (.letE (.call 152 (mk3 (mk1 (.get (arg 2) (.nat 2))) snfNE snfNE))
  (.letE (.call 186 (mk2 (mk2 snfNE (.var 3)) (.get (.var 2) (.nat 0))))
  (.letE (.call 152 (mk3 (mk1 (.get (arg 2) (.nat 1))) snfNE snfNE))
    (mk3 (.get (.var 2) (.nat 1)) (.var 4) (.var 5))))))

/-- Where the alternation step and its pieces are. -/
structure snfAltAt (P : Program) : Prop where
  hnf : hnfMainAt P
  tt : hnfTabAt P 152 168
  tcell : P.funs[168]? = some snfTrCellF
  mul : linDenseMulAt P 186
  alt : P.funs[221]? = some snfAltE

/-- The cost of one alternation step, in terms of `Z = 10 Y + 100`. -/
def snfAltCostZ (K D Z : ℕ) : ℕ :=
  100 * (snfF K D Z + snfF K D (2 * snfF K D Z + Z) +
    snfF K D (4 * (snfF K D Z + snfF K D (2 * snfF K D Z + Z) + Z)) + Z)

/-- The cost of one alternation step. -/
def snfAltCost (K D Y : ℕ) : ℕ := snfAltCostZ K D (10 * Y + 100)

theorem snfAltCost_mono {K D Y Y' : ℕ} (h : Y ≤ Y') : snfAltCost K D Y ≤ snfAltCost K D Y' := by
  unfold snfAltCost snfAltCostZ
  have h1 : snfF K D (10 * Y + 100) ≤ snfF K D (10 * Y' + 100) := snfF_mono (by omega)
  have h2 : snfF K D (2 * snfF K D (10 * Y + 100) + (10 * Y + 100)) ≤
      snfF K D (2 * snfF K D (10 * Y' + 100) + (10 * Y' + 100)) := snfF_mono (by omega)
  have h3 := snfF_mono (K := K) (D := D) (show 4 * (snfF K D (10 * Y + 100) +
      snfF K D (2 * snfF K D (10 * Y + 100) + (10 * Y + 100)) + (10 * Y + 100)) ≤
    4 * (snfF K D (10 * Y' + 100) + snfF K D (2 * snfF K D (10 * Y' + 100) + (10 * Y' + 100)) +
      (10 * Y' + 100)) by omega)
  omega

/-- The full-rank instance of a nonsingular square matrix. -/
def snfInst {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0) : FullRankInst :=
  ⟨n, n, hn, le_rfl, M, snf_inj_of_det hM⟩

set_option maxHeartbeats 8000000 in
/-- **One alternation step.** -/
theorem snfAlt_spec {P : Program} (h : snfAltAt P) {K D : ℕ} (hE : SnfEnv K D) {n : ℕ}
    (hn : 0 < n) (s : SnfSt n) (hdet : s.H.det ≠ 0) (i : ℕ) {Y : ℕ}
    (hY : (snfStVal s).wt ≤ Y) (hnY : n ≤ Y) (hiY : i ≤ Y) :
    FunDet P 221 (.list [.list [.nat n], .nat i, snfStVal s]) (snfStVal (snfStep s))
      (snfAltCost K D Y) := by
  set Z := 10 * Y + 100 with hZ
  set vs : List Val := [.list [.nat n], .nat i, snfStVal s] with hvs
  have wn := wt_nat_le n
  have wi := wt_nat_le i
  have wn1 := wt_list_le [Val.nat n]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wn1
  have wa : (Val.list vs).wt ≤ 8 * Y + 40 := by
    have := wt_list3_le (.list [.nat n]) (.nat i) (snfStVal s)
    rw [← hvs] at this; omega
  have wsv : (snfStVal s).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have wH : (encIntMatrix s.H).wt < (snfStVal s).wt := wt_le_wt_list (by simp [snfStVal])
  have wP : (encIntMatrix s.P).wt < (snfStVal s).wt := wt_le_wt_list (by simp [snfStVal])
  have wQ : (encIntMatrix s.Q).wt < (snfStVal s).wt := wt_le_wt_list (by simp [snfStVal])
  -- reading `n` and the parts of the state
  have dn : ∀ rest : List Val, Det P (Val.list vs :: rest) snfNE (.nat n) (3 * (Val.list vs).wt + 20) := by
    intro rest
    have d := Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n][0]? = some (.nat n) from rfl)
    refine d.mono ?_
    have : (Val.list [Val.nat n]).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
    have : (Val.nat n).wt < (Val.list [Val.nat n]).wt := wt_le_wt_list (by simp)
    omega
  have dc : ∀ (rest : List Val) (k : ℕ) (v : Val), k ≤ 2 →
      [encIntMatrix s.H, encIntMatrix s.P, encIntMatrix s.Q][k]? = some v →
      Det P (Val.list vs :: rest) (.get (arg 2) (.nat k)) v (3 * (Val.list vs).wt + 20) := by
    intro rest k v hk hv
    have d := Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 2) rfl) (Det.nat k) hv
    refine d.mono ?_
    have : v.wt < (snfStVal s).wt := wt_le_wt_list (List.mem_of_getElem? hv)
    omega
  -- a transpose call
  have htr : ∀ (rest : List Val) (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ), k ≤ 2 →
      [encIntMatrix s.H, encIntMatrix s.P, encIntMatrix s.Q][k]? = some (encIntMatrix M) →
      Det P (Val.list vs :: rest) (.call 152 (mk3 (mk1 (.get (arg 2) (.nat k))) snfNE snfNE))
        (encIntMatrix M.transpose) (20 * Z + snfF K D Z + (encIntMatrix M.transpose).wt) := by
    intro rest M k hk hv
    have wM : (encIntMatrix M).wt < (snfStVal s).wt := wt_le_wt_list (List.mem_of_getElem? hv)
    have d1 := Det.mk3 (Det.mk1 (dc rest k _ hk hv)) (dn rest) (dn rest)
    have w1 := wt_list_le [encIntMatrix M]
    have w2 := wt_list3_le (.list [encIntMatrix M]) (.nat n) (.nat n)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w1
    have hX : (Val.list [.list [encIntMatrix M], .nat n, .nat n]).wt ≤ Z := by omega
    have st := (snfTrTab_spec h.tt h.tcell M hX (by omega)).mono (hE.tr Z)
    refine (Det.call d1 st).mono ?_
    unfold snfF
    omega
  -- step 1: `Hᵀ`
  have d1 := htr [] s.H 0 (by omega) rfl
  set v1 := encIntMatrix s.H.transpose with hv1
  have wv1 : v1.wt < snfF K D Z := by
    have hX : (Val.list [.list [encIntMatrix s.H], .nat n, .nat n]).wt ≤ Z := by
      have w1 := wt_list_le [encIntMatrix s.H]
      have w2 := wt_list3_le (.list [encIntMatrix s.H]) (.nat n) (.nat n)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at w1
      omega
    exact ((snfTrTab_spec h.tt h.tcell s.H hX (by omega)).mono (hE.tr Z)).wt_lt
  -- step 2: the Hermite form of `Hᵀ`
  have hdetT : s.H.transpose.det ≠ 0 := by rwa [Matrix.det_transpose]
  set I := snfInst hn s.H.transpose hdetT with hI
  have eI : fullRankInput I = .list [.nat n, .nat n, v1] := rfl
  have wI : (fullRankInput I).wt ≤ 2 * snfF K D Z + Z := by
    rw [eI]; have := wt_list3_le (.nat n) (.nat n) v1; omega
  have sh := (hnfMain_spec h.hnf I).mono ((hE.hnf _).trans (snfF_mono wI))
  set Z2 := 2 * snfF K D Z + Z with hZ2
  set v2 := Val.list [encIntMatrix (snfU s.H.transpose), encIntMatrix (snfH s.H.transpose)] with hv2
  have sh' : FunDet P 151 (.list [.nat n, .nat n, v1]) v2 (snfF K D Z2) := sh
  have d2 := Det.call (Det.mk3 (dn [v1]) (dn [v1]) (Det.var' (P := P) (env := [Val.list vs, v1]) (i := 1) rfl))
    sh'
  have wv2 : v2.wt < snfF K D Z2 := sh'.wt_lt
  -- step 3: `Qᵀ`
  have d3 := htr [v1, v2] s.Q 2 (by omega) rfl
  set v3 := encIntMatrix s.Q.transpose with hv3
  have wv3 : v3.wt < snfF K D Z := by
    have hX : (Val.list [.list [encIntMatrix s.Q], .nat n, .nat n]).wt ≤ Z := by
      have w1 := wt_list_le [encIntMatrix s.Q]
      have w2 := wt_list3_le (.list [encIntMatrix s.Q]) (.nat n) (.nat n)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at w1
      omega
    exact ((snfTrTab_spec h.tt h.tcell s.Q hX (by omega)).mono (hE.tr Z)).wt_lt
  -- step 4: `U Qᵀ`
  have wU : (encIntMatrix (snfU s.H.transpose)).wt < v2.wt := wt_le_wt_list (by simp [hv2])
  have wH' : (encIntMatrix (snfH s.H.transpose)).wt < v2.wt := wt_le_wt_list (by simp [hv2])
  set Z3 := 4 * (snfF K D Z + snfF K D Z2 + Z) with hZ3
  have wm : (Val.list [.list [.nat n, v3], encIntMatrix (snfU s.H.transpose)]).wt ≤ Z3 := by
    have := wt_list2_le (.nat n) v3
    have := wt_list2_le (.list [.nat n, v3]) (encIntMatrix (snfU s.H.transpose))
    omega
  have hnv3 : n < v3.wt := hnf_rows_lt_wt s.Q.transpose
  have hv3a : v3.wt < (Val.list [.nat n, v3]).wt := wt_le_wt_list (by simp)
  have hv3b : (Val.list [.nat n, v3]).wt <
      (Val.list [.list [.nat n, v3], encIntMatrix (snfU s.H.transpose)]).wt := wt_le_wt_list (by simp)
  have hmw : n ≤ (Val.list [.list [.nat n, v3], encIntMatrix (snfU s.H.transpose)]).wt := by omega
  have sm := (linDenseMul_spec h.mul (snfU s.H.transpose) s.Q.transpose).mono
    ((hE.mul n _ hmw).trans (snfF_mono wm))
  have dv2 : Det P [Val.list vs, v1, v2, v3] (.var 2) v2 (v2.wt + 1) := Det.var' rfl
  have d4 := Det.call (Det.mk2 (Det.mk2 (dn [v1, v2, v3]) (Det.var' (P := P) (env := [Val.list vs, v1, v2, v3])
    (i := 3) rfl)) (Det.get' dv2 (Det.nat 0) rfl)) sm
  set v4 := encIntMatrix (snfU s.H.transpose * s.Q.transpose) with hv4
  have wv4 : v4.wt < snfF K D Z3 := sm.wt_lt
  -- step 5: `Pᵀ`
  have d5 := htr [v1, v2, v3, v4] s.P 1 (by omega) rfl
  set v5 := encIntMatrix s.P.transpose with hv5
  have wv5 : v5.wt < snfF K D Z := by
    have hX : (Val.list [.list [encIntMatrix s.P], .nat n, .nat n]).wt ≤ Z := by
      have w1 := wt_list_le [encIntMatrix s.P]
      have w2 := wt_list3_le (.list [encIntMatrix s.P]) (.nat n) (.nat n)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at w1
      omega
    exact ((snfTrTab_spec h.tt h.tcell s.P hX (by omega)).mono (hE.tr Z)).wt_lt
  -- the output
  have dv2' : Det P [Val.list vs, v1, v2, v3, v4, v5] (.var 2) v2 (v2.wt + 1) := Det.var' rfl
  have d6 := Det.mk3 (Det.get' dv2' (Det.nat 1) rfl)
    (Det.var' (P := P) (env := [Val.list vs, v1, v2, v3, v4, v5]) (i := 4) rfl)
    (Det.var' (P := P) (env := [Val.list vs, v1, v2, v3, v4, v5]) (i := 5) rfl)
  have dall := Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 d6))))
  apply FunDet.intro h.alt
  refine dall.mono ?_
  have wout : (snfStVal (snfStep s)).wt ≤ 2 * (v2.wt + v4.wt + v5.wt) + 7 := by
    have := wt_list3_le (encIntMatrix (snfH s.H.transpose)) v4 v5
    show (Val.list [encIntMatrix (snfH s.H.transpose), v4, v5]).wt ≤ _
    omega
  have g1 := wt_list3_le (.nat n) (.nat n) v1
  have g2 := wt_list2_le (.nat n) v3
  have g3 := wt_list2_le (.list [.nat n, v3]) (encIntMatrix (snfU s.H.transpose))
  have g4 := wt_list3_le (encIntMatrix (snfH s.H.transpose)) v4 v5
  have f1 : Z ≤ snfF K D Z := snfF_ge hE.one_le hE.d_pos
  have f2 : Z2 ≤ snfF K D Z2 := snfF_ge hE.one_le hE.d_pos
  have f3 : Z3 ≤ snfF K D Z3 := snfF_ge hE.one_le hE.d_pos
  have e1 : snfAltCost K D Y = 100 * (snfF K D Z + snfF K D Z2 + snfF K D Z3 + Z) := by
    unfold snfAltCost; rw [← hZ]; unfold snfAltCostZ; rw [← hZ2, ← hZ3]
  rw [e1]
  have ea : (snfStVal (snfStep s)) = .list [encIntMatrix (snfH s.H.transpose), v4, v5] := rfl
  have eaw : (snfStVal (snfStep s)).wt =
      (Val.list [encIntMatrix (snfH s.H.transpose), v4, v5]).wt := rfl
  clear_value Z Z2 Z3 v1 v2 v3 v4 v5
  omega

end GI.Impl
