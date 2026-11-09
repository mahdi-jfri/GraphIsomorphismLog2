module

public import Workspace.Degree.GraphMain
public import Workspace.Degree.GraphReal

/-!
# The graph theorem

`graphFuns b fd j` is the graph program. `graphSolver` proves `GraphSolver graphFuns`: given
the string solver at `fd` (`StringSolver`) and `Membership` at `j`, function `b` returns a correct
answer on `inputVal G H` at a cost of `exp(C log(n + 2) log(d + 2))`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly GI.Statement Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The entry: decode the input, and answer `[1, 0]` (the empty isomorphism, no generators) if
`n = 0`. -/
def graphMainE (dec body : ℕ) : Expr :=
  .letE (.call dec (.var 0))
    (.ite (.get (.var 1) (.nat 0)) (.call body (.var 1)) (mk2 (.nat 1) (.nat 0)))

/-- **The graph program**, with its entry at `b`, the string solver at `fd` and `Membership` at
`j`. -/
def graphFuns (b fd j : ℕ) : List Expr :=
  [graphMainE (b + 3) (b + 1)] ++ [bodyE (b + 15) (b + 18) (b + 2) (b + 162) (b + 38) (b + 26) (b + 30)] ++
    [ctxE (b + 15)] ++ decodeFuns (b + 3) ++ rangeFuns (b + 15) ++ maxDegFuns (b + 18) ++
    tabFuns (b + 26) (arg 0) ++ outFuns (b + 30) ++ isoFuns (b + 38) fd j ++ autFuns (b + 162) fd j

/-- A bound on the weight of the input. -/
def IW (n : ℕ) : ℕ := (2 * n * n + 1) * (2 * (n + 1) + 5) + 4

theorem inputVal_wt (G H : SimpleGraph (Fin n)) : (inputVal G H).wt ≤ IW n := by
  have hcs : ∀ x ∈ inputCells G H, x ≤ n + 1 := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    exact inputLayout_le (inputMem_layout G H) a
  have := wt_natList_le _ hcs
  have hl : (inputCells G H).length = 2 * n * n + 1 := by simp [inputCells]
  rw [hl] at this
  exact this

/-- The budget of the program. -/
noncomputable def mainT (h : Membership) (S n : ℕ) : ℕ :=
  decodeK * (n + 1) ^ 2 * (IW n + (n + 1) ^ 2) + bodyC h S n + 100 * IW n + 1000 * WB n

/-- The bound of the program. -/
noncomputable def mainC (h : Membership) (S n : ℕ) : ℕ := 1000000 * mainT h S n

theorem answerOK_zero (G H : SimpleGraph (Fin 0)) : AnswerOK G H (.list [.nat 1, .nat 0]) := by
  let σ : G ≃g H := ⟨Equiv.refl _, fun {a} => a.elim0⟩
  have hgen : Subgroup.closure {g | g ∈ ([] : List (Perm (Fin 0)))} = autGroup G := by
    ext g
    have : g = 1 := Subsingleton.elim _ _
    subst this
    simp only [one_mem]
  have := answerOK_yes σ [] hgen
  simpa [yesCells, permCells, permsCells] using this

set_option maxHeartbeats 8000000 in
/-- **The program, with the cost `S` of the solver.** -/
theorem main_spec {P : Program} {b fd j S d : ℕ} (h : Membership) (hP : P.HasAt b (graphFuns b fd j))
    (hj : P.prims[j]? = some (membershipPrim h))
    (hSol : ∀ D, 6 ≤ D → D ≤ d + 6 → D ≤ n + 6 → SolverAt P fd D (n * D * (n * D)) S)
    (G H : SimpleGraph (Fin n)) (hdG : ∀ u, degL G u ≤ d) (hdH : ∀ u, degL H u ≤ d) :
    FunAll P b (inputVal G H) fun w cost => AnswerOK G H w ∧ cost ≤ mainC h S n := by
  classical
  have hM : P.funs[b]? = some (graphMainE (b + 3) (b + 1)) :=
    hP.left.left.left.left.left.left.left.left.left.single
  have hBd : P.funs[b + 1]? = some (bodyE (b + 15) (b + 18) (b + 2) (b + 162) (b + 38) (b + 26)
      (b + 30)) := hP.left.left.left.left.left.left.left.left.right.single
  have hCx : P.funs[b + 2]? = some (ctxE (b + 15)) := hP.left.left.left.left.left.left.left.right.single
  have hDec : P.HasAt (b + 3) (decodeFuns (b + 3)) := hP.left.left.left.left.left.left.right
  have hR : P.HasAt (b + 15) (rangeFuns (b + 15)) := hP.left.left.left.left.left.right
  have hDg : P.HasAt (b + 18) (maxDegFuns (b + 18)) := hP.left.left.left.left.right
  have hTb : P.HasAt (b + 26) (tabFuns (b + 26) (arg 0)) := hP.left.left.left.right
  have hO : P.HasAt (b + 30) (outFuns (b + 30)) := hP.left.left.right
  have hIs : P.HasAt (b + 38) (isoFuns (b + 38) fd j) := hP.left.right
  have hAu : P.HasAt (b + 162) (autFuns (b + 162) fd j) := hP.right
  have hB : BodyAt P (b + 15) (b + 18) (b + 2) (b + 162) (b + 38) (b + 26) (b + 30) fd j :=
    ⟨hR, hDg, hCx, hAu, hIs, hTb, hO⟩
  have h0 := WB_ge n
  have wv := inputVal_wt G H
  have wI := inVal_wt G H
  set T := mainT h S n with hT
  have hTI : 2 * IW n + 100 ≤ T := by simp only [hT, mainT]; omega
  have hTW : 1000 * WB n ≤ T := by simp only [hT, mainT]; omega
  have hTD : decodeK * (n + 1) ^ 2 * ((inputVal G H).wt + (n + 1) ^ 2) ≤ T := by
    have := Nat.mul_le_mul_left (decodeK * (n + 1) ^ 2) (show (inputVal G H).wt + (n + 1) ^ 2 ≤
      IW n + (n + 1) ^ 2 by omega)
    simp only [hT, mainT]
    omega
  have hTB : bodyC h S n ≤ T := by simp only [hT, mainT]; omega
  set R' : Val → Prop := fun w => AnswerOK G H w ∧ w.wt ≤ T with hR'
  have cDec := Lv.call (Lv.var (P := P) (T := T) (env := [inputVal G H]) (i := 0) (v := inputVal G H)
    rfl (by omega)) (decode_inputVal hDec G H) hTD
  refine FunAll.intro hM ((giLet_lv (R := R') (K := 1000000 * T) cDec ?_).mono
    fun w c hw => ⟨hw.1.1, by simp only [mainC]; exact hw.2⟩)
  have wDec := cDec.wt_lt
  set E := [inputVal G H, inVal G H] with hE
  have v1 : Lv P E T (.var 1) (inVal G H) 1 := Lv.var rfl (by omega)
  have c0 := Lv.get (vs := [.nat n, adjVal G, adjVal H]) v1 (Lv.nat 0 (by omega)) rfl
  have wc0 := c0.wt_lt
  refine (giIte_lv (R := R') (K := 999000 * T) c0 (fun hx => ?_) fun hx => ?_).mono
    fun w c hw => ⟨hw.1, by have := hw.1.2; omega⟩
  · have hn : 0 < n := Nat.pos_of_ne_zero hx
    have hbody := body_spec h hBd hB hj hSol hn G H hdG hdH
    refine (giCall_lv (R := R') (K := 998000 * T) v1 (hbody.wt_lt.mono fun w c hw =>
      ⟨⟨hw.1.1, by have := hw.1.2; have := hw.2; omega⟩, by have := hw.1.2; have := hw.2; omega⟩)).mono
      fun w c hw => ⟨hw.1, by have := hw.1.2; omega⟩
  · have l := Lv.mk2 (Lv.nat (P := P) (env := E) (T := T) 1 (by omega)) (Lv.nat 0 (by omega))
      (by omega)
    have wl := l.wt_lt
    have w2 : (Val.list [.nat 1, .nat 0]).wt ≤ T := by
      have h1 : (Val.nat 1).wt ≤ WB n := nat_wt (by omega)
      have h2 : (Val.nat 0).wt ≤ WB n := nat_wt (by omega)
      have := wt_lit (c := WB n) [Val.nat 1, Val.nat 0] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl) <;> assumption)
      simp only [List.length_cons, List.length_nil] at this
      omega
    refine Det.post l fun c' hc' => ⟨⟨?_, w2⟩, by omega⟩
    subst hx
    exact answerOK_zero G H

/-! ### The cost -/

theorem stepC_poly2 (h : Membership) : PolyB2 fun S n => stepC h S n := by
  have := WB_poly
  have := VB_poly
  have := preC_poly
  have := postC_poly h
  unfold stepC stepT postNilT preW LB kB
  poly2

theorem riC_poly2 (h : Membership) : PolyB2 fun S n => riC h S n := by
  have := WB_poly
  have := VB_poly
  have := levC_poly
  have := rankC_poly
  have := stepC_poly2 h
  unfold riC riT iterC preW LB kB
  poly2

theorem isoStepC_poly2 (h : Membership) : PolyB2 fun S n => isoStepC h S n := by
  have := WB_poly
  have := levC_poly
  have := riC_poly2 h
  unfold isoStepC isoStepT isoSrchC isoSrchT findC' testC testT anyC' rkT tW extC extT swC swT levB
  poly2

theorem autC_poly2 (h : Membership) : PolyB2 fun S n => autC h S n := by
  have := WB_poly
  have := levC_poly
  have := riC_poly2 h
  unfold autC autT swC swT levB appC AL
  poly2

theorem bodyC_poly2 (h : Membership) : PolyB2 fun S n => bodyC h S n := by
  have := WB_poly
  have : PolyB rngC := by unfold rngC kB; poly
  have := autC_poly2 h
  have := isoStepC_poly2 h
  unfold bodyC bodyT rngC degLC dgStepT filtC dgT ctxT autLC isoLC outT OW GLn tbC AL kB
  poly2

theorem mainC_poly2 (h : Membership) : PolyB2 fun S n => mainC h S n := by
  have := WB_poly
  have := bodyC_poly2 h
  unfold mainC mainT IW
  poly2

/-- A bound on the weight of a string query on `Fin k`. -/
def SWk (k : ℕ) : ℕ :=
  10 * (2 * (10 * ((k ^ 2 + 2) * (2 * (k * (4 * k + 5) + 4) + 1) + 2 * k + 30)) + 1) + 4

theorem SWk_mono {k k' : ℕ} (h : k ≤ k') : SWk k ≤ SWk k' := by
  unfold SWk
  gcongr

theorem stringVal_wt {k : ℕ} (gs : List (Perm (Fin k))) (x y : Fin k → ℕ) (hgs : gs.length ≤ k ^ 2)
    (hc : ∀ i, x i < 2 * k ∧ y i < 2 * k) : (stringVal k gs x y).wt ≤ SWk k := by
  set E := k * (4 * k + 5) + 4 with hE
  have hE2 : k * (2 * (2 * k) + 5) + 4 = E := by rw [hE]; ring
  have wperm : ∀ g : Perm (Fin k), (encPerm g).wt ≤ E := fun g => by
    rw [encPerm_eq_encFun, ← hE2]
    exact wt_encFun_le _ fun i => by have := (g i).isLt; omega
  have wx : (encFun x).wt ≤ E := by
    rw [← hE2]; exact wt_encFun_le _ fun i => (hc i).1.le
  have wy : (encFun y).wt ≤ E := by
    rw [← hE2]; exact wt_encFun_le _ fun i => (hc i).2.le
  have w1 : (encFun fun _ : Fin k => 1).wt ≤ E := by
    rw [← hE2]; exact wt_encFun_le _ fun i => by have := i.isLt; omega
  have wl : (Val.list ((1 :: gs).map encPerm)).wt ≤ (k ^ 2 + 1) * (2 * E + 1) + 4 := by
    have := wt_lit ((1 :: gs).map encPerm) (c := E) (by
      intro v hv
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
      exact wperm g)
    simp only [List.length_map, List.length_cons] at this
    have := Nat.mul_le_mul_right (2 * E + 1) (show gs.length + 1 ≤ k ^ 2 + 1 by omega)
    omega
  have wk := wt_nat_le k
  have hm : (k ^ 2 + 1) * (2 * E + 1) ≤ (k ^ 2 + 2) * (2 * E + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hEc : E ≤ (k ^ 2 + 2) * (2 * E + 1) := by nlinarith
  set c := 10 * ((k ^ 2 + 2) * (2 * E + 1) + 2 * k + 30) with hcdef
  have wG : (encGroup gs).wt ≤ c := by
    have := wt_lit [Val.nat k, .list ((1 :: gs).map encPerm)]
      (c := (k ^ 2 + 1) * (2 * E + 1) + 4 + k + 2) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro v (rfl | rfl) <;> omega)
    simp only [List.length_cons, List.length_nil] at this
    exact this.trans (by omega)
  have w0 : (Val.list []).wt ≤ 4 := by
    have := wt_lit (c := 0) [] (by simp)
    simpa using this
  have wb : (boolVal false).wt ≤ 2 := by simpa [boolVal] using wt_nat_le 0
  have w2 := wt_nat_le 2
  have := wt_lit (stringVal k gs x y |> fun v => match v with | .list vs => vs | _ => []) (c := c)
  have hs : stringVal k gs x y = .list [.nat k, encGroup gs, encFun fun _ : Fin k => 1, encFun x,
    encFun y, .list [], .list [], boolVal false, .nat 2, .nat k] := rfl
  rw [hs]
  have := wt_lit [Val.nat k, encGroup gs, encFun fun _ : Fin k => 1, encFun x, encFun y, .list [],
    .list [], boolVal false, .nat 2, .nat k] (c := c) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
  simp only [List.length_cons, List.length_nil] at this
  simp only [SWk, ← hE, ← hcdef]
  omega

theorem kB_le_pow (n : ℕ) : kB n + 2 ≤ (n + 2) ^ 8 := by
  have h1 : n * (n + 6) ≤ 3 * (n + 2) ^ 2 := by
    have : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
    rw [this]
    nlinarith
  have h2 : kB n ≤ 9 * ((n + 2) ^ 2) ^ 2 := by
    unfold kB
    calc (n * (n + 6)) ^ 2 ≤ (3 * (n + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 9 * ((n + 2) ^ 2) ^ 2 := by ring
  have h3 : 16 ≤ ((n + 2) ^ 2) ^ 2 := by
    have : 4 ≤ (n + 2) ^ 2 := by nlinarith
    nlinarith
  have e : (n + 2) ^ 8 = ((n + 2) ^ 2) ^ 2 * ((n + 2) ^ 2) ^ 2 := by ring
  rw [e]
  nlinarith

theorem d_le_pow (d : ℕ) : d + 6 + 2 ≤ (d + 2) ^ 3 := by
  have : (d + 2) ^ 3 = (d + 2) * (d + 2) * (d + 2) := by ring
  rw [this]
  nlinarith [Nat.zero_le d]

/-- The solver bound at one size. -/
noncomputable def Sreal (a : ℝ) (K m n d : ℕ) : ℝ :=
  Real.exp (a * Real.log ((kB n : ℝ) + 2) * Real.log (((d + 6 : ℕ) : ℝ) + 2)) * K *
    ((SWk (kB n) : ℝ) + 1) ^ m

set_option maxHeartbeats 2000000 in
theorem solverAt_of {Pg : Program} {fd : ℕ} {a : ℝ} {K m : ℕ} (ha : 0 ≤ a)
    (hS : ∀ (D k : ℕ) (gs : List (Perm (Fin k))) (x y : Fin k → ℕ),
      6 ≤ D → gs.length ≤ k ^ 2 → GammaHat D (gens gs) → (∀ i, x i < 2 * k ∧ y i < 2 * k) →
        FunAll Pg fd (.list [.nat D, stringVal k gs x y]) fun u cost =>
          AnsC (Equiv.refl _) u (stringState (gens gs) x y).answer ∧
            (cost : ℝ) ≤ Real.exp (a * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) * K *
              (((stringVal k gs x y).wt : ℝ) + 1) ^ m)
    (n d D k : ℕ) (h6 : 6 ≤ D) (hDd : D ≤ d + 6) (hk : k ≤ kB n) :
    SolverAt Pg fd D k ⌈Sreal a K m n d⌉₊ := by
  intro gs x y hgs hG hc
  refine (hS D k gs x y h6 hgs hG hc).mono fun u c hu => ⟨hu.1, ?_⟩
  have hc' := hu.2
  have hw := (stringVal_wt gs x y hgs hc).trans (SWk_mono hk)
  generalize (stringVal k gs x y).wt = W at hc' hw
  have l1 : Real.log ((k : ℝ) + 2) ≤ Real.log ((kB n : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 2)
  have l2 : Real.log ((D : ℝ) + 2) ≤ Real.log (((d + 6 : ℕ) : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hDd 2)
  have p1 : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by
    have := k.cast_nonneg (α := ℝ); linarith)
  have p2 : 0 ≤ Real.log ((D : ℝ) + 2) := Real.log_nonneg (by
    have := D.cast_nonneg (α := ℝ); linarith)
  have e1 : Real.exp (a * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) ≤
      Real.exp (a * Real.log ((kB n : ℝ) + 2) * Real.log (((d + 6 : ℕ) : ℝ) + 2)) :=
    Real.exp_le_exp.2 (mul_le_mul (mul_le_mul_of_nonneg_left l1 ha) l2 p2
      (mul_nonneg ha (p1.trans l1)))
  have e2 : ((W : ℝ) + 1) ^ m ≤ ((SWk (kB n) : ℝ) + 1) ^ m :=
    pow_le_pow_left₀ (by positivity) (by have := (Nat.cast_le (α := ℝ)).2 hw; linarith) m
  have hK : (0 : ℝ) ≤ K := K.cast_nonneg
  have e3 : (c : ℝ) ≤ Sreal a K m n d :=
    hc'.trans (mul_le_mul (mul_le_mul_of_nonneg_right e1 hK) e2 (by positivity) (by positivity))
  exact Nat.cast_le.1 (e3.trans (Nat.le_ceil _))

/-- **The graph theorem.** -/
theorem graphSolver : GraphSolver graphFuns := by
  intro h Pg b fd j hP hj hSS
  obtain ⟨a, K, m, ha, hS⟩ := hSS
  obtain ⟨K2, e, hK2⟩ := mainC_poly2 h
  obtain ⟨K3, e3, hK3⟩ : PolyB fun n => SWk (kB n) + 1 := by
    unfold SWk kB
    poly
  have hW : LogExpB fun n _ => (SWk (kB n) : ℝ) + 1 := by
    refine LogExpB.mono (LogExpB.mul (LogExpB.const K3) (LogExpB.pow LogExpB.n2 (fun n d => by positivity) e3)
      (fun _ _ => by positivity) (fun n d => by positivity)) fun n d => ?_
    have := hK3 n
    simp only [pc] at this
    have h1 : ((SWk (kB n) + 1 : ℕ) : ℝ) ≤ (K3 : ℝ) * ((n : ℝ) + 1) ^ e3 := by exact_mod_cast this
    have h2 : ((n : ℝ) + 1) ^ e3 ≤ ((n : ℝ) + 2) ^ e3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) e3
    push_cast at h1
    nlinarith [K3.cast_nonneg (α := ℝ), pow_nonneg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity) e3]
  have hX : LogExpB fun n d => Real.exp (a * Real.log ((kB n : ℝ) + 2) *
      Real.log (((d + 6 : ℕ) : ℝ) + 2)) :=
    LogExpB.expLog ha (fun n d => by positivity) (fun n d => by positivity)
      (fun n d => by exact_mod_cast kB_le_pow n) (fun n d => by exact_mod_cast d_le_pow d)
  have hB : LogExpB fun n d => (K2 : ℝ) * (((n : ℝ) + 2) * (Real.exp (a * Real.log ((kB n : ℝ) + 2) *
      Real.log (((d + 6 : ℕ) : ℝ) + 2)) * ((1 + (K : ℝ)) * ((SWk (kB n) : ℝ) + 1) ^ m))) ^ e := by
    refine LogExpB.mul (LogExpB.const _) (LogExpB.pow (LogExpB.mul LogExpB.n2 (LogExpB.mul hX (LogExpB.mul (LogExpB.const _)
      (LogExpB.pow hW (fun _ _ => by positivity) m) (fun _ _ => by positivity)
      (fun _ _ => by positivity)) (fun _ _ => by positivity) (fun _ _ => by positivity))
      (fun _ _ => by positivity) (fun _ _ => by positivity)) (fun _ _ => by positivity) e)
      (fun _ _ => by positivity) (fun _ _ => by positivity)
  obtain ⟨C, hC⟩ := hB
  refine ⟨C, fun n d G H hG hH => ?_⟩
  have hdG : ∀ u, degL G u ≤ d := fun u => by rw [degL_eq_ncard]; exact hG u
  have hdH : ∀ u, degL H u ≤ d := fun u => by rw [degL_eq_ncard]; exact hH u
  refine (main_spec (S := ⌈Sreal a K m n d⌉₊) h hP hj
    (fun D h6 h1 h2 => solverAt_of ha hS n d D _ h6 h1 (by
      have hnD : n * D ≤ n * (n + 6) := Nat.mul_le_mul_left _ h2
      have := Nat.mul_le_mul hnD hnD
      simpa [kB, sq] using this)) G H hdG hdH).mono fun w c hw => ⟨hw.1, ?_⟩
  refine le_trans ?_ (hC n d)
  set Sr := Sreal a K m n d with hSr
  set E := Real.exp (a * Real.log ((kB n : ℝ) + 2) * Real.log (((d + 6 : ℕ) : ℝ) + 2)) with hE
  set W := ((SWk (kB n) : ℝ) + 1) ^ m with hWd
  have hE1 : 1 ≤ E := Real.one_le_exp (by
    have p1 : 0 ≤ Real.log ((kB n : ℝ) + 2) := Real.log_nonneg (by
      have := (kB n).cast_nonneg (α := ℝ); linarith)
    have p2 : 0 ≤ Real.log (((d + 6 : ℕ) : ℝ) + 2) := Real.log_nonneg (by
      have := (d + 6).cast_nonneg (α := ℝ); linarith)
    positivity)
  have hW1 : 1 ≤ W := one_le_pow₀ (by have := (SWk (kB n)).cast_nonneg (α := ℝ); linarith)
  have hSr0 : 0 ≤ Sr := by rw [hSr, Sreal]; positivity
  have hceil : (⌈Sr⌉₊ : ℝ) < Sr + 1 := Nat.ceil_lt_add_one hSr0
  have hSrE : Sr = E * K * W := rfl
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  have hbase : (n : ℝ) + ⌈Sr⌉₊ + 1 ≤ ((n : ℝ) + 2) * (E * ((1 + K) * W)) := by
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have h1 : (n : ℝ) + ⌈Sr⌉₊ + 1 ≤ ((n : ℝ) + 2) * (1 + E * K * W) := by nlinarith
    have h2 : 1 + E * K * W ≤ E * ((1 + K) * W) := by nlinarith [mul_le_mul hE1 hW1 zero_le_one (by linarith)]
    nlinarith
  have hc := hw.2.trans (hK2 ⌈Sr⌉₊ n)
  have hc' : (c : ℝ) ≤ (K2 : ℝ) * ((n : ℝ) + ⌈Sr⌉₊ + 1) ^ e := by exact_mod_cast hc
  refine hc'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase e)
    (by positivity))

end GI.Degree
