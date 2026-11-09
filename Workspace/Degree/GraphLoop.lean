module

public import Workspace.Degree.GraphPre

/-!
# The loop on radii

Lemma 9.4 of the paper as a program. `stepFuns a fd j` runs one step of the loop,
on `[c, r, acc]`. The accumulator is `[]`, or `[U, G]` with `U = ρ T`, `T ∈ Ball r` and
`⟨G⟩ = ballGroup r`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly Equiv
open GI.Machine (BinOp)
open scoped Pointwise

variable {n D : ℕ}

/-- The string solver at one size, with cost at most `S`. -/
def SolverAt (Pg : Program) (fd D k S : ℕ) : Prop :=
  ∀ (gs : List (Perm (Fin k))) (x y : Fin k → ℕ), gs.length ≤ k ^ 2 → GammaHat D (gens gs) →
    (∀ i, x i < 2 * k ∧ y i < 2 * k) →
    FunAll Pg fd (.list [.nat D, stringVal k gs x y]) fun u cost =>
      AnsC (Equiv.refl _) u (stringState (gens gs) x y).answer ∧ cost ≤ S

/-- The body of a step. -/
def stepE (fp fd fq : ℕ) : Expr :=
  .ite (.length (arg 2))
    (.letE (.call fp (.var 0))
      (.letE (.call fd (.get (.var 1) (.nat 3)))
        (.call fq (mk3 (mk3 (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1))
          (.get (.var 1) (.nat 2))) (.get (arg 2) (.nat 0)) (.var 2)))))
    .nil

/-- The functions of a step, at base `a`. Sixty-four functions. -/
def stepFuns (a fd j : ℕ) : List Expr :=
  [stepE (a + 1) fd (a + 38), preE (a + 2) (a + 10) (a + 14) (a + 34)] ++ fwdFuns (a + 2) ++
    tabFuns (a + 10) colE ++ gensFuns (a + 14) ++ tabFuns (a + 34) (.nat 1) ++
    [postE (a + 39) (a + 47) (a + 52) (a + 55) (a + 59)] ++ parFuns (a + 39) ++ decFuns (a + 47) ++
    mapFuns (a + 52) (a + 47) ++ composeFuns (a + 55) ++ reduceFuns (a + 59) j

/-- The invariant of the loop. -/
def LoopInv (ρ : Perm (Fin n)) (ℓ : Fin n → ℕ) (R : ℕ) (X Y : SimpleGraph (Fin n)) (r : ℕ)
    (acc : Val) : Prop :=
  (acc = .list [] ∧ Ball ℓ R X (pull ρ Y) = ∅) ∨
    ∃ (T : Perm (Fin n)) (gs : List (Perm (Fin n))),
      acc = .list [encPerm (ρ * T), encGroup gs] ∧ gs.length ≤ n ^ 2 ∧
        T ∈ Ball ℓ r X (pull ρ Y) ∧ gens gs = ballGroup ℓ r X

/-- What a step uses of its graphs. -/
structure StepHyp (ρ : Perm (Fin n)) (D : ℕ) (ℓ : Fin n → ℕ) (R : ℕ)
    (X Y : SimpleGraph (Fin n)) : Prop where
  hX : HasLevels X ℓ R
  hY : HasLevels (pull ρ Y) ℓ R
  dX : ∀ u, (fwd ℓ X u).length ≤ D
  dY : ∀ (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D
  size : R ≤ n
  sz : Sz n D
  lev : ∀ u, ℓ u ≤ n

theorem ball_empty_of_le {ℓ : Fin n → ℕ} {X Y : SimpleGraph (Fin n)} {r R : ℕ} (hr : r ≤ R)
    (h : Ball ℓ r X Y = ∅) : Ball ℓ R X Y = ∅ := by
  induction R, hr using Nat.le_induction with
  | base => exact h
  | succ R _ ih =>
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    have := Ball.cut hg
    rw [ih] at this
    exact this

theorem pull_pull (T ρ : Perm (Fin n)) (Y : SimpleGraph (Fin n)) :
    pull T (pull ρ Y) = pull (ρ * T) Y := by
  ext a b
  rfl

/-- The map `dec` on all permutations. -/
noncomputable def decTot {ℓ : Fin n → ℕ} {r R : ℕ} {X : SimpleGraph (Fin n)}
    {fX : Fin n → List (Fin n)} {par : Fin n → Fin n × Fin D} (hX : HasLevels X ℓ R)
    (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX) (hDX : ∀ u, (fX u).length ≤ D)
    (hpar : ParOK ℓ r fX par) (z : Fin D) (f : Perm (Fin n × Fin D)) : Perm (Fin n) :=
  open Classical in
  if hf : f ∈ querySub D ℓ r X fX then decHom hX hr fXok hDX hpar z ⟨f, hf⟩ else 1

theorem decTot_one {ℓ : Fin n → ℕ} {r R : ℕ} {X : SimpleGraph (Fin n)}
    {fX : Fin n → List (Fin n)} {par : Fin n → Fin n × Fin D} (hX : HasLevels X ℓ R)
    (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX) (hDX : ∀ u, (fX u).length ≤ D)
    (hpar : ParOK ℓ r fX par) (z : Fin D) : decTot hX hr fXok hDX hpar z 1 = 1 := by
  rw [decTot, dif_pos (one_mem _)]
  exact map_one (decHom hX hr fXok hDX hpar z)

theorem decTot_apply {ℓ : Fin n → ℕ} {r R : ℕ} {X : SimpleGraph (Fin n)}
    {fX : Fin n → List (Fin n)} {par : Fin n → Fin n × Fin D} (hX : HasLevels X ℓ R)
    (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX) (hDX : ∀ u, (fX u).length ≤ D)
    (hpar : ParOK ℓ r fX par) (z : Fin D) {f : Perm (Fin n × Fin D)}
    (hf : f ∈ querySub D ℓ r X fX) (u : Fin n) :
    decTot hX hr fXok hDX hpar z f u = decMap ℓ r fX par z f u := by
  rw [decTot, dif_pos hf]
  exact (query_dec (z := z) hX hX hr fXok fXok hDX hDX hpar one_mem_ball_self hf).choose_spec.2 u

theorem image_refl_eq {k : ℕ} {A S : Set (Perm (Fin k))}
    (h : toFin (Equiv.refl (Fin k)) '' A = S) : A = S := by
  have e : ∀ g, toFin (Equiv.refl (Fin k)) g = g := fun g => by
    ext
    rfl
  rw [← h]
  ext g
  simp [e]

theorem gammaHat_query (z : Fin n × Fin D) (hD : 0 < D) {G : Subgroup (Perm (Fin n))}
    (hG : GammaHat D G) (gs : List (Perm (Fin n))) (hgs : gens gs = G) :
    GammaHat D (gens (slotGens hD gs)) := by
  rw [gens_slotGens, hgs]
  have h1 := gammaHat_slotGroup (z0 hD) hG
  let e := (slotGroup D G).equivMapOfInjective (diag n D) (diag_injective z)
  exact h1.of_injective e.symm.toMonoidHom e.symm.injective

/-- The budget of a step. -/
noncomputable def stepT (h : Membership) (S n : ℕ) : ℕ :=
  S + 1 + preC n + postC h n + 100 * postNilT n + preW n

/-- The bound of a step. -/
noncomputable def stepC (h : Membership) (S n : ℕ) : ℕ := 1000000 * stepT h S n

theorem stepCtx_wt (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n)
    (X Y : SimpleGraph (Fin n)) :
    (stepCtx D ℓ X Y).wt ≤ 3 * (2 * (8 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := by
  have h0 := WB_ge n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have wX := adjVal_wt X
  have wY := adjVal_wt Y
  have wn : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  have wDn : (Val.nat D).wt ≤ WB n := nat_wt (by have := hS.le; omega)
  have wm : (Val.nat (n * D)).wt ≤ WB n := nat_wt (by omega)
  have wk : (Val.nat (n * D * (n * D))).wt ≤ WB n := nat_wt (by omega)
  have wℓ : (encFun ℓ).wt ≤ WB n := table_wt (by omega) hℓ
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wj : (ids (n * D)).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wK : (ids (n * D * (n * D))).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have hb0 : (Val.list (baseV n D ℓ)).wt ≤ 8 * (2 * WB n + 1) + 4 := wt_lit _ (by
    intro v hv
    simp only [baseV, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  exact wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl) <;> omega)

theorem le_kB (n : ℕ) : n ≤ kB n := by
  have h1 : n ≤ n * (n + 6) := Nat.le_mul_of_pos_right _ (by omega)
  exact h1.trans (Nat.le_self_pow (by omega) _)

/-- The argument of a step. -/
theorem stepArg_wt (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n)
    (X Y : SimpleGraph (Fin n)) (U : Perm (Fin n)) {gs : List (Perm (Fin n))}
    (hgs : gs.length ≤ n ^ 2) :
    2 * (Val.list [stepCtx D ℓ X Y, .nat r, .list [encPerm U, encGroup gs]]).wt + 100 ≤ preW n := by
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have wc := stepCtx_wt (D := D) hS hℓ X Y
  have wU : (encPerm U).wt ≤ WB n := perm_wt (by omega) U
  have wn : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  have wr : (Val.nat r).wt ≤ WB n := nat_wt (by omega)
  have hg1 : ((1 : Perm (Fin n)) :: gs).length ≤ kB n ^ 2 + 1 := by
    have : n ^ 2 ≤ kB n ^ 2 := Nat.pow_le_pow_left (le_kB n) 2
    simp only [List.length_cons]
    omega
  have wL : (Val.list (((1 : Perm (Fin n)) :: gs).map encPerm)).wt ≤ LB n :=
    permList_wt (by omega) hg1
  have w1 : (encGroup gs).wt ≤ 2 * (2 * (LB n + WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl) <;> omega)
  have w2 : (Val.list [encPerm U, encGroup gs]).wt ≤
      2 * (2 * (2 * (2 * (LB n + WB n) + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl) <;> omega)
  have w3 : (Val.list [stepCtx D ℓ X Y, .nat r, .list [encPerm U, encGroup gs]]).wt ≤
      3 * (2 * (3 * (2 * (8 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 +
        (2 * (2 * (2 * (2 * (LB n + WB n) + 1) + 4 + WB n) + 1) + 4) + WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl) <;> omega)
  simp only [preW]
  omega

set_option maxHeartbeats 4000000 in
/-- **One step of the loop.** -/
theorem step_spec {P : Program} {a fd j S : ℕ} (h : Membership) (hP : P.HasAt a (stepFuns a fd j))
    (hj : P.prims[j]? = some (membershipPrim h)) (hSol : SolverAt P fd D (n * D * (n * D)) S)
    {ρ : Perm (Fin n)} {ℓ : Fin n → ℕ} {R : ℕ} {X Y : SimpleGraph (Fin n)}
    (hH : StepHyp ρ D ℓ R X Y) {r : ℕ} (hr : r + 1 ≤ R) {acc : Val}
    (hI : LoopInv ρ ℓ R X Y r acc) :
    FunAll P a (.list [stepCtx D ℓ X Y, .nat r, acc]) fun w cost =>
      LoopInv ρ ℓ R X Y (r + 1) w ∧ cost ≤ stepC h S n := by
  classical
  have hS := hH.sz
  have hD : 0 < D := by have := hS.six; omega
  have hℓ := hH.lev
  have hrn : r ≤ n := by have := hH.size; omega
  have h1 := hP.left
  have h2 := h1.left
  have h3 := h2.left
  have h4 := h3.left
  have h5 := h4.left
  have h6 := h5.left
  have h7 := h6.left
  have h8 := h7.left
  have h9 := h8.left
  have h10 : P.HasAt a ([stepE (a + 1) fd (a + 38)] ++ [preE (a + 2) (a + 10) (a + 14) (a + 34)]) :=
    h9.left
  have hfS : P.funs[a]? = some (stepE (a + 1) fd (a + 38)) := h10.left.single
  have hfP : P.funs[a + 1]? = some (preE (a + 2) (a + 10) (a + 14) (a + 34)) := h10.right.single
  have hFw : P.HasAt (a + 2) (fwdFuns (a + 2)) := h9.right
  have hCl : P.HasAt (a + 10) (tabFuns (a + 10) colE) := h8.right
  have hGn : P.HasAt (a + 14) (gensFuns (a + 14)) := h7.right
  have hOn : P.HasAt (a + 34) (tabFuns (a + 34) (.nat 1)) := h6.right
  have hfQ : P.funs[a + 38]? = some (postE (a + 39) (a + 47) (a + 52) (a + 55) (a + 59)) :=
    h5.right.single
  have hPr : P.HasAt (a + 39) (parFuns (a + 39)) := h4.right
  have hDc : P.HasAt (a + 47) (decFuns (a + 47)) := h3.right
  have hMp : P.HasAt (a + 52) (mapFuns (a + 52) (a + 47)) := h2.right
  have hCp : P.HasAt (a + 55) (composeFuns (a + 55)) := h1.right
  have hRd : P.HasAt (a + 59) (reduceFuns (a + 59) j) := hP.right
  have hTT : ∀ {x : ℕ}, x ≤ preW n → x ≤ stepT h S n := fun hx => by
    simp only [stepT]
    omega
  rcases hI with ⟨rfl, hE⟩ | ⟨Tb, gs, rfl, hgs, hTb, hg⟩
  · set A := Val.list [stepCtx D ℓ X Y, .nat r, .list []] with hA
    have w0 : 2 * A.wt + 100 ≤ preW n := by
      have wc := stepCtx_wt (D := D) hS hℓ X Y
      have wr : (Val.nat r).wt ≤ WB n := nat_wt (by have := le_kB n; omega)
      have w4 : (Val.list []).wt ≤ WB n := by
        have := wt_lit [] (c := 0) (by simp)
        simp only [List.length_nil] at this
        have := WB_ge n
        omega
      have w3 : A.wt ≤ 3 * (2 * (3 * (2 * (8 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 + WB n) + 1) + 4 :=
        wt_lit _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl | rfl | rfl) <;> omega)
      have hV := WB_le_VB n
      have := WB_ge n
      simp only [preW]
      omega
    have a2 : Lv P [A] (stepT h S n) (arg 2) (.list []) 1 :=
      Lv.arg (vs := [stepCtx D ℓ X Y, .nat r, .list []]) rfl
        (hTT (by change 2 * A.wt + 2 + 5 ≤ preW n; omega))
    have hl := Lv.length a2 (hTT (by omega))
    have n1 : Lv P [A] (stepT h S n) .nil (.list []) 1 := Lv.nil (hTT (by omega))
    have := funDet_of_lv hfS (T := stepT h S n) (m := 1000000)
      (Lv.mono (e := stepE (a + 1) fd (a + 38)) (Lv.ite_zero (t := _) hl n1) (by norm_num))
    refine FunAll.mono this fun w cost hw => ⟨Or.inl ⟨hw.1, hE⟩, ?_⟩
    simp only [stepC]
    exact hw.2
  set U := ρ * Tb with hU
  set Z := pull U Y with hZ
  have hpp : pull Tb (pull ρ Y) = Z := pull_pull Tb ρ Y
  set A := Val.list [stepCtx D ℓ X Y, .nat r, .list [encPerm U, encGroup gs]] with hA
  have w0 : 2 * A.wt + 100 ≤ preW n := stepArg_wt hS hℓ hrn X Y U hgs
  have hR1 : r ≤ R := by omega
  set z : Fin n × Fin D := (⟨0, hS.pos⟩, z0 hD) with hz
  have fXok := fwdOK ℓ X
  have fYok : FwdOK ℓ (pull Tb (pull ρ Y)) (fwd ℓ Z) := by rw [hpp]; exact fwdOK ℓ Z
  set par := parSlot z ℓ r (fwd ℓ X) with hpar_def
  have hparOK : ParOK ℓ r (fwd ℓ X) par := parSlot_parOK hH.hX hr z hH.dX
  have hpar : ∀ w, ℓ w = r + 1 → (slotE n D (par w) : ℕ) = parNum D ℓ r (fwd ℓ X) w :=
    fun w hw => (parSlot_ok hH.hX hr z hH.dX hw).2.1
  have hPre := pre_spec hfP hFw hCl hGn hOn hS hD hℓ hrn X Y U hgs
  have wPV := FunDet.wt_lt hPre
  set PV := preV hD ℓ r X Y U gs with hPV
  set cX := colorX D ℓ r X (fwd ℓ X) with hcX
  set cY := colorX D ℓ r Z (fwd ℓ Z) with hcY
  have hk36 : 5 < 2 * (n * D * (n * D)) := by
    have := hS.m_le_k
    have := hS.six
    have : D ≤ n * D := Nat.le_mul_of_pos_left _ hS.pos
    omega
  have hcol : ∀ i, cX i < 2 * (n * D * (n * D)) ∧ cY i < 2 * (n * D * (n * D)) := fun i => by
    obtain ⟨s, s', rfl⟩ := exists_pair i
    simp only [hcX, hcY, colorX_pair]
    exact ⟨(slotColor_le _ _).trans_lt hk36, (slotColor_le _ _).trans_lt hk36⟩
  have hgG : gens (slotGens hD gs) = (slotGroup D (ballGroup ℓ r X)).map (diag n D) := by
    rw [gens_slotGens, hg]
  have hSv := hSol (slotGens hD gs) cX cY (length_slotGens_le hS hD hgs)
    (gammaHat_query z hD (gammaHat_ballGroup hH.hX (by omega) hH.dX hR1) gs hg) hcol
  set T := stepT h S n with hT
  have hT0 : preC n + S + 1 ≤ T := by simp only [hT, stepT]; omega
  have hT1 : postC h n + 100 * postNilT n ≤ T := by simp only [hT, stepT]; omega
  have c0 : Lv P [A] T (.length (arg 2)) (.nat 2) _ :=
    Lv.length (vs := [encPerm U, encGroup gs]) (Lv.arg (vs := [stepCtx D ℓ X Y, .nat r,
      .list [encPerm U, encGroup gs]]) rfl (hTT (by change 2 * A.wt + 2 + 5 ≤ preW n; omega)))
      (hTT (by omega))
  have c0' := Lv.mono c0 (show _ ≤ 10 by norm_num)
  have cP := Lv.call (Lv.var (env := [A]) (i := 0) rfl (hTT (by omega))) hPre (by omega)
  have cP' := Lv.mono cP (show _ ≤ 10 by norm_num)
  refine FunAll.intro hfS (EvalAll.ite c0' (fun vc cc h => ⟨2, h.1⟩) fun x cc hx => ?_)
  obtain ⟨hx2, hcc⟩ := hx
  obtain rfl : x = 2 := by injection hx2
  rw [if_neg (by norm_num : (2 : ℕ) ≠ 0)]
  refine EvalAll.letE cP' fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  have v1 : ∀ tl, Lv P (A :: PV :: tl) T (.var 1) PV 1 := fun tl => Lv.var rfl (by omega)
  have n3 : ∀ env : List Val, ∀ i, i ≤ 3 → Lv P env T (.nat i) (.nat i) 1 := fun env i hi =>
    Lv.nat i (hTT (by omega))
  set qv : Val := .list [.nat D, stringVal (n * D * (n * D)) (slotGens hD gs) cX cY] with hqv
  have gq := Lv.get (vs := [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z, qv]) (v1 []) (n3 _ 3 le_rfl) rfl
  refine EvalAll.letE (Ra := fun u c => AnsC (Equiv.refl _) u
      (stringState (gens (slotGens hD gs)) cX cY).answer ∧ c ≤ 10 * T + 2 * S + 1 ∧ u.wt ≤ S)
    (EvalAll.call_funAll (Lv.mono gq (show _ ≤ 10 by norm_num)) fun v ca hv => ?_)
    fun u cu hu => ?_
  · obtain ⟨rfl, hca'⟩ := hv
    refine FunAll.mono hSv.wt_lt fun w cb hw => ⟨hw.1.1, ?_, ?_⟩
    · have := hw.1.2
      have := hw.2
      omega
    · have := hw.1.2
      have := hw.2
      omega
  obtain ⟨hAns, hcu, hwu⟩ := hu
  have gB := Lv.get (vs := [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z, qv]) (v1 [u]) (n3 _ 0 (by omega)) rfl
  have gX := Lv.get (vs := [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z, qv]) (v1 [u]) (n3 _ 1 (by omega)) rfl
  have gZ := Lv.get (vs := [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z, qv]) (v1 [u]) (n3 _ 2 (by omega)) rfl
  have gU := Lv.get (vs := [encPerm U, encGroup gs]) (Lv.arg (rest := [PV, u])
    (vs := [stepCtx D ℓ X Y, .nat r, .list [encPerm U, encGroup gs]]) rfl
    (hTT (by change 2 * A.wt + 2 + 5 ≤ preW n; omega))) (n3 _ 0 (by omega)) rfl
  have vu : Lv P [A, PV, u] T (.var 2) u 1 := Lv.var rfl (by omega)
  have args := Lv.mono (Lv.mk3 (Lv.mk3 gB gX gZ (hTT (by omega))) gU vu (hTT (by omega)))
    (show _ ≤ 10000 by norm_num)
  refine EvalAll.call_funAll args fun v ca2 hv => ?_
  obtain ⟨rfl, hca2⟩ := hv
  have hV := WB_le_VB n
  have h0 := WB_ge n
  have wb := bv_wt hS hℓ hrn
  have wFX := fwdV_le_VB ℓ X
  have wFZ := fwdV_le_VB ℓ Z
  have wU : (encPerm U).wt ≤ WB n := perm_wt (by have := le_kB n; omega) U
  have wB3 : (Val.list [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z]).wt ≤ 3 * (2 * VB n + 1) + 4 :=
    wt_lit _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl) <;> omega)
  rcases hAns with ⟨rfl, hAe⟩ | ⟨t, hs, rfl, hhs, hAt⟩
  · -- the answer is empty
    have w4 : (Val.list []).wt ≤ WB n := by
      have := wt_lit [] (c := 0) (by simp)
      simp only [List.length_nil] at this
      omega
    have wA : (Val.list [.list [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z], encPerm U, .list []]).wt ≤
        3 * (2 * (3 * (2 * VB n + 1) + 4 + VB n) + 1) + 4 := wt_lit _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl) <;> omega)
    have hN := post_nil (n := n) hfQ (b := .list [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z]) (U := encPerm U)
      (by simp only [postNilT]; omega)
    have hQ : Query D ℓ r X (pull Tb (pull ρ Y)) (fwd ℓ X) (fwd ℓ Z) = ∅ := by
      rw [hpp]
      refine Set.eq_empty_of_forall_notMem fun g hg' => ?_
      have hm : diag n D g ∈ (stringState (gens (slotGens hD gs)) cX cY).answer := by
        change diag n D g ∈ answer (gens (slotGens hD gs)) Set.univ cX cY
        rw [hgG]
        exact mem_answer_iff.2 ⟨g, hg', rfl⟩
      rw [hAe] at hm
      exact hm
    have hE : Ball ℓ R X (pull ρ Y) = ∅ := ball_empty_of_le hr
      (Set.eq_empty_of_forall_notMem fun hh hmem =>
        step_empty (z0 hD) hTb fXok fYok hH.dX hparOK hQ hmem)
    refine FunAll.mono (FunAll.wt_lt hN) fun w cb hw => ⟨Or.inl ⟨hw.1.1, hE⟩, ?_⟩
    have := hw.1.2
    have := hw.2
    simp only [stepC]
    omega
  · -- the answer is a coset
    have hAc : t • (gens hs : Set (Perm (Fin (n * D * (n * D))))) =
        answer ((slotGroup D (ballGroup ℓ r X)).map (diag n D)) Set.univ cX cY := by
      have e1 := image_refl_eq hAt
      change answer (gens (slotGens hD gs)) Set.univ cX cY = _ at e1
      rw [hgG] at e1
      exact e1.symm
    obtain ⟨g₀, hg₀, rfl, hs', rfl, hc⟩ := answer_coset z hAc
    have hg₁ : g₀ ∈ Query D ℓ r X (pull Tb (pull ρ Y)) (fwd ℓ X) (fwd ℓ Z) := by
      rw [hpp]
      exact hg₀
    obtain ⟨e, he, heB⟩ := step_coset (z := z0 hD) hTb hH.hX hH.hY hr fXok fYok hH.dX (hH.dY U)
      hparOK hg₁
    have hlen : hs'.length ≤ kB n ^ 2 := by
      have := Nat.pow_le_pow_left hS.k_le 2
      simp only [List.length_map] at hhs
      omega
    set decP := decTot hH.hX hr fXok hH.dX hparOK (z0 hD) with hdecP
    have hdec : ∀ f ∈ (1 :: hs'), ∀ u, decP f u = decMap ℓ r (fwd ℓ X) par (z0 hD) f u := by
      intro f hf u
      refine decTot_apply hH.hX hr fXok hH.dX hparOK (z0 hD) ?_ u
      rcases List.mem_cons.1 hf with rfl | hf
      · exact one_mem _
      · rw [← hc]
        exact Subgroup.subset_closure hf
    have hdec1 : decP 1 = 1 := decTot_one hH.hX hr fXok hH.dX hparOK (z0 hD)
    have hPost := post_some h hfQ hPr hDc hMp hCp hRd hj hS hD hℓ hrn (X := X) (Z := Z) (U := U) hpar z he
      hlen decP hdec hdec1
    have hes : List.Forall₂ (fun f e => ∀ u, e u = decMap ℓ r (fwd ℓ X) par (z0 hD) f u) hs'
        (hs'.map decP) :=
      List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun f hf u =>
        hdec f (List.mem_cons_of_mem _ hf) u)
    refine FunAll.mono (FunAll.wt_lt hPost) fun w cb hw =>
      ⟨Or.inr ⟨Tb * e, keepList (hs'.map decP), ?_, length_keepList_le _, heB, ?_⟩, ?_⟩
    · rw [hw.1.1, mul_assoc]
    · rw [gens_keepList]
      exact step_group hH.hX hr fXok hH.dX hparOK hc hes
    · have := hw.1.2
      have := hw.2
      simp only [stepC]
      omega

end GI.Degree
