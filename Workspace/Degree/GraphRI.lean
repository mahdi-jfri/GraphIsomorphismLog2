module

public import Workspace.Degree.GraphLoop
public import Workspace.Degree.GraphRankProg
public import Workspace.Degree.GraphLevProg

/-!
# Rooted isomorphism

`riFuns b fd j` on `[riCtx D X Y, v, w]` returns `[]` if there is no isomorphism of the component
of `v` in `X` onto the component of `w` in `Y` that sends `v` to `w`. Otherwise it returns such a
map `τ` and generators of `ballGroup (lev X v) (n - 1) X` (`ri_spec`). This is Lemma 9.4 of
the paper.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The context of `ri`. -/
noncomputable def riCtx (D : ℕ) (X Y : SimpleGraph (Fin n)) : Val :=
  .list [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D), .nat (n * D * (n * D)),
    ids (n * D), ids (n * D * (n * D))]

/-- The main function of `ri`. -/
def riMainE (b : ℕ) : Expr :=
  let g := fun i => Expr.get (arg 0) (.nat i)
  .letE (.call (b + 1) (mk4 (g 0) (g 2) (g 3) (arg 1)))
  (.letE (.call (b + 1) (mk4 (g 1) (g 2) (g 3) (arg 2)))
  (.letE (.call (b + 18) (mk4 (.var 1) (.var 2) (g 3) (g 2)))
    (.ite (.get (.var 3) (.nat 1)) .nil
      (.call (b + 39) (mk3
        (mk3 (.snoc (.snoc (.snoc (mk5 (g 2) (g 4) (g 5) (g 6) (.var 1)) (g 3)) (g 7)) (g 8))
          (g 0) (g 1))
        (.arith .sub (g 2) (.nat 1)) (mk2 (.get (.var 3) (.nat 0)) (mk2 (g 2) (mk1 (g 3)))))))))

/-- The functions of `ri`. One hundred and six functions. -/
def riFuns (b fd j : ℕ) : List Expr :=
  [riMainE b] ++ levFuns (b + 1) ++ rankFuns (b + 18) ++ iterFuns (b + 39) (b + 42) ++
    stepFuns (b + 42) fd j

/-- The output of `ri`. -/
def RIOut (X : SimpleGraph (Fin n)) (v : Fin n) (Y : SimpleGraph (Fin n)) (w : Fin n)
    (out : Val) : Prop :=
  (out = .list [] ∧ ∀ g, ¬IsRooted X v Y w g) ∨
    ∃ (τ : Perm (Fin n)) (gs : List (Perm (Fin n))), out = .list [encPerm τ, encGroup gs] ∧
      IsRooted X v Y w τ ∧ gens gs = ballGroup (lev X v) (n - 1) X ∧ gs.length ≤ n ^ 2

theorem one_mem_ball_zero {ℓ : Fin n → ℕ} {R : ℕ} {X Y : SimpleGraph (Fin n)}
    (hX : HasLevels X ℓ R) : (1 : Perm (Fin n)) ∈ Ball ℓ 0 X Y := by
  obtain ⟨o, ho⟩ := hX.root
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun a b ha hb => ?_⟩
  have e1 : a = o := (ho a).1 (by omega)
  have e2 : b = o := (ho b).1 (by omega)
  subst e1 e2
  simp

theorem gens_nil : gens ([] : List (Perm (Fin n))) = ⊥ := by
  simp [gens]

theorem acc_wt (hS : Sz n D) (U : Perm (Fin n)) {gs : List (Perm (Fin n))}
    (hgs : gs.length ≤ n ^ 2) : (Val.list [encPerm U, encGroup gs]).wt ≤ preW n := by
  have := stepArg_wt (D := D) (ℓ := fun _ : Fin n => 0) hS (fun _ => Nat.zero_le _) (r := 0) (Nat.zero_le _)
    ⊥ ⊥ U hgs
  have h2 := wt_le_wt_list (vs := [stepCtx D (fun _ : Fin n => 0) ⊥ ⊥, .nat 0,
    .list [encPerm U, encGroup gs]]) (v := .list [encPerm U, encGroup gs]) (by simp)
  omega

theorem loopInv_wt (hS : Sz n D) {ρ : Perm (Fin n)} {ℓ : Fin n → ℕ} {R : ℕ}
    {X Y : SimpleGraph (Fin n)} {r : ℕ} {acc : Val} (h : LoopInv ρ ℓ R X Y r acc) :
    acc.wt ≤ preW n := by
  rcases h with ⟨rfl, -⟩ | ⟨T, gs, rfl, hgs, -, -⟩
  · have := wt_lit [] (c := 0) (by simp)
    simp only [List.length_nil] at this
    have := WB_ge n
    have := WB_le_VB n
    simp only [preW]
    omega
  · exact acc_wt hS _ hgs

/-- The cost of the loop. -/
noncomputable def iterC (h : Membership) (S n : ℕ) : ℕ :=
  n * stepC h S n + loopModK * (n + 1) * (3 * preW n + n + 1)

/-- The budget of `ri`. -/
noncomputable def riT (h : Membership) (S n : ℕ) : ℕ :=
  2 * levC n + rankC n + iterC h S n + preW n

/-- The bound of `ri`. -/
noncomputable def riC (h : Membership) (S n : ℕ) : ℕ := 10000000 * riT h S n

theorem riCtx_wt (hS : Sz n D) (X Y : SimpleGraph (Fin n)) : (riCtx D X Y).wt ≤ 9 * (2 * WB n + 1) + 4 := by
  have h0 := WB_ge n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have wX := adjVal_wt X
  have wY := adjVal_wt Y
  have wn : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  have wDn : (Val.nat D).wt ≤ WB n := nat_wt (by have := hS.le; omega)
  have wm : (Val.nat (n * D)).wt ≤ WB n := nat_wt (by omega)
  have wk : (Val.nat (n * D * (n * D))).wt ≤ WB n := nat_wt (by omega)
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wj : (ids (n * D)).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wK : (ids (n * D * (n * D))).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  exact wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption)

set_option maxHeartbeats 4000000 in
/-- **Rooted isomorphism.** -/
theorem ri_spec {P : Program} {b fd j S : ℕ} (h : Membership) (hP : P.HasAt b (riFuns b fd j))
    (hj : P.prims[j]? = some (membershipPrim h)) (hSol : SolverAt P fd D (n * D * (n * D)) S)
    (hS : Sz n D) (X Y : SimpleGraph (Fin n)) (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D)
    (v w : Fin n) :
    FunAll P b (.list [riCtx D X Y, .nat v, .nat w]) fun out cost =>
      RIOut X v Y w out ∧ cost ≤ riC h S n := by
  classical
  have hM : P.funs[b]? = some (riMainE b) := hP.left.left.left.left.single
  have hLv : P.HasAt (b + 1) (levFuns (b + 1)) := hP.left.left.left.right
  have hRk : P.HasAt (b + 18) (rankFuns (b + 18)) := hP.left.left.right
  have hIt : P.HasAt (b + 39) (iterFuns (b + 39) (b + 42)) := hP.left.right
  have hSt : P.HasAt (b + 42) (stepFuns (b + 42) fd j) := hP.right
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have hlB : levB n ≤ WB n := levB_le_WB n
  have wc := riCtx_wt hS X Y
  have wv : (Val.nat v).wt ≤ WB n := fin_wt (by have := le_kB n; omega) v
  have ww : (Val.nat w).wt ≤ WB n := fin_wt (by have := le_kB n; omega) w
  set ℓ := lev X v with hℓ
  set lY := lev Y w with hlY
  have hℓn : ∀ u, ℓ u ≤ n := lev_le X v
  have hlYn : ∀ u, lY u ≤ n := lev_le Y w
  have wL : (encFun ℓ).wt ≤ WB n := table_wt (by have := le_kB n; omega) hℓn
  have wLY : (encFun lY).wt ≤ WB n := table_wt (by have := le_kB n; omega) hlYn
  have wR0 : (encFun (rhoN ℓ lY)).wt ≤ WB n :=
    table_wt (by have := le_kB n; omega) (rhoN_le ℓ lY)
  set ok : ℕ := if ∃ u, rhoN ℓ lY u = n then 1 else 0 with hok
  have wok : (Val.nat ok).wt ≤ WB n := nat_wt (by simp only [hok]; split <;> omega)
  set R := Val.list [encFun (rhoN ℓ lY), .nat ok] with hR
  have wRR : R.wt ≤ 2 * (2 * WB n + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl) <;> omega)
  set A := Val.list [riCtx D X Y, .nat v, .nat w] with hA
  have wA : A.wt ≤ 3 * (2 * (9 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl) <;> omega)
  have hpre : 2 * A.wt + 100 + 4 * VB n ≤ preW n := by
    simp only [preW]
    omega
  set T := riT h S n with hT
  have hTp : preW n + 2 * levC n + rankC n ≤ T := by simp only [hT, riT]; omega
  have ga : ∀ rest {i : ℕ} {x : Val}, [riCtx D X Y, .nat v, .nat w][i]? = some x → i ≤ 2 →
      Lv P (A :: rest) T (arg i) x 1 := fun rest i x hx hi =>
    Lv.arg hx (by change 2 * A.wt + i + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ i, i ≤ 8 → Lv P env T (.nat i) (.nat i) 1 := fun env i hi =>
    Lv.nat i (by omega)
  have gc : ∀ rest (i : ℕ) {x : Val}, [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))][i]? = some x → i ≤ 8 →
      Lv P (A :: rest) T (.get (arg 0) (.nat i)) x _ := fun rest i x hx hi =>
    Lv.get (vs := [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))]) (ga rest (i := 0) rfl (by omega))
      (n9 _ i hi) hx
  have cX := Lv.mono (Lv.call (Lv.mk4 (gc [] 0 rfl (by omega)) (gc [] 2 rfl (by omega))
    (gc [] 3 rfl (by omega)) (ga [] (i := 1) rfl (by omega)) (by omega)) (lev_spec hLv X v)
    (by omega)) (show _ ≤ 1000 by norm_num)
  have cY := Lv.mono (Lv.call (Lv.mk4 (gc [encFun ℓ] 1 rfl (by omega)) (gc _ 2 rfl (by omega))
    (gc _ 3 rfl (by omega)) (ga _ (i := 2) rfl (by omega)) (by omega)) (lev_spec hLv Y w)
    (by omega)) (show _ ≤ 1000 by norm_num)
  have cR := Lv.mono (Lv.call (Lv.mk4 (Lv.var (env := [A, encFun ℓ, encFun lY]) (i := 1) rfl
    (by omega)) (Lv.var (env := [A, encFun ℓ, encFun lY]) (i := 2) rfl (by omega))
    (gc _ 3 rfl (by omega)) (gc _ 2 rfl (by omega)) (by omega)) (rank_spec hRk hℓn hlYn)
    (by omega)) (show _ ≤ 1000 by norm_num)
  refine FunAll.intro hM (EvalAll.letE cX fun x1 c1 hx1 => ?_)
  obtain ⟨rfl, hc1⟩ := hx1
  refine EvalAll.letE cY fun x2 c2 hx2 => ?_
  obtain ⟨rfl, hc2⟩ := hx2
  refine EvalAll.letE cR fun x3 c3 hx3 => ?_
  obtain ⟨rfl, hc3⟩ := hx3
  set E := [A, encFun ℓ, encFun lY, R] with hE
  have v3 : Lv P E T (.var 3) R 1 := Lv.var rfl (by omega)
  have gok := Lv.mono (Lv.get (vs := [encFun (rhoN ℓ lY), .nat ok]) v3 (n9 _ 1 (by omega)) rfl)
    (show _ ≤ 100 by norm_num)
  refine EvalAll.ite gok (fun vc cc hc => ⟨ok, hc.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  obtain rfl : x = ok := by injection hx
  by_cases hex : ∃ u, rhoN ℓ lY u = n
  · -- no map keeps the levels
    have e1 : ok = 1 := if_pos hex
    rw [if_neg (show ok ≠ 0 by omega)]
    refine Det.post (Lv.mono (Lv.nil (P := P) (env := E) (T := T) (by omega))
      (show 1 ≤ 1 by norm_num)) fun c' hc' => ⟨Or.inl ⟨rfl, fun g hg => ?_⟩, ?_⟩
    · obtain ⟨u, hu⟩ := hex
      have := rhoN_lt (g := g) (lX := ℓ) (lY := lY) hg.lev_eq u
      omega
    · have := wt_lit [] (c := 0) (by simp)
      simp only [List.length_nil] at this
      simp only [riC]
      omega
  · have e1 : ok = 0 := if_neg hex
    rw [if_pos e1]
    have hlt : ∀ u, rhoN ℓ lY u < n := fun u =>
      lt_of_le_of_ne (rhoN_le ℓ lY u) fun h' => hex ⟨u, h'⟩
    obtain ⟨ρ, hρ⟩ := exists_rhoPerm hlt
    have hρl : ∀ u, lY (ρ u) = ℓ u := fun u => (hρ u).2
    have hH : StepHyp ρ D ℓ (n - 1) X Y :=
      ⟨lev_hasLevels X v, (lev_hasLevels Y w).relabel hρl, dX ℓ, fun U u => dY ℓ U u,
        by omega, hS, hℓn⟩
    have eR : encFun (rhoN ℓ lY) = encPerm (ρ * 1) := by
      rw [mul_one, encPerm_eq_encFun]
      congr 1
      funext u
      exact (hρ u).1.symm
    have eG : Val.list [.nat n, .list [ids n]] = encGroup ([] : List (Perm (Fin n))) := by
      rw [ids_eq]
      rfl
    have hTi : iterC h S n ≤ T := by simp only [hT, riT]; omega
    have base := Lv.snoc (Lv.snoc (Lv.snoc (Lv.mk5 (gc [encFun ℓ, encFun lY, R] 2 rfl (by omega))
      (gc _ 4 rfl (by omega)) (gc _ 5 rfl (by omega)) (gc _ 6 rfl (by omega))
      (Lv.var (env := E) (i := 1) rfl (by omega)) (by omega)) (gc _ 3 rfl (by omega)) (by omega))
      (gc _ 7 rfl (by omega)) (by omega)) (gc _ 8 rfl (by omega)) (by omega)
    have ctx : Lv P E T _ (stepCtx D ℓ X Y) _ :=
      Lv.mk3 base (gc _ 0 rfl (by omega)) (gc _ 1 rfl (by omega)) (by omega)
    have kk := Lv.arith (op := .sub) (z := n - 1) (gc [encFun ℓ, encFun lY, R] 2 rfl (by omega))
      (n9 E 1 (by omega)) rfl (by omega)
    have gR := Lv.get (vs := [encFun (rhoN ℓ lY), .nat ok]) v3 (n9 _ 0 (by omega)) rfl
    have acc := Lv.mk2 gR (Lv.mk2 (gc [encFun ℓ, encFun lY, R] 2 rfl (by omega))
      (Lv.mk1 (gc [encFun ℓ, encFun lY, R] 3 rfl (by omega)) (by omega)) (by omega)) (by omega)
    rw [eR, eG] at acc
    have args := Lv.mono (Lv.mk3 ctx kk acc (by omega)) (show _ ≤ 1000000 by norm_num)
    refine EvalAll.call_funAll args fun va ca hva => ?_
    obtain ⟨rfl, hca⟩ := hva
    have h0inv : LoopInv ρ ℓ (n - 1) X Y 0 (.list [encPerm (ρ * 1), encGroup []]) :=
      Or.inr ⟨1, [], rfl, by simp, one_mem_ball_zero hH.hX, by rw [gens_nil, ballGroup_zero hH.hX]⟩
    have hit := iter_spec (c := stepCtx D ℓ X Y) (k := n - 1)
      (acc0 := .list [encPerm (ρ * 1), encGroup []]) hIt (Inv := LoopInv ρ ℓ (n - 1) X Y)
      (M := preW n) (B := fun _ => stepC h S n) h0inv (fun i acc _ hI => loopInv_wt hS hI)
      (fun i acc hi hI => step_spec h hSt hj hSol hH (by omega) hI)
    have wa := stepArg_wt hS hℓn (r := n - 1) (by omega) X Y (ρ * 1) (gs := []) (by simp)
    refine FunAll.mono hit fun out c hw => ⟨?_, ?_⟩
    · rcases hw.1 with ⟨rfl, hE⟩ | ⟨T', gs, rfl, hgs, hTb, hg⟩
      · refine Or.inl ⟨rfl, fun g hg => ?_⟩
        obtain ⟨T', hT'⟩ := hg.mem_ball (ρ := ρ) hρl
        rw [hE] at hT'
        exact hT'
      · exact Or.inr ⟨ρ * T', gs, rfl, rooted_of_mem_ball (fun a b => Iff.rfl) hρl hTb, hg, hgs⟩
    · have hwo := loopInv_wt hS hw.1
      have hc := hw.2
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
      have e1 : (n - 1) * stepC h S n ≤ n * stepC h S n := Nat.mul_le_mul_right _ (by omega)
      have e2 : loopModK * (n - 1 + 1) * ((Val.list [stepCtx D ℓ X Y, .nat (n - 1),
          .list [encPerm (ρ * 1), encGroup []]]).wt + (n - 1) + preW n + 1) ≤
          loopModK * (n + 1) * (3 * preW n + n + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have e3 : c ≤ iterC h S n := by simp only [iterC]; omega
      simp only [riC]
      omega

end GI.Degree
