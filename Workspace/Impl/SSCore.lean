import Workspace.Impl.SSRoundsProg

/-!
# The core program

`ssCoreF` runs `ssBuild` on the context `ssCtx B gs`: it makes the empty state, inserts the
generators and runs `|B| n + 1` rounds (`ssCoreF_spec`). `ssFuns b` lists all functions of the
core, from `b` on, and `SsCoreAt.of_hasAt` finds the parts in it.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The core: `c ↦ ssBuild`, on `c = ssCtx B gs`. -/
def ssCoreF (repl genIt roundsIt : ℕ) : Expr :=
  .letE (mk2 (.call repl (mk2 (.get (.var 0) (.nat 3)) .nil)) .nil)
    (.letE (.call genIt (mk3 (.var 0) (.arith .sub (.length (.get (.var 0) (.nat 2))) (.nat 1))
        (.var 1)))
      (.call roundsIt (mk3 (.var 0) (.arith .add (.get (.var 0) (.nat 3)) (.nat 1)) (.var 2))))

/-- All functions of the core, from `b` on. -/
def ssFuns (b : ℕ) : List Expr :=
  composeFuns b ++ (invFuns (b + 4) ++ (setFuns (b + 16) ++ (appendFuns (b + 19) ++
    (replicateFuns (b + 22) ++ (iterFuns (b + 25) (b + 28) ++ ([ssSiftStepF b (b + 4)] ++
    (foldlFuns (b + 29) (b + 32) ++ ([ssChainF] ++ ([ssInsertF (b + 25) (b + 29) (b + 16) (b + 19)] ++
    (iterFuns (b + 34) (b + 37) ++ ([ssGenStepF (b + 33)] ++ (iterFuns (b + 38) (b + 41) ++
    ([ssPairF (b + 33) b] ++ (iterFuns (b + 42) (b + 45) ++ ([ssRoundStepF (b + 38)] ++
    [ssCoreF (b + 22) (b + 34) (b + 42)])))))))))))))))

/-- The parts of the core. -/
structure SsCoreAt (P : Program) (b : ℕ) : Prop where
  core : P.funs[b + 46]? = some (ssCoreF (b + 22) (b + 34) (b + 42))
  repl : P.HasAt (b + 22) (replicateFuns (b + 22))
  gen : SsGenAt P (b + 34) (b + 33) (b + 25) (b + 29) (b + 16) (b + 19) b (b + 4)
  rounds : SsRoundsAt P (b + 42) (b + 38) (b + 33) (b + 25) (b + 29) (b + 16) (b + 19) b (b + 4)

theorem SsCoreAt.of_hasAt {P : Program} {b : ℕ} (h : P.HasAt b (ssFuns b)) : SsCoreAt P b := by
  unfold ssFuns at h
  have hc := h.left
  have h1 := h.right; rw [show (composeFuns b).length = 4 from rfl] at h1
  have hi := h1.left
  have h2 := h1.right; rw [show (invFuns (b + 4)).length = 12 from rfl,
    show b + 4 + 12 = b + 16 by omega] at h2
  have hs := h2.left
  have h3 := h2.right; rw [show (setFuns (b + 16)).length = 3 from rfl,
    show b + 16 + 3 = b + 19 by omega] at h3
  have ha := h3.left
  have h4 := h3.right; rw [show (appendFuns (b + 19)).length = 3 from rfl,
    show b + 19 + 3 = b + 22 by omega] at h4
  have hr := h4.left
  have h5 := h4.right; rw [show (replicateFuns (b + 22)).length = 3 from rfl,
    show b + 22 + 3 = b + 25 by omega] at h5
  have hsi := h5.left
  have h6 := h5.right; rw [show (iterFuns (b + 25) (b + 28)).length = 3 from rfl,
    show b + 25 + 3 = b + 28 by omega] at h6
  have hss := h6.left.single
  have h7 := h6.right; rw [show [ssSiftStepF b (b + 4)].length = 1 from rfl,
    show b + 28 + 1 = b + 29 by omega] at h7
  have hch := h7.left
  have h8 := h7.right; rw [show (foldlFuns (b + 29) (b + 32)).length = 3 from rfl,
    show b + 29 + 3 = b + 32 by omega] at h8
  have hchs := h8.left.single
  have h9 := h8.right; rw [show [ssChainF].length = 1 from rfl,
    show b + 32 + 1 = b + 33 by omega] at h9
  have hins := h9.left.single
  have h10 := h9.right; rw [show [ssInsertF (b + 25) (b + 29) (b + 16) (b + 19)].length = 1 from rfl,
    show b + 33 + 1 = b + 34 by omega] at h10
  have hgi := h10.left
  have h11 := h10.right; rw [show (iterFuns (b + 34) (b + 37)).length = 3 from rfl,
    show b + 34 + 3 = b + 37 by omega] at h11
  have hgs := h11.left.single
  have h12 := h11.right; rw [show [ssGenStepF (b + 33)].length = 1 from rfl,
    show b + 37 + 1 = b + 38 by omega] at h12
  have hri := h12.left
  have h13 := h12.right; rw [show (iterFuns (b + 38) (b + 41)).length = 3 from rfl,
    show b + 38 + 3 = b + 41 by omega] at h13
  have hps := h13.left.single
  have h14 := h13.right; rw [show [ssPairF (b + 33) b].length = 1 from rfl,
    show b + 41 + 1 = b + 42 by omega] at h14
  have hrsi := h14.left
  have h15 := h14.right; rw [show (iterFuns (b + 42) (b + 45)).length = 3 from rfl,
    show b + 42 + 3 = b + 45 by omega] at h15
  have hrs := h15.left.single
  have h16 := h15.right; rw [show [ssRoundStepF (b + 38)].length = 1 from rfl,
    show b + 45 + 1 = b + 46 by omega] at h16
  have hcore := h16.single
  have hsift : SsSiftAt P (b + 25) b (b + 4) := ⟨hsi, hss, hc, hi⟩
  have hinsAt : SsInsAt P (b + 33) (b + 25) (b + 29) (b + 16) (b + 19) b (b + 4) :=
    ⟨hins, hsift, hch, hchs, hs, ha⟩
  exact ⟨hcore, hr, ⟨hgi, hgs, hinsAt⟩, ⟨hrsi, hrs, ⟨hri, hps, hinsAt⟩⟩⟩

/-- The cost of the core. -/
def ssCoreCost (Y : ℕ) : ℕ := 10 ^ 8 * (ssW Y + 1) ^ 4

theorem ss_core_cost {W0 E c1 A1 M : ℕ}
    (h1 : c1 ≤ loopModK * (M + 1) * (A1 + M + W0 + 1)) (hA1 : A1 ≤ W0) (hM : M ≤ W0)
    (hE : E ≤ c1 + ((2 * 10 ^ 7 + 9000) * (W0 + 1) ^ 3 + (3 * 10 ^ 7 + 9000) * (W0 + 1) ^ 4)) :
    E + 300 * (10 * W0 + 10 + 1) ≤ 10 ^ 8 * (W0 + 1) ^ 4 := by
  unfold loopModK at h1
  have m1 : 1000 * (M + 1) * (A1 + M + W0 + 1) ≤ 3000 * ((W0 + 1) ^ 2) := by
    calc 1000 * (M + 1) * (A1 + M + W0 + 1) ≤ 1000 * (W0 + 1) * (3 * (W0 + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 3000 * ((W0 + 1) ^ 2) := by ring
  generalize hV : W0 + 1 = V at *
  have q1 : V ≤ V ^ 2 := by nlinarith
  have q2 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q3 : V ^ 3 ≤ V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  generalize V ^ 2 = Q2 at *
  generalize V ^ 3 = Q3 at *
  generalize V ^ 4 = Q4 at *
  linarith

/-- **The core.** -/
theorem ssCoreF_spec {P : Program} {b : ℕ} (hP : SsCoreAt P b) {B : List (Fin n)}
    {gs : List (Perm (Fin n))} {Y : ℕ} (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P (b + 46) (ssCtx B gs) (ssEncSt (ssBuild B gs)) (ssCoreCost Y) := by
  obtain ⟨hMM, hG, -, h1000⟩ := ss_W_facts hY
  obtain ⟨-, hTY, -, hY3, hZ⟩ := ss_Y_facts hY
  have hZW := ssZ_le_ssW Y
  have hMT : B.length * n ≤ B.length * n * (2 * n + 8) := Nat.le_mul_of_pos_right _ (by omega)
  have hinv0 : SsInv B gs (ssInit B) := ssInv_init
  have hinv1 := (ssGens_spec hinv0).1
  have hc := ss_ctx_wt hY
  have hs0 := ss_st_wt hinv0 hY
  have hs1 := ss_st_wt hinv1 hY
  have hs2 := ss_st_wt (ssBuild_spec (B := B) (gs := gs)).1 hY
  have hMW : B.length * n + 1 + 2 ≤ ssW Y := by
    rcases Nat.lt_or_ge (B.length * n) 2 with h | h
    · omega
    · have := Nat.mul_le_mul_right (B.length * n) h; omega
  set W := 10 * ssW Y + 10 with hW
  clear_value W
  set M := B.length * n with hM
  -- the empty state
  have hinit : ssEncSt (ssInit B) = .list [.list (List.replicate M (.list [])), .list []] := by
    simp [ssEncSt, ssInit, ssEncTab, ssEncProg, ssEncSlot, List.map_replicate, hM]
  have hrepW : (Val.list (List.replicate M (Val.list []))).wt ≤ ssW Y := by
    have := hs0; rw [hinit] at this
    exact (le_of_lt (wt_le_wt_list (by simp))).trans this
  have hcW : (ssCtx B gs).wt ≤ W := by omega
  have dC : ∀ rest : List Val, StDC P (ssCtx B gs :: rest) (.var 0) (ssCtx B gs) 1 0 W :=
    fun rest => StDC.var' rfl hcW
  have dM : ∀ rest, StDC P (ssCtx B gs :: rest) (.get (.var 0) (.nat 3)) (.nat M) 3 0 W :=
    fun rest => StDC.get (v := .nat M) (x := 3) (dC rest) (StDC.nat 3 (by omega)) rfl
      ((wt_nat_le _).trans (by omega))
  have hrep := replicate_spec hP.repl M (.list [])
  have hrepD : FunDet P (b + 22) (.list [.nat M, .list []]) (.list (List.replicate M (.list [])))
      (loopModK * (M + 1) * ((Val.list [.nat M, .list []]).wt + M + ssW Y + 1)) :=
    hrep.mono fun w c ⟨hw, hc⟩ => ⟨hw, hc.trans (by rw [hw]; exact Nat.mul_le_mul_left _ (by omega))⟩
  have hA1 : (Val.list [.nat M, .list []]).wt ≤ ssW Y := by
    refine (ssSmall_list (Z := ssZ Y) ?_ fun v hv => ?_).wt_le
    · rw [size_list_eq]; simp [size_list_eq]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ssSmall_nat (by omega) (by omega)
      · exact ssSmall_list (by simp [size_list_eq]; omega) (by simp)
  have hnilW : (Val.list []).wt ≤ W :=
    (le_of_lt (wt_le_wt_list (show Val.list [] ∈ [Val.nat M, Val.list []] by simp))).trans
      (by omega)
  have dRep := StDC.call (StDC.mk2 (dM []) (StDC.nil (by omega)) (by omega) (by omega)) hrepD
    (by omega)
  have dS0 := StDC.mk2 dRep (StDC.nil (by omega)) (by rw [← hinit]; omega) (by omega)
  rw [← hinit] at dS0
  -- the generators
  have hgl : ((1 :: gs).map encPerm).length = gs.length + 1 := by simp
  have dG : StDC P [ssCtx B gs, ssEncSt (ssInit B)]
      (.arith .sub (.length (.get (.var 0) (.nat 2))) (.nat 1)) (.nat gs.length) 6 0 W := by
    have d := StDC.length (StDC.get (v := .list ((1 :: gs).map encPerm)) (x := 2) (dC [ssEncSt (ssInit B)])
      (StDC.nat 2 (by omega)) rfl (by
        have := (le_of_lt (wt_le_wt_list (show Val.list ((1 :: gs).map encPerm) ∈
          [.nat n, ssEncB B, .list ((1 :: gs).map encPerm), .nat (B.length * n)] by simp))).trans
          hc
        omega)) (by rw [hgl]; omega)
    rw [hgl] at d
    exact (StDC.arith (op := .sub) (z := gs.length) d (StDC.nat 1 (by omega)) (by simp)
      ((wt_nat_le _).trans (by omega))).mono (by omega) le_rfl
  have dA2 := StDC.mk3 (dC _) dG (StDC.var' (env := [ssCtx B gs, ssEncSt (ssInit B)]) (i := 1)
    rfl (by omega)) ((st_wt_list3 hc ((wt_nat_le _).trans (by omega)) hs0).trans (by omega))
    (by omega)
  have dS1 := StDC.call dA2 (ssGensLoop_spec hP.gen hinv0 hY) (by omega)
  -- the rounds
  have dR : StDC P [ssCtx B gs, ssEncSt (ssInit B), ssEncSt (ssGens B gs (ssInit B))]
      (.arith .add (.get (.var 0) (.nat 3)) (.nat 1)) (.nat (M + 1)) 5 0 W :=
    StDC.arith (op := .add) (dM _) (StDC.nat 1 (by omega)) rfl ((wt_nat_le _).trans (by omega))
  have dA3 := StDC.mk3 (dC _) dR (StDC.var' (env := [ssCtx B gs, ssEncSt (ssInit B),
    ssEncSt (ssGens B gs (ssInit B))]) (i := 2) rfl (by omega))
    ((st_wt_list3 hc ((wt_nat_le _).trans (by omega)) hs1).trans (by omega)) (by omega)
  have dS2 := StDC.call dA3 (ssRoundsLoop_spec hP.rounds hinv1 hY) (by
    show (ssEncSt (ssBuild B gs)).wt ≤ W; omega)
  refine StDC.funDet hP.core (StDC.letE dS0 (StDC.letE dS1 dS2 (by
    show (ssEncSt (ssBuild B gs)).wt ≤ W; omega)) (by
    show (ssEncSt (ssBuild B gs)).wt ≤ W; omega)) (ss_cost_fin2 (by norm_num) ?_)
  unfold ssCoreCost
  rw [hW]
  refine ss_core_cost (M := M) (A1 := (Val.list [.nat M, .list []]).wt) le_rfl hA1 (by omega) ?_
  simp only [Nat.zero_add, Nat.add_zero, ssGensCost, ssRoundsCost]
  omega

end GI.Impl
