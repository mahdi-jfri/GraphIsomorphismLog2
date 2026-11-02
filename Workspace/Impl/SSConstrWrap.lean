import Workspace.Impl.SSConstrBase

/-!
# Constructive membership

`ssCmF` outputs `[1, prog]`. With no generators, `prog` is empty (then `x = 1`). Otherwise it
builds the table for the base `[0, …, n-1]`, sifts `x`, and outputs `ssConstrProg`: the table
program, the chain of the used entries, and one inversion (`ssCmF_spec`). By
`ss_constr_reaches` the program reaches `x` when `x ∈ ⟨gs⟩`. The program is
`ssWrapProgram [ssCmF 51 29 19]`, with `ssCmF` at `52`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The first three instructions of the local part, at program length `N`. -/
def ssCmInit (N : Expr) : Expr :=
  mk3 (mk2 (.nat 0) (.nat 0)) (mk2 (.nat 1) N) (mk3 (.nat 2) (.arith .add N (.nat 1)) N)

/-- The branch with generators: the table, the sift, and `ssConstrProg`. -/
def ssCmT (stsift chain app : ℕ) : Expr :=
  .letE (.call stsift (.var 0))
    (.letE (.get (.get (.var 1) (.nat 0)) (.nat 1))
      (.letE (.call chain (mk3 (.length (.var 2)) (.get (.get (.var 1) (.nat 1)) (.nat 1))
          (ssCmInit (.length (.var 2)))))
        (mk2 (.nat 1) (.snoc (.call app (mk2 (.var 2) (.var 3)))
          (mk2 (.nat 1) (.arith .sub (.arith .add (.length (.var 2)) (.length (.var 3)))
            (.nat 1)))))))

/-- Constructive membership on `[encGroup gs, encPerm x]`. -/
def ssCmF (stsift chain app : ℕ) : Expr :=
  .ite (.arith .sub (.length (.get (.get (.var 0) (.nat 0)) (.nat 1))) (.nat 1))
    (ssCmT stsift chain app) (mk2 (.nat 1) .nil)

/-- The program length is a power of the number of input cells. -/
theorem ss_cm_len {s w L u m : ℕ} (hs : 2 ≤ s) (hw : w ≤ s * (s + 2))
    (hL : L ≤ 3 * (3 * (w + 1)) ^ 3) (hu : u ≤ m) (hm : m ≤ w) :
    L + 4 + 2 * u ≤ s ^ 20 := by
  have h1 : 3 * (w + 1) ≤ 3 * (s + 1) ^ 2 := by nlinarith
  have h2 : (3 * (w + 1)) ^ 3 ≤ (3 * (s + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (s + 1) ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h4 : (3 * (s + 1) ^ 2) ^ 3 ≤ (3 * (2 * s) ^ 2) ^ 3 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h3) 3
  have e : (3 * (2 * s) ^ 2) ^ 3 = 1728 * s ^ 6 := by ring
  have h5 : 2 ^ 14 ≤ s ^ 14 := Nat.pow_le_pow_left hs 14
  have e2 : s ^ 20 = s ^ 14 * s ^ 6 := by ring
  have h6 : 2 ^ 14 * s ^ 6 ≤ s ^ 14 * s ^ 6 := Nat.mul_le_mul_right _ h5
  have h7 : s * (s + 2) + 1 ≤ s ^ 6 := by
    have : s * (s + 2) + 1 ≤ 4 * s ^ 2 := by nlinarith
    have h8 : 4 * s ^ 2 ≤ s ^ 2 * s ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
    have h9 : s ^ 2 * s ^ 2 ≤ s ^ 6 := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  rw [e2]
  rw [e] at h4
  omega

theorem ss_cm_cost {X W k E C c1 c2 A B l A' B' : ℕ} (hC : C = 10 ^ 8 * (X + 1) ^ 4)
    (hW : W = 40 * X + 50) (hk : k ≤ 300) (hE : E ≤ 4 * C + c1 + c2)
    (h1 : c1 ≤ 5000 * (A + B + 1) ^ 2) (hA : A ≤ W) (hB : B ≤ W)
    (h2 : c2 ≤ 1000 * (l + 1) * (A' + l + B' + 1)) (hl : l ≤ W) (hA' : A' ≤ W) (hB' : B' ≤ W) :
    k * (W + 1) + E ≤ 100 * C := by
  have q1 : (A + B + 1) ^ 2 ≤ (101 * (X + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q2 : 1000 * (l + 1) * (A' + l + B' + 1) ≤ 1000 * (51 * (X + 1)) * (151 * (X + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have q3 : k * (W + 1) ≤ 300 * (51 * (X + 1)) := Nat.mul_le_mul hk (by omega)
  have e1 : (101 * (X + 1)) ^ 2 = 10201 * (X + 1) ^ 2 := by ring
  have e2 : 1000 * (51 * (X + 1)) * (151 * (X + 1)) = 7701000 * (X + 1) ^ 2 := by ring
  have r1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have r2 : (X + 1) ^ 2 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [e1] at q1
  rw [e2] at q2
  subst hC
  generalize (X + 1) ^ 2 = Q2 at *
  generalize (X + 1) ^ 4 = Q4 at *
  have := Nat.mul_le_mul_left 5000 q1
  omega

theorem ss_gens_nil_eq {x : Perm (Fin n)} (hx : x ∈ gens ([] : List (Perm (Fin n)))) : x = 1 := by
  simpa [gens] using hx

/-- **Constructive membership.** -/
theorem ssCmF_spec {P : Program} (hw : SsWrapAt P) (hf : P.funs[52]? = some (ssCmF 51 29 19))
    (gs : List (Perm (Fin n))) (x : Perm (Fin n)) (hx : x ∈ gens gs) :
    FunAll P 52 (.list [encGroup gs, encPerm x]) (fun v c =>
      (∃ prog : List SlpInstr, v = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
        prog.length ≤ (Val.list [encGroup gs, encPerm x]).cells.length ^ 20 ∧
        SlpReaches gs prog x) ∧
      c ≤ 10 * ssPolyK * ((Val.list [encGroup gs, encPerm x]).wt + 1) ^ 32) := by
  set w := (Val.list [encGroup gs, encPerm x]).wt with hwdef
  set s := (Val.list [encGroup gs, encPerm x]).cells.length with hsdef
  have hs2 : 2 ≤ s := (Val.list [encGroup gs, encPerm x]).two_le_size
  have hcells : ∀ a ∈ (Val.list [encGroup gs, encPerm x]).cells, a ≤ s + 1 := fun a ha => by
    have := ss_list_cells (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ss_encGroup_cells_le (by simp)
      · exact ss_encPerm_cells_le x (by simp)) a ha
    rw [size_eq_length] at this
    simpa only [one_mul, pow_one] using this
  have hws : w ≤ s * (s + 2) := wt_le_of_cells_le hcells
  have hY := ss_wrap_Y (gs := gs) (vs := [encGroup gs, encPerm x]) (by simp)
  rw [← hwdef] at hY
  have hnw' : n < w := (ss_encGroup_wt gs).1.trans (wt_le_wt_list (by simp))
  set Y := 3 * (w + 1) with hYdef
  have hss := ssStSiftF_spec hw.stsift hw.range hw.start hw.core x hY
  have hY' : n + (List.finRange n).length + gs.length + 2 ≤ Y := by
    rw [List.length_finRange]; exact hY
  obtain ⟨hinv, -, -⟩ := ssBuild_spec (B := List.finRange n) (gs := gs)
  have hsm := ssInv_small hinv hY'
  have hsw := ss_st_wt hinv hY'
  have hx0 := (ss_mem_correct gs x).mpr hx
  obtain ⟨-, -, -, hY3, hZ⟩ := ss_Y_facts hY'
  have hZW := ssZ_le_ssW Y
  have hYW := (ss_le_core (Y := Y) (by omega)).1
  have facts := ssSift_acc_facts (List.finRange n) (ssBuild (List.finRange n) gs).1 hsm.idx x
    (List.finRange n).length
  have hfold : (List.range (List.finRange n).length).foldl
    (ssSiftStep (List.finRange n) (ssBuild (List.finRange n) gs).1) (x, [], 0) =
      ssSift (List.finRange n) (ssBuild (List.finRange n) gs).1 x := rfl
  rw [hfold, List.length_finRange] at facts
  have hR := (ssSmall_acc (Z := ssZ Y) (ssSift (List.finRange n) (ssBuild (List.finRange n) gs).1 x)
    facts.2.1 (facts.2.2.trans (by omega)) (by have := facts.1; omega)).wt_le_ssW
  have hreach : 0 < gs.length → SlpReaches gs (ssConstrProg (ssBuild (List.finRange n) gs).2
      (ssSift (List.finRange n) (ssBuild (List.finRange n) gs).1 x).2.1) x := fun hg =>
    ss_constr_reaches hinv (fun i => List.mem_finRange i) hg hx0
  generalize ssSift (List.finRange n) (ssBuild (List.finRange n) gs).1 x = r
    at hss hR hx0 facts hreach
  generalize ssBuild (List.finRange n) gs = st at hss hinv hsm hsw hreach
  obtain ⟨T, prog⟩ := st
  obtain ⟨g', used, stop⟩ := r
  simp only at hx0 facts hreach
  subst hx0
  set X := ssW Y with hX
  set W := 40 * X + 50 with hW
  clear_value W
  set a := Val.list [.list [.nat n, .list ((1 :: gs).map encPerm)], encPerm x] with ha
  have haw : a.wt = w := rfl
  have haW : a.wt ≤ W := by omega
  have hgl : ((1 :: gs).map encPerm).length = gs.length + 1 := by simp
  have hGw : (Val.list ((1 :: gs).map encPerm)).wt ≤ W := by
    have h1 : (Val.list ((1 :: gs).map encPerm)).wt <
        (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt := wt_le_wt_list (by simp)
    have h2 : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt < a.wt :=
      wt_le_wt_list (by simp)
    omega
  have dc0 := StDC.length (StDC.get (x := 1) (v := .list ((1 :: gs).map encPerm))
    (StDC.get (x := 0) (v := .list [.nat n, .list ((1 :: gs).map encPerm)])
      (StDC.var' (P := P) (env := [a]) (i := 0) (v := a) rfl haW) (StDC.nat 0 (by omega)) rfl
      (by have : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt < a.wt :=
            wt_le_wt_list (by simp)
          omega)) (StDC.nat 1 (by omega)) rfl hGw) (by
    have := length_lt_wt_list ((1 :: gs).map encPerm); omega)
  rw [hgl] at dc0
  have dc := StDC.arith (op := .sub) (z := gs.length) dc0 (StDC.nat 1 (by omega)) (by simp)
    ((wt_nat_le _).trans (by omega))
  have hC : ssCoreCost Y = 10 ^ 8 * (X + 1) ^ 4 := rfl
  have hn1 : (Val.nat 1).wt ≤ X := (wt_nat_le 1).trans (by omega)
  have hnil : (Val.list []).wt ≤ X := by
    have : (Val.list []).wt ≤ 4 := by decide
    omega
  by_cases hg : gs.length = 0
  · -- no generators: the empty program
    have hgs : gs = [] := List.eq_nil_of_length_eq_zero hg
    have dOut := StDC.mk2 (P := P) (env := [a]) (W := W) (StDC.nat 1 (by omega))
      (StDC.nil (by omega)) ((st_wt_list2 hn1 hnil).trans (by omega)) (by omega)
    have dTop := StDC.ite (t := ssCmT 51 29 19) (nt := 0) (Et := 0) dc (fun h => absurd hg h)
      (fun _ => dOut)
      ((st_wt_list2 hn1 hnil).trans (by omega))
    refine FunAll.mono (StDC.funDet (c := 100 * ssCoreCost Y) hf dTop
      (ss_cm_cost (c1 := 0) (c2 := 0) (A := 0) (B := 0) (l := 0) (A' := 0) (B' := 0) hC hW
        (by norm_num) (by omega) (by norm_num) (by omega) (by omega) (by norm_num) (by omega)
        (by omega) (by omega))) fun v c ⟨hv, hc⟩ => ⟨⟨[], hv, by simp, ?_⟩, ss_wrap_cost hc⟩
    subst hgs
    have := ss_gens_nil_eq hx
    subst this
    exact ⟨[], rfl, rfl⟩
  -- the table, the sift and the program
  have hRw : (Val.list [ssEncSt (T, prog), ssEncAcc (g', used, 0)]).wt ≤ 4 * X + 6 :=
    st_wt_list2 hsw hR
  set R := Val.list [ssEncSt (T, prog), ssEncAcc (g', used, 0)] with hRdef
  have dR : StDC P [a] (.call 51 (.var 0)) R (1 + 1) (0 + 4 * ssCoreCost Y) W :=
    StDC.call (StDC.var' (i := 0) (v := a) rfl haW) hss (hRw.trans (by omega))
  have hPw : (ssEncProg prog).wt ≤ X := hsm.prog.wt_le_ssW
  have hSt : (Val.list [ssEncTab T, ssEncProg prog]).wt ≤ X := hsw
  have hAc : (Val.list [encPerm g', natList used, .nat 0]).wt ≤ X := hR
  have hUw : (natList used).wt ≤ X := by
    have : (natList used).wt < (Val.list [encPerm g', natList used, .nat 0]).wt :=
      wt_le_wt_list (by simp)
    omega
  have hN : prog.length ≤ 3 * Y ^ 3 := hsm.plen'
  have hul : used.length ≤ n := facts.1
  have hins := ss_constr_insMax prog used (M := ssZ Y) hsm.ins facts.2.1 (by omega)
  have hlocl := length_ssConstrLoc prog.length used
  have hfl := length_ssConstrProg prog used
  have hsmall : ∀ q : List SlpInstr, (∀ ins ∈ q, ins ∈ ssConstrProg prog used) →
      q.length ≤ (ssConstrProg prog used).length → (ssEncProg q).wt ≤ X := fun q hq hl =>
    (ssSmall_prog (fun ins h => hins ins (hq ins h)) (by omega) (by omega)).wt_le_ssW
  have hLw : (ssEncProg (ssConstrLoc prog.length used)).wt ≤ X :=
    hsmall _ (fun ins h => List.mem_append_left _ (List.mem_append_right _ h)) (by omega)
  have hAw : (ssEncProg (prog ++ ssConstrLoc prog.length used)).wt ≤ X :=
    hsmall _ (fun ins h => List.mem_append_left _ h) (by rw [List.length_append]; omega)
  have hFw : (ssEncProg (ssConstrProg prog used)).wt ≤ X := hsmall _ (fun _ h => h) le_rfl
  set N := prog.length with hNdef
  set loc := ssConstrLoc N used with hloc
  have hNw : ∀ k, k ≤ N + 2 → (Val.nat k).wt ≤ X := fun k hk => (wt_nat_le k).trans (by omega)
  -- the program of the table
  set e1 := [a, R] with he1
  have dP : StDC P e1 (.get (.get (.var 1) (.nat 0)) (.nat 1)) (ssEncProg prog) 5 0 W :=
    StDC.get (x := 1) (v := ssEncProg prog) (StDC.get (x := 0)
      (v := .list [ssEncTab T, ssEncProg prog]) (StDC.var' (i := 1) (v := R) rfl
        (hRw.trans (by omega))) (StDC.nat 0 (by omega)) rfl (by omega))
      (StDC.nat 1 (by omega)) rfl (by omega)
  have dN : ∀ rest, StDC P ([a, R, ssEncProg prog] ++ rest) (.length (.var 2)) (.nat N) 2 0 W :=
    fun rest => by
      have := StDC.length (vs := prog.map encSlpInstr) (StDC.var' (P := P) (W := W)
        (env := [a, R, ssEncProg prog] ++ rest) (i := 2) (v := ssEncProg prog) rfl
        (by omega)) (by rw [List.length_map]; omega)
      rw [List.length_map] at this
      exact this
  set e2 := [a, R, ssEncProg prog] with he2
  have dU : StDC P e2 (.get (.get (.var 1) (.nat 1)) (.nat 1)) (natList used) 5 0 W :=
    StDC.get (x := 1) (v := natList used) (StDC.get (x := 1)
      (v := .list [encPerm g', natList used, .nat 0]) (StDC.var' (i := 1) (v := R) rfl
        (hRw.trans (by omega))) (StDC.nat 1 (by omega)) rfl (by omega))
      (StDC.nat 1 (by omega)) rfl (by omega)
  have dN2 : StDC P e2 (.length (.var 2)) (.nat N) 2 0 W := by
    simpa using dN []
  have h00 := st_wt_list2 (hNw 0 (by omega)) (hNw 0 (by omega))
  have h1N := st_wt_list2 hn1 (hNw N (by omega))
  have h2N := st_wt_list3 (hNw 2 (by omega)) (hNw (N + 1) (by omega)) (hNw N (by omega))
  have hpre : ∀ (L : List ℕ) (l0 : List SlpInstr), l0 <+: L.foldl (ssChain N) l0 := by
    intro L
    induction L with
    | nil => intro l0; exact List.prefix_refl _
    | cons u L ih => intro l0; exact (List.prefix_append _ _).trans (ih _)
  have hIw : (Val.list [.list [.nat 0, .nat 0], .list [.nat 1, .nat N],
      .list [.nat 2, .nat (N + 1), .nat N]]).wt ≤ X :=
    hsmall [.gen 0, .inv N, .mul (N + 1) N] (fun ins h => List.mem_append_left _
      (List.mem_append_right _ ((hpre used _).subset h))) (by
        show 3 ≤ _; rw [hfl]; omega)
  have dI := StDC.mk3 (StDC.mk2 (StDC.nat 0 (by omega)) (StDC.nat 0 (by omega))
      (h00.trans (by omega)) (by omega))
    (StDC.mk2 (StDC.nat 1 (by omega)) dN2 (h1N.trans (by omega)) (by omega))
    (StDC.mk3 (StDC.nat 2 (by omega)) (StDC.arith (op := .add) (z := N + 1) dN2
      (StDC.nat 1 (by omega)) rfl ((hNw (N + 1) (by omega)).trans (by omega))) dN2
      (h2N.trans (by omega))
      (by omega))
    (hIw.trans (by omega)) (by omega)
  have hCa : (Val.list [.nat N, natList used, ssEncProg [.gen 0, .inv N, .mul (N + 1) N]]).wt ≤
      6 * X + 7 :=
    st_wt_list3 (hNw N (by omega)) hUw hIw
  have hchain : FunDet P 29 (.list [.nat N, natList used, ssEncProg [.gen 0, .inv N,
      .mul (N + 1) N]]) (ssEncProg loc)
      (5000 * ((Val.list [.nat N, natList used, ssEncProg [.gen 0, .inv N, .mul (N + 1) N]]).wt +
        (ssEncProg loc).wt + 1) ^ 2) :=
    ssChainFold_spec hw.core.gen.insAt.chainAt hw.core.gen.insAt.chainStep N used _
  have dI' : StDC P e2 (ssCmInit (.length (.var 2)))
      (ssEncProg [.gen 0, .inv N, .mul (N + 1) N]) _ _ W := dI
  have hLw' : (ssEncProg loc).wt ≤ X := hLw
  have dL := StDC.call (StDC.mk3 dN2 dU dI' (hCa.trans (by omega)) (by omega)) hchain
    (hLw'.trans (by omega))
  -- the output
  set e3 := e2 ++ [ssEncProg loc] with he3
  have hl3 := length_lt_wt_list (loc.map encSlpInstr)
  have hLw2 : (Val.list (loc.map encSlpInstr)).wt ≤ X := hLw'
  have hPw2 : (Val.list (prog.map encSlpInstr)).wt ≤ X := hPw
  have hA2 : (Val.list [.list (prog.map encSlpInstr), .list (loc.map encSlpInstr)]).wt ≤
      4 * X + 6 := st_wt_list2 hPw2 hLw2
  have hB2 : (Val.list (prog.map encSlpInstr ++ loc.map encSlpInstr)).wt ≤ X := by
    rw [← List.map_append]; exact hAw
  have happD : FunDet P 19 (.list [.list (prog.map encSlpInstr), .list (loc.map encSlpInstr)])
      (.list (prog.map encSlpInstr ++ loc.map encSlpInstr))
      (1000 * ((loc.map encSlpInstr).length + 1) *
        ((Val.list [.list (prog.map encSlpInstr), .list (loc.map encSlpInstr)]).wt +
          (loc.map encSlpInstr).length +
          (Val.list (prog.map encSlpInstr ++ loc.map encSlpInstr)).wt + 1)) :=
    (append_spec hw.core.gen.insAt.appAt (prog.map encSlpInstr) (loc.map encSlpInstr)).mono
      fun v c ⟨h1, h2⟩ => ⟨h1, by subst h1; exact h2⟩
  have dA := StDC.call (StDC.mk2 (StDC.var' (P := P) (W := W) (env := e3) (i := 2)
      (v := .list (prog.map encSlpInstr)) rfl (hPw2.trans (by omega)))
    (StDC.var' (P := P) (W := W) (env := e3) (i := 3) (v := .list (loc.map encSlpInstr)) rfl
      (hLw2.trans (by omega))) (hA2.trans (by omega)) (by omega)) happD (hB2.trans (by omega))
  have dLl0 := StDC.length (StDC.var' (P := P) (W := W) (env := e3) (i := 3)
      (v := .list (loc.map encSlpInstr)) rfl (hLw2.trans (by omega))) (W := W) (by omega)
  have dLl : StDC P e3 (.length (.var 3)) (.nat loc.length) 2 0 W := by
    rw [List.length_map] at dLl0; exact dLl0
  have hNw2 : ∀ k, k ≤ N + loc.length → (Val.nat k).wt ≤ X := fun k hk =>
    (wt_nat_le k).trans (by rw [hlocl] at hk; omega)
  have dIdx := StDC.arith (op := .sub) (z := N + loc.length - 1)
    (StDC.arith (op := .add) (z := N + loc.length) (dN [ssEncProg loc]) dLl rfl
      ((hNw2 _ le_rfl).trans (by omega))) (StDC.nat 1 (by omega)) rfl
    ((hNw2 _ (by omega)).trans (by omega))
  have hInv : (Val.list [.nat 1, .nat (N + loc.length - 1)]).wt ≤ 4 * X + 6 :=
    st_wt_list2 (hNw2 1 (by rw [hlocl]; omega)) (hNw2 _ (by omega))
  have dInv := StDC.mk2 (StDC.nat 1 (by omega)) dIdx (hInv.trans (by omega)) (by omega)
  have hval : prog.map encSlpInstr ++ loc.map encSlpInstr ++
      [.list [.nat 1, .nat (N + loc.length - 1)]] = (ssConstrProg prog used).map encSlpInstr := by
    rw [show ssConstrProg prog used = prog ++ loc ++ [.inv (N + loc.length - 1)] from rfl]
    simp only [List.map_append, List.map_cons, List.map_nil, encSlpInstr]
  have hFw2 : (Val.list ((ssConstrProg prog used).map encSlpInstr)).wt ≤ X := hFw
  have dSn := StDC.snoc dA dInv (by rw [hval]; exact hFw2.trans (by omega))
  rw [hval] at dSn
  have hOw := st_wt_list2 (hNw 1 (by omega)) hFw2
  have dOut := StDC.mk2 (StDC.nat 1 (by omega)) dSn (hOw.trans (by omega)) (by omega)
  have dB3 := StDC.letE dL dOut (hOw.trans (by omega))
  have dB2 := StDC.letE dP dB3 (hOw.trans (by omega))
  have dT := StDC.letE dR dB2 (hOw.trans (by omega))
  have dTop := StDC.ite (e := mk2 (.nat 1) .nil) (ne := 0) (Ee := 0) dc (fun _ => dT)
    (fun h => absurd h hg) (hOw.trans (by omega))
  have hLl : (loc.map encSlpInstr).length ≤ W := by omega
  refine FunAll.mono (StDC.funDet (c := 100 * ssCoreCost Y) hf dTop
      (ss_cm_cost hC hW (by norm_num)
        (by simp only [Nat.zero_add, Nat.add_zero, Nat.add_assoc]; exact le_rfl) le_rfl
        (hCa.trans (by omega))
        (hLw'.trans (by omega)) le_rfl hLl (hA2.trans (by omega)) (hB2.trans (by omega))))
    fun v c ⟨hv, hc⟩ => ⟨⟨ssConstrProg prog used, hv, ?_, hreach (Nat.pos_of_ne_zero hg)⟩,
      ss_wrap_cost hc⟩
  rw [hfl]
  exact ss_cm_len hs2 hws hN hul hnw'.le

end GI.Impl
