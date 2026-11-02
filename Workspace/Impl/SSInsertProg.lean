import Workspace.Impl.SSSmall

/-!
# Insertion as a program

`ssInsertF` computes `ssInsert`: it sifts `g` (`ssSiftLoop_spec`); if `g` passes, it returns
the state; otherwise it builds the chain of instructions (`ssChainFold_spec`), writes the new
entry into its slot (`set_spec`) and appends the chain to the program (`append_spec`).
The argument is `[ctx, st, g, ins₀]` with the context `ctx = [n, B, [1, g₁, …]]`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The context of the core: `[n, B, [1, g₁, …, g_m], |B| n]`. -/
def ssCtx (B : List (Fin n)) (gs : List (Perm (Fin n))) : Val :=
  .list [.nat n, ssEncB B, .list ((1 :: gs).map encPerm), .nat (B.length * n)]

/-- The body of insertion. -/
def ssInsertF (sift chain setb app : ℕ) : Expr :=
  .letE (.call sift (mk3 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 0)))
      (.length (.get (arg 0) (.nat 1))) (mk3 (arg 2) .nil (.nat 0))))
    (.ite (.get (.var 1) (.nat 2))
      (.letE (.get (.get (arg 0) (.nat 1)) (.arith .sub (.get (.var 1) (.nat 2)) (.nat 1)))
        (.letE (.call chain (mk3 (.length (.get (arg 1) (.nat 1))) (.get (.var 1) (.nat 1))
            (.snoc .nil (arg 3))))
          (mk2 (.call setb (mk3 (.get (arg 1) (.nat 0))
                (.arith .add (.arith .mul (.arith .sub (.get (.var 1) (.nat 2)) (.nat 1))
                    (.get (arg 0) (.nat 0)))
                  (.get (.get (.var 1) (.nat 0)) (.var 2)))
                (mk2 (.get (.var 1) (.nat 0))
                  (.arith .sub (.arith .add (.length (.get (arg 1) (.nat 1))) (.length (.var 3)))
                    (.nat 1)))))
            (.call app (mk2 (.get (arg 1) (.nat 1)) (.var 3))))))
      (arg 1))

/-- The parts of insertion. -/
structure SsInsAt (P : Program) (f sift chain setb app comp inv : ℕ) : Prop where
  fn : P.funs[f]? = some (ssInsertF sift chain setb app)
  siftAt : SsSiftAt P sift comp inv
  chainAt : P.HasAt chain (foldlFuns chain (chain + 3))
  chainStep : P.funs[chain + 3]? = some ssChainF
  setAt : P.HasAt setb (setFuns setb)
  appAt : P.HasAt app (appendFuns app)

/-- The cost of sifting, in terms of the weight bound. -/
def ssSiftCost' (W0 : ℕ) : ℕ := 10 ^ 6 * (W0 + 1) ^ 2

/-- The cost of insertion. -/
def ssInsCost (Y : ℕ) : ℕ := 10 ^ 7 * (ssW Y + 1) ^ 2

theorem ssSmall_ctx' {B : List (Fin n)} {gs : List (Perm (Fin n))} {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) : SsSmall (ssZ Y) (ssCtx B gs) := by
  obtain ⟨-, hTY, hG, hY3, hZ⟩ := ss_Y_facts hY
  have hgs : (Val.list ((1 :: gs).map encPerm)).size ≤ (gs.length + 1) * (2 * n + 3) + 3 := by
    refine (size_list_le (B := 2 * n + 3) fun v hv => ?_).trans (by simp)
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv; rw [size_encPerm]
  have hgs' : (Val.list (encPerm 1 :: gs.map encPerm)).size ≤ (gs.length + 1) * (2 * n + 3) + 3 :=
    hgs
  refine ssSmall_list ?_ fun v hv => ?_
  · rw [size_list_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ssEncB, size_natList,
      size_nat, List.length_map]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ssSmall_nat (by omega) (by omega)
    · refine ssSmall_natList (fun x hx => ?_) (by simp; omega)
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      have := y.isLt; omega
    · refine ssSmall_list (by omega) fun v hv => ?_
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv
      exact ssSmall_encPerm σ (by omega)
    · refine ssSmall_nat ?_ (by omega)
      have : B.length * n ≤ B.length * n * (2 * n + 8) := Nat.le_mul_of_pos_right _ (by omega)
      omega

theorem ss_cost_fin2 {k E W c : ℕ} (hk : k ≤ 300) (hE : E + 300 * (W + 1) ≤ c) :
    k * (W + 1) + E ≤ c := by
  have := Nat.mul_le_mul_right (W + 1) hk; omega

theorem ss_mul_le {a b V k l : ℕ} (ha : a ≤ k * V) (hb : b ≤ l * V) : a * b ≤ (k * l) * (V * V) :=
  (Nat.mul_le_mul ha hb).trans (by rw [Nat.mul_mul_mul_comm])

theorem ss_ins_cost0 {W0 : ℕ} (c : ℕ) (hc : c ≤ ssSiftCost' W0) :
    c + 300 * (10 * W0 + 10 + 1) ≤ 10 ^ 7 * (W0 + 1) ^ 2 := by
  unfold ssSiftCost' at hc
  have e : (W0 + 1) ^ 2 = (W0 + 1) * (W0 + 1) := by ring
  have := Nat.le_mul_of_pos_left (W0 + 1) (show 0 < W0 + 1 by omega)
  rw [e] at hc ⊢
  omega

theorem ss_ins_cost {W0 c1 c2 c3 c4 A2 R2 l3 A3 R3 l4 A4 R4 : ℕ} (h1 : c1 ≤ ssSiftCost' W0)
    (h2 : c2 ≤ 5000 * (A2 + R2 + 1) ^ 2) (hA2 : A2 ≤ 6 * W0 + 7) (hR2 : R2 ≤ W0)
    (h3 : c3 ≤ loopModK * (l3 + 1) * (A3 + l3 + R3 + 1)) (hl3 : l3 ≤ W0) (hA3 : A3 ≤ 6 * W0 + 7)
    (hR3 : R3 ≤ W0)
    (h4 : c4 ≤ loopModK * (l4 + 1) * (A4 + l4 + R4 + 1)) (hl4 : l4 ≤ W0) (hA4 : A4 ≤ 6 * W0 + 7)
    (hR4 : R4 ≤ W0) :
    c1 + c2 + c3 + c4 + 300 * (10 * W0 + 10 + 1) ≤ 10 ^ 7 * (W0 + 1) ^ 2 := by
  unfold ssSiftCost' at h1
  unfold loopModK at h3 h4
  have e : (W0 + 1) ^ 2 = (W0 + 1) * (W0 + 1) := by ring
  rw [e] at h1 ⊢
  have e2 : (A2 + R2 + 1) ^ 2 = (A2 + R2 + 1) * (A2 + R2 + 1) := by ring
  rw [e2] at h2
  have m2 := ss_mul_le (V := W0 + 1) (k := 8) (l := 8) (a := A2 + R2 + 1) (b := A2 + R2 + 1)
    (by omega) (by omega)
  have m3 := ss_mul_le (V := W0 + 1) (k := 1) (l := 9) (a := l3 + 1) (b := A3 + l3 + R3 + 1)
    (by omega) (by omega)
  have m4 := ss_mul_le (V := W0 + 1) (k := 1) (l := 9) (a := l4 + 1) (b := A4 + l4 + R4 + 1)
    (by omega) (by omega)
  have := Nat.le_mul_of_pos_left (W0 + 1) (show 0 < W0 + 1 by omega)
  rw [Nat.mul_assoc] at h3 h4
  omega

/-- **Insertion.** -/
theorem ssInsertF_spec {P : Program} {f sift chain setb app comp inv : ℕ}
    (hP : SsInsAt P f sift chain setb app comp inv) {B : List (Fin n)}
    {gs : List (Perm (Fin n))} {st : SsState n} (hinv : SsInv B gs st)
    {es : List (Perm (Fin n))} (hes : slpEntries gs st.2 [] = some es) {g : Perm (Fin n)}
    {ins0 : SlpInstr} (hins : slpEntries gs [ins0] es = some (es ++ [g])) {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P f (.list [ssCtx B gs, ssEncSt st, encPerm g, encSlpInstr ins0])
      (ssEncSt (ssInsert B st g ins0)) (ssInsCost Y) := by
  have hsm := ssInv_small hinv hY
  have hsm' := ssInv_small (ssInsert_spec hinv hes hins).1 hY
  obtain ⟨hK, hTY, hG, hY3, hZ⟩ := ss_Y_facts hY
  have hYL : n + B.length + 2 ≤ Y := by omega
  have hlen := hinv.len
  have hes_len : es.length = st.2.length := by
    obtain ⟨v, rfl, hv⟩ := slpEntries_prefix _ _ _ hes
    simpa using hv
  have hins0 : ssInsMax ins0 ≤ ssZ Y := by
    have h1 := ss_slp_max gs [ins0] es _ hins ins0 (by simp)
    have h2 := hsm.plen'
    simp only [List.length_append, List.length_singleton] at h1
    omega
  obtain ⟨T, prog⟩ := st
  simp only at hlen hes_len
  have hpl : prog.length * 9 + 3 ≤ ssZ Y := hsm.plen
  have hpl' : prog.length ≤ 3 * Y ^ 3 := hsm.plen'
  have hidx0 : ∀ s ∈ T, ∀ e, s = some e → e.2 ≤ ssZ Y := hsm.idx
  have htab0 : SsSmall (ssZ Y) (ssEncTab T) := hsm.tab
  have hprog0 : SsSmall (ssZ Y) (ssEncProg prog) := hsm.prog
  -- weights
  set Z := ssZ Y with hZdef
  set W0 := ssW Y with hW0def
  have hZW : Z ≤ W0 := ssZ_le_ssW Y
  have hsw : ∀ v, SsSmall Z v → v.wt ≤ W0 := fun v h => h.wt_le
  set W := 10 * W0 + 10 with hWdef
  have hnatW : ∀ k, k ≤ Z → (Val.nat k).wt ≤ W := fun k hk => (wt_nat_le k).trans (by omega)
  have hsc : ssSiftCost Y ≤ ssSiftCost' W0 := by simp only [ssSiftCost, ssSiftCost', hW0def, le_refl]
  have hctxS : SsSmall Z (ssCtx B gs) := ssSmall_ctx' hY
  have hic : ssInsCost Y = 10 ^ 7 * (W0 + 1) ^ 2 := by simp only [ssInsCost, hW0def]
  clear_value W Z W0
  have hn2 : n + 2 ≤ Y := by omega
  have hL : B.length ≤ Y := by omega
  have hY4 : Y ≤ Z := by omega
  have hctx := hsw _ hctxS
  have hTw := hsw _ htab0
  have hPw := hsw _ hprog0
  have hSw : (ssEncSt (T, prog)).wt ≤ W0 :=
    hsw _ (hZdef ▸ hsm.st hn2 (by rw [hlen]; exact hTY))
  have hgw := hsw _ (ssSmall_encPerm g (show 2 * n + 3 ≤ Z by omega))
  have hIw := hsw _ (ssSmall_instr hins0 (show 9 ≤ Z by omega))
  have haW : (Val.list [ssCtx B gs, ssEncSt (T, prog), encPerm g, encSlpInstr ins0]).wt ≤ W :=
    (st_wt_list4 hctx hSw hgw hIw).trans (by omega)
  set a := Val.list [ssCtx B gs, ssEncSt (T, prog), encPerm g, encSlpInstr ins0] with ha
  have dArg : ∀ j v, [ssCtx B gs, ssEncSt (T, prog), encPerm g, encSlpInstr ins0][j]? = some v →
      v.wt ≤ W0 → ∀ rest : List Val, StDC P (a :: rest) (arg j) v 3 0 W := fun j v hv hw rest =>
    StDC.arg hv haW (by have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega)
      (by omega)
  have d0 : ∀ rest, StDC P (a :: rest) (.get (arg 0) (.nat 0)) (.nat n) 5 0 W := fun rest =>
    (StDC.get (v := .nat n) (dArg 0 _ rfl hctx rest) (StDC.nat 0 (by omega)) rfl
      (hnatW n (by omega))).mono (by omega) le_rfl
  have hBw : (ssEncB B).wt ≤ W0 :=
    (le_of_lt (wt_le_wt_list (show ssEncB B ∈ [.nat n, ssEncB B, .list ((1 :: gs).map encPerm), .nat (B.length * n)]
      by simp))).trans hctx
  have d1 : ∀ rest, StDC P (a :: rest) (.get (arg 0) (.nat 1)) (ssEncB B) 5 0 W := fun rest =>
    (StDC.get (v := ssEncB B) (dArg 0 _ rfl hctx rest) (StDC.nat 1 (by omega)) rfl
      (by omega)).mono (by omega) le_rfl
  have dT : ∀ rest, StDC P (a :: rest) (.get (arg 1) (.nat 0)) (ssEncTab T) 5 0 W := fun rest =>
    (StDC.get (v := ssEncTab T) (dArg 1 _ rfl hSw rest) (StDC.nat 0 (by omega)) rfl
      (by omega)).mono (by omega) le_rfl
  have dP : ∀ rest, StDC P (a :: rest) (.get (arg 1) (.nat 1)) (ssEncProg prog) 5 0 W :=
    fun rest => (StDC.get (v := ssEncProg prog) (dArg 1 _ rfl hSw rest) (StDC.nat 1 (by omega))
      rfl (by omega)).mono (by omega) le_rfl
  have dPL : ∀ rest, StDC P (a :: rest) (.length (.get (arg 1) (.nat 1))) (.nat prog.length) 6 0 W :=
    fun rest => by
      have := StDC.length (dP rest) (by have := hpl; simp; omega)
      simpa only [List.length_map] using this
  -- sifting
  have facts := ssSift_acc_facts B T hidx0 g B.length
  have hfold : (List.range B.length).foldl (ssSiftStep B T) (g, [], 0) = ssSift B T g := rfl
  rw [hfold] at facts
  have hsiftc := ssSmall_ctx B T hidx0 (by rw [hlen]; omega)
  have hacc0 := ssSmall_acc (Z := Z) (g, [], 0) (by simp) (by simp) (by simp; omega)
  have hR := ssSmall_acc (Z := Z) (ssSift B T g) facts.2.1 (facts.2.2.trans (by omega))
    (by have := facts.1; omega)
  have hBL : ((B.map Fin.val).map Val.nat).length = B.length := by simp
  have dL : StDC P [a] (.length (.get (arg 0) (.nat 1))) (.nat B.length) 6 0 W := by
    have := StDC.length (vs := (B.map Fin.val).map Val.nat) (d1 []) (by rw [hBL]; omega)
    rwa [hBL] at this
  have dSA : StDC P [a] (mk3 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
      (.get (arg 1) (.nat 0))) (.length (.get (arg 0) (.nat 1))) (mk3 (arg 2) .nil (.nat 0)))
      (.list [ssSiftCtx B T, .nat B.length, ssEncAcc (g, [], 0)]) 40 0 W :=
    (StDC.mk3 (StDC.mk3 (d0 []) (d1 []) (dT []) ((hsw _ hsiftc).trans (by omega)) (by omega)) dL
      (StDC.mk3 (dArg 2 _ rfl hgw []) (StDC.nil (by omega)) (StDC.nat 0 (by omega))
        ((hsw _ hacc0).trans (by omega)) (by omega))
      ((st_wt_list3 (hsw _ hsiftc) ((wt_nat_le _).trans (by omega : B.length + 2 ≤ W0)) (hsw _ hacc0)).trans (by omega))
      (by omega)).mono (by norm_num) le_rfl
  have dR := StDC.call dSA (ssSiftLoop_spec hP.siftAt B T hlen hYL (by rw [← hZdef]; exact hidx0) g)
    ((hsw _ hR).trans (by omega))
  generalize hr : ssSift B T g = r at dR facts hR
  obtain ⟨h, used, stop⟩ := r
  simp only at facts
  have hRw := hsw _ hR
  set R := ssEncAcc (h, used, stop) with hRdef
  have dStop : StDC P [a, R] (.get (.var 1) (.nat 2)) (.nat stop) 3 0 W :=
    StDC.get (v := .nat stop) (StDC.var' rfl (by show R.wt ≤ W; omega)) (StDC.nat 2 (by omega)) rfl
      (hnatW _ (by omega))
  by_cases hstop : stop = 0
  · -- `g` passes: the state is returned
    have hres : ssInsert B (T, prog) g ins0 = (T, prog) := by
      simp only [ssInsert, hr, hstop, if_true]
    rw [hres]
    refine StDC.funDet hP.fn (StDC.letE dR (StDC.ite (nt := 0) (Et := 0) dStop
      (fun h => absurd hstop h) (fun _ => dArg 1 _ rfl hSw [R]) (by omega)) (by omega))
      (ss_cost_fin2 (by norm_num) ?_)
    have := ss_ins_cost0 (W0 := W0) (ssSiftCost Y) hsc
    rw [hic, hWdef]
    simpa only [Nat.zero_add, Nat.add_zero] using this
  -- `g` stops at level `stop - 1`
  have hs1 : stop - 1 < B.length := by have := facts.2.2; omega
  have hBi : B[stop - 1]? = some (B[stop - 1]'hs1) := List.getElem?_eq_getElem hs1
  have hBb := ssEncB_get B hs1
  generalize hb : B[stop - 1]'hs1 = b at hBi hBb
  set loc := used.foldl (ssChain prog.length) [ins0] with hloc
  have hres : ssInsert B (T, prog) g ins0 =
      (T.set ((stop - 1) * n + (h b : ℕ)) (some (h, prog.length + loc.length - 1)), prog ++ loc) := by
    simp only [ssInsert, hr, hstop, if_false, hBi]; rfl
  rw [hres] at hsm' ⊢
  set T' := T.set ((stop - 1) * n + (h b : ℕ)) (some (h, prog.length + loc.length - 1)) with hT'
  have hpl2 : (prog ++ loc).length * 9 + 3 ≤ Z := by rw [hZdef]; exact hsm'.plen
  have hins2 : ∀ ins ∈ prog ++ loc, ssInsMax ins ≤ Z := by rw [hZdef]; exact hsm'.ins
  have htab2 : SsSmall Z (ssEncTab T') := by rw [hZdef]; exact hsm'.tab
  have hprog2 : SsSmall Z (ssEncProg (prog ++ loc)) := by rw [hZdef]; exact hsm'.prog
  -- sizes of the new parts
  have hlocS : SsSmall Z (ssEncProg loc) := by
    refine ssSmall_prog (fun ins hins => hins2 ins (by simp [hins])) ?_ (by omega)
    have := hpl2; simp only [List.length_append] at this; omega
  have hlocw := hsw _ hlocS
  have hnewlen : prog.length + loc.length - 1 ≤ Z := by
    have := hpl2; simp only [List.length_append] at this; omega
  have hslotS : SsSmall Z (ssEncSlot (some (h, prog.length + loc.length - 1))) :=
    ssSmall_slot (fun e he => by cases he; exact hnewlen) (by omega)
  have hslotw := hsw _ hslotS
  have hT'w := hsw _ htab2
  have hP'w := hsw _ hprog2
  have hres'w : (ssEncSt (T.set ((stop - 1) * n + (h b : ℕ)) (some (h, prog.length + loc.length - 1)),
      prog ++ loc)).wt ≤ W0 :=
    hsw _ (hZdef ▸ hsm'.st hn2 (by rw [List.length_set, hlen]; exact hTY))
  have hUw : (natList used).wt ≤ W0 :=
    hsw _ (ssSmall_natList facts.2.1 (by have := facts.1; omega))
  have hI1 : SsSmall Z (ssEncProg [ins0]) := ssSmall_prog (by simpa using hins0) (by simp; omega)
    (by omega)
  have hI1w := hsw _ hI1
  -- `b = B[stop - 1]`
  have dS1 : StDC P [a, R] (.arith .sub (.get (.var 1) (.nat 2)) (.nat 1)) (.nat (stop - 1)) 5 0 W :=
    StDC.arith (op := .sub) dStop (StDC.nat 1 (by omega)) rfl (hnatW _ (by omega))
  have dB : StDC P [a, R] (.get (.get (arg 0) (.nat 1))
      (.arith .sub (.get (.var 1) (.nat 2)) (.nat 1))) (.nat b) 11 0 W :=
    (StDC.get (d1 [R]) dS1 hBb (hnatW _ (by have := b.isLt; omega))).mono (by omega) le_rfl
  set E2 := [a, R, Val.nat b] with hE2
  -- the chain
  have dU : StDC P E2 (.get (.var 1) (.nat 1)) (natList used) 3 0 W :=
    StDC.get (v := natList used) (StDC.var' rfl (by show R.wt ≤ W; omega)) (StDC.nat 1 (by omega)) rfl (by omega)
  have dI1 : StDC P E2 (.snoc .nil (arg 3)) (ssEncProg [ins0]) 5 0 W :=
    (StDC.snoc (vs := []) (StDC.nil (by omega)) (dArg 3 _ rfl hIw [R, .nat b])
      (by show (ssEncProg [ins0]).wt ≤ W; omega)).mono (by omega) le_rfl
  have hCA : (Val.list [.nat prog.length, natList used, ssEncProg [ins0]]).wt ≤ 6 * W0 + 7 :=
    st_wt_list3 ((wt_nat_le _).trans (by have := hpl; omega)) hUw hI1w
  have dCA : StDC P E2 (mk3 (.length (.get (arg 1) (.nat 1))) (.get (.var 1) (.nat 1))
      (.snoc .nil (arg 3))) (.list [.nat prog.length, natList used, ssEncProg [ins0]]) 18 0 W :=
    (StDC.mk3 (dPL [R, .nat b]) dU dI1 (by omega) (by omega)).mono (by omega) le_rfl
  have hchain := ssChainFold_spec hP.chainAt hP.chainStep prog.length used [ins0]
  rw [← hloc] at hchain
  have dLoc := StDC.call dCA hchain (by omega)
  set E3 := [a, R, Val.nat b, ssEncProg loc] with hE3
  -- the new slot
  have hhb : (h b : ℕ) < n := (h b).isLt
  have hidxZ : (stop - 1) * n + (h b : ℕ) + 2 ≤ Z := by
    have : (stop - 1) * n + (h b : ℕ) < B.length * n := by
      calc (stop - 1) * n + (h b : ℕ) < (stop - 1) * n + n := by omega
        _ = (stop - 1 + 1) * n := by ring
        _ ≤ B.length * n := Nat.mul_le_mul_right _ (by omega)
    have : B.length * n ≤ Y * Y := Nat.mul_le_mul hL (by omega)
    have : Y * Y ≤ Y ^ 3 := by
      have e : Y ^ 3 = Y * Y * Y := by ring
      rw [e]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have dHg : ∀ rest, StDC P (a :: R :: rest) (.get (.var 1) (.nat 0)) (encPerm h) 3 0 W :=
    fun rest => StDC.get (v := encPerm h) (StDC.var' rfl (by show R.wt ≤ W; omega)) (StDC.nat 0 (by omega)) rfl
      ((le_of_lt (wt_le_wt_list (show encPerm h ∈ [encPerm h, natList used, Val.nat stop] by simp))).trans
        (show R.wt ≤ W by omega))
  have dS1' : StDC P E3 (.arith .sub (.get (.var 1) (.nat 2)) (.nat 1)) (.nat (stop - 1)) 5 0 W :=
    StDC.arith (op := .sub)
      (StDC.get (v := .nat stop) (StDC.var' rfl (by show R.wt ≤ W; omega)) (StDC.nat 2 (by omega)) rfl
        (hnatW _ (by omega))) (StDC.nat 1 (by omega)) rfl (hnatW _ (by omega))
  have dIdx : StDC P E3 (.arith .add (.arith .mul (.arith .sub (.get (.var 1) (.nat 2)) (.nat 1))
      (.get (arg 0) (.nat 0))) (.get (.get (.var 1) (.nat 0)) (.var 2)))
      (.nat ((stop - 1) * n + (h b : ℕ))) 20 0 W := by
    have d1 := StDC.arith (op := .mul) (z := (stop - 1) * n) dS1' (d0 _) rfl
      (hnatW _ (by omega))
    have d2 := StDC.get (dHg [.nat b, ssEncProg loc])
      (StDC.var' (i := 2) (v := .nat b) rfl (hnatW _ (by have := b.isLt; omega))) (ssEncPerm_get h b)
      (hnatW _ (by omega))
    exact (StDC.arith (op := .add) (z := (stop - 1) * n + (h b : ℕ)) d1 d2 rfl
      (hnatW _ (by omega))).mono (by omega) le_rfl
  have dLL : StDC P E3 (.length (.var 3)) (.nat loc.length) 2 0 W := by
    have := StDC.length (vs := loc.map encSlpInstr) (StDC.var' (P := P) (W := W) (env := E3) (i := 3) (v := ssEncProg loc) rfl (by omega))
      (by have := hpl2; simp only [List.length_append] at this; simp; omega)
    simpa only [List.length_map] using this
  have dNew : StDC P E3 (.arith .sub (.arith .add (.length (.get (arg 1) (.nat 1)))
      (.length (.var 3))) (.nat 1)) (.nat (prog.length + loc.length - 1)) 11 0 W :=
    (StDC.arith (op := .sub) (StDC.arith (op := .add) (z := prog.length + loc.length) (dPL _) dLL rfl
      (hnatW _ (by have := hpl2; simp only [List.length_append] at this; omega)))
      (StDC.nat 1 (by omega)) rfl (hnatW _ hnewlen)).mono (by omega) le_rfl
  have dSlot : StDC P E3 (mk2 (.get (.var 1) (.nat 0)) (.arith .sub (.arith .add
      (.length (.get (arg 1) (.nat 1))) (.length (.var 3))) (.nat 1)))
      (ssEncSlot (some (h, prog.length + loc.length - 1))) 17 0 W :=
    StDC.mk2 (dHg _) dNew (by show (ssEncSlot (some (h, prog.length + loc.length - 1))).wt ≤ W; omega)
      (by omega)
  have hSA3 : (Val.list [Val.list (T.map ssEncSlot), .nat ((stop - 1) * n + (h b : ℕ)),
      ssEncSlot (some (h, prog.length + loc.length - 1))]).wt ≤ 6 * W0 + 7 :=
    st_wt_list3 hTw ((wt_nat_le _).trans (by omega)) hslotw
  have hSA : (Val.list [ssEncTab T, .nat ((stop - 1) * n + (h b : ℕ)),
      ssEncSlot (some (h, prog.length + loc.length - 1))]).wt ≤ W := hSA3.trans (by omega)
  have dSA2 : StDC P E3 (mk3 (.get (arg 1) (.nat 0)) (.arith .add (.arith .mul
      (.arith .sub (.get (.var 1) (.nat 2)) (.nat 1)) (.get (arg 0) (.nat 0)))
      (.get (.get (.var 1) (.nat 0)) (.var 2))) (mk2 (.get (.var 1) (.nat 0))
      (.arith .sub (.arith .add (.length (.get (arg 1) (.nat 1))) (.length (.var 3))) (.nat 1))))
      (.list [ssEncTab T, .nat ((stop - 1) * n + (h b : ℕ)),
        ssEncSlot (some (h, prog.length + loc.length - 1))]) 46 0 W :=
    (StDC.mk3 (dT _) dIdx dSlot hSA (by omega)).mono (by omega) le_rfl
  have hset := set_spec hP.setAt (T.map ssEncSlot) ((stop - 1) * n + (h b : ℕ))
    (ssEncSlot (some (h, prog.length + loc.length - 1)))
  rw [← List.map_set] at hset
  have dSet := StDC.call dSA2 hset (by show (ssEncTab T').wt ≤ W; omega)
  have hAA : (Val.list [ssEncProg prog, ssEncProg loc]).wt ≤ W :=
    (st_wt_list2 hPw hlocw).trans (by omega)
  have happ : FunDet P app (.list [ssEncProg prog, ssEncProg loc]) (ssEncProg (prog ++ loc))
      (loopModK * ((loc.map encSlpInstr).length + 1) *
        ((Val.list [ssEncProg prog, ssEncProg loc]).wt + (loc.map encSlpInstr).length +
          (ssEncProg (prog ++ loc)).wt + 1)) :=
    (append_spec hP.appAt (prog.map encSlpInstr) (loc.map encSlpInstr)).mono fun w c ⟨hw, hc⟩ => by
      have e : ssEncProg (prog ++ loc) = .list (prog.map encSlpInstr ++ loc.map encSlpInstr) := by
        simp [ssEncProg]
      rw [e]; exact ⟨hw, hw ▸ hc⟩
  have dApp := StDC.call (StDC.mk2 (dP _) (StDC.var' (P := P) (W := W) (env := E3) (i := 3) (v := ssEncProg loc) rfl (by omega)) hAA
    (by omega)) happ (by omega)
  have hresW : (ssEncSt (T', prog ++ loc)).wt ≤ W := le_trans hres'w (by omega)
  have dRes := StDC.mk2 dSet dApp hresW (by omega)
  refine StDC.funDet hP.fn (StDC.letE dR (StDC.ite (ne := 0) (Ee := 0) dStop
    (fun _ => StDC.letE dB (StDC.letE dLoc dRes hresW) hresW)
    (fun h => absurd h hstop) hresW) hresW)
    (ss_cost_fin2 (by norm_num) ?_)
  -- the cost
  have hl3 : (T.map ssEncSlot).length ≤ W0 := by
    rw [List.length_map, hlen]
    have : B.length * n ≤ B.length * n * (2 * n + 8) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hl4 : (loc.map encSlpInstr).length ≤ W0 := by
    rw [List.length_map]; have := hpl2; simp only [List.length_append] at this; omega
  have := ss_ins_cost hsc le_rfl hCA hlocw le_rfl hl3 hSA3 hT'w le_rfl hl4
    ((st_wt_list2 hPw hlocw).trans (by omega)) hP'w
  rw [hic, hWdef]
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc] using this

end GI.Impl
