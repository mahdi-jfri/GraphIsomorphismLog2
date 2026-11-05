module

public import Workspace.Impl.SSGenProg

@[expose] public section

/-!
# The rounds, as programs

`ssPairF` is one pair step (`ssPair`): it reads the slots `k / M` and `k % M`, and if both are
filled it inserts the product of their entries with the instruction `mul`. A round is the loop
over `k < M²` (`ssRoundLoop_spec`), and the loop over `M + 1` rounds is `ssRoundsLoop_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The body of one pair step, on `[c, k, st]`. -/
def ssPairF (ins comp : ℕ) : Expr :=
  .letE (.get (.get (arg 2) (.nat 0)) (.arith .div (arg 1) (.get (arg 0) (.nat 3))))
    (.letE (.get (.get (arg 2) (.nat 0)) (.arith .mod (arg 1) (.get (arg 0) (.nat 3))))
      (.ite (.length (.var 1))
        (.ite (.length (.var 2))
          (.call ins (mk4 (arg 0) (arg 2)
            (.call comp (mk2 (.get (.var 1) (.nat 0)) (.get (.var 2) (.nat 0))))
            (mk3 (.nat 2) (.get (.var 1) (.nat 1)) (.get (.var 2) (.nat 1)))))
          (arg 2))
        (arg 2)))

theorem ss_add_cost2 {W0 E : ℕ} (hE : E ≤ 10 ^ 7 * (W0 + 1) ^ 2 + 30000 * (W0 + 1)) :
    E + 300 * (10 * W0 + 10 + 1) ≤ 2 * 10 ^ 7 * (W0 + 1) ^ 2 := by
  have e : (W0 + 1) ^ 2 = (W0 + 1) * (W0 + 1) := by ring
  have := Nat.le_mul_of_pos_left (W0 + 1) (show 0 < W0 + 1 by omega)
  rw [e] at hE ⊢
  omega

theorem ssSlot_len {s : SsSlot n} : ∃ vs, ssEncSlot s = .list vs ∧ (vs.length = 0 ↔ s = none) := by
  cases s with
  | none => exact ⟨[], rfl, by simp⟩
  | some e => exact ⟨[encPerm e.1, .nat e.2], rfl, by simp⟩



/-- **One pair step.** -/
theorem ssPairF_spec {P : Program} {f ins sift chain setb app comp inv : ℕ}
    (hf : P.funs[f]? = some (ssPairF ins comp)) (hP : SsInsAt P ins sift chain setb app comp inv)
    {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n} (hinv : SsInv B gs st)
    {k : ℕ} (hk : k < B.length * n * (B.length * n)) {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P f (.list [ssCtx B gs, .nat k, ssEncSt st])
      (ssEncSt (ssPair B (B.length * n) st k)) (ssGenCost Y) := by
  obtain ⟨hMM, hG, hn4, h1000⟩ := ss_W_facts hY
  obtain ⟨-, -, -, hY3, hZ⟩ := ss_Y_facts hY
  have hZW := ssZ_le_ssW Y
  have hsm := ssInv_small hinv hY
  have hc := ss_ctx_wt hY
  have hs := ss_st_wt hinv hY
  have hspair := ssPair_spec (B := B) rfl hinv k
  have hs' := ss_st_wt hspair.1 hY
  obtain ⟨T, prog⟩ := st
  have hlen : T.length = B.length * n := hinv.len
  have hidx : ∀ s ∈ T, ∀ e, s = some e → e.2 ≤ ssZ Y := hsm.idx
  set M := B.length * n with hM
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hk; simp at hk
    · exact h
  have hp : k / M < M := (Nat.div_lt_iff_lt_mul hMpos).mpr hk
  have hq : k % M < M := Nat.mod_lt _ hMpos
  have hMW : M + 2 ≤ ssW Y := by have := Nat.le_mul_self M; omega
  have hpT : k / M < T.length := hlen ▸ hp
  have hqT : k % M < T.length := hlen ▸ hq
  -- weights
  set W := 10 * ssW Y + 10 with hW
  clear_value W
  have hTw : (ssEncTab T).wt ≤ ssW Y :=
    (le_of_lt (wt_le_wt_list (show ssEncTab T ∈ [ssEncTab T, ssEncProg prog] by simp))).trans hs
  have hslw : ∀ p (hp : p < T.length), (ssEncSlot T[p]).wt ≤ ssW Y := fun p hp =>
    (le_of_lt (wt_le_wt_list (List.mem_map.mpr ⟨T[p], List.getElem_mem hp, rfl⟩))).trans hTw
  have hkW : (Val.nat k).wt ≤ ssW Y := (wt_nat_le k).trans (by omega)
  have haw : (Val.list [ssCtx B gs, .nat k, ssEncSt (T, prog)]).wt ≤ W :=
    (st_wt_list3 hc hkW hs).trans (by omega)
  set a := Val.list [ssCtx B gs, .nat k, ssEncSt (T, prog)] with ha
  have dArg : ∀ j v, [ssCtx B gs, .nat k, ssEncSt (T, prog)][j]? = some v → v.wt ≤ ssW Y →
      ∀ rest : List Val, StDC P (a :: rest) (arg j) v 3 0 W :=
    fun j v hv hw rest => StDC.arg hv haw
      (by have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega) (by omega)
  have dM : ∀ rest, StDC P (a :: rest) (.get (arg 0) (.nat 3)) (.nat M) 5 0 W := fun rest =>
    (StDC.get (v := .nat M) (dArg 0 _ rfl hc rest) (StDC.nat 3 (by omega)) rfl
      ((wt_nat_le _).trans (by omega))).mono (by omega) le_rfl
  have dTab : ∀ rest, StDC P (a :: rest) (.get (arg 2) (.nat 0)) (ssEncTab T) 5 0 W := fun rest =>
    (StDC.get (v := ssEncTab T) (dArg 2 _ rfl hs rest) (StDC.nat 0 (by omega)) rfl
      (by omega)).mono (by omega) le_rfl
  have hgetT : ∀ p (hp : p < T.length), (T.map ssEncSlot)[p]? = some (ssEncSlot T[p]) :=
    fun p hp => by simp [hp]
  have dS : StDC P [a] (.get (.get (arg 2) (.nat 0)) (.arith .div (arg 1) (.get (arg 0) (.nat 3))))
      (ssEncSlot (T[k / M]'hpT)) 15 0 W :=
    (StDC.get (dTab []) (StDC.arith (op := .div) (z := k / M) (dArg 1 _ rfl hkW []) (dM []) rfl
      ((wt_nat_le _).trans (by omega))) (hgetT _ hpT) (by have := hslw _ hpT; omega)).mono
      (by omega) le_rfl
  have dT : StDC P [a, ssEncSlot (T[k / M]'hpT)] (.get (.get (arg 2) (.nat 0))
      (.arith .mod (arg 1) (.get (arg 0) (.nat 3)))) (ssEncSlot (T[k % M]'hqT)) 15 0 W :=
    (StDC.get (dTab [ssEncSlot (T[k / M]'hpT)]) (StDC.arith (op := .mod) (z := k % M)
      (dArg 1 _ rfl hkW [ssEncSlot (T[k / M]'hpT)]) (dM [ssEncSlot (T[k / M]'hpT)]) rfl
      ((wt_nat_le _).trans (by omega))) (hgetT _ hqT) (by have := hslw _ hqT; omega)).mono
      (by omega) le_rfl
  have hsS : (T[k / M]?).join = (T[k / M]'hpT) := by rw [List.getElem?_eq_getElem hpT]; rfl
  have htS : (T[k % M]?).join = (T[k % M]'hqT) := by rw [List.getElem?_eq_getElem hqT]; rfl
  have hstW : (ssEncSt (ssPair B M (T, prog) k)).wt ≤ W := hs'.trans (by omega)
  have hstW0 : (ssEncSt (T, prog)).wt ≤ W := hs.trans (by omega)
  have hcost : ∀ E, E ≤ ssInsCost Y + permK * (n + 1) ^ 3 →
      E + 300 * (W + 1) ≤ ssGenCost Y := fun E hE => by
    unfold ssGenCost
    rw [hW]
    refine ss_add_cost2 (hE.trans ?_)
    unfold ssInsCost permK
    have := Nat.pow_le_pow_right (show 0 < n + 1 by omega) (show 3 ≤ 4 by norm_num)
    omega
  obtain ⟨vs, hvs, hvs0⟩ := ssSlot_len (s := (T[k / M]'hpT))
  obtain ⟨vt, hvt, hvt0⟩ := ssSlot_len (s := (T[k % M]'hqT))
  have hvsl : vs.length + 2 ≤ W := by
    have := hslw _ hpT; rw [hvs] at this
    have := length_lt_wt_list vs; omega
  have hvtl : vt.length + 2 ≤ W := by
    have := hslw _ hqT; rw [hvt] at this
    have := length_lt_wt_list vt; omega
  have dLs : StDC P [a, ssEncSlot (T[k / M]'hpT), ssEncSlot (T[k % M]'hqT)] (.length (.var 1))
      (.nat vs.length) 2 0 W :=
    StDC.length (StDC.var' (i := 1) (v := .list vs) (by rw [← hvs]; rfl)
      (by rw [← hvs]; have := hslw _ hpT; omega)) hvsl
  have dLt : StDC P [a, ssEncSlot (T[k / M]'hpT), ssEncSlot (T[k % M]'hqT)] (.length (.var 2))
      (.nat vt.length) 2 0 W :=
    StDC.length (StDC.var' (i := 2) (v := .list vt) (by rw [← hvt]; rfl)
      (by rw [← hvt]; have := hslw _ hqT; omega)) hvtl
  have dA2 := fun (_ : True) => dArg 2 _ rfl hs [ssEncSlot (T[k / M]'hpT), ssEncSlot (T[k % M]'hqT)]
  cases hTs : (T[k / M]'hpT) with
  | none =>
    have hres : ssPair B M (T, prog) k = (T, prog) := by
      unfold ssPair; simp only [hsS, hTs]
    rw [hres] at hstW ⊢
    have h0 : vs.length = 0 := hvs0.mpr hTs
    rw [h0] at dLs
    exact StDC.funDet hf (StDC.letE dS (StDC.letE dT (StDC.ite (nt := 0) (Et := 0) dLs
      (fun h => absurd rfl h) (fun _ => dA2 trivial) hstW0) hstW0) hstW0)
      (ss_cost_fin2 (by norm_num) (hcost _ (by omega)))
  | some s =>
    have hsne : vs.length ≠ 0 := fun h => by have := hvs0.mp h; rw [hTs] at this; simp at this
    cases hTt : (T[k % M]'hqT) with
    | none =>
      have hres : ssPair B M (T, prog) k = (T, prog) := by
        unfold ssPair; simp only [hsS, htS, hTs, hTt]
      rw [hres] at hstW ⊢
      have h0 : vt.length = 0 := hvt0.mpr hTt
      rw [h0] at dLt
      exact StDC.funDet hf (StDC.letE dS (StDC.letE dT (StDC.ite (ne := 0) (Ee := 0) dLs
        (fun _ => StDC.ite (nt := 0) (Et := 0) dLt (fun h => absurd rfl h) (fun _ => dA2 trivial)
          hstW0) (fun h => absurd h hsne) hstW0) hstW0) hstW0)
        (ss_cost_fin2 (by norm_num) (hcost _ (by omega)))
    | some t =>
      have htne : vt.length ≠ 0 := fun h => by have := hvt0.mp h; rw [hTt] at this; simp at this
      -- the entries are entries of the program
      obtain ⟨es, hes, hcons⟩ := hinv.slp
      have hsS' : (T[k / M]?).join = some s := by rw [hsS, hTs]
      have htS' : (T[k % M]?).join = some t := by rw [htS, hTt]
      obtain ⟨i, j, hij, -⟩ := ssGet_of_slot (B := B) hsS' (hM ▸ hp)
      obtain ⟨i', j', hij', -⟩ := ssGet_of_slot (B := B) htS' (hM ▸ hq)
      obtain ⟨hs1, hs2⟩ := List.getElem?_eq_some_iff.mp (hcons _ _ _ hij)
      obtain ⟨ht1, ht2⟩ := List.getElem?_eq_some_iff.mp (hcons _ _ _ hij')
      have hmul : slpEntries gs [.mul s.2 t.2] es = some (es ++ [s.1 * t.1]) := by
        rw [slpEntries_mul _ hs1 ht1, hs2, ht2]
      have hres : ssPair B M (T, prog) k = ssInsert B (T, prog) (s.1 * t.1) (.mul s.2 t.2) := by
        unfold ssPair; simp only [hsS, htS, hTs, hTt]
      rw [hres] at hstW ⊢
      have hins := ssInsertF_spec hP hinv hes hmul hY
      -- values
      have hsv : ssEncSlot (T[k / M]'hpT) = .list [encPerm s.1, .nat s.2] := by rw [hTs]; rfl
      have htv : ssEncSlot (T[k % M]'hqT) = .list [encPerm t.1, .nat t.2] := by rw [hTt]; rfl
      have hs2Z : s.2 ≤ ssZ Y := hidx _ (hTs ▸ List.getElem_mem hpT) s rfl
      have ht2Z : t.2 ≤ ssZ Y := hidx _ (hTt ▸ List.getElem_mem hqT) t rfl
      have hpw : ∀ σ : Perm (Fin n), (encPerm σ).wt ≤ ssW Y := fun σ =>
        (ssSmall_encPerm σ (Z := ssZ Y) (by omega)).wt_le
      have hsW : (Val.list [encPerm s.1, .nat s.2]).wt ≤ W := by
        rw [← hsv]; have := hslw _ hpT; omega
      have htW : (Val.list [encPerm t.1, .nat t.2]).wt ≤ W := by
        rw [← htv]; have := hslw _ hqT; omega
      set E3 := [a, ssEncSlot (T[k / M]'hpT), ssEncSlot (T[k % M]'hqT)] with hE3
      have dVs : StDC P E3 (.var 1) (.list [encPerm s.1, .nat s.2]) 1 0 W :=
        StDC.var' (by rw [hE3, ← hsv]; rfl) hsW
      have dVt : StDC P E3 (.var 2) (.list [encPerm t.1, .nat t.2]) 1 0 W :=
        StDC.var' (by rw [hE3, ← htv]; rfl) htW
      have dComp := StDC.call (StDC.mk2 (StDC.get (v := encPerm s.1) dVs (StDC.nat 0 (by omega)) rfl
          ((hpw _).trans (by omega)))
        (StDC.get dVt (StDC.nat 0 (by omega)) rfl ((hpw _).trans (by omega)))
        ((st_wt_list2 (hpw s.1) (hpw t.1)).trans (by omega)) (by omega))
        (compose_spec hP.siftAt.comp s.1 t.1) ((hpw _).trans (by omega))
      have hiW : (encSlpInstr (.mul s.2 t.2)).wt ≤ ssW Y :=
        (ssSmall_instr (Z := ssZ Y) (ins := .mul s.2 t.2)
          (by simp only [ssInsMax]; omega) (by omega)).wt_le
      have hiv : encSlpInstr (.mul s.2 t.2) = .list [.nat 2, .nat s.2, .nat t.2] := rfl
      have hW4 : 2 + 2 ≤ W := by omega
      have hW3 : 1 + 2 ≤ W := by omega
      have hs2W : (Val.nat s.2).wt ≤ W := (wt_nat_le _).trans (by omega)
      have ht2W : (Val.nat t.2).wt ≤ W := (wt_nat_le _).trans (by omega)
      have hIW : (Val.list [.nat 2, .nat s.2, .nat t.2]).wt ≤ W := by rw [← hiv]; omega
      have dI1 : StDC P E3 (.nat 2) (.nat 2) 1 0 W := StDC.nat 2 hW4
      have dI2 : StDC P E3 (.get (.var 1) (.nat 1)) (.nat s.2) 3 0 W :=
        StDC.get (x := 1) (vs := [encPerm s.1, .nat s.2]) dVs (StDC.nat 1 hW3) (by simp) hs2W
      have dI3 : StDC P E3 (.get (.var 2) (.nat 1)) (.nat t.2) 3 0 W :=
        StDC.get (x := 1) (vs := [encPerm t.1, .nat t.2]) dVt (StDC.nat 1 hW3) (by simp) ht2W
      have dI : StDC P E3 (mk3 (.nat 2) (.get (.var 1) (.nat 1)) (.get (.var 2) (.nat 1)))
          (.list [.nat 2, .nat s.2, .nat t.2]) 11 0 W := StDC.mk3 dI1 dI2 dI3 hIW (by omega)
      rw [← hiv] at dI
      have dA := StDC.mk4 (dArg 0 _ rfl hc _) (dArg 2 _ rfl hs _) dComp dI
        ((st_wt_list4 hc hs (hpw _) hiW).trans (by omega)) (by omega)
      exact StDC.funDet hf (StDC.letE dS (StDC.letE dT (StDC.ite (ne := 0) (Ee := 0) dLs
        (fun _ => StDC.ite (ne := 0) (Ee := 0) dLt (fun _ => StDC.call dA hins hstW)
          (fun h => absurd h htne) hstW) (fun h => absurd h hsne) hstW) hstW) hstW)
        (ss_cost_fin2 (by norm_num) (hcost _ (by omega)))

end GI.Impl
