import Workspace.Impl.SSChain

/-!
# One step of sifting, as a program

`ssSiftStepF comp inv` is the body of one step of the sifting loop (`ssSiftStep`). Its argument
is `[c, i, acc]` with the context `c = [n, B, T]` and the accumulator `acc = [g, used, stop]`.
If `stop ≠ 0` it returns `acc`. Otherwise it reads `b = B[i]` and `j = g b`; if `j = b` it
returns `acc`; otherwise it reads the slot `T[i·n + j]`: if the slot is empty it returns
`[g, used, i + 1]`, and if it holds `[t, k]` it returns `[t⁻¹ g, used ++ [k], 0]`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The body of one sifting step. -/
def ssSiftStepF (comp inv : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 2)) (arg 2)
    (.letE (.get (.get (arg 0) (.nat 1)) (arg 1))
      (.letE (.get (.get (arg 2) (.nat 0)) (.var 1))
        (.ite (.arith .eq (.var 2) (.var 1)) (arg 2)
          (.letE (.get (.get (arg 0) (.nat 2))
                    (.arith .add (.arith .mul (arg 1) (.get (arg 0) (.nat 0))) (.var 2)))
            (.ite (.length (.var 3))
              (mk3 (.call comp (mk2 (.call inv (.get (.var 3) (.nat 0))) (.get (arg 2) (.nat 0))))
                (.snoc (.get (arg 2) (.nat 1)) (.get (.var 3) (.nat 1))) (.nat 0))
              (mk3 (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1))
                (.arith .add (arg 1) (.nat 1))))))))

/-- The context of the sifting loop. -/
def ssSiftCtx (B : List (Fin n)) (T : List (SsSlot n)) : Val :=
  .list [.nat n, ssEncB B, ssEncTab T]

theorem ssEncPerm_get (g : Perm (Fin n)) (b : Fin n) :
    ((List.finRange n).map fun i => Val.nat (g i))[(b : ℕ)]? = some (.nat (g b)) :=
  encFun_getElem? (fun i => (g i : ℕ)) b

theorem ssEncB_get (B : List (Fin n)) {i : ℕ} (hi : i < B.length) :
    (B.map Fin.val |>.map Val.nat)[i]? = some (.nat B[i]) := by
  simp [hi]

theorem ss_cost_fin {k E W c1 c2 : ℕ} (hk : k ≤ 100) (hE : E ≤ c1 + c2) :
    k * (W + 1) + E ≤ 100 * (W + 1) + c1 + c2 := by
  have := Nat.mul_le_mul_right (W + 1) hk; omega

/-- **One sifting step.** -/
theorem ssSiftStepF_spec {P : Program} {f comp inv : ℕ}
    (hf : P.funs[f]? = some (ssSiftStepF comp inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv)) (B : List (Fin n)) (T : List (SsSlot n))
    (hT : T.length = B.length * n) (acc : Perm (Fin n) × List ℕ × ℕ) {i : ℕ} (hi : i < B.length)
    {W : ℕ} (hW1 : (Val.list [ssSiftCtx B T, .nat i, ssEncAcc acc]).wt ≤ W)
    (hW2 : (ssEncAcc (ssSiftStep B T acc i)).wt ≤ W) (hW3 : 30 * (n + 1) ^ 2 ≤ W)
    (hW4 : B.length * n + 2 ≤ W) :
    FunDet P f (.list [ssSiftCtx B T, .nat i, ssEncAcc acc]) (ssEncAcc (ssSiftStep B T acc i))
      (100 * (W + 1) + permK * (n + 1) ^ 3 + invK * (n + 1) ^ 4) := by
  obtain ⟨g, used, stop⟩ := acc
  -- weights, stated before the abbreviations
  have hca : (ssSiftCtx B T).wt < (Val.list [ssSiftCtx B T, .nat i, ssEncAcc (g, used, stop)]).wt :=
    wt_le_wt_list (by simp)
  have hAa : (ssEncAcc (g, used, stop)).wt <
      (Val.list [ssSiftCtx B T, .nat i, ssEncAcc (g, used, stop)]).wt := wt_le_wt_list (by simp)
  have hia : (Val.nat i).wt < (Val.list [ssSiftCtx B T, .nat i, ssEncAcc (g, used, stop)]).wt :=
    wt_le_wt_list (by simp)
  have hBc : (ssEncB B).wt < (ssSiftCtx B T).wt := wt_le_wt_list (by simp [ssSiftCtx])
  have hTc : (ssEncTab T).wt < (ssSiftCtx B T).wt := wt_le_wt_list (by simp [ssSiftCtx])
  have hgA : (encPerm g).wt < (ssEncAcc (g, used, stop)).wt := wt_le_wt_list (by simp [ssEncAcc])
  have huA : (natList used).wt < (ssEncAcc (g, used, stop)).wt := wt_le_wt_list (by simp [ssEncAcc])
  have hsA : (Val.nat stop).wt < (ssEncAcc (g, used, stop)).wt := wt_le_wt_list (by simp [ssEncAcc])
  set a := Val.list [ssSiftCtx B T, .nat i, ssEncAcc (g, used, stop)] with ha
  set c := ssSiftCtx B T with hc
  set A := ssEncAcc (g, used, stop) with hA
  have hn2 : n + 2 ≤ W := by nlinarith
  have hW4' : 4 ≤ W := by nlinarith
  have hpw : ∀ σ : Perm (Fin n), (encPerm σ).wt ≤ W := fun σ => by
    have := wt_encPerm_le σ; nlinarith
  have hnat : ∀ k, k ≤ n → (Val.nat k).wt ≤ W := fun k hk => (wt_nat_le k).trans (by omega)
  have haW : a.wt ≤ W := hW1
  -- reading the argument
  have dArg : ∀ j v, [c, Val.nat i, A][j]? = some v → ∀ rest : List Val,
      StDC P (a :: rest) (arg j) v 3 0 W := fun j v hv rest => by
    refine StDC.arg hv haW (by have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega) ?_
    have := wt_le_wt_list (List.mem_of_getElem? hv)
    exact (le_of_lt this).trans haW
  have dAcc := fun rest => dArg 2 A rfl rest
  have dStop : ∀ rest, StDC P (a :: rest) (.get (arg 2) (.nat 2)) (.nat stop) 5 0 W := fun rest =>
    (StDC.get (v := .nat stop) (dAcc rest) (StDC.nat 2 (by omega)) rfl (by omega)).mono (by omega) le_rfl
  have dG : ∀ rest, StDC P (a :: rest) (.get (arg 2) (.nat 0)) (encPerm g) 5 0 W := fun rest =>
    (StDC.get (dAcc rest) (StDC.nat 0 (by omega)) rfl (hpw g)).mono (by omega) le_rfl
  have dU : ∀ rest, StDC P (a :: rest) (.get (arg 2) (.nat 1)) (natList used) 5 0 W := fun rest =>
    (StDC.get (v := natList used) (dAcc rest) (StDC.nat 1 (by omega)) rfl (by omega)).mono (by omega) le_rfl
  have dC := fun rest => dArg 0 c rfl rest
  have dI := fun rest => dArg 1 (.nat i) rfl rest
  by_cases hstop : stop = 0
  swap
  · -- stopped: the accumulator is returned
    have hres : ssSiftStep B T (g, used, stop) i = (g, used, stop) := by
      unfold ssSiftStep; exact if_neg hstop
    rw [hres] at hW2 ⊢
    refine StDC.funDet hf (StDC.ite (ne := 0) (Ee := 0) (dStop []) (fun _ => dAcc [])
      (fun h => absurd h hstop) (by omega)) (ss_cost_fin (by norm_num) (by omega))
  subst hstop
  have hBi : B[i]? = some (B[i]'hi) := List.getElem?_eq_getElem hi
  have hBb := ssEncB_get B hi
  generalize hb : B[i]'hi = b at hBi hBb
  -- `b = B[i]` and `j = g b`
  have dB : ∀ rest, StDC P (a :: rest) (.get (.get (arg 0) (.nat 1)) (arg 1)) (.nat b) 9 0 W :=
    fun rest => (StDC.get (StDC.get (v := ssEncB B) (dC rest) (StDC.nat 1 (by omega)) rfl (by omega)) (dI rest)
      hBb (hnat b b.isLt.le)).mono (by omega) le_rfl
  set E1 := [a, Val.nat b] with hE1
  have dJ : StDC P E1 (.get (.get (arg 2) (.nat 0)) (.var 1)) (.nat (g b)) 7 0 W :=
    (StDC.get (dG [.nat b]) (StDC.var' rfl (hnat b b.isLt.le)) (ssEncPerm_get g b)
      (hnat _ (g b).isLt.le)).mono (by omega) le_rfl
  set E2 := [a, Val.nat b, .nat (g b)] with hE2
  have dEq : StDC P E2 (.arith .eq (.var 2) (.var 1)) (.nat (if (g b : ℕ) = b then 1 else 0))
      3 0 W :=
    StDC.arith (op := .eq) (StDC.var' rfl (hnat _ (g b).isLt.le)) (StDC.var' rfl (hnat b b.isLt.le))
      rfl (by split_ifs <;> exact (wt_nat_le _).trans (by omega))
  by_cases hdiag : g b = b
  · -- `g` fixes `B[i]`
    have hres : ssSiftStep B T (g, used, 0) i = (g, used, 0) := by
      simp [ssSiftStep, hBi, hdiag]
    rw [hres] at hW2 ⊢
    have hv : (if (g b : ℕ) = b then 1 else 0) = 1 := by simp [hdiag]
    rw [hv] at dEq
    have hAW : A.wt ≤ W := hW2
    refine StDC.funDet hf (StDC.ite (nt := 0) (Et := 0) (dStop []) (fun h => absurd rfl h)
      (fun _ => StDC.letE (dB []) (StDC.letE dJ (StDC.ite (ne := 0) (Ee := 0) dEq
        (fun _ => dArg 2 A rfl [.nat b, .nat (g b)]) (fun h => absurd h one_ne_zero) hAW) hAW) hAW)
      hAW) (ss_cost_fin (by norm_num) (by omega))
  -- the slot
  have hne : (g b : ℕ) ≠ b := fun h => hdiag (Fin.ext h)
  have hv : (if (g b : ℕ) = b then 1 else 0) = 0 := by simp [hne]
  rw [hv] at dEq
  set q := i * n + (g b : ℕ) with hq
  have hqT : q < T.length := by
    rw [hT]
    calc i * n + (g b : ℕ) < i * n + n := by have := (g b).isLt; omega
      _ = (i + 1) * n := by ring
      _ ≤ B.length * n := Nat.mul_le_mul_right _ hi
  have hqW : q + 2 ≤ W := by
    have : q < B.length * n := hT ▸ hqT
    omega
  have hTq : T[q]? = some T[q] := List.getElem?_eq_getElem hqT
  have hget : ssGet T i (g b) = T[q] := by
    show (T[i * n + (g b : ℕ)]?).join = T[q]
    rw [← hq, hTq]; rfl
  have hslot : ((T.map ssEncSlot))[q]? = some (ssEncSlot T[q]) := by simp [hqT]
  have hsT : (ssEncSlot T[q]).wt ≤ W := by
    have : (ssEncSlot T[q]).wt < (ssEncTab T).wt :=
      wt_le_wt_list (List.mem_map.mpr ⟨T[q], List.getElem_mem hqT, rfl⟩)
    omega
  have dQ : StDC P E2 (.arith .add (.arith .mul (arg 1) (.get (arg 0) (.nat 0))) (.var 2))
      (.nat q) 13 0 W := by
    have d1 := StDC.arith (op := .mul) (dI [.nat b, .nat (g b)])
      (StDC.get (dC [.nat b, .nat (g b)]) (StDC.nat 0 (by omega)) rfl (hnat n le_rfl)) rfl
      (show (Val.nat (i * n)).wt ≤ W from (wt_nat_le _).trans (by omega))
    exact (StDC.arith (op := .add) (z := q) d1 (StDC.var' rfl (hnat _ (g b).isLt.le)) rfl
      ((wt_nat_le _).trans hqW)).mono (by omega) le_rfl
  have dS : StDC P E2 (.get (.get (arg 0) (.nat 2))
      (.arith .add (.arith .mul (arg 1) (.get (arg 0) (.nat 0))) (.var 2))) (ssEncSlot T[q])
      20 0 W :=
    (StDC.get (StDC.get (v := ssEncTab T) (dC [.nat b, .nat (g b)]) (StDC.nat 2 (by omega)) rfl (by omega)) dQ
      hslot hsT).mono (by omega) le_rfl
  cases hTqv : T[q] with
  | none =>
    have hres : ssSiftStep B T (g, used, 0) i = (g, used, i + 1) := by
      simp [ssSiftStep, hBi, hdiag, hget, hTqv]
    rw [hres] at hW2 ⊢
    rw [hTqv] at dS hsT
    have dSv : StDC P [a, Val.nat b, .nat (g b), ssEncSlot (none : SsSlot n)] (.var 3) (ssEncSlot (none : SsSlot n)) 1 0 W :=
      StDC.var' rfl hsT
    have dL : StDC P [a, Val.nat b, .nat (g b), ssEncSlot (none : SsSlot n)] (.length (.var 3)) (.nat 0) 2 0 W :=
      StDC.length (vs := []) dSv (by simp; omega)
    have hi1 : (Val.nat (i + 1)).wt ≤ W :=
      (le_of_lt (wt_le_wt_list (show Val.nat (i + 1) ∈ [encPerm g, natList used, .nat (i + 1)] by
        simp))).trans hW2
    have dR : StDC P [a, Val.nat b, .nat (g b), ssEncSlot (none : SsSlot n)] (mk3 (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1))
        (.arith .add (arg 1) (.nat 1))) (ssEncAcc (g, used, i + 1)) 19 0 W :=
      (StDC.mk3 (dG _) (dU _) (StDC.arith (op := .add) (z := i + 1) (dI _) (StDC.nat 1 (by omega)) rfl hi1) hW2
        (by omega)).mono (by omega) le_rfl
    refine StDC.funDet hf (StDC.ite (nt := 0) (Et := 0) (dStop []) (fun h => absurd rfl h)
      (fun _ => StDC.letE (dB []) (StDC.letE dJ (StDC.ite (nt := 0) (Et := 0) dEq
        (fun h => absurd rfl h) (fun _ => StDC.letE dS (StDC.ite (nt := 0) (Et := 0) dL
          (fun h => absurd rfl h) (fun _ => dR) hW2) hW2) hW2) hW2) hW2) hW2)
      (ss_cost_fin (by norm_num) (by omega))
  | some e =>
    have hres : ssSiftStep B T (g, used, 0) i = (e.1⁻¹ * g, used ++ [e.2], 0) := by
      simp [ssSiftStep, hBi, hdiag, hget, hTqv]
    rw [hres] at hW2 ⊢
    rw [hTqv] at dS hsT
    have hev : ssEncSlot (some e) = .list [encPerm e.1, .nat e.2] := rfl
    rw [hev] at hsT
    have dSv : StDC P [a, Val.nat b, .nat (g b), ssEncSlot (some e)] (.var 3)
        (.list [encPerm e.1, .nat e.2]) 1 0 W := StDC.var' rfl hsT
    have he2 : (Val.nat e.2).wt ≤ W := (le_of_lt (wt_le_wt_list (by simp))).trans hsT
    have dL : StDC P [a, Val.nat b, .nat (g b), ssEncSlot (some e)] (.length (.var 3)) (.nat 2) 2 0 W :=
      StDC.length dSv (by simp; omega)
    have dInv := StDC.call (StDC.get dSv (StDC.nat 0 (by omega)) rfl (hpw e.1))
      (inv_spec hinv e.1) (hpw _)
    have hpair : (Val.list [encPerm e.1⁻¹, encPerm g]).wt ≤ W := by
      have h1 := wt_list2_le (encPerm e.1⁻¹) (encPerm g)
      have h2 := wt_encPerm_le e.1⁻¹
      have h3 := wt_encPerm_le g
      nlinarith
    have dComp := StDC.call (StDC.mk2 dInv (dG _) hpair (by omega)) (compose_spec hcomp _ _)
      (hpw _)
    have hul : (natList (used ++ [e.2])).wt ≤ W :=
      (le_of_lt (wt_le_wt_list (show natList (used ++ [e.2]) ∈
        [encPerm (e.1⁻¹ * g), natList (used ++ [e.2]), .nat 0] by simp))).trans hW2
    have dSn : StDC P [a, Val.nat b, .nat (g b), ssEncSlot (some e)] (.snoc (.get (arg 2) (.nat 1)) (.get (.var 3) (.nat 1)))
        (natList (used ++ [e.2])) 9 0 W := by
      have e' : natList (used ++ [e.2]) = .list (used.map Val.nat ++ [.nat e.2]) := by simp [natList]
      rw [e'] at hul ⊢
      exact (StDC.snoc (vs := used.map Val.nat) (dU [Val.nat b, .nat (g b), ssEncSlot (some e)])
        (StDC.get dSv (StDC.nat 1 (by omega)) rfl he2) hul).mono (by norm_num) (by norm_num)
    have dR := StDC.mk3 dComp dSn (StDC.nat 0 (by omega)) hW2 (by omega)
    refine StDC.funDet hf (StDC.ite (nt := 0) (Et := 0) (dStop []) (fun h => absurd rfl h)
      (fun _ => StDC.letE (dB []) (StDC.letE dJ (StDC.ite (nt := 0) (Et := 0) dEq
        (fun h => absurd rfl h) (fun _ => StDC.letE dS (StDC.ite (ne := 0) (Ee := 0) dL
          (fun _ => dR) (fun h => absurd h (by norm_num)) hW2) hW2) hW2) hW2) hW2) hW2)
      (ss_cost_fin (by norm_num) (by omega))

end GI.Impl
