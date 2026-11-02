import Workspace.Impl.SSEnc

/-!
# The chain of a sift, as a program

`ssChainF` is one link (`ssChain`): on `[N, acc, u]` it appends `inv u` and
`mul (N + |acc|) (N + |acc| - 1)`. The fold `foldlFuns b ssChainF` over the used indices gives
`used.foldl (ssChain N) loc0` (`ssChainFold_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

/-- One link of the chain, on `[N, acc, u]`. -/
def ssChainF : Expr :=
  .snoc (.snoc (arg 1) (mk2 (.nat 1) (arg 2)))
    (mk3 (.nat 2) (.arith .add (arg 0) (.length (arg 1)))
      (.arith .sub (.arith .add (arg 0) (.length (arg 1))) (.nat 1)))

theorem ssChain_enc (N : ℕ) (acc : List SlpInstr) (u : ℕ) :
    ssEncProg (ssChain N acc u) = .list (acc.map encSlpInstr ++ [.list [.nat 1, .nat u]] ++
      [.list [.nat 2, .nat (N + acc.length), .nat (N + acc.length - 1)]]) := by
  simp [ssEncProg, ssChain, encSlpInstr]

/-- **One link.** -/
theorem ssChainF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some ssChainF) (N : ℕ)
    (acc : List SlpInstr) (u : ℕ) :
    FunDet P f (.list [.nat N, ssEncProg acc, .nat u]) (ssEncProg (ssChain N acc u))
      (40 * ((Val.list [.nat N, ssEncProg acc, .nat u]).wt +
        (ssEncProg (ssChain N acc u)).wt + 1)) := by
  set a := Val.list [.nat N, ssEncProg acc, .nat u] with ha
  set r := ssEncProg (ssChain N acc u) with hr
  set W := a.wt + r.wt with hW
  have hr' := ssChain_enc N acc u
  rw [← hr] at hr'
  have haW : a.wt ≤ W := by omega
  have hrW : r.wt ≤ W := by omega
  have hpa : (ssEncProg acc).wt ≤ W := by
    have : (ssEncProg acc).wt < a.wt := wt_le_wt_list (by simp [ha]); omega
  have hNa : (Val.nat N).wt ≤ W := by
    have : (Val.nat N).wt < a.wt := wt_le_wt_list (by simp [ha]); omega
  have hua : (Val.nat u).wt ≤ W := by
    have : (Val.nat u).wt < a.wt := wt_le_wt_list (by simp [ha]); omega
  have h4 : 4 ≤ W := by
    have h3 : 3 < a.wt := length_lt_wt_list [Val.nat N, ssEncProg acc, .nat u]
    omega
  -- pieces of the result
  set i1 := Val.list [.nat 1, .nat u]
  set i2 := Val.list [.nat 2, .nat (N + acc.length), .nat (N + acc.length - 1)]
  have hmem1 : i1 ∈ acc.map encSlpInstr ++ [i1] ++ [i2] := by simp
  have hmem2 : i2 ∈ acc.map encSlpInstr ++ [i1] ++ [i2] := by simp
  rw [hr'] at hrW
  have hi1 : i1.wt ≤ W := (wt_le_wt_list hmem1).le.trans hrW
  have hi2 : i2.wt ≤ W := (wt_le_wt_list hmem2).le.trans hrW
  have hpre : (Val.list (acc.map encSlpInstr ++ [i1])).wt ≤ W :=
    (wt_list_mono (List.prefix_append _ _)).trans hrW
  have hs1 : (Val.nat (N + acc.length)).wt ≤ W :=
    (wt_le_wt_list (show Val.nat (N + acc.length) ∈ [.nat 2, .nat (N + acc.length),
      .nat (N + acc.length - 1)] by simp)).le.trans hi2
  have hs2 : (Val.nat (N + acc.length - 1)).wt ≤ W :=
    (wt_le_wt_list (show Val.nat (N + acc.length - 1) ∈ [.nat 2, .nat (N + acc.length),
      .nat (N + acc.length - 1)] by simp)).le.trans hi2
  have hlen : (Val.nat acc.length).wt ≤ W := by
    calc (Val.nat acc.length).wt = GI.Machine.len acc.length + 2 := wt_nat' _
      _ ≤ GI.Machine.len (N + acc.length) + 2 := by
          have := GI.Machine.len_mono (show acc.length ≤ N + acc.length by omega); omega
      _ = (Val.nat (N + acc.length)).wt := (wt_nat' _).symm
      _ ≤ W := hs1
  have hn1 : (Val.nat 1).wt ≤ W := by have : (Val.nat 1).wt = 3 := rfl; omega
  have hn2 : (Val.nat 2).wt ≤ W := (wt_le_wt_list (show Val.nat 2 ∈ [.nat 2, .nat (N + acc.length),
      .nat (N + acc.length - 1)] by simp)).le.trans hi2
  have dA : ∀ j v, [Val.nat N, ssEncProg acc, .nat u][j]? = some v → v.wt ≤ W →
      StDC P [a] (arg j) v 3 0 W := fun j v hv hw =>
    StDC.arg hv haW (by have : j < 3 := (List.getElem?_eq_some_iff.mp hv).1; omega) hw
  have dP : StDC P [a] (arg 1) (.list (acc.map encSlpInstr)) 3 0 W := dA 1 _ rfl hpa
  have hlenP : (acc.map encSlpInstr).length + 2 ≤ W := by
    have := length_lt_wt_list (acc.map encSlpInstr ++ [i1] ++ [i2])
    simp only [List.length_append, List.length_map, List.length_singleton] at this ⊢
    omega
  have dL : StDC P [a] (.length (arg 1)) (.nat acc.length) 4 0 W := by
    simpa using StDC.length dP hlenP
  have dS1 := StDC.arith (op := .add) (dA 0 _ rfl hNa) dL rfl hs1
  have dS2 := StDC.arith (op := .sub) dS1 (StDC.nat 1 (by omega)) rfl hs2
  have dI2 := StDC.mk3 (StDC.nat 2 (by omega)) dS1 dS2 hi2 h4
  have dI1 := StDC.mk2 (StDC.nat 1 (by omega)) (dA 2 _ rfl hua) hi1 h4
  have dT1 := StDC.snoc dP dI1 hpre
  have dT2 := StDC.snoc dT1 dI2 hrW
  refine StDC.funDet hf (P := P) (by rw [hr']; exact dT2) ?_
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem ssChain_prefix (N : ℕ) : ∀ (X : List ℕ) (loc : List SlpInstr),
    loc <+: X.foldl (ssChain N) loc := by
  intro X
  induction X with
  | nil => intro loc; exact List.prefix_refl _
  | cons u X ih =>
    intro loc
    rw [List.foldl_cons]
    exact (List.prefix_append _ _).trans (ih _)

theorem ssChain_take_prefix (N : ℕ) (X : List ℕ) (loc : List SlpInstr) (i : ℕ) :
    (X.take i).foldl (ssChain N) loc <+: X.foldl (ssChain N) loc := by
  conv_rhs => rw [← List.take_append_drop i X]
  rw [List.foldl_append]
  exact ssChain_prefix N _ _

theorem wt_ssEncProg_mono {p q : List SlpInstr} (h : p <+: q) :
    (ssEncProg p).wt ≤ (ssEncProg q).wt :=
  wt_list_mono (List.IsPrefix.map _ h)

theorem ss_fold_cost {c S L A M : ℕ}
    (hc : c ≤ S + loopModK * (L + 1) * (A + L + M + 1))
    (hS : S ≤ L * (40 * (2 * (A + M + A) + 7 + M + 1))) (hL : L ≤ A) :
    c ≤ 5000 * (A + M + 1) ^ 2 := by
  have k1 : L * (40 * (2 * (A + M + A) + 7 + M + 1)) ≤ 320 * (A + M + 1) ^ 2 := by
    calc L * (40 * (2 * (A + M + A) + 7 + M + 1))
        ≤ (A + M + 1) * (320 * (A + M + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 320 * (A + M + 1) ^ 2 := by ring
  have k2 : loopModK * (L + 1) * (A + L + M + 1) ≤ 2000 * (A + M + 1) ^ 2 := by
    unfold loopModK
    calc 1000 * (L + 1) * (A + L + M + 1)
        ≤ 1000 * (A + M + 1) * (2 * (A + M + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 2000 * (A + M + 1) ^ 2 := by ring
  omega

/-- **The chain.** -/
theorem ssChainFold_spec {P : Program} {b g : ℕ} (h : P.HasAt b (foldlFuns b g))
    (hg : P.funs[g]? = some ssChainF) (N : ℕ) (used : List ℕ) (loc0 : List SlpInstr) :
    FunAll P b (.list [.nat N, natList used, ssEncProg loc0]) (fun w c =>
      w = ssEncProg (used.foldl (ssChain N) loc0) ∧
      c ≤ 5000 * ((Val.list [.nat N, natList used, ssEncProg loc0]).wt +
        (ssEncProg (used.foldl (ssChain N) loc0)).wt + 1) ^ 2) := by
  set a := Val.list [.nat N, natList used, ssEncProg loc0] with ha
  set M := (ssEncProg (used.foldl (ssChain N) loc0)).wt with hM
  have hxs : (Val.list (used.map Val.nat)).wt < a.wt := wt_le_wt_list (by simp [natList])
  have hNa : (Val.nat N).wt < a.wt := wt_le_wt_list (by simp)
  have hlen := length_lt_wt_list (used.map Val.nat)
  have hstep : ∀ i acc (hi : i < (used.map Val.nat).length),
      acc = ssEncProg ((used.take i).foldl (ssChain N) loc0) →
      FunAll P g (.list [.nat N, acc, (used.map Val.nat)[i]]) (fun w cost =>
        w = ssEncProg ((used.take (i + 1)).foldl (ssChain N) loc0) ∧
        cost ≤ 40 * (2 * (a.wt + M + a.wt) + 7 + M + 1)) := by
    rintro i acc hi rfl
    simp only [List.length_map] at hi
    have hui : (used.map Val.nat)[i] = .nat used[i] := by simp
    rw [hui]
    have htake : (used.take (i + 1)).foldl (ssChain N) loc0 =
        ssChain N ((used.take i).foldl (ssChain N) loc0) used[i] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
      rfl
    refine FunAll.mono (ssChainF_spec hg N _ used[i]) fun w c ⟨hw, hc⟩ => ⟨by rw [hw, htake], ?_⟩
    have h1 := wt_list3_le (.nat N) (ssEncProg ((used.take i).foldl (ssChain N) loc0)) (.nat used[i])
    have h2 : (ssEncProg ((used.take i).foldl (ssChain N) loc0)).wt ≤ M :=
      wt_ssEncProg_mono (ssChain_take_prefix N used loc0 i)
    have h3 : (ssEncProg (ssChain N ((used.take i).foldl (ssChain N) loc0) used[i])).wt ≤ M := by
      rw [← htake]; exact wt_ssEncProg_mono (ssChain_take_prefix N used loc0 (i + 1))
    have h4 : (Val.nat used[i]).wt < a.wt :=
      lt_trans (wt_le_wt_list (by simp)) hxs
    omega
  refine (foldl_spec h (Inv := fun i acc => acc = ssEncProg ((used.take i).foldl (ssChain N) loc0))
    (M := M) (B := fun _ => 40 * (2 * (a.wt + M + a.wt) + 7 + M + 1)) (by simp)
    (fun i acc _ hacc => by rw [hacc]; exact wt_ssEncProg_mono (ssChain_take_prefix N used loc0 i))
    hstep).mono fun w c ⟨hw, hc⟩ => ⟨by simpa using hw, ?_⟩
  have hl : (used.map Val.nat).length ≤ a.wt := by omega
  exact ss_fold_cost hc (by simp) hl

end GI.Impl
