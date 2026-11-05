module

public import Workspace.Impl.TermGlueLabPSetP

@[expose] public section

/-!
# The setup of step 5 when no generators of `N` are stored (`t = 0`)

Step 5 of the label program. The setup program (`tmGLPSet_spec`) needs at least
one stored generator of `N` (the quotient program runs on a `t × t` matrix with `0 < t`). When
the stored list `σN` is empty, `N = ⟨σN⟩ = 1`, so `A/B(x)` is trivial and its coordinates
have no entries: the context is `[0, [], [], []]` (`tmGLP_setOut_nil`: it meets `TmGLPSetOut`
with `0 × 0` matrices).

`tmGLPSetDF set` tests `t` (the length of the stored list, read from `encGroup σN`, which has
`1` in front) and runs the setup program only when `0 < t`. `tmGLPSetD_spec` is
`tmGLPSet_spec` without the hypothesis `0 < t`, so step 5 runs for every `σN`.
-/

namespace GI.Impl

open GI.Lang Equiv
open scoped IsMulCommutative
open GI.Cited (Val encInt encIntMatrix encPerm encGroup gens FullRankInst fullRankInput)

variable {n : ℕ}

theorem tmGLP_gens_nil_eq (g : Perm (Fin n)) (hg : g ∈ gens ([] : List (Perm (Fin n)))) :
    g = 1 := by
  have h : gens ([] : List (Perm (Fin n))) = ⊥ := by
    simp [gens]
  rw [h] at hg
  exact Subgroup.mem_bot.mp hg

instance tmGLP_gens_nil_sub : Subsingleton (gens ([] : List (Perm (Fin n)))) :=
  ⟨fun a b => Subtype.ext ((tmGLP_gens_nil_eq _ a.2).trans (tmGLP_gens_nil_eq _ b.2).symm)⟩

/-- **The presentation with no generators.** -/
theorem tmGLP_pres_nil (σS : List (Perm (Fin n))) (M : Matrix (Fin 0) (Fin 0) ℤ) :
    linPermPresentation σS ([] : List (Perm (Fin n))) M := by
  haveI : IsEmpty (Fin ([] : List (Perm (Fin n))).length) := Fin.isEmpty'
  set G := gens ([] : List (Perm (Fin n)))
  set K := (gens σS).subgroupOf G
  have hN : K.Normal := ⟨fun a _ g => by
    rw [Subsingleton.elim g 1]; simpa⟩
  letI := hN
  haveI hsub : Subsingleton (G ⧸ K) := ⟨fun a b => by
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact congrArg _ (Subsingleton.elim _ _)⟩
  have hQ : IsMulCommutative (G ⧸ K) := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  refine ⟨hN, hQ, ?_⟩
  letI := hQ
  refine ⟨by simp [Matrix.det_isEmpty], fun y => ⟨0, Subsingleton.elim _ _⟩, fun z _ => ?_, ?_⟩
  · rw [LinearMap.mem_ker, Subsingleton.elim z 0]
    exact LinearMap.map_zero _
  · rw [Matrix.det_isEmpty, Int.natAbs_one]
    haveI : Subsingleton (Additive (G ⧸ K)) := hsub
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨Additive.ofMul 1⟩⟩

/-- **The context with no generators** meets `TmGLPSetOut`. -/
theorem tmGLP_setOut_nil (σS bs : List (Perm (Fin n)))
    (hbs : ∀ b ∈ bs, b ∈ gens ([] : List (Perm (Fin n)))) :
    TmGLPSetOut σS ([] : List (Perm (Fin n))) bs (.list [.nat 0, .list [], .list [], .list []]) := by
  haveI : IsEmpty (Fin ([] : List (Perm (Fin n))).length) := Fin.isEmpty'
  refine ⟨0, 0, 1, 1, 1, ?_, tmGLP_pres_nil σS 0, fun j => ?_, by simp, fun i => i.elim0,
    fun w => ?_, by simp, by simp⟩
  · simp [tmGLPMCtx, encIntMatrix, linVecVal]
  · have h1 : bs[j.val]'j.isLt = 1 := tmGLP_gens_nil_eq _ (hbs _ (List.getElem_mem _))
    rw [h1]
    refine ⟨[], ⟨[], rfl, rfl⟩, ?_⟩
    simp only [linExponentValue, linSlpValue, linSlpEntries, Option.map_some]
    exact congrArg some (Subsingleton.elim _ _)
  · exact ⟨fun _ i => i.elim0, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The setup for every `t`**, on `[gens N*, gens N, [b_j]]`. -/
def tmGLPSetDF (set : ℕ) : Expr :=
  .ite (.arith .sub (.length (.get (arg 1) (.nat 1))) (.nat 1)) (.call set (.var 0))
    (mk4 (.nat 0) .nil .nil .nil)

def tmGLPSetDC (FA FQ FI : ℕ → ℕ) (Ce De W : ℕ) : ℕ :=
  3 * tmGLPSetC FA FQ FI Ce De W + 100 * (W + 1) + 1000

theorem tmGLPSetC_mono {FA FQ FI : ℕ → ℕ} (hFA : Monotone FA) (hFQ : Monotone FQ)
    (hFI : Monotone FI) (Ce De : ℕ) : Monotone (tmGLPSetC FA FQ FI Ce De) := by
  intro W W' h
  have hA : tmGLPSetA FA W ≤ tmGLPSetA FA W' := hFA (by omega)
  have hZ : tmGLPSetZ Ce De W ≤ tmGLPSetZ Ce De W' :=
    tmGLPItemsC_mono (fun a b h => by unfold tmGLPBud; gcongr) (by omega)
  have hAp : tmGLPSetAp FA Ce De W ≤ tmGLPSetAp FA Ce De W' := by
    unfold tmGLPSetAp; gcongr
  have hQ : tmGLPSetQ FA FQ Ce De W ≤ tmGLPSetQ FA FQ Ce De W' := hFQ (by omega)
  have hI : tmGLPSetI FA FQ FI Ce De W ≤ tmGLPSetI FA FQ FI Ce De W' := hFI (by omega)
  unfold tmGLPSetC
  omega

theorem tmGLPSetDC_mono {FA FQ FI : ℕ → ℕ} (hFA : Monotone FA) (hFQ : Monotone FQ)
    (hFI : Monotone FI) (Ce De : ℕ) : Monotone (tmGLPSetDC FA FQ FI Ce De) := by
  intro W W' h
  have := tmGLPSetC_mono hFA hFQ hFI Ce De h
  unfold tmGLPSetDC
  omega

/-- **The setup for every `t`.** The hypotheses are those of `tmGLPSet_spec` without `0 < t`. -/
theorem tmGLPSetD_spec (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {fd f abel mec ec jm ap quo inv : ℕ} (hfd : P.funs[fd]? = some (tmGLPSetDF f))
    (hf : P.funs[f]? = some (tmGLPSetF abel mec ap quo inv))
    (σS σN bs : List (Perm (Fin n)))
    {FA FQ FI : ℕ → ℕ} (hFA : Monotone FA) (hFQ : Monotone FQ) (hFI : Monotone FI)
    (hab : FunAll P abel (.list [encGroup σS, encGroup σN]) (fun out c =>
      (∃ M : Matrix (Fin σN.length) (Fin σN.length) ℤ, out = encIntMatrix M ∧
        linPermPresentation σS σN M) ∧ c ≤ FA (Val.list [encGroup σS, encGroup σN]).wt))
    (hmec : P.HasAt mec (mapFuns mec ec)) (hec : linElementCoordinatesAt P ec jm hm)
    {Ce De : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hbs : ∀ b ∈ bs, b ∈ gens σN) (hap : P.HasAt ap (appendFuns ap))
    (hquo : ∀ I : FullRankInst, FunAll P quo (fullRankInput I) (fun out c =>
      TmGLQOut I.A out ∧ c ≤ FQ (fullRankInput I).wt))
    (hinv : ∀ {t : ℕ} (ht : 0 < t) (V : Matrix (Fin t) (Fin t) ℤ) (hV : IsUnit V.det),
      FunAll P inv (fullRankInput (tmGLPInst ht V hV)) (fun w c =>
        ∃ U : Matrix (Fin t) (Fin t) ℤ, w = encIntMatrix U ∧ U * V = 1 ∧ V * U = 1 ∧
          c ≤ FI (fullRankInput (tmGLPInst ht V hV)).wt)) :
    FunAll P fd (.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]) (fun w c =>
      TmGLPSetOut σS σN bs w ∧ c ≤ tmGLPSetDC FA FQ FI Ce De
        (Val.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]).wt) := by
  set a : Val := .list [encGroup σS, encGroup σN, .list (bs.map encPerm)] with ha
  set W := a.wt with hW
  set gl : List Val := (1 :: σN).map encPerm with hgl
  have eN : encGroup σN = .list [.nat n, .list gl] := rfl
  have d1 : Det P [a] (arg 1) (.list [.nat n, .list gl]) _ := Det.arg' (vs := [encGroup σS,
    encGroup σN, .list (bs.map encPerm)]) (rest := []) (j := 1) (by rw [eN]; rfl)
  have dl := Det.length (Det.get' d1 (Det.nat 1) (x := 1) (vs := [.nat n, .list gl]) rfl)
  have hlen : gl.length = σN.length + 1 := by simp [hgl]
  rw [hlen] at dl
  have dt := Det.arith' (op := .sub) dl (Det.nat 1) (z := σN.length) (by simp [GI.Machine.BinOp.eval])
  have wN : (encGroup σN).wt < W := wt_le_wt_list (by simp)
  have wgl : (Val.list gl).wt < (encGroup σN).wt := by rw [eN]; exact wt_le_wt_list (by simp)
  have lgl := length_lt_wt_list gl
  have : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  have : (Val.nat σN.length).wt ≤ σN.length + 2 := wt_nat_le _
  apply FunAll.intro hfd
  rcases Nat.eq_zero_or_pos σN.length with h0 | hpos
  · -- no stored generators
    obtain rfl : σN = [] := List.length_eq_zero_iff.mp h0
    have dz := Det.ite_zero (t := .call f (.var 0)) dt
      (Det.mk4 (P := P) (env := [a]) (Det.nat 0) Det.nil Det.nil Det.nil)
    refine dz.post fun c hc => ⟨tmGLP_setOut_nil σS bs hbs, ?_⟩
    have : (Val.list [Val.nat 0, Val.list [], Val.list [], Val.list []]).wt ≤ 100 := by decide
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have e1 : (Val.list [encGroup σS, encGroup ([] : List (Perm (Fin n))),
      .list (bs.map encPerm)]).wt = W := rfl
    unfold tmGLPSetDC
    simp only [List.length_nil] at *
    omega
  · -- the setup program
    have hs := tmGLPSet_spec hm hf σS σN bs hpos hFA hFQ hFI hab hmec hec hEB hbs hap hquo hinv
    have dv := Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl
    refine EvalAll.ite dt (fun _ _ h => ⟨σN.length, h.1⟩) fun y cc h => ?_
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_neg (by omega)]
    refine EvalAll.call_funAll dv fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine FunAll.mono (FunAll.wt_lt hs) fun w c ⟨⟨hw, hc⟩, hww⟩ => ⟨hw, ?_⟩
    have e1 : (Val.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]).wt = W := rfl
    have el : tmGLPSetC FA FQ FI Ce De
      (Val.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]).wt =
        tmGLPSetC FA FQ FI Ce De W := rfl
    unfold tmGLPSetDC
    omega

end GI.Impl
