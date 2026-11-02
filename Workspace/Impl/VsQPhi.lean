import Workspace.Impl.VsQGL
import Workspace.Impl.LinMembership
import Workspace.Impl.LinGroupSlp
import Workspace.Proved.VsQProb

/-!
# The matrix of a group element

Group elements are carried as permutations. To apply `φ(x)` for `x ∈ G = ⟨gs⟩`, the program asks
constructive membership for a straight-line program reaching `x` from `gs`, and evaluates it in
the matrix group `φ(G)` (`linGroupSlp_spec`), with the carried form `vsQE` of matrices. Inverses
are powers: every element of `φ(G)` has order dividing `n!`, so `u⁻¹ = u ^ (n! - 1)`; the
exponent `E = n! - 2` is stored in the carried form.

* `vsQPhiF`, `vsQPhiFuns b j mul inv` (7 functions), `vsQPhi_spec`: on `[Γ, x]` with
  `Γ = [encGroup gs, table, vsQE 1]` it returns `vsQE (φ x)`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Matrix Equiv

/-- On `[Γ, x]`: the SLP for `x`, evaluated with the table `Γ[1]` and identity `Γ[2]`. -/
def vsQPhiF (cm slp : ℕ) : Expr :=
  .letE (.call cm (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (.call slp (mk3 (.get (arg 0) (.nat 1)) (.get (.var 1) (.nat 1)) (.get (arg 0) (.nat 2))))

/-- The block at `b` (7 functions); constructive membership is primitive `j`, the group
operations are at `mul` and `inv`. -/
def vsQPhiFuns (b j mul inv : ℕ) : List Expr :=
  [vsQPhiF (b + 1) (b + 2), linMembershipF j] ++ linGroupSlpFuns (b + 2) mul inv

theorem vsQPhiFuns_length (b j mul inv : ℕ) : (vsQPhiFuns b j mul inv).length = 7 := rfl

variable (I : VecStabInst)

/-- The exponent stored for inverses. -/
def vsQExp : ℕ := I.n.factorial - 2

/-- The image `φ(G)`. -/
abbrev VsQImg := (I.φ).range

/-- The carried form of an element of `φ(G)`. -/
def vsQEnc (u : VsQImg I) : Val :=
  vsQE I.p I.d (vsQExp I) (((u : Matrix.GeneralLinearGroup (Fin I.d) (ZMod I.p))) : Matrix _ _ _)

/-- The table of the generators. -/
def vsQTable : Val := .list (I.gs.attach.map fun g =>
  vsQE I.p I.d (vsQExp I) ((I.φ ⟨g.1, Subgroup.subset_closure g.2⟩ : Matrix.GeneralLinearGroup _ _) :
    Matrix _ _ _))

/-- The global context of the evaluation. -/
def vsQGam : Val := .list [encGroup I.gs, vsQTable I, vsQE I.p I.d (vsQExp I) 1]

variable {I}

/-- Every element of `φ(G)` has `u ^ (vsQExp + 1) = u⁻¹`. -/
theorem vsQImg_pow (u : VsQImg I) : u ^ (vsQExp I + 1) = u⁻¹ := by
  obtain ⟨_, ⟨g, rfl⟩⟩ := u
  rcases Nat.lt_or_ge I.n 2 with hn | hn
  · have hg : (g : Perm (Fin I.n)) = 1 := by
      have : Subsingleton (Perm (Fin I.n)) := by
        rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_perm, Fintype.card_fin]
        rcases (show I.n = 0 ∨ I.n = 1 by omega) with h | h <;> rw [h] <;> decide
      exact Subsingleton.elim _ _
    have hg' : g = 1 := Subtype.ext hg
    subst hg'
    ext1
    simp
  · have h1 : (g : Perm (Fin I.n)) ^ I.n.factorial = 1 := by
      have := pow_card_eq_one (G := Perm (Fin I.n)) (x := (g : Perm (Fin I.n)))
      rwa [Fintype.card_perm, Fintype.card_fin] at this
    have h2 : g ^ I.n.factorial = 1 := Subtype.ext (by simpa using h1)
    have hf : 2 ≤ I.n.factorial := (Nat.self_le_factorial I.n).trans' hn
    have hu : (⟨I.φ g, g, rfl⟩ : VsQImg I) ^ I.n.factorial = 1 := by
      ext1; simp [← map_pow, h2]
    have e : vsQExp I + 1 + 1 = I.n.factorial := by unfold vsQExp; omega
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, e, hu]

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Matrix Equiv

theorem linGroupSlpCost_mono2 {W W' L L' B C : ℕ} (hW : W ≤ W') (hL : L ≤ L') :
    linGroupSlpCost W L B C ≤ linGroupSlpCost W' L' B C := by
  unfold linGroupSlpCost linGroupSlpLoopCost linGroupSlpLoopStepCost linGroupSlpStepCost
    linGroupSlpArg linVectorAccWt
  gcongr

/-- The cost of evaluating `φ(x)`. -/
def vsQPhiCost (cm W L N : ℕ) : ℕ :=
  cm + linGroupSlpCost W L (vsQW N) (10 ^ 8 * (N + 1) ^ 6) + 40 * W + 4 * vsQW N + 200

variable {I : VecStabInst}

/-- The generators in `φ(G)`. -/
def vsQGensImg (I : VecStabInst) : List (VsQImg I) :=
  (linSubgroupGenerators (gens I.gs) I.gs (fun g hg => Subgroup.subset_closure hg)).map
    I.φ.rangeRestrict

theorem vsQTable_eq : linGroupSlpTable (vsQEnc I) (vsQGensImg I) = vsQTable I := by
  simp [linGroupSlpTable, vsQGensImg, linSubgroupGenerators, vsQTable, vsQEnc, List.map_map,
    Function.comp_def]

set_option maxHeartbeats 1000000 in
/-- **The matrix of a group element.** -/
theorem vsQPhi_spec (hcm : ConstructiveMembership) {P : Program} {b j gl N : ℕ}
    (hb : P.HasAt b (vsQPhiFuns b j gl (gl + 2)))
    (hj : P.prims[j]? = some (linMembershipPrim hcm)) (hgl : P.HasAt gl (vsQGLFuns gl))
    (hsz : VsQSz I.p I.d (vsQExp I) N) {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) :
    FunDet P b (.list [vsQGam I, encPerm x]) (vsQE I.p I.d (vsQExp I) (vsQPhi I x))
      (vsQPhiCost (linMembershipCost hcm ⟨I.n, I.gs, x⟩)
        (4 * (Val.list [vsQGam I, encPerm x]).wt +
          2 * linMembershipWt (linMembershipDegree hcm) ⟨I.n, I.gs, x⟩ + 10)
        ((memberInput ⟨I.n, I.gs, x⟩).cells.length ^ linMembershipDegree hcm) N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h0 : P.funs[b]? = some (vsQPhiF (b + 1) (b + 2)) :=
    hb.get (j := 0) (by rw [vsQPhiFuns_length]; omega)
  have h1 : P.funs[b + 1]? = some (linMembershipF j) :=
    hb.get (j := 1) (by rw [vsQPhiFuns_length]; omega)
  have hslp : linGroupSlpAt P (b + 2) gl (gl + 2) := linGroupSlpAt_of (hb.block 2 rfl)
  set I' : MemberInst := ⟨I.n, I.gs, x⟩
  have hcm' := linMembership_member_spec hcm h1 hj I' hx
  -- the group operations on `φ(G)`
  have hB : ∀ u : VsQImg I, (vsQEnc I u).wt ≤ vsQW N := fun u => wt_vsQE_le hsz _
  have hm : ∀ u v : VsQImg I, FunDet P gl (.list [vsQEnc I u, vsQEnc I v]) (vsQEnc I (u * v))
      (6 * 10 ^ 6 * (N + 1) ^ 5) := fun u v => vsQMul_spec hgl hsz _ _
  have hi : ∀ u : VsQImg I, FunDet P (gl + 2) (vsQEnc I u) (vsQEnc I u⁻¹) (10 ^ 8 * (N + 1) ^ 6) := by
    intro u
    have := vsQInv_spec hgl hsz ((u : Matrix.GeneralLinearGroup (Fin I.d) (ZMod I.p)) : Matrix _ _ _)
    rw [← vsQImg_pow u]
    simpa [vsQEnc] using this
  have hm' : ∀ u v : VsQImg I, FunDet P gl (.list [vsQEnc I u, vsQEnc I v]) (vsQEnc I (u * v))
      (10 ^ 8 * (N + 1) ^ 6) := by
    intro u v
    refine (hm u v).mono ?_
    have : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  apply FunAll.intro h0
  refine EvalAll.letE (Ra := fun r c => (∃ prog : List SlpInstr,
      r = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
      prog.length ≤ (memberInput I').cells.length ^ linMembershipDegree hcm ∧
      SlpReaches I'.gs prog I'.x) ∧
      c ≤ 16 * (Val.list [vsQGam I, encPerm x]).wt + 80 + linMembershipCost hcm I' + r.wt + 1) ?_ ?_
  · have da := Det.mk2 (Det.get' (Det.arg' (P := P) (vs := [vsQGam I, encPerm x]) (rest := [])
      (j := 0) rfl) (Det.nat 0) (show [encGroup I.gs, vsQTable I,
        vsQE I.p I.d (vsQExp I) 1][0]? = some (encGroup I.gs) from rfl))
      (Det.arg' (P := P) (vs := [vsQGam I, encPerm x]) (rest := []) (j := 1) rfl)
    refine EvalAll.call_funAll da fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hcm'.mono fun w cb hw => ⟨hw.1, ?_⟩
    have wg : (encGroup I.gs).wt < (vsQGam I).wt := wt_le_wt_list (by simp [vsQGam])
    have wl := wt_list2_le (encGroup I.gs) (encPerm x)
    have wl2 := wt_list2_le (vsQGam I) (encPerm x)
    have w0 : (Val.nat 0).wt = 2 := rfl
    have w1 : (Val.nat 1).wt = 3 := rfl
    change ca + cb + w.wt + 1 ≤ _
    have := hw.2
    have wk : (vsQGam I).wt < (Val.list [vsQGam I, encPerm x]).wt := wt_le_wt_list (by simp)
    have wx : (encPerm x).wt < (Val.list [vsQGam I, encPerm x]).wt := wt_le_wt_list (by simp)
    omega
  · rintro r ca ⟨⟨prog, rfl, hlen, hreach⟩, hca⟩
    obtain ⟨y, hyx, hy⟩ := linSlpReaches_subgroup (gens I.gs) I.gs
      (fun g hg => Subgroup.subset_closure hg) prog x hreach
    have hv := linSlpValue_map I.φ.rangeRestrict
      (linSubgroupGenerators (gens I.gs) I.gs (fun g hg => Subgroup.subset_closure hg)) prog
    rw [hy] at hv
    have hv' : (linSlpEntries (vsQGensImg I) prog []).map (fun es => es.getLast?.getD 1) =
        some (I.φ.rangeRestrict y) := hv
    obtain ⟨es, hes, hlast⟩ : ∃ es, linSlpEntries (vsQGensImg I) prog [] = some es ∧
        es.getLast?.getD 1 = I.φ.rangeRestrict y := by
      cases he : linSlpEntries (vsQGensImg I) prog [] with
      | none => rw [he] at hv'; simp at hv'
      | some es =>
        refine ⟨es, rfl, ?_⟩
        rw [he] at hv'
        simpa using hv'
    have hs := linGroupSlp_spec hslp (vsQEnc I) hB hm' hi (vsQGensImg I) prog es hes
    rw [vsQTable_eq, hlast] at hs
    have he1 : vsQEnc I 1 = vsQE I.p I.d (vsQExp I) 1 := rfl
    rw [he1] at hs
    have hres : vsQEnc I (I.φ.rangeRestrict y) = vsQE I.p I.d (vsQExp I) (vsQPhi I x) := by
      rw [vsQPhi_of_mem hx]
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      subst this
      rfl
    rw [hres] at hs
    set r : Val := .list [.nat 1, .list (prog.map encSlpInstr)] with hr
    have g1 := Det.get' (Det.arg' (P := P) (vs := [vsQGam I, encPerm x]) (rest := [r]) (j := 0) rfl)
      (Det.nat 1) (show [encGroup I.gs, vsQTable I, vsQE I.p I.d (vsQExp I) 1][1]? =
        some (vsQTable I) from rfl)
    have g2 := Det.get' (Det.arg' (P := P) (vs := [vsQGam I, encPerm x]) (rest := [r]) (j := 0) rfl)
      (Det.nat 2) (show [encGroup I.gs, vsQTable I, vsQE I.p I.d (vsQExp I) 1][2]? =
        some (vsQE I.p I.d (vsQExp I) 1) from rfl)
    have gp := Det.get' (Det.var' (P := P) (env := [.list [vsQGam I, encPerm x], r]) (i := 1) rfl)
      (Det.nat 1) (show [Val.nat 1, .list (prog.map encSlpInstr)][1]? =
        some (.list (prog.map encSlpInstr)) from rfl)
    have dc := Det.call (Det.mk3 g1 gp g2) hs
    refine EvalAll.mono dc fun w cb hw => ⟨hw.1, ?_⟩
    obtain ⟨rfl, hcb⟩ := hw
    have hrw : r.wt ≤ linMembershipWt (linMembershipDegree hcm) I' :=
      linMembershipOut_wt ⟨prog, rfl, hlen, hreach⟩
    have wpl : (Val.list (prog.map encSlpInstr)).wt < r.wt := wt_le_wt_list (by simp [hr])
    have wt1 : (vsQTable I).wt < (vsQGam I).wt := wt_le_wt_list (by simp [vsQGam])
    have wt2 : (vsQE I.p I.d (vsQExp I) 1).wt < (vsQGam I).wt := wt_le_wt_list (by simp [vsQGam])
    have w3 := wt_list3_le (vsQTable I) (.list (prog.map encSlpInstr)) (vsQE I.p I.d (vsQExp I) 1)
    have wk : (vsQGam I).wt < (Val.list [vsQGam I, encPerm x]).wt := wt_le_wt_list (by simp)
    have wout := wt_vsQE_le hsz (vsQPhi I x)
    have hmono := linGroupSlpCost_mono2 (B := vsQW N) (C := 10 ^ 8 * (N + 1) ^ 6)
      (W := (Val.list [vsQTable I, .list (prog.map encSlpInstr), vsQE I.p I.d (vsQExp I) 1]).wt)
      (W' := 4 * (Val.list [vsQGam I, encPerm x]).wt +
        2 * linMembershipWt (linMembershipDegree hcm) I' + 10) (by omega)
      hlen
    have w1 : (Val.nat 1).wt = 3 := rfl
    have w2 : (Val.nat 2).wt = 4 := rfl
    have w0 : (Val.nat 0).wt = 2 := rfl
    have hri : (Val.list [Val.nat 1, Val.list (List.map encSlpInstr prog)]).wt = r.wt := rfl
    unfold vsQPhiCost
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at *
    have hvw : vsQW N = 100 * (N + 1) ^ 3 := rfl
    omega

end GI.Impl
