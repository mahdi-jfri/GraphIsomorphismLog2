module

public import Workspace.Degree.Enum
public import Workspace.Impl.Orbit

@[expose] public section

/-!
# The orbit chain of the degree algorithm

The text of `Iface.orbitSpec` of the general algorithm, with `ChildPost` in place of `Iface.Post`.
The first call runs on the largest orbit (`firstChild`). When its answer is not empty, the second
call runs on the rest under the automorphism group of the first orbit (`secondChild`). The step does
not use the threshold of the general algorithm. It only needs a state that is not transitive.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- The call on the largest orbit. -/
noncomputable def firstChild (S : State Ω C) {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) : State Ω C :=
  S.inherit S.G D₁ hD₁.invariant S.x S.y

theorem orbit_rest_inv (S : State Ω C) {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) :
    Invariant (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) :=
  (S.dom_inv.diff hD₁.invariant).mono (autGroup_le S.G D₁ hD₁.invariant S.x)

/-- The call on the rest of the domain, with the target moved by `t`. -/
noncomputable def secondChild (S : State Ω C) {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) (t : Perm Ω) :
    State Ω C :=
  S.resetChild _ _ (orbit_rest_inv S hD₁) S.x (S.y ∘ t)

/-- **The answer of the first child**, as `first_answer` of the general algorithm, with the exact
answer. -/
theorem first_answerD {S₁ : State Ω C} {G : Subgroup (Perm Ω)} {D₁ : Set Ω}
    (hD₁ : Invariant G D₁) {x y : Ω → C} (h₁ : S₁.Inst G D₁ x y)
    {e : Ω ≃ Fin k} {x₁ : Perm (Fin k)} {gs : List (Perm (Fin k))}
    (hA : toFin e '' S₁.answer = x₁ • (gens gs : Set (Perm (Fin k)))) :
    (toFin e).symm x₁ ∈ S₁.answer ∧ gens gs = groupFin e (autGroup G D₁ hD₁ x) := by
  have ht := toFin_symm_apply_mem hA
  refine ⟨ht, ?_⟩
  have hex : S₁.answer = answer G D₁ x y := State.answer_of_inst h₁
  rw [hex] at ht hA
  rw [answer_eq_smul_aut hD₁ ht, toFin_image_coset, MulEquiv.apply_symm_apply] at hA
  have h2 := congrArg (fun X : Set (Perm (Fin k)) => x₁⁻¹ • X) hA
  simp only [inv_smul_smul] at h2
  exact SetLike.coe_injective h2.symm

/-- **The orbit chain meets its specification.** -/
theorem orbit_specD {Pg : Program} {F : Funs} {f bl bs bg bc : ℕ}
    (hf : Pg.funs[f]? = some (orbitBody F bl bs bg bc))
    (hlo : Pg.HasAt bl (loFuns bl)) (hsp : Pg.HasAt bs (splitFuns bs))
    (hga : Pg.HasAt bg (gatherFuns bg)) (hco : Pg.HasAt bc (composeFuns bc))
    (Bc : State Ω C → ℝ) (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C} {v : Val}
    (hv' : Canon e c v S) (hne : S.dom.Nonempty) (hint : ¬ S.Transitive)
    (hcall₁ : ∀ (D₁ : Set Ω) (hD₁ : S.LargestOrbit D₁) (val : Val),
      Canon e c val (firstChild S hD₁) →
      FunAll Pg F.cont val (ChildPost Bc (firstChild S hD₁) e))
    (hcall₂ : ∀ (D₁ : Set Ω) (hD₁ : S.LargestOrbit D₁) (t : Perm Ω) (val : Val),
      Canon e c val (secondChild S hD₁ t) →
      FunAll Pg F.cont val (ChildPost Bc (secondChild S hD₁ t) e)) :
    FunAll Pg f v (fun u cost => AnsC e u S.answer ∧ ∃ (D₁ : Set Ω) (hD₁ : S.LargestOrbit D₁)
      (L : List (State Ω C)), (L = [firstChild S hD₁] ∨
          ∃ t, L = [firstChild S hD₁, secondChild S hD₁ t]) ∧
        (cost : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + (L.map Bc).sum) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  have hwv := hv'.wt_le
  obtain ⟨gv, dv, xv, yv, hv0, rv, hgv, hdv, hxv, hyv, hhv, hrv, hvv⟩ := hv'.val
  obtain ⟨gs, rfl, hgens, hl⟩ := hgv
  have hdv' : dv = indVal e S.dom := hdv
  subst hdv' hvv
  -- The largest orbit.
  obtain ⟨D₁, hsub, horb, hlarge, hloD⟩ :=
    lo_spec hlo e S.dom_inv hne hgens hl
  have hD₁ : S.LargestOrbit D₁ := ⟨hsub, horb, hlarge⟩
  set T₁ := S.inherit S.G D₁ hD₁.invariant S.x S.y with hT₁
  have hcan₁ := canon_first hv' hD₁
  have hcall₁' := hcall₁ D₁ hD₁ _ hcan₁
  refine FunAll.intro hf ?_
  -- Step 1: the largest orbit.
  have d1 := Det.call (Det.mk2 (Det.arg' (P := Pg) (vs := [.nat k, encGroup gs, indVal e S.dom, xv,
    yv, hv0, rv, boolVal S.floor, .nat S.h, .nat S.N]) (rest := []) (j := 1) rfl)
    (Det.arg' (j := 2) rfl)) hloD
  refine EvalAll.letE d1 fun pv cp hp => ?_
  obtain ⟨rfl, hcp⟩ := hp
  refine EvalAll.letE (Det.get' (Det.var' (i := 1)
    (v := .list [indVal e D₁, indVal e (S.dom \ D₁)]) rfl) (Det.nat 0) (v := indVal e D₁) rfl)
    fun d1v cd1 hd1 => ?_
  obtain ⟨rfl, hcd1⟩ := hd1
  refine EvalAll.letE (Det.get' (Det.var' (i := 1)
    (v := .list [indVal e D₁, indVal e (S.dom \ D₁)]) rfl) (Det.nat 1)
    (v := indVal e (S.dom \ D₁)) rfl) fun d2v cd2 hd2 => ?_
  obtain ⟨rfl, hcd2⟩ := hd2
  -- Weights.
  have wD : ∀ D' : Set Ω, (indVal e D').wt ≤ k * 7 + 4 := fun D' => DomVal.wt_le (domVal_indVal e D')
  have wG : (encGroup gs).wt < stateW k S := (wt_le_wt_list (by simp)).trans_le hwv
  have wY : yv.wt < stateW k S := (wt_le_wt_list (by simp)).trans_le hwv
  have wAW : 8 * (k + 1) ^ 2 ≤ ansW k := by unfold ansW; omega
  have wkk : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have wC₁ := (Canon.wt_le hcan₁).trans (stateW_first (k := k) S hD₁)
  have wL := wt_list2_le (encGroup gs) (indVal e S.dom)
  have wP := wt_list2_le (indVal e D₁) (indVal e (S.dom \ D₁))
  have wD₁ := wD D₁
  have wD₂ := wD (S.dom \ D₁)
  have wD₀ := wD S.dom
  -- The bound `Z¹⁵`.
  have hZ1 : 1 ≤ (stateW k S + ansW k + 1) ^ 15 := Nat.one_le_pow _ _ (by omega)
  have hZZ : stateW k S + ansW k + 1 ≤ (stateW k S + ansW k + 1) ^ 15 :=
    Nat.le_self_pow (by norm_num) _
  have hkZ : (k + 1) ^ 15 ≤ (stateW k S + ansW k + 1) ^ 15 :=
    Nat.pow_le_pow_left (by have : k + 1 ≤ stateW k S := (by unfold stateW; omega); omega) _
  -- Step 1b: the row test of the first child.
  classical
  have hspl := split_spec hsp e S hrv hD₁.nonempty
  have wRV : rv.wt < stateW k S := (wt_le_wt_list (by simp)).trans_le hwv
  have wSP := wt_list2_le rv (indVal e D₁)
  refine EvalAll.letE (Det.call (Det.mk2 (Det.arg' (j := 6) (v := rv) rfl)
    (Det.var' (i := 2) (v := indVal e D₁) rfl)) hspl) fun spv csp hspv => ?_
  obtain ⟨rfl, hcsp⟩ := hspv
  have wsp : (Val.nat (if S.ColsSplit D₁ then 1 else 0)).wt ≤ 3 := by
    split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hspZ : splitK * ((Val.list [rv, indVal e D₁]).wt + 1) ^ 3 ≤
      splitK * 125 * (stateW k S + ansW k + 1) ^ 15 := by
    have h1 : (Val.list [rv, indVal e D₁]).wt + 1 ≤ 5 * (stateW k S + ansW k + 1) := by
      have := wD D₁; have : k * 7 + 4 ≤ stateW k S := by unfold stateW; omega
      omega
    have h2 : (stateW k S + ansW k + 1) ^ 3 ≤ (stateW k S + ansW k + 1) ^ 15 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    calc splitK * ((Val.list [rv, indVal e D₁]).wt + 1) ^ 3
        ≤ splitK * (5 * (stateW k S + ansW k + 1)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
      _ = splitK * 125 * (stateW k S + ansW k + 1) ^ 3 := by ring
      _ ≤ splitK * 125 * (stateW k S + ansW k + 1) ^ 15 := Nat.mul_le_mul_left _ h2
  -- Step 2: `Continue` on the first orbit.
  refine EvalAll.letE (call_childD (firstArg_det (eS := .var 4) (eD := .var 2)
    (c := 6 * stateW k S + 2 * ansW k + 60) ((Det.var' (i := 4) rfl).mono (by omega))
    ((Det.var' (i := 2) rfl).mono (by have := wD D₁; omega)) (by omega)) hcall₁')
    fun u₁ cu₁ hu₁ => ?_
  obtain ⟨cb₁, hA₁, hcb₁, hcu₁⟩ := hu₁
  have wu₁ := hA₁.wt_le
  have hin₁ : T₁.Inst S.G D₁ S.x S.y := S.inherit_inst _ _ _ _ _
  rcases hA₁ with ⟨rfl, hE₁⟩ | ⟨x₁, gs₁, rfl, hl₁, hA₁⟩
  · -- The first answer is empty: so is the answer (`Run.orbitStop`).
    refine EvalAll.ite (Det.length (Det.var' (i := 5) (v := .list []) rfl)) (fun _ _ h => ⟨_, h.1⟩)
      fun x cc hx => ?_
    obtain ⟨hx, hcc⟩ := hx
    cases hx
    simp only [List.length_nil, if_true]
    refine (Det.var' (i := 5) (v := .list []) rfl).post fun c' hc' => ?_
    refine ⟨Or.inl ⟨rfl, (step_orbitStop hD₁ hin₁ hE₁.symm).symm⟩, D₁, hD₁, [T₁], Or.inl rfl, ?_⟩
    have key : ∀ n : ℕ, n ≤ orbK * (stateW k S + ansW k + 1) ^ 15 + cb₁ →
        (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + ([T₁].map Bc).sum := by
      intro n hn
      have hn' : (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + cb₁ := by
        exact_mod_cast hn
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h1 : (cb₁ : ℝ) ≤ Bc T₁ := hcb₁
      linarith
    apply key
    simp only [List.length_nil] at hcc
    simp only [orbK, loK, splitK] at hcp hcsp hspZ ⊢
    omega
  · -- The first answer is `[t, H₁]`.
    obtain ⟨ht, hgens₁⟩ := first_answerD hD₁.invariant (S₁ := T₁) hin₁ hA₁
    have htx : toFin e ((toFin e).symm x₁) = x₁ := MulEquiv.apply_symm_apply _ _
    generalize (toFin e).symm x₁ = t at ht htx
    refine EvalAll.ite (Det.length (Det.var' (i := 5) (v := .list [encPerm x₁, encGroup gs₁]) rfl))
      (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
    obtain ⟨hx, hcc⟩ := hx
    cases hx
    rw [if_neg (show [encPerm x₁, encGroup gs₁].length ≠ 0 by simp)]
    refine EvalAll.letE (Det.get' (Det.var' (i := 5) (v := .list [encPerm x₁, encGroup gs₁]) rfl)
      (Det.nat 0) (v := encPerm x₁) rfl) fun xv₁ cx₁ hx₁ => ?_
    obtain ⟨rfl, hcx₁⟩ := hx₁
    refine EvalAll.letE (Det.get' (Det.var' (i := 5) (v := .list [encPerm x₁, encGroup gs₁]) rfl)
      (Det.nat 1) (v := encGroup gs₁) rfl) fun gv₁ cg₁ hg₁ => ?_
    obtain ⟨rfl, hcg₁⟩ := hg₁
    -- Step 3: the colors `y ∘ t`.
    have hyv' : yv = .list ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))) := hyv
    have hgat := gather_spec hga (L := (List.finRange k).map fun i => Val.nat (c (S.y (e.symm i))))
      (is := (List.finRange k).map fun i => (x₁ i : ℕ)) (by simp)
    rw [← htx, gather_colors e c S.y t, ← encPerm_eq_natList, htx, ← hyv'] at hgat
    refine EvalAll.letE (Det.call (Det.mk2 (Det.arg' (j := 4) (v := yv) rfl)
      (Det.var' (i := 6) (v := encPerm x₁) rfl)) hgat) fun y₂ cy₂ hy₂ => ?_
    obtain ⟨rfl, hcy₂⟩ := hy₂
    -- Step 4: `Continue` on the rest.
    have hinv := orbit_rest_inv S hD₁
    have hcan₂ := canon_resetChild hv' (D' := S.dom \ D₁) (hD' := hinv) (y' := S.y ∘ t)
      (gv' := encGroup gs₁) (yv' := encFun fun i => c ((S.y ∘ t) (e.symm i)))
      ⟨gs₁, rfl, hgens₁, hl₁⟩ rfl (fun a => (hv'.colors (t a)).2)
    have hcall₂' := hcall₂ D₁ hD₁ t _ hcan₂
    have wC₂ := (Canon.wt_le hcan₂).trans (stateW_resetChild (k := k) S _ _ hinv S.x (S.y ∘ t))
    have wY₂ : (encFun fun i => c ((S.y ∘ t) (e.symm i))).wt <
        (childVal k (encGroup gs₁) (indVal e (S.dom \ D₁)) xv
          (encFun fun i => c ((S.y ∘ t) (e.symm i))) hv0 S.N).wt := wt_le_wt_list (by simp)
    have wG₁ : (encGroup gs₁).wt < (Val.list [encPerm x₁, encGroup gs₁]).wt :=
      wt_le_wt_list (by simp)
    have wX₁ : (encPerm x₁).wt < (Val.list [encPerm x₁, encGroup gs₁]).wt :=
      wt_le_wt_list (by simp)
    have wYX := wt_list2_le yv (encPerm x₁)
    have wpx₁ := wt_encPerm_le x₁
    have hZ3 : (stateW k S + ansW k + 1) ^ 3 ≤ (stateW k S + ansW k + 1) ^ 15 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    have hg3 : ((Val.list [yv, encPerm x₁]).wt + 1) ^ 3 ≤ 343 * (stateW k S + ansW k + 1) ^ 15 := by
      have h1 : (Val.list [yv, encPerm x₁]).wt + 1 ≤ 7 * (stateW k S + ansW k + 1) := by omega
      calc ((Val.list [yv, encPerm x₁]).wt + 1) ^ 3 ≤ (7 * (stateW k S + ansW k + 1)) ^ 3 :=
            Nat.pow_le_pow_left h1 3
        _ = 343 * (stateW k S + ansW k + 1) ^ 3 := by ring
        _ ≤ 343 * (stateW k S + ansW k + 1) ^ 15 := Nat.mul_le_mul_left _ hZ3
    have ey₂ : (Val.list ((List.finRange k).map fun i => Val.nat (c ((S.y ∘ t) (e.symm i))))).wt =
        (encFun fun i => c ((S.y ∘ t) (e.symm i))).wt := rfl
    have hk3 : (k + 1) ^ 3 ≤ (stateW k S + ansW k + 1) ^ 15 :=
      (Nat.pow_le_pow_right (by omega) (by norm_num : 3 ≤ 15)).trans hkZ
    refine EvalAll.letE (call_childD (childArg_det (eG := .var 7) (eD := .var 3) (eY := .var 8)
      (c := 2 * stateW k S + 2 * ansW k + 20) ((Det.var' (i := 7) rfl).mono (by omega))
      ((Det.var' (i := 3) rfl).mono (by omega))
      ((Det.var' (i := 8) rfl).mono (by omega)) (by omega)) hcall₂') fun u₂ cu₂ hu₂ => ?_
    obtain ⟨cb₂, hA₂, hcb₂, hcu₂⟩ := hu₂
    have wu₂ := hA₂.wt_le
    have hch : t • (secondChild S hD₁ t).answer = S.answer :=
      step_orbitChain hD₁ hin₁ t ht (S₂ := secondChild S hD₁ t) ⟨rfl, rfl, rfl, rfl⟩ rfl rfl
    rcases hA₂ with ⟨rfl, hE₂⟩ | ⟨x₂, gs₂, rfl, hl₂, hA₂⟩
    · -- The second answer is empty: so is the answer.
      refine EvalAll.ite (Det.length (Det.var' (i := 9) (v := .list []) rfl))
        (fun _ _ h => ⟨_, h.1⟩) fun x cc' hx => ?_
      obtain ⟨hx, hcc'⟩ := hx
      cases hx
      simp only [List.length_nil, if_true]
      refine (Det.var' (i := 9) (v := .list []) rfl).post fun c' hc' => ?_
      have hE : (∅ : Set (Perm Ω)) = S.answer := by
        rw [← hch, hE₂, Set.smul_set_empty]
      refine ⟨Or.inl ⟨rfl, hE.symm⟩, D₁, hD₁, _, Or.inr ⟨t, rfl⟩, ?_⟩
      have key : ∀ n : ℕ, n ≤ orbK * (stateW k S + ansW k + 1) ^ 15 + cb₁ + cb₂ →
          (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) +
            ([T₁, secondChild S hD₁ t].map Bc).sum := by
        intro n hn
        have hn' : (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + cb₁ + cb₂ := by
          exact_mod_cast hn
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have h1 : (cb₁ : ℝ) ≤ Bc T₁ := hcb₁
        have h2 : (cb₂ : ℝ) ≤ Bc (secondChild S hD₁ t) := hcb₂
        linarith
      apply key
      simp only [List.length_nil, List.length_cons] at hcc hcc'
      simp only [orbK, loK, gatherK, splitK] at hcp hcy₂ hc' hcsp hspZ ⊢
      omega
    · -- The answer `[t t₂, H₂]`.
      refine EvalAll.ite (Det.length (Det.var' (i := 9)
        (v := .list [encPerm x₂, encGroup gs₂]) rfl)) (fun _ _ h => ⟨_, h.1⟩) fun x cc' hx => ?_
      obtain ⟨hx, hcc'⟩ := hx
      cases hx
      rw [if_neg (show [encPerm x₂, encGroup gs₂].length ≠ 0 by simp)]
      refine (Det.mk2 (Det.call (Det.mk2 (Det.var' (i := 6) rfl)
        (Det.get' (Det.var' (i := 9) (v := .list [encPerm x₂, encGroup gs₂]) rfl) (Det.nat 0)
          (v := encPerm x₂) rfl)) (compose_spec hco x₁ x₂))
        (Det.get' (Det.var' (i := 9) (v := .list [encPerm x₂, encGroup gs₂]) rfl) (Det.nat 1)
          (v := encGroup gs₂) rfl)).post fun c' hc' => ?_
      refine ⟨Or.inr ⟨x₁ * x₂, gs₂, rfl, hl₂, ?_⟩, D₁, hD₁, _, Or.inr ⟨t, rfl⟩, ?_⟩
      · rw [← hch, chain_answer hA₂, htx]
      have key : ∀ n : ℕ, n ≤ orbK * (stateW k S + ansW k + 1) ^ 15 + cb₁ + cb₂ →
          (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) +
            ([T₁, secondChild S hD₁ t].map Bc).sum := by
        intro n hn
        have hn' : (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + cb₁ + cb₂ := by
          exact_mod_cast hn
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have h1 : (cb₁ : ℝ) ≤ Bc T₁ := hcb₁
        have h2 : (cb₂ : ℝ) ≤ Bc (secondChild S hD₁ t) := hcb₂
        linarith
      have := wt_encPerm_le x₂
      have := wt_encPerm_le (x₁ * x₂)
      have := wt_list2_le (encPerm x₁) (encPerm x₂)
      have := wt_list2_le (encPerm (x₁ * x₂)) (encGroup gs₂)
      have : (encGroup gs₂).wt < (Val.list [encPerm x₂, encGroup gs₂]).wt := wt_le_wt_list (by simp)
      apply key
      simp only [List.length_nil, List.length_cons] at hcc hcc'
      simp only [orbK, loK, gatherK, permK, splitK] at hcp hcy₂ hc' hcsp hspZ ⊢
      omega


end GI.Degree
