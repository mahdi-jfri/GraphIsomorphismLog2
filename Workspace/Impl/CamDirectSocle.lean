module

public import Workspace.Impl.CamDirectFactor

@[expose] public section

/-!
# Direct socle search for Cameron–Maróti groups

This file implements the chief-series-free socle-finding subroutine from Proposition 2.3 of
`Workspace/CamDirectSocle.lean`:

* `camSocleInnerStep`: for fixed `(y₁, z)`, computes the `(G_{x₀, y₁})`-orbit `O` of `z`, the
  pointwise stabilizer `P` of `O` in `G_{x₀}`, its derived subgroup `D = ⁅P, P⁆`, and updates the
  best accumulator with the normal closure of `D` in `G` (`camSocleCand G x₀ y₁ z`).
* `camSocleOuterStep`: for fixed `y₁`, computes `G_{x₀, y₁}` and runs the inner `n`-step loop over
  `z < n`.
* `camSocleFuns` and `camSocle_spec`: runs the outer `n`-step loop over `y₁ < n` via
  `camSearchEntryBody`. Under `MarotiStructure (gens gs) e` and `IsPreprimitive (gens gs) (Fin n)`
  (`25 ≤ n`, `5 ≤ m`, `1 ≤ k`, `2 * k < m`), Proposition 2.3 (`camSocleCand_min_eq_socle`)
  guarantees that the returned generator list `w` satisfies `GensVal n w (camProd e Finset.univ)`.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp len len_le_self)

variable {n m k r : ℕ}

/-! ### 1. Candidate sets for the 2D `(y₁, z)` search -/

/-- Candidates tested after outer steps `0, …, i - 1`. -/
def camSocleOuterCands (G : Subgroup (Perm (Fin n))) (x₀ : Fin n) (i : ℕ) :
    Set (Subgroup (Perm (Fin n))) :=
  {K | ∃ y₁ z : Fin n, (y₁ : ℕ) < i ∧ K = camSocleCand G x₀ y₁ z}

/-- Candidates tested after outer steps `0, …, i - 1` and inner steps `0, …, j - 1` at `y₁`. -/
def camSocleInnerCands (G : Subgroup (Perm (Fin n))) (x₀ y₁ : Fin n) (i j : ℕ) :
    Set (Subgroup (Perm (Fin n))) :=
  camSocleOuterCands G x₀ i ∪ {K | ∃ z : Fin n, (z : ℕ) < j ∧ K = camSocleCand G x₀ y₁ z}

theorem camSocleOuterCands_zero (G : Subgroup (Perm (Fin n))) (x₀ : Fin n) :
    camSocleOuterCands G x₀ 0 = ∅ := by
  ext K; simp [camSocleOuterCands]

theorem camSocleInnerCands_zero (G : Subgroup (Perm (Fin n))) (x₀ y₁ : Fin n) (i : ℕ) :
    camSocleInnerCands G x₀ y₁ i 0 = camSocleOuterCands G x₀ i := by
  ext K; simp [camSocleInnerCands]

theorem camSocleInnerCands_succ (G : Subgroup (Perm (Fin n))) (x₀ y₁ : Fin n) (i : ℕ)
    {j : ℕ} (hj : j < n) :
    insert (camSocleCand G x₀ y₁ ⟨j, hj⟩) (camSocleInnerCands G x₀ y₁ i j) =
      camSocleInnerCands G x₀ y₁ i (j + 1) := by
  ext K
  simp only [Set.mem_insert_iff, camSocleInnerCands, Set.mem_union, Set.mem_ofPred]
  constructor
  · rintro (rfl | h | ⟨z, hz, rfl⟩)
    · exact Or.inr ⟨⟨j, hj⟩, by simp, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, by omega, rfl⟩
  · rintro (h | ⟨z, hz, rfl⟩)
    · exact Or.inr (Or.inl h)
    · rcases eq_or_ne (z : ℕ) j with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨z, by omega, rfl⟩)

theorem camSocleInnerCands_full (G : Subgroup (Perm (Fin n))) (x₀ : Fin n) {i : ℕ} (hi : i < n) :
    camSocleInnerCands G x₀ ⟨i, hi⟩ i n = camSocleOuterCands G x₀ (i + 1) := by
  ext K
  simp only [camSocleInnerCands, camSocleOuterCands, Set.mem_union, Set.mem_ofPred]
  constructor
  · rintro (⟨y₁, z, hy₁, rfl⟩ | ⟨z, _, rfl⟩)
    · exact ⟨y₁, z, by omega, rfl⟩
    · exact ⟨⟨i, hi⟩, z, by simp, rfl⟩
  · rintro ⟨y₁, z, hy₁, rfl⟩
    rcases eq_or_ne (y₁ : ℕ) i with h | hne
    · have hy₁_eq : y₁ = ⟨i, hi⟩ := Fin.ext h
      subst hy₁_eq
      exact Or.inr ⟨z, z.isLt, rfl⟩
    · exact Or.inl ⟨y₁, z, by omega, rfl⟩

/-! ### 2. Inner and outer loop steps and module layout -/

/-- Argument size bound for all cited primitives called during `camSocle`. -/
def camSocleB (gv : Val) (n : ℕ) : ℕ := 2 * gv.wt + 2000 * (n + 1) ^ 6

/-- On `[[gv_G, gv_G₀, gv_H₁], .nat z, acc]`:
1. `pts ← camOrbList [gv_H₁, .nat z]`
2. `w_P ← pointwiseStab [gv_G₀, pts]`
3. `gv_P ← mkGroup [n, w_P]`
4. `w_D ← derivedSubgroup gv_P`
5. `camNclBest [gv_G, w_D, acc]`. -/
def camSocleInnerStep (orb mg nb jp jd : ℕ) : Expr :=
  .letE (.call orb (mk2 (.get (arg 0) (.nat 2)) (arg 1)))
  (.letE (.prim jp (mk2 (.get (arg 0) (.nat 1)) (.var 1)))
  (.letE (.call mg (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 2)))
  (.letE (.prim jd (.var 3))
    (.call nb (mk3 (.get (arg 0) (.nat 0)) (.var 4) (arg 2))))))

/-- On `[[gv_G, gv_G₀], .nat y₁, acc]`:
1. `w_H₁ ← pointwiseStab [gv_G, [.nat 0, .nat y₁]]`
2. `gv_H₁ ← mkGroup [n, w_H₁]`
3. `call iit [[gv_G, gv_G₀, gv_H₁], .nat n, acc]`. -/
def camSocleOuterStep (mg iit jp : ℕ) : Expr :=
  .letE (.prim jp (mk2 (.get (arg 0) (.nat 0)) (mk2 (.nat 0) (arg 1))))
  (.letE (.call mg (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 1)))
    (.call iit (mk3
      (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.var 2))
      (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (arg 2))))

/-- All functions of the direct socle search at base `b` (58 functions). -/
def camSocleFuns (b jo jp jn jd : ℕ) : List Expr :=
  [camSearchEntryBody (b + 10) (b + 1) jp] ++
    iterFuns (b + 1) (b + 4) ++
    [camSocleOuterStep (b + 10) (b + 5) jp] ++
    iterFuns (b + 5) (b + 8) ++
    [camSocleInnerStep (b + 18) (b + 10) (b + 9) jp jd,
      camNclBestBody (b + 10) (b + 17) jo jn] ++
    mkGroupFuns (b + 10) ++
    [camKeepBest] ++
    camOrbListFuns (b + 18)

theorem length_camSocleFuns (b jo jp jn jd : ℕ) : (camSocleFuns b jo jp jn jd).length = 58 := by
  simp [camSocleFuns, iterFuns, loopFuns, mkGroupFuns, rangeFuns, appendFuns,
    length_camOrbListFuns]

/-- Where the parts of `camSocleFuns` sit. -/
structure CamSocleAt (P : Program) (b jo jp jn jd : ℕ) (ho : GroupOrder) (hp : PointwiseStab)
    (hncl : NormalClosure) (hd : DerivedSubgroup) : Prop where
  entry : P.funs[b]? = some (camSearchEntryBody (b + 10) (b + 1) jp)
  oiter : P.HasAt (b + 1) (iterFuns (b + 1) (b + 4))
  ostep : P.funs[b + 4]? = some (camSocleOuterStep (b + 10) (b + 5) jp)
  iiter : P.HasAt (b + 5) (iterFuns (b + 5) (b + 8))
  istep : P.funs[b + 8]? = some (camSocleInnerStep (b + 18) (b + 10) (b + 9) jp jd)
  nb : P.funs[b + 9]? = some (camNclBestBody (b + 10) (b + 17) jo jn)
  mg : P.HasAt (b + 10) (mkGroupFuns (b + 10))
  kb : P.funs[b + 17]? = some camKeepBest
  orb : CamOrbListAt P (b + 18)
  po : P.prims[jo]? = some (groupOrderPrim ho)
  pp : P.prims[jp]? = some (pointwiseStabPrim hp)
  pn : P.prims[jn]? = some (normalClosurePrim hncl)
  pd : P.prims[jd]? = some (derivedSubgroupPrim hd)

theorem camSocleAt_of {P : Program} {b jo jp jn jd : ℕ} {ho : GroupOrder} {hp : PointwiseStab}
    {hncl : NormalClosure} {hd : DerivedSubgroup} (h : P.HasAt b (camSocleFuns b jo jp jn jd))
    (po : P.prims[jo]? = some (groupOrderPrim ho))
    (pp : P.prims[jp]? = some (pointwiseStabPrim hp))
    (pn : P.prims[jn]? = some (normalClosurePrim hncl))
    (pd : P.prims[jd]? = some (derivedSubgroupPrim hd)) :
    CamSocleAt P b jo jp jn jd ho hp hncl hd := by
  simp only [camSocleFuns] at h
  have h2 := h.left.left.left.right
  exact
  { entry := h.left.left.left.left.left.left.left.single
    oiter := by simpa using h.left.left.left.left.left.left.right
    ostep := by
      simpa [iterFuns, loopFuns, Nat.add_assoc] using h.left.left.left.left.left.right.single
    iiter := by simpa [iterFuns, loopFuns, Nat.add_assoc] using h.left.left.left.left.right
    istep := by simpa [iterFuns, loopFuns, Nat.add_assoc] using h2 0 (by simp)
    nb := by simpa [iterFuns, loopFuns, Nat.add_assoc] using h2 1 (by simp)
    mg := by simpa [iterFuns, loopFuns, Nat.add_assoc] using h.left.left.right
    kb := by
      simpa [iterFuns, loopFuns, mkGroupFuns, rangeFuns, appendFuns, Nat.add_assoc] using
        h.left.right.single
    orb := camOrbListAt_of (by
      simpa [iterFuns, loopFuns, mkGroupFuns, rangeFuns, appendFuns, Nat.add_assoc] using h.right)
    po := po, pp := pp, pn := pn, pd := pd }

/-! ### 3. Step specifications and main socle specification -/

def camSocleInnerStepK : ℕ := 2 * 10 ^ 9

/-- One inner step `z = j < n` of the direct socle search. -/
theorem camSocleInnerStep_spec {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    {hd : DerivedSubgroup} {P : Program} {b jo jp jn jd : ℕ}
    (hP : CamSocleAt P b jo jp jn jd ho hp hncl hd)
    (gs hs₀ hs₁ : List (Perm (Fin n))) (hhs₀l : hs₀.length ≤ n ^ 2) (hhs₁l : hs₁.length ≤ n ^ 2)
    {x₀ y₁ : Fin n} (h0g : gens hs₀ = pointwiseStab (gens gs) [x₀])
    (h1g : gens hs₁ = pointwiseStab (gens gs) [x₀, y₁])
    {i j : ℕ} (hj : j < n) {acc : Val}
    (hinv : CamBestInv (camSocleInnerCands (gens gs) x₀ y₁ i j) acc) :
    FunAll P (b + 8) (.list [.list [encGroup gs, encGroup hs₀, encGroup hs₁], .nat j, acc])
      (fun w cost => CamBestInv (camSocleInnerCands (gens gs) x₀ y₁ i (j + 1)) w ∧
        cost ≤ (groupOrderPrim ho).boundSize (camSocleB (encGroup gs) n) +
          (pointwiseStabPrim hp).boundSize (camSocleB (encGroup gs) n) +
          (normalClosurePrim hncl).boundSize (camSocleB (encGroup gs) n) +
          (derivedSubgroupPrim hd).boundSize (camSocleB (encGroup gs) n) +
          camSocleInnerStepK * ((encGroup gs).wt + (n + 1) ^ 15)) := by
  set z : Fin n := ⟨j, hj⟩
  set c := Val.list [encGroup gs, encGroup hs₀, encGroup hs₁]
  set a := Val.list [c, .nat j, acc]
  have dA0 := fun (rest : List Val) =>
    Det.arg' (P := P) (vs := [c, .nat j, acc]) (rest := rest) (j := 0) rfl
  have dG := fun (rest : List Val) =>
    Det.get' (dA0 rest) (Det.nat 0)
      (show [encGroup gs, encGroup hs₀, encGroup hs₁][0]? = some (encGroup gs) from rfl)
  have dG0 := fun (rest : List Val) =>
    Det.get' (dA0 rest) (Det.nat 1)
      (show [encGroup gs, encGroup hs₀, encGroup hs₁][1]? = some (encGroup hs₀) from rfl)
  have dH1 := fun (rest : List Val) =>
    Det.get' (dA0 rest) (Det.nat 2)
      (show [encGroup gs, encGroup hs₀, encGroup hs₁][2]? = some (encGroup hs₁) from rfl)
  have dN := fun (rest : List Val) => Det.encPerms_size (gs := 1 :: gs) (dG rest)
  -- 1. camOrbList on [encGroup hs₁, .nat z]
  obtain ⟨O, hO, hOl, hOmem, fO⟩ := camOrbList_spec hP.orb hs₁ hhs₁l z
  have d1 := Det.call (Det.mk2 (dH1 [])
    (Det.arg' (P := P) (vs := [c, .nat j, acc]) (rest := []) (j := 1) rfl)) fO
  refine FunAll.intro hP.istep (EvalAll.letE d1 fun vO cO h1 => ?_)
  obtain ⟨rfl, hcO⟩ := h1
  -- 2. pointwiseStab on [encGroup hs₀, encPts O]
  set E1 := [a, encPts O]
  have d2a := Det.mk2 (dG0 [encPts O]) (Det.var' (P := P) (env := E1) (i := 1) rfl)
  refine EvalAll.letE (pointwiseStab_call hp hP.pp d2a ⟨hs₀, rfl, rfl⟩) fun w_P cP h2 => ?_
  obtain ⟨hw_P, hcP⟩ := h2
  have hP_eq : pointwiseStab (gens hs₀) O =
      camOrbStab (gens gs) (pointwiseStab (gens gs) [x₀, y₁]) x₀ z := by
    rw [h0g]
    exact pointwiseStab_eq_camOrbStab (gens gs) (pointwiseStab (gens gs) [x₀, y₁]) x₀ z O
      fun y => by rw [hOmem, h1g]
  rw [hP_eq] at hw_P
  -- 3. mkGroup on w_P
  obtain ⟨ps, rfl, hpsl, fP, ⟨ps', hPe, hPg⟩, hPw⟩ := mkGroup_gensVal hP.mg hw_P
  obtain rfl := encGroup_injective hPe
  set E2 := [a, encPts O, .list (ps.map encPerm)]
  have d3 := Det.call (Det.mk2 (dN [encPts O, .list (ps.map encPerm)])
    (Det.var' (P := P) (env := E2) (i := 2) rfl)) fP
  refine EvalAll.letE d3 fun vP cmP h3 => ?_
  obtain ⟨rfl, hcmP⟩ := h3
  -- 4. derivedSubgroup on encGroup ps
  set E3 := [a, encPts O, .list (ps.map encPerm), encGroup ps]
  have d4 := derivedSubgroup_call hd hP.pd (Det.var' (P := P) (env := E3) (i := 3) rfl)
    ⟨ps, rfl, hPg⟩
  refine EvalAll.letE d4 fun w_D cD h4 => ?_
  obtain ⟨hw_D, hcD⟩ := h4
  -- 5. camNclBest on [encGroup gs, w_D, acc]
  set E4 := [a, encPts O, .list (ps.map encPerm), encGroup ps, w_D]
  have d5a := Det.mk3 (dG (E4.drop 1))
    (Det.var' (P := P) (env := E4) (i := 4) rfl)
    (Det.arg' (P := P) (vs := [c, .nat j, acc]) (rest := E4.drop 1) (j := 2) rfl)
  refine EvalAll.call_funAll d5a fun v5 ca5 hv5 => ?_
  obtain ⟨rfl, hca5⟩ := hv5
  have hD_le : ⁅camOrbStab (gens gs) (pointwiseStab (gens gs) [x₀, y₁]) x₀ z,
      camOrbStab (gens gs) (pointwiseStab (gens gs) [x₀, y₁]) x₀ z⁆ ≤ gens gs := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    have hxG := camOrbStab_le (gens gs) _ x₀ z hx
    have hyG := camOrbStab_le (gens gs) _ x₀ z hy
    exact (gens gs).mul_mem ((gens gs).mul_mem ((gens gs).mul_mem hxG hyG)
      ((gens gs).inv_mem hxG)) ((gens gs).inv_mem hyG)
  refine (camNclBest_spec hP.nb hP.mg hP.kb hP.po hP.pn gs hD_le hw_D hinv).mono
    fun w cb5 ⟨hw, hcb5⟩ => ?_
  refine ⟨hw.congr (camSocleInnerCands_succ (gens gs) x₀ y₁ i hj), ?_⟩
  clear d5a d4 d3 d2a d1 fP fO dN dH1 dG0 dG dA0
  -- Weights and bounds
  have hw_hs0 := wt_encGroup_le_sq hhs₀l
  have hw_hs1 := wt_encGroup_le_sq hhs₁l
  have hw_acc := hinv.wt_le
  have hw_w := hw.wt_le
  have hw_wP := GensVal.wt_le hw_P
  have hw_wD := GensVal.wt_le hw_D
  have hw_O : (encPts O).wt ≤ 5 * (n + 1) ^ 2 := by
    rw [← natList_map_val_eq_encPts]
    exact wt_natList_le_sq (B := n)
      (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact u.isLt.le)
      (by simpa using hOl)
  have hw_j := wt_nat_le j
  have hw_n := wt_nat_le n
  have hwc := wt_list3_le (encGroup gs) (encGroup hs₀) (encGroup hs₁)
  have hwa := wt_list3_le c (.nat j) acc
  have hwm1 := wt_list2_le (encGroup hs₁) (.nat j)
  have hwm2 := wt_list2_le (encGroup hs₀) (encPts O)
  have hwm3 := wt_list2_le (.nat n) (.list (ps.map encPerm))
  have hwm5 := wt_list3_le (encGroup gs) w_D acc
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p915 : (n + 1) ^ 9 ≤ (n + 1) ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn2 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hb_ps := (pointwiseStabPrim hp).bound_le (v := .list [encGroup hs₀, encPts O])
    (B := camSocleB (encGroup gs) n) ((Val.size_le_wt _).trans (by unfold camSocleB; omega))
  have hb_der := (derivedSubgroupPrim hd).bound_le (v := encGroup ps)
    (B := camSocleB (encGroup gs) n) ((Val.size_le_wt _).trans (by unfold camSocleB; omega))
  have hb_ncl : (normalClosurePrim hncl).boundSize (2 * (encGroup gs).wt + 700 * (n + 1) ^ 6) ≤
      (normalClosurePrim hncl).boundSize (camSocleB (encGroup gs) n) :=
    camDirect_boundSize_mono (normalClosurePrim hncl) (by unfold camSocleB; omega)
  have hb_ord : (groupOrderPrim ho).boundSize (320 * (n + 1) ^ 6) ≤
      (groupOrderPrim ho).boundSize (camSocleB (encGroup gs) n) :=
    camDirect_boundSize_mono (groupOrderPrim ho) (by unfold camSocleB; omega)
  have he_a : (Val.list [c, .nat j, acc]).wt = a.wt := rfl
  have he_c : (Val.list [encGroup gs, encGroup hs₀, encGroup hs₁]).wt = c.wt := rfl
  have he_G : (encPerms (1 :: gs)).wt = (encGroup gs).wt := rfl
  simp only [camSocleInnerStepK, camOrbListK, camNclBestK, mkGroupK] at *
  clear_value a c E1 E2 E3 E4
  generalize (n + 1) ^ 15 = Q15 at *
  generalize (n + 1) ^ 9 = Q9 at *
  generalize (n + 1) ^ 6 = Q6 at *
  generalize (n + 1) ^ 2 = Q2 at *
  omega

def camSocleOuterStepK : ℕ := 3 * 10 ^ 9

/-- One outer step `y₁ = i < n` of the direct socle search. -/
theorem camSocleOuterStep_spec {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    {hd : DerivedSubgroup} {P : Program} {b jo jp jn jd : ℕ}
    (hP : CamSocleAt P b jo jp jn jd ho hp hncl hd)
    (gs hs₀ : List (Perm (Fin n))) (hhs₀l : hs₀.length ≤ n ^ 2) (hn : 0 < n)
    (h0g : gens hs₀ = pointwiseStab (gens gs) [⟨0, hn⟩])
    {i : ℕ} (hi : i < n) {acc : Val}
    (hinv : CamBestInv (camSocleOuterCands (gens gs) ⟨0, hn⟩ i) acc) :
    FunAll P (b + 4) (.list [.list [encGroup gs, encGroup hs₀], .nat i, acc])
      (fun w cost => CamBestInv (camSocleOuterCands (gens gs) ⟨0, hn⟩ (i + 1)) w ∧
        cost ≤ (n + 1) * ((groupOrderPrim ho).boundSize (camSocleB (encGroup gs) n) +
          (pointwiseStabPrim hp).boundSize (camSocleB (encGroup gs) n) +
          (normalClosurePrim hncl).boundSize (camSocleB (encGroup gs) n) +
          (derivedSubgroupPrim hd).boundSize (camSocleB (encGroup gs) n)) +
          camSocleOuterStepK * (n + 1) * ((encGroup gs).wt + (n + 1) ^ 15)) := by
  set x₀ : Fin n := ⟨0, hn⟩
  set y₁ : Fin n := ⟨i, hi⟩
  set c := Val.list [encGroup gs, encGroup hs₀]
  set a := Val.list [c, .nat i, acc]
  have dA0 := fun (rest : List Val) =>
    Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := rest) (j := 0) rfl
  have dG := fun (rest : List Val) =>
    Det.get' (dA0 rest) (Det.nat 0)
      (show [encGroup gs, encGroup hs₀][0]? = some (encGroup gs) from rfl)
  have dG0 := fun (rest : List Val) =>
    Det.get' (dA0 rest) (Det.nat 1)
      (show [encGroup gs, encGroup hs₀][1]? = some (encGroup hs₀) from rfl)
  have dN := fun (rest : List Val) => Det.encPerms_size (gs := 1 :: gs) (dG rest)
  -- 1. pointwiseStab on [encGroup gs, [0, y₁]]
  have d1a : Det P [a] (mk2 (.get (arg 0) (.nat 0)) (mk2 (.nat 0) (arg 1)))
      (.list [encGroup gs, encPts [x₀, y₁]]) _ :=
    Det.mk2 (dG []) (Det.mk2 (Det.nat 0)
      (Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 1) rfl))
  refine FunAll.intro hP.ostep (EvalAll.letE (pointwiseStab_call hp hP.pp d1a ⟨gs, rfl, rfl⟩)
    fun w₁ c₁ h1 => ?_)
  obtain ⟨hw₁, hc₁⟩ := h1
  -- 2. mkGroup on w₁
  obtain ⟨hs₁, rfl, hhs₁l, f1, ⟨hs₁', h1e, h1g⟩, h1w⟩ := mkGroup_gensVal hP.mg hw₁
  obtain rfl := encGroup_injective h1e
  set E1 := [a, .list (hs₁.map encPerm)]
  have d2 := Det.call (Det.mk2 (dN [.list (hs₁.map encPerm)])
    (Det.var' (P := P) (env := E1) (i := 1) rfl)) f1
  refine EvalAll.letE d2 fun v1 cm1 h2 => ?_
  obtain ⟨rfl, hcm1⟩ := h2
  -- 3. call inner iter on [[encGroup gs, encGroup hs₀, encGroup hs₁], .nat n, acc]
  set E2 := [a, .list (hs₁.map encPerm), encGroup hs₁]
  have d3a := Det.mk3
    (Det.mk3 (dG (E2.drop 1)) (dG0 (E2.drop 1)) (Det.var' (P := P) (env := E2) (i := 2) rfl))
    (dN (E2.drop 1))
    (Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := E2.drop 1) (j := 2) rfl)
  refine EvalAll.call_funAll d3a fun v3 ca3 hv3 => ?_
  obtain ⟨rfl, hca3⟩ := hv3
  set S4 := (groupOrderPrim ho).boundSize (camSocleB (encGroup gs) n) +
    (pointwiseStabPrim hp).boundSize (camSocleB (encGroup gs) n) +
    (normalClosurePrim hncl).boundSize (camSocleB (encGroup gs) n) +
    (derivedSubgroupPrim hd).boundSize (camSocleB (encGroup gs) n)
  set IStepB := S4 + camSocleInnerStepK * ((encGroup gs).wt + (n + 1) ^ 15)
  have hinv0 : CamBestInv (camSocleInnerCands (gens gs) x₀ y₁ i 0) acc := by
    rw [camSocleInnerCands_zero]; exact hinv
  refine (iter_spec hP.iiter hinv0 (M := 40 * (n + 1) ^ 6) (B := fun _ => IStepB)
    (fun j acc' _ h => h.wt_le)
    (fun j acc' hj h => camSocleInnerStep_spec hP gs hs₀ hs₁ hhs₀l hhs₁l h0g h1g hj h)).mono
    fun w cb3 ⟨hw, hcb3⟩ => ?_
  refine ⟨hw.congr (camSocleInnerCands_full (gens gs) x₀ hi), ?_⟩
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcb3
  clear d3a d2 d1a f1 dN dG0 dG dA0
  have hw_hs0 := wt_encGroup_le_sq hhs₀l
  have hw_hs1 := wt_encGroup_le_sq hhs₁l
  have hw_acc := hinv.wt_le
  have hw_w := hw.wt_le
  have hw_w1 := GensVal.wt_le hw₁
  have hw_i := wt_nat_le i
  have hw_0 := wt_nat_le 0
  have hw_n := wt_nat_le n
  have w_pts : (encPts [x₀, y₁]).wt ≤ 6 * (n + 2) + 4 := by simpa using wt_encPts_le [x₀, y₁]
  have he_pts0 : (Val.list [Val.nat ↑x₀, Val.nat i]).wt = (encPts [x₀, y₁]).wt := rfl
  have he_pts1 : (Val.list [Val.nat ↑x₀, Val.nat ↑y₁]).wt = (encPts [x₀, y₁]).wt := rfl
  have hwc := wt_list2_le (encGroup gs) (encGroup hs₀)
  have hwa := wt_list3_le c (.nat i) acc
  have hwm1 := wt_list2_le (encGroup gs) (encPts [x₀, y₁])
  have hwm2 := wt_list2_le (.nat n) (.list (hs₁.map encPerm))
  have hwc3 := wt_list3_le (encGroup gs) (encGroup hs₀) (encGroup hs₁)
  have hwa3 := wt_list3_le (.list [encGroup gs, encGroup hs₀, encGroup hs₁]) (.nat n) acc
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p915 : (n + 1) ^ 9 ≤ (n + 1) ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have hb_ps := (pointwiseStabPrim hp).bound_le (v := .list [encGroup gs, encPts [x₀, y₁]])
    (B := camSocleB (encGroup gs) n) ((Val.size_le_wt _).trans (by unfold camSocleB; omega))
  have hps_le_S4 : (pointwiseStabPrim hp).boundSize (camSocleB (encGroup gs) n) ≤ S4 := by
    unfold S4; omega
  have hsum : (Val.list [.list [encGroup gs, encGroup hs₀, encGroup hs₁], .nat n, acc]).wt +
      n + 40 * (n + 1) ^ 6 + 1 ≤ 4 * (encGroup gs).wt + 5000 * (n + 1) ^ 6 := by omega
  have hmul := Nat.mul_le_mul_left (loopModK * (n + 1)) hsum
  have eStep : n * IStepB = n * S4 + n * (camSocleInnerStepK * ((encGroup gs).wt + (n + 1) ^ 15)) := by
    unfold IStepB; ring
  have hStep : n * (camSocleInnerStepK * ((encGroup gs).wt + (n + 1) ^ 15)) ≤
      camSocleInnerStepK * ((n + 1) * (encGroup gs).wt + (n + 1) * (n + 1) ^ 15) := by
    calc n * (camSocleInnerStepK * ((encGroup gs).wt + (n + 1) ^ 15))
        ≤ (n + 1) * (camSocleInnerStepK * ((encGroup gs).wt + (n + 1) ^ 15)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = camSocleInnerStepK * ((n + 1) * (encGroup gs).wt + (n + 1) * (n + 1) ^ 15) := by ring
  have eS4 : (n + 1) * S4 = n * S4 + S4 := by ring
  have he_a : (Val.list [c, .nat i, acc]).wt = a.wt := rfl
  have he_c : (Val.list [encGroup gs, encGroup hs₀]).wt = c.wt := rfl
  have he_G : (encPerms (1 :: gs)).wt = (encGroup gs).wt := rfl
  have hGW : (encGroup gs).wt ≤ (n + 1) * (encGroup gs).wt := Nat.le_mul_of_pos_left _ (by omega)
  have hQ9 : (n + 1) ^ 9 ≤ (n + 1) * (n + 1) ^ 15 :=
    p915.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hQ6 : (n + 1) ^ 6 ≤ (n + 1) * (n + 1) ^ 15 := p69.trans hQ9
  have hNQ6 : (n + 1) * (n + 1) ^ 6 ≤ (n + 1) * (n + 1) ^ 15 :=
    Nat.mul_le_mul_left _ (p69.trans p915)
  rw [eS4]
  rw [eStep] at hcb3
  have hDist1 : loopModK * (n + 1) * (4 * (encGroup gs).wt + 5000 * (n + 1) ^ 6) =
      4 * loopModK * ((n + 1) * (encGroup gs).wt) +
      5000 * loopModK * ((n + 1) * (n + 1) ^ 6) := by ring
  have hDist2 : camSocleOuterStepK * (n + 1) * ((encGroup gs).wt + (n + 1) ^ 15) =
      camSocleOuterStepK * ((n + 1) * (encGroup gs).wt + (n + 1) * (n + 1) ^ 15) := by ring
  rw [hDist1] at hmul
  rw [hDist2]
  simp only [camSocleOuterStepK, camSocleInnerStepK, loopModK, mkGroupK] at *
  clear_value a c E1 E2 S4 IStepB
  generalize (n + 1) * (n + 1) ^ 15 = NQ15 at *
  generalize (n + 1) * (n + 1) ^ 6 = NQ6 at *
  generalize (n + 1) * (encGroup gs).wt = NGW at *
  generalize (n + 1) ^ 15 = Q15 at *
  generalize (n + 1) ^ 9 = Q9 at *
  generalize (n + 1) ^ 6 = Q6 at *
  omega

def camSocleK : ℕ := 5 * 10 ^ 9

/-- Cost bound of the direct socle search on `gv = encGroup gs`. -/
noncomputable def camSocleCost (ho : GroupOrder) (hp : PointwiseStab) (hncl : NormalClosure)
    (hd : DerivedSubgroup) (gv : Val) (n : ℕ) : ℕ :=
  (n + 1) ^ 2 * ((groupOrderPrim ho).boundSize (camSocleB gv n) +
    (pointwiseStabPrim hp).boundSize (camSocleB gv n) +
    (normalClosurePrim hncl).boundSize (camSocleB gv n) +
    (derivedSubgroupPrim hd).boundSize (camSocleB gv n)) +
  camSocleK * (n + 1) ^ 2 * (gv.wt + (n + 1) ^ 15)

/-- **Direct socle search (Proposition 2.3).** On `encGroup gs` where `G = gens gs` is primitive
and has a Maróti structure `e` (`25 ≤ n`, `5 ≤ m`, `1 ≤ k`, `2 * k < m`), returns `w` with
`GensVal n w (camProd e Finset.univ)`. -/
theorem camSocle_spec {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    {hd : DerivedSubgroup} {P : Program} {b jo jp jn jd : ℕ}
    (hP : CamSocleAt P b jo jp jn jd ho hp hncl hd)
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}
    (gs : List (Perm (Fin n))) (hM : MarotiStructure (gens gs) e)
    (hprim : MulAction.IsPreprimitive (gens gs) (Fin n))
    (hn : 25 ≤ n) (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) :
    FunAll P b (encGroup gs)
      (fun w cost => GensVal n w (camProd e Finset.univ) ∧
        cost ≤ camSocleCost ho hp hncl hd (encGroup gs) n) := by
  have hn0 : 0 < n := by omega
  set x₀ : Fin n := ⟨0, hn0⟩
  have hne_cand : ∃ K ∈ camSocleOuterCands (gens gs) x₀ n, 1 < Nat.card K := by
    obtain ⟨y₁, z, _, hgt⟩ := camSocleCand_exists_eq_socle hM hprim hn hm hk1 hk x₀
    exact ⟨camSocleCand (gens gs) x₀ y₁ z, ⟨y₁, z, y₁.isLt, rfl⟩, hgt⟩
  set S4 := (groupOrderPrim ho).boundSize (camSocleB (encGroup gs) n) +
    (pointwiseStabPrim hp).boundSize (camSocleB (encGroup gs) n) +
    (normalClosurePrim hncl).boundSize (camSocleB (encGroup gs) n) +
    (derivedSubgroupPrim hd).boundSize (camSocleB (encGroup gs) n)
  set OStepB := (n + 1) * S4 + camSocleOuterStepK * (n + 1) * ((encGroup gs).wt + (n + 1) ^ 15)
  set LCost := n * OStepB + loopModK * (n + 1) * (4 * (encGroup gs).wt + 5000 * (n + 1) ^ 6)
  refine (camSearchEntry_spec hP.entry hP.mg hP.pp gs hn0 hne_cand
    (LCost := LCost) (fun hs₀ hhs₀l h0g => ?_)).mono
    fun w cost ⟨⟨Best, hBmem, hbw, hBgt, hBmin⟩, hc⟩ => ?_
  · have h0 : CamBestInv (camSocleOuterCands (gens gs) x₀ 0) (.list [.list [], .nat 0]) := by
      rw [camSocleOuterCands_zero]; exact camBestInv_empty
    refine (iter_spec hP.oiter h0 (M := 40 * (n + 1) ^ 6) (B := fun _ => OStepB)
      (fun i acc _ h => h.wt_le)
      (fun i acc hi h => camSocleOuterStep_spec hP gs hs₀ hhs₀l hn0 h0g hi h)).mono
      fun res cl ⟨hinv, hcl'⟩ => ⟨hinv, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcl'
    have hw_hs0 := wt_encGroup_le_sq hhs₀l
    have w1 := wt_list2_le (encGroup gs) (encGroup hs₀)
    have w2 := wt_list2_le (.list []) (.nat 0)
    have w3 := wt_list3_le (.list [encGroup gs, encGroup hs₀]) (.nat n) (.list [.list [], .nat 0])
    have wn := wt_nat_le n
    have wn0 := wt_nat_le 0
    have wnil := wt_list_nil
    have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have hsum : (Val.list [.list [encGroup gs, encGroup hs₀], .nat n,
        .list [.list [], .nat 0]]).wt + n + 40 * (n + 1) ^ 6 + 1 ≤
        4 * (encGroup gs).wt + 5000 * (n + 1) ^ 6 := by omega
    have hmul := Nat.mul_le_mul_left (loopModK * (n + 1)) hsum
    omega
  · obtain ⟨y₁, z, -, rfl⟩ := hBmem
    have hBeq := camSocleCand_min_eq_socle hM hprim hn hm hk1 hk x₀ y₁ z hBgt
      fun y₁' z' hgt' => hBmin _ ⟨y₁', z', y₁'.isLt, rfl⟩ hgt'
    refine ⟨hBeq ▸ hbw, ?_⟩
    have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have hb_ps : (pointwiseStabPrim hp).boundSize (2 * (encGroup gs).wt + 30 * (n + 1)) ≤
        (pointwiseStabPrim hp).boundSize (camSocleB (encGroup gs) n) :=
      camDirect_boundSize_mono (pointwiseStabPrim hp) (by unfold camSocleB; omega)
    have hps_le_S4 : (pointwiseStabPrim hp).boundSize (camSocleB (encGroup gs) n) ≤ S4 := by
      unfold S4; omega
    have eOStep : n * OStepB =
        n * ((n + 1) * S4) +
        n * (camSocleOuterStepK * (n + 1) * ((encGroup gs).wt + (n + 1) ^ 15)) := by
      unfold OStepB; ring
    have hOStep : n * (camSocleOuterStepK * (n + 1) * ((encGroup gs).wt + (n + 1) ^ 15)) ≤
        camSocleOuterStepK * ((n + 1) ^ 2 * (encGroup gs).wt + (n + 1) ^ 2 * (n + 1) ^ 15) := by
      calc n * (camSocleOuterStepK * (n + 1) * ((encGroup gs).wt + (n + 1) ^ 15))
          ≤ (n + 1) * (camSocleOuterStepK * (n + 1) * ((encGroup gs).wt + (n + 1) ^ 15)) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = camSocleOuterStepK * ((n + 1) ^ 2 * (encGroup gs).wt + (n + 1) ^ 2 * (n + 1) ^ 15) := by
            ring
    have hS4_sq : n * ((n + 1) * S4) + S4 ≤ (n + 1) ^ 2 * S4 := by
      have : (n + 1) ^ 2 * S4 = n * ((n + 1) * S4) + n * S4 + S4 := by ring
      omega
    have hLoop : loopModK * (n + 1) * (4 * (encGroup gs).wt + 5000 * (n + 1) ^ 6) ≤
        4 * loopModK * ((n + 1) ^ 2 * (encGroup gs).wt) +
        5000 * loopModK * ((n + 1) ^ 2 * (n + 1) ^ 15) := by
      have h1 : (n + 1) * (encGroup gs).wt ≤ (n + 1) ^ 2 * (encGroup gs).wt := by
        rw [sq]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))
      have h2 : (n + 1) * (n + 1) ^ 6 ≤ (n + 1) ^ 2 * (n + 1) ^ 15 := by
        refine Nat.mul_le_mul (by rw [sq]; exact Nat.le_mul_of_pos_left _ (by omega)) ?_
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have e : loopModK * (n + 1) * (4 * (encGroup gs).wt + 5000 * (n + 1) ^ 6) =
          4 * loopModK * ((n + 1) * (encGroup gs).wt) +
          5000 * loopModK * ((n + 1) * (n + 1) ^ 6) := by ring
      rw [e]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    have hGW2 : (encGroup gs).wt ≤ (n + 1) ^ 2 * (encGroup gs).wt :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have hQ9_2 : (n + 1) ^ 9 ≤ (n + 1) ^ 2 * (n + 1) ^ 15 :=
      (Nat.pow_le_pow_right (by omega) (by omega : 9 ≤ 15)).trans
        (Nat.le_mul_of_pos_left _ (by positivity))
    have hDist : camSocleK * (n + 1) ^ 2 * ((encGroup gs).wt + (n + 1) ^ 15) =
        camSocleK * ((n + 1) ^ 2 * (encGroup gs).wt + (n + 1) ^ 2 * (n + 1) ^ 15) := by ring
    unfold camSocleCost
    change cost ≤ (n + 1) ^ 2 * S4 + camSocleK * (n + 1) ^ 2 * ((encGroup gs).wt + (n + 1) ^ 15)
    rw [hDist]
    unfold LCost at hc
    rw [eOStep] at hc
    simp only [camSocleK, camSocleOuterStepK, camSearchEntryK, loopModK] at *
    clear_value S4 OStepB LCost
    generalize (n + 1) ^ 2 * (n + 1) ^ 15 = N2Q15 at *
    generalize (n + 1) ^ 2 * (encGroup gs).wt = N2GW at *
    generalize (n + 1) ^ 9 = Q9 at *
    generalize (n + 1) ^ 6 = Q6 at *
    omega

/-! ### 4. Synthetic `Prim` wrapper for `camFactorCost` and `camSocleCost` -/

/-- Combined degree of `camDirectPrim`. -/
noncomputable def camDirectD (ho : GroupOrder) (hp : PointwiseStab)
    (hncl : NormalClosure) (hd : DerivedSubgroup) : ℕ :=
  (groupOrderPrim ho).k + (pointwiseStabPrim hp).k +
    (normalClosurePrim hncl).k + (derivedSubgroupPrim hd).k + 4

/-- Combined constant of `camDirectPrim`. -/
noncomputable def camDirectC (ho : GroupOrder) (hp : PointwiseStab)
    (hncl : NormalClosure) (hd : DerivedSubgroup) : ℕ :=
  (groupOrderPrim ho).c + (pointwiseStabPrim hp).c +
    (normalClosurePrim hncl).c + (derivedSubgroupPrim hd).c +
    camFactorK + camSocleK

/-- Synthetic `Prim` whose `.boundSize` upper-bounds both `camFactorCost` and `camSocleCost`. -/
noncomputable def camDirectPrim (ho : GroupOrder) (hp : PointwiseStab)
    (hncl : NormalClosure) (hd : DerivedSubgroup) : Prim where
  Pre := fun _ => False
  Post := fun _ _ => False
  c := camDirectC ho hp hncl hd
  k := camDirectD ho hp hncl hd
  prog := ⟨[]⟩
  spec := fun x => False.elim x.2

private theorem mul_boundSize_le (p : Prim) (D : ℕ) {M B : ℕ} (hM : M ≤ B + 2) (hk : p.k + 1 ≤ D) :
    M * p.boundSize B ≤ p.c * (B + 2) ^ D := by
  unfold Prim.boundSize
  calc M * (p.c * (B + 2) ^ p.k)
      ≤ (B + 2) * (p.c * (B + 2) ^ p.k) := Nat.mul_le_mul_right _ hM
    _ = p.c * (B + 2) ^ (p.k + 1) := by rw [pow_succ]; ring
    _ ≤ p.c * (B + 2) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk)

theorem camFactorCost_le_boundSize (ho : GroupOrder) (hp : PointwiseStab)
    (hncl : NormalClosure) (hd : DerivedSubgroup) (n : ℕ) :
    camFactorCost ho hp hncl n ≤ (camDirectPrim ho hp hncl hd).boundSize (camLoopB n) := by
  set B := camLoopB n
  set D := camDirectD ho hp hncl hd
  have hn6 : (n + 1) ^ 6 ≤ B := by unfold B camLoopB; omega
  have hnB : n + 1 ≤ B + 2 := by
    have : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    omega
  have h1 := mul_boundSize_le (groupOrderPrim ho) D hnB (by unfold D camDirectD; omega)
  have h2 := mul_boundSize_le (pointwiseStabPrim hp) D hnB (by unfold D camDirectD; omega)
  have h3 := mul_boundSize_le (normalClosurePrim hncl) D hnB (by unfold D camDirectD; omega)
  have h16 : (n + 1) ^ 16 ≤ (B + 2) ^ D := by
    calc (n + 1) ^ 16 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = ((n + 1) ^ 6) ^ 3 := by ring
      _ ≤ (B + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ ≤ (B + 2) ^ D := Nat.pow_le_pow_right (by omega) (by unfold D camDirectD; omega)
  have h4 := Nat.mul_le_mul_left camFactorK h16
  change camFactorCost ho hp hncl n ≤ camDirectC ho hp hncl hd * (B + 2) ^ D
  unfold camFactorCost camDirectC
  change (n + 1) * ((groupOrderPrim ho).boundSize B + (pointwiseStabPrim hp).boundSize B +
    (normalClosurePrim hncl).boundSize B) + camFactorK * (n + 1) ^ 16 ≤ _
  rw [Nat.mul_add, Nat.mul_add]
  have eR : ((groupOrderPrim ho).c + (pointwiseStabPrim hp).c + (normalClosurePrim hncl).c +
      (derivedSubgroupPrim hd).c + camFactorK + camSocleK) * (B + 2) ^ D =
    (groupOrderPrim ho).c * (B + 2) ^ D + (pointwiseStabPrim hp).c * (B + 2) ^ D +
    (normalClosurePrim hncl).c * (B + 2) ^ D + (derivedSubgroupPrim hd).c * (B + 2) ^ D +
    camFactorK * (B + 2) ^ D + camSocleK * (B + 2) ^ D := by ring
  rw [eR]
  omega

theorem camSocleCost_le_boundSize (ho : GroupOrder) (hp : PointwiseStab)
    (hncl : NormalClosure) (hd : DerivedSubgroup) (v : Val) (n B : ℕ)
    (h1 : (n + 1) ^ 6 ≤ B) (h2 : camSocleB v n ≤ B) :
    camSocleCost ho hp hncl hd v n ≤ (camDirectPrim ho hp hncl hd).boundSize B := by
  set D := camDirectD ho hp hncl hd
  have hn2 : (n + 1) ^ 2 ≤ B + 2 := by
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have b1 := Nat.mul_le_mul_left ((n + 1) ^ 2) (camDirect_boundSize_mono (groupOrderPrim ho) h2)
  have b2 := Nat.mul_le_mul_left ((n + 1) ^ 2) (camDirect_boundSize_mono (pointwiseStabPrim hp) h2)
  have b3 := Nat.mul_le_mul_left ((n + 1) ^ 2) (camDirect_boundSize_mono (normalClosurePrim hncl) h2)
  have b4 := Nat.mul_le_mul_left ((n + 1) ^ 2) (camDirect_boundSize_mono (derivedSubgroupPrim hd) h2)
  have m1 := b1.trans (mul_boundSize_le (groupOrderPrim ho) D hn2 (by unfold D camDirectD; omega))
  have m2 := b2.trans (mul_boundSize_le (pointwiseStabPrim hp) D hn2 (by unfold D camDirectD; omega))
  have m3 := b3.trans (mul_boundSize_le (normalClosurePrim hncl) D hn2 (by unfold D camDirectD; omega))
  have m4 := b4.trans (mul_boundSize_le (derivedSubgroupPrim hd) D hn2 (by unfold D camDirectD; omega))
  have hwt : v.wt ≤ B := by unfold camSocleB at h2; omega
  have hn15 : (n + 1) ^ 15 ≤ (B + 1) ^ 3 := by
    calc (n + 1) ^ 15 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = ((n + 1) ^ 6) ^ 3 := by ring
      _ ≤ (B + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hrem : (n + 1) ^ 2 * (v.wt + (n + 1) ^ 15) ≤ (B + 2) ^ D := by
    have hsum : v.wt + (n + 1) ^ 15 ≤ (B + 2) ^ 3 := by
      have : B + (B + 1) ^ 3 ≤ (B + 2) ^ 3 := by nlinarith
      omega
    calc (n + 1) ^ 2 * (v.wt + (n + 1) ^ 15)
        ≤ (B + 2) * (B + 2) ^ 3 := Nat.mul_le_mul hn2 hsum
      _ = (B + 2) ^ 4 := by ring
      _ ≤ (B + 2) ^ D := Nat.pow_le_pow_right (by omega) (by unfold D camDirectD; omega)
  have m5 : camSocleK * (n + 1) ^ 2 * (v.wt + (n + 1) ^ 15) ≤ camSocleK * (B + 2) ^ D := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left camSocleK hrem
  change camSocleCost ho hp hncl hd v n ≤ camDirectC ho hp hncl hd * (B + 2) ^ D
  unfold camSocleCost camDirectC
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

end GI.Impl
