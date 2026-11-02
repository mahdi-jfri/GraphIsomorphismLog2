import Workspace.Impl.CamPCol
import Workspace.Impl.CamPLoopMath
import Workspace.Impl.CamCombine

/-!
# Steps 7–8 of `camProg`: the coordinate of one factor, from the factor alone

`camFacBody` works on `[[N, ⟨⟩, m, k], T]`, where `T = camProd e {i}` is one simple factor of the
socle `N = camProd e univ`. It restricts `T` to the orbit `O` of the point `0` (`camRestr_spec`),
then computes the column of the factor (`camCol_spec`). The preconditions of `camCol_spec` hold:
- `T ≤ N`, and `N` normalizes `T` (`camX_prod_mono`, `camX_prod_normal`);
- the Johnson promise for `T` on `O`, by `cam_johnson_promise`, since the orbit of `0` under
  `T` is the set of points that agree with `0` outside coordinate `i` (`camX_orbit_factor`);
- every orbit of `C_N(T) = camProd e (univ.erase i)` meets `O` (`cam_cent_erase`,
  `camX_orbit_others`).
The output `CamFacOut` is what `cam_combine` needs about the factor.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp len len_le_self)

variable {n m k r : ℕ}

theorem length_camRestrFuns (b : ℕ) : (camRestrFuns b).length = 63 := by
  simp [camRestrFuns, length_orbitFuns, rangeFuns, filterFuns, mapFuns, loopFuns, camResFuns,
    gatherFuns, camIdxFuns, findEqFuns, findFuns, mkGroupFuns, appendFuns]

/-- On `[ctx, T]`: restrict `T` to an orbit, then compute its column. -/
def camFacBody (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 .nil (arg 1))) (.call (b + 64) (mk2 (arg 0) (.var 1)))

/-- The coordinate of one factor, at base `b` (116 functions). -/
def camFacFuns (b jj jq : ℕ) : List Expr :=
  [camFacBody b] ++ camRestrFuns (b + 1) ++ camColFuns (b + 64) jj jq

structure CamFacAt (P : Program) (b jj jq : ℕ) (hj : JohnsonIdentification)
    (hqc : QuotientCentralizer) : Prop where
  body : P.funs[b]? = some (camFacBody b)
  restr : CamRestrAt P (b + 1)
  col : CamColAt P (b + 64) jj jq hj hqc

theorem camFacAt_of {P : Program} {b jj jq : ℕ} {hj : JohnsonIdentification}
    {hqc : QuotientCentralizer} (h : P.HasAt b (camFacFuns b jj jq))
    (pj : P.prims[jj]? = some (johnsonPrim hj))
    (pq : P.prims[jq]? = some (quotientCentralizerPrim hqc)) : CamFacAt P b jj jq hj hqc := by
  simp only [camFacFuns] at h
  exact ⟨h.left.left.single, camRestrAt_of h.left.right,
    camColAt_of (by simpa [length_camRestrFuns, Nat.add_assoc] using h.right) pj pq⟩

/-- **What the coordinate of factor `i` gives**, with base point `x₀`. -/
def CamFacOut (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (i : Fin r) (x₀ : Fin n)
    (v : Val) : Prop :=
  ∃ (O : List (Fin n)) (ts' : List (Perm (Fin O.length)))
    (ι : Fin O.length ≃ {A : Finset (Fin m) // A.card = k}),
    Function.Injective O.get ∧ (∀ y, (∃ w, O.get w = y) ↔ ∀ j, j ≠ i → e y j = e x₀ j) ∧
    (∀ g, g ∈ gens ts' ↔ ∃ t ∈ camProd e {i}, ∀ w, O.get (g w) = t (O.get w)) ∧
    IsJohnsonId (gens ts') ι ∧
    ∃ F : Fin n → {A : Finset (Fin m) // A.card = k},
      (∀ x w, e (O.get w) i = e x i → F x = ι w) ∧
      v = camColV fun x => kVal (F x)

/-- The bound on the arguments of the cited calls. -/
def camFacB (Z : ℕ) : ℕ := 8110 * Z ^ 2

def camFacK : ℕ := 10 ^ 20 * 811 ^ 15

theorem cam_boundSize_mono (p : Prim) {B B' : ℕ} (h : B ≤ B') : p.boundSize B ≤ p.boundSize B' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- **The coordinate of one factor.** -/
theorem camFac_spec {hj : JohnsonIdentification} {hqc : QuotientCentralizer} {P : Program}
    {b jj jq : ℕ} (hP : CamFacAt P b jj jq hj hqc)
    (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (hn : 0 < n)
    (h5 : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) (hb : (k + 1) ^ 2 < m + 2) (hmn : m ≤ n)
    (ns ts : List (Perm (Fin n))) (hns : gens ns = camProd e Finset.univ) (i : Fin r)
    (hts : gens ts = camProd e {i}) :
    FunAll P b (.list [.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m, .nat k],
        encGroup ts])
      (fun v cost => CamFacOut e i ⟨0, hn⟩ v ∧
        cost ≤ (johnsonPrim hj).boundSize (camFacB ((Val.list [.list [encGroup ns,
            encGroup ([] : List (Perm (Fin n))), .nat m, .nat k], encGroup ts]).wt + 1)) +
          (quotientCentralizerPrim hqc).boundSize (camFacB ((Val.list [.list [encGroup ns,
            encGroup ([] : List (Perm (Fin n))), .nat m, .nat k], encGroup ts]).wt + 1)) +
          camFacK * ((Val.list [.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m,
            .nat k], encGroup ts]).wt + 1) ^ 30) := by
  set x₀ : Fin n := ⟨0, hn⟩ with hx₀
  set cx := Val.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m, .nat k] with hcx
  set a := Val.list [cx, encGroup ts] with ha
  obtain ⟨O, hO, ts', hOm, hts'm, hts'l, fR⟩ := camRestr_spec hP.restr (.list []) ts hn
  have hinj : Function.Injective O.get := hO.injective_get
  have hν : ∀ y, (∃ w, O.get w = y) ↔ ∀ j, j ≠ i → e y j = e x₀ j := by
    intro y
    rw [← List.mem_iff_get, hOm y, hts]
    exact camX_orbit_factor (by omega) (by omega) i x₀ y
  have hH : ∀ g, g ∈ gens ts' ↔ ∃ t ∈ camProd e {i}, ∀ w, O.get (g w) = t (O.get w) := by
    intro g; rw [hts'm g, hts]; rfl
  obtain ⟨ι₀, -, hJ₀⟩ := cam_johnson_promise e i x₀ O.get hinj hν hH
  have hTN : gens ts ≤ gens ns := by
    rw [hts, hns]; exact camX_prod_mono (Finset.subset_univ _)
  have hnorm : ∀ y ∈ gens ns, ∀ x ∈ gens ts, y * x * y⁻¹ ∈ gens ts := by
    rw [hts, hns]; exact camX_prod_normal _ _
  have hCe : ∀ C, CamCent (gens ns) (gens ts) C → C = camProd e (Finset.univ.erase i) := by
    intro C hC
    refine cam_cent_erase e h5 hk1 (by omega) (Finset.mem_univ i) fun y => ?_
    rw [hC y, hns, hts]
  have horb : ∀ C, CamCent (gens ns) (gens ts) C → ∀ x y, y ∈ MulAction.orbit C x ↔
      e y i = e x i := by
    intro C hC x y
    rw [hCe C hC, show Finset.univ.erase i = {i}ᶜ by ext; simp]
    exact camX_orbit_others (by omega) (by omega) i x y
  have hcov : ∀ C, CamCent (gens ns) (gens ts) C → ∀ x, ∃ u ∈ O, u ∈ MulAction.orbit C x := by
    intro C hC x
    refine ⟨e.symm (Function.update (e x₀) i (e x i)), ?_, ?_⟩
    · rw [List.mem_iff_get]
      exact (hν _).mpr fun j hj => by simp [Function.update_of_ne hj]
    · rw [horb C hC]; simp
  have hcol := camCol_spec hP.col ns ts O hO ts' hTN hnorm h5 hk1 hb hmn ⟨ι₀, hJ₀⟩ hcov
  have dA1 := Det.arg' (P := P) (vs := [cx, encGroup ts]) (rest := []) (j := 1) rfl
  have dR := Det.call (Det.mk2 (Det.nil (P := P) (env := [a])) dA1) fR
  refine FunAll.intro hP.body (EvalAll.letE dR fun vA cA hA => ?_)
  obtain ⟨rfl, hcA⟩ := hA
  refine EvalAll.call_funAll (Det.mk2 (Det.arg' (P := P) (vs := [cx, encGroup ts])
    (rest := [.list [natList (O.map Fin.val), encGroup ts', encGroup ts]]) (j := 0) rfl)
    (Det.var' (P := P) (env := [a, .list [natList (O.map Fin.val), encGroup ts', encGroup ts]])
      (i := 1) rfl)) fun vB cB hB => ?_
  obtain ⟨rfl, hcB⟩ := hB
  have hCC : CamCent (gens ns) (gens ts) (camProd e (Finset.univ.erase i)) := fun y => by
    rw [hns, hts]
    exact (Set.ext_iff.mp (camX_centralizer h5 hk1 (by omega) (Finset.mem_univ i)) y).symm
  refine hcol.mono fun v cost hv => ?_
  obtain ⟨ι, hι, w, hwC, rfl, hcost⟩ := hv
  refine ⟨⟨O, ts', ι, hinj, hν, hH, hι, fun x => ι (w x), fun x w' hw' => ?_, rfl⟩, ?_⟩
  · -- the point of `O` with the label of `x` is the one with coordinate `i` of `x`
    have h1 := (horb _ hCC x _).mp (hwC _ hCC x)
    have h2 : e (O.get (w x)) = e (O.get w') := by
      funext j
      by_cases hj : j = i
      · subst hj; rw [h1, hw']
      · rw [(hν _).mp ⟨w x, rfl⟩ j hj, (hν _).mp ⟨w', rfl⟩ j hj]
    show ι (w x) = ι w'
    rw [hinj (e.injective h2)]
  · clear hcol fR dR dA1
    set A := Val.list [natList (O.map Fin.val), encGroup ts', encGroup ts] with hA
    set Z := a.wt + 1 with hZ
    have haw : (Val.list [cx, encGroup ts]).wt = a.wt := rfl
    have hTw : (encGroup ts).wt < a.wt := wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have hcxw : cx.wt < a.wt := wt_le_wt_list (List.mem_cons_self ..)
    have hS := S_le_wt_encGroup ts
    have hOl : O.length ≤ n := by simpa using hO.length_le_card
    have hnZ : n + 1 ≤ Z := by
      have : n + 1 ≤ (ts.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
    have hn2 : (n + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left hnZ 2
    have hOv : (natList (O.map Fin.val)).wt ≤ 5 * Z ^ 2 :=
      (wt_natList_le_sq (B := n) (fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega) (by simpa using hOl)).trans (by omega)
    have hT' : (encGroup ts').wt ≤ 160 * Z ^ 2 := by
      have h1 := wt_encGroup_le ts'
      have h2 : (ts'.length + 2) * (O.length + 1) ≤ 2 * Z := by
        rw [hts'l]
        have : (ts.length + 1 + 2) * (O.length + 1) ≤ (2 * (ts.length + 2)) * (n + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have e : (2 * (ts.length + 2)) * (n + 1) = 2 * ((ts.length + 2) * (n + 1)) := by ring
        omega
      have h3 := Nat.pow_le_pow_left h2 2
      have e : (2 * Z) ^ 2 = 4 * Z ^ 2 := by ring
      omega
    have hAw := wt_list3_le (natList (O.map Fin.val)) (encGroup ts') (encGroup ts)
    have hAe : (Val.list [natList (O.map Fin.val), encGroup ts', encGroup ts]).wt = A.wt := rfl
    have hA' : A.wt ≤ 350 * Z ^ 2 := by omega
    have hW := wt_list2_le cx A
    have hW' : (Val.list [cx, A]).wt + 1 ≤ 811 * Z ^ 2 := by omega
    have hB1 := cam_boundSize_mono (johnsonPrim hj) (show 10 * ((Val.list [cx, A]).wt + 1) ≤
      camFacB Z by unfold camFacB; omega)
    have hB2 := cam_boundSize_mono (quotientCentralizerPrim hqc) (show 10 * ((Val.list [cx, A]).wt + 1) ≤
      camFacB Z by unfold camFacB; omega)
    have hC15 : ((Val.list [cx, A]).wt + 1) ^ 15 ≤ 811 ^ 15 * Z ^ 30 := by
      calc ((Val.list [cx, A]).wt + 1) ^ 15 ≤ (811 * Z ^ 2) ^ 15 := Nat.pow_le_pow_left hW' 15
        _ = 811 ^ 15 * Z ^ 30 := by ring
    have hR0 := wt_list2_le (.list []) (encGroup ts)
    have hnil : (Val.list []).wt ≤ 10 := by decide
    have hR7 : ((Val.list [.list [], encGroup ts]).wt + 1) ^ 7 ≤ 23 ^ 7 * Z ^ 30 := by
      have hZ2' : 2 ≤ Z := by omega
      calc ((Val.list [.list [], encGroup ts]).wt + 1) ^ 7 ≤ (23 * Z) ^ 7 :=
            Nat.pow_le_pow_left (by omega) 7
        _ = 23 ^ 7 * Z ^ 7 := by ring
        _ ≤ 23 ^ 7 * Z ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hv : (camColV fun x => kVal (ι (w x))).wt ≤ 12 * Z ^ 3 := by
      have h1 := cam_wt_list_le_of (vs := (List.finRange n).map fun x => kVal (ι (w x)))
        (B := 5 * (m + 1) ^ 2)
        (fun v hv => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv; exact wt_kVal_le _)
      simp only [List.length_map, List.length_finRange] at h1
      have h2 : n * (2 * (5 * (m + 1) ^ 2) + 1) ≤ Z * (11 * Z ^ 2) := by
        refine Nat.mul_le_mul (by omega) ?_
        have := Nat.pow_le_pow_left (show m + 1 ≤ n + 1 by omega) 2
        omega
      have e : Z * (11 * Z ^ 2) = 11 * Z ^ 3 := by ring
      have : 2 ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left (by omega) 3
      exact h1.trans (by omega)
    have hve : (Val.list ((List.finRange n).map fun x => kVal (ι (w x)))).wt =
      (camColV fun x => kVal (ι (w x))).wt := rfl
    have h23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h330 : Z ^ 3 ≤ Z ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
    have hcx' : (Val.list [cx, A]).wt = (Val.list [Val.list [encGroup ns,
      encGroup ([] : List (Perm (Fin n))), .nat m, .nat k], Val.list [natList (O.map Fin.val),
        encGroup ts', encGroup ts]]).wt := rfl
    rw [← hcx'] at hcost
    simp only [camFacK, camColK, camRestrK] at *
    clear_value A Z a cx
    generalize Z ^ 30 = Q30 at *
    generalize Z ^ 3 = Q3 at *
    generalize Z ^ 2 = Q2 at *
    omega

end GI.Impl
