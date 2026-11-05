module

public import Workspace.Impl.CamPResPerm
public import Workspace.Lang.Lib.Orbit
public import Workspace.Lang.Lib.Search
public import Workspace.Lang.Prims.Ops

@[expose] public section

/-!
# Step 7 of `camProg`: one factor on one of its orbits

`camRestrBody` works on `[c, encGroup ts]` for a group `T = ⟨ts⟩`. It computes
1. the orbit labels of `T` (`orbitFuns`);
2. the orbit `O` of the point `0`, as the sorted list of the points whose label is that of `0`
   (`filter` over `range n`);
3. the restriction of every generator to `O` (`map` of `camRes`), and the group value of the
   restricted generators (`mkGroup`).
It returns `[natList O, encGroup ts', encGroup ts]` (`camRestr_spec`). The restricted group
`⟨ts'⟩` is the restriction of `T` to `O` (`cam_restrict_gens`): this is the group that the
Johnson identification is applied to.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp len len_le_self)

variable {n : ℕ}

/-! ### Groups and orbits -/

theorem cam_gens_cons_one (ts : List (Perm (Fin n))) : gens (1 :: ts) = gens ts := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.mpr fun g hg => ?_
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (gens ts).one_mem
    · exact Subgroup.subset_closure hg
  · refine Subgroup.closure_le _ |>.mpr fun g hg => Subgroup.subset_closure (List.mem_cons_of_mem _ hg)

theorem cam_orbit_mem {G : Subgroup (Perm (Fin n))} {t : Perm (Fin n)} (ht : t ∈ G) {x u : Fin n}
    (hu : u ∈ MulAction.orbit G x) : t u ∈ MulAction.orbit G x := by
  obtain ⟨g, rfl⟩ := hu
  exact ⟨⟨t, ht⟩ * g, by simp [mul_smul]⟩

/-! ### The orbit of `0` as a filtered list -/

/-- The label of a number, `0` outside `Fin n`. -/
def camLabN (lab : Fin n → ℕ) (y : ℕ) : ℕ := if h : y < n then lab ⟨y, h⟩ else 0

/-- The test of the filter: the label of `y` is that of `0`. -/
def camLabQ (lab : Fin n → ℕ) : Val → Bool
  | .nat y => decide (camLabN lab y = camLabN lab 0)
  | .list _ => false

theorem cam_filter_range (lab : Fin n → ℕ) (hn : 0 < n) :
    ((List.range n).map Val.nat).filter (camLabQ lab) =
      (((List.finRange n).filter fun y => decide (lab y = lab ⟨0, hn⟩)).map Fin.val).map Val.nat := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.filter_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro y _
  simp [camLabQ, camLabN, Function.comp_def, hn]

/-- The test function: on `[encFun lab, y]`, whether `lab y = lab 0`. -/
def camLabTest : Expr := .arith .eq (.get (arg 0) (arg 1)) (.get (arg 0) (.nat 0))

theorem camLabTest_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some camLabTest)
    (lab : Fin n → ℕ) (hlab : ∀ x, lab x ≤ n) (hn : 0 < n) (y : Fin n) :
    FunDet P f (.list [encFun lab, .nat y]) (boolVal (camLabQ lab (.nat y)))
      (100 * (n + 1) ^ 2 + 100) := by
  have dL := Det.arg' (P := P) (vs := [encFun lab, .nat y]) (rest := []) (j := 0) rfl
  have dY := Det.arg' (P := P) (vs := [encFun lab, .nat y]) (rest := []) (j := 1) rfl
  have d1 := Det.get' dL dY (encFun_getElem? lab y)
  have d0 := Det.get' dL (Det.nat 0) (encFun_getElem? lab ⟨0, hn⟩)
  have dE := Det.arith (op := .eq) d1 d0
  have hv : Val.nat (BinOp.eval .eq (lab y) (lab ⟨0, hn⟩)) = boolVal (camLabQ lab (.nat y)) := by
    simp only [BinOp.eval, camLabQ, camLabN, y.isLt, hn, dif_pos]
    by_cases h : lab y = lab ⟨0, hn⟩ <;> simp [h]
  rw [hv] at dE
  refine FunDet.intro hf (dE.mono ?_)
  have h1 := wt_encFun_le_sq lab hlab
  have h2 := wt_list2_le (encFun lab) (.nat y)
  have h3 := wt_nat_le y
  have h4 := wt_nat_le (lab y)
  have h5 := wt_nat_le (lab ⟨0, hn⟩)
  have h6 := wt_boolVal_le (camLabQ lab (.nat y))
  have h7 := hlab y
  have h8 := hlab ⟨0, hn⟩
  have h9 := y.isLt
  have h10 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-! ### The program -/

/-- The body, at base `b`, on `[c, encGroup ts]`. Environment `[a, labels, range n, O,
restricted generators, restricted group]`. -/
def camRestrBody (b : ℕ) : Expr :=
  .letE (.call (b + 2) (arg 1))
  (.letE (.call (b + 34) (.get (arg 1) (.nat 0)))
  (.letE (.call (b + 37) (mk2 (.var 1) (.var 2)))
  (.letE (.call (b + 40) (mk2 (.var 3) (.get (arg 1) (.nat 1))))
  (.letE (.call (b + 56) (mk2 (.length (.var 3)) (.var 4)))
    (mk3 (.var 3) (.var 5) (arg 1))))))

/-- The restriction to an orbit, at base `b` (63 functions). -/
def camRestrFuns (b : ℕ) : List Expr :=
  [camRestrBody b, camLabTest] ++ orbitFuns (b + 2) ++ rangeFuns (b + 34) ++
    filterFuns (b + 37) (b + 1) ++ mapFuns (b + 40) (b + 43) ++ camResFuns (b + 43) ++
    mkGroupFuns (b + 56)

/-- Where the parts of the restriction sit. -/
structure CamRestrAt (P : Program) (b : ℕ) : Prop where
  body : P.funs[b]? = some (camRestrBody b)
  test : P.funs[b + 1]? = some camLabTest
  orb : P.HasAt (b + 2) (orbitFuns (b + 2))
  rng : P.HasAt (b + 34) (rangeFuns (b + 34))
  flt : P.HasAt (b + 37) (filterFuns (b + 37) (b + 1))
  mp : P.HasAt (b + 40) (mapFuns (b + 40) (b + 43))
  res : P.HasAt (b + 43) (camResFuns (b + 43))
  mg : P.HasAt (b + 56) (mkGroupFuns (b + 56))

theorem camRestrAt_of {P : Program} {b : ℕ} (h : P.HasAt b (camRestrFuns b)) :
    CamRestrAt P b := by
  simp only [camRestrFuns] at h
  have h2 := h.left.left.left.left.left.left
  exact
  { body := by simpa using h2 0 (by simp)
    test := by simpa using h2 1 (by simp)
    orb := by simpa using h.left.left.left.left.left.right
    rng := by simpa [length_orbitFuns, Nat.add_assoc] using h.left.left.left.left.right
    flt := by
      simpa [length_orbitFuns, rangeFuns, loopFuns, Nat.add_assoc] using h.left.left.left.right
    mp := by
      simpa [length_orbitFuns, rangeFuns, filterFuns, loopFuns, Nat.add_assoc] using
        h.left.left.right
    res := by
      simpa [length_orbitFuns, rangeFuns, filterFuns, mapFuns, loopFuns, Nat.add_assoc] using
        h.left.right
    mg := by
      simpa [length_orbitFuns, rangeFuns, filterFuns, mapFuns, loopFuns, camResFuns, gatherFuns,
        camIdxFuns, findEqFuns, findFuns, Nat.add_assoc] using h.right }

def camRestrK : ℕ := 10 ^ 15

/-- **One factor on one orbit.** -/
theorem camRestr_spec {P : Program} {b : ℕ} (hP : CamRestrAt P b) (c : Val)
    (ts : List (Perm (Fin n))) (hn : 0 < n) :
    ∃ (O : List (Fin n)) (hO : O.Nodup) (ts' : List (Perm (Fin O.length))),
      (∀ y, y ∈ O ↔ y ∈ MulAction.orbit (gens ts) (⟨0, hn⟩ : Fin n)) ∧
      (∀ g, g ∈ gens ts' ↔ ∃ t ∈ gens ts, CamRestricts O.get g t) ∧
      ts'.length = ts.length + 1 ∧
      FunDet P b (.list [c, encGroup ts])
        (.list [natList (O.map Fin.val), encGroup ts', encGroup ts])
        (camRestrK * ((Val.list [c, encGroup ts]).wt + 1) ^ 7) := by
  obtain ⟨lab, hlabd, hlab1, hlab2⟩ := orbits_spec hP.orb (1 :: ts)
  set O := (List.finRange n).filter fun y => decide (lab y = lab ⟨0, hn⟩) with hOd
  have hO : O.Nodup := (List.nodup_finRange n).filter _
  have hmem : ∀ y, y ∈ O ↔ y ∈ MulAction.orbit (gens ts) (⟨0, hn⟩ : Fin n) := by
    intro y
    rw [hOd, List.mem_filter, ← cam_gens_cons_one ts]
    simp only [List.mem_finRange, true_and, decide_eq_true_eq]
    rw [eq_comm]
    exact hlab1 _ _
  have hinv : ∀ t ∈ 1 :: ts, ∀ u ∈ O, t u ∈ O := by
    intro t ht u hu
    rw [hmem] at hu ⊢
    rw [← cam_gens_cons_one ts] at hu ⊢
    exact cam_orbit_mem (Subgroup.subset_closure ht) hu
  set ts' := (1 :: ts).map (camRes O hO) with hts'
  have hres : ∀ t ∈ 1 :: ts, CamRestricts O.get (camRes O hO t) t := fun t ht =>
    camRes_spec O hO t (hinv t ht)
  refine ⟨O, hO, ts', hmem, fun g => ?_, by simp [hts'], ?_⟩
  · have := cam_restrict_gens O.get (fun _ _ h => (List.Nodup.get_inj_iff hO).mp h) (1 :: ts) ts'
      (fun t ht => ⟨_, List.mem_map_of_mem ht, hres t ht⟩)
      (fun g hg => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
        exact ⟨t, ht, hres t ht⟩) g
    rw [this, cam_gens_cons_one]
  -- the program
  set a := Val.list [c, encGroup ts] with ha
  set L := encFun lab with hL
  set R := natList (List.range n) with hR
  set Ov := natList (O.map Fin.val) with hOv
  set Ls := Val.list (ts'.map encPerm) with hLs
  have hlabn : ∀ x, lab x ≤ n := fun x => (hlab2 x).1.le
  have hOl : O.length ≤ n := by simpa using hO.length_le_card
  -- 1. the orbit labels
  have d1 := Det.call (Det.arg' (P := P) (vs := [c, encGroup ts]) (rest := []) (j := 1) rfl) hlabd
  -- 2. `range n`
  have fR : FunDet P (b + 34) (.nat n) R
      (loopModK * (n + 1) * ((Val.nat n).wt + n + R.wt + 1)) :=
    (range_spec hP.rng n).mono fun w cc h => ⟨h.1, by have := h.2; rw [h.1] at this; exact this⟩
  have d2 := Det.call (Det.encPerms_size (gs := 1 :: ts)
    (Det.arg' (P := P) (vs := [c, encGroup ts]) (rest := [L]) (j := 1) rfl)) fR
  -- 3. the orbit of `0`
  have hxs : ∀ x ∈ (List.range n).map Val.nat, FunDet P (b + 1) (.list [L, x])
      (boolVal (camLabQ lab x)) (100 * (n + 1) ^ 2 + 100) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact camLabTest_det hP.test lab hlabn hn ⟨y, List.mem_range.mp hy⟩
  have fF : FunDet P (b + 37) (.list [L, R]) Ov
      (n * (100 * (n + 1) ^ 2 + 100) + loopModK * (n + 1) * ((Val.list [L, R]).wt + n + Ov.wt + 1)) := by
    refine (filter_spec hP.flt hxs).mono fun w cc h => ?_
    obtain ⟨hw, hc⟩ := h
    rw [cam_filter_range lab hn] at hw
    subst hw
    refine ⟨rfl, ?_⟩
    have e1 : (((List.range n).map Val.nat).map fun _ => 100 * (n + 1) ^ 2 + 100).sum =
        n * (100 * (n + 1) ^ 2 + 100) := by simp [Function.comp_def, List.sum_replicate]
    rw [e1] at hc
    simp only [List.length_map, List.length_range] at hc
    exact hc
  have d3 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, L, R]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, L, R]) (i := 2) rfl)) fF
  -- 4. the restricted generators
  have hgs : ∀ x ∈ (1 :: ts).map encPerm, FunAll P (b + 43) (.list [Ov, x]) (fun w cost =>
      (∀ t ∈ 1 :: ts, x = encPerm t → w = encPerm (camRes O hO t)) ∧
        cost ≤ camResK * (n + 1) ^ 6) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    refine FunAll.mono (camRes_det hP.res O hO t (hinv t ht)) fun w cc h => ⟨fun t' _ ht' => ?_, h.2⟩
    rw [encPerm_injective ht'] at h
    exact h.1
  have fM : FunDet P (b + 40) (.list [Ov, .list ((1 :: ts).map encPerm)]) Ls
      ((ts.length + 1) * (camResK * (n + 1) ^ 6) +
        mapK * (ts.length + 2) * ((Val.list [Ov, .list ((1 :: ts).map encPerm)]).wt + Ls.wt + 1)) := by
    refine (map_spec hP.mp hgs).mono fun w cc h => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := h
    have hws' := forall₂_map_eq (g := fun t => encPerm (camRes O hO t))
      (fun t ht w hw => hw t ht rfl) hws
    have hw : ws = ts'.map encPerm := by rw [hws', hts', List.map_map]; rfl
    subst hw
    refine ⟨rfl, ?_⟩
    have e1 : (((1 :: ts).map encPerm).map fun _ => camResK * (n + 1) ^ 6).sum =
        (ts.length + 1) * (camResK * (n + 1) ^ 6) := by
      simp [Function.comp_def, List.sum_replicate]; ring
    rw [e1] at hc
    simp only [List.length_map, List.length_cons] at hc
    exact hc
  have d4 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, L, R, Ov]) (i := 3) rfl)
    (Det.encPerms_gens (gs := 1 :: ts)
      (Det.arg' (P := P) (vs := [c, encGroup ts]) (rest := [L, R, Ov]) (j := 1) rfl))) fM
  -- 5. the restricted group
  have dlen := Det.length (Det.var' (P := P) (env := [a, L, R, Ov, Ls]) (i := 3) rfl)
  have hlen : ((O.map Fin.val).map Val.nat).length = O.length := by simp
  rw [hlen] at dlen
  have d5 := Det.call (Det.mk2 dlen (Det.var' (P := P) (env := [a, L, R, Ov, Ls]) (i := 4) rfl))
    (mkGroup_spec hP.mg ts')
  -- 6. the result
  have d6 := Det.mk3 (Det.var' (P := P) (env := [a, L, R, Ov, Ls, encGroup ts']) (i := 3) rfl)
    (Det.var' (P := P) (env := [a, L, R, Ov, Ls, encGroup ts']) (i := 5) rfl)
    (Det.arg' (P := P) (vs := [c, encGroup ts]) (rest := [L, R, Ov, Ls, encGroup ts']) (j := 1) rfl)
  refine FunDet.intro hP.body ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4
    (Det.letE d5 d6))))).mono ?_)
  clear d1 d2 d3 d4 d5 d6 dlen fR fF fM hgs hxs hlabd
  -- the weights
  set W := a.wt with hW
  have haw : (Val.list [c, encGroup ts]).wt = W := rfl
  have hS := S_le_wt_encGroup ts
  have hgw : (encGroup ts).wt < W := wt_le_wt_list (by simp)
  have hcw : c.wt < W := wt_le_wt_list (by simp)
  have hn1 : n + 1 ≤ (ts.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hl1 : ts.length + 2 ≤ (ts.length + 2) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  set X := W + 1 with hX
  have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX37 : X ^ 3 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnX : n + 1 ≤ X := by omega
  have hn2 : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX 2
  have hwL : L.wt ≤ 4 * (n + 1) ^ 2 := wt_encFun_le_sq lab hlabn
  have hwR : R.wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (B := n) (fun x hx => (List.mem_range.mp hx).le) (by simp)
  have hwO : Ov.wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (B := n) (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega)
      (by simpa using hOl)
  have hts'l : ts'.length = ts.length + 1 := by simp [hts']
  have hSS : (ts'.length + 1) * (O.length + 1) ≤ X := by
    rw [hts'l]
    calc (ts.length + 1 + 1) * (O.length + 1) ≤ (ts.length + 2) * (n + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ X := by omega
  have hSS2 : (ts'.length + 2) * (O.length + 1) ≤ 2 * X := by
    rw [hts'l]
    calc (ts.length + 1 + 2) * (O.length + 1) ≤ (2 * (ts.length + 2)) * (n + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * ((ts.length + 2) * (n + 1)) := by ring
      _ ≤ 2 * X := by omega
  have hwLs : Ls.wt ≤ 13 * X ^ 2 :=
    (wt_list_encPerms_le ts').trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSS 2))
  have hwG' : (encGroup ts').wt ≤ 160 * X ^ 2 := by
    have := wt_encGroup_le ts'
    have h2 := Nat.pow_le_pow_left hSS2 2
    have e : (2 * X) ^ 2 = 4 * X ^ 2 := by ring
    omega
  -- the nonlinear terms
  have T1 : orbitK * (((1 :: ts).length + 1) * (n + 1)) ^ 5 ≤ orbitK * X ^ 7 := by
    have e : (1 :: ts).length + 1 = ts.length + 2 := by simp
    rw [e]
    refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 5).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hn3 : (n + 1) * (10 * X ^ 2) ≤ 10 * X ^ 3 := by
    calc (n + 1) * (10 * X ^ 2) ≤ X * (10 * X ^ 2) := Nat.mul_le_mul_right _ hnX
      _ = 10 * X ^ 3 := by ring
  have hn3' : (n + 1) * (40 * X ^ 2) ≤ 40 * X ^ 3 := by
    calc (n + 1) * (40 * X ^ 2) ≤ X * (40 * X ^ 2) := Nat.mul_le_mul_right _ hnX
      _ = 40 * X ^ 3 := by ring
  have wn := wt_nat_le n
  have T2 : loopModK * (n + 1) * ((Val.nat n).wt + n + R.wt + 1) ≤ loopModK * (10 * X ^ 3) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (by omega)).trans hn3)
  have T3 : n * (100 * (n + 1) ^ 2 + 100) ≤ 200 * X ^ 3 := by
    calc n * (100 * (n + 1) ^ 2 + 100) ≤ X * (200 * X ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 200 * X ^ 3 := by ring
  have wLR := wt_list2_le L R
  have T4 : loopModK * (n + 1) * ((Val.list [L, R]).wt + n + Ov.wt + 1) ≤
      loopModK * (40 * X ^ 3) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (by omega)).trans hn3')
  have hn6 : (n + 1) ^ 6 * X ≤ X ^ 7 := by
    calc (n + 1) ^ 6 * X ≤ X ^ 6 * X := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnX 6)
      _ = X ^ 7 := by ring
  have T5 : (ts.length + 1) * (camResK * (n + 1) ^ 6) ≤ camResK * X ^ 7 := by
    calc (ts.length + 1) * (camResK * (n + 1) ^ 6) ≤ X * (camResK * (n + 1) ^ 6) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = camResK * ((n + 1) ^ 6 * X) := by ring
      _ ≤ camResK * X ^ 7 := Nat.mul_le_mul_left _ hn6
  have wOg : (Val.list [Ov, .list ((1 :: ts).map encPerm)]).wt ≤ 2 * (Ov.wt + W) + 6 := by
    have := wt_list2_le Ov (.list ((1 :: ts).map encPerm))
    have : (Val.list ((1 :: ts).map encPerm)).wt < (encGroup ts).wt :=
      wt_le_wt_list (vs := [.nat n, _]) (by simp)
    omega
  have T6 : mapK * (ts.length + 2) * ((Val.list [Ov, .list ((1 :: ts).map encPerm)]).wt + Ls.wt + 1)
      ≤ mapK * (40 * X ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (ts.length + 2) * ((Val.list [Ov, .list ((1 :: ts).map encPerm)]).wt + Ls.wt + 1)
        ≤ X * (40 * X ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 40 * X ^ 3 := by ring
  have T7 : mkGroupK * ((ts'.length + 2) * (O.length + 1)) ^ 3 ≤ mkGroupK * (8 * X ^ 3) := by
    refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hSS2 3).trans (le_of_eq (by ring)))
  have w3 := wt_list3_le Ov (encGroup ts') (encGroup ts)
  have w2a := wt_list2_le (.nat O.length) Ls
  have w2b := wt_list2_le Ov Ls
  have w2c := wt_list2_le L R
  have hOn := wt_nat_le O.length
  have hlenO : ((O.map Fin.val).map Val.nat).length = O.length := by simp
  have hOv' : (Val.list ((O.map Fin.val).map Val.nat)).wt = Ov.wt := rfl
  have hgl : (Val.list ((1 :: ts).map encPerm)).wt < (encGroup ts).wt :=
    wt_le_wt_list (vs := [.nat n, _]) (by simp)
  simp only [camRestrK, orbitK, loopModK, camResK, mapK, mkGroupK] at *
  clear_value X W a L R Ov Ls ts' O
  generalize X ^ 7 = Q7 at *
  generalize X ^ 3 = Q3 at *
  generalize X ^ 2 = Q2 at *
  omega

end GI.Impl
