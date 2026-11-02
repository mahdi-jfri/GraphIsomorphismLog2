import Workspace.Impl.CamPRestr
import Workspace.Impl.CamPTrans
import Workspace.Lang.Prims.Johnson
import Workspace.Lang.Prims.PermGroups
import Workspace.Lang.Prims.Blocks

/-!
# Steps 7–8 of `camProg`: the coordinate of one factor

`camColBody` works on `[[N, ⊥, m, k], [O, ⟨ts'⟩, T]]`, where `T = ⟨ts⟩` is one simple factor of
the socle `N`, `O` is an orbit of `T` and `⟨ts'⟩` is `T` restricted to `O` (`camRestr_spec`).
1. **Johnson identification** ([H, §2.8]) of `⟨ts'⟩`: a bijection `ι` from the positions of `O`
   to the `k`-sets of `Fin m`.
2. **Centralizer** `C = C_N(T)`, by the cited **QuotientCentralizer** with `K = 1`.
3. The orbit labels of `C`; for every point `x`, the position `w x` of the first point of `O`
   with the label of `x`.
4. The column: for every point `x`, the `k`-set `ι (w x)`.

When `C` is the product of the other factors, two points have the same label exactly when they
have the same coordinate at this factor (`camX_orbit_others`), so `ι (w x)` is the coordinate of
`x`, up to the renaming of `Fin m` that `cam_combine` absorbs.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp len len_le_self)

variable {n : ℕ}

/-! ### Weights -/

/-- A `k`-set of `Fin m`, as the sorted list of its elements. -/
def kVal {m k : ℕ} (A : {A : Finset (Fin m) // A.card = k}) : Val :=
  .list ((A.1.sort (· ≤ ·)).map fun a => .nat a)

theorem encKSets_eq {n' m k : ℕ} (ι : Fin n' ≃ {A : Finset (Fin m) // A.card = k}) :
    encKSets ι = .list ((List.finRange n').map fun w => kVal (ι w)) := rfl

theorem cam_flatMap_val {m : ℕ} (l : List (Fin m)) :
    List.flatMap (fun a : Fin m => [Fin.val a]) l = List.map Fin.val l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

theorem wt_kVal_le {m k : ℕ} (A : {A : Finset (Fin m) // A.card = k}) :
    (kVal A).wt ≤ 5 * (m + 1) ^ 2 := by
  have e : kVal A = natList ((A.1.sort (· ≤ ·)).map Fin.val) := by
    simp [kVal, natList, cam_flatMap_val, List.map_map, Function.comp_def]
  rw [e]
  have hl : ((A.1.sort (· ≤ ·)).map Fin.val).length ≤ m := by
    simp only [List.length_map, Finset.length_sort]
    exact (Finset.card_le_univ _).trans (by simp)
  exact wt_natList_le_sq (B := m) (by
    intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact a.isLt.le) hl

theorem wt_encKSets_le {n' m k : ℕ} (ι : Fin n' ≃ {A : Finset (Fin m) // A.card = k}) :
    (encKSets ι).wt ≤ n' * (10 * (m + 1) ^ 2 + 1) + 4 := by
  rw [encKSets_eq]
  have := cam_wt_list_le_of (vs := (List.finRange n').map fun w => kVal (ι w)) (B := 5 * (m + 1) ^ 2)
    (by intro v hv; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv; exact wt_kVal_le _)
  simp only [List.length_map, List.length_finRange] at this
  have e : 2 * (5 * (m + 1) ^ 2) + 1 = 10 * (m + 1) ^ 2 + 1 := by ring
  rw [e] at this
  exact this

theorem cam_gens_nil : gens ([] : List (Perm (Fin n))) = ⊥ := by
  simp [gens]

/-- The centralizer of `T` in `N`, as the output of **QuotientCentralizer** with `K = 1`. -/
def CamCent (N T C : Subgroup (Perm (Fin n))) : Prop :=
  ∀ y, y ∈ C ↔ y ∈ N ∧ ∀ x ∈ T, y * x * y⁻¹ * x⁻¹ ∈ (⊥ : Subgroup (Perm (Fin n)))

/-! ### The program -/

/-- The body, at base `b`, with the primitives `jj` (Johnson) and `jq` (QuotientCentralizer).
Environment `[a, ι, C gens, C, labels of C, labels of O, positions]`. -/
def camColBody (b jj jq : ℕ) : Expr :=
  .letE (.prim jj (mk3 (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 3))))
  (.letE (.prim jq (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 0))
      (.get (arg 1) (.nat 2))))
  (.letE (.call (b + 1) (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 2)))
  (.letE (.call (b + 8) (.var 3))
  (.letE (.call (b + 40) (mk2 (.var 4) (.get (arg 1) (.nat 0))))
  (.letE (.call (b + 44) (mk2 (.var 5) (.var 4)))
    (.call (b + 40) (mk2 (.var 1) (.var 6))))))))

/-- The coordinate of one factor, at base `b` (52 functions). -/
def camColFuns (b jj jq : ℕ) : List Expr :=
  [camColBody b jj jq] ++ mkGroupFuns (b + 1) ++ orbitFuns (b + 8) ++ gatherFuns (b + 40) ++
    camIdxFuns (b + 44)

/-- Where the parts of the column function sit. -/
structure CamColAt (P : Program) (b jj jq : ℕ) (hj : JohnsonIdentification)
    (hqc : QuotientCentralizer) : Prop where
  body : P.funs[b]? = some (camColBody b jj jq)
  mg : P.HasAt (b + 1) (mkGroupFuns (b + 1))
  orb : P.HasAt (b + 8) (orbitFuns (b + 8))
  gat : P.HasAt (b + 40) (gatherFuns (b + 40))
  idx : P.HasAt (b + 44) (camIdxFuns (b + 44))
  pj : P.prims[jj]? = some (johnsonPrim hj)
  pq : P.prims[jq]? = some (quotientCentralizerPrim hqc)

theorem camColAt_of {P : Program} {b jj jq : ℕ} {hj : JohnsonIdentification}
    {hqc : QuotientCentralizer} (h : P.HasAt b (camColFuns b jj jq))
    (pj : P.prims[jj]? = some (johnsonPrim hj)) (pq : P.prims[jq]? = some (quotientCentralizerPrim hqc)) :
    CamColAt P b jj jq hj hqc := by
  simp only [camColFuns] at h
  exact
  { body := h.left.left.left.left.single
    mg := by simpa using h.left.left.left.right
    orb := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, Nat.add_assoc] using
      h.left.left.right
    gat := by
      simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, length_orbitFuns, Nat.add_assoc] using
        h.left.right
    idx := by
      simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, length_orbitFuns, gatherFuns, mapFuns,
        Nat.add_assoc] using h.right
    pj := pj
    pq := pq }

/-- The value of `gather` on a list of labels. -/
theorem cam_gather_lab (lab : Fin n → ℕ) (O : List (Fin n)) :
    (O.map Fin.val).map (fun i => ((List.finRange n).map fun j => Val.nat (lab j)).getD i (.nat 0)) =
      (O.map lab).map Val.nat := by
  simp only [List.map_map]
  refine List.map_congr_left fun u _ => ?_
  simp [List.getD_eq_getElem?_getD]

def camColK : ℕ := 10 ^ 18

/-- **The coordinate of one factor.** -/
theorem camCol_spec {hj : JohnsonIdentification} {hqc : QuotientCentralizer} {P : Program}
    {b jj jq : ℕ} (hP : CamColAt P b jj jq hj hqc) (ns ts : List (Perm (Fin n)))
    (O : List (Fin n)) (hO : O.Nodup) (ts' : List (Perm (Fin O.length))) {m k : ℕ}
    (hTN : gens ts ≤ gens ns) (hnorm : ∀ y ∈ gens ns, ∀ x ∈ gens ts, y * x * y⁻¹ ∈ gens ts)
    (h5 : 5 ≤ m) (hk1 : 1 ≤ k) (hb : (k + 1) ^ 2 < m + 2) (hmn : m ≤ n)
    (hJ : ∃ ι : Fin O.length ≃ {A : Finset (Fin m) // A.card = k}, IsJohnsonId (gens ts') ι)
    (hcov : ∀ C, CamCent (gens ns) (gens ts) C → ∀ x, ∃ u ∈ O, u ∈ MulAction.orbit C x) :
    FunAll P b (.list [.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m, .nat k],
        .list [natList (O.map Fin.val), encGroup ts', encGroup ts]])
      (fun v cost => ∃ ι : Fin O.length ≃ {A : Finset (Fin m) // A.card = k},
        IsJohnsonId (gens ts') ι ∧ ∃ w : Fin n → Fin O.length,
          (∀ C, CamCent (gens ns) (gens ts) C → ∀ x, O.get (w x) ∈ MulAction.orbit C x) ∧
          v = .list ((List.finRange n).map fun x => kVal (ι (w x))) ∧
          cost ≤ (johnsonPrim hj).boundSize (10 * ((Val.list [.list [encGroup ns,
              encGroup ([] : List (Perm (Fin n))), .nat m, .nat k],
              .list [natList (O.map Fin.val), encGroup ts', encGroup ts]]).wt + 1)) +
            (quotientCentralizerPrim hqc).boundSize (10 * ((Val.list [.list [encGroup ns,
              encGroup ([] : List (Perm (Fin n))), .nat m, .nat k],
              .list [natList (O.map Fin.val), encGroup ts', encGroup ts]]).wt + 1)) +
            camColK * ((Val.list [.list [encGroup ns, encGroup ([] : List (Perm (Fin n))),
              .nat m, .nat k], .list [natList (O.map Fin.val), encGroup ts', encGroup ts]]).wt
              + 1) ^ 15) := by
  set cx := Val.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m, .nat k] with hcx
  set aj := Val.list [natList (O.map Fin.val), encGroup ts', encGroup ts] with haj
  set a := Val.list [cx, aj] with ha
  have hOl : O.length ≤ n := by simpa using hO.length_le_card
  -- 1. Johnson
  have dA0 := Det.arg' (P := P) (vs := [cx, aj]) (rest := []) (j := 0) rfl
  have dA1 := Det.arg' (P := P) (vs := [cx, aj]) (rest := []) (j := 1) rfl
  have dJa := Det.mk3 (Det.get' dA1 (Det.nat 1)
      (show [natList (O.map Fin.val), encGroup ts', encGroup ts][1]? = some (encGroup ts') from rfl))
    (Det.get' dA0 (Det.nat 2) (show [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m,
      .nat k][2]? = some (.nat m) from rfl))
    (Det.get' dA0 (Det.nat 3) (show [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m,
      .nat k][3]? = some (.nat k) from rfl))
  refine FunAll.intro hP.body (EvalAll.letE (johnson_call hj hP.pj dJa ⟨ts', rfl, rfl⟩ h5 hk1 hb hJ)
    fun vI cI hI => ?_)
  obtain ⟨⟨ι, hι, rfl⟩, hcI⟩ := hI
  -- 2. the centralizer
  have hK : gens ([] : List (Perm (Fin n))) = ⊥ := cam_gens_nil
  have hKG : gens ([] : List (Perm (Fin n))) ≤ gens ns := by rw [hK]; exact bot_le
  have hKn : ∀ g ∈ gens ns, ∀ k ∈ gens ([] : List (Perm (Fin n))),
      g * k * g⁻¹ ∈ gens ([] : List (Perm (Fin n))) := by
    intro g _ k hk; rw [hK] at hk ⊢; rw [Subgroup.mem_bot] at hk ⊢; rw [hk]; group
  have hKT : gens ([] : List (Perm (Fin n))) ≤ gens ts := by rw [hK]; exact bot_le
  have dB0 := Det.arg' (P := P) (vs := [cx, aj]) (rest := [encKSets ι]) (j := 0) rfl
  have dB1 := Det.arg' (P := P) (vs := [cx, aj]) (rest := [encKSets ι]) (j := 1) rfl
  have dN := Det.get' dB0 (Det.nat 0) (show [encGroup ns, encGroup ([] : List (Perm (Fin n))),
    .nat m, .nat k][0]? = some (encGroup ns) from rfl)
  have dQa := Det.mk4 dN (Det.get' dB0 (Det.nat 1) (show [encGroup ns,
      encGroup ([] : List (Perm (Fin n))), .nat m, .nat k][1]? = some
      (encGroup ([] : List (Perm (Fin n)))) from rfl)) dN
    (Det.get' dB1 (Det.nat 2)
      (show [natList (O.map Fin.val), encGroup ts', encGroup ts][2]? = some (encGroup ts) from rfl))
  refine EvalAll.letE (quotientCentralizer_call hqc hP.pq dQa ⟨ns, rfl, rfl⟩ ⟨[], rfl, rfl⟩
    ⟨ns, rfl, rfl⟩ ⟨ts, rfl, rfl⟩ hKG hKn hKG hKT le_rfl hTN hnorm) fun vQ cQ hQ => ?_
  obtain ⟨⟨C, hCg, hCm⟩, hcQ⟩ := hQ
  have hCC : CamCent (gens ns) (gens ts) C := by
    intro y; rw [hCm y, hK]
  obtain ⟨cks, rfl, hcl, fC, ⟨cks', hce, hcg⟩, hCw⟩ := mkGroup_gensVal hP.mg hCg
  obtain rfl := encGroup_injective hce
  -- 3. the orbit labels of `C`
  obtain ⟨lab, hlabd, hlab1, hlab2⟩ := orbits_spec hP.orb (1 :: cks)
  have hgC : gens (1 :: cks) = C := by rw [cam_gens_cons_one, hcg]
  have hlabn : ∀ x, lab x ≤ n := fun x => (hlab2 x).1.le
  have hlabO : ∀ x y, lab x = lab y ↔ y ∈ MulAction.orbit C x := by
    intro x y; rw [hlab1, ← hgC]; rfl
  -- 4. the positions
  have hex : ∀ x : Fin n, (O.map lab).findIdx (fun v => decide (v = lab x)) < O.length := by
    intro x
    obtain ⟨u, hu, hux⟩ := hcov C hCC x
    have := List.findIdx_lt_length_of_exists (p := fun v => decide (v = lab x)) (xs := O.map lab)
      ⟨lab u, List.mem_map_of_mem hu, by simp [(hlabO x u).mpr hux]⟩
    simpa using this
  set w : Fin n → Fin O.length := fun x => ⟨_, hex x⟩ with hw
  have hwl : ∀ x, lab (O.get (w x)) = lab x := by
    intro x
    have h1 := List.findIdx_getElem (p := fun v => decide (v = lab x)) (xs := O.map lab)
      (w := by simpa using hex x)
    simp only [List.getElem_map, decide_eq_true_eq] at h1
    exact h1
  have hwC : ∀ C', CamCent (gens ns) (gens ts) C' → ∀ x, O.get (w x) ∈ MulAction.orbit C' x := by
    intro C' hC' x
    have hCe : C' = C := by ext y; rw [hC' y, hCC y]
    rw [hCe, ← hlabO]
    exact (hwl x).symm
  -- the deterministic rest
  set I := encKSets ι with hI
  set vQ := Val.list (cks.map encPerm) with hvQ
  have dC0 := Det.arg' (P := P) (vs := [cx, aj]) (rest := [I, vQ]) (j := 0) rfl
  have dCn := Det.encPerms_size (gs := 1 :: ns) (Det.get' dC0 (Det.nat 0) (show [encGroup ns,
    encGroup ([] : List (Perm (Fin n))), .nat m, .nat k][0]? = some (encGroup ns) from rfl))
  have d3 := Det.call (Det.mk2 dCn (Det.var' (P := P) (env := [a, I, vQ]) (i := 2) rfl)) fC
  have d4 := Det.call (Det.var' (P := P) (env := [a, I, vQ, encGroup cks]) (i := 3) rfl) hlabd
  have hgi : ∀ i ∈ O.map Fin.val, i < ((List.finRange n).map fun j => Val.nat (lab j)).length := by
    intro i hi; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hi; simp
  have fG1 := gather_spec hP.gat hgi
  rw [cam_gather_lab] at fG1
  have dE1 := Det.arg' (P := P) (vs := [cx, aj]) (rest := [I, vQ, encGroup cks, encFun lab]) (j := 1) rfl
  have d5 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, I, vQ, encGroup cks, encFun lab])
    (i := 4) rfl) (Det.get' dE1 (Det.nat 0) (show [natList (O.map Fin.val), encGroup ts',
      encGroup ts][0]? = some (natList (O.map Fin.val)) from rfl))) fG1
  set OL := Val.list ((O.map lab).map Val.nat) with hOL
  have hOLn : OL = natList (O.map lab) := rfl
  have fI := camIdx_spec hP.idx (O := O.map lab) (vs := (List.finRange n).map lab) (B := n)
    (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact hlabn u)
    (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact hlabn u)
    (by simpa using hOl) (by simp)
  rw [← encFun_eq_natList] at fI
  have dv4 := Det.var' (P := P) (env := [a, I, vQ, encGroup cks, encFun lab, OL]) (i := 4) rfl
  have d6 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, I, vQ, encGroup cks, encFun lab, OL])
    (i := 5) rfl) dv4) fI
  set IX := natList (((List.finRange n).map lab).map fun v =>
    (O.map lab).findIdx fun x => decide (x = v)) with hIX
  have hix : ∀ i ∈ ((List.finRange n).map lab).map (fun v => (O.map lab).findIdx fun x =>
      decide (x = v)), i < ((List.finRange O.length).map fun w => kVal (ι w)).length := by
    intro i hi
    simp only [List.map_map, List.mem_map, List.mem_finRange, true_and, Function.comp_apply] at hi
    obtain ⟨x, rfl⟩ := hi
    simpa using hex x
  have fG2 := gather_spec hP.gat hix
  have hval : ((((List.finRange n).map lab).map fun v => (O.map lab).findIdx fun x =>
      decide (x = v)).map fun i => ((List.finRange O.length).map fun w => kVal (ι w)).getD i
        (.nat 0)) = (List.finRange n).map fun x => kVal (ι (w x)) := by
    simp only [List.map_map]
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, List.getD_eq_getElem?_getD]
    have hx := hex x
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hx)]
    simp [hw]
  rw [hval] at fG2
  have d7 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, I, vQ, encGroup cks, encFun lab, OL, IX])
    (i := 1) rfl) (Det.var' (P := P) (env := [a, I, vQ, encGroup cks, encFun lab, OL, IX])
    (i := 6) rfl)) fG2
  refine (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6 d7)))).post fun cc hcc =>
    ⟨ι, hι, w, hwC, rfl, ?_⟩
  clear d3 d4 d5 d6 d7 dQa dJa dA0 dA1 dB0 dB1 dN dC0 dCn dE1 dv4 fG1 fG2 fI fC hlabd
  -- the weights
  have hIXw : IX.wt = (natList (((List.finRange n).map lab).map fun v =>
    (O.map lab).findIdx fun x => decide (x = v))).wt := rfl
  have hOLw : OL.wt = (natList (O.map lab)).wt := rfl
  have haw : (Val.list [cx, aj]).wt = a.wt := rfl
  have hcxw : cx.wt < a.wt := wt_le_wt_list (by simp)
  have hajw : aj.wt < a.wt := wt_le_wt_list (by simp)
  have hNw : (encGroup ns).wt < cx.wt := wt_le_wt_list (by simp)
  have hKw : (encGroup ([] : List (Perm (Fin n)))).wt < cx.wt := wt_le_wt_list (by simp)
  have hmw : (Val.nat m).wt < cx.wt := wt_le_wt_list (by simp)
  have hkw : (Val.nat k).wt < cx.wt := wt_le_wt_list (by simp)
  have hOvw : (natList (O.map Fin.val)).wt < aj.wt := wt_le_wt_list (by simp)
  have hT'w : (encGroup ts').wt < aj.wt := wt_le_wt_list (by simp)
  have hTw : (encGroup ts).wt < aj.wt := wt_le_wt_list (by simp)
  have hnN := S_le_wt_encGroup ns
  have hn1 : n + 1 ≤ (ns.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  set X := a.wt + 1 with hX
  have hnX : n + 1 ≤ X := by omega
  have hXp : ∀ i j, i ≤ j → X ^ i ≤ X ^ j := fun i j h => Nat.pow_le_pow_right (by omega) h
  have hn2 : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX 2
  have hn3 : (n + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hnX 3
  have hn4 : (n + 1) ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hnX 4
  have hn6 : (n + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hnX 6
  have hn9 : (n + 1) ^ 9 ≤ X ^ 9 := Nat.pow_le_pow_left hnX 9
  have h1X : 1 ≤ X := by omega
  have hX12 := hXp 1 2 (by omega)
  have hX23 := hXp 2 3 (by omega)
  have hX34 := hXp 3 4 (by omega)
  have hX46 := hXp 4 6 (by omega)
  have hX69 := hXp 6 9 (by omega)
  have hX915 := hXp 9 15 (by omega)
  have hXX : X ^ 1 = X := pow_one X
  -- the primitive calls
  have wJa := wt_list3_le (encGroup ts') (.nat m) (.nat k)
  have A1 := (johnsonPrim hj).bound_le (v := .list [encGroup ts', .nat m, .nat k])
    (B := 10 * X) ((Val.size_le_wt _).trans (by omega))
  have wQa := wt_list4_le (encGroup ns) (encGroup ([] : List (Perm (Fin n)))) (encGroup ns)
    (encGroup ts)
  have A2 := (quotientCentralizerPrim hqc).bound_le (v := .list [encGroup ns,
    encGroup ([] : List (Perm (Fin n))), encGroup ns, encGroup ts]) (B := 10 * X)
    ((Val.size_le_wt _).trans (by omega))
  -- the values
  have hX2 : 2 ≤ X := by have := a.two_le_size; have := a.size_le_wt; omega
  have hX38 : 8 ≤ X ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hX2 3
  have wI : I.wt ≤ 12 * X ^ 3 := by
    have h1 := wt_encKSets_le ι
    rw [← hI] at h1
    have h2 : O.length * (10 * (m + 1) ^ 2 + 1) ≤ X * (11 * X ^ 2) := by
      refine Nat.mul_le_mul (by omega) ?_
      have := Nat.pow_le_pow_left (show m + 1 ≤ n + 1 by omega) 2
      omega
    have e : X * (11 * X ^ 2) = 11 * X ^ 3 := by ring
    omega
  have wvQ : vQ.wt ≤ 13 * X ^ 6 := (GensVal.wt_le hCg).trans (by omega)
  have wCk : (encGroup cks).wt ≤ 320 * X ^ 6 := hCw.trans (by omega)
  have wL : (encFun lab).wt ≤ 4 * X ^ 2 := (wt_encFun_le_sq lab hlabn).trans (by omega)
  have wOL : OL.wt ≤ 5 * X ^ 2 := by
    rw [hOLw]
    refine (wt_natList_le_sq (B := n) ?_ (by simpa using hOl)).trans (by omega)
    intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact hlabn u
  have wIX : IX.wt ≤ 5 * X ^ 2 := by
    rw [hIXw]
    refine (wt_natList_le_sq (B := n) ?_ (by simp)).trans (by omega)
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact List.findIdx_le_length.trans (by simpa using hOl)
  have wOv : (natList (O.map Fin.val)).wt ≤ 5 * X ^ 2 := by
    refine (wt_natList_le_sq (B := n) ?_ (by simpa using hOl)).trans (by omega)
    intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega
  have wR : (Val.list ((List.finRange n).map fun x => kVal (ι (w x)))).wt ≤ 12 * X ^ 3 := by
    have h1 := cam_wt_list_le_of (vs := (List.finRange n).map fun x => kVal (ι (w x)))
      (B := 5 * (m + 1) ^ 2)
      (fun v hv => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv; exact wt_kVal_le _)
    simp only [List.length_map, List.length_finRange] at h1
    have h2 : n * (2 * (5 * (m + 1) ^ 2) + 1) ≤ X * (11 * X ^ 2) := by
      refine Nat.mul_le_mul (by omega) ?_
      have := Nat.pow_le_pow_left (show m + 1 ≤ n + 1 by omega) 2
      omega
    have e : X * (11 * X ^ 2) = 11 * X ^ 3 := by ring
    omega
  -- the library calls
  have A3 : 8 * mkGroupK * (n + 1) ^ 9 ≤ 8 * mkGroupK * X ^ 15 :=
    Nat.mul_le_mul_left _ (hn9.trans hX915)
  have A4 : orbitK * (((1 :: cks).length + 1) * (n + 1)) ^ 5 ≤ 32 * orbitK * X ^ 15 := by
    have h1 : ((1 :: cks).length + 1) * (n + 1) ≤ 2 * X ^ 3 := by
      have : (1 :: cks).length + 1 ≤ 2 * (n + 1) ^ 2 := by
        have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
        simp only [List.length_cons]; omega
      calc ((1 :: cks).length + 1) * (n + 1) ≤ (2 * (n + 1) ^ 2) * (n + 1) :=
            Nat.mul_le_mul_right _ this
        _ = 2 * (n + 1) ^ 3 := by ring
        _ ≤ 2 * X ^ 3 := by omega
    have h2 := Nat.pow_le_pow_left h1 5
    have e : (2 * X ^ 3) ^ 5 = 32 * X ^ 15 := by ring
    rw [e] at h2
    calc orbitK * (((1 :: cks).length + 1) * (n + 1)) ^ 5 ≤ orbitK * (32 * X ^ 15) :=
          Nat.mul_le_mul_left _ h2
      _ = 32 * orbitK * X ^ 15 := by ring
  have A5 : gatherK * ((Val.list [.list ((List.finRange n).map fun j => Val.nat (lab j)),
      natList (O.map Fin.val)]).wt + 1) ^ 3 ≤ 8000 * gatherK * X ^ 15 := by
    have h0 := wt_list2_le (encFun lab) (natList (O.map Fin.val))
    have h1 : (Val.list [.list ((List.finRange n).map fun j => Val.nat (lab j)),
        natList (O.map Fin.val)]).wt + 1 ≤ 20 * X ^ 2 := by
      have : (Val.list [.list ((List.finRange n).map fun j => Val.nat (lab j)),
        natList (O.map Fin.val)]).wt = (Val.list [encFun lab, natList (O.map Fin.val)]).wt := rfl
      omega
    have h2 := Nat.pow_le_pow_left h1 3
    have e : (20 * X ^ 2) ^ 3 = 8000 * X ^ 6 := by ring
    rw [e] at h2
    calc _ ≤ gatherK * (8000 * X ^ 6) := Nat.mul_le_mul_left _ h2
      _ = 8000 * gatherK * X ^ 6 := by ring
      _ ≤ 8000 * gatherK * X ^ 15 := Nat.mul_le_mul_left _ (by omega)
  have A6 : camIdxK * (n + 1) ^ 4 ≤ camIdxK * X ^ 15 := Nat.mul_le_mul_left _ (by omega)
  have A7 : gatherK * ((Val.list [.list ((List.finRange O.length).map fun w => kVal (ι w)),
      natList (((List.finRange n).map lab).map fun v =>
        (O.map lab).findIdx fun x => decide (x = v))]).wt + 1) ^ 3 ≤ 64000 * gatherK * X ^ 15 := by
    have h0 := wt_list2_le I IX
    have h1 : (Val.list [.list ((List.finRange O.length).map fun w => kVal (ι w)),
      natList (((List.finRange n).map lab).map fun v =>
        (O.map lab).findIdx fun x => decide (x = v))]).wt + 1 ≤ 40 * X ^ 3 := by
      have : (Val.list [.list ((List.finRange O.length).map fun w => kVal (ι w)),
        natList (((List.finRange n).map lab).map fun v =>
          (O.map lab).findIdx fun x => decide (x = v))]).wt = (Val.list [I, IX]).wt := rfl
      omega
    have h2 := Nat.pow_le_pow_left h1 3
    have e : (40 * X ^ 3) ^ 3 = 64000 * X ^ 9 := by ring
    rw [e] at h2
    calc _ ≤ gatherK * (64000 * X ^ 9) := Nat.mul_le_mul_left _ h2
      _ = 64000 * gatherK * X ^ 9 := by ring
      _ ≤ 64000 * gatherK * X ^ 15 := Nat.mul_le_mul_left _ (by omega)
  have wvI := wt_list2_le I IX
  have wvL := wt_list2_le (encFun lab) (natList (O.map Fin.val))
  have wvO := wt_list2_le OL (encFun lab)
  have wvC := wt_list2_le (.nat n) vQ
  have wnn := wt_nat_le n
  have hOLe : (Val.list ((O.map lab).map Val.nat)).wt = OL.wt := rfl
  have hEN : (encPerms (1 :: ns)).wt = (encGroup ns).wt := rfl
  simp only [camColK, orbitK, mkGroupK, gatherK, camIdxK] at *
  clear_value X a cx aj I vQ OL IX w
  generalize X ^ 15 = Q15 at *
  generalize X ^ 9 = Q9 at *
  generalize X ^ 6 = Q6 at *
  generalize X ^ 4 = Q4 at *
  generalize X ^ 3 = Q3 at *
  generalize X ^ 2 = Q2 at *
  omega

end GI.Impl
