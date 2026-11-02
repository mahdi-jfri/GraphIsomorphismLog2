import Workspace.Assembly.ConvertParts

/-!
# Converting the answer (`ConvertSpec`)

`convFuns c` is a program of 20 functions at base `c`. Its entry gets `[inputVal G H, u]`,
where `u` is the value of the answer of the pair state (`AnswerVal`).

* If `u = []`, the graphs are not isomorphic, and the entry returns `[0]`.
* Otherwise `u = [x, encGroup gs]` stores a coset `x · ⟨gs⟩`. The entry calls `yesF`, which
  reads `n` off the input, reads the vertex permutation `p` of `x` off the diagonal
  (`p i = x (i, i) / n`), projects `1` and the generators `gs` in the same way, and lays out
  `[1, p 0, …, p (n - 1), k, h₀ 0, …]` (`yes_spec`).

By `coset_rep` and `coset_group` (`Workspace/Assembly/ConvertMath.lean`), `p` is an isomorphism
and the projections generate `Aut(G)` (`closure_unPair`), so the output is correct
(`convert_spec`). The cost is at most `convK * (wt u + n + 1)^6`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)
open GI.Machine (BinOp)
open scoped Pointwise

variable {n : ℕ}

/-! ### Lists of numbers -/

theorem encFun_eq_ofFn (f : Fin n → ℕ) : encFun f = .list ((List.ofFn f).map .nat) := by
  rw [List.ofFn_eq_map, List.map_map]; rfl

theorem wt_natList_le (l : List ℕ) {B : ℕ} (h : ∀ x ∈ l, x ≤ B) :
    (Val.list (l.map .nat)).wt ≤ l.length * (2 * B + 5) + 4 := by
  have h1 := wt_list_le (l.map Val.nat)
  have h2 : ((l.map Val.nat).map Val.wt).sum ≤ l.length * (B + 2) := by
    have := List.sum_le_card_nsmul ((l.map Val.nat).map Val.wt) (B + 2) (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp]
      rintro _ x hx rfl; have := wt_nat_le x; have := h x hx; omega)
    simpa using this
  simp only [List.length_map] at h1
  nlinarith

/-! ### The cells of a positive answer -/

/-- The first cells: 1, the diagonal of `x`, and the number of generators (with the identity). -/
def yesPre (x : Perm (Fin (n * n))) (gs : List (Perm (Fin (n * n)))) : List ℕ :=
  1 :: (List.ofFn (proj x) ++ [gs.length + 1])

/-- The diagonals of the identity and of the generators. -/
def yesGens (gs : List (Perm (Fin (n * n)))) : List (List ℕ) :=
  (1 :: gs).map fun g => List.ofFn (proj g)

theorem length_yesGens (gs : List (Perm (Fin (n * n)))) : (yesGens gs).length = gs.length + 1 := by
  simp [yesGens]

theorem yesGens_length_mem {gs : List (Perm (Fin (n * n)))} :
    ∀ l ∈ yesGens gs, l.length = n := by
  intro l hl
  obtain ⟨g, -, rfl⟩ := List.mem_map.mp hl
  simp

theorem yesGens_le {gs : List (Perm (Fin (n * n)))} :
    ∀ x ∈ (yesGens gs).flatten, x ≤ n := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨g, -, rfl⟩ := List.mem_map.mp hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact proj_le g i

/-! ### The positive case -/

/-- The positive case at base `c` (`yesF c` sits at `c + 1`): read `n`, build
`ids = [0, …, n - 1]` (`c + 2`), the diagonal of the representative (`c + 5`), the diagonals of
the generators (`c + 9`), the first cells (`c + 13`), and concatenate (`c + 16`). -/
def yesF (c : ℕ) : Expr :=
  .letE (.get (arg 0) (.nat 0))
  (.letE (.call (c + 2) (.var 1))
  (.letE (.call (c + 5) (mk2 (mk2 (.var 1) (.get (arg 1) (.nat 0))) (.var 2)))
  (.letE (.get (.get (arg 1) (.nat 1)) (.nat 1))
  (.letE (.call (c + 9) (mk2 (mk2 (.var 1) (.var 2)) (.var 4)))
  (.letE (.snoc (.call (c + 13) (mk2 (mk1 (.nat 1)) (.var 3))) (.length (.var 4)))
    (.call (c + 16) (mk3 .nil (.var 5) (.var 6))))))))

/-- The entry of the converter at base `c`. -/
def convEntry (c : ℕ) : Expr :=
  .ite (.arith .eq (.length (arg 1)) (.nat 0)) (mk1 (.nat 0)) (.call (c + 1) (.var 0))

/-- **The converter**, at base `c` (20 functions). -/
def convFuns (c : ℕ) : List Expr :=
  [convEntry c, yesF c] ++ rangeFuns (c + 2) ++ diagMapFuns (c + 5) ++ projMapFuns (c + 9) (c + 5)
    ++ appendFuns (c + 13) ++ catFuns (c + 16) (c + 13)

theorem length_convFuns (c : ℕ) : (convFuns c).length = 20 := by
  simp [convFuns, rangeFuns, diagMapFuns, projMapFuns, appendFuns, catFuns, foldlFuns, mapFuns,
    loopFuns]

theorem convFuns_parts {P : Program} {c : ℕ} (h : P.HasAt c (convFuns c)) :
    P.funs[c]? = some (convEntry c) ∧ P.funs[c + 1]? = some (yesF c) ∧
      P.HasAt (c + 2) (rangeFuns (c + 2)) ∧ P.HasAt (c + 5) (diagMapFuns (c + 5)) ∧
      P.HasAt (c + 9) (projMapFuns (c + 9) (c + 5)) ∧ P.HasAt (c + 13) (appendFuns (c + 13)) ∧
      P.HasAt (c + 16) (catFuns (c + 16) (c + 13)) := by
  simp only [convFuns] at h
  have h0 := h.left.left.left.left.left
  refine ⟨by simpa using h0 0 (by simp), by simpa using h0 1 (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.left.left.left.left.right
  · simpa [rangeFuns, loopFuns, Nat.add_assoc] using h.left.left.left.right
  · simpa [rangeFuns, diagMapFuns, mapFuns, loopFuns, Nat.add_assoc] using h.left.left.right
  · simpa [rangeFuns, diagMapFuns, projMapFuns, mapFuns, loopFuns, Nat.add_assoc]
      using h.left.right
  · simpa [rangeFuns, diagMapFuns, projMapFuns, appendFuns, mapFuns, loopFuns, Nat.add_assoc]
      using h.right

/-- The constant of the cost bound of the converter. -/
def convK : ℕ := 100000000

theorem inputCells_zero (G H : SimpleGraph (Fin n)) : (inputCells G H)[0]? = some n := by
  simp [inputCells, (inputMem_layout G H).size]

theorem cells_yes_le (x : Perm (Fin (n * n))) (gs : List (Perm (Fin (n * n)))) :
    ∀ a ∈ yesPre x gs ++ (yesGens gs).flatten, a ≤ n + gs.length + 1 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · simp only [yesPre, List.mem_cons, List.mem_append, List.mem_ofFn, List.mem_nil_iff,
      or_false] at ha
    rcases ha with rfl | ⟨i, rfl⟩ | rfl
    · omega
    · have := proj_le x i; omega
    · omega
  · have := yesGens_le a ha; omega

theorem length_cells_yes (x : Perm (Fin (n * n))) (gs : List (Perm (Fin (n * n)))) :
    (yesPre x gs ++ (yesGens gs).flatten).length = n + 2 + (gs.length + 1) * n := by
  have : ((yesGens gs).map List.length).sum = (gs.length + 1) * n := by
    rw [List.map_congr_left yesGens_length_mem, List.map_const', List.sum_replicate,
      length_yesGens, smul_eq_mul]
  simp only [yesPre, List.length_append, List.length_cons, List.length_ofFn, List.length_flatten,
    List.length_nil, this]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **The positive case.** On `[inputVal G H, [x, encGroup gs]]`, `yesF` returns the cells
`yesPre x gs ++ (yesGens gs).flatten`, at cost at most `convK (wt u + n + 1)^6`. -/
theorem yes_spec {P : Program} {c : ℕ} (h : P.HasAt c (convFuns c)) (G H : SimpleGraph (Fin n))
    (x : Perm (Fin (n * n))) (gs : List (Perm (Fin (n * n)))) :
    FunDet P (c + 1) (.list [inputVal G H, .list [encPerm x, encGroup gs]])
      (.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat))
      (convK * ((Val.list [encPerm x, encGroup gs]).wt + n + 1) ^ 6) := by
  obtain ⟨-, hyes, hrange, hdm, hpm, happ, hcat⟩ := convFuns_parts h
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (Val.list [encPerm x, encGroup gs]).wt + n + 1 := ⟨_, rfl⟩
  rw [← hY]
  -- the values
  have eG : encGroup gs = .list [.nat (n * n), .list ((1 :: gs).map encPerm)] := rfl
  have hids : FunDet P (c + 2) (.nat n) (encFun fun i : Fin n => (i : ℕ)) (8000 * (n + 1) ^ 3) := by
    refine FunAll.mono (range_spec hrange n) fun w cw hw => ⟨?_, ?_⟩
    · rw [hw.1, encFun_id]
    · have hc := hw.2
      rw [hw.1, ← encFun_id, loopModK_mul] at hc
      have := wt_nat_le n
      have := wt_ids_le n
      have := mul_pow_le (show n + 1 ≤ 1 * (n + 1) ^ 1 by simp)
        (show (Val.nat n).wt + n + (encFun fun i : Fin n => (i : ℕ)).wt + 1 ≤ 8 * (n + 1) ^ 2
          by nlinarith)
      simp only [one_mul, show 1 + 2 = 3 from rfl] at this
      omega
  have hsig := diagMap_spec hdm (n := n) x
  have hPM := projMap_spec hpm hdm (n := n) (1 :: gs)
  have ehs : Val.list ((1 :: gs).map fun g => encFun (proj g)) =
      .list ((yesGens gs).map fun l => .list (l.map .nat)) := by
    simp only [yesGens, List.map_map, Function.comp_def, encFun_eq_ofFn]
  rw [ehs] at hPM
  have hAP := append_spec happ [.nat 1] ((List.ofFn (proj x)).map .nat)
  have hcat' := cat_spec hcat happ (.list []) (yesGens gs) (yesPre x gs) yesGens_length_mem
  -- weights
  have wI := wt_inputVal_le G H
  have wx := wt_encPerm_le x
  have wg : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := by
    rw [eG]; exact wt_le_wt_list (by simp)
  have wgu : (encGroup gs).wt < (Val.list [encPerm x, encGroup gs]).wt := wt_le_wt_list (by simp)
  have wxu : (encPerm x).wt < (Val.list [encPerm x, encGroup gs]).wt := wt_le_wt_list (by simp)
  have hlen := length_lt_wt_list ((1 :: gs).map encPerm)
  simp only [List.length_map, List.length_cons] at hlen
  have wsig := wt_encFun_le_sq (proj x) (proj_le x)
  have wids := wt_ids_le n
  have wn := wt_nat_le n
  have wout := wt_natList_le _ (cells_yes_le x gs)
  rw [length_cells_yes] at wout
  have wpre : (Val.list ((yesPre x gs).map .nat)).wt ≤
      (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt :=
    wt_list_mono (List.IsPrefix.map _ (List.prefix_append _ _))
  have whs : (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt ≤
      (gs.length + 1) * (8 * (n + 1) ^ 2 + 1) + 4 := by
    rw [← ehs]
    have h1 := wt_list_le ((1 :: gs).map fun g => encFun (proj g))
    have h2 : (((1 :: gs).map fun g => encFun (proj g)).map Val.wt).sum ≤
        (gs.length + 1) * (4 * (n + 1) ^ 2) := by
      have := List.sum_le_card_nsmul (((1 :: gs).map fun g => encFun (proj g)).map Val.wt)
        (4 * (n + 1) ^ 2) (by
          simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index,
            and_imp]
          rintro _ g - rfl; exact wt_encFun_le_sq (proj g) (proj_le g))
      simpa using this
    simp only [List.length_map, List.length_cons] at h1
    nlinarith
  rw [encFun_eq_ofFn (proj x)] at hsig wsig
  have ePRE : Val.list (([Val.nat 1] ++ (List.ofFn (proj x)).map .nat) ++
      [.nat ((1 :: gs).map encPerm).length]) = (Val.list ((yesPre x gs).map .nat)) := by
    simp [yesPre]
  -- the run
  have d1 : Det P [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])])] (.get (arg 0) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.arg' (P := P) (vs := [inputVal G H, (Val.list [encPerm x, encGroup gs])]) (rest := []) (j := 0) rfl :
      Det P [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])])] (arg 0) (.list ((inputCells G H).map .nat)) _) (Det.nat 0)
      (by simp [inputCells_zero G H])
  have d2 := Det.call (Det.var' (P := P) (env := [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n]) (i := 1) rfl) hids
  have gx : Det P [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n, (encFun fun i : Fin n => (i : ℕ))] (.get (arg 1) (.nat 0)) (encPerm x) _ :=
    Det.get' (Det.arg' (vs := [inputVal G H, (Val.list [encPerm x, encGroup gs])]) (rest := [.nat n, (encFun fun i : Fin n => (i : ℕ))]) (j := 1) rfl)
      (Det.nat 0) rfl
  have d3 := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := P) (env := [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n, (encFun fun i : Fin n => (i : ℕ))]) (i := 1)
    rfl) gx) (Det.var' (i := 2) rfl)) hsig
  have d4 : Det P [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n, (encFun fun i : Fin n => (i : ℕ)), (Val.list ((List.ofFn (proj x)).map .nat))] (.get (.get (arg 1) (.nat 1)) (.nat 1)) (Val.list ((1 :: gs).map encPerm)) _ :=
    Det.get' (Det.get' (Det.arg' (vs := [inputVal G H, (Val.list [encPerm x, encGroup gs])]) (rest := [.nat n, (encFun fun i : Fin n => (i : ℕ)), (Val.list ((List.ofFn (proj x)).map .nat))]) (j := 1)
      rfl) (Det.nat 1)
      (show ([encPerm x, encGroup gs] : List Val)[1]? = some (.list [.nat (n * n), (Val.list ((1 :: gs).map encPerm))]) from rfl))
      (Det.nat 1) rfl
  have hPMd : FunDet P (c + 9) (.list [.list [.nat n, (encFun fun i : Fin n => (i : ℕ))], (Val.list ((1 :: gs).map encPerm))]) (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat)))
      ((1 :: gs).length * (120000 * (n + 1) ^ 5) + mapK * ((1 :: gs).length + 1) *
        ((Val.list [.list [.nat n, (encFun fun i : Fin n => (i : ℕ))], (Val.list ((1 :: gs).map encPerm))]).wt + (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt + 1)) :=
    FunAll.mono hPM fun w cw hw => ⟨hw.1, by have := hw.2; rw [hw.1] at this; exact this⟩
  have d5 := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := P) (env := [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n, (encFun fun i : Fin n => (i : ℕ)), (Val.list ((List.ofFn (proj x)).map .nat)), (Val.list ((1 :: gs).map encPerm))])
    (i := 1) rfl) (Det.var' (i := 2) rfl)) (Det.var' (i := 4) rfl)) hPMd
  have hAPd : FunDet P (c + 13) (.list [.list [.nat 1], (Val.list ((List.ofFn (proj x)).map .nat))])
      (.list ([.nat 1] ++ (List.ofFn (proj x)).map .nat))
      (loopModK * (n + 1) * ((Val.list [.list [.nat 1], (Val.list ((List.ofFn (proj x)).map .nat))]).wt + n +
        (Val.list ([.nat 1] ++ (List.ofFn (proj x)).map .nat)).wt + 1)) :=
    FunAll.mono hAP fun w cw hw => ⟨hw.1, by
      have := hw.2; rw [hw.1] at this; simpa using this⟩
  have d6 := Det.snoc (Det.call (Det.mk2 (Det.mk1 (Det.nat 1)) (Det.var' (P := P)
    (env := [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n, (encFun fun i : Fin n => (i : ℕ)), (Val.list ((List.ofFn (proj x)).map .nat)), (Val.list ((1 :: gs).map encPerm)), (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat)))]) (i := 3) rfl)) hAPd)
    (Det.length (Det.var' (P := P) (env := [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n, (encFun fun i : Fin n => (i : ℕ)), (Val.list ((List.ofFn (proj x)).map .nat)), (Val.list ((1 :: gs).map encPerm)), (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat)))]) (i := 4) rfl))
  rw [ePRE] at d6
  have d7 := Det.call (Det.mk3 Det.nil (Det.var' (P := P)
    (env := [(Val.list [inputVal G H, (Val.list [encPerm x, encGroup gs])]), .nat n, (encFun fun i : Fin n => (i : ℕ)), (Val.list ((List.ofFn (proj x)).map .nat)), (Val.list ((1 :: gs).map encPerm)), (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))), (Val.list ((yesPre x gs).map .nat))]) (i := 5) rfl) (Det.var' (i := 6) rfl)) hcat'
  refine FunDet.intro hyes ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5
    (Det.letE d6 d7)))))).mono ?_)
  -- the cost: the bounds in `Y`
  have hgY : gs.length + 3 ≤ Y := by omega
  have hnY : n + 1 ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have q1 : ∀ k, (n + 1) ^ k ≤ Y ^ k := fun k => Nat.pow_le_pow_left hnY k
  have q2 : ∀ i j, i ≤ j → Y ^ i ≤ Y ^ j := fun i j h => Nat.pow_le_pow_right hY1 h
  have r1 := q1 2
  have r2 := q1 3
  have r3 := q1 5
  have s12 := q2 1 2 (by omega)
  have s23 := q2 2 3 (by omega)
  have s34 := q2 3 4 (by omega)
  have s45 := q2 4 5 (by omega)
  have s56 := q2 5 6 (by omega)
  have y1 : Y ^ 1 = Y := pow_one Y
  have hU : (Val.list [encPerm x, encGroup gs]).wt + n + 1 = Y := hY.symm
  have wA0 := wt_list2_le (inputVal G H) (Val.list [encPerm x, encGroup gs])
  have hlg : (1 :: gs).length = gs.length + 1 := rfl
  -- the projections
  have hZ1 : (Val.list [.list [.nat n, (encFun fun i : Fin n => (i : ℕ))], (Val.list ((1 :: gs).map encPerm))]).wt + (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt + 1 ≤ 60 * Y ^ 3 := by
    have a1 := wt_list2_le (.list [.nat n, (encFun fun i : Fin n => (i : ℕ))]) (Val.list ((1 :: gs).map encPerm))
    have a2 := wt_list2_le (.nat n) (encFun fun i : Fin n => (i : ℕ))
    have := mul_pow_le (show gs.length + 1 ≤ 1 * Y ^ 1 by omega)
      (show 8 * (n + 1) ^ 2 + 1 ≤ 9 * Y ^ 2 by omega)
    simp only [one_mul, show 1 + 2 = 3 from rfl] at this
    omega
  have hPMc : (1 :: gs).length * (120000 * (n + 1) ^ 5) + mapK * ((1 :: gs).length + 1) *
      ((Val.list [.list [.nat n, (encFun fun i : Fin n => (i : ℕ))], (Val.list ((1 :: gs).map encPerm))]).wt + (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt + 1) ≤ 200000 * Y ^ 6 := by
    rw [mapK_mul, hlg]
    have m1 := mul_pow_le (show gs.length + 1 ≤ 1 * Y ^ 1 by omega)
      (show 120000 * (n + 1) ^ 5 ≤ 120000 * Y ^ 5 by omega)
    have m2 := mul_pow_le (show gs.length + 1 + 1 ≤ 1 * Y ^ 1 by omega) hZ1
    simp only [one_mul, show 1 + 5 = 6 from rfl, show 1 + 3 = 4 from rfl] at m1 m2
    omega
  -- the first cells
  have hAPc : loopModK * (n + 1) * ((Val.list [.list [.nat 1], (Val.list ((List.ofFn (proj x)).map .nat))]).wt + n +
      (Val.list ([.nat 1] ++ (List.ofFn (proj x)).map .nat)).wt + 1) ≤ 30000 * Y ^ 3 := by
    rw [loopModK_mul]
    have a1 := wt_list2_le (.list [.nat 1]) (Val.list ((List.ofFn (proj x)).map .nat))
    have a2 := wt_list1_le (.nat 1)
    have a3 := wt_nat_le 1
    have a4 : (Val.list ([.nat 1] ++ (List.ofFn (proj x)).map .nat)).wt ≤ (Val.list ((List.ofFn (proj x)).map .nat)).wt + 2 * 3 + 2 := by
      have := wt_list_cons_le (.nat 1) ((List.ofFn (proj x)).map .nat)
      simpa using this
    have := mul_pow_le (show n + 1 ≤ 1 * Y ^ 1 by omega)
      (show (Val.list [.list [.nat 1], (Val.list ((List.ofFn (proj x)).map .nat))]).wt + n +
        (Val.list ([.nat 1] ++ (List.ofFn (proj x)).map .nat)).wt + 1 ≤ 30 * Y ^ 2 by omega)
    simp only [one_mul, show 1 + 2 = 3 from rfl] at this
    omega
  -- the output
  have wOUT : (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt ≤ 30 * Y ^ 3 := by
    have m1 := mul_pow_le (show gs.length + 1 ≤ 1 * Y ^ 1 by omega)
      (show n ≤ 1 * Y ^ 1 by omega)
    simp only [one_mul, show 1 + 1 = 2 from rfl] at m1
    have m2 := mul_pow_le (show n + 2 + (gs.length + 1) * n ≤ 3 * Y ^ 2 by omega)
      (show 2 * (n + gs.length + 1) + 5 ≤ 7 * Y ^ 1 by omega)
    simp only [show 2 + 1 = 3 from rfl] at m2
    omega
  have hCc : (yesGens gs).length * (4000 * (n + 1) * (2 * (Val.list []).wt + 2 * (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt +
        3 * (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt + 20)) + loopModK * ((yesGens gs).length + 1) *
        ((Val.list [.list [], (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))), (Val.list ((yesPre x gs).map .nat))]).wt + (yesGens gs).length + (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt + 1) ≤
      2000000 * Y ^ 6 := by
    rw [loopModK_mul, length_yesGens]
    have whs' : (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt ≤ 10 * Y ^ 3 := by
      have := mul_pow_le (show gs.length + 1 ≤ 1 * Y ^ 1 by omega)
        (show 8 * (n + 1) ^ 2 + 1 ≤ 9 * Y ^ 2 by omega)
      simp only [one_mul, show 1 + 2 = 3 from rfl] at this
      omega
    have a1 := wt_list3_le (.list []) (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))) (Val.list ((yesPre x gs).map .nat))
    have m1 := mul_pow_le (show n + 1 ≤ 1 * Y ^ 1 by omega)
      (show 2 * (Val.list []).wt + 2 * (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt + 3 * (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt + 20 ≤ 130 * Y ^ 3 by
        simp only [wt_list_nil]; omega)
    simp only [one_mul, show 1 + 3 = 4 from rfl] at m1
    have m2 := mul_pow_le (show gs.length + 1 ≤ 1 * Y ^ 1 by omega)
      (show 4000 * (n + 1) * (2 * (Val.list []).wt + 2 * (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))).wt + 3 * (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt + 20) ≤
        520000 * Y ^ 4 by rw [Nat.mul_assoc]; omega)
    have m3 := mul_pow_le (show gs.length + 1 + 1 ≤ 1 * Y ^ 1 by omega)
      (show (Val.list [.list [], (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))), (Val.list ((yesPre x gs).map .nat))]).wt + (gs.length + 1) + (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt + 1 ≤ 200 * Y ^ 3 by
        simp only [wt_list_nil] at a1; omega)
    simp only [one_mul, show 1 + 4 = 5 from rfl, show 1 + 3 = 4 from rfl] at m2 m3
    omega
  have hids' : 8000 * (n + 1) ^ 3 ≤ 8000 * Y ^ 3 := by omega
  have hsig' : 100000 * (n + 1) ^ 5 ≤ 100000 * Y ^ 5 := by omega
  have wPRE := wpre
  have wI' : (inputVal G H).wt ≤ 30 * Y ^ 3 := by omega
  have b1 := wt_list2_le (.nat n) (encPerm x)
  have b2 := wt_list2_le (.list [.nat n, encPerm x]) (encFun fun i : Fin n => (i : ℕ))
  have b3 := wt_list2_le (.nat n) (encFun fun i : Fin n => (i : ℕ))
  have b4 := wt_list2_le (.list [.nat n, (encFun fun i : Fin n => (i : ℕ))]) (Val.list ((1 :: gs).map encPerm))
  have b5 := wt_list1_le (.nat 1)
  have b6 := wt_list2_le (.list [.nat 1]) (Val.list ((List.ofFn (proj x)).map .nat))
  have b7 := wt_list3_le (.list []) (Val.list ((yesGens gs).map fun l => Val.list (l.map .nat))) (Val.list ((yesPre x gs).map .nat))
  have b8 := wt_nat_le 1
  have b9 := wt_nat_le ((1 :: gs).map encPerm).length
  have b10 : ((1 :: gs).map encPerm).length = gs.length + 1 := by simp
  have b11 : (Val.list ((inputCells G H).map .nat)).wt = (inputVal G H).wt := rfl
  have b12 := wt_nat_le (n * n)
  have b13 : (Val.list [.nat (n * n), (Val.list ((1 :: gs).map encPerm))]).wt = (encGroup gs).wt := rfl
  have hwout : (Val.list ((yesPre x gs ++ (yesGens gs).flatten).map .nat)).wt ≤ 30 * Y ^ 3 := wOUT
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ Y ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
      _ ≤ Y ^ 4 := q1 4
  have wsig' : (Val.list ((List.ofFn (proj x)).map .nat)).wt ≤ 4 * Y ^ 2 := by omega
  have wids' : (encFun fun i : Fin n => (i : ℕ)).wt ≤ 4 * Y ^ 2 := by omega
  have wx' : (encPerm x).wt ≤ 4 * Y ^ 4 := by omega
  have a4 : (Val.list ([.nat 1] ++ (List.ofFn (proj x)).map .nat)).wt ≤
      (Val.list ((List.ofFn (proj x)).map .nat)).wt + 2 * 3 + 2 := by
    have := wt_list_cons_le (.nat 1) ((List.ofFn (proj x)).map .nat)
    simpa using this
  have wn' : (Val.nat n).wt ≤ 2 * Y := by omega
  have wnn : (Val.nat (n * n)).wt ≤ 2 * Y ^ 2 + 2 := by omega
  clear hids hsig hPM hAP hcat' hPMd hAPd d1 d2 d3 d4 d5 d6 d7 gx
  simp only [wt_list_nil] at *
  rw [convK]
  omega

/-! ### Correctness of the cells -/

theorem mem_range_of_gens {G : SimpleGraph (Fin n)} {gs : List (Perm (Fin (n * n)))}
    (h : gens gs = (GI.Statement.autGroup G).map (pairHom n)) :
    ∀ g ∈ 1 :: gs, g ∈ (pairHom n).range := by
  intro g hg
  have : g ∈ gens (1 :: gs) := Subgroup.subset_closure hg
  rw [gens_one_cons, h] at this
  obtain ⟨a, -, rfl⟩ := this
  exact ⟨a, rfl⟩

/-- The cells of a positive answer are `yesCells` of the isomorphism and the projected
generators. -/
theorem yesCells_eq {G H : SimpleGraph (Fin n)} {x : Perm (Fin (n * n))}
    {gs : List (Perm (Fin (n * n)))} {p : Perm (Fin n)} (hp : p ∈ isoSet G H)
    (hpx : pairHom n p = x) (h : gens gs = (GI.Statement.autGroup G).map (pairHom n)) :
    yesPre x gs ++ (yesGens gs).flatten = yesCells (isoOf hp).toEquiv ((1 :: gs).map unPair) := by
  have hr := mem_range_of_gens h
  have e1 : List.ofFn (proj x) = permCells p := by
    rw [permCells, ← hpx]
    congr 1
    funext i
    exact proj_pairHom p i
  have e2 : yesGens gs = ((1 :: gs).map unPair).map permCells := by
    rw [yesGens, List.map_map]
    refine List.map_congr_left fun g hg => ?_
    simp only [Function.comp_apply, permCells]
    congr 1
    funext i
    exact proj_eq_unPair (hr g hg) i
  rw [yesPre, yesCells, isoOf_toEquiv, permsCells, e1, e2]
  simp

/-! ### The converter -/

open Classical in
/-- **The converter.** On `[inputVal G H, u]`, where `u` is the value of the answer of the
pair state, the converter returns a correct answer at cost at most
`5 convK (wt u + n + 1)^6`. -/
theorem convert_spec {P : Program} {c : ℕ} (h : P.HasAt c (convFuns c)) (G H : SimpleGraph (Fin n))
    (u : Val) (hu : AnswerVal (pairEnum n) u (graphState G H).answer) :
    FunAll P c (.list [inputVal G H, u]) fun out cost =>
      AnswerOK G H out ∧ cost ≤ 5 * convK * (u.wt + n + 1) ^ 6 := by
  obtain ⟨hentry, -⟩ := convFuns_parts h
  have wI := wt_inputVal_le G H
  have wA := wt_list2_le (inputVal G H) u
  have hY1 : 1 ≤ (u.wt + n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q3 : (n + 1) ^ 3 ≤ (u.wt + n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have q36 : (u.wt + n + 1) ^ 3 ≤ (u.wt + n + 1) ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have q1 : u.wt + n + 1 ≤ (u.wt + n + 1) ^ 3 := by
    calc u.wt + n + 1 = (u.wt + n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hconv : 1000 * (u.wt + n + 1) ^ 6 ≤ convK * (u.wt + n + 1) ^ 6 :=
    Nat.mul_le_mul_right _ (by rw [convK]; omega)
  rw [show ∀ a b : ℕ, 5 * a * b = 5 * (a * b) from fun a b => Nat.mul_assoc 5 a b]
  rcases hu with ⟨rfl, hA⟩ | ⟨x, gs, rfl, hC⟩
  · -- no isomorphism
    have hc := Det.arith' (op := .eq) (Det.length (Det.arg' (P := P)
      (vs := [inputVal G H, .list []]) (rest := []) (j := 1) rfl)) (Det.nat 0)
      (show BinOp.eval .eq ([] : List Val).length 0 = 1 from rfl)
    have ht := Det.mk1 (P := P) (env := [Val.list [inputVal G H, .list []]]) (Det.nat 0)
    have hd := FunDet.intro hentry (Det.ite_pos hc one_ne_zero ht)
    refine FunAll.mono hd fun w cost hw => ⟨?_, hw.2.trans ?_⟩
    · rw [hw.1]
      exact answerOK_no (isEmpty_of_answer_empty G H hA)
    · have := wt_list1_le (Val.nat 0)
      have := wt_nat_le 0
      have := wt_nat_le 1
      simp only [List.length_nil] at *
      omega
  · -- an isomorphism: read the coset
    have hC' : pairHom n '' isoSet G H = x • (gens gs : Set (Perm (Fin (n * n)))) := by
      rw [← answer_image, hC]
    obtain ⟨p, hp, hpx⟩ := coset_rep hC'
    have hK := coset_group hC'
    have hc := Det.arith' (op := .eq) (Det.length (Det.arg' (P := P)
      (vs := [inputVal G H, .list [encPerm x, encGroup gs]]) (rest := []) (j := 1) rfl))
      (Det.nat 0) (show BinOp.eval .eq [encPerm x, encGroup gs].length 0 = 0 from rfl)
    have hy := yes_spec h G H x gs
    have hw := hy.wt_lt
    have he := Det.call (Det.var' (P := P)
      (env := [Val.list [inputVal G H, .list [encPerm x, encGroup gs]]]) (i := 0) rfl) hy
    have hd := FunDet.intro hentry (Det.ite_zero hc he)
    refine FunAll.mono hd fun w cost hw' => ⟨?_, hw'.2.trans ?_⟩
    · rw [hw'.1, yesCells_eq hp hpx hK]
      exact answerOK_yes _ _ (closure_unPair hK)
    · have := wt_nat_le 0
      simp only [List.length_cons, List.length_nil] at *
      omega

/-- **`ConvertSpec`** for every program that holds the converter at `c`. -/
theorem convertSpec_of_hasAt {P : Program} {c : ℕ} (h : P.HasAt c (convFuns c)) :
    ConvertSpec P c :=
  ⟨5 * convK, 6, fun _ G H u hu => convert_spec h G H u hu⟩

end GI.Assembly
