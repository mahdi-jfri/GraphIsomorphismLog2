import Workspace.Impl.RowA18Link
import Workspace.Lang.Lib.Orbit

/-!
# The case choice of the row step, in `GI.Lang`

The row step splits on whether `N` is transitive on the row `B` (Algorithm 4: "if `L` is
transitive on a row"). Given generators `σs` of `N` (`Nb_gens`), the program computes the orbit
labels of `⟨σs⟩` (`orbitFuns`, the least point of each orbit) and their maximum. The maximum is
`0` exactly when every point lies in the orbit of every other point (`trans_iff_max`), which is
transitivity of `N` (`transitive_iff`). No cited task.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms)

variable {m : ℕ}

theorem foldl_max_bounds (l : List ℕ) (a : ℕ) :
    a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max a y)
    refine ⟨le_trans (le_max_left a y) h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

theorem le_foldl_max_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) {a : ℕ} : x ≤ l.foldl max a :=
  (foldl_max_bounds l a).2 x hx

/-- **The maximal orbit label is `0`** exactly when the generated group is transitive. -/
theorem trans_iff_max (σs : List (Perm (Fin m))) :
    ((List.finRange m).map (orbitLabels σs)).foldl max 0 = 0 ↔
      ∀ x y : Fin m, y ∈ genOrbit σs x := by
  obtain ⟨hsame, hleast⟩ := orbitLabels_spec σs
  have hzero : ((List.finRange m).map (orbitLabels σs)).foldl max 0 = 0 ↔
      ∀ x, orbitLabels σs x = 0 := by
    constructor
    · intro h x
      have hmem : orbitLabels σs x ∈ (List.finRange m).map (orbitLabels σs) :=
        List.mem_map_of_mem (List.mem_finRange x)
      have hle : orbitLabels σs x ≤ ((List.finRange m).map (orbitLabels σs)).foldl max 0 :=
        le_foldl_max_of_mem hmem
      omega
    · intro h
      apply Nat.le_zero.1
      exact foldl_max_le le_rfl fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        rw [h y]
  rw [hzero]
  constructor
  · intro h x y
    exact (hsame x y).1 (by rw [h x, h y])
  · intro h x
    obtain ⟨hlt, -, hmin⟩ := hleast x
    exact Nat.le_zero.1 (hmin ⟨0, by omega⟩ (h x _))

/-- On `encPerms σs`: the maximal orbit label (`max` at `b + 1`, `orbitFuns` at `b + 6`). -/
def transF (b : ℕ) : Expr := .call (b + 1) (.call (b + 6) (.var 0))

/-- The test module at `b` (38 functions). -/
def transFuns (b : ℕ) : List Expr := [transF b] ++ maxFuns (b + 1) ++ orbitFuns (b + 6)

/-- The cost constant of the test. -/
def transK : ℕ := 10 ^ 7

/-- **The transitivity test.** The answer is `0` exactly when `⟨σs⟩` is transitive. -/
theorem trans_spec {P : Program} {b : ℕ} (h : P.HasAt b (transFuns b))
    (σs : List (Perm (Fin m))) :
    FunAll P b (encPerms σs) (fun w c => ∃ t : ℕ, w = .nat t ∧
      (t = 0 ↔ ∀ x y : Fin m, y ∈ genOrbit σs x) ∧ t ≤ m ∧ c ≤ transK * ((σs.length + 1) * (m + 1)) ^ 5) := by
  have hentry : P.funs[b]? = some (transF b) := by
    simpa using (h.block 0 (gs := [transF b]) (by rfl)).single
  have hmax : P.HasAt (b + 1) (maxFuns (b + 1)) := h.block 1 (by rfl)
  have horb : P.HasAt (b + 6) (orbitFuns (b + 6)) := h.block 6 (by rfl)
  have d1 := Det.call (Det.var' (P := P) (env := [encPerms σs]) (i := 0) rfl) (orbitFuns_spec horb σs)
  rw [encFun_eq_natList] at d1
  have hB : ∀ x ∈ (List.finRange m).map (orbitLabels σs), x ≤ m := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact ((orbitLabels_spec σs).2 y).1.le
  have d2 := Det.call d1 (max_spec hmax hB (by simp))
  refine FunAll.intro hentry (d2.post fun c hc => ⟨_, rfl, trans_iff_max σs,
    foldl_max_le (Nat.zero_le _) hB, ?_⟩)
  -- the cost
  clear d2 d1 hentry hmax horb h
  have hX1 : m + 1 ≤ (σs.length + 1) * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h1 := wt_list_encPerms_le σs
  obtain ⟨X, hX⟩ : ∃ X, (σs.length + 1) * (m + 1) = X := ⟨_, rfl⟩
  rw [hX] at hX1 h1 hc ⊢
  have hX2 : 1 ≤ X := by omega
  have w1 : (encPerms σs).wt ≤ 40 * X ^ 2 := by
    have h2 := wt_list2_le (.nat m) (.list (σs.map encPerm))
    have h3 := wt_nat_le m
    have : (encPerms σs).wt = (Val.list [.nat m, .list (σs.map encPerm)]).wt := rfl
    have h4 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
    omega
  have w2 : (natList ((List.finRange m).map (orbitLabels σs))).wt ≤ 5 * (m + 1) ^ 2 :=
    wt_natList_le_sq hB (by simp)
  have hmax' : ((List.finRange m).map (orbitLabels σs)).foldl max 0 ≤ m :=
    foldl_max_le (Nat.zero_le _) hB
  have w3 := wt_nat_le (((List.finRange m).map (orbitLabels σs)).foldl max 0)
  have p2 : (m + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hX1 2
  have p3 : (m + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hX1 3
  have m25 : X ^ 2 ≤ X ^ 5 := Nat.pow_le_pow_right hX2 (by omega)
  have m35 : X ^ 3 ≤ X ^ 5 := Nat.pow_le_pow_right hX2 (by omega)
  have m15 : X ≤ X ^ 5 := Nat.le_self_pow (by norm_num) X
  have e1 : orbitK = 1000000 := rfl
  have e2 : maxK = 100000 := rfl
  have e3 : transK = 10000000 := rfl
  simp only [e1, e2] at hc
  rw [e3]
  linarith

end GI.Impl
