/-
Permutations of `Fin n` in the format `GI.Cited.encPerm`, and functions `Fin n → ℕ` in the same
format (`encFun`): the list of the values at `0, …, n - 1`.

* Applying a permutation is indexing (`Det.applyPerm`).
* `composeFuns`: on `[encPerm σ, encPerm τ]`, the value `encPerm (σ * τ)`.
* `rangeFuns` on `n` gives `encPerm 1` (`range_eq_encPerm_one`).
* `invFuns`: on `encPerm σ`, the value `encPerm σ⁻¹`.

Each operation costs at most `permK * (n + 1) ^ 3`.
-/
module

public import Workspace.Lang.Lib.Fold
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)

variable {n : ℕ}

/-! ### Functions on `Fin n` as values -/

/-- A function `Fin n → ℕ`, as the list of its values. -/
def encFun (f : Fin n → ℕ) : Val := .list ((List.finRange n).map fun i => .nat (f i))

theorem encPerm_eq_encFun (σ : Equiv.Perm (Fin n)) : encPerm σ = encFun fun i => (σ i : ℕ) := rfl

theorem encFun_getElem? (f : Fin n → ℕ) (i : Fin n) :
    ((List.finRange n).map fun i => Val.nat (f i))[(i : ℕ)]? = some (.nat (f i)) := by
  simp

theorem wt_encFun_le (f : Fin n → ℕ) {B : ℕ} (hf : ∀ i, f i ≤ B) :
    (encFun f).wt ≤ n * (2 * B + 5) + 4 := by
  have h1 := wt_list_le ((List.finRange n).map fun i => Val.nat (f i))
  have h2 : (((List.finRange n).map fun i => Val.nat (f i)).map Val.wt).sum ≤ n * (B + 2) := by
    have := List.sum_le_card_nsmul (((List.finRange n).map fun i => Val.nat (f i)).map Val.wt)
      (B + 2) (by
        simp only [List.map_map, List.mem_map, List.mem_finRange, true_and, Function.comp_apply,
          forall_exists_index, forall_apply_eq_imp_iff]
        intro i; have := wt_nat_le (f i); have := hf i; omega)
    simpa using this
  simp only [List.length_map, List.length_finRange] at h1
  rw [encFun]
  nlinarith

theorem wt_encPerm_le (σ : Equiv.Perm (Fin n)) : (encPerm σ).wt ≤ 4 * (n + 1) ^ 2 := by
  have := wt_encFun_le (fun i => (σ i : ℕ)) (B := n) fun i => (σ i).isLt.le
  rw [encPerm_eq_encFun]
  nlinarith

/-- Applying a permutation to a point: indexing. -/
theorem Det.applyPerm {P : Program} {env : List Val} {e ei : Expr} {σ : Equiv.Perm (Fin n)}
    {i : Fin n} {ca cb : ℕ} (he : Det P env e (encPerm σ) ca) (hi : Det P env ei (.nat i) cb) :
    Det P env (.get e ei) (.nat (σ i)) (ca + cb + (Val.nat (σ i)).wt + 1) :=
  Det.get' he hi (encFun_getElem? (fun i => (σ i : ℕ)) i)

/-! ### Identity -/

theorem range_eq_encPerm_one : natList (List.range n) = encPerm (1 : Equiv.Perm (Fin n)) := by
  simp only [natList, encPerm, Equiv.Perm.coe_one, id]
  congr 1
  apply List.ext_getElem <;> simp

/-! ### Composition -/

/-- The cost constant of the permutation operations. -/
def permK : ℕ := 30000

/-- The function of `compose`: on `[c, x]`, entry `x` of `c`. -/
def composeF : Expr := .get (arg 0) (arg 1)

/-- `compose`, at base `b` (four functions): on `[encPerm σ, encPerm τ]`, `encPerm (σ * τ)`. -/
def composeFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [composeF]

/-- **Composition.** -/
theorem compose_spec {P : Program} {b : ℕ} (h : P.HasAt b (composeFuns b))
    (σ τ : Equiv.Perm (Fin n)) :
    FunDet P b (.list [encPerm σ, encPerm τ]) (encPerm (σ * τ)) (permK * (n + 1) ^ 3) := by
  have hE := wt_encPerm_le σ
  have hE' := wt_encPerm_le τ
  have hf : ∀ x ∈ (List.finRange n).map (fun i => Val.nat (τ i)),
      FunAll P (b + 3) (.list [encPerm σ, x]) (fun w cost =>
        (∀ i : Fin n, x = .nat i → w = .nat (σ i)) ∧ cost ≤ 100 * (n + 1) ^ 2) := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    have hb : P.funs[b + 3]? = some composeF := by
      simpa [composeFuns, mapFuns, loopFuns] using h.right.single
    refine FunAll.intro hb ((Det.applyPerm (Det.arg' (rest := []) (j := 0) rfl)
      (Det.arg' (j := 1) rfl)).post fun cost hc => ⟨fun i hi => ?_, ?_⟩)
    · simp only [Val.nat.injEq] at hi
      rw [Fin.ext hi]
    · have h1 := wt_list2_le (encPerm σ) (.nat (τ j))
      have h2 := wt_nat_le (τ j)
      have h3 := wt_nat_le (σ (τ j))
      have h4 := (τ j).isLt
      have h5 := (σ (τ j)).isLt
      nlinarith
  refine ((map_spec h.left hf).mono fun w cost hw => ?_)
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' := forall₂_map_eq (g := fun i => Val.nat ((σ * τ) i))
    (fun a _ w hw => by rw [hw (τ a) rfl]; rfl) hws
  subst hws'
  refine ⟨rfl, ?_⟩
  have hw := wt_encPerm_le (σ * τ)
  have ha := wt_list2_le (encPerm σ) (encPerm τ)
  simp only [List.map_map, List.length_map, List.length_finRange] at hc
  have hs : ((List.finRange n).map ((fun _ => 100 * (n + 1) ^ 2) ∘
      fun i => Val.nat (τ i))).sum = n * (100 * (n + 1) ^ 2) := by
    rw [show ((fun _ => 100 * (n + 1) ^ 2) ∘ fun i : Fin n => Val.nat (τ i)) =
      fun _ => 100 * (n + 1) ^ 2 from rfl, List.map_const', List.sum_replicate,
      List.length_finRange, smul_eq_mul]
  have e1 : (Val.list [encPerm σ, Val.list ((List.finRange n).map fun i => Val.nat (τ i))]).wt =
    (Val.list [encPerm σ, encPerm τ]).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun i => Val.nat ((σ * τ) i))).wt =
    (encPerm (σ * τ)).wt := rfl
  rw [hs, e1, e2] at hc
  have h1 : mapK * (n + 1) * ((Val.list [encPerm σ, encPerm τ]).wt + (encPerm (σ * τ)).wt + 1) ≤
      mapK * (n + 1) * (27 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h2 : n * (100 * (n + 1) ^ 2) ≤ 100 * (n + 1) ^ 3 := by nlinarith
  have h3 : mapK * (n + 1) * (27 * (n + 1) ^ 2) = 27000 * (n + 1) ^ 3 := by
    simp only [mapK]; ring
  simp only [permK]
  omega

end GI.Lang

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)

variable {n : ℕ}

/-! ### Inverse -/

/-- The test "is the number `j`". -/
def natEq (j : ℕ) : Val → Bool
  | .nat y => y == j
  | .list _ => false

theorem findIdx_perm (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    ((List.finRange n).map (fun i => Val.nat (σ i))).findIdx (natEq j) = σ⁻¹ j := by
  rw [List.findIdx_eq (by simp)]
  simp only [List.getElem_map, List.getElem_finRange, natEq]
  refine ⟨by simp, fun k hk => ?_⟩
  simp only [beq_eq_false_iff_ne]
  intro h
  have : σ⁻¹ j = ⟨k, by omega⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact (Fin.ext (by simpa using h)).symm
  rw [this] at hk; simp at hk

/-- The test of `inverse`: on `[j, x]`, whether `x` is the number `j`. -/
def eqTestF : Expr := .arith .eq (arg 1) (arg 0)

/-- The function of the outer map of `inverse`: on `[c, j]`, find `j` in `c`. -/
def invF (find : ℕ) : Expr := .call find (mk2 (arg 1) (arg 0))

/-- The entry of `inverse`. -/
def invEntry (b : ℕ) : Expr := .call (b + 1) (mk2 (.var 0) (.call (b + 5) (.length (.var 0))))

/-- `inverse`, at base `b` (twelve functions): on `encPerm σ`, the value `encPerm σ⁻¹`. -/
def invFuns (b : ℕ) : List Expr :=
  [invEntry b] ++ mapFuns (b + 1) (b + 4) ++ [invF (b + 8)] ++ rangeFuns (b + 5) ++
    findFuns (b + 8) (b + 11) ++ [eqTestF]

/-- The cost constant of `inverse`. -/
def invK : ℕ := 100000

theorem wt_list2_encPerm_le (σ : Equiv.Perm (Fin n)) (j : ℕ) (hj : j ≤ n) :
    (Val.list [.nat j, encPerm σ]).wt ≤ 20 * (n + 1) ^ 2 ∧
      (Val.list [encPerm σ, .nat j]).wt ≤ 20 * (n + 1) ^ 2 := by
  have h1 := wt_list2_le (.nat j) (encPerm σ)
  have h2 := wt_list2_le (encPerm σ) (.nat j)
  have h3 := wt_nat_le j
  have h4 := wt_encPerm_le σ
  constructor <;> nlinarith

/-- **Inverse.** -/
theorem inv_spec {P : Program} {b : ℕ} (h : P.HasAt b (invFuns b)) (σ : Equiv.Perm (Fin n)) :
    FunDet P b (encPerm σ) (encPerm σ⁻¹) (invK * (n + 1) ^ 4) := by
  simp only [invFuns] at h
  have hE := wt_encPerm_le σ
  have hEi := wt_encPerm_le σ⁻¹
  have hentry : P.funs[b]? = some (invEntry b) := h.left.left.left.left.left.single
  have hmap : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := by
    simpa using h.left.left.left.left.right
  have hinvF : P.funs[b + 4]? = some (invF (b + 8)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.left.left.right.single
  have hrange : P.HasAt (b + 5) (rangeFuns (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.left.right
  have hfind : P.HasAt (b + 8) (findFuns (b + 8) (b + 11)) := by
    simpa [mapFuns, loopFuns, rangeFuns, Nat.add_assoc] using h.left.right
  have htest : P.funs[b + 11]? = some eqTestF := by
    simpa [mapFuns, loopFuns, rangeFuns, findFuns, Nat.add_assoc] using h.right.single
  -- the test
  have hT : ∀ (j : Fin n), ∀ x ∈ (List.finRange n).map (fun i => Val.nat (σ i)),
      FunDet P (b + 11) (.list [.nat j, x]) (boolVal (natEq j x)) (50 * (n + 1)) := by
    intro j x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    refine FunDet.intro htest ((Det.arith' (Det.arg' (rest := []) (j := 1) rfl)
      (Det.arg' (j := 0) rfl) (z := (natEq j (.nat (σ i))).toNat) ?_).mono ?_)
    · simp only [BinOp.eval, natEq]
      by_cases hij : (σ i : ℕ) = j
      · simp [hij]
      · rw [show ((σ i : ℕ) == j) = false from beq_eq_false_iff_ne.mpr hij]; simpa using hij
    · have := wt_list2_le (.nat j) (.nat (σ i))
      have := wt_nat_le j
      have := wt_nat_le (σ i)
      have := (σ i).isLt
      have := j.isLt
      have : (natEq j (.nat (σ i))).toNat ≤ 1 := Bool.toNat_le _
      nlinarith
  -- the find
  have hF : ∀ j : Fin n, FunDet P (b + 8)
      (.list [.nat j, .list ((List.finRange n).map fun i => Val.nat (σ i))])
      (.nat (σ⁻¹ j)) (26000 * (n + 1) ^ 3) := by
    intro j
    refine (find_spec hfind (hT j)).mono fun w cost hw => ⟨by rw [hw.1, findIdx_perm], ?_⟩
    have hc := hw.2
    simp only [List.map_map, List.length_map, List.length_finRange] at hc
    have hs : ((List.finRange n).map ((fun _ => 50 * (n + 1)) ∘ fun i => Val.nat (σ i))).sum =
        n * (50 * (n + 1)) := by
      rw [show ((fun _ => 50 * (n + 1)) ∘ fun i : Fin n => Val.nat (σ i)) =
        fun _ => 50 * (n + 1) from rfl, List.map_const', List.sum_replicate,
        List.length_finRange, smul_eq_mul]
    rw [hs] at hc
    have ha := (wt_list2_encPerm_le σ j j.isLt.le).1
    have e1 : (Val.list [.nat j, .list ((List.finRange n).map fun i => Val.nat (σ i))]).wt =
      (Val.list [.nat j, encPerm σ]).wt := rfl
    rw [e1] at hc
    have h1 : loopModK * (n + 1) * ((Val.list [.nat j, encPerm σ]).wt + 2 * n + 3) ≤
        loopModK * (n + 1) * (25 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    have h2 : loopModK * (n + 1) * (25 * (n + 1) ^ 2) = 25000 * (n + 1) ^ 3 := by
      simp only [loopModK]; ring
    have h3 : n * (50 * (n + 1)) ≤ 1000 * (n + 1) ^ 3 := by nlinarith
    omega
  -- the function of the outer map
  have hG : ∀ x ∈ (List.range n).map Val.nat,
      FunAll P (b + 4) (.list [encPerm σ, x]) (fun w cost =>
        (∀ j : Fin n, x = .nat j → w = .nat (σ⁻¹ j)) ∧ cost ≤ 27000 * (n + 1) ^ 3) := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    refine FunAll.intro hinvF ((Det.call (Det.mk2 (Det.arg' (rest := []) (j := 1) rfl)
      (Det.arg' (j := 0) rfl)) (hF ⟨j, hj⟩)).post fun cost hc => ⟨fun j' hj' => ?_, ?_⟩)
    · simp only [Val.nat.injEq] at hj'
      have : j' = ⟨j, hj⟩ := Fin.ext hj'.symm
      rw [this]
    · obtain ⟨h1, h2⟩ := wt_list2_encPerm_le σ j hj.le
      have h3 := wt_nat_le (σ⁻¹ ⟨j, hj⟩)
      have h4 := (σ⁻¹ ⟨j, hj⟩).isLt
      have h5 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have h6 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
      have e : (Val.list [Val.nat j, Val.list ((List.finRange n).map fun i => Val.nat (σ i))]).wt =
        (Val.list [Val.nat j, encPerm σ]).wt := rfl
      rw [e] at hc
      linarith
  -- the range
  have hR : FunDet P (b + 5) (.nat n) (natList (List.range n)) (7000 * (n + 1) ^ 3) := by
    refine (range_spec hrange n).mono fun w cost hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hw.1, range_eq_encPerm_one] at hc
    have h1 := wt_encPerm_le (1 : Equiv.Perm (Fin n))
    have h2 := wt_nat_le n
    have h3 : loopModK * (n + 1) * ((Val.nat n).wt + n + (encPerm (1 : Equiv.Perm (Fin n))).wt + 1)
        ≤ loopModK * (n + 1) * (7 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    have h4 : loopModK * (n + 1) * (7 * (n + 1) ^ 2) = 7000 * (n + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega
  -- the outer map
  have hM := map_spec hmap hG
  have hlen := Det.length (P := P) (Det.var' (env := [encPerm σ]) (i := 0) rfl)
  simp only [encPerm, List.length_map, List.length_finRange] at hlen
  refine FunDet.intro hentry ((EvalAll.call_funAll (Det.mk2 (Det.var' (i := 0) rfl)
    (Det.call hlen hR)) fun v ca hv => ?_))
  obtain ⟨rfl, hca⟩ := hv
  refine hM.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hxs : (List.range n).map Val.nat = (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl
  rw [hxs] at hws hc
  have hws' : ws = (List.finRange n).map fun i => Val.nat (σ⁻¹ i) :=
    forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map, List.length_finRange] at hc
  have hs : ((List.finRange n).map ((fun _ => 27000 * (n + 1) ^ 3) ∘ fun i : Fin n => Val.nat (i : ℕ))).sum =
      n * (27000 * (n + 1) ^ 3) := by
    rw [show ((fun _ => 27000 * (n + 1) ^ 3) ∘ fun i : Fin n => Val.nat (i : ℕ)) =
      fun _ => 27000 * (n + 1) ^ 3 from rfl, List.map_const', List.sum_replicate,
      List.length_finRange, smul_eq_mul]
  rw [hs] at hc
  have e1 : (Val.list [encPerm σ, .list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))]).wt =
    (Val.list [encPerm σ, encPerm (1 : Equiv.Perm (Fin n))]).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun i => Val.nat (σ⁻¹ i))).wt =
    (encPerm σ⁻¹).wt := rfl
  rw [e1, e2] at hc
  have h1 := wt_encPerm_le (1 : Equiv.Perm (Fin n))
  have h2 := wt_list2_le (encPerm σ) (encPerm (1 : Equiv.Perm (Fin n)))
  have h3 : mapK * (n + 1) * ((Val.list [encPerm σ, encPerm (1 : Equiv.Perm (Fin n))]).wt +
      (encPerm σ⁻¹).wt + 1) ≤ mapK * (n + 1) * (27 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h4 : mapK * (n + 1) * (27 * (n + 1) ^ 2) = 27000 * (n + 1) ^ 3 := by
    simp only [mapK]; ring
  have h5 : n * (27000 * (n + 1) ^ 3) ≤ 27000 * (n + 1) ^ 4 := by
    have : n * (n + 1) ^ 3 ≤ (n + 1) ^ 4 := by
      rw [pow_succ (n + 1) 3, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have h6 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h7 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h8 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h9 := wt_list2_le (encPerm σ) (natList (List.range n))
  have h10 : (natList (List.range n)).wt = (encPerm (1 : Equiv.Perm (Fin n))).wt := by
    rw [range_eq_encPerm_one]
  have h11 : (encPerm σ).wt = (Val.list ((List.finRange n).map fun i => Val.nat (σ i))).wt := rfl
  simp only [invK]
  linarith

/-! ### Lists of permutations in the format `encPerms` -/

/-- Reading `n` from `encPerms gs = [n, gens]`. -/
theorem Det.encPerms_size {P : Program} {env : List Val} {e : Expr} {gs : List (Equiv.Perm (Fin n))}
    {c : ℕ} (he : Det P env e (encPerms gs) c) :
    Det P env (.get e (.nat 0)) (.nat n) (c + 3 + (Val.nat n).wt + 1) :=
  Det.get' he (Det.nat 0) rfl

/-- Reading the list of generators from `encPerms gs`. -/
theorem Det.encPerms_gens {P : Program} {env : List Val} {e : Expr}
    {gs : List (Equiv.Perm (Fin n))} {c : ℕ} (he : Det P env e (encPerms gs) c) :
    Det P env (.get e (.nat 1)) (.list (gs.map encPerm))
      (c + 4 + (Val.list (gs.map encPerm)).wt + 1) :=
  Det.get' he (Det.nat 1) rfl

/-- Reading generator `t` from the list of generators. -/
theorem Det.getPerm {P : Program} {env : List Val} {e et : Expr}
    {gs : List (Equiv.Perm (Fin n))} {t : ℕ} (ht : t < gs.length) {ca cb : ℕ}
    (he : Det P env e (.list (gs.map encPerm)) ca) (hi : Det P env et (.nat t) cb) :
    Det P env (.get e et) (encPerm gs[t]) (ca + cb + (encPerm gs[t]).wt + 1) :=
  Det.get' he hi (by simp [ht])

end GI.Lang
