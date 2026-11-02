import Workspace.Impl.AggTup

/-!
# The orbit of a test tuple, on a list of label pairs

`graphTupFuns` works on the format of the other graph-form modules: a list of label pairs
`[a, b]`. It encodes the pairs as permutations `a ⊕ b` of `Fin (k + q)` (`pEncMap_spec`) and
runs the orbit program on lists of points (`tupOrb_spec`). `graphTup_spec` states the result for
any start tuple; `imgOrd_spec` reads off the order of `φ_T(A)` as the length of the orbit of the
label points of `T` (`ncard_tupOrbit`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {k q : ℕ}

/-- On `[[k, q], pairs, x₀, B]`: encode the pairs, then run the orbit program. -/
def graphTupEntry (b : ℕ) : Expr :=
  let kE := Expr.get (arg 0) (.nat 0)
  let qE := Expr.get (arg 0) (.nat 1)
  .letE (.call (b + 1) (mk2 kE (arg 1)))
    (.call (b + 14) (.snoc (mk4 (.nat 0) (.var 1) (arg 2) (arg 3)) (.arith .add kE qE)))

/-- The module at base `b` (37 functions). -/
def graphTupFuns (b : ℕ) : List Expr :=
  [graphTupEntry b] ++ pEncMapFuns (b + 1) ++ tupOrbFuns (b + 14)

/-- The cost constant of the module. -/
def graphTupK : ℕ := 10 ^ 10

/-- The size parameter of the module. -/
def tupM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) (B l : ℕ) : ℕ :=
  k + q + ps.length + B + l + 20

/-- **The orbit of a tuple of points under the encoded pairs.** -/
theorem graphTup_spec {P : Program} {b : ℕ} (hb : P.HasAt b (graphTupFuns b))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (x₀ : List (Fin (k + q))) {B : ℕ}
    (hB : (actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair) x₀).ncard
      ≤ B) :
    FunAll P b (.list [.list [.nat k, .nat q], .list (ps.map pairV), natList (ptsKey x₀), .nat B])
      (fun w c => ∃ L : List (List (Fin (k + q)) × Perm (Fin (k + q))), w = encPairs ptsKey L ∧
        (L.map Prod.fst).Nodup ∧
        (∀ y, y ∈ L.map Prod.fst ↔
          y ∈ actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair) x₀) ∧
        (∀ p ∈ L, p.2 ∈ gens (ps.map encPair) ∧ x₀.map p.2 = p.1) ∧
        c ≤ graphTupK * tupM k q ps B x₀.length ^ 12) := by
  have hentry : P.funs[b]? = some (graphTupEntry b) := by
    simpa using (hb.block 0 (gs := [graphTupEntry b]) (by rfl)).single
  have hen : P.HasAt (b + 1) (pEncMapFuns (b + 1)) := hb.block 1 (by rfl)
  have hto : P.HasAt (b + 14) (tupOrbFuns (b + 14)) := hb.block 14 (by rfl)
  set A : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV), natList (ptsKey x₀), .nat B]
    with hA
  set E : Val := .list (ps.map fun p => encPerm (encPair p)) with hE
  have gk : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 0)) (.nat k) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      natList (ptsKey x₀), .nat B]) (rest := rest) (j := 0) rfl) (Det.nat 0) (v := .nat k) rfl
  have gq : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 1)) (.nat q) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      natList (ptsKey x₀), .nat B]) (rest := rest) (j := 0) rfl) (Det.nat 1) (v := .nat q) rfl
  have d1 := Det.call (Det.mk2 (gk []) (Det.arg' (P := P) (vs := [.list [.nat k, .nat q],
    .list (ps.map pairV), natList (ptsKey x₀), .nat B]) (rest := []) (j := 1) rfl))
    (pEncMap_spec hen ps)
  have dI := Det.snoc (Det.mk4 (Det.nat (P := P) (env := [A, E]) 0)
    (Det.var' (P := P) (env := [A, E]) (i := 1) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), natList (ptsKey x₀),
      .nat B]) (rest := [E]) (j := 2) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), natList (ptsKey x₀),
      .nat B]) (rest := [E]) (j := 3) rfl))
    (Det.arith' (op := .add) (gk [E]) (gq [E]) (z := k + q) rfl)
  have eE : E = .list ((ps.map encPair).map encPerm) := by simp [hE, List.map_map]
  have hT := tupOrb_spec hto (ps.map encPair) x₀ hB
  rw [← eE] at hT
  refine FunAll.intro hentry (EvalAll.letE d1 fun _ _ h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.call_funAll dI fun _ _ h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine hT.wt_lt.mono fun w c hw => ?_
  obtain ⟨⟨L, rfl, h1, h2, h3, -, h5⟩, hwc⟩ := hw
  refine ⟨L, rfl, h1, h2, h3, ?_⟩
  -- the cost
  set M := tupM k q ps B x₀.length with hM
  have hMd : k + q + ps.length + B + x₀.length + 20 = M := rfl
  have hM1 : 1 ≤ M := by omega
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b hab => Nat.pow_le_pow_right hM1 hab
  have pl : ∀ x n, x ≤ M → x ^ n ≤ M ^ n := fun x n hx => Nat.pow_le_pow_left hx n
  have bps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
    have := wt_pairList_le ps
    have h3 := pl (pM k q ps) 3 (by unfold pM; omega)
    omega
  have bX : (natList (ptsKey x₀)).wt ≤ 3 * M ^ 2 + 4 := by
    have := wt_ptsKey_le x₀
    have : x₀.length * (2 * (k + q) + 5) ≤ M * (3 * M) := Nat.mul_le_mul (by omega) (by omega)
    have e : M * (3 * M) = 3 * M ^ 2 := by ring
    omega
  have bkq := wt_list2_le (.nat k) (.nat q)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wkq := wt_nat_le (k + q)
  have wB := wt_nat_le B
  have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have bA := wt_list4_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (natList (ptsKey x₀))
    (.nat B)
  have bA1 := wt_list2_le (.nat k) (.list (ps.map pairV))
  have bE : E.wt ≤ 9 * M ^ 3 + 4 := by
    have h1 := wt_list_map_le ps (fun p => encPerm (encPair p))
      (W := 4 * (k + q + 1) ^ 2) fun p _ => wt_encPerm_le _
    have h2 : ps.length * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
      Nat.mul_le_mul (by omega) (by
        have := pl (k + q + 1) 2 (by omega); have := Nat.one_le_pow 2 M hM1; omega)
    have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
    rw [hE]; omega
  have b4 := wt_list4_le (.nat 0) E (natList (ptsKey x₀)) (.nat B)
  have b5 := wt_list_snoc_le [.nat 0, E, natList (ptsKey x₀), .nat B] (.nat (k + q))
  have cE : ps.length * pEncCost k q ≤ natStepK * M ^ 4 := by
    have h2 : ps.length * pEncCost k q ≤ M * (natStepK * M ^ 3) :=
      Nat.mul_le_mul (by omega) (by
        show natStepK * (k + q + 1) ^ 3 ≤ _; exact Nat.mul_le_mul_left _ (pl _ 3 (by omega)))
    have e2 : M * (natStepK * M ^ 3) = natStepK * M ^ 4 := by ring
    omega
  have m3a : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
  have m3b := Nat.one_le_pow 3 M hM1
  have cE2 : mapK * (ps.length + 1) * ((Val.list [.nat k, .list (ps.map pairV)]).wt + E.wt + 1)
      ≤ mapK * M * (1000 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : mapK * M * (1000 * M ^ 3) = 10 ^ 6 * M ^ 4 := by simp only [mapK]; ring
  have hlen : (ps.map encPair).length = ps.length := List.length_map _
  have cT : tupK * ((ps.map encPair).length + (k + q) + B + x₀.length + 20) ^ 12 ≤
      tupK * M ^ 12 := Nat.mul_le_mul_left _ (pl _ 12 (by omega))
  have m4 : M ^ 3 ≤ M ^ 12 := pw 3 12 (by omega)
  have m5 : M ^ 4 ≤ M ^ 12 := pw 4 12 (by omega)
  have m2 : M ^ 2 ≤ M ^ 12 := pw 2 12 (by omega)
  have m1 : M ≤ M ^ 12 := (Nat.le_self_pow (by norm_num) M).trans (pw 1 12 (by omega))
  rw [← hE] at hc1
  clear d1 dI hT
  simp only [graphTupK, tupK, natStepK] at *
  omega

end GI.Impl
