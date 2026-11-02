import Workspace.Impl.SCosBase2

/-!
# The base case, the transversal and the search

Step 5 of `scosBaseF`: the Schreier transversal of `n + α` under the generators of `gv`
(`schreier_spec`). Step 6: the index of the pair whose point is `τ` (`find_spec` with the test
function 11). The costs are bounded by `S = 10¹⁶ M⁶` and `10⁵ S²`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The environment after step 4. -/
noncomputable abbrev scosBaseE4 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n) :
    List Val :=
  [scosBaseV gs x a, .nat a, .nat n, .nat (n + a), .nat (scosBaseTau x a)]

/-- The length of `xv`. -/
theorem scosBase_len (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n)
    (rest : List Val) :
    Det (𝒫) (scosBaseV gs x a :: rest) (.length (arg 1)) (.nat (n + n))
      (2 * (scosBaseV gs x a).wt + n + n + 9) := by
  have d1 : Det (𝒫) (scosBaseV gs x a :: rest) (arg 1)
      (.list ((List.finRange (n + n)).map fun i => Val.nat (nintSum x i))) _ :=
    Det.arg' (vs := [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))])
      (rest := rest) (j := 1) rfl
  have d := Det.length d1
  simp only [List.length_map, List.length_finRange] at d
  have e : (scosBaseV gs x a).wt = (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt := rfl
  exact d.mono (by omega)

theorem scosBase_wt5 (a b c d e : Val) :
    (Val.list [a, b, c, d, e]).wt ≤ 2 * (a.wt + b.wt + c.wt + d.wt + e.wt) + 9 := by
  have := wt_list_le [a, b, c, d, e]; simp at this; omega

/-- The bound `S` of the transversal. -/
def scosBaseS (M : ℕ) : ℕ := 10 ^ 16 * M ^ 6

/-- The arithmetic of step 5. -/
theorem scosBase_e5_arith {M l N ca cb w : ℕ} (hl : l < M) (hN : N + 1 ≤ M) (hca : ca ≤ 200 * M + 1000)
    (hcb : cb ≤ schK * (l + 2 * N + 20) ^ 6) (hw : w < cb) :
    ca + cb + w + 1 ≤ scosBaseS M ∧ w ≤ scosBaseS M := by
  have h1 : l + 2 * N + 20 ≤ 24 * M := by omega
  have h2 : (l + 2 * N + 20) ^ 6 ≤ 24 ^ 6 * M ^ 6 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left h1 6
  have h3 : M ≤ M ^ 6 := Nat.le_self_pow (by norm_num) M
  have hK : schK = 11000000 := rfl
  rw [hK] at hcb
  unfold scosBaseS
  constructor <;> omega

/-- **Step 5**: the Schreier transversal of `n + α`. -/
theorem scosBase_e5 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n) {M : ℕ}
    (hM : (scosBaseV gs x a).wt ≤ M) (hN : n + n + 1 ≤ M) :
    EvalAll (𝒫) (scosBaseE4 gs x a)
      (.call 91 (scosMk5 (.nat 0) (.get (arg 0) (.nat 1)) (mk1 (.var 3)) (.length (arg 1))
        (.length (arg 1))))
      (fun w cost => ∃ L : List (Fin (n + n) × Perm (Fin (n + n))), w = encPairs ptKey L ∧
        (L.map Prod.fst).Nodup ∧
        (∀ β, β ∈ L.map Prod.fst ↔ ∃ g ∈ genGroup (1 :: gs), g (Fin.natAdd n a) = β) ∧
        (∀ p ∈ L, p.2 ∈ genGroup (1 :: gs) ∧ p.2 (Fin.natAdd n a) = p.1) ∧
        cost ≤ scosBaseS M ∧ w.wt ≤ scosBaseS M) := by
  have w5 : (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt ≤ M := hM
  have dg : Det (𝒫) (scosBaseE4 gs x a) (arg 0)
      (.list [.nat (n + n), .list ((1 :: gs).map encPerm)]) _ :=
    Det.arg' (vs := [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))])
      (rest := [.nat a, .nat n, .nat (n + a), .nat (scosBaseTau x a)]) (j := 0) rfl
  have dgs := Det.get' dg (Det.nat 1) (v := .list ((1 :: gs).map encPerm)) rfl
  have dp : Det (𝒫) (scosBaseE4 gs x a) (mk1 (.var 3)) (natList (ptKey (Fin.natAdd n a))) _ :=
    Det.mk1 (Det.var' (i := 3) rfl)
  have dl := scosBase_len (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs x a
    [.nat a, .nat n, .nat (n + a), .nat (scosBaseTau x a)]
  have darg := Det.snoc (Det.mk4 (Det.nat (P := 𝒫) (env := scosBaseE4 gs x a) 0) dgs dp dl) dl
  have darg' : Det (𝒫) (scosBaseE4 gs x a)
      (scosMk5 (.nat 0) (.get (arg 0) (.nat 1)) (mk1 (.var 3)) (.length (arg 1)) (.length (arg 1)))
      (.list [.nat 0, .list ((1 :: gs).map encPerm), natList (ptKey (Fin.natAdd n a)),
        .nat (n + n), .nat (n + n)]) _ := darg
  refine EvalAll.call_funAll darg' fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine ((schreier_spec (scos_schreier (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (1 :: gs) (Fin.natAdd n a)).wt_lt).mono fun w cb hw => ?_
  obtain ⟨⟨L, h1, h2, h3, h4, -, h6⟩, hwt⟩ := hw
  refine ⟨L, h1, h2, h3, h4, ?_⟩
  -- the cost
  have hgl : ((1 :: gs).map encPerm).length < (Val.list ((1 :: gs).map encPerm)).wt :=
    length_lt_wt_list _
  have hg1 : (Val.list ((1 :: gs).map encPerm)).wt <
      (Val.list [.nat (n + n), .list ((1 :: gs).map encPerm)]).wt := wt_le_wt_list (by simp)
  have hg2 : (Val.list [.nat (n + n), .list ((1 :: gs).map encPerm)]).wt <
      (scosBaseV gs x a).wt := wt_le_wt_list (v := encGroup gs) (by simp)
  simp only [List.length_map] at hgl
  have hl : (1 :: gs).length < M := by omega
  have wA : (Val.list [.nat 0, .list ((1 :: gs).map encPerm), natList (ptKey (Fin.natAdd n a)),
      .nat (n + n), .nat (n + n)]).wt ≤ 10 * M + 40 := by
    have hw0 := scosBase_wt5 (.nat 0) (.list ((1 :: gs).map encPerm))
      (natList (ptKey (Fin.natAdd n a))) (.nat (n + n)) (.nat (n + n))
    have e1 : (natList (ptKey (Fin.natAdd n a))).wt =
      (Val.list [.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ)]).wt := rfl
    have e2 := wt_list1_le (.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ))
    have e3 := wt_nat_le ((Fin.natAdd n a : Fin (n + n)) : ℕ)
    have e6 := (Fin.natAdd n a : Fin (n + n)).isLt
    have e4 := wt_nat_le (n + n)
    have e5 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    omega
  have wB : (Val.list [.nat 0, .list ((1 :: gs).map encPerm), natList (ptKey (Fin.natAdd n a)),
      .nat (n + n), .nat (n + n)]).wt = (Val.list ([.nat 0, .list ((1 :: gs).map encPerm),
      natList (ptKey (Fin.natAdd n a)), .nat (n + n)] ++ [.nat (n + n)])).wt := rfl
  have wC : (Val.list [.nat 0, .list ((1 :: gs).map encPerm),
      natList (ptKey (Fin.natAdd n a)), .nat (n + n)]).wt ≤ 10 * M + 40 :=
    (wt_list_mono ⟨[.nat (n + n)], rfl⟩).trans wA
  have wD : (Val.list [.nat (n + n), .list ((1 :: gs).map encPerm)]).wt ≤ M := by omega
  have wE : (natList (ptKey (Fin.natAdd n a))).wt ≤ 2 * M + 20 := by
    have e1 : (natList (ptKey (Fin.natAdd n a))).wt =
      (Val.list [.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ)]).wt := rfl
    have e2 := wt_list1_le (.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ))
    have e3 := wt_nat_le ((Fin.natAdd n a : Fin (n + n)) : ℕ)
    have e6 := (Fin.natAdd n a : Fin (n + n)).isLt
    omega
  have e : (scosBaseV gs x a).wt = (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt := rfl
  have hca' : ca ≤ 200 * M + 1000 := by
    have e2 := wt_list1_le (.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ))
    have e3 := wt_nat_le ((Fin.natAdd n a : Fin (n + n)) : ℕ)
    have e6 := (Fin.natAdd n a : Fin (n + n)).isLt
    omega
  exact scosBase_e5_arith (l := (1 :: gs).length) (N := n + n) hl hN hca'
    (by simpa using h6) hwt

end Steps

end GI.Impl
