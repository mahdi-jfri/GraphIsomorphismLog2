import Workspace.Impl.SCosBase3

/-!
# The base case, the search for `τ`

Step 6 of `scosBaseF`: the index of the first pair `([β], t)` of the transversal with `β = τ`,
by `find_spec` with the test function 11 (`scosPtTestF`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The test of function 11 on a pair value: whether its point is `τ`. -/
def scosBaseQ (τ : ℕ) : Val → Bool
  | .list (.list [.nat b] :: _) => decide (b = τ)
  | _ => false

theorem scosBaseQ_pair (τ : ℕ) (p : Fin (n + n) × Perm (Fin (n + n))) :
    scosBaseQ τ (GI.Lang.encPair ptKey p) = decide ((p.1 : ℕ) = τ) := rfl

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The cost bound of one test. -/
def scosBaseBt (n τ : ℕ) : ℕ := 1000 * (n + n + 1) ^ 2 + 20 * τ + 1000

/-- **The test** (function 11) on `[τ, [[β], t]]`. -/
theorem scosBase_test (τ : ℕ) (p : Fin (n + n) × Perm (Fin (n + n))) :
    FunDet (𝒫) 11 (.list [.nat τ, GI.Lang.encPair ptKey p])
      (boolVal (scosBaseQ τ (GI.Lang.encPair ptKey p))) (scosBaseBt n τ) := by
  obtain ⟨β, t⟩ := p
  have d0 : Det (𝒫) [.list [.nat τ, GI.Lang.encPair ptKey (β, t)]] (arg 1)
      (.list [natList (ptKey β), encPerm t]) _ :=
    Det.arg' (vs := [.nat τ, GI.Lang.encPair ptKey (β, t)]) (rest := []) (j := 1) rfl
  have d1 : Det (𝒫) [.list [.nat τ, GI.Lang.encPair ptKey (β, t)]] (.get (arg 1) (.nat 0))
      (.list [.nat (β : ℕ)]) _ := Det.get' d0 (Det.nat 0) (v := natList (ptKey β)) rfl
  have d2 := Det.get' d1 (Det.nat 0) (v := .nat (β : ℕ)) rfl
  have d3 : Det (𝒫) [.list [.nat τ, GI.Lang.encPair ptKey (β, t)]] (arg 0) (.nat τ) _ :=
    Det.arg' (vs := [.nat τ, GI.Lang.encPair ptKey (β, t)]) (rest := []) (j := 0) rfl
  have d := Det.arith' (op := .eq) d2 d3 rfl
  have hv : (Val.nat (BinOp.eval .eq (β : ℕ) τ)) = boolVal (scosBaseQ τ (GI.Lang.encPair ptKey (β, t))) := by
    rw [scosBaseQ_pair]
    simp only [BinOp.eval]
    by_cases h : (β : ℕ) = τ <;> simp [h]
  rw [hv] at d
  refine FunDet.intro scos_ptTest (d.mono ?_)
  have w1 := wt_list2_le (.nat τ) (GI.Lang.encPair ptKey (β, t))
  have w2 : (GI.Lang.encPair ptKey (β, t)).wt = (Val.list [natList (ptKey β), encPerm t]).wt := rfl
  have w3 := wt_list2_le (natList (ptKey β)) (encPerm t)
  have w4 : (natList (ptKey β)).wt = (Val.list [.nat (β : ℕ)]).wt := rfl
  have w5 := wt_list1_le (.nat (β : ℕ))
  have w6 := wt_nat_le (β : ℕ)
  have w7 := wt_nat_le τ
  have w8 := wt_encPerm_le t
  have w9 : (Val.nat (BinOp.eval .eq (β : ℕ) τ)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs
    · exact wt_nat_le 1
    · exact (wt_nat_le 0).trans (by norm_num)
  have hb := β.isLt
  have hz : BinOp.eval .eq (β : ℕ) τ ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
  have p1 : n + n + 1 ≤ (n + n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold scosBaseBt
  simp only [Nat.zero_add] at *
  omega

/-- The arithmetic of step 6. -/
theorem scosBase_d6_arith {l W τ M S Bt cf ca Wc : ℕ} (hl : l < W) (hW : W ≤ S) (hτ : τ ≤ M)
    (hMS : M ^ 2 ≤ S) (hM1 : 1 ≤ M) (hBt : Bt ≤ 3000 * M ^ 2)
    (hcf : cf ≤ l * Bt + 1000 * (l + 1) * (Wc + 2 * l + 3)) (hWc : Wc ≤ 2 * (τ + 2 + W) + 6)
    (hca : ca ≤ 3 * Wc + 2 * W + 2 * τ + 100) :
    ca + cf + (l + 2) + 1 ≤ 100000 * S ^ 2 := by
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have hS1 : 1 ≤ S := by omega
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) S
  have e1 : l * Bt ≤ S * (3000 * S) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (l + 1) * (Wc + 2 * l + 3) ≤ (2 * S) * (20 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e3 : 1000 * (l + 1) * (Wc + 2 * l + 3) = 1000 * ((l + 1) * (Wc + 2 * l + 3)) := by ring
  have e4 : S * (3000 * S) = 3000 * S ^ 2 := by ring
  have e5 : (2 * S) * (20 * S) = 40 * S ^ 2 := by ring
  omega

/-- **Step 6**: the index of `τ` in the transversal. -/
theorem scosBase_d6 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n)
    (L : List (Fin (n + n) × Perm (Fin (n + n)))) {M S : ℕ} (hN : n + n + 1 ≤ M)
    (hLw : (encPairs ptKey L).wt ≤ S) (hMS : M ^ 2 ≤ S) :
    Det (𝒫) (scosBaseE4 gs x a ++ [encPairs ptKey L]) (.call 114 (mk2 (.var 4) (.var 5)))
      (.nat (L.findIdx fun p => decide ((p.1 : ℕ) = scosBaseTau x a))) (100000 * S ^ 2) := by
  set τ : ℕ := (scosBaseTau x a : ℕ) with hτ
  have hf := find_spec (scos_findPt (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (c := .nat τ) (xs := L.map (GI.Lang.encPair ptKey)) (q := scosBaseQ τ) (B := fun _ => scosBaseBt n τ)
    (fun y hy => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
      exact scosBase_test τ p)
  have hidx : (L.map (GI.Lang.encPair ptKey)).findIdx (scosBaseQ τ) =
      L.findIdx fun p => decide ((p.1 : ℕ) = τ) := by
    rw [List.findIdx_map]; rfl
  have dv4 : Det (𝒫) (scosBaseE4 gs x a ++ [encPairs ptKey L]) (.var 4) (.nat τ) _ :=
    Det.var' (i := 4) rfl
  have dv5 : Det (𝒫) (scosBaseE4 gs x a ++ [encPairs ptKey L]) (.var 5)
      (.list (L.map (GI.Lang.encPair ptKey))) _ := Det.var' (i := 5) rfl
  have d := Det.call (Det.mk2 dv4 dv5) (hf.mono fun w cost h => ⟨h.1, h.2⟩)
  rw [hidx] at d
  refine d.mono ?_
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
  have hlen : L.length < (encPairs ptKey L).wt := by
    have := length_lt_wt_list (L.map (GI.Lang.encPair ptKey))
    simpa [encPairs] using this
  have e0 : (encPairs ptKey L).wt = (Val.list (L.map (GI.Lang.encPair ptKey))).wt := rfl
  have hτM : τ ≤ M := by
    have := (scosBaseTau x a).isLt; omega
  have hM1 : 1 ≤ M := by omega
  have hBt : scosBaseBt n τ ≤ 3000 * M ^ 2 := by
    unfold scosBaseBt
    have p1 : (n + n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hN 2
    have p2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
    omega
  have hWc := wt_list2_le (.nat τ) (.list (L.map (GI.Lang.encPair ptKey)))
  have w1 := wt_nat_le τ
  have w2 := wt_nat_le (L.findIdx fun p => decide ((p.1 : ℕ) = τ))
  have w3 : (L.findIdx fun p => decide ((p.1 : ℕ) = τ)) ≤ L.length := List.findIdx_le_length
  have hK : loopModK = 1000 := rfl
  rw [hK]
  generalize hcf : (L.map (GI.Lang.encPair ptKey)).findIdx (scosBaseQ τ) = cf0 at *
  have := scosBase_d6_arith (l := L.length) (W := (encPairs ptKey L).wt) (τ := τ) (M := M) (S := S)
    (Bt := scosBaseBt n τ) (Wc := (Val.list [.nat τ, .list (L.map (GI.Lang.encPair ptKey))]).wt)
    (cf := L.length * scosBaseBt n τ + 1000 * (L.length + 1) *
      ((Val.list [.nat τ, .list (L.map (GI.Lang.encPair ptKey))]).wt + 2 * L.length + 3))
    (ca := (Val.nat τ).wt + 1 + ((Val.list (L.map (GI.Lang.encPair ptKey))).wt + 1) +
      2 * (Val.list [.nat τ, .list (L.map (GI.Lang.encPair ptKey))]).wt + 7)
    hlen hLw hτM hMS hM1 hBt le_rfl (by omega) (by omega)
  omega

end Steps

end GI.Impl
