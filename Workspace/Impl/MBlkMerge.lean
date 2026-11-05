module

public import Workspace.Impl.MBlkMath
public import Workspace.Lang.Lib.Orbit

@[expose] public section

/-!
# Joining two classes, as a program

A partition by representatives `lab : Fin n → Fin n` is the value `mlab lab`, the list of the
`n` representatives. `mblkMergeFuns` computes `mblkMerge lab u v` from `[[lab u, lab v], lab]`:
a `map` over the list that replaces every entry `lab v` by `lab u`.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- A partition by representatives, as a value. -/
def mlab (lab : Fin n → Fin n) : Val := encFun fun x => (lab x : ℕ)

theorem mlab_eq (lab : Fin n → Fin n) :
    mlab lab = .list ((List.finRange n).map fun i => .nat (lab i : ℕ)) := rfl

theorem wt_mlab_le (lab : Fin n → Fin n) : (mlab lab).wt ≤ 4 * (n + 1) ^ 2 :=
  wt_encFun_le_sq _ fun x => (lab x).isLt.le

/-- The identity partition is the list of points. -/
theorem mlab_id : mlab (id : Fin n → Fin n) = encFun fun x : Fin n => (x : ℕ) := rfl

/-! ### One entry -/

/-- On `[[a, b], l]`: `a` if `l = b`, else `l`. -/
def mblkElemF : Expr :=
  .ite (.arith .eq (arg 1) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 0)) (arg 1)

theorem mblkElem_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some mblkElemF) {a b l : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hl : l ≤ n) :
    FunDet P f (.list [.list [.nat a, .nat b], .nat l]) (.nat (if l = b then a else l))
      (300 * (n + 1)) := by
  set A := Val.list [.list [.nat a, .nat b], .nat l] with hA
  have d1 := Det.arg' (P := P) (rest := []) (vs := [.list [.nat a, .nat b], .nat l]) (j := 1) rfl
  have d2 := Det.get' (P := P) (Det.arg' (rest := []) (vs := [.list [.nat a, .nat b], .nat l])
    (j := 0) rfl) (Det.nat 1) (show [Val.nat a, .nat b][1]? = some (.nat b) from rfl)
  have d3 := Det.get' (P := P) (Det.arg' (rest := []) (vs := [.list [.nat a, .nat b], .nat l])
    (j := 0) rfl) (Det.nat 0) (show [Val.nat a, .nat b][0]? = some (.nat a) from rfl)
  have dc := Det.arith' (op := .eq) d1 d2 rfl
  have dt := Det.ite' dc d3 d1
  have hv : (if BinOp.eval .eq l b = 0 then Val.nat l else Val.nat a) =
      .nat (if l = b then a else l) := by
    simp only [BinOp.eval]; split_ifs <;> simp_all
  rw [hv] at dt
  refine FunDet.intro hf (dt.mono ?_)
  have h1 := wt_nat_le a
  have h2 := wt_nat_le b
  have h3 := wt_nat_le l
  have h4 := wt_list2_le (.nat a) (.nat b)
  have h5 := wt_list2_le (.list [.nat a, .nat b]) (.nat l)
  have h6 := wt_nat_le (if l = b then a else l)
  have h7 : (if l = b then a else l) ≤ n := by split_ifs <;> omega
  have h8 : BinOp.eval .eq l b ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
  have e : (Val.list [.list [.nat a, .nat b], .nat l]).wt = A.wt := rfl
  omega

/-! ### The map -/

/-- `map mblkElemF`, at base `b` (four functions): on `[[lab u, lab v], mlab lab]`, the value
`mlab (mblkMerge lab u v)`. -/
def mblkMergeFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [mblkElemF]

theorem mblkMerge_spec {P : Program} {b : ℕ} (h : P.HasAt b (mblkMergeFuns b))
    (lab : Fin n → Fin n) (u v : Fin n) :
    FunDet P b (.list [.list [.nat (lab u), .nat (lab v)], mlab lab])
      (mlab (mblkMerge lab u v)) (100000 * (n + 1) ^ 3) := by
  have hf : P.funs[b + 3]? = some mblkElemF := by
    simpa [mblkMergeFuns, mapFuns, loopFuns] using h.right.single
  set c := Val.list [.nat (lab u), .nat (lab v)] with hc
  have hM := map_spec (c := c) (xs := (List.finRange n).map fun i => Val.nat (lab i : ℕ)) h.left
    (R := fun x w => ∀ k : ℕ, x = .nat k → w = .nat (if k = lab v then lab u else k))
    (B := fun _ => 300 * (n + 1)) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (mblkElem_spec hf (lab u).isLt.le (lab v).isLt.le (lab i).isLt.le)
        fun w c hw => ⟨fun k hk => ?_, hw.2⟩
      cases hk
      exact hw.1)
  refine hM.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hcost⟩ := hw
  have hws' : ws = (List.finRange n).map fun i => Val.nat (mblkMerge lab u v i : ℕ) := by
    refine forall₂_map_eq (h := hws) fun i _ w hw => ?_
    rw [hw _ rfl]
    simp only [mblkMerge, Fin.val_inj]
    split_ifs <;> rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map, List.length_finRange, sum_const_finRange] at hcost
  have h1 := wt_mlab_le lab
  have h3 := wt_mlab_le (mblkMerge lab u v)
  have h4 := wt_nat_le (lab u)
  have h5 := wt_nat_le (lab v)
  have h6 : c.wt ≤ 2 * ((Val.nat (lab u)).wt + (Val.nat (lab v)).wt) + 6 := wt_list2_le _ _
  have h7 := wt_list2_le c (mlab lab)
  have hu := (lab u).isLt
  have hv := (lab v).isLt
  have e1 : (Val.list [c, .list ((List.finRange n).map fun i => Val.nat (lab i : ℕ))]).wt =
      (Val.list [c, mlab lab]).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun i => Val.nat (mblkMerge lab u v i : ℕ))).wt =
      (mlab (mblkMerge lab u v)).wt := rfl
  rw [e1, e2] at hcost
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h8 : mapK * (n + 1) * ((Val.list [c, mlab lab]).wt + (mlab (mblkMerge lab u v)).wt + 1) ≤
      mapK * (n + 1) * (60 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have e8 : mapK * (n + 1) * (60 * (n + 1) ^ 2) = 60000 * (n + 1) ^ 3 := by
    simp only [mapK]; ring
  have h9 : n * (300 * (n + 1)) ≤ 300 * (n + 1) ^ 3 := by
    have : n * (n + 1) ≤ (n + 1) ^ 3 := by
      calc n * (n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = (n + 1) ^ 2 := by ring
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have e : n * (300 * (n + 1)) = 300 * (n * (n + 1)) := by ring
    omega
  omega

end GI.Impl
