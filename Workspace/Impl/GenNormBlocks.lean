module

public import Workspace.Impl.GenNormLabels
public import Workspace.Impl.GenCosetsMath
public import Workspace.Impl.GenNormRecover

@[expose] public section

/-!
# Computing the Johnson block indicators

The input table lists a subset at each quotient block. Membership gives its indicator.
When the subset is larger than half the points, subtracting that indicator from one gives
the complement. The outer map leaves an empty list off the domain.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples)

/-- On `[[subset,complement],j]`, the subset or complement indicator at `j`. -/
def normMemFlipF (mem : ℕ) : Expr :=
  .letE (.call mem (mk2 (arg 1) (.get (arg 0) (.nat 0))))
    (.ite (.get (arg 0) (.nat 1)) (.arith .sub (.nat 1) (.var 1)) (.var 1))

/-- Computing one bit of the Johnson block map has polynomial cost. -/
theorem normMemFlip_spec {Pg : Program} {f mem m : ℕ}
    (hf : Pg.funs[f]? = some (normMemFlipF mem)) (hm : Pg.HasAt mem (normMemFuns mem))
    (A : Finset (Fin m)) (b : Bool) (j : Fin m) :
    FunDet Pg f (.list [.list [normSetVal A, boolVal b], .nat j])
      (boolVal (decide (j ∈ (if b then Aᶜ else A))))
      (100000 * (m + 1) ^ 3 + 1000 * ((Val.list [.list [normSetVal A, boolVal b], .nat j]).wt + 1)) := by
  let ctx := Val.list [normSetVal A, boolVal b]
  let inp := Val.list [ctx, .nat j]
  have wc : ctx.wt < inp.wt := wt_le_wt_list (by simp)
  have wa : (normSetVal A).wt < ctx.wt := wt_le_wt_list (by simp)
  have wb : (boolVal b).wt < ctx.wt := wt_le_wt_list (by simp)
  have wj : (Val.nat j).wt < inp.wt := wt_le_wt_list (by simp)
  have dctx : ∀ rest, Det Pg (inp :: rest) (arg 0) ctx (2 * inp.wt + 5) :=
    fun rest => Det.arg' (j := 0) rfl
  have dA : Det Pg [inp] (.get (arg 0) (.nat 0)) (normSetVal A) (4 * inp.wt + 20) :=
    (Det.get' (dctx []) (Det.nat 0) rfl).mono (by omega)
  have dj : Det Pg [inp] (arg 1) (.nat j) (2 * inp.wt + 6) := Det.arg' (j := 1) rfl
  have dc := Det.call (Det.mk2 dj dA) (normMem_spec hm A j)
  have df : Det Pg [inp, boolVal (decide (j ∈ A))] (.get (arg 0) (.nat 1)) (boolVal b)
      (4 * inp.wt + 20) := (Det.get' (dctx _) (Det.nat 1) rfl).mono (by omega)
  have dv := Det.var' (P := Pg) (env := [inp, boolVal (decide (j ∈ A))]) (i := 1) rfl
  have dw := wt_boolVal_le (decide (j ∈ A))
  have dw' : (Val.nat (decide (j ∈ A)).toNat).wt ≤ 3 := dw
  have warg := wt_list2_le (.nat j) (normSetVal A)
  refine FunDet.intro hf ?_
  cases b with
  | false =>
    have hbody := Det.ite_zero (t := .arith .sub (.nat 1) (.var 1)) df dv
    have hout : boolVal (decide (j ∈ (if false then Aᶜ else A))) = boolVal (decide (j ∈ A)) := rfl
    rw [hout]
    exact (Det.letE dc hbody).mono (by
      change _ ≤ 100000 * (m + 1) ^ 3 + 1000 * (inp.wt + 1)
      omega)
  | true =>
    have dsub := Det.arith' (op := .sub) (Det.nat (P := Pg)
      (env := [inp, boolVal (decide (j ∈ A))]) 1) dv
      (z := (decide (j ∈ Aᶜ)).toNat) (by
        by_cases hj : j ∈ A <;> simp [GI.Machine.BinOp.eval, hj])
    have hbody := Det.ite_pos (e := .var 1) df (by decide) dsub
    have wout := wt_boolVal_le (decide (j ∈ Aᶜ))
    have wout' : (Val.nat (decide (j ∈ Aᶜ)).toNat).wt ≤ 3 := wout
    have hb := Bool.toNat_le (decide (j ∈ Aᶜ))
    exact (Det.letE dc hbody).mono (by
      change _ ≤ 100000 * (m + 1) ^ 3 + 1000 * (inp.wt + 1)
      omega)

/-- Mapping the bit program gives a whole subset or complement indicator. -/
theorem normBits_spec {Pg : Program} {b f mem m : ℕ}
    (hmap : Pg.HasAt b (mapFuns b f)) (hf : Pg.funs[f]? = some (normMemFlipF mem))
    (hm : Pg.HasAt mem (normMemFuns mem)) (A : Finset (Fin m)) (flip : Bool) :
    FunDet Pg b (.list [.list [normSetVal A, boolVal flip], encPerm (1 : Perm (Fin m))])
      (encFun fun j : Fin m => (decide (j ∈ (if flip then Aᶜ else A))).toNat)
      (10 ^ 8 * ((normSetVal A).wt + m + 1) ^ 4) := by
  let ctx := Val.list [normSetVal A, boolVal flip]
  let Z := (normSetVal A).wt + m + 1
  have hZ : 1 ≤ Z := by dsimp only [Z]; omega
  have hmZ : m + 1 ≤ Z := by dsimp only [Z]; omega
  have hAZ : (normSetVal A).wt ≤ Z := by dsimp only [Z]; omega
  have wf := wt_boolVal_le flip
  have wc := wt_list2_le (normSetVal A) (boolVal flip)
  have wcZ : ctx.wt ≤ 14 * Z := by dsimp only [ctx]; omega
  have h1 : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) _
  have ht : ∀ j : Fin m, FunDet Pg f (.list [ctx, .nat j])
      (.nat (decide (j ∈ (if flip then Aᶜ else A))).toNat) (10 ^ 6 * Z ^ 3) := by
    intro j
    have h := normMemFlip_spec hf hm A flip j
    refine h.mono ?_
    have wj := wt_nat_le (j : ℕ)
    have hj := j.2
    have wa := wt_list2_le ctx (.nat j)
    have hm3 : (m + 1) ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left hmZ 3
    change 100000 * (m + 1) ^ 3 + 1000 * ((Val.list [ctx, .nat j]).wt + 1) ≤ _
    omega
  have h := tabulate_spec hmap (c := ctx)
    (F := fun j : Fin m => Val.nat (decide (j ∈ (if flip then Aᶜ else A))).toNat) ht
  have hout : (Val.list ((List.finRange m).map fun j : Fin m =>
      Val.nat (decide (j ∈ (if flip then Aᶜ else A))).toNat)) =
      encFun (fun j : Fin m => (decide (j ∈ (if flip then Aᶜ else A))).toNat) := rfl
  have hin : encFun (fun j : Fin m => (j : ℕ)) = encPerm (1 : Perm (Fin m)) := rfl
  rw [hout, hin] at h
  refine h.mono ?_
  have wid := wt_encPerm_le (1 : Perm (Fin m))
  have wout := wt_encFun_le (fun j : Fin m => (decide (j ∈ (if flip then Aᶜ else A))).toNat)
    (B := 1) (fun j => Bool.toNat_le _)
  have wa := wt_list2_le ctx (encPerm (1 : Perm (Fin m)))
  have hm2 : (m + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left hmZ 2
  have h12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcost1 : m * (10 ^ 6 * Z ^ 3) ≤ 10 ^ 6 * Z ^ 4 := by
    calc _ ≤ Z * (10 ^ 6 * Z ^ 3) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hcost2 : mapK * (m + 1) *
      ((Val.list [ctx, encPerm (1 : Perm (Fin m))]).wt +
        (encFun (fun j : Fin m => (decide (j ∈ (if flip then Aᶜ else A))).toNat)).wt + 1) ≤
          54000 * Z ^ 3 := by
    calc _ ≤ 1000 * Z * (54 * Z ^ 2) := by
          apply Nat.mul_le_mul
          · simp only [mapK]; omega
          · omega
      _ = _ := by ring
  have h34 : Z ^ 3 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ (by omega)
  change _ ≤ 10 ^ 8 * Z ^ 4
  omega

/-- The block indicator at one position, with an empty entry off the domain. -/
noncomputable def normBlockAt {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (flip : Bool) (i : Fin n) : Val := by
  classical
  exact if en.symm i ∈ S.dom then
    encFun (fun j : Fin m => (decide (j ∈ (if flip then (Q.kset e (en.symm i))ᶜ else
      Q.kset e (en.symm i)))).toNat) else .list []

/-- On `[[E,num,domain,pointIds,complement],i]`, compute the block indicator at position `i`. -/
def normBlockCellF (bits : ℕ) : Expr :=
  .ite (.get (.get (arg 0) (.nat 2)) (arg 1))
    (.call bits (mk2 (mk2
      (.get (.get (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))) (.nat 0))
      (.get (arg 0) (.nat 4))) (.get (arg 0) (.nat 3)))) .nil

private theorem normBlockGet {Pg : Program} {fields : List Val} {entry : Val} {j : ℕ} {v : Val}
    (hj : fields[j]? = some v) :
    Det Pg [.list [.list fields, entry]] (.get (arg 0) (.nat j)) v
      (5 * (Val.list [.list fields, entry]).wt + j + 20) := by
  have hc : (Val.list fields).wt < (Val.list [.list fields, entry]).wt := wt_le_wt_list (by simp)
  have hv : v.wt < (Val.list fields).wt := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact wt_getElem_lt _ _ h
  exact (Det.get' (Det.arg' (j := 0) rfl) (Det.nat j) hj).mono (by omega)

set_option maxHeartbeats 2000000 in
/-- The block indicator is computed from the numbered quotient and Cameron table. -/
theorem normBlockCell_spec {Pg : Program} {f bits bit mem n m k : ℕ}
    (hf : Pg.funs[f]? = some (normBlockCellF bits))
    (hmap : Pg.HasAt bits (mapFuns bits bit)) (hbit : Pg.funs[bit]? = some (normMemFlipF mem))
    (hmem : Pg.HasAt mem (normMemFuns mem))
    {Ω C : Type} {S : State Ω C} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (num : Fin n → ℕ)
    (hnum : ∀ i, num i = Q.labFin en i) (flip : Bool) (i : Fin n) :
    FunDet Pg f (.list [.list [encKSetTuples e, encFun num, encFun (indF en S.dom),
      encPerm (1 : Perm (Fin m)), boolVal flip], .nat i]) (normBlockAt en Q e flip i)
      (10 ^ 12 * ((Val.list [.list [encKSetTuples e, encFun num, encFun (indF en S.dom),
        encPerm (1 : Perm (Fin m)), boolVal flip], .nat i]).wt + n + m + 20) ^ 5) := by
  classical
  let fields := [encKSetTuples e, encFun num, encFun (indF en S.dom),
    encPerm (1 : Perm (Fin m)), boolVal flip]
  let ctx := Val.list fields
  let inp := Val.list [ctx, .nat i]
  let Z := inp.wt + n + m + 20
  have hZ20 : 20 ≤ Z := by dsimp only [Z]; omega
  have hmZ : m + 1 ≤ Z := by dsimp only [Z]; omega
  have hinZ : inp.wt ≤ Z := by dsimp only [Z]; omega
  have wc : ctx.wt < inp.wt := wt_le_wt_list (by simp)
  have wE : (encKSetTuples e).wt < inp.wt := (wt_le_wt_list (by simp [fields])).trans wc
  have wid : (encPerm (1 : Perm (Fin m))).wt < inp.wt := (wt_le_wt_list (by simp [fields])).trans wc
  have dE : Det Pg [inp] (.get (arg 0) (.nat 0)) (encKSetTuples e) (5 * inp.wt + 20) := normBlockGet rfl
  have dnum : Det Pg [inp] (.get (arg 0) (.nat 1)) (encFun num) (5 * inp.wt + 21) := normBlockGet rfl
  have ddm : Det Pg [inp] (.get (arg 0) (.nat 2)) (encFun (indF en S.dom)) (5 * inp.wt + 22) := normBlockGet rfl
  have dids : Det Pg [inp] (.get (arg 0) (.nat 3)) (encPerm (1 : Perm (Fin m)))
      (5 * inp.wt + 23) := normBlockGet rfl
  have dflip : Det Pg [inp] (.get (arg 0) (.nat 4)) (boolVal flip) (5 * inp.wt + 24) := normBlockGet rfl
  have di : Det Pg [inp] (arg 1) (.nat i) (2 * inp.wt + 6) := Det.arg' (j := 1) rfl
  have dd := Det.get' ddm di (encFun_getElem? (indF en S.dom) i)
  have wzero := wt_nat_le 0
  have wone := wt_nat_le 1
  have wnil : (Val.list []).wt = 4 := rfl
  by_cases hi : en.symm i ∈ S.dom
  · have hid : indF en S.dom i = 1 := by simp [indF, hi]
    rw [hid] at dd
    have hni : num i = (Q.blk (en.symm i) : ℕ) := by
      rw [hnum]
      simp only [PrimitiveQuotient.labFin, if_pos hi]
    have dn := Det.get' dnum di (encFun_getElem? num i)
    rw [hni] at dn
    obtain ⟨row, htable, hget, rfl⟩ := normTable_get e (Q.blk (en.symm i))
    have wr : (Val.list [normSetVal (e (Q.blk (en.symm i)) 0).1]).wt < inp.wt := by
      have h := wt_getElem_lt ((List.finRange Q.d).map fun b => Val.list [normSetVal (e b 0).1])
        (Q.blk (en.symm i)).val (by simp)
      simp only [List.getElem_map, List.getElem_finRange] at h
      rw [← htable] at h
      exact h.trans wE
    have ws : (normSetVal (e (Q.blk (en.symm i)) 0).1).wt < inp.wt :=
      (wt_le_wt_list (by simp)).trans wr
    have dE' := dE
    rw [htable] at dE'
    have ds := Det.get' (Det.get' dE' dn hget) (Det.nat 0) rfl
    have db := Det.call (Det.mk2 (Det.mk2 ds dflip) dids)
      (normBits_spec hmap hbit hmem (e (Q.blk (en.symm i)) 0).1 flip)
    have hn := wt_nat_le (Q.blk (en.symm i) : ℕ)
    have hni' : (Q.blk (en.symm i) : ℕ) < Q.d := (Q.blk (en.symm i)).2
    have hd := Q.d_le_card en
    have wf := wt_boolVal_le flip
    have wa := wt_list2_le (normSetVal (e (Q.blk (en.symm i)) 0).1) (boolVal flip)
    have wp := wt_list2_le (.list [normSetVal (e (Q.blk (en.symm i)) 0).1, boolVal flip])
      (encPerm (1 : Perm (Fin m)))
    have wo := wt_encFun_le (fun j : Fin m =>
      (decide (j ∈ (if flip then (e (Q.blk (en.symm i)) 0).1ᶜ else (e (Q.blk (en.symm i)) 0).1))).toNat)
      (B := 1) (fun j => Bool.toNat_le _)
    have hpow : ((normSetVal (e (Q.blk (en.symm i)) 0).1).wt + m + 1) ^ 4 ≤ Z ^ 5 :=
      (Nat.pow_le_pow_left (show _ ≤ Z by dsimp only [Z]; omega) 4).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    have h15 : Z ≤ Z ^ 5 := Nat.le_self_pow (by norm_num) _
    unfold normBlockAt
    rw [if_pos hi]
    refine FunDet.intro hf ((Det.ite_pos (e := .nil) dd (by decide) db).mono ?_)
    change _ ≤ 10 ^ 12 * Z ^ 5
    omega
  · have hid : indF en S.dom i = 0 := by simp [indF, hi]
    rw [hid] at dd
    unfold normBlockAt
    rw [if_neg hi]
    refine FunDet.intro hf ((Det.ite_zero (t := .call bits (mk2 (mk2
      (.get (.get (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))) (.nat 0))
      (.get (arg 0) (.nat 4))) (.get (arg 0) (.nat 3)))) dd Det.nil).mono ?_)
    have h15 : Z ≤ Z ^ 5 := Nat.le_self_pow (by norm_num) _
    change _ ≤ 10 ^ 12 * Z ^ 5
    omega

end GI.Impl
