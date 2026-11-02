import Workspace.Impl.AggItemCiCfgC
import Workspace.Impl.AggStructDC

/-!
# The configuration query: the generators as a program

`itcqSwF` computes one entry of a diagonal transposition: on `[[n, i, j], t]`, the number
`s (t % n) + n · s (t / n)` with `s = swap i j`. That is entry `t` of
`encPerm (itciD n (swap i j))` (`itcq_swE_val`). `itcq_swF_spec` is its cost.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup)

/-- `swap i j` on a number, with `i = I`, `j = J`. -/
def itcqSE (x I J : Expr) : Expr := .ite (.arith .eq x I) J (.ite (.arith .eq x J) I x)

/-- On `[[n, i, j], t]`: entry `t` of the diagonal transposition of `i` and `j`. -/
def itcqSwF : Expr :=
  .letE (.arith .div (arg 1) (.get (arg 0) (.nat 0)))
    (.letE (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))
      (.arith .add (itcqSE (.var 2) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)))
        (.arith .mul (.get (arg 0) (.nat 0))
          (itcqSE (.var 1) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))))))

/-- The number `swap i j x`. -/
def itcqS (i j x : ℕ) : ℕ := if x = i then j else if x = j then i else x

theorem itcqS_val {n : ℕ} (i j x : Fin n) : itcqS i j x = (swap i j x : ℕ) := by
  rw [swap_apply_def]
  unfold itcqS
  split_ifs <;> simp_all [Fin.ext_iff]

theorem itcq_swE_val {n : ℕ} (i j : Fin n) (t : Fin (n * n)) :
    (itciD n (swap i j) t : ℕ) = itcqS i j (t % n) + n * itcqS i j (t / n) := by
  have ha : (t : ℕ) / n < n := ((itciPE n).symm t).1.isLt
  have hb : (t : ℕ) % n < n := ((itciPE n).symm t).2.isLt
  have e1 := itcqS_val i j ⟨_, ha⟩
  have e2 := itcqS_val i j ⟨_, hb⟩
  simp only at e1 e2
  rw [e1, e2]
  simp [itciD, toFin, Equiv.permCongr_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem itcqS_lt {n i j x : ℕ} (hi : i < n) (hj : j < n) (hx : x < n) : itcqS i j x < n := by
  unfold itcqS; split_ifs <;> assumption

section Prog

variable {P : Program} {env : List Val} {W : ℕ}

theorem itcq_se_spec {x I J : Expr} {a i j nx Ex nI EI nJ EJ : ℕ}
    (hx : StDC P env x (.nat a) nx Ex W) (hI : StDC P env I (.nat i) nI EI W)
    (hJ : StDC P env J (.nat j) nJ EJ W) (hw : a + 3 ≤ W) (hiw : i + 3 ≤ W) (hjw : j + 3 ≤ W) :
    StDC P env (itcqSE x I J) (.nat (itcqS i j a)) (3 * nx + 3 * nI + 3 * nJ + 5)
      (3 * Ex + 3 * EI + 3 * EJ) W := by
  have hw01 : ∀ y z : ℕ, (Val.nat (if y = z then 1 else 0)).wt ≤ W := fun y z => by
    split_ifs <;> (have := wt_nat_le 1; have := wt_nat_le 0; omega)
  have c1 := StDC.arith hx hI (op := .eq) rfl (hw01 a i)
  have c2 := StDC.arith hx hJ (op := .eq) rfl (hw01 a j)
  have hv : (Val.nat (itcqS i j a)).wt ≤ W := by
    unfold itcqS; split_ifs <;> exact (wt_nat_le _).trans (by omega)
  refine (StDC.ite (nt := nJ) (Et := EJ) (ne := nx + nJ + 1 + nI + nx + 1)
    (Ee := Ex + EJ + EI + Ex) c1 (fun h => ?_) (fun h => ?_) hv).mono (by omega) (by omega)
  · have : a = i := by
      simp only [Machine.BinOp.eval_eq] at h; split_ifs at h with h'; exact h'; simp at h
    rw [show itcqS i j a = j by simp [itcqS, this]]
    exact hJ
  · have hai : a ≠ i := by
      simp only [Machine.BinOp.eval_eq] at h; split_ifs at h with h'; simp at h; exact h'
    refine StDC.ite (nt := nI) (Et := EI) (ne := nx) (Ee := Ex) c2 (fun h2 => ?_) (fun h2 => ?_) hv
    · have : a = j := by
        simp only [Machine.BinOp.eval_eq] at h2; split_ifs at h2 with h'; exact h'; simp at h2
      rw [show itcqS i j a = i by simp [itcqS, this, hai]]
      exact hI
    · have haj : a ≠ j := by
        simp only [Machine.BinOp.eval_eq] at h2; split_ifs at h2 with h'; simp at h2; exact h'
      rw [show itcqS i j a = a by simp [itcqS, hai, haj]]
      exact hx

theorem itcq_lt_sq {n x y : ℕ} (hx : x < n) (hy : y < n) : x + n * y < n * n := by
  have : n * (y + 1) ≤ n * n := Nat.mul_le_mul_left n hy
  rw [Nat.mul_succ] at this
  omega

/-- **One entry of a diagonal transposition**, in cost `103 (W + 1)`. -/
theorem itcq_swF_spec {f : ℕ} (hf : P.funs[f]? = some itcqSwF) {n i j t : ℕ} (hi : i < n)
    (hj : j < n) (ht : t < n * n)
    (hW : (Val.list [.list [.nat n, .nat i, .nat j], .nat t]).wt + n * n + 3 ≤ W) :
    FunDet P f (.list [.list [.nat n, .nat i, .nat j], .nat t])
      (.nat (itcqS i j (t % n) + n * itcqS i j (t / n))) (103 * (W + 1)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; simp at ht
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hl : (Val.list [.nat n, .nat i, .nat j]).wt ≤ (Val.list [.list [.nat n, .nat i, .nat j], .nat t]).wt := st_wt_mem (by simp)
  have htw : (Val.nat t).wt ≤ (Val.list [.list [.nat n, .nat i, .nat j], .nat t]).wt := st_wt_mem (by simp)
  have hqd : t / n < n := Nat.div_lt_of_lt_mul ht
  have hqm : t % n < n := Nat.mod_lt _ hn
  have G : ∀ (rest : List Val) (m v : ℕ), [Val.nat n, .nat i, .nat j][m]? = some (.nat v) →
      StDC P ((Val.list [.list [.nat n, .nat i, .nat j], .nat t]) :: rest) (.get (arg 0) (.nat m)) (.nat v) 5 0 W := by
    intro rest m v hm
    have hm3 : m < 3 := by
      by_contra h; rw [List.getElem?_eq_none (by simp; omega)] at hm; cases hm
    have hv : (Val.nat v).wt ≤ W := by
      have := st_wt_mem (List.mem_of_getElem? hm); omega
    have A0 : StDC P ((Val.list [.list [.nat n, .nat i, .nat j], .nat t]) :: rest) (arg 0) (.list [.nat n, .nat i, .nat j]) 3 0 W :=
      StDC.arg (vs := [.list [.nat n, .nat i, .nat j], .nat t]) rfl (by omega) (by omega)
        (by omega)
    exact (StDC.get A0 (StDC.nat m (by omega)) hm hv).mono (by omega) le_rfl
  have T1 : ∀ rest : List Val, StDC P ((Val.list [.list [.nat n, .nat i, .nat j], .nat t]) :: rest) (arg 1) (.nat t) 3 0 W := fun rest =>
    StDC.arg (vs := [.list [.nat n, .nat i, .nat j], .nat t]) rfl (by omega) (by omega)
      (by omega)
  have hdiv := StDC.arith (T1 []) (G [] 0 n rfl) (op := .div) (z := t / n) rfl
    ((wt_nat_le _).trans (by omega))
  have hmod := StDC.arith (T1 [.nat (t / n)]) (G [.nat (t / n)] 0 n rfl) (op := .mod)
    (z := t % n) rfl ((wt_nat_le _).trans (by omega))
  have v1 : StDC P ((Val.list [.list [.nat n, .nat i, .nat j], .nat t]) :: [Val.nat (t / n), .nat (t % n)]) (.var 1) (.nat (t / n)) 1 0 W := StDC.var' rfl
    ((wt_nat_le _).trans (by omega))
  have v2 : StDC P ((Val.list [.list [.nat n, .nat i, .nat j], .nat t]) :: [Val.nat (t / n), .nat (t % n)]) (.var 2) (.nat (t % n)) 1 0 W := StDC.var' rfl
    ((wt_nat_le _).trans (by omega))
  have s2 := itcq_se_spec v2 (G _ 1 i rfl) (G _ 2 j rfl) (by omega) (by omega) (by omega)
  have s1 := itcq_se_spec v1 (G _ 1 i rfl) (G _ 2 j rfl) (by omega) (by omega) (by omega)
  have hs1 := itcqS_lt hi hj hqd
  have hs2 := itcqS_lt hi hj hqm
  have hlt := itcq_lt_sq hs2 hs1
  have m1 := StDC.arith (G _ 0 n rfl) s1 (op := .mul) (z := n * itcqS i j (t / n)) rfl
    ((wt_nat_le _).trans (by omega))
  have m2 := StDC.arith s2 m1 (op := .add)
    (z := itcqS i j (t % n) + n * itcqS i j (t / n)) rfl ((wt_nat_le _).trans (by omega))
  have l2 := StDC.letE hmod m2 ((wt_nat_le _).trans (by omega))
  have l1 := StDC.letE hdiv l2 ((wt_nat_le _).trans (by omega))
  exact StDC.funDet hf l1 (by omega)

/-- On `[[n, R], g]` with `R = [0, …, n² - 1]`: the diagonal transposition number `g`. -/
def itcqGenF (mp : ℕ) : Expr :=
  .call mp (mk2 (mk3 (.get (arg 0) (.nat 0)) (.arith .div (arg 1) (.get (arg 0) (.nat 0)))
    (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))) (.get (arg 0) (.nat 1)))

/-- The cost bound of `itcqGenF`. -/
def itcqGenC (m : ℕ) : ℕ := 10 ^ 6 * (m + 2) ^ 3

theorem itcq_sq_le {m : ℕ} : (m + 1) ^ 2 ≤ (m + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2

theorem itcq_mul_sq (m : ℕ) : (m + 1) * (m + 2) ^ 2 ≤ (m + 2) ^ 3 := by
  calc (m + 1) * (m + 2) ^ 2 ≤ (m + 2) * (m + 2) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = (m + 2) ^ 3 := by ring

theorem itcq_m_sq (m : ℕ) : m * (m + 2) ≤ (m + 2) ^ 2 := by
  calc m * (m + 2) ≤ (m + 2) * (m + 2) := Nat.mul_le_mul_right _ (by omega)
    _ = (m + 2) ^ 2 := by ring

theorem itcq_sq_cube (m : ℕ) : (m + 2) ^ 2 ≤ (m + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)

/-- The value of the diagonal transposition of `i`, `j`, from its entries. -/
theorem itcq_swV {n : ℕ} (i j : Fin n) :
    ((List.range (n * n)).map Val.nat).map (fun x => match x with
      | .nat t => .nat (itcqS i j (t % n) + n * itcqS i j (t / n))
      | _ => .nat 0) = (List.finRange (n * n)).map fun t => Val.nat (itciD n (swap i j) t) := by
  rw [List.map_map, ← List.map_coe_finRange, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply]
  rw [itcq_swE_val]

/-- **The diagonal transposition number `g`** as a program. -/
theorem itcq_genF_spec {f mp sw : ℕ} (hf : P.funs[f]? = some (itcqGenF mp))
    (hmp : P.HasAt mp (mapFuns mp sw)) (hsw : P.funs[sw]? = some itcqSwF) {n g : ℕ}
    (hg : g < n * n) :
    FunDet P f (.list [.list [.nat n, natList (List.range (n * n))], .nat g])
      (encPerm (itciD n (swap ((itciPE n).symm ⟨g, hg⟩).1 ((itciPE n).symm ⟨g, hg⟩).2)))
      (itcqGenC (n * n)) := by
  set m := n * n with hm
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; simp [m] at hg
  have hnm : n ≤ m := Nat.le_mul_self n
  set i : Fin n := ((itciPE n).symm ⟨g, hg⟩).1
  set j : Fin n := ((itciPE n).symm ⟨g, hg⟩).2
  have hi : (i : ℕ) = g / n := rfl
  have hj : (j : ℕ) = g % n := rfl
  have hil := i.isLt
  have hjl := j.isLt
  have hiw := wt_nat_le (i : ℕ)
  have hjw := wt_nat_le (j : ℕ)
  have hnw := wt_nat_le n
  have hgw := wt_nat_le g
  have hR : (natList (List.range m)).wt ≤ 5 * (m + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => (List.mem_range.1 hx).le) (by simp)
  have hsq := itcq_sq_le (m := m)
  have hc3 := wt_list3_le (.nat n) (.nat i) (.nat j)
  -- the inner map
  have hin : ∀ x ∈ (List.range m).map Val.nat, FunDet P sw
      (.list [.list [.nat n, .nat i, .nat j], x]) (match x with
        | .nat t => .nat (itcqS i j (t % n) + n * itcqS i j (t / n))
        | _ => .nat 0) (103 * (100 * (m + 2) + 1)) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    have ht' := List.mem_range.1 ht
    have h2 := wt_list2_le (.list [.nat n, .nat i, .nat j]) (.nat t)
    have htw := wt_nat_le t
    exact itcq_swF_spec hsw i.isLt j.isLt ht' (by omega)
  have hM := map_det hmp (c := .list [.nat n, .nat i, .nat j]) hin
  rw [itcq_swV i j, ← encFun, ← encPerm_eq_encFun] at hM
  -- the body
  set A := Val.list [.list [.nat n, natList (List.range m)], .nat g]
  have hA1 : (Val.list [.nat n, natList (List.range m)]).wt ≤ A.wt := st_wt_mem (by simp [A])
  have hA2 : A.wt ≤ _ := wt_list2_le (.list [.nat n, natList (List.range m)]) (.nat g)
  have hA3 := wt_list2_le (.nat n) (natList (List.range m))
  have hAg : (Val.nat g).wt ≤ A.wt := st_wt_mem (by simp [A])
  set W := 100 * (m + 2) ^ 2
  have hm2 := itcq_m_sq m
  have hlin : m + 2 ≤ (m + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hAW : A.wt ≤ W := by omega
  have a0 : StDC P [A] (arg 0) (.list [.nat n, natList (List.range m)]) 3 0 W :=
    StDC.arg (vs := [.list [.nat n, natList (List.range m)], .nat g]) rfl (by omega) (by omega)
      (by omega)
  have a1 : StDC P [A] (arg 1) (.nat g) 3 0 W :=
    StDC.arg (vs := [.list [.nat n, natList (List.range m)], .nat g]) rfl (by omega) (by omega)
      (by omega)
  have gn := StDC.get a0 (StDC.nat 0 (by omega)) (v := .nat n) rfl (by omega)
  have gR := StDC.get a0 (StDC.nat 1 (by omega)) (v := natList (List.range m)) rfl (by omega)
  have dv := StDC.arith a1 gn (op := .div) (z := i) hi.symm (by omega)
  have md := StDC.arith a1 gn (op := .mod) (z := j) hj.symm (by omega)
  have c3 := StDC.mk3 gn dv md (by omega) (by omega)
  have hc2 := wt_list2_le (.list [.nat n, .nat i, .nat j]) (natList (List.range m))
  have c2 := StDC.mk2 c3 gR (by omega) (by omega)
  have hPw : (encPerm (itciD n (swap i j))).wt ≤ 4 * (m + 1) ^ 2 := wt_encPerm_le _
  have cl := StDC.call c2 hM (by omega)
  refine StDC.funDet hf cl ?_
  -- the cost
  simp only [List.length_map, List.length_range]
  have hin2 : (Val.list [.list [.nat n, .nat i, .nat j], natList (List.range m)]).wt ≤
      30 * (m + 2) ^ 2 := by omega
  have k1 : m * (103 * (100 * (m + 2) + 1)) ≤ 20000 * (m + 2) ^ 2 := by
    have : m * (100 * (m + 2) + 1) ≤ 101 * (m + 2) ^ 2 := by
      have := itcq_m_sq m
      calc m * (100 * (m + 2) + 1) = 100 * (m * (m + 2)) + m := by ring
        _ ≤ 101 * (m + 2) ^ 2 := by nlinarith
    calc m * (103 * (100 * (m + 2) + 1)) = 103 * (m * (100 * (m + 2) + 1)) := by ring
      _ ≤ 20000 * (m + 2) ^ 2 := by omega
  have k2 : mapK * (m + 1) * ((Val.list [.list [.nat n, .nat i, .nat j], natList (List.range m)]).wt
      + (encPerm (itciD n (swap i j))).wt + 1) ≤ 35000 * (m + 2) ^ 3 := by
    have h1 : (Val.list [.list [.nat n, .nat i, .nat j], natList (List.range m)]).wt
      + (encPerm (itciD n (swap i j))).wt + 1 ≤ 35 * (m + 2) ^ 2 := by omega
    have := itcq_mul_sq m
    calc mapK * (m + 1) * (_ + _ + 1) ≤ 1000 * (m + 1) * (35 * (m + 2) ^ 2) :=
          Nat.mul_le_mul_left _ h1
      _ = 35000 * ((m + 1) * (m + 2) ^ 2) := by ring
      _ ≤ 35000 * (m + 2) ^ 3 := Nat.mul_le_mul_left _ this
  have := itcq_sq_cube m
  show _ ≤ 10 ^ 6 * (m + 2) ^ 3
  have hW3 : 21 * (W + 1) ≤ 2200 * (m + 2) ^ 3 := by omega
  have k2' : mapK * (m + 1) * ((Val.list [.list [.nat n, .nat i, .nat j],
      .list ((List.range m).map Val.nat)]).wt + (encPerm (itciD n (swap i j))).wt + 1) ≤
      35000 * (m + 2) ^ 3 := k2
  omega

end Prog

end GI.Impl
