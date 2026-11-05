module

public import Workspace.Impl.AggItemCfTr
public import Workspace.Lang.Prims.StabOrbit
public import Workspace.Lang.Lib.Loop

@[expose] public section

/-!
# The degree of transitivity as a program

`itCfDegFuns b jps` (51 functions) runs on `[⟨H⟩, ⟨xs⟩]`, a group `H` by generators (with the
identity first, `encGroup`) and a list `xs` of the points of an `H`-invariant set `Φ` without
repeats. It walks the stabilizer chain along `xs` (`AggItemCfTr.lean`). The accumulator is
`[⟨G_i⟩, d, f]`: `G_i` is the stabilizer in `H` of the first `i` points, `d` the first failing
step found so far, and `f = 1` once a step has failed. At step `i` (while `f = 0`) the program
`stabOrbitFuns` returns the stabilizer of `xs[i]` in `G_i`, which is `G_{i+1}`, and the orbit of
`xs[i]` under `G_i`. The step holds exactly when the orbit has `|Φ| - i` points
(`itCf_chain_iff_length`). The stabilizers come from the cited **PointwiseStab** (inside
`stabOrbitFuns`); its precondition is a group value, which the accumulator always holds.

`itCf_deg_spec`: the result is `[⟨G⟩, transDeg H Φ, f]`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab PointwiseStab)

variable {q : ℕ}

/-- The step of the chain loop, on `[[⟨H⟩, ⟨xs⟩], i, [⟨G_i⟩, d, f]]`. -/
def itCfDegStep (so : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 2)) (arg 2)
    (.letE (.call so (mk2 (.get (arg 2) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))))
      (.ite (.arith .eq (.length (.get (.var 1) (.nat 1)))
          (.arith .sub (.length (.get (arg 0) (.nat 1))) (arg 1)))
        (mk3 (.get (.var 1) (.nat 0)) (.arith .add (arg 1) (.nat 1)) (.nat 0))
        (mk3 (.get (arg 2) (.nat 0)) (arg 1) (.nat 1))))

/-- The chain loop at base `b` (51 functions), with the pointwise stabilizer at `jps`. -/
def itCfDegFuns (b jps : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) (mk3 (.get (.var 0) (.nat 0)) (.nat 0) (.nat 0))
    (itCfDegStep (b + 3)) ++ stabOrbitFuns (b + 3) jps

theorem itCf_pstab_nil (H : Subgroup (Perm (Fin q))) : pointwiseStab H [] = H := by
  ext g
  simp [pointwiseStab]

/-- The weight bound of the accumulator's group. -/
def itCfDegG (gv : Val) (q : ℕ) : ℕ := gv.wt + 700 * (q + 1) ^ 6

/-- The weight bound of the accumulator. -/
def itCfDegM (gv : Val) (q N : ℕ) : ℕ := 2 * (itCfDegG gv q + 2 * N + 10) + 7

/-- The argument size bound of one stabilizer call. -/
def itCfDegY (gv : Val) (q N : ℕ) : ℕ := 2 * (itCfDegG gv q + q + 2) + 8

/-- The cost bound of one step. -/
noncomputable def itCfDegD (hps : PointwiseStab) (a gv : Val) (q N : ℕ) : ℕ :=
  (pointwiseStabPrim hps).boundSize (itCfDegY gv q N + 3) +
    stabOrbitK * itCfDegY gv q N ^ 9 + 1000 * (a.wt + itCfDegM gv q N + N + 10)

/-- The invariant of the chain loop after `i` steps. -/
def ItCfDegInv (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q)) (xs : List (Fin q)) (G : ℕ)
    (i : ℕ) (acc : Val) : Prop :=
  ∃ (gs : List (Perm (Fin q))) (d f : ℕ), acc = .list [encGroup gs, .nat d, .nat f] ∧
    (encGroup gs).wt ≤ G ∧ d ≤ i ∧ f ≤ 1 ∧
    (∀ x : ℕ → Fin q, (∀ l (hl : l < xs.length), x l = xs[l]) → ∀ j < d, ItCfChain H Φ x j) ∧
    (f = 0 → d = i ∧ gens gs = pointwiseStab H (xs.take i)) ∧
    (f ≠ 0 → d < xs.length ∧
      ∀ x : ℕ → Fin q, (∀ l (hl : l < xs.length), x l = xs[l]) → ¬ ItCfChain H Φ x d)

theorem itCf_len_eq_card {Φ : Finset (Fin q)} {xs : List (Fin q)} (hnd : xs.Nodup)
    (hmem : ∀ b, b ∈ xs ↔ b ∈ Φ) : xs.length = Φ.card := by
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1; ext b; simp [hmem]

theorem itCf_encPts_eq (xs : List (Fin q)) :
    encPts xs = .list (xs.map fun j : Fin q => Val.nat j.val) := by
  unfold encPts; congr 1
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all

theorem itCf_encPts_get (xs : List (Fin q)) (i : ℕ) (hi : i < xs.length) :
    (xs.map fun j : Fin q => Val.nat j)[i]? = some (.nat xs[i]) := by
  simp [hi]

set_option maxHeartbeats 4000000 in
/-- One step of the chain loop keeps the invariant. -/
theorem itCf_degStep_spec (hps : PointwiseStab) {P : Program} {so jps : ℕ}
    (hso : P.HasAt so (stabOrbitFuns so jps)) (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hs : List (Perm (Fin q))) (Φ : Finset (Fin q)) (xs : List (Fin q))
    (hpres : ∀ h ∈ gens hs, ∀ a ∈ Φ, h a ∈ Φ) (hnd : xs.Nodup) (hmem : ∀ b, b ∈ xs ↔ b ∈ Φ)
    {i : ℕ} (hi : i < xs.length) {acc : Val}
    (hinv : ItCfDegInv (gens hs) Φ xs (itCfDegG (encGroup hs) q) i acc) :
    EvalAll P [.list [.list [encGroup hs, encPts xs], .nat i, acc]] (itCfDegStep so)
      (fun acc' cb => ItCfDegInv (gens hs) Φ xs (itCfDegG (encGroup hs) q) (i + 1) acc' ∧
        cb ≤ itCfDegD hps (.list [encGroup hs, encPts xs]) (encGroup hs) q xs.length +
          100 * ((Val.list [encGroup hs, encPts xs]).wt + xs.length +
            itCfDegM (encGroup hs) q xs.length + 1)) := by
  have hN : xs.length = Φ.card := itCf_len_eq_card hnd hmem
  obtain ⟨gs, d, f, rfl, hgw, hdi, hf1le, hok, hf0, hf1⟩ := hinv
  set a : Val := .list [encGroup hs, encPts xs] with ha
  set acc : Val := .list [encGroup gs, .nat d, .nat f] with hacc
  set sa : Val := .list [a, .nat i, acc] with hsa
  have esa : (Val.list [a, .nat i, acc]).wt = sa.wt := rfl
  have eacc : (Val.list [encGroup gs, .nat d, .nat f]).wt = acc.wt := rfl
  have ea : (Val.list [encGroup hs, encPts xs]).wt = a.wt := rfl
  have hep : encPts xs = .list (xs.map fun j : Fin q => Val.nat j.val) := itCf_encPts_eq xs
  -- weights
  have wa : a.wt < sa.wt := wt_le_wt_list (by simp [hsa])
  have wacc : acc.wt < sa.wt := wt_le_wt_list (by simp [hsa])
  have wi : (Val.nat i).wt < sa.wt := wt_le_wt_list (by simp [hsa])
  have wg0 : (encGroup hs).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wxs : (encPts xs).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wgs : (encGroup gs).wt < acc.wt := wt_le_wt_list (by simp [hacc])
  have hnq := S_le_wt_encGroup hs
  have hq1 : q + 1 ≤ (encGroup hs).wt := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hnq
  have hlen : xs.length < (encPts xs).wt := by
    have := length_lt_wt_list (xs.map fun j : Fin q => Val.nat j)
    simp only [List.length_map] at this
    rw [hep]; exact this
  have h3 := wt_list3_le (encGroup gs) (.nat d) (.nat f)
  have hsa3 := wt_list3_le a (.nat i) acc
  have wnd := wt_nat_le d
  have wnf := wt_nat_le f
  have wni := wt_nat_le i
  have hfle : f ≤ 1 ∨ True := Or.inr trivial
  -- reading the flag
  have dacc := Det.arg' (P := P) (vs := [a, .nat i, acc]) (rest := []) (j := 2) (v := acc) rfl
  have dflag := Det.get' dacc (Det.nat 2) (v := .nat f) (show [encGroup gs, Val.nat d,
    Val.nat f][2]? = some (.nat f) from rfl)
  refine EvalAll.ite dflag (fun _ _ h => ⟨f, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  cases hx
  by_cases hf : f = 0
  swap
  · -- a step has failed already: keep the accumulator
    rw [if_neg hf]
    obtain ⟨hdN, hno⟩ := hf1 hf
    refine EvalAll.mono dacc fun w cb ⟨hw, hcb⟩ => ⟨⟨gs, d, f, hw, hgw, by omega, hf1le, hok,
      fun h => absurd h hf, fun _ => ⟨hdN, hno⟩⟩, ?_⟩
    subst hw
    unfold itCfDegG at hgw
    unfold itCfDegD itCfDegM itCfDegG
    omega
  rw [if_pos hf]
  subst hf
  obtain ⟨hdi', hgens⟩ := hf0 rfl
  subst d
  -- the stabilizer and the orbit of `(xs[i]'hi)` in `G_i`
  have eL : (Val.list (xs.map fun j : Fin q => Val.nat j.val)).wt = (encPts xs).wt := by rw [hep]
  have wxi := wt_nat_le ((xs[i]'hi) : ℕ)
  have hxi := (xs[i]'hi).isLt
  have hpw := wt_list2_le (encGroup gs) (.nat (xs[i]'hi))
  have dpt := Det.get' (Det.get' (Det.arg' (P := P) (vs := [a, .nat i, acc]) (rest := [])
      (j := 0) (v := a) rfl) (Det.nat 1) (v := .list (xs.map fun j : Fin q => Val.nat j.val))
        (show [encGroup hs, encPts xs][1]? = some (.list (xs.map fun j : Fin q => Val.nat j.val))
          by rw [hep]; rfl))
    (Det.arg' (P := P) (vs := [a, .nat i, acc]) (rest := []) (j := 1) (v := .nat i) rfl)
    (itCf_encPts_get xs i hi)
  have dG := Det.get' dacc (Det.nat 0) (v := encGroup gs) (show [encGroup gs, Val.nat i,
    Val.nat 0][0]? = some (encGroup gs) from rfl)
  have darg : Det P [sa] (mk2 (.get (arg 2) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1)))
      (.list [encGroup gs, .nat (xs[i]'hi)]) (30 * sa.wt + 100) :=
    (Det.mk2 dG dpt).mono (by omega)
  have hGV : GroupVal q (encGroup gs) (pointwiseStab (gens hs) (xs.take i)) := ⟨gs, rfl, hgens⟩
  have hSO := stabOrbit_spec hps hso hj hGV (xs[i]'hi)
  have hcall : EvalAll P [sa]
      (.call so (mk2 (.get (arg 2) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))))
      (fun w c => (∃ v1 v2, w = .list [v1, v2] ∧
          GroupVal q v1 (pointwiseStab (pointwiseStab (gens hs) (xs.take i)) [(xs[i]'hi)]) ∧
          ∃ O : List (Fin q), v2 = encPts O ∧ O.Nodup ∧
            ∀ y, y ∈ O ↔ ∃ g ∈ pointwiseStab (gens hs) (xs.take i), g (xs[i]'hi) = y) ∧
        w.wt ≤ 700 * (q + 1) ^ 6 ∧
        c ≤ 30 * sa.wt + 100 +
          ((pointwiseStabPrim hps).boundSize ((Val.list [encGroup gs, .nat (xs[i]'hi)]).wt + 3) +
            stabOrbitK * (Val.list [encGroup gs, .nat (xs[i]'hi)]).wt ^ 9) + w.wt + 1) :=
    EvalAll.call_funAll darg fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact hSO.mono fun w c hw => ⟨hw.1, hw.2.1, by omega⟩
  refine EvalAll.letE hcall fun v ca hv => ?_
  obtain ⟨⟨v1, v2, rfl, hv1, O, rfl, hOnd, hOm⟩, hww, hcSO⟩ := hv
  -- the size test
  have wv1 : v1.wt < (Val.list [v1, encPts O]).wt := wt_le_wt_list (by simp)
  have wO : (encPts O).wt < (Val.list [v1, encPts O]).wt := wt_le_wt_list (by simp)
  have eLO : (Val.list (O.map fun j : Fin q => Val.nat j.val)).wt = (encPts O).wt := by
    rw [itCf_encPts_eq]
  set R : Val := .list [v1, encPts O] with hR
  have dres := Det.var' (P := P) (env := [sa, R]) (i := 1) (v := R) rfl
  have dlenO := Det.length (Det.get' dres (Det.nat 1)
    (v := .list (O.map fun j : Fin q => Val.nat j.val)) (show [v1, encPts O][1]? =
    some (.list (O.map fun j : Fin q => Val.nat j.val)) by rw [itCf_encPts_eq]; rfl))
  have dlenX := Det.length (Det.get' (Det.arg' (P := P) (vs := [a, .nat i, acc])
      (rest := [R]) (j := 0) (v := a) rfl) (Det.nat 1)
      (v := .list (xs.map fun j : Fin q => Val.nat j.val))
      (show [encGroup hs, encPts xs][1]? = some (.list (xs.map fun j : Fin q => Val.nat j.val))
        by rw [hep]; rfl))
  have dI := Det.arg' (P := P) (vs := [a, .nat i, acc]) (rest := [R]) (j := 1) (v := .nat i) rfl
  have elO : (O.map fun j : Fin q => Val.nat j.val).length = O.length := List.length_map _
  have elX : (xs.map fun j : Fin q => Val.nat j.val).length = xs.length := List.length_map _
  have hOl : O.length < (encPts O).wt := by
    have := length_lt_wt_list (O.map fun j : Fin q => Val.nat j.val)
    simp only [List.length_map] at this
    omega
  have dsub := Det.arith' (op := .sub) dlenX dI (z := xs.length - i) (by
    simp only [GI.Machine.BinOp.eval, elX])
  have dtest : Det P [sa, R] (.arith .eq (.length (.get (.var 1) (.nat 1)))
      (.arith .sub (.length (.get (arg 0) (.nat 1))) (arg 1)))
      (.nat (if O.length = xs.length - i then 1 else 0)) (20 * (sa.wt + R.wt) + 100) :=
    (Det.arith' (op := .eq) dlenO dsub (z := if O.length = xs.length - i then 1 else 0) (by
      simp only [GI.Machine.BinOp.eval, elO])).mono (by
        have := wt_nat_le (xs.length - i)
        have : (if O.length = xs.length - i then 1 else 0) ≤ 1 := by split_ifs <;> omega
        omega)
  -- the two outcomes
  have hstab : pointwiseStab (pointwiseStab (gens hs) (xs.take i)) [(xs[i]'hi)] =
      pointwiseStab (gens hs) (xs.take (i + 1)) := by
    rw [itCf_pstab_snoc, List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  have hchain : ∀ x : ℕ → Fin q, (∀ l (hl : l < xs.length), x l = xs[l]) →
      (ItCfChain (gens hs) Φ x i ↔ O.length = Φ.card - i) := fun x hx =>
    itCf_chain_iff_length hpres xs hnd hmem x hx hi O hOnd fun y => by
      rw [hOm y, hx i hi]
  obtain ⟨gs1, rfl, hgs1⟩ := hv1
  have w1R : (encGroup gs1).wt < R.wt := wt_le_wt_list (by simp [hR])
  have hG1 : (encGroup gs1).wt ≤ itCfDegG (encGroup hs) q := by unfold itCfDegG; omega
  have dG1 := Det.get' dres (Det.nat 0) (v := encGroup gs1) (show [encGroup gs1,
    encPts O][0]? = some (encGroup gs1) from rfl)
  have e3 := wt_list3_le (encGroup gs1) (.nat (i + 1)) (.nat 0)
  have e4 := wt_list3_le (encGroup gs) (.nat i) (.nat 1)
  have := wt_nat_le (i + 1)
  have := wt_nat_le 0
  have := wt_nat_le 1
  have dok : Det P [sa, R] (mk3 (.get (.var 1) (.nat 0)) (.arith .add (arg 1) (.nat 1)) (.nat 0))
      (.list [encGroup gs1, .nat (i + 1), .nat 0]) (20 * (sa.wt + R.wt) + 100) :=
    (Det.mk3 dG1 (Det.arith' (op := .add) dI (Det.nat 1) (z := i + 1) rfl) (Det.nat 0)).mono
      (by omega)
  have dG0 := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, acc])
      (rest := [R]) (j := 2) (v := acc) rfl) (Det.nat 0)
      (v := encGroup gs) (show [encGroup gs, Val.nat i, Val.nat 0][0]? = some (encGroup gs) from rfl)
  have dno : Det P [sa, R] (mk3 (.get (arg 2) (.nat 0)) (arg 1) (.nat 1))
      (.list [encGroup gs, .nat i, .nat 1]) (20 * (sa.wt + R.wt) + 100) :=
    (Det.mk3 dG0 dI (Det.nat 1)).mono (by omega)
  have hite := Det.ite' dtest dok dno
  refine EvalAll.mono hite fun w cb ⟨hw, hcb⟩ => ⟨?_, ?_⟩
  · subst hw
    by_cases hO : O.length = xs.length - i
    · rw [if_pos hO]
      simp only [one_ne_zero, if_false]
      refine ⟨gs1, i + 1, 0, rfl, ?_, le_rfl, by omega, fun x hx j hj => ?_, fun _ => ⟨rfl, ?_⟩,
        fun h => absurd rfl h⟩
      · exact hG1
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hok x hx j hj
        · exact (hchain x hx).2 (by omega)
      · rw [hgs1, hstab]
    · rw [if_neg hO]
      simp only [if_true]
      refine ⟨gs, i, 1, rfl, hgw, by omega, le_rfl, hok, fun h => absurd h one_ne_zero, fun _ =>
        ⟨hi, fun x hx hc => hO (by have := (hchain x hx).1 hc; omega)⟩⟩
  · -- the cost
    have eR : (Val.list [encGroup gs1, encPts O]).wt = R.wt := rfl
    have hY : (Val.list [encGroup gs, Val.nat (xs[i]'hi)]).wt ≤ itCfDegY (encGroup hs) q xs.length := by
      unfold itCfDegY
      omega
    have hbs : (pointwiseStabPrim hps).boundSize ((Val.list [encGroup gs, Val.nat (xs[i]'hi)]).wt + 3) ≤
        (pointwiseStabPrim hps).boundSize (itCfDegY (encGroup hs) q xs.length + 3) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have h9 : (Val.list [encGroup gs, Val.nat (xs[i]'hi)]).wt ^ 9 ≤
        itCfDegY (encGroup hs) q xs.length ^ 9 := Nat.pow_le_pow_left hY 9
    have h9' := Nat.mul_le_mul_left stabOrbitK h9
    have hGd : itCfDegG (encGroup hs) q = (encGroup hs).wt + 700 * (q + 1) ^ 6 := rfl
    have w1 : (Val.list [encGroup gs1, Val.nat (i + 1), Val.nat 0]).wt ≤
        itCfDegM (encGroup hs) q xs.length := by unfold itCfDegM; omega
    have w2 : (Val.list [encGroup gs, Val.nat i, Val.nat 1]).wt ≤
        itCfDegM (encGroup hs) q xs.length := by unfold itCfDegM; omega
    have hmx := max_le w1 w2
    have wv : w.wt ≤ itCfDegM (encGroup hs) q xs.length := by
      rw [hw]
      by_cases h : O.length = xs.length - i
      · rw [if_pos h, if_neg one_ne_zero]; exact w1
      · rw [if_neg h, if_pos rfl]; exact w2
    have e2 := wt_list2_le (encGroup gs1) (encPts O)
    have hsaw : sa.wt ≤ 2 * (a.wt + (i + 2) + acc.wt) + 7 := by omega
    have haccw : acc.wt ≤ itCfDegM (encGroup hs) q xs.length := by unfold itCfDegM; omega
    have hOq : (encPts O).wt ≤ R.wt := le_of_lt wO
    have hRM : R.wt ≤ 700 * (q + 1) ^ 6 := hww
    have hMv : 700 * (q + 1) ^ 6 ≤ itCfDegM (encGroup hs) q xs.length := by
      unfold itCfDegM; omega
    unfold itCfDegD
    omega

/-- The cost bound of the chain loop on `a = [⟨H⟩, ⟨xs⟩]`, with `N = |xs|`. -/
noncomputable def itCfDegC (hps : PointwiseStab) (a gv : Val) (q N : ℕ) : ℕ :=
  N * itCfDegD hps a gv q N + N * (100 * (a.wt + N + itCfDegM gv q N + 1)) +
    loopK * (N + 1) * (a.wt + N + itCfDegM gv q N + 1) + 100 * (a.wt + N + itCfDegM gv q N) + 300

/-- **The degree of transitivity as a program.** Let `H = ⟨hs⟩` map `Φ` into itself and let `xs`
list the points of `Φ` without repeats. On `[⟨H⟩, ⟨xs⟩]` the chain loop returns
`[⟨G⟩, transDeg H Φ, f]`. -/
theorem itCf_deg_spec (hps : PointwiseStab) {P : Program} {b jps : ℕ}
    (h : P.HasAt b (itCfDegFuns b jps)) (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hs : List (Perm (Fin q))) (Φ : Finset (Fin q)) (xs : List (Fin q))
    (hpres : ∀ h ∈ gens hs, ∀ a ∈ Φ, h a ∈ Φ) (hnd : xs.Nodup) (hmem : ∀ b, b ∈ xs ↔ b ∈ Φ) :
    FunAll P b (.list [encGroup hs, encPts xs]) (fun w cost => ∃ (gs : List (Perm (Fin q)))
      (f : ℕ), w = .list [encGroup gs, .nat (transDeg (gens hs) Φ), .nat f] ∧
      cost ≤ itCfDegC hps (.list [encGroup hs, encPts xs]) (encGroup hs) q xs.length) := by
  have hl : P.HasAt b (loopFuns b (.length (.get (.var 0) (.nat 1)))
      (mk3 (.get (.var 0) (.nat 0)) (.nat 0) (.nat 0)) (itCfDegStep (b + 3))) := h.left
  have hso : P.HasAt (b + 3) (stabOrbitFuns (b + 3) jps) := by
    simpa [loopFuns] using h.right
  have hN := itCf_len_eq_card hnd hmem
  have hep := itCf_encPts_eq xs
  set a : Val := .list [encGroup hs, encPts xs] with ha
  have ea : (Val.list [encGroup hs, encPts xs]).wt = a.wt := rfl
  have wg0 : (encGroup hs).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wxs : (encPts xs).wt < a.wt := wt_le_wt_list (by simp [ha])
  have hlen : xs.length < (encPts xs).wt := by
    have := length_lt_wt_list (xs.map fun j : Fin q => Val.nat j.val)
    simp only [List.length_map] at this
    rw [hep]; exact this
  have elX : (xs.map fun j : Fin q => Val.nat j.val).length = xs.length := List.length_map _
  have eL : (Val.list (xs.map fun j : Fin q => Val.nat j.val)).wt = (encPts xs).wt := by rw [hep]
  have dk0 := Det.length (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 1)
      (v := .list (xs.map fun j : Fin q => Val.nat j.val))
      (show [encGroup hs, encPts xs][1]? = some (.list (xs.map fun j : Fin q => Val.nat j.val))
        by rw [hep]; rfl))
  rw [elX] at dk0
  have dk : Det P [a] (.length (.get (.var 0) (.nat 1))) (.nat xs.length) (4 * a.wt + 20) :=
    dk0.mono (by omega)
  have h30 := wt_list3_le (encGroup hs) (.nat 0) (.nat 0)
  have w0 := wt_nat_le 0
  have dacc : Det P [a] (mk3 (.get (.var 0) (.nat 0)) (.nat 0) (.nat 0))
      (.list [encGroup hs, .nat 0, .nat 0]) (40 * a.wt + 200) :=
    (Det.mk3 (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 0)
      (v := encGroup hs) rfl) (Det.nat 0) (Det.nat 0)).mono (by omega)
  have hM : ∀ i acc, i ≤ xs.length →
      ItCfDegInv (gens hs) Φ xs (itCfDegG (encGroup hs) q) i acc →
      acc.wt ≤ itCfDegM (encGroup hs) q xs.length := by
    intro i acc hi hinv
    obtain ⟨gs, d, f, hacc, hgw, hdi, hf, -⟩ := hinv
    subst hacc
    have hgw' : (encGroup gs).wt ≤ itCfDegG (encGroup hs) q := hgw
    have hdi' : d ≤ i := hdi
    have := wt_list3_le (encGroup gs) (.nat d) (.nat f)
    have := wt_nat_le d
    have := wt_nat_le f
    unfold itCfDegM
    omega
  have h0 : ItCfDegInv (gens hs) Φ xs (itCfDegG (encGroup hs) q) 0
      (.list [encGroup hs, .nat 0, .nat 0]) :=
    ⟨hs, 0, 0, rfl, by unfold itCfDegG; omega, le_rfl, by omega,
      fun _ _ j hj => absurd hj (Nat.not_lt_zero _), fun _ => ⟨rfl, by
        rw [List.take_zero, itCf_pstab_nil]⟩, fun h => absurd rfl h⟩
  refine (loopFuns_spec hl dk dacc (Inv := ItCfDegInv (gens hs) Φ xs (itCfDegG (encGroup hs) q))
    (Step := fun i acc acc' cb => cb ≤ itCfDegD hps a (encGroup hs) q xs.length +
      100 * (a.wt + xs.length + itCfDegM (encGroup hs) q xs.length + 1)) h0
    fun i acc hi hinv => itCf_degStep_spec hps hso hj hs Φ xs hpres hnd hmem hi hinv).mono ?_
  rintro w cost ⟨cl, hlp, hcost⟩
  obtain ⟨hinv, hcl⟩ := hlp.le (fun i a a' cb _ _ hs => hs) hM
  have hw := hM xs.length w le_rfl hinv
  obtain ⟨gs, d, f, rfl, -, hdi, hf, hok, hf0, hf1⟩ := hinv
  refine ⟨gs, f, ?_, ?_⟩
  · -- the result is the degree
    have hd : d = transDeg (gens hs) Φ := by
      rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
      · have : Φ.card = 0 := by omega
        have := (transDeg_spec (gens hs) Φ).2
        omega
      · let x : ℕ → Fin q := fun l => xs.getD l (xs[0]'hpos)
        have hx : ∀ l (hl : l < xs.length), x l = xs[l] := fun l hl => by
          simp [x, List.getElem?_eq_getElem hl]
        have hxinj : ∀ i j, i < Φ.card → j < Φ.card → x i = x j → i = j := by
          intro i j hi hj e
          rw [hx i (by omega), hx j (by omega)] at e
          exact (hnd.getElem_inj_iff).1 e
        have hxΦ : ∀ i < Φ.card, x i ∈ Φ := fun i hi => by
          rw [hx i (by omega), ← hmem]; exact List.getElem_mem _
        refine (itCf_transDeg_eq hpres x hxΦ hxinj (d := d) (by omega) (hok x hx) fun hlt => ?_).symm
        by_cases hf' : f = 0
        · obtain ⟨rfl, -⟩ := hf0 hf'
          omega
        · exact (hf1 hf').2 x hx
    rw [hd]
  · rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcl
    have h4 := wt_list4_le a (.nat xs.length) (.nat 0) (.list [encGroup hs, .nat 0, .nat 0])
    have := wt_nat_le xs.length
    have hM7 : 7 ≤ itCfDegM (encGroup hs) q xs.length := by unfold itCfDegM; omega
    unfold itCfDegC
    generalize xs.length * itCfDegD hps a (encGroup hs) q xs.length = K1 at hcl ⊢
    generalize xs.length * (100 * (a.wt + xs.length + itCfDegM (encGroup hs) q xs.length + 1)) =
      K2 at hcl ⊢
    generalize loopK * (xs.length + 1) * (a.wt + xs.length + itCfDegM (encGroup hs) q xs.length + 1)
      = K3 at hcl ⊢
    omega

end GI.Impl
