import Workspace.Impl.AggItemHvMath
import Workspace.Impl.AggItemC1Sch
import Workspace.Impl.AggItemC1Chk

/-!
# Case 2a as a program: the generators of `A`

`A = certLift ⊓ π⁻¹(Alt(Φ) × Alt(C))` is, inside the graph of `certLift`, the kernel of the sign
of the `Φ`-side (`it_hv_A_graph`). From the graph pairs `fx` of `certLift` and the indicator of
`Φ`, `itHvAF` computes graph pairs of `A`:

1. the first pair `t` whose `Φ`-side is odd (`find` with the test `itHvChF`);
2. if there is none, `fx` itself (`it_hv_chi_all`);
3. otherwise the Schreier list `itHvSch χ t fx` (`it_hv_schreier`), entry by entry.

The `Φ`-side of a label permutation is a map over the points (`itHvRsF`), its sign the parity of
its inversions (`it_par_spec`, given as a hypothesis), and products of pairs are two
compositions (`itHvPmF`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {k q : ℕ}

/-! ### Products of pairs -/

/-- On `[pairV a, pairV b]`: `pairV (a * b)`. -/
def itHvPmF (cmp : ℕ) : Expr :=
  mk2 (.call cmp (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0))))
    (.call cmp (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))))

/-- The cost bound of a product of pairs. -/
def itHvPmC (n : ℕ) : ℕ := 10 ^ 6 * (n + 1) ^ 3

theorem it_hvPm_spec {P : Program} {f cmp : ℕ} (hf : P.funs[f]? = some (itHvPmF cmp))
    (hcmp : P.HasAt cmp (composeFuns cmp)) (a b : Perm (Fin k) × Perm (Fin q)) :
    FunDet P f (.list [pairV a, pairV b]) (pairV (a * b)) (itHvPmC (k + q)) := by
  have wa := wt_pairV_le a
  have wb := wt_pairV_le b
  have wab := wt_pairV_le (a * b)
  set D := k + q + 1
  have hD1 : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hk2 : (k + 1) ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq2 : (q + 1) ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk3 : (k + 1) ^ 3 ≤ D ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq3 : (q + 1) ^ 3 ≤ D ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hD23 : D ^ 2 ≤ D ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 200 * D ^ 2
  have hin := st_wt_list2 wa wb
  have wa1 := wt_encPerm_le a.1
  have wa2 := wt_encPerm_le a.2
  have wb1 := wt_encPerm_le b.1
  have wb2 := wt_encPerm_le b.2
  have w1 := wt_encPerm_le (a.1 * b.1)
  have w2 := wt_encPerm_le (a.2 * b.2)
  set vs : List Val := [pairV a, pairV b]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have g00 := StDC.get g0 (StDC.nat 0 (by omega)) (v := encPerm a.1) rfl (by omega)
  have g01 := StDC.get g0 (StDC.nat 1 (by omega)) (v := encPerm a.2) rfl (by omega)
  have g10 := StDC.get g1 (StDC.nat 0 (by omega)) (v := encPerm b.1) rfl (by omega)
  have g11 := StDC.get g1 (StDC.nat 1 (by omega)) (v := encPerm b.2) rfl (by omega)
  have l1 := wt_list2_le (encPerm a.1) (encPerm b.1)
  have l2 := wt_list2_le (encPerm a.2) (encPerm b.2)
  have c1 := StDC.call (StDC.mk2 g00 g10 (by omega) (by omega)) (compose_spec hcmp a.1 b.1)
    (by omega)
  have c2 := StDC.call (StDC.mk2 g01 g11 (by omega) (by omega)) (compose_spec hcmp a.2 b.2)
    (by omega)
  have l3 := wt_list2_le (encPerm (a.1 * b.1)) (encPerm (a.2 * b.2))
  have o := StDC.mk2 c1 c2 (by omega) (by omega)
  refine StDC.funDet hf o ?_
  have hW : W = 200 * D ^ 2 := rfl
  have hDe : (k + q + 1) ^ 3 = D ^ 3 := rfl
  unfold itHvPmC permK
  omega

/-! ### The `Φ`-side of a label permutation -/

open Classical in
/-- The indicator of `Φ`, as a value. -/
noncomputable def itHvInd (Φ : Finset (Fin q)) : Val := encFun fun i : Fin q => if i ∈ Φ then 1 else 0

theorem it_hvInd_wt (Φ : Finset (Fin q)) : (itHvInd Φ).wt ≤ 5 * (q + 1) ^ 2 :=
  it_encFun_wt _ fun i => by have := i.isLt; split_ifs <;> omega

/-- On `[[encPerm σ, ind], i]`: `σ i` if `i ∈ Φ`, else `i`. -/
def itHvRsB : Expr :=
  .ite (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (.get (arg 0) (.nat 0)) (arg 1)) (arg 1)

open Classical in
/-- The `Φ`-side as a function. -/
noncomputable def itHvRf (Φ : Finset (Fin q)) (σ : Perm (Fin q)) (i : Fin q) : ℕ :=
  if i ∈ Φ then σ i else i

theorem itHvRf_le (Φ : Finset (Fin q)) (σ : Perm (Fin q)) (i : Fin q) : itHvRf Φ σ i ≤ q := by
  unfold itHvRf; split_ifs <;> omega

theorem it_hvRsB_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itHvRsB)
    (Φ : Finset (Fin q)) (σ : Perm (Fin q)) (i : Fin q) :
    FunDet P f (.list [.list [encPerm σ, itHvInd Φ], .nat i]) (.nat (itHvRf Φ σ i))
      (5000 * (q + 1) ^ 2) := by
  classical
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hs := wt_encPerm_le σ
  have hI := it_hvInd_wt Φ
  have hc := wt_list2_le (encPerm σ) (itHvInd Φ)
  have hin := wt_list2_le (.list [encPerm σ, itHvInd Φ]) (.nat i)
  have hi := wt_nat_le (i : ℕ)
  have hsi := wt_nat_le (σ i : ℕ)
  have hil := i.isLt
  have hsil := (σ i).isLt
  set W := 50 * (q + 1) ^ 2
  set vs : List Val := [.list [encPerm σ, itHvInd Φ], .nat i]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gI := StDC.get g0 (StDC.nat 1 (by omega)) (v := itHvInd Φ) rfl (by omega)
  have gS := StDC.get g0 (StDC.nat 0 (by omega)) (v := encPerm σ) rfl (by omega)
  have cI := StDC.get gI g1 (v := .nat (if i ∈ Φ then 1 else 0))
    (by simp) (by
      have h1 := wt_nat_le (if i ∈ Φ then 1 else 0)
      have h2 : (if i ∈ Φ then 1 else 0) ≤ 1 := by split_ifs <;> omega
      omega)
  have o := StDC.ite (v := .nat (itHvRf Φ σ i)) cI
    (fun h => by
      have hm : i ∈ Φ := by by_contra hn; simp [hn] at h
      have e : itHvRf Φ σ i = σ i := by simp [itHvRf, hm]
      rw [e]
      exact StDC.get gS g1 (v := .nat (σ i)) (by simp) (by omega))
    (fun h => by
      have hm : i ∉ Φ := by intro hn; simp [hn] at h
      have e : itHvRf Φ σ i = i := by simp [itHvRf, hm]
      rw [e]; exact g1)
    (by have := wt_nat_le (itHvRf Φ σ i); have := itHvRf_le Φ σ i; omega)
  refine StDC.funDet hf o ?_
  have hW : W = 50 * (q + 1) ^ 2 := rfl
  omega

/-- On `[encPerm σ, ind]`: the `Φ`-side of `σ` as a list of images. -/
def itHvRsF (rng mp : ℕ) : Expr :=
  .letE (.call rng (.length (.get (.var 0) (.nat 0)))) (.call mp (mk2 (.var 0) (.var 1)))

/-- The cost bound of the `Φ`-side. -/
def itHvRsC (q : ℕ) : ℕ := 10 ^ 7 * (q + 1) ^ 3

theorem it_hvRs_spec {P : Program} {f rng mp b : ℕ} (hf : P.funs[f]? = some (itHvRsF rng mp))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp b))
    (hb : P.funs[b]? = some itHvRsB) (Φ : Finset (Fin q)) (σ : Perm (Fin q)) :
    FunDet P f (.list [encPerm σ, itHvInd Φ]) (encFun (itHvRf Φ σ)) (itHvRsC q) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq23 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs := wt_encPerm_le σ
  have hI := it_hvInd_wt Φ
  have hc := wt_list2_le (encPerm σ) (itHvInd Φ)
  have hR := it_range_wt (q := q)
  have hO := it_encFun_wt (itHvRf Φ σ) (itHvRf_le Φ σ)
  set W := 100 * (q + 1) ^ 2
  have v0 : StDC P [.list [encPerm σ, itHvInd Φ]] (.var 0) (.list [encPerm σ, itHvInd Φ]) 1 0 W :=
    StDC.var' rfl (by omega)
  have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := encPerm σ) rfl (by omega)
  have l0 := StDC.length g0 (by simp; omega)
  have el : ((List.finRange q).map fun i => Val.nat (σ i : ℕ)).length = q := by simp
  simp only [encPerm, el] at l0
  have d1 := StDC.call l0 (st_range_det hrng q) (by omega)
  set E1 : List Val := [.list [encPerm σ, itHvInd Φ], natList (List.range q)]
  have u0 : StDC P E1 (.var 0) (.list [encPerm σ, itHvInd Φ]) 1 0 W := StDC.var' rfl (by omega)
  have u1 : StDC P E1 (.var 1) (natList (List.range q)) 1 0 W := StDC.var' rfl (by omega)
  have h2 := wt_list2_le (.list [encPerm σ, itHvInd Φ]) (natList (List.range q))
  have hM := it_tab hmp (c := .list [encPerm σ, itHvInd Φ]) (itHvRf Φ σ) (itHvRf_le Φ σ)
    (fun i => it_hvRsB_spec hb Φ σ i)
  have d2 := StDC.call (StDC.mk2 u0 u1 (by omega) (by omega)) hM (by omega)
  refine StDC.funDet hf (StDC.letE d1 d2 (by omega)) ?_
  have hW : W = 100 * (q + 1) ^ 2 := rfl
  have c1 : q * (5000 * (q + 1) ^ 2) ≤ 5000 * (q + 1) ^ 3 := by
    calc q * (5000 * (q + 1) ^ 2) ≤ (q + 1) * (5000 * (q + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 5000 * (q + 1) ^ 3 := by ring
  have c2 : mapK * (q + 1) * (2 * (Val.list [encPerm σ, itHvInd Φ]).wt + 22 * (q + 1) ^ 2) ≤
      mapK * (q + 1) * (100 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have c3 : mapK * (q + 1) * (100 * (q + 1) ^ 2) = 10 ^ 5 * (q + 1) ^ 3 := by
    simp only [mapK]; ring
  have c4 : 10000 * (q + 1) ^ 3 ≤ 10000 * (q + 1) ^ 3 := le_rfl
  unfold itHvRsC
  omega

open Classical in
/-- The `Φ`-side as a list of images is the encoding of `itHvR`, when `σ` maps `Φ` onto
itself. -/
theorem itHvRf_eq {Φ : Finset (Fin q)} {σ : Perm (Fin q)} (h : ∀ a, σ a ∈ Φ ↔ a ∈ Φ) :
    encFun (itHvRf Φ σ) = encPerm (itHvR Φ σ) := by
  rw [encPerm_eq_encFun]
  congr 1
  funext i
  rw [itHvRf, itHvR_apply h]
  split_ifs <;> rfl

/-! ### The sign test -/

/-- The `Φ`-side of the label part of `s` is odd. -/
noncomputable def itHvOdd (Φ : Finset (Fin q)) (s : Perm (Fin k) × Perm (Fin q)) : Bool :=
  decide (itpNInv (itHvR Φ s.2) % 2 = 1)

theorem itHvOdd_iff (Φ : Finset (Fin q)) (s : Perm (Fin k) × Perm (Fin q)) :
    itHvOdd Φ s = true ↔ itHvChi Φ s ≠ 1 := by
  rw [itHvOdd, decide_eq_true_iff, itHvChi, ne_eq, itp_sign_one_iff, Nat.even_iff]
  omega

/-- On `[ind, pairV s]`: whether the `Φ`-side of `s` is odd. -/
def itHvChF (rs par : ℕ) : Expr :=
  .call par (.call rs (mk2 (.get (arg 1) (.nat 1)) (arg 0)))

/-- The cost bound of the sign test. -/
def itHvChC (k q : ℕ) : ℕ := 10 ^ 8 * (k + q + 1) ^ 4

theorem it_hvCh_spec {P : Program} {f rs rng mp b par : ℕ} (hf : P.funs[f]? = some (itHvChF rs par))
    (hrs : P.funs[rs]? = some (itHvRsF rng mp))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp b))
    (hb : P.funs[b]? = some itHvRsB)
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (Φ : Finset (Fin q)) (s : Perm (Fin k) × Perm (Fin q)) (hs : ∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) :
    FunDet P f (.list [itHvInd Φ, pairV s]) (boolVal (itHvOdd Φ s)) (itHvChC k q) := by
  have ws := wt_pairV_le s
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hD1 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq2 : (q + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq3 : (q + 1) ^ 3 ≤ (k + q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq4 : (q + 1) ^ 4 ≤ (k + q + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hD23 : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hD34 : (k + q + 1) ^ 3 ≤ (k + q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hI := it_hvInd_wt Φ
  have hin := wt_list2_le (itHvInd Φ) (pairV s)
  have h2 := wt_encPerm_le s.2
  have hR := wt_encPerm_le (itHvR Φ s.2)
  have hRl := wt_list2_le (encPerm s.2) (itHvInd Φ)
  have hb2 := wt_boolVal_le (itHvOdd Φ s)
  set W := 200 * (k + q + 1) ^ 2
  set vs : List Val := [itHvInd Φ, pairV s]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have g1 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have g12 := StDC.get g1 (StDC.nat 1 (by omega)) (v := encPerm s.2) rfl (by omega)
  have hRs := it_hvRs_spec hrs hrng hmp hb Φ s.2
  rw [itHvRf_eq hs] at hRs
  have cR := StDC.call (StDC.mk2 g12 g0 (by omega) (by omega)) hRs (by omega)
  have e : Val.nat (itpNInv (itHvR Φ s.2) % 2) = boolVal (itHvOdd Φ s) := by
    simp only [boolVal, itHvOdd, Val.nat.injEq]
    have := Nat.mod_two_eq_zero_or_one (itpNInv (itHvR Φ s.2))
    rcases this with h | h <;> simp [h]
  have cP := StDC.call cR (hpar (itHvR Φ s.2)) (by rw [e]; omega)
  rw [e] at cP
  refine StDC.funDet hf cP ?_
  have hW : W = 200 * (k + q + 1) ^ 2 := rfl
  unfold itHvChC itHvRsC itParC
  omega

/-! ### The Schreier list, entry by entry -/

/-- Entry `j` of the program's Schreier list: `t t` for `j = 0`; then, for `s = S[(j-1)/2]`,
`s` and `t s t` if the `Φ`-side of `s` is even, `s t` and `t s` if it is odd. -/
noncomputable def itHvSchE (Φ : Finset (Fin q)) (t : Perm (Fin k) × Perm (Fin q))
    (S : List (Perm (Fin k) × Perm (Fin q))) (j : ℕ) : Perm (Fin k) × Perm (Fin q) :=
  if j = 0 then t * t else
  if h : (j - 1) / 2 < S.length then
    if itHvOdd Φ S[(j - 1) / 2] then
      (if (j - 1) % 2 = 0 then S[(j - 1) / 2] * t else t * S[(j - 1) / 2])
    else (if (j - 1) % 2 = 0 then S[(j - 1) / 2] else t * S[(j - 1) / 2] * t)
  else 1

theorem itHvSchE_mem (Φ : Finset (Fin q)) (t : Perm (Fin k) × Perm (Fin q))
    (S : List (Perm (Fin k) × Perm (Fin q))) (g : Perm (Fin k) × Perm (Fin q)) :
    g ∈ (List.range (2 * S.length + 1)).map (itHvSchE Φ t S) ↔
      g ∈ itHvSch (itHvChi Φ) t S := by
  rw [it_hv_mem_sch, List.mem_map]
  have hodd : ∀ s : Perm (Fin k) × Perm (Fin q), itHvOdd Φ s = true ↔ itHvChi Φ s ≠ 1 :=
    itHvOdd_iff Φ
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h0 : j = 0
    · left; simp [itHvSchE, h0]
    right
    have hj' : (j - 1) / 2 < S.length := by have := List.mem_range.1 hj; omega
    refine ⟨S[(j - 1) / 2], List.getElem_mem hj', ?_⟩
    rw [itHvSchE, if_neg h0, dif_pos hj']
    by_cases hs : itHvOdd Φ S[(j - 1) / 2] = true
    · right; refine ⟨(hodd _).1 hs, ?_⟩; rw [if_pos hs]; split_ifs <;> simp
    · left
      refine ⟨by by_contra hc; exact hs ((hodd _).2 hc), ?_⟩
      rw [if_neg hs]; split_ifs <;> simp
  · rintro (rfl | ⟨s, hs, h⟩)
    · exact ⟨0, List.mem_range.2 (by omega), by simp [itHvSchE]⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    have e0 : (2 * i + 1 - 1) / 2 = i := by omega
    have e1 : (2 * i + 2 - 1) / 2 = i := by omega
    have m0 : 2 * i + 1 ∈ List.range (2 * S.length + 1) := List.mem_range.2 (by omega)
    have m1 : 2 * i + 2 ∈ List.range (2 * S.length + 1) := List.mem_range.2 (by omega)
    have v0 : itHvSchE Φ t S (2 * i + 1) = if itHvOdd Φ S[i] then S[i] * t else S[i] := by
      rw [itHvSchE, if_neg (by omega), dif_pos (by omega)]; simp only [e0]
      split_ifs <;> first | rfl | omega
    have v1 : itHvSchE Φ t S (2 * i + 2) =
        if itHvOdd Φ S[i] then t * S[i] else t * S[i] * t := by
      rw [itHvSchE, if_neg (by omega), dif_pos (by omega)]; simp only [e1]
      split_ifs <;> first | rfl | omega
    have hn : ∀ {s}, itHvChi Φ s = 1 → itHvOdd Φ s = false := fun h => by
      cases hb : itHvOdd Φ _ with
      | false => rfl
      | true => exact absurd h ((hodd _).1 hb)
    rcases h with ⟨h1, rfl | rfl⟩ | ⟨h1, rfl | rfl⟩
    · exact ⟨_, m0, by rw [v0, hn h1]; rfl⟩
    · exact ⟨_, m1, by rw [v1, hn h1]; rfl⟩
    · exact ⟨_, m0, by rw [v0, if_pos ((hodd _).2 h1)]⟩
    · exact ⟨_, m1, by rw [v1, if_pos ((hodd _).2 h1)]⟩

/-- `if` on the number `0`: only the second branch runs. -/
theorem itHv_ite0 {P : Program} {env : List Val} {W : ℕ} {c t e : Expr} {v : Val} {nc ne Ec Ee : ℕ}
    (hc : StDC P env c (.nat 0) nc Ec W) (he : StDC P env e v ne Ee W) (hw : v.wt ≤ W) :
    StDC P env (.ite c t e) v (nc + 0 + ne + 1) (Ec + 0 + Ee) W :=
  StDC.ite (nt := 0) (Et := 0) hc (fun h => absurd rfl h) (fun _ => he) hw

/-- `if` on a nonzero number: only the first branch runs. -/
theorem itHv_ite1 {P : Program} {env : List Val} {W : ℕ} {c t e : Expr} {v : Val} {x nc nt Ec Et : ℕ}
    (hc : StDC P env c (.nat x) nc Ec W) (hx : x ≠ 0) (ht : StDC P env t v nt Et W)
    (hw : v.wt ≤ W) :
    StDC P env (.ite c t e) v (nc + nt + 0 + 1) (Ec + Et + 0) W :=
  StDC.ite (ne := 0) (Ee := 0) hc (fun _ => ht) (fun h => absurd h hx) hw

/-- On `[[T, S, ind], j]`: entry `j` of the Schreier list. -/
def itHvSchB (ch pm : ℕ) : Expr :=
  let T := Expr.get (arg 0) (.nat 0)
  let S := Expr.get (arg 0) (.nat 1)
  let ind := Expr.get (arg 0) (.nat 2)
  let j1 := Expr.arith .sub (arg 1) (.nat 1)
  let s := Expr.get S (.arith .div j1 (.nat 2))
  .ite (arg 1)
    (.ite (.call ch (mk2 ind s))
      (.ite (.arith .mod j1 (.nat 2)) (.call pm (mk2 T s)) (.call pm (mk2 s T)))
      (.ite (.arith .mod j1 (.nat 2)) (.call pm (mk2 (.call pm (mk2 T s)) T)) s))
    (.call pm (mk2 T T))

/-- The weight of a list of pairs. -/
theorem it_hv_pairs_wt {S : List (Perm (Fin k) × Perm (Fin q))} {m : ℕ} (hS : S.length ≤ m) :
    (Val.list (S.map pairV)).wt ≤ m * (45 * (k + q + 1) ^ 2) + 4 := by
  have h := wt_list_le_of (S.map pairV) (c := 22 * (k + q + 1) ^ 2) (fun v hv => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv; exact wt_pairV_le p)
  rw [List.length_map] at h
  have : S.length * (2 * (22 * (k + q + 1) ^ 2) + 1) ≤ m * (45 * (k + q + 1) ^ 2) := by
    have : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact Nat.mul_le_mul hS (by omega)
  omega

/-- The cost bound of one Schreier entry, for a size `M ≥ |S| + k + q + 1`. -/
def itHvSchBC (M : ℕ) : ℕ := 10 ^ 9 * M ^ 4

set_option maxHeartbeats 4000000 in
theorem it_hvSchB_spec {P : Program} {f ch pm : ℕ} (hf : P.funs[f]? = some (itHvSchB ch pm))
    (Φ : Finset (Fin q)) (hch : ∀ s : Perm (Fin k) × Perm (Fin q), (∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) →
      FunDet P ch (.list [itHvInd Φ, pairV s]) (boolVal (itHvOdd Φ s)) (itHvChC k q))
    (hpm : ∀ a b : Perm (Fin k) × Perm (Fin q),
      FunDet P pm (.list [pairV a, pairV b]) (pairV (a * b)) (itHvPmC (k + q)))
    (t : Perm (Fin k) × Perm (Fin q)) {S : List (Perm (Fin k) × Perm (Fin q))}
    (hS : ∀ s ∈ S, ∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) {M : ℕ} (hM : S.length + k + q + 1 ≤ M)
    {j : ℕ} (hj : j < 2 * S.length + 1) :
    FunDet P f (.list [.list [pairV t, .list (S.map pairV), itHvInd Φ], .nat j])
      (pairV (itHvSchE Φ t S j)) (itHvSchBC M) := by
  have hD1 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hDM2 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hDM3 : (k + q + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hDM4 : (k + q + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hM1 : 1 ≤ M := by omega
  have hM12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq2 : (q + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hSw := it_hv_pairs_wt (le_refl S.length) (k := k) (q := q)
  have hSM : S.length * (45 * (k + q + 1) ^ 2) ≤ 45 * M ^ 3 := by
    calc S.length * (45 * (k + q + 1) ^ 2) ≤ M * (45 * M ^ 2) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 45 * M ^ 3 := by ring
  have hI := it_hvInd_wt Φ
  have hT := wt_pairV_le t
  have hc := wt_list3_le (pairV t) (.list (S.map pairV)) (itHvInd Φ)
  have hjw := wt_nat_le j
  have hin := wt_list2_le (.list [pairV t, .list (S.map pairV), itHvInd Φ]) (.nat j)
  set W := 2000 * M ^ 3
  set vs : List Val := [.list [pairV t, .list (S.map pairV), itHvInd Φ], .nat j]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gJ := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gT := StDC.get g0 (StDC.nat 0 (by omega)) (v := pairV t) rfl (by omega)
  have gS := StDC.get g0 (StDC.nat 1 (by omega)) (v := .list (S.map pairV)) rfl (by omega)
  have gI := StDC.get g0 (StDC.nat 2 (by omega)) (v := itHvInd Φ) rfl (by omega)
  have hpw : ∀ p : Perm (Fin k) × Perm (Fin q), (pairV p).wt ≤ 22 * (k + q + 1) ^ 2 :=
    wt_pairV_le
  have h2 : ∀ a b : Val, a.wt ≤ 22 * (k + q + 1) ^ 2 → b.wt ≤ 22 * (k + q + 1) ^ 2 →
      (Val.list [a, b]).wt ≤ W := fun a b ha hb => by
    have := wt_list2_le a b; omega
  have hW : W = 2000 * M ^ 3 := rfl
  have hE := hpw (itHvSchE Φ t S j)
  by_cases h0 : j = 0
  · subst h0
    have hv : itHvSchE Φ t S 0 = t * t := by simp [itHvSchE]
    refine StDC.funDet hf (itHv_ite0 (v := pairV (itHvSchE Φ t S 0)) gJ (by
        rw [hv]
        exact StDC.call (StDC.mk2 gT gT (h2 _ _ hT hT) (by omega)) (hpm t t) (by
          have := hpw (t * t); omega)) (by omega)) ?_
    unfold itHvSchBC itHvPmC
    nlinarith
  have hj2 : (j - 1) / 2 < S.length := by omega
  set s := S[(j - 1) / 2]
  have hsS : s ∈ S := List.getElem_mem hj2
  have hs := hpw s
  have gD := StDC.arith' (op := .div) (StDC.arith' (op := .sub) gJ (StDC.nat 1 (by omega)) rfl
    (by simp only [GI.Machine.BinOp.eval]; omega)) (StDC.nat 2 (by omega)) rfl
    (by simp only [GI.Machine.BinOp.eval]; omega)
  have gM := StDC.arith' (op := .mod) (StDC.arith' (op := .sub) gJ (StDC.nat 1 (by omega)) rfl
    (by simp only [GI.Machine.BinOp.eval]; omega)) (StDC.nat 2 (by omega)) rfl
    (by simp only [GI.Machine.BinOp.eval]; have := Nat.mod_lt (j - 1) (by omega : 2 > 0); omega)
  have gs := StDC.get gS gD (v := pairV s) (by simp [s, hj2]) (by omega)
  have cC := StDC.call (StDC.mk2 gI gs (by have := wt_list2_le (itHvInd Φ) (pairV s); omega)
    (by omega)) (hch s (hS s hsS)) (by have := wt_boolVal_le (itHvOdd Φ s); omega)
  refine StDC.funDet hf (itHv_ite1 (v := pairV (itHvSchE Φ t S j)) gJ h0 (by
      exact StDC.ite (v := pairV (itHvSchE Φ t S j)) cC (fun hp => by
        have hp' : itHvOdd Φ s = true := by
          cases hb : itHvOdd Φ s
          · rw [hb] at hp; exact absurd rfl hp
          · rfl
        exact StDC.ite gM
          (fun hm => by
            have hv : itHvSchE Φ t S j = t * s := by
              rw [itHvSchE, if_neg h0, dif_pos hj2, if_pos hp']
              simp only [GI.Machine.BinOp.eval] at hm
              rw [if_neg hm]
            rw [hv]
            exact StDC.call (StDC.mk2 gT gs (h2 _ _ hT hs) (by omega)) (hpm t s)
              (by have := hpw (t * s); omega))
          (fun hm => by
            have hv : itHvSchE Φ t S j = s * t := by
              rw [itHvSchE, if_neg h0, dif_pos hj2, if_pos hp']
              simp only [GI.Machine.BinOp.eval] at hm
              rw [if_pos hm]
            rw [hv]
            exact StDC.call (StDC.mk2 gs gT (h2 _ _ hs hT) (by omega)) (hpm s t)
              (by have := hpw (s * t); omega)) (by omega)) (fun hp => by
        have hp' : itHvOdd Φ s = false := by
          cases hb : itHvOdd Φ s
          · rfl
          · rw [hb] at hp; exact absurd hp (by decide)
        exact StDC.ite gM
          (fun hm => by
            have hv : itHvSchE Φ t S j = t * s * t := by
              rw [itHvSchE, if_neg h0, dif_pos hj2, if_neg (by rw [hp']; decide)]
              simp only [GI.Machine.BinOp.eval] at hm
              rw [if_neg hm]
            rw [hv]
            have c1 := StDC.call (StDC.mk2 gT gs (h2 _ _ hT hs) (by omega)) (hpm t s)
              (by have := hpw (t * s); omega)
            exact StDC.call (StDC.mk2 c1 gT (h2 _ _ (hpw _) hT) (by omega)) (hpm (t * s) t)
              (by have := hpw (t * s * t); omega))
          (fun hm => by
            have hv : itHvSchE Φ t S j = s := by
              rw [itHvSchE, if_neg h0, dif_pos hj2, if_neg (by rw [hp']; decide)]
              simp only [GI.Machine.BinOp.eval] at hm
              rw [if_pos hm]
            rw [hv]; exact gs) (by omega)) (by omega)) (by omega)) ?_
  unfold itHvSchBC itHvPmC itHvChC
  nlinarith

/-! ### The whole list -/

/-- On `[T, S, ind]`: the Schreier list. -/
def itHvSchF (rng mp : ℕ) : Expr :=
  .letE (.call rng (.arith .add (.arith .mul (.nat 2) (.length (.get (.var 0) (.nat 1)))) (.nat 1)))
    (.call mp (mk2 (.var 0) (.var 1)))

/-- The cost bound of the Schreier list, for a size `M ≥ |S| + k + q + 1`. -/
def itHvSchC (M : ℕ) : ℕ := 10 ^ 11 * M ^ 5

/-- The Schreier entries as values. -/
noncomputable def itHvSchV (Φ : Finset (Fin q)) (t : Perm (Fin k) × Perm (Fin q))
    (S : List (Perm (Fin k) × Perm (Fin q))) : Val → Val
  | .nat j => pairV (itHvSchE Φ t S j)
  | _ => .nat 0

set_option maxHeartbeats 4000000 in
theorem it_hvSch_spec {P : Program} {f rng mp sb ch pm : ℕ} (hf : P.funs[f]? = some (itHvSchF rng mp))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp sb))
    (hsb : P.funs[sb]? = some (itHvSchB ch pm))
    (Φ : Finset (Fin q)) (hch : ∀ s : Perm (Fin k) × Perm (Fin q), (∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) →
      FunDet P ch (.list [itHvInd Φ, pairV s]) (boolVal (itHvOdd Φ s)) (itHvChC k q))
    (hpm : ∀ a b : Perm (Fin k) × Perm (Fin q),
      FunDet P pm (.list [pairV a, pairV b]) (pairV (a * b)) (itHvPmC (k + q)))
    (t : Perm (Fin k) × Perm (Fin q)) {S : List (Perm (Fin k) × Perm (Fin q))}
    (hS : ∀ s ∈ S, ∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) {M : ℕ} (hM : S.length + k + q + 1 ≤ M) :
    FunDet P f (.list [pairV t, .list (S.map pairV), itHvInd Φ])
      (.list (((List.range (2 * S.length + 1)).map (itHvSchE Φ t S)).map pairV)) (itHvSchC M) := by
  have hD1 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hDM2 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM1 : 1 ≤ M := by omega
  have hM12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM45 : M ^ 4 ≤ M ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq2 : (q + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  set m := S.length with hm
  have hSw := it_hv_pairs_wt (le_refl m) (k := k) (q := q) (S := S)
  have hSM : m * (45 * (k + q + 1) ^ 2) ≤ 45 * M ^ 3 := by
    calc m * (45 * (k + q + 1) ^ 2) ≤ M * (45 * M ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 45 * M ^ 3 := by ring
  have hI := it_hvInd_wt Φ
  have hT := wt_pairV_le t
  set c : Val := .list [pairV t, .list (S.map pairV), itHvInd Φ] with hcdef
  have hc : c.wt ≤ 2 * ((pairV t).wt + (Val.list (S.map pairV)).wt + (itHvInd Φ).wt) + 7 :=
    wt_list3_le _ _ _
  have hcw : c.wt ≤ 200 * M ^ 3 := by omega
  set O := ((List.range (2 * m + 1)).map (itHvSchE Φ t S)).map pairV
  have hOl : ((List.range (2 * m + 1)).map (itHvSchE Φ t S)).length ≤ 2 * m + 1 := by simp
  have hOw : (Val.list O).wt ≤ (2 * m + 1) * (45 * (k + q + 1) ^ 2) + 4 := it_hv_pairs_wt hOl
  have hOM : (2 * m + 1) * (45 * (k + q + 1) ^ 2) ≤ 135 * M ^ 3 := by
    calc (2 * m + 1) * (45 * (k + q + 1) ^ 2) ≤ (3 * M) * (45 * M ^ 2) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 135 * M ^ 3 := by ring
  have hR := it_range_wt (q := 2 * m + 1)
  have hR2 : 5 * (2 * m + 1 + 1) ^ 2 ≤ 45 * M ^ 2 := by
    have : (2 * m + 1 + 1) ^ 2 ≤ (3 * M) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (3 * M) ^ 2 = 9 * M ^ 2 := by ring
    omega
  set W := 1000 * M ^ 3
  have hMap : FunDet P mp (.list [c, natList (List.range (2 * m + 1))]) (.list O)
      ((2 * m + 1) * itHvSchBC M + mapK * (2 * m + 1 + 1) * (1000 * M ^ 3)) := by
    have h := map_det hmp (c := c) (xs := (List.range (2 * m + 1)).map Val.nat)
      (F := itHvSchV Φ t S) (B := itHvSchBC M)
      (fun v hv => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
        exact it_hvSchB_spec hsb Φ hch hpm t hS hM (List.mem_range.1 hj))
    have e : ((List.range (2 * m + 1)).map Val.nat).map (itHvSchV Φ t S) = O := by
      simp only [O, List.map_map]; rfl
    rw [e] at h
    refine h.mono ?_
    have h2 := wt_list2_le c (natList (List.range (2 * m + 1)))
    simp only [List.length_map, List.length_range]
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    show (Val.list [c, natList (List.range (2 * m + 1))]).wt + (Val.list O).wt + 1 ≤ _
    omega
  have v0 : StDC P [c] (.var 0) c 1 0 W := StDC.var' rfl (by omega)
  have g1 := StDC.get v0 (StDC.nat 1 (by omega)) (v := .list (S.map pairV)) rfl (by omega)
  have l1 := StDC.length g1 (by simp only [List.length_map]; have := wt_nat_le m; omega)
  simp only [List.length_map, ← hm] at l1
  have a1 := StDC.arith (op := .mul) (StDC.nat 2 (by omega)) l1 rfl (by
    simp only [GI.Machine.BinOp.eval]; have := wt_nat_le (2 * m); omega)
  have a2 := StDC.arith (op := .add) a1 (StDC.nat 1 (by omega)) rfl (by
    simp only [GI.Machine.BinOp.eval]; have := wt_nat_le (2 * m + 1); omega)
  have d1 := StDC.call a2 (st_range_det hrng (2 * m + 1)) (by omega)
  set E1 : List Val := [c, natList (List.range (2 * m + 1))]
  have u0 : StDC P E1 (.var 0) c 1 0 W := StDC.var' rfl (by omega)
  have u1 : StDC P E1 (.var 1) (natList (List.range (2 * m + 1))) 1 0 W := StDC.var' rfl (by omega)
  have h2 := wt_list2_le c (natList (List.range (2 * m + 1)))
  have d2 := StDC.call (StDC.mk2 u0 u1 (by omega) (by omega)) hMap (by omega)
  refine StDC.funDet hf (StDC.letE d1 d2 (by omega)) ?_
  have hW : W = 1000 * M ^ 3 := rfl
  have c1 : (2 * m + 1) * itHvSchBC M ≤ 3 * 10 ^ 9 * M ^ 5 := by
    unfold itHvSchBC
    calc (2 * m + 1) * (10 ^ 9 * M ^ 4) ≤ (3 * M) * (10 ^ 9 * M ^ 4) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 3 * 10 ^ 9 * M ^ 5 := by ring
  have c2 : mapK * (2 * m + 1 + 1) * (1000 * M ^ 3) ≤ 4 * 10 ^ 6 * M ^ 4 := by
    calc mapK * (2 * m + 1 + 1) * (1000 * M ^ 3) ≤ 1000 * (4 * M) * (1000 * M ^ 3) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = 4 * 10 ^ 6 * M ^ 4 := by ring
  have c3 : 10000 * (2 * m + 1 + 1) ^ 3 ≤ 64 * 10 ^ 4 * M ^ 3 := by
    have : (2 * m + 1 + 1) ^ 3 ≤ (4 * M) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e : (4 * M) ^ 3 = 64 * M ^ 3 := by ring
    omega
  unfold itHvSchC
  omega

/-! ### The generators of `A` -/

/-- The program's generating list of the kernel of the `Φ`-sign: the Schreier list for the first
pair with an odd `Φ`-side, or `S` if there is none. -/
noncomputable def itHvAL (Φ : Finset (Fin q)) (S : List (Perm (Fin k) × Perm (Fin q))) :
    List (Perm (Fin k) × Perm (Fin q)) :=
  if h : S.findIdx (itHvOdd Φ) < S.length then
    (List.range (2 * S.length + 1)).map (itHvSchE Φ S[S.findIdx (itHvOdd Φ)] S)
  else S

/-- **The program's list generates the kernel of the `Φ`-sign**, when every label part maps `Φ`
onto itself: by Schreier's lemma (`it_hv_schreier`) with the first odd pair, or, if there is
none, since then every element is even (`it_hv_chi_all`). -/
theorem it_hvAL_mem {Φ : Finset (Fin q)} {S : List (Perm (Fin k) × Perm (Fin q))}
    (hinv : ∀ σ ∈ gens (S.map Prod.snd), ∀ a, σ a ∈ Φ ↔ a ∈ Φ) (p : Perm (Fin k) × Perm (Fin q)) :
    p ∈ Subgroup.closure {g | g ∈ itHvAL Φ S} ↔
      p ∈ Subgroup.closure {s | s ∈ S} ∧ itHvChi Φ p = 1 := by
  have hmul := it_hv_chi_mul hinv
  unfold itHvAL
  split_ifs with h
  · have hodd := List.findIdx_getElem (w := h)
    set t := S[S.findIdx (itHvOdd Φ)]
    have htS : t ∈ Subgroup.closure {s | s ∈ S} := Subgroup.subset_closure (List.getElem_mem h)
    have hχt : itHvChi Φ t = -1 := (it_units_cases _).resolve_left ((itHvOdd_iff Φ t).1 hodd)
    rw [← it_hv_schreier (itHvChi Φ) hmul htS hχt p]
    constructor <;> intro hp <;>
      [exact (Subgroup.closure_le _).2 (fun g hg => Subgroup.subset_closure
        ((itHvSchE_mem Φ t S g).1 hg)) hp;
       exact (Subgroup.closure_le _).2 (fun g hg => Subgroup.subset_closure
        ((itHvSchE_mem Φ t S g).2 hg)) hp]
  · have hall : ∀ s ∈ S, itHvChi Φ s = 1 := by
      intro s hs
      by_contra hc
      have h1 : itHvOdd Φ s = true := (itHvOdd_iff Φ s).2 hc
      exact h (List.findIdx_lt_length_of_exists ⟨s, hs, h1⟩)
    exact ⟨fun hp => ⟨hp, it_hv_chi_all (itHvChi Φ) hmul hall p hp⟩, fun hp => hp.1⟩

/-- **The graph pairs of `A`**: for graph pairs `fs` of `F` whose label parts map `Φ` onto itself,
the program's list `itHvAL Φ fs` is a list of graph pairs of `F ⊓ π⁻¹(Alt(Φ) × Alt(C))`. -/
theorem it_hvAL_pairGens {Ω C : Type} {e : Ω ≃ Fin k} {S : GI.Algorithm.State Ω C}
    {L : GiantLabels S} {F : Subgroup (Perm Ω)} {Φ : Finset (Fin L.q)}
    {fs : List (Perm (Fin k) × Perm (Fin L.q))} (hfs : PairGens e L F fs)
    (hinv : ∀ σ ∈ gens (fs.map Prod.snd), ∀ a, σ a ∈ Φ ↔ a ∈ Φ) :
    PairGens e L (F ⊓ L.lift (GI.Rectangle.evenSides Φ Φᶜ)) (itHvAL Φ fs) := by
  unfold PairGens
  ext p
  rw [it_hvAL_mem hinv p, it_hv_A_graph hfs hinv p]

/-! ### The program -/

theorem it_pairV_injective : Function.Injective (pairV (k := k) (q := q)) := by
  intro a b h
  simp only [pairV, Val.list.injEq, List.cons.injEq] at h
  exact Prod.ext (encPerm_injective h.1) (encPerm_injective h.2.1)

open Classical in
/-- The find test on values. -/
noncomputable def itHvOddV (Φ : Finset (Fin q)) (x : Val) : Bool :=
  decide (∃ s : Perm (Fin k) × Perm (Fin q), pairV s = x ∧ itHvOdd Φ s = true)

theorem itHvOddV_pairV (Φ : Finset (Fin q)) (s : Perm (Fin k) × Perm (Fin q)) :
    itHvOddV (k := k) Φ (pairV s) = itHvOdd Φ s := by
  classical
  unfold itHvOddV
  cases h : itHvOdd Φ s
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro s' hs' h'
    rw [it_pairV_injective hs'] at h'
    rw [h] at h'; exact absurd h' (by decide)
  · simp only [decide_eq_true_eq]
    exact ⟨s, rfl, h⟩

/-- On `[ind, S]`: graph pairs of the kernel of the `Φ`-sign. -/
def itHvAF (fd sch : ℕ) : Expr :=
  .letE (.call fd (.var 0))
    (.ite (.arith .eq (.var 1) (.length (.get (.var 0) (.nat 1))))
      (.get (.var 0) (.nat 1))
      (.call sch (mk3 (.get (.get (.var 0) (.nat 1)) (.var 1)) (.get (.var 0) (.nat 1))
        (.get (.var 0) (.nat 0)))))

/-- The cost bound of `itHvAF`, for a size `M ≥ |S| + k + q + 1`. -/
def itHvAC (M : ℕ) : ℕ := 10 ^ 12 * M ^ 5

set_option maxHeartbeats 4000000 in
/-- **The generators of `A` as a program.** -/
theorem it_hvA_spec {P : Program} {f fd sch rng mp sb ch pm : ℕ} (hf : P.funs[f]? = some (itHvAF fd sch))
    (hfd : P.HasAt fd (findFuns fd ch)) (hsch : P.funs[sch]? = some (itHvSchF rng mp))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp sb))
    (hsb : P.funs[sb]? = some (itHvSchB ch pm))
    (Φ : Finset (Fin q)) (hch : ∀ s : Perm (Fin k) × Perm (Fin q), (∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) →
      FunDet P ch (.list [itHvInd Φ, pairV s]) (boolVal (itHvOdd Φ s)) (itHvChC k q))
    (hpm : ∀ a b : Perm (Fin k) × Perm (Fin q),
      FunDet P pm (.list [pairV a, pairV b]) (pairV (a * b)) (itHvPmC (k + q)))
    {S : List (Perm (Fin k) × Perm (Fin q))}
    (hS : ∀ s ∈ S, ∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) {M : ℕ} (hM : S.length + k + q + 1 ≤ M) :
    FunDet P f (.list [itHvInd Φ, .list (S.map pairV)]) (.list ((itHvAL Φ S).map pairV))
      (itHvAC M) := by
  have hD1 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hDM2 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hDM4 : (k + q + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hM1 : 1 ≤ M := by omega
  have hM12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM45 : M ^ 4 ≤ M ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq2 : (q + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  set m := S.length with hm
  have hSw := it_hv_pairs_wt (le_refl m) (k := k) (q := q) (S := S)
  have hSM : m * (45 * (k + q + 1) ^ 2) ≤ 45 * M ^ 3 := by
    calc m * (45 * (k + q + 1) ^ 2) ≤ M * (45 * M ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 45 * M ^ 3 := by ring
  have hI := it_hvInd_wt Φ
  set v : Val := .list [itHvInd Φ, .list (S.map pairV)] with hvdef
  have hv : v.wt ≤ 2 * ((itHvInd Φ).wt + (Val.list (S.map pairV)).wt) + 6 := wt_list2_le _ _
  -- the find call
  have hfind : FunDet P fd v (.nat (S.findIdx (itHvOdd Φ)))
      (m * itHvChC k q + loopModK * (m + 1) * (v.wt + 2 * m + 3)) := by
    have h := find_spec hfd (c := itHvInd Φ) (xs := S.map pairV) (q := itHvOddV (k := k) Φ)
      (B := fun _ => itHvChC k q) (fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
        rw [itHvOddV_pairV]
        exact hch s (hS s hs))
    have e : (S.map pairV).findIdx (itHvOddV (k := k) Φ) = S.findIdx (itHvOdd Φ) := by
      rw [List.findIdx_map]
      congr 1
      funext s
      exact itHvOddV_pairV Φ s
    refine h.mono fun w c ⟨h1, h2⟩ => ⟨by rw [h1, e], ?_⟩
    rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at h2
    exact h2
  have hfi := wt_nat_le (S.findIdx (itHvOdd Φ))
  have hfl : S.findIdx (itHvOdd Φ) ≤ m := List.findIdx_le_length
  set W := 1000 * M ^ 3
  have hW : W = 1000 * M ^ 3 := rfl
  have v0 : StDC P [v] (.var 0) v 1 0 W := StDC.var' rfl (by omega)
  have d1 := StDC.call v0 hfind (by omega)
  set E1 : List Val := [v, .nat (S.findIdx (itHvOdd Φ))]
  have u0 : StDC P E1 (.var 0) v 1 0 W := StDC.var' rfl (by omega)
  have u1 : StDC P E1 (.var 1) (.nat (S.findIdx (itHvOdd Φ))) 1 0 W := StDC.var' rfl (by omega)
  have uS := StDC.get u0 (StDC.nat 1 (by omega)) (v := .list (S.map pairV)) rfl (by omega)
  have uI := StDC.get u0 (StDC.nat 0 (by omega)) (v := itHvInd Φ) rfl (by omega)
  have uL := StDC.length uS (by simp only [List.length_map]; have := wt_nat_le m; omega)
  simp only [List.length_map, ← hm] at uL
  have hO := it_hv_pairs_wt (S := itHvAL Φ S) (m := 2 * m + 1) (k := k) (q := q) (by
    unfold itHvAL
    split_ifs
    · rw [List.length_map, List.length_range]
    · omega)
  have hOM : (2 * m + 1) * (45 * (k + q + 1) ^ 2) ≤ 135 * M ^ 3 := by
    calc (2 * m + 1) * (45 * (k + q + 1) ^ 2) ≤ (3 * M) * (45 * M ^ 2) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 135 * M ^ 3 := by ring
  have hAw : (Val.list ((itHvAL Φ S).map pairV)).wt ≤ W := by omega
  by_cases h : S.findIdx (itHvOdd Φ) < m
  · have cmp := StDC.arith (op := .eq) u1 uL (z := 0) (by
      simp only [GI.Machine.BinOp.eval]; rw [if_neg (by omega)]) (by
      have := wt_nat_le 0; omega)
    set t := S[S.findIdx (itHvOdd Φ)]
    have ht := wt_pairV_le t
    have gt := StDC.get uS u1 (v := pairV t)
      (by rw [List.getElem?_map, List.getElem?_eq_getElem h]; rfl) (by omega)
    have hin := wt_list3_le (pairV t) (.list (S.map pairV)) (itHvInd Φ)
    have hsch' := it_hvSch_spec hsch hrng hmp hsb Φ hch hpm t hS hM
    have eA : itHvAL Φ S = (List.range (2 * S.length + 1)).map (itHvSchE Φ t S) := by
      rw [itHvAL, dif_pos h]
    rw [← eA] at hsch'
    refine StDC.funDet hf (StDC.letE d1 (itHv_ite0 cmp (StDC.call (StDC.mk3 gt uS uI (by omega)
      (by omega)) hsch' hAw) hAw) hAw) ?_
    have c1 : m * itHvChC k q ≤ 10 ^ 8 * M ^ 5 := by
      unfold itHvChC
      calc m * (10 ^ 8 * (k + q + 1) ^ 4) ≤ M * (10 ^ 8 * M ^ 4) := Nat.mul_le_mul (by omega) (by omega)
        _ = 10 ^ 8 * M ^ 5 := by ring
    have c2 : loopModK * (m + 1) * (v.wt + 2 * m + 3) ≤ 10 ^ 6 * M ^ 4 := by
      calc loopModK * (m + 1) * (v.wt + 2 * m + 3) ≤ 1000 * M * (200 * M ^ 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by simp [loopModK]) (by omega)) (by omega)
        _ = 2 * 10 ^ 5 * M ^ 4 := by ring
        _ ≤ 10 ^ 6 * M ^ 4 := by omega
    unfold itHvAC itHvSchC
    omega
  · have hfe : S.findIdx (itHvOdd Φ) = m := by omega
    have cmp := StDC.arith (op := .eq) u1 uL (z := 1) (by
      simp only [GI.Machine.BinOp.eval]; rw [if_pos hfe]) (by
      have := wt_nat_le 1; omega)
    have eA : itHvAL Φ S = S := by rw [itHvAL, dif_neg h]
    rw [← eA] at uS
    refine StDC.funDet hf (StDC.letE d1 (itHv_ite1 cmp (by decide) uS hAw) hAw) ?_
    have c1 : m * itHvChC k q ≤ 10 ^ 8 * M ^ 5 := by
      unfold itHvChC
      calc m * (10 ^ 8 * (k + q + 1) ^ 4) ≤ M * (10 ^ 8 * M ^ 4) := Nat.mul_le_mul (by omega) (by omega)
        _ = 10 ^ 8 * M ^ 5 := by ring
    have c2 : loopModK * (m + 1) * (v.wt + 2 * m + 3) ≤ 10 ^ 6 * M ^ 4 := by
      calc loopModK * (m + 1) * (v.wt + 2 * m + 3) ≤ 1000 * M * (200 * M ^ 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by simp [loopModK]) (by omega)) (by omega)
        _ = 2 * 10 ^ 5 * M ^ 4 := by ring
        _ ≤ 10 ^ 6 * M ^ 4 := by omega
    unfold itHvAC
    omega

end GI.Impl
