import Workspace.Impl.VsFMatStep
import Workspace.Impl.VStabLinSift

/-!
# Matrix products over `𝔽_p` as a `GI.Lang` program

A matrix is the list of its rows (`natList` each). Row `a` of the product, started from a vector
`z`, is `vsFRowMul p a B z = z + ∑_k a_k B_k`, a fold of `vsFMulAcc` over the rows of `B`. The
product `A B` is `A.map (vsFRowMul p · B 0)`.

* `vsFRowFold_spec`: the fold, on `[[p, a], B, [0, z]]`, cost at most `3 · 10^6 (N + 1)^4`.
* `vsFRowF`, `vsFRow_spec`: one row, on `[[p, B, z], a]`, cost at most `4 · 10^6 (N + 1)^4`.
* `vsFMatMulFuns`, `vsFMatMul_spec`: the product, on `[[p, B, z], A]` (16 functions), cost at
  most `5 · 10^6 (N + 1)^5`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- The row `z + ∑_k a_k B_k`, modulo `p`. -/
def vsFRowMul (p : ℕ) (a : List ℕ) (Bm : List (List ℕ)) (z : List ℕ) : List ℕ :=
  (Bm.foldl (vsFMulAcc p a) (0, z)).2

theorem vsFMulAcc_foldl_fst (p : ℕ) (a : List ℕ) (L : List (List ℕ)) (acc : ℕ × List ℕ) :
    (L.foldl (vsFMulAcc p a) acc).1 = acc.1 + L.length := by
  induction L generalizing acc with
  | nil => simp
  | cons r L ih => rw [List.foldl_cons, ih]; simp [vsFMulAcc]; omega

theorem vsFMulAcc_foldl_length (p : ℕ) (a : List ℕ) (L : List (List ℕ)) (acc : ℕ × List ℕ) :
    (L.foldl (vsFMulAcc p a) acc).2.length = acc.2.length := by
  induction L generalizing acc with
  | nil => simp
  | cons r L ih => rw [List.foldl_cons, ih]; simp [vsFMulAcc, vsLin_length]

theorem vsFMulAcc_foldl_lt {p : ℕ} (hp : 0 < p) (a : List ℕ) (L : List (List ℕ))
    {acc : ℕ × List ℕ} (h : ∀ y ∈ acc.2, y < p) : ∀ y ∈ (L.foldl (vsFMulAcc p a) acc).2, y < p := by
  induction L generalizing acc with
  | nil => simpa using h
  | cons r L ih => rw [List.foldl_cons]; exact ih (vsLin_lt hp _ _)

theorem vsFMulAcc_take_succ (p : ℕ) (a : List ℕ) (L : List (List ℕ)) (acc : ℕ × List ℕ) (i : ℕ)
    (hi : i < L.length) :
    (L.take (i + 1)).foldl (vsFMulAcc p a) acc =
      vsFMulAcc p a ((L.take i).foldl (vsFMulAcc p a) acc) L[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-- The weight of a matrix with at most `N + 1` rows, of entries and lengths at most `N`. -/
theorem wt_vsFMat_le {N : ℕ} {Bm : List (List ℕ)} (hB : ∀ r ∈ Bm, ∀ y ∈ r, y ≤ N)
    (lB : ∀ r ∈ Bm, r.length ≤ N) (hl : Bm.length ≤ N + 1) :
    (Val.list (Bm.map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 := by
  have h := vs_wt_list_le_of (Bm.map natList) (c := 5 * (N + 1) ^ 2) (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ r hr rfl
    exact wt_natList_le_sq (hB r hr) (lB r hr))
  rw [List.length_map] at h
  have e : (N + 1) * (2 * (5 * (N + 1) ^ 2) + 1) ≤ 11 * (N + 1) ^ 3 := by
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e3 : (N + 1) ^ 3 = (N + 1) * (N + 1) ^ 2 := by ring
    rw [e3]; nlinarith
  have := Nat.mul_le_mul_right (2 * (5 * (N + 1) ^ 2) + 1) hl
  omega

/-- The hypotheses on a row `a`, a matrix `B` and a start vector `z`: entries of `a` and `z`
below `p`, entries and lengths at most `N`, rows of `B` at least as long as `z`, and at most as
many rows as `a` has entries. -/
structure VsFRowFits (p N : ℕ) (a : List ℕ) (Bm : List (List ℕ)) (z : List ℕ) : Prop where
  ha : ∀ y ∈ a, y < p
  la : a.length ≤ N
  hz : ∀ y ∈ z, y < p
  lz : z.length ≤ N
  hB : ∀ r ∈ Bm, ∀ y ∈ r, y ≤ N
  lB : ∀ r ∈ Bm, r.length ≤ N
  zB : ∀ r ∈ Bm, z.length ≤ r.length
  Ba : Bm.length ≤ a.length

/-- **The fold.** On `[[p, a], B, [0, z]]` it returns `[length B, z + ∑_k a_k B_k]`. -/
theorem vsFRowFold_spec {P : Program} {b st lin : ℕ} (h : P.HasAt b (foldlFuns b st))
    (hf : P.funs[st]? = some (vsFMulStepF lin)) (hl : P.HasAt lin (vsLinFuns lin))
    {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) {a z : List ℕ} {Bm : List (List ℕ)}
    (H : VsFRowFits p N a Bm z) :
    FunDet P b (.list [vsFCtx p a, .list (Bm.map natList), vsFAccVal (0, z)])
      (vsFAccVal (Bm.foldl (vsFMulAcc p a) (0, z))) (3 * 10 ^ 6 * (N + 1) ^ 4) := by
  have hBl : Bm.length ≤ N := H.Ba.trans H.la
  have hR := wt_vsFMat_le H.hB H.lB (by omega)
  have hpre : ∀ i ≤ Bm.length, ((Bm.take i).foldl (vsFMulAcc p a) (0, z)).1 = i ∧
      ((Bm.take i).foldl (vsFMulAcc p a) (0, z)).2.length = z.length ∧
      ∀ y ∈ ((Bm.take i).foldl (vsFMulAcc p a) (0, z)).2, y < p := by
    intro i hi
    refine ⟨?_, vsFMulAcc_foldl_length p a _ _, vsFMulAcc_foldl_lt hp a _ H.hz⟩
    rw [vsFMulAcc_foldl_fst, List.length_take]
    simp only [zero_add]
    omega
  have hM : ∀ i acc, i ≤ (Bm.map natList).length →
      acc = vsFAccVal ((Bm.take i).foldl (vsFMulAcc p a) (0, z)) →
      acc.wt ≤ 20 * (N + 1) ^ 2 := by
    rintro i acc hi rfl
    rw [List.length_map] at hi
    obtain ⟨h1, h2, h3⟩ := hpre i hi
    exact wt_vsFAccVal_le (k := _) (v := _) (by omega) (fun y hy => (h3 y hy).le.trans hpN)
      (by rw [h2]; exact H.lz)
  have hg : ∀ i acc (hi : i < (Bm.map natList).length),
      acc = vsFAccVal ((Bm.take i).foldl (vsFMulAcc p a) (0, z)) →
      FunAll P st (.list [vsFCtx p a, acc, (Bm.map natList)[i]]) (fun w cost =>
        w = vsFAccVal ((Bm.take (i + 1)).foldl (vsFMulAcc p a) (0, z)) ∧
        cost ≤ 2 * 10 ^ 6 * (N + 1) ^ 3) := by
    rintro i acc hi rfl
    rw [List.length_map] at hi
    obtain ⟨h1, h2, h3⟩ := hpre i hi.le
    have hri := List.getElem_mem hi
    have := H.Ba
    rw [List.getElem_map, vsFMulAcc_take_succ p a Bm (0, z) i hi]
    have := vsFMulStep_spec (k := ((Bm.take i).foldl (vsFMulAcc p a) (0, z)).1)
      (v := ((Bm.take i).foldl (vsFMulAcc p a) (0, z)).2) (r := Bm[i]) hf hl hp hpN H.ha H.la
      (by rw [h1]; omega) h3 (by rw [h2]; exact H.lz) (H.hB _ hri) (H.lB _ hri)
      (by rw [h2]; exact H.zB _ hri)
    exact this
  refine ((foldl_spec h (c := vsFCtx p a) (acc0 := vsFAccVal (0, z)) (M := 20 * (N + 1) ^ 2)
    (B := fun _ => 2 * 10 ^ 6 * (N + 1) ^ 3)
    (Inv := fun i acc => acc = vsFAccVal ((Bm.take i).foldl (vsFMulAcc p a) (0, z)))
    (by simp) hM hg).mono fun w cost hw => ⟨?_, ?_⟩)
  · rw [hw.1, List.length_map, List.take_length]
  · have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have haN : ∀ y ∈ a, y ≤ N := fun y hy => (H.ha y hy).le.trans hpN
    have hzN : ∀ y ∈ z, y ≤ N := fun y hy => (H.hz y hy).le.trans hpN
    have wC := wt_vsFCtx_le hpN haN H.la
    have wZ := wt_vsFAccVal_le (k := 0) (Nat.zero_le N) hzN H.lz
    have w3 := wt_list3_le (vsFCtx p a) (.list (Bm.map natList)) (vsFAccVal (0, z))
    have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hN4 : (N + 1) * (N + 1) ^ 3 = (N + 1) ^ 4 := by ring
    have k1 : Bm.length * (2 * 10 ^ 6 * (N + 1) ^ 3) ≤ (N + 1) * (2 * 10 ^ 6 * (N + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : loopModK * (Bm.length + 1) *
        ((Val.list [vsFCtx p a, .list (Bm.map natList), vsFAccVal (0, z)]).wt + Bm.length +
          20 * (N + 1) ^ 2 + 1) ≤ 1000 * (N + 1) * (150 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
    have e1 : (N + 1) * (2 * 10 ^ 6 * (N + 1) ^ 3) = 2 * 10 ^ 6 * (N + 1) ^ 4 := by
      rw [← hN4]; ring
    have e2 : 1000 * (N + 1) * (150 * (N + 1) ^ 3) = 150000 * (N + 1) ^ 4 := by
      rw [← hN4]; ring
    omega

/-! ### One row -/

/-- The context of the product: `[p, B, z]`. -/
def vsFMatCtx (p : ℕ) (Bm : List (List ℕ)) (z : List ℕ) : Val :=
  .list [.nat p, .list (Bm.map natList), natList z]

/-- One row, on `[[p, B, z], a]`: call the fold at `fold` on `[[p, a], B, [0, z]]` and keep
the vector. -/
def vsFRowF (fold : ℕ) : Expr :=
  .get (.call fold (mk3 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))
    (mk2 (.nat 0) (.get (arg 0) (.nat 2))))) (.nat 1)

theorem vsFRow_spec {P : Program} {f fold st lin : ℕ} (hf0 : P.funs[f]? = some (vsFRowF fold))
    (h : P.HasAt fold (foldlFuns fold st))
    (hf : P.funs[st]? = some (vsFMulStepF lin)) (hl : P.HasAt lin (vsLinFuns lin))
    {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) {a z : List ℕ} {Bm : List (List ℕ)}
    (H : VsFRowFits p N a Bm z) :
    FunDet P f (.list [vsFMatCtx p Bm z, natList a]) (natList (vsFRowMul p a Bm z))
      (4 * 10 ^ 6 * (N + 1) ^ 4) := by
  set A := Val.list [vsFMatCtx p Bm z, natList a] with hA
  have g0 := Det.arg' (P := P) (rest := []) (vs := [vsFMatCtx p Bm z, natList a]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [vsFMatCtx p Bm z, natList a]) (j := 1) rfl
  have dp := Det.get' g0 (Det.nat 0)
    (show [Val.nat p, .list (Bm.map natList), natList z][0]? = some _ from rfl)
  have dB := Det.get' g0 (Det.nat 1)
    (show [Val.nat p, .list (Bm.map natList), natList z][1]? = some _ from rfl)
  have dz := Det.get' g0 (Det.nat 2)
    (show [Val.nat p, .list (Bm.map natList), natList z][2]? = some _ from rfl)
  have dargs := Det.mk3 (Det.mk2 dp g1) dB (Det.mk2 (Det.nat 0) dz)
  have dcall := Det.call dargs (vsFRowFold_spec h hf hl hp hpN H)
  set R := Bm.foldl (vsFMulAcc p a) (0, z) with hRdef
  have dget := Det.get' dcall (Det.nat 1)
    (show [Val.nat R.1, natList R.2][1]? = some (natList R.2) from rfl)
  refine FunDet.intro hf0 (dget.mono ?_)
  -- the cost
  have hBl : Bm.length ≤ N := H.Ba.trans H.la
  have haN : ∀ y ∈ a, y ≤ N := fun y hy => (H.ha y hy).le.trans hpN
  have hzN : ∀ y ∈ z, y ≤ N := fun y hy => (H.hz y hy).le.trans hpN
  have hR1 : R.1 = Bm.length := by rw [hRdef, vsFMulAcc_foldl_fst]; simp
  have hR2 : R.2.length = z.length := vsFMulAcc_foldl_length p a Bm (0, z)
  have := H.lz
  have hR3 : ∀ y ∈ R.2, y ≤ N := fun y hy => (vsFMulAcc_foldl_lt hp a Bm H.hz y hy).le.trans hpN
  have wR := wt_vsFAccVal_le (k := R.1) (v := R.2) (by omega) hR3 (by omega)
  have wR2 := wt_natList_le_sq hR3 (by omega)
  have wBm := wt_vsFMat_le H.hB H.lB (by omega)
  have wa := wt_natList_le_sq haN H.la
  have wz := wt_natList_le_sq hzN H.lz
  have wC := wt_vsFCtx_le hpN haN H.la
  have wZ := wt_vsFAccVal_le (k := 0) (Nat.zero_le N) hzN H.lz
  have w3 := wt_list3_le (.nat p) (.list (Bm.map natList)) (natList z)
  have w3' := wt_list3_le (vsFCtx p a) (.list (Bm.map natList)) (vsFAccVal (0, z))
  have w2 := wt_list2_le (vsFMatCtx p Bm z) (natList a)
  have wp := wt_nat_le p
  have w0 := wt_nat_le 0
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN4 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have eC : (Val.list [Val.nat p, natList a]).wt = (vsFCtx p a).wt := rfl
  have eZ : (Val.list [Val.nat 0, natList z]).wt = (vsFAccVal (0, z)).wt := rfl
  have eM : (Val.list [Val.nat p, .list (Bm.map natList), natList z]).wt =
    (vsFMatCtx p Bm z).wt := rfl
  have eR : (vsFAccVal R).wt = (Val.list [Val.nat R.1, natList R.2]).wt := rfl
  have eR' : vsFAccVal (R.1, R.2) = vsFAccVal R := rfl
  have eRow : natList R.2 = natList (vsFRowMul p a Bm z) := rfl
  rw [eR'] at wR
  have e3 : (Val.list [Val.list [Val.nat p, natList a], Val.list (Bm.map natList),
      Val.list [Val.nat 0, natList z]]).wt =
    (Val.list [vsFCtx p a, .list (Bm.map natList), vsFAccVal (0, z)]).wt := rfl
  have hBN := H.lz
  omega

/-! ### The product -/

/-- The product, at base `b`: map the row function over the rows of `A` (16 functions). -/
def vsFMatMulFuns (b : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [vsFRowF (b + 4)] ++ foldlFuns (b + 4) (b + 7) ++
    [vsFMulStepF (b + 8)] ++ vsLinFuns (b + 8)

theorem vsFMatMulFuns_length (b : ℕ) : (vsFMatMulFuns b).length = 16 := rfl

theorem vsFMat_natList_inj {a a' : List ℕ} (h : natList a = natList a') : a = a' := by
  have h1 : a.map Val.nat = a'.map Val.nat := Val.list.inj h
  exact List.map_injective_iff.2 (fun x y hxy => Val.nat.inj hxy) h1

/-- The hypotheses on the right factor `B` and the start vector `z`. -/
structure VsFMatFits (p N : ℕ) (Bm : List (List ℕ)) (z : List ℕ) : Prop where
  hz : ∀ y ∈ z, y < p
  lz : z.length ≤ N
  hB : ∀ r ∈ Bm, ∀ y ∈ r, y ≤ N
  lB : ∀ r ∈ Bm, r.length ≤ N
  zB : ∀ r ∈ Bm, z.length ≤ r.length
  lBN : Bm.length ≤ N

/-- **The product.** On `[[p, B, z], A]`, with `B` and `z` fitting, every row `a` of `A` with
entries below `p`, length at most `N` and at least the number of rows of `B`, and at most `N`
rows, the result is the list of rows `vsFRowMul p a B z`. With `z = 0` this is the matrix
product `A B` modulo `p`. -/
theorem vsFMatMul_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFMatMulFuns b))
    {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) {z : List ℕ} {Bm A : List (List ℕ)}
    (HB : VsFMatFits p N Bm z)
    (HA : ∀ a ∈ A, (∀ y ∈ a, y < p) ∧ a.length ≤ N ∧ Bm.length ≤ a.length)
    (hA : A.length ≤ N) :
    FunDet P b (.list [vsFMatCtx p Bm z, .list (A.map natList)])
      (.list (A.map fun a => natList (vsFRowMul p a Bm z))) (5 * 10 ^ 6 * (N + 1) ^ 5) := by
  have hm : P.HasAt b (mapFuns b (b + 3)) := h.block 0 rfl
  have hr : P.funs[b + 3]? = some (vsFRowF (b + 4)) :=
    h.get (j := 3) (by rw [vsFMatMulFuns_length]; omega)
  have hfo : P.HasAt (b + 4) (foldlFuns (b + 4) (b + 7)) := h.block 4 rfl
  have hst : P.funs[b + 7]? = some (vsFMulStepF (b + 8)) :=
    h.get (j := 7) (by rw [vsFMatMulFuns_length]; omega)
  have hl : P.HasAt (b + 8) (vsLinFuns (b + 8)) := h.block 8 rfl
  have H : ∀ a ∈ A, VsFRowFits p N a Bm z := fun a ha =>
    ⟨(HA a ha).1, (HA a ha).2.1, HB.hz, HB.lz, HB.hB, HB.lB, HB.zB, (HA a ha).2.2⟩
  have hrow : ∀ x ∈ A.map natList, FunAll P (b + 3) (.list [vsFMatCtx p Bm z, x])
      (fun w cost => (fun x w => ∀ a, x = natList a → w = natList (vsFRowMul p a Bm z)) x w ∧
        cost ≤ 4 * 10 ^ 6 * (N + 1) ^ 4) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine FunAll.mono (vsFRow_spec hr hfo hst hl hp hpN (H a ha)) fun w c hw => ⟨?_, hw.2⟩
    intro a' ha'
    rw [hw.1, vsFMat_natList_inj ha']
  refine (map_spec hm hrow).mono fun w c hw => ?_
  obtain ⟨ws, rfl, hR, hc⟩ := hw
  have hws : ws = A.map fun a => natList (vsFRowMul p a Bm z) :=
    forall₂_map_eq (fun a _ w hw => hw a rfl) hR
  subst hws
  refine ⟨rfl, ?_⟩
  simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
  -- the cost
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN4 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN5 : (N + 1) * (N + 1) ^ 4 = (N + 1) ^ 5 := by ring
  have wA := wt_vsFMat_le (Bm := A) (N := N) (fun a ha y hy => ((HA a ha).1 y hy).le.trans hpN)
    (fun a ha => (HA a ha).2.1) (by omega)
  have wO := wt_vsFMat_le (Bm := A.map fun a => vsFRowMul p a Bm z) (N := N)
    (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ a ha rfl y hy
      exact (vsFMulAcc_foldl_lt hp a Bm HB.hz y hy).le.trans hpN)
    (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ a ha rfl
      rw [vsFRowMul, vsFMulAcc_foldl_length]
      exact HB.lz)
    (by rw [List.length_map]; omega)
  rw [List.map_map] at wO
  have wO' : (Val.list (A.map fun a => natList (vsFRowMul p a Bm z))).wt ≤
      11 * (N + 1) ^ 3 + 4 := by
    simpa only [Function.comp_def] using wO
  have hctx : (vsFMatCtx p Bm z).wt ≤ 60 * (N + 1) ^ 3 := by
    have wBm := wt_vsFMat_le HB.hB HB.lB (by have := HB.lBN; omega)
    have wz := wt_natList_le_sq (fun y hy => (HB.hz y hy).le.trans hpN) HB.lz
    have w3 := wt_list3_le (.nat p) (.list (Bm.map natList)) (natList z)
    have wp := wt_nat_le p
    show (Val.list [.nat p, .list (Bm.map natList), natList z]).wt ≤ _
    omega
  have w2 := wt_list2_le (vsFMatCtx p Bm z) (.list (A.map natList))
  have k1 : A.length * (4 * 10 ^ 6 * (N + 1) ^ 4) ≤ (N + 1) * (4 * 10 ^ 6 * (N + 1) ^ 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have k2 : mapK * (A.length + 1) * ((Val.list [vsFMatCtx p Bm z, .list (A.map natList)]).wt +
      (Val.list (A.map fun a => natList (vsFRowMul p a Bm z))).wt + 1) ≤
      1000 * (N + 1) * (200 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have e1 : (N + 1) * (4 * 10 ^ 6 * (N + 1) ^ 4) = 4 * 10 ^ 6 * (N + 1) ^ 5 := by
    rw [← hN5]; ring
  have e2 : 1000 * (N + 1) * (200 * (N + 1) ^ 4) = 200000 * (N + 1) ^ 5 := by
    rw [← hN5]; ring
  omega

end GI.Impl
