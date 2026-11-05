module

public import Workspace.CamDirectSocle
public import Workspace.Impl.CamPRestr
public import Workspace.Impl.CamPLoopMath
public import Workspace.Impl.CamPCol

@[expose] public section

/-!
# Direct simple factor search in `camProd e S`

This file implements the chief-series-free factor-finding subroutine from Proposition 2.2 of
`Workspace/CamDirectSocle.lean`, together with shared subroutines also used by the direct socle
search in `Workspace/Impl/CamDirectSocle.lean`:

1. `camOrbListFuns`: given `[encGroup ts, .nat z]`, computes `encPts O` for the deduplicated list
   `O` of points in the `(gens ts)`-orbit of `z`.
2. `camKeepBest` and `CamBestInv`: maintains `[best_w, .nat best_ord]`, keeping the minimum-order
   nontrivial candidate subgroup seen so far.
3. `camNclBestBody`: given `[gv_G, w_K, acc]`, computes the normal closure of `K` in `G`, its
   order, and updates `acc` via `camKeepBest`.
4. `camSearchEntryBody`: given `gv = encGroup gs`, computes `gv₀ = encGroup hs₀` for the stabilizer
   of `0` in `G = gens gs`, runs an `n`-step `iterFuns` loop starting from `[.nil, .nat 0]`, and
   returns the generator list `res[0]` of the minimum-order nontrivial candidate.
5. `camFactorStep` and `camFactorFuns`: for each `z < n`, forms the candidate
   `camFactorCand Cur x₀ z` and updates the best accumulator; by `camFactorCand_min_is_single`,
   the returned generator list generates a single simple factor `camProd e {i₀}` (`i₀ ∈ S`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp len len_le_self)

/-- The bound on the arguments of the cited calls in the factor loop. -/
def camLoopB (n : ℕ) : ℕ := 4000 * (n + 1) ^ 6

variable {n m k r : ℕ}

/-! ### 1. Orbit of an arbitrary point `z` as `encPts O` -/

/-- Filter predicate testing whether a point `y` lies in the same `lab`-class as `z`. -/
def camOrbListQ (lab : Fin n → ℕ) (z : Fin n) : Val → Bool
  | .nat y => decide (camLabN lab y = lab z)
  | .list _ => false

theorem cam_filter_range_pt (lab : Fin n → ℕ) (z : Fin n) :
    ((List.range n).map Val.nat).filter (camOrbListQ lab z) =
      (((List.finRange n).filter fun y => decide (lab y = lab z)).map Fin.val).map Val.nat := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.filter_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro y _
  simp [camOrbListQ, camLabN, Function.comp_def]

theorem natList_map_val_eq_encPts (O : List (Fin n)) :
    natList (O.map Fin.val) = encPts O := by
  rw [encPts_eq, natList, List.map_map]; rfl

/-- On `[[encFun lab, .nat z], .nat y]`: whether `lab y = lab z`. -/
def camOrbListTest : Expr :=
  .arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))

theorem camOrbListTest_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some camOrbListTest)
    (lab : Fin n → ℕ) (hlab : ∀ x, lab x ≤ n) (z y : Fin n) :
    FunDet P f (.list [.list [encFun lab, .nat z], .nat y]) (boolVal (camOrbListQ lab z (.nat y)))
      (200 * (n + 1) ^ 2 + 200) := by
  set c := Val.list [encFun lab, .nat z]
  have dC := Det.arg' (P := P) (vs := [c, .nat y]) (rest := []) (j := 0) rfl
  have dY := Det.arg' (P := P) (vs := [c, .nat y]) (rest := []) (j := 1) rfl
  have dL := Det.get' dC (Det.nat 0)
    (show [encFun lab, Val.nat z][0]? = some (encFun lab) from rfl)
  have dZ := Det.get' dC (Det.nat 1)
    (show [encFun lab, Val.nat z][1]? = some (.nat z) from rfl)
  have d1 := Det.get' dL dY (encFun_getElem? lab y)
  have d2 := Det.get' dL dZ (encFun_getElem? lab z)
  have dE := Det.arith (op := .eq) d1 d2
  have hv : Val.nat (BinOp.eval .eq (lab y) (lab z)) = boolVal (camOrbListQ lab z (.nat y)) := by
    simp only [BinOp.eval, camOrbListQ, camLabN, y.isLt, ↓reduceDIte]
    by_cases h : lab y = lab z <;> simp [h]
  rw [hv] at dE
  refine FunDet.intro hf (dE.mono ?_)
  have h1 := wt_encFun_le_sq lab hlab
  have h2 := wt_list2_le (encFun lab) (.nat z)
  have h3 := wt_list2_le c (.nat y)
  have h4 := wt_nat_le y
  have h5 := wt_nat_le z
  have h6 := wt_nat_le (lab y)
  have h7 := wt_nat_le (lab z)
  have h8 := wt_boolVal_le (camOrbListQ lab z (.nat y))
  have h9 := hlab y
  have h10 := hlab z
  have h11 := y.isLt
  have h12 := z.isLt
  have h13 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hc : (Val.list [encFun lab, .nat z]).wt = c.wt := rfl
  omega

/-- On `[encGroup ts, .nat z]`: compute orbit labels of `ts`, build `range n`, and filter points
with the same label as `z`. -/
def camOrbListBody (b : ℕ) : Expr :=
  .letE (.call (b + 2) (arg 0))
  (.letE (.call (b + 34) (.get (arg 0) (.nat 0)))
    (.call (b + 37) (mk2 (mk2 (.var 1) (arg 1)) (.var 2))))

/-- The orbit-list module at base `b` (40 functions). -/
def camOrbListFuns (b : ℕ) : List Expr :=
  [camOrbListBody b, camOrbListTest] ++ orbitFuns (b + 2) ++ rangeFuns (b + 34) ++
    filterFuns (b + 37) (b + 1)

theorem length_camOrbListFuns (b : ℕ) : (camOrbListFuns b).length = 40 := by
  simp [camOrbListFuns, length_orbitFuns, rangeFuns, filterFuns, loopFuns]

/-- Where the parts of `camOrbListFuns` sit. -/
structure CamOrbListAt (P : Program) (b : ℕ) : Prop where
  body : P.funs[b]? = some (camOrbListBody b)
  test : P.funs[b + 1]? = some camOrbListTest
  orb : P.HasAt (b + 2) (orbitFuns (b + 2))
  rng : P.HasAt (b + 34) (rangeFuns (b + 34))
  flt : P.HasAt (b + 37) (filterFuns (b + 37) (b + 1))

theorem camOrbListAt_of {P : Program} {b : ℕ} (h : P.HasAt b (camOrbListFuns b)) :
    CamOrbListAt P b := by
  simp only [camOrbListFuns] at h
  have h2 := h.left.left.left
  exact
  { body := by simpa using h2 0 (by simp)
    test := by simpa using h2 1 (by simp)
    orb := by simpa using h.left.left.right
    rng := by simpa [length_orbitFuns, Nat.add_assoc] using h.left.right
    flt := by simpa [length_orbitFuns, rangeFuns, loopFuns, Nat.add_assoc] using h.right }

def camOrbListK : ℕ := 10 ^ 9

/-- **Orbit of `z` as `encPts O`.** When `ts.length ≤ n ^ 2`, the cost is at most
`camOrbListK * (n + 1) ^ 15`. -/
theorem camOrbList_spec {P : Program} {b : ℕ} (hP : CamOrbListAt P b)
    (ts : List (Perm (Fin n))) (hts : ts.length ≤ n ^ 2) (z : Fin n) :
    ∃ O : List (Fin n), O.Nodup ∧ O.length ≤ n ∧
      (∀ y, y ∈ O ↔ y ∈ MulAction.orbit (gens ts) z) ∧
      FunDet P b (.list [encGroup ts, .nat z]) (encPts O)
        (camOrbListK * (n + 1) ^ 15) := by
  obtain ⟨lab, hlabd, hlab1, hlab2⟩ := orbits_spec hP.orb (1 :: ts)
  set O := (List.finRange n).filter fun y => decide (lab y = lab z) with hOd
  have hO : O.Nodup := (List.nodup_finRange n).filter _
  have hOl : O.length ≤ n := by simpa using hO.length_le_card
  have hmem : ∀ y, y ∈ O ↔ y ∈ MulAction.orbit (gens ts) z := by
    intro y
    rw [hOd, List.mem_filter, ← cam_gens_cons_one ts]
    simp only [List.mem_finRange, true_and, decide_eq_true_eq]
    rw [eq_comm]
    exact hlab1 _ _
  refine ⟨O, hO, hOl, hmem, ?_⟩
  set a := Val.list [encGroup ts, .nat z] with ha
  set L := encFun lab with hL
  set R := natList (List.range n) with hR
  set c := Val.list [L, .nat z] with hc
  have hlabn : ∀ x, lab x ≤ n := fun x => (hlab2 x).1.le
  -- 1. orbit labels
  have d1 := Det.call (Det.arg' (P := P) (vs := [encGroup ts, .nat z]) (rest := []) (j := 0) rfl)
    hlabd
  -- 2. range n
  have fR : FunDet P (b + 34) (.nat n) R
      (loopModK * (n + 1) * ((Val.nat n).wt + n + R.wt + 1)) :=
    (range_spec hP.rng n).mono fun w cc h => ⟨h.1, by have := h.2; rw [h.1] at this; exact this⟩
  have d2 := Det.call (Det.encPerms_size (gs := 1 :: ts)
    (Det.arg' (P := P) (vs := [encGroup ts, .nat z]) (rest := [L]) (j := 0) rfl)) fR
  -- 3. filter
  have hxs : ∀ x ∈ (List.range n).map Val.nat, FunDet P (b + 1) (.list [c, x])
      (boolVal (camOrbListQ lab z x)) (200 * (n + 1) ^ 2 + 200) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact camOrbListTest_det hP.test lab hlabn z ⟨y, List.mem_range.mp hy⟩
  have fF : FunDet P (b + 37) (.list [c, R]) (encPts O)
      (n * (200 * (n + 1) ^ 2 + 200) +
        loopModK * (n + 1) * ((Val.list [c, R]).wt + n + (encPts O).wt + 1)) := by
    refine (filter_spec hP.flt hxs).mono fun w cc h => ?_
    obtain ⟨hw, hc'⟩ := h
    rw [cam_filter_range_pt lab z, ← natList, natList_map_val_eq_encPts] at hw
    subst hw
    refine ⟨rfl, ?_⟩
    have e1 : (((List.range n).map Val.nat).map fun _ => 200 * (n + 1) ^ 2 + 200).sum =
        n * (200 * (n + 1) ^ 2 + 200) := by simp [Function.comp_def, List.sum_replicate]
    rw [e1] at hc'
    simp only [List.length_map, List.length_range] at hc'
    exact hc'
  have dc := Det.mk2 (Det.var' (P := P) (env := [a, L, R]) (i := 1) rfl)
    (Det.arg' (P := P) (vs := [encGroup ts, .nat z]) (rest := [L, R]) (j := 1) rfl)
  have d3 := Det.call (Det.mk2 dc (Det.var' (P := P) (env := [a, L, R]) (i := 2) rfl)) fF
  refine FunDet.intro hP.body ((Det.letE d1 (Det.letE d2 d3)).mono ?_)
  clear d1 d2 d3 dc fR fF hxs hlabd
  -- Weights
  have hwG := wt_encGroup_le_sq hts
  have hwz := wt_nat_le z
  have hwa := wt_list2_le (encGroup ts) (.nat z)
  have hwL : L.wt ≤ 4 * (n + 1) ^ 2 := wt_encFun_le_sq lab hlabn
  have hwR : R.wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (B := n) (fun x hx => (List.mem_range.mp hx).le) (by simp)
  have hwO : (encPts O).wt ≤ 5 * (n + 1) ^ 2 := by
    rw [← natList_map_val_eq_encPts]
    exact wt_natList_le_sq (B := n)
      (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact u.isLt.le)
      (by simpa using hOl)
  have hwc := wt_list2_le L (.nat z)
  have hwcR := wt_list2_le c R
  have hwn := wt_nat_le n
  have hzlt := z.isLt
  have he1 : (Val.list [encGroup ts, .nat z]).wt = a.wt := rfl
  have he2 : (encPerms (1 :: ts)).wt = (encGroup ts).wt := rfl
  have he3 : (Val.list [L, .nat z]).wt = c.wt := rfl
  have he4 : (Val.list [Val.list [L, .nat z], R]).wt = (Val.list [c, R]).wt := rfl
  have hS3 : ((1 :: ts).length + 1) * (n + 1) ≤ 2 * (n + 1) ^ 3 := by
    simpa using measure_le_of_sq hts
  have horb : orbitK * (((1 :: ts).length + 1) * (n + 1)) ^ 5 ≤ 32 * orbitK * (n + 1) ^ 15 := by
    calc orbitK * (((1 :: ts).length + 1) * (n + 1)) ^ 5
        ≤ orbitK * (2 * (n + 1) ^ 3) ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS3 5)
      _ = 32 * orbitK * (n + 1) ^ 15 := by ring
  have hfl1 : n * (200 * (n + 1) ^ 2 + 200) ≤ 400 * (n + 1) ^ 3 := by
    have : 200 * (n + 1) ^ 2 + 200 ≤ 400 * (n + 1) ^ 2 := by
      have := Nat.one_le_pow 2 (n + 1) (by omega); omega
    calc n * (200 * (n + 1) ^ 2 + 200) ≤ (n + 1) * (400 * (n + 1) ^ 2) :=
          Nat.mul_le_mul (by omega) this
      _ = 400 * (n + 1) ^ 3 := by ring
  have h12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hrng : loopModK * (n + 1) * ((Val.nat n).wt + n + R.wt + 1) ≤
      8 * loopModK * (n + 1) ^ 3 := by
    have : (Val.nat n).wt + n + R.wt + 1 ≤ 8 * (n + 1) ^ 2 := by omega
    calc loopModK * (n + 1) * ((Val.nat n).wt + n + R.wt + 1)
        ≤ loopModK * (n + 1) * (8 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ this
      _ = 8 * loopModK * (n + 1) ^ 3 := by ring
  have hfl2 : loopModK * (n + 1) * ((Val.list [c, R]).wt + n + (encPts O).wt + 1) ≤
      50 * loopModK * (n + 1) ^ 3 := by
    have : (Val.list [c, R]).wt + n + (encPts O).wt + 1 ≤ 50 * (n + 1) ^ 2 := by omega
    calc loopModK * (n + 1) * ((Val.list [c, R]).wt + n + (encPts O).wt + 1)
        ≤ loopModK * (n + 1) * (50 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ this
      _ = 50 * loopModK * (n + 1) ^ 3 := by ring
  have p23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p615 : (n + 1) ^ 6 ≤ (n + 1) ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have p12 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [camOrbListK, orbitK, loopModK] at *
  clear_value a L R c O
  generalize (n + 1) ^ 15 = Q15 at *
  generalize (n + 1) ^ 6 = Q6 at *
  generalize (n + 1) ^ 3 = Q3 at *
  generalize (n + 1) ^ 2 = Q2 at *
  omega

/-! ### 2. Tracking the minimum-order nontrivial candidate (`camKeepBest`) -/

/-- Whether a candidate of order `ord` improves on the current best order `best_ord` (`0` if none). -/
def camBetter (best_ord ord : ℕ) : Prop :=
  1 < ord ∧ (best_ord = 0 ∨ ord < best_ord)

instance (best_ord ord : ℕ) : Decidable (camBetter best_ord ord) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- `acc` holds the minimum-order nontrivial subgroup seen so far among `Cands`. -/
def CamBestInv (Cands : Set (Subgroup (Perm (Fin n)))) (acc : Val) : Prop :=
  (acc = .list [.list [], .nat 0] ∧ ∀ K ∈ Cands, Nat.card K ≤ 1) ∨
  ∃ (Best : Subgroup (Perm (Fin n))) (best_w : Val),
    acc = .list [best_w, .nat (Nat.card Best)] ∧
    GensVal n best_w Best ∧
    Best ∈ Cands ∧
    1 < Nat.card Best ∧
    ∀ K ∈ Cands, 1 < Nat.card K → Nat.card Best ≤ Nat.card K

theorem camBestInv_empty : CamBestInv (n := n) ∅ (.list [.list [], .nat 0]) :=
  Or.inl ⟨rfl, by simp⟩

theorem CamBestInv.congr {C₁ C₂ : Set (Subgroup (Perm (Fin n)))} {acc : Val}
    (h : CamBestInv C₁ acc) (heq : C₁ = C₂) : CamBestInv C₂ acc :=
  heq ▸ h

theorem CamBestInv.wt_le {Cands : Set (Subgroup (Perm (Fin n)))} {acc : Val}
    (h : CamBestInv Cands acc) : acc.wt ≤ 40 * (n + 1) ^ 6 := by
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨Best, best_w, rfl, hbw, -, -, -⟩
  · have w1 := wt_list2_le (.list []) (.nat 0)
    have w2 := wt_list_nil
    have w3 := wt_nat_le 0
    omega
  · have w1 := GensVal.wt_le hbw
    have w2 := wt_card_le Best
    have w3 := wt_list2_le best_w (.nat (Nat.card Best))
    have hn2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem CamBestInv.extract {Cands : Set (Subgroup (Perm (Fin n)))} {acc : Val}
    (h : CamBestInv Cands acc) (hne : ∃ K ∈ Cands, 1 < Nat.card K) :
    ∃ (Best : Subgroup (Perm (Fin n))) (best_w : Val),
      acc = .list [best_w, .nat (Nat.card Best)] ∧
      GensVal n best_w Best ∧
      Best ∈ Cands ∧
      1 < Nat.card Best ∧
      ∀ K ∈ Cands, 1 < Nat.card K → Nat.card Best ≤ Nat.card K := by
  rcases h with ⟨-, hle⟩ | h
  · obtain ⟨K, hK, hgt⟩ := hne
    have := hle K hK
    omega
  · exact h

/-- On `[acc, cand_w, .nat ord]` with `acc = [best_w, .nat best_ord]`:
replace `acc` by `[cand_w, .nat ord]` if `1 < ord ∧ (best_ord = 0 ∨ ord < best_ord)`. -/
def camKeepBest : Expr :=
  .ite (.arith .mul (.arith .lt (.nat 1) (arg 2))
      (.arith .add (.arith .eq (.get (arg 0) (.nat 1)) (.nat 0))
        (.arith .lt (arg 2) (.get (arg 0) (.nat 1)))))
    (mk2 (arg 1) (arg 2))
    (arg 0)

theorem camKeepBest_eval_eq_zero (best_ord ord : ℕ) :
    BinOp.eval .mul (BinOp.eval .lt 1 ord)
      (BinOp.eval .add (BinOp.eval .eq best_ord 0) (BinOp.eval .lt ord best_ord)) = 0 ↔
      ¬ camBetter best_ord ord := by
  simp only [BinOp.eval, camBetter]
  by_cases h1 : 1 < ord <;> by_cases h2 : best_ord = 0 <;> by_cases h3 : ord < best_ord <;>
    simp [h1, h2, h3]

theorem camKeepBest_step {Cands : Set (Subgroup (Perm (Fin n)))} {best_w : Val} {best_ord : ℕ}
    (hinv : CamBestInv Cands (.list [best_w, .nat best_ord]))
    {K : Subgroup (Perm (Fin n))} {cand_w : Val} (hK : GensVal n cand_w K) :
    CamBestInv (insert K Cands)
      (if camBetter best_ord (Nat.card K) then .list [cand_w, .nat (Nat.card K)]
       else .list [best_w, .nat best_ord]) := by
  rcases hinv with ⟨heq, hle⟩ | ⟨Best, bw, heq, hbw, hBmem, hBgt, hBmin⟩
  · simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    by_cases hb : camBetter 0 (Nat.card K)
    · simp only [hb, ↓reduceIte]
      refine Or.inr ⟨K, cand_w, rfl, hK, Set.mem_insert _ _, hb.1, fun M hM hMgt => ?_⟩
      rcases Set.mem_insert_iff.mp hM with rfl | hM
      · exact le_rfl
      · have := hle M hM; omega
    · simp only [hb, ↓reduceIte]
      refine Or.inl ⟨rfl, fun M hM => ?_⟩
      rcases Set.mem_insert_iff.mp hM with rfl | hM
      · simp only [camBetter, true_or, and_true, not_lt] at hb; exact hb
      · exact hle M hM
  · simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    by_cases hb : camBetter (Nat.card Best) (Nat.card K)
    · simp only [hb, ↓reduceIte]
      obtain ⟨hKgt, h0 | hlt⟩ := hb
      · omega
      · refine Or.inr ⟨K, cand_w, rfl, hK, Set.mem_insert _ _, hKgt, fun M hM hMgt => ?_⟩
        rcases Set.mem_insert_iff.mp hM with rfl | hM
        · exact le_rfl
        · exact hlt.le.trans (hBmin M hM hMgt)
    · simp only [hb, ↓reduceIte]
      refine Or.inr ⟨Best, best_w, rfl, hbw, Set.mem_insert_of_mem _ hBmem, hBgt,
        fun M hM hMgt => ?_⟩
      rcases Set.mem_insert_iff.mp hM with rfl | hM
      · have hne0 : Nat.card Best ≠ 0 := by omega
        simp only [camBetter, hMgt, hne0, false_or, true_and, not_lt] at hb
        exact hb
      · exact hBmin M hM hMgt

/-- **Updating the best candidate.** -/
theorem camKeepBest_spec {P : Program} {kb : ℕ} (hkb : P.funs[kb]? = some camKeepBest)
    {Cands : Set (Subgroup (Perm (Fin n)))} {acc cand_w : Val} {K : Subgroup (Perm (Fin n))}
    (hinv : CamBestInv Cands acc) (hK : GensVal n cand_w K) :
    FunAll P kb (.list [acc, cand_w, .nat (Nat.card K)])
      (fun w cost => CamBestInv (insert K Cands) w ∧ cost ≤ 2000 * (n + 1) ^ 6) := by
  have ⟨best_w, best_ord, hacc_eq, hbo_wt⟩ :
      ∃ best_w best_ord, acc = .list [best_w, .nat best_ord] ∧
        (Val.nat best_ord).wt ≤ n ^ 2 + 3 := by
    rcases hinv with ⟨rfl, -⟩ | ⟨Best, bw, rfl, -, -, -, -⟩
    · exact ⟨.list [], 0, rfl, by rw [show (Val.nat 0).wt = 2 from rfl]; omega⟩
    · exact ⟨bw, Nat.card Best, rfl, wt_card_le Best⟩
  have hinv' : CamBestInv Cands (.list [best_w, .nat best_ord]) := hacc_eq ▸ hinv
  have hw_acc := hinv.wt_le
  rw [hacc_eq] at hw_acc ⊢
  set acc0 := Val.list [best_w, .nat best_ord]
  set ord := Nat.card K
  set a := Val.list [acc0, cand_w, .nat ord]
  have dA0 := Det.arg' (P := P) (vs := [acc0, cand_w, .nat ord]) (rest := []) (j := 0) rfl
  have dA1 := Det.arg' (P := P) (vs := [acc0, cand_w, .nat ord]) (rest := []) (j := 1) rfl
  have dA2 := Det.arg' (P := P) (vs := [acc0, cand_w, .nat ord]) (rest := []) (j := 2) rfl
  have dBO := Det.get' dA0 (Det.nat 1)
    (show [best_w, Val.nat best_ord][1]? = some (.nat best_ord) from rfl)
  have dC1 := Det.arith (op := .lt) (Det.nat 1) dA2
  have dC2 := Det.arith (op := .eq) dBO (Det.nat 0)
  have dC3 := Det.arith (op := .lt) dA2 dBO
  have dC23 := Det.arith (op := .add) dC2 dC3
  have dCond := Det.arith (op := .mul) dC1 dC23
  have dThen := Det.mk2 dA1 dA2
  have dIte := Det.ite' dCond dThen dA0
  refine FunAll.mono (FunDet.intro hkb dIte) fun w cost ⟨hw, hc⟩ => ?_
  have hcond := camKeepBest_eval_eq_zero best_ord ord
  have hval : (if BinOp.eval .mul (BinOp.eval .lt 1 ord)
      (BinOp.eval .add (BinOp.eval .eq best_ord 0) (BinOp.eval .lt ord best_ord)) = 0 then
        acc0 else .list [cand_w, .nat ord]) =
      (if camBetter best_ord ord then .list [cand_w, .nat ord] else acc0) := by
    by_cases hb : camBetter best_ord ord
    · have h0 : BinOp.eval .mul (BinOp.eval .lt 1 ord)
          (BinOp.eval .add (BinOp.eval .eq best_ord 0) (BinOp.eval .lt ord best_ord)) ≠ 0 :=
        mt hcond.mp (not_not.mpr hb)
      simp only [hb, h0, ↓reduceIte]
    · have h0 : BinOp.eval .mul (BinOp.eval .lt 1 ord)
          (BinOp.eval .add (BinOp.eval .eq best_ord 0) (BinOp.eval .lt ord best_ord)) = 0 :=
        hcond.mpr hb
      simp only [hb, h0, ↓reduceIte]
  rw [hval] at hw
  subst hw
  refine ⟨camKeepBest_step hinv' hK, ?_⟩
  have wK := GensVal.wt_le hK
  have word : (Val.nat ord).wt ≤ n ^ 2 + 3 := wt_card_le K
  have wThen := wt_list2_le cand_w (.nat ord)
  have wa := wt_list3_le acc0 cand_w (.nat ord)
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hn2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have wc1 : (Val.nat (BinOp.eval .lt 1 ord)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> decide
  have wc2 : (Val.nat (BinOp.eval .eq best_ord 0)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> decide
  have wc3 : (Val.nat (BinOp.eval .lt ord best_ord)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> decide
  have wc23 : (Val.nat (BinOp.eval .add (BinOp.eval .eq best_ord 0)
      (BinOp.eval .lt ord best_ord))).wt ≤ 4 := by
    simp only [BinOp.eval]; split_ifs <;> decide
  have wcM : (Val.nat (BinOp.eval .mul (BinOp.eval .lt 1 ord)
      (BinOp.eval .add (BinOp.eval .eq best_ord 0) (BinOp.eval .lt ord best_ord)))).wt ≤ 4 := by
    simp only [BinOp.eval]; split_ifs <;> decide
  have hm1 : max (2 * a.wt + 1 + 5 + (2 * a.wt + 2 + 5) + 2 * (Val.list [cand_w, .nat ord]).wt + 7)
      (2 * a.wt + 0 + 5) ≤ 4 * a.wt + 2 * (Val.list [cand_w, .nat ord]).wt + 25 :=
    max_le (by omega) (by omega)
  have hm2 : max (Val.list [cand_w, .nat ord]).wt acc0.wt ≤
      (Val.list [cand_w, .nat ord]).wt + acc0.wt :=
    max_le (by omega) (by omega)
  have e_a : (Val.list [acc0, cand_w, .nat ord]).wt = a.wt := rfl
  clear dA0 dA1 dA2 dBO dC1 dC2 dC3 dC23 dCond dThen dIte
  clear_value acc0 ord a
  omega

/-! ### 3. Normal closure + order + keep-best (`camNclBestBody`) -/

/-- On `[gv_G, w_K, acc]`:
1. `gv_K ← mkGroup [n, w_K]`
2. `w_N ← normalClosure [gv_G, gv_K]`
3. `gv_N ← mkGroup [n, w_N]`
4. `ord ← groupOrder gv_N`
5. `camKeepBest [acc, w_N, ord]`. -/
def camNclBestBody (mg kb jo jn : ℕ) : Expr :=
  .letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
  (.letE (.prim jn (mk2 (arg 0) (.var 1)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
  (.letE (.prim jo (.var 3))
    (.call kb (mk3 (arg 2) (.var 2) (.var 4))))))

def camNclBestK : ℕ := 10 ^ 8

/-- **Normal closure + order + keep-best.** -/
theorem camNclBest_spec {ho : GroupOrder} {hncl : NormalClosure} {P : Program}
    {nb mg kb jo jn : ℕ} (hnb : P.funs[nb]? = some (camNclBestBody mg kb jo jn))
    (hmg : P.HasAt mg (mkGroupFuns mg)) (hkb : P.funs[kb]? = some camKeepBest)
    (hpo : P.prims[jo]? = some (groupOrderPrim ho))
    (hpn : P.prims[jn]? = some (normalClosurePrim hncl))
    (gs : List (Perm (Fin n))) {K : Subgroup (Perm (Fin n))} (hKG : K ≤ gens gs)
    {w_K acc : Val} (hK : GensVal n w_K K)
    {Cands : Set (Subgroup (Perm (Fin n)))} (hinv : CamBestInv Cands acc) :
    FunAll P nb (.list [encGroup gs, w_K, acc])
      (fun w cost => CamBestInv (insert (camNormClosure (gens gs) K) Cands) w ∧
        cost ≤ (normalClosurePrim hncl).boundSize (2 * (encGroup gs).wt + 700 * (n + 1) ^ 6) +
          (groupOrderPrim ho).boundSize (320 * (n + 1) ^ 6) +
          camNclBestK * ((encGroup gs).wt + (n + 1) ^ 9)) := by
  set gv_G := encGroup gs with hgv_G
  set a := Val.list [gv_G, w_K, acc] with ha
  have dA0 := fun (rest : List Val) =>
    Det.arg' (P := P) (vs := [gv_G, w_K, acc]) (rest := rest) (j := 0) rfl
  have dN := fun (rest : List Val) => Det.encPerms_size (gs := 1 :: gs) (dA0 rest)
  -- 1. mkGroup on w_K
  obtain ⟨ks, rfl, hksl, fK, ⟨ks', hKe, hKg⟩, hKw⟩ := mkGroup_gensVal hmg hK
  obtain rfl := encGroup_injective hKe
  have d1 := Det.call (Det.mk2 (dN [])
    (Det.arg' (P := P) (vs := [gv_G, .list (ks.map encPerm), acc]) (rest := []) (j := 1) rfl)) fK
  refine FunAll.intro hnb (EvalAll.letE d1 fun vK cK h1 => ?_)
  obtain ⟨rfl, hcK⟩ := h1
  -- 2. normalClosure on [gv_G, encGroup ks]
  set E1 := [a, encGroup ks]
  have d2a := Det.mk2 (dA0 [encGroup ks]) (Det.var' (P := P) (env := E1) (i := 1) rfl)
  refine EvalAll.letE (normalClosure_call hncl hpn d2a ⟨gs, rfl, rfl⟩) fun w_N cN h2 => ?_
  obtain ⟨hw_N, hcN⟩ := h2
  rw [camNormClosure_eq_of_gens hKg hKG] at hw_N
  -- 3. mkGroup on w_N
  obtain ⟨ns, rfl, hnsl, fN, ⟨ns', hNe, hNg⟩, hNw⟩ := mkGroup_gensVal hmg hw_N
  obtain rfl := encGroup_injective hNe
  set E2 := [a, encGroup ks, .list (ns.map encPerm)]
  have d3 := Det.call (Det.mk2 (dN [encGroup ks, .list (ns.map encPerm)])
    (Det.var' (P := P) (env := E2) (i := 2) rfl)) fN
  refine EvalAll.letE d3 fun vN cmN h3 => ?_
  obtain ⟨rfl, hcmN⟩ := h3
  -- 4. groupOrder on encGroup ns
  set E3 := [a, encGroup ks, .list (ns.map encPerm), encGroup ns]
  have d4 := groupOrder_call ho hpo (Det.var' (P := P) (env := E3) (i := 3) rfl) ⟨ns, rfl, hNg⟩
  refine EvalAll.letE d4 fun vO cO h4 => ?_
  obtain ⟨rfl, hcO⟩ := h4
  -- 5. camKeepBest
  set E4 := [a, encGroup ks, .list (ns.map encPerm), encGroup ns,
    .nat (Nat.card (camNormClosure (gens gs) K))]
  have d5a := Det.mk3
    (Det.arg' (P := P) (vs := [gv_G, .list (ks.map encPerm), acc]) (rest := E4.drop 1) (j := 2) rfl)
    (Det.var' (P := P) (env := E4) (i := 2) rfl)
    (Det.var' (P := P) (env := E4) (i := 4) rfl)
  refine EvalAll.call_funAll d5a fun v5 ca5 hv5 => ?_
  obtain ⟨rfl, hca5⟩ := hv5
  refine (camKeepBest_spec hkb hinv hw_N).mono fun w cb5 ⟨hw, hcb5⟩ => ⟨hw, ?_⟩
  clear d5a d4 d3 d2a d1 fN fK dN dA0
  -- Weights and cost
  have hw_acc := hinv.wt_le
  have hw_w := hw.wt_le
  have hw_wK := GensVal.wt_le hK
  have hw_wN := GensVal.wt_le hw_N
  have hw_ord := wt_card_le (camNormClosure (gens gs) K)
  have hw_n := wt_nat_le n
  have hwa := wt_list3_le gv_G (.list (ks.map encPerm)) acc
  have hwm1 := wt_list2_le (.nat n) (.list (ks.map encPerm))
  have hwm2 := wt_list2_le gv_G (encGroup ks)
  have hwm3 := wt_list2_le (.nat n) (.list (ns.map encPerm))
  have hwm4 := wt_list3_le acc (.list (ns.map encPerm))
    (.nat (Nat.card (camNormClosure (gens gs) K)))
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hb_ncl := (normalClosurePrim hncl).bound_le (v := .list [gv_G, encGroup ks])
    (B := 2 * gv_G.wt + 700 * (n + 1) ^ 6)
    ((Val.size_le_wt _).trans (by omega))
  have hb_ord := (groupOrderPrim ho).bound_le (v := encGroup ns)
    (B := 320 * (n + 1) ^ 6)
    ((Val.size_le_wt _).trans hNw)
  have he_a : (Val.list [gv_G, .list (ks.map encPerm), acc]).wt = a.wt := rfl
  have he_G : (encPerms (1 :: gs)).wt = gv_G.wt := rfl
  have hn2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [camNclBestK, mkGroupK] at *
  clear_value a gv_G E1 E2 E3 E4
  generalize (n + 1) ^ 9 = Q9 at *
  generalize (n + 1) ^ 6 = Q6 at *
  generalize (n + 1) ^ 2 = Q2 at *
  omega

/-! ### 4. Top-level search entry (`camSearchEntryBody`) -/

/-- On `gv = encGroup gs`:
1. `w₀ ← pointwiseStab [gv, [.nat 0]]`
2. `gv₀ ← mkGroup [n, w₀]`
3. `res ← call it [[gv, gv₀], n, [[], 0]]`
4. return `res[0]`. -/
def camSearchEntryBody (mg it jp : ℕ) : Expr :=
  .letE (.prim jp (mk2 (.var 0) (mk1 (.nat 0))))
  (.letE (.call mg (mk2 (.get (.var 0) (.nat 0)) (.var 1)))
  (.letE (.call it (mk3 (mk2 (.var 0) (.var 2)) (.get (.var 0) (.nat 0)) (mk2 .nil (.nat 0))))
    (.get (.var 3) (.nat 0))))

def camSearchEntryK : ℕ := 10 ^ 8

/-- **Top-level search entry.** -/
theorem camSearchEntry_spec {hp : PointwiseStab} {P : Program} {b mg it jp : ℕ}
    (hb : P.funs[b]? = some (camSearchEntryBody mg it jp))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hpp : P.prims[jp]? = some (pointwiseStabPrim hp))
    (gs : List (Perm (Fin n))) (hn : 0 < n)
    {Cands : Set (Subgroup (Perm (Fin n)))} {LCost : ℕ}
    (hne : ∃ K ∈ Cands, 1 < Nat.card K)
    (hit : ∀ hs₀ : List (Perm (Fin n)), hs₀.length ≤ n ^ 2 →
      gens hs₀ = pointwiseStab (gens gs) [⟨0, hn⟩] →
      FunAll P it (.list [.list [encGroup gs, encGroup hs₀], .nat n, .list [.list [], .nat 0]])
        (fun res cl => CamBestInv Cands res ∧ cl ≤ LCost)) :
    FunAll P b (encGroup gs)
      (fun w cost =>
        (∃ Best ∈ Cands, GensVal n w Best ∧ 1 < Nat.card Best ∧
          ∀ K ∈ Cands, 1 < Nat.card K → Nat.card Best ≤ Nat.card K) ∧
        cost ≤ LCost + (pointwiseStabPrim hp).boundSize (2 * (encGroup gs).wt + 30 * (n + 1)) +
          camSearchEntryK * ((encGroup gs).wt + (n + 1) ^ 9)) := by
  set gv := encGroup gs with hgv
  set x₀ : Fin n := ⟨0, hn⟩
  have dG := fun (rest : List Val) => Det.var' (P := P) (env := gv :: rest) (i := 0) rfl
  have dN := fun (rest : List Val) => Det.encPerms_size (gs := 1 :: gs) (dG rest)
  -- 1. pointwiseStab on [gv, [0]]
  have d1a : Det P [gv] (mk2 (.var 0) (mk1 (.nat 0))) (.list [gv, encPts [x₀]]) _ :=
    Det.mk2 (dG []) (Det.mk1 (Det.nat 0))
  refine FunAll.intro hb (EvalAll.letE (pointwiseStab_call hp hpp d1a ⟨gs, rfl, rfl⟩)
    fun w₀ c₀ h1 => ?_)
  obtain ⟨hw₀, hc₀⟩ := h1
  -- 2. mkGroup on w₀
  obtain ⟨hs₀, rfl, hhs₀l, f0, ⟨hs₀', h0e, h0g⟩, h0w⟩ := mkGroup_gensVal hmg hw₀
  obtain rfl := encGroup_injective h0e
  set E1 := [gv, .list (hs₀.map encPerm)]
  have d2 := Det.call (Det.mk2 (dN [.list (hs₀.map encPerm)])
    (Det.var' (P := P) (env := E1) (i := 1) rfl)) f0
  refine EvalAll.letE d2 fun v0 cm0 h2 => ?_
  obtain ⟨rfl, hcm0⟩ := h2
  -- 3. call it
  set E2 := [gv, .list (hs₀.map encPerm), encGroup hs₀]
  have d3a := Det.mk3
    (Det.mk2 (dG [.list (hs₀.map encPerm), encGroup hs₀])
      (Det.var' (P := P) (env := E2) (i := 2) rfl))
    (dN [.list (hs₀.map encPerm), encGroup hs₀])
    (Det.mk2 Det.nil (Det.nat 0))
  refine EvalAll.letE (Ra := fun res c3 => CamBestInv Cands res ∧
      c3 ≤ LCost + 30 * gv.wt + 10000 * (n + 1) ^ 6)
    (EvalAll.call_funAll d3a fun v3 ca3 hv3 => ?_) fun res cl3 h3 => ?_
  · obtain ⟨rfl, hca3⟩ := hv3
    refine (hit hs₀ hhs₀l h0g).mono fun res cl ⟨hinv, hcl⟩ => ⟨hinv, ?_⟩
    have hw_res := hinv.wt_le
    have w1 := wt_list2_le gv (encGroup hs₀)
    have w2 := wt_list2_le (.list []) (.nat 0)
    have w3 := wt_list3_le (.list [gv, encGroup hs₀]) (.nat n) (.list [.list [], .nat 0])
    have wn := wt_nat_le n
    have wn0 := wt_nat_le 0
    have wnil := wt_list_nil
    have heG : (encPerms (1 :: gs)).wt = gv.wt := rfl
    have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    omega
  obtain ⟨hinv, hcl3⟩ := h3
  obtain ⟨Best, best_w, rfl, hbw, hBmem, hBgt, hBmin⟩ := hinv.extract hne
  -- 4. get res[0]
  set E3 := [gv, .list (hs₀.map encPerm), encGroup hs₀, .list [best_w, .nat (Nat.card Best)]]
  have d4 := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl) (Det.nat 0)
    (show [best_w, Val.nat (Nat.card Best)][0]? = some best_w from rfl)
  refine d4.post fun c4 hc4 => ⟨⟨Best, hBmem, hbw, hBgt, hBmin⟩, ?_⟩
  clear d4 d3a d2 d1a f0 dN dG
  have hw_res := hinv.wt_le
  have hw_bw := GensVal.wt_le hbw
  have hw_w0 := GensVal.wt_le hw₀
  have w_pts : (encPts [x₀]).wt ≤ 3 * (n + 2) + 4 := by simpa using wt_encPts_le [x₀]
  have he_pts : (Val.list [Val.nat ↑x₀]).wt = (encPts [x₀]).wt := rfl
  have w_arg0 := wt_list2_le gv (encPts [x₀])
  have w_mk0 := wt_list2_le (.nat n) (.list (hs₀.map encPerm))
  have wn := wt_nat_le n
  have hb_ps := (pointwiseStabPrim hp).bound_le (v := .list [gv, encPts [x₀]])
    (B := 2 * gv.wt + 30 * (n + 1)) ((Val.size_le_wt _).trans (by omega))
  have heG : (encPerms (1 :: gs)).wt = gv.wt := rfl
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [camSearchEntryK, mkGroupK] at *
  clear_value gv E1 E2 E3
  generalize (n + 1) ^ 9 = Q9 at *
  generalize (n + 1) ^ 6 = Q6 at *
  omega

/-! ### 5. Direct factor search (`camFactorStep` and `camFactorFuns`) -/

/-- Monotonicity of `Prim.boundSize`. -/
theorem camDirect_boundSize_mono (p : Prim) {A B : ℕ} (h : A ≤ B) :
    p.boundSize A ≤ p.boundSize B :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- The candidate set after testing `z = 0, …, i - 1` in `Cur`. -/
def camFactorCands (Cur : Subgroup (Perm (Fin n))) (x₀ : Fin n) (i : ℕ) :
    Set (Subgroup (Perm (Fin n))) :=
  {K | ∃ z : Fin n, (z : ℕ) < i ∧ K = camFactorCand Cur x₀ z}

theorem camFactorCands_zero (Cur : Subgroup (Perm (Fin n))) (x₀ : Fin n) :
    camFactorCands Cur x₀ 0 = ∅ := by
  ext K; simp [camFactorCands]

theorem camFactorCands_succ (Cur : Subgroup (Perm (Fin n))) (x₀ : Fin n) {i : ℕ} (hi : i < n) :
    insert (camFactorCand Cur x₀ ⟨i, hi⟩) (camFactorCands Cur x₀ i) =
      camFactorCands Cur x₀ (i + 1) := by
  ext K
  simp only [Set.mem_insert_iff, camFactorCands, Set.mem_ofPred]
  constructor
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact ⟨⟨i, hi⟩, by simp, rfl⟩
    · exact ⟨z, by omega, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    rcases eq_or_ne (z : ℕ) i with rfl | hne
    · left; rfl
    · right; exact ⟨z, by omega, rfl⟩

/-- On `[[gv_Cur, gv_H₀], .nat z, acc]`:
1. `pts ← camOrbList [gv_H₀, .nat z]`
2. `w_P ← pointwiseStab [gv_H₀, pts]`
3. `camNclBest [gv_Cur, w_P, acc]`. -/
def camFactorStep (orb nb jp : ℕ) : Expr :=
  .letE (.call orb (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
  (.letE (.prim jp (mk2 (.get (arg 0) (.nat 1)) (.var 1)))
    (.call nb (mk3 (.get (arg 0) (.nat 0)) (.var 2) (arg 2))))

/-- All functions of the direct factor search at base `b` (54 functions). -/
def camFactorFuns (b jo jp jn : ℕ) : List Expr :=
  [camSearchEntryBody (b + 6) (b + 1) jp] ++
    iterFuns (b + 1) (b + 4) ++
    [camFactorStep (b + 14) (b + 5) jp, camNclBestBody (b + 6) (b + 13) jo jn] ++
    mkGroupFuns (b + 6) ++
    [camKeepBest] ++
    camOrbListFuns (b + 14)

theorem length_camFactorFuns (b jo jp jn : ℕ) : (camFactorFuns b jo jp jn).length = 54 := by
  simp [camFactorFuns, iterFuns, loopFuns, mkGroupFuns, rangeFuns, appendFuns,
    length_camOrbListFuns]

/-- Where the parts of `camFactorFuns` sit. -/
structure CamFactorAt (P : Program) (b jo jp jn : ℕ) (ho : GroupOrder) (hp : PointwiseStab)
    (hncl : NormalClosure) : Prop where
  entry : P.funs[b]? = some (camSearchEntryBody (b + 6) (b + 1) jp)
  iter : P.HasAt (b + 1) (iterFuns (b + 1) (b + 4))
  step : P.funs[b + 4]? = some (camFactorStep (b + 14) (b + 5) jp)
  nb : P.funs[b + 5]? = some (camNclBestBody (b + 6) (b + 13) jo jn)
  mg : P.HasAt (b + 6) (mkGroupFuns (b + 6))
  kb : P.funs[b + 13]? = some camKeepBest
  orb : CamOrbListAt P (b + 14)
  po : P.prims[jo]? = some (groupOrderPrim ho)
  pp : P.prims[jp]? = some (pointwiseStabPrim hp)
  pn : P.prims[jn]? = some (normalClosurePrim hncl)

theorem camFactorAt_of {P : Program} {b jo jp jn : ℕ} {ho : GroupOrder} {hp : PointwiseStab}
    {hncl : NormalClosure} (h : P.HasAt b (camFactorFuns b jo jp jn))
    (po : P.prims[jo]? = some (groupOrderPrim ho))
    (pp : P.prims[jp]? = some (pointwiseStabPrim hp))
    (pn : P.prims[jn]? = some (normalClosurePrim hncl)) :
    CamFactorAt P b jo jp jn ho hp hncl := by
  simp only [camFactorFuns] at h
  have h2 := h.left.left.left.right
  exact
  { entry := h.left.left.left.left.left.single
    iter := by simpa using h.left.left.left.left.right
    step := by simpa [iterFuns, loopFuns, Nat.add_assoc] using h2 0 (by simp)
    nb := by simpa [iterFuns, loopFuns, Nat.add_assoc] using h2 1 (by simp)
    mg := by simpa [iterFuns, loopFuns, Nat.add_assoc] using h.left.left.right
    kb := by
      simpa [iterFuns, loopFuns, mkGroupFuns, rangeFuns, appendFuns, Nat.add_assoc] using
        h.left.right.single
    orb := camOrbListAt_of (by
      simpa [iterFuns, loopFuns, mkGroupFuns, rangeFuns, appendFuns, Nat.add_assoc] using h.right)
    po := po, pp := pp, pn := pn }

def camFactorStepK : ℕ := 5 * 10 ^ 10

/-- One step `z = i < n` of the direct factor search. -/
theorem camFactorStep_spec {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    {P : Program} {b jo jp jn : ℕ} (hP : CamFactorAt P b jo jp jn ho hp hncl)
    (cur hs₀ : List (Perm (Fin n))) (hcl : cur.length ≤ n ^ 2) (hhs₀l : hs₀.length ≤ n ^ 2)
    {x₀ : Fin n} (h0g : gens hs₀ = pointwiseStab (gens cur) [x₀])
    {i : ℕ} (hi : i < n) {acc : Val} (hinv : CamBestInv (camFactorCands (gens cur) x₀ i) acc) :
    FunAll P (b + 4) (.list [.list [encGroup cur, encGroup hs₀], .nat i, acc])
      (fun w cost => CamBestInv (camFactorCands (gens cur) x₀ (i + 1)) w ∧
        cost ≤ (groupOrderPrim ho).boundSize (camLoopB n) +
          (pointwiseStabPrim hp).boundSize (camLoopB n) +
          (normalClosurePrim hncl).boundSize (camLoopB n) +
          camFactorStepK * (n + 1) ^ 15) := by
  set z : Fin n := ⟨i, hi⟩
  set c := Val.list [encGroup cur, encGroup hs₀]
  set a := Val.list [c, .nat i, acc]
  have dA0 := fun (rest : List Val) =>
    Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := rest) (j := 0) rfl
  have dCur := fun (rest : List Val) =>
    Det.get' (dA0 rest) (Det.nat 0)
      (show [encGroup cur, encGroup hs₀][0]? = some (encGroup cur) from rfl)
  have dH0 := fun (rest : List Val) =>
    Det.get' (dA0 rest) (Det.nat 1)
      (show [encGroup cur, encGroup hs₀][1]? = some (encGroup hs₀) from rfl)
  -- 1. camOrbList on [encGroup hs₀, .nat z]
  obtain ⟨O, hO, hOl, hOmem, fO⟩ := camOrbList_spec hP.orb hs₀ hhs₀l z
  have d1 := Det.call (Det.mk2 (dH0 [])
    (Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 1) rfl)) fO
  refine FunAll.intro hP.step (EvalAll.letE d1 fun vO cO h1 => ?_)
  obtain ⟨rfl, hcO⟩ := h1
  -- 2. pointwiseStab on [encGroup hs₀, encPts O]
  set E1 := [a, encPts O]
  have d2a := Det.mk2 (dH0 [encPts O]) (Det.var' (P := P) (env := E1) (i := 1) rfl)
  refine EvalAll.letE (pointwiseStab_call hp hP.pp d2a ⟨hs₀, rfl, rfl⟩) fun w_P cP h2 => ?_
  obtain ⟨hw_P, hcP⟩ := h2
  have hP_eq : pointwiseStab (gens hs₀) O =
      camOrbStab (gens cur) (pointwiseStab (gens cur) [x₀]) x₀ z := by
    rw [h0g]
    exact pointwiseStab_eq_camOrbStab (gens cur) (pointwiseStab (gens cur) [x₀]) x₀ z O
      fun y => by rw [hOmem, h0g]
  rw [hP_eq] at hw_P
  -- 3. camNclBest on [encGroup cur, w_P, acc]
  set E2 := [a, encPts O, w_P]
  have d3a := Det.mk3 (dCur [encPts O, w_P])
    (Det.var' (P := P) (env := E2) (i := 2) rfl)
    (Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := [encPts O, w_P]) (j := 2) rfl)
  refine EvalAll.call_funAll d3a fun v3 ca3 hv3 => ?_
  obtain ⟨rfl, hca3⟩ := hv3
  refine (camNclBest_spec hP.nb hP.mg hP.kb hP.po hP.pn cur
    (camOrbStab_le (gens cur) _ x₀ z) hw_P hinv).mono fun w cb3 ⟨hw, hcb3⟩ => ?_
  refine ⟨hw.congr (camFactorCands_succ (gens cur) x₀ hi), ?_⟩
  clear d3a d2a d1 fO dH0 dCur dA0
  -- Weights and bounds
  have hw_cur := wt_encGroup_le_sq hcl
  have hw_hs0 := wt_encGroup_le_sq hhs₀l
  have hw_acc := hinv.wt_le
  have hw_w := hw.wt_le
  have hw_wP := GensVal.wt_le hw_P
  have hw_O : (encPts O).wt ≤ 5 * (n + 1) ^ 2 := by
    rw [← natList_map_val_eq_encPts]
    exact wt_natList_le_sq (B := n)
      (by intro x hx; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact u.isLt.le)
      (by simpa using hOl)
  have hw_i := wt_nat_le i
  have hwc := wt_list2_le (encGroup cur) (encGroup hs₀)
  have hwa := wt_list3_le c (.nat i) acc
  have hwm1 := wt_list2_le (encGroup hs₀) (.nat i)
  have hwm2 := wt_list2_le (encGroup hs₀) (encPts O)
  have hwm3 := wt_list3_le (encGroup cur) w_P acc
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p915 : (n + 1) ^ 9 ≤ (n + 1) ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn2 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hb_ps := (pointwiseStabPrim hp).bound_le (v := .list [encGroup hs₀, encPts O])
    (B := camLoopB n) ((Val.size_le_wt _).trans (by unfold camLoopB; omega))
  have hb_ncl : (normalClosurePrim hncl).boundSize (2 * (encGroup cur).wt + 700 * (n + 1) ^ 6) ≤
      (normalClosurePrim hncl).boundSize (camLoopB n) :=
    camDirect_boundSize_mono (normalClosurePrim hncl) (by unfold camLoopB; omega)
  have hb_ord : (groupOrderPrim ho).boundSize (320 * (n + 1) ^ 6) ≤
      (groupOrderPrim ho).boundSize (camLoopB n) :=
    camDirect_boundSize_mono (groupOrderPrim ho) (by unfold camLoopB; omega)
  have he_a : (Val.list [c, .nat i, acc]).wt = a.wt := rfl
  have he_c : (Val.list [encGroup cur, encGroup hs₀]).wt = c.wt := rfl
  simp only [camFactorStepK, camOrbListK, camNclBestK] at *
  clear_value a c E1 E2
  generalize (n + 1) ^ 15 = Q15 at *
  generalize (n + 1) ^ 9 = Q9 at *
  generalize (n + 1) ^ 6 = Q6 at *
  generalize (n + 1) ^ 2 = Q2 at *
  omega

def camFactorK : ℕ := 10 ^ 11

/-- Cost bound of the direct factor search on `encGroup cur` with `cur.length ≤ n ^ 2`. -/
noncomputable def camFactorCost (ho : GroupOrder) (hp : PointwiseStab) (hncl : NormalClosure)
    (n : ℕ) : ℕ :=
  (n + 1) * ((groupOrderPrim ho).boundSize (camLoopB n) +
    (pointwiseStabPrim hp).boundSize (camLoopB n) +
    (normalClosurePrim hncl).boundSize (camLoopB n)) +
  camFactorK * (n + 1) ^ 16

/-- **Direct factor search (Proposition 2.2).** On `encGroup cur` with `gens cur = camProd e S`
(`S.Nonempty`), returns `w` with `GensVal n w (camProd e {i₀})` for some `i₀ ∈ S`. -/
theorem camFactor_spec {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    {P : Program} {b jo jp jn : ℕ} (hP : CamFactorAt P b jo jp jn ho hp hncl)
    (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) (hn : 0 < n)
    {S : Finset (Fin r)} (hne : S.Nonempty)
    (cur : List (Perm (Fin n))) (hcl : cur.length ≤ n ^ 2)
    (hcur : gens cur = camProd e S) :
    FunAll P b (encGroup cur)
      (fun w cost => (∃ i₀ ∈ S, GensVal n w (camProd e {i₀})) ∧
        cost ≤ camFactorCost ho hp hncl n) := by
  set x₀ : Fin n := ⟨0, hn⟩
  have hne_cand : ∃ K ∈ camFactorCands (gens cur) x₀ n, 1 < Nat.card K := by
    obtain ⟨i₀, hi₀S⟩ := hne
    obtain ⟨z₀, hz₀⟩ := camFactorCand_single (e := e) hm hk1 hk hi₀S x₀
    refine ⟨camFactorCand (gens cur) x₀ z₀, ⟨z₀, z₀.isLt, rfl⟩, ?_⟩
    rw [hcur, hz₀, camX_card_prod (by omega) hk1 (by omega), Finset.card_singleton, pow_one]
    have h5 : Nat.factorial 5 ≤ m.factorial := Nat.factorial_le hm
    have : Nat.factorial 5 = 120 := by decide
    have := Nat.choose_pos (show k ≤ m by omega)
    omega
  set StepB := (groupOrderPrim ho).boundSize (camLoopB n) +
    (pointwiseStabPrim hp).boundSize (camLoopB n) +
    (normalClosurePrim hncl).boundSize (camLoopB n) +
    camFactorStepK * (n + 1) ^ 15
  set LCost := n * StepB + loopModK * (n + 1) * (5000 * (n + 1) ^ 6)
  refine (camSearchEntry_spec hP.entry hP.mg hP.pp cur hn hne_cand
    (LCost := LCost) (fun hs₀ hhs₀l h0g => ?_)).mono fun w cost ⟨⟨Best, hBmem, hbw, hBgt, hBmin⟩, hc⟩ => ?_
  · have h0 : CamBestInv (camFactorCands (gens cur) x₀ 0) (.list [.list [], .nat 0]) := by
      rw [camFactorCands_zero]; exact camBestInv_empty
    refine (iter_spec hP.iter h0 (M := 40 * (n + 1) ^ 6) (B := fun _ => StepB)
      (fun i acc _ h => h.wt_le)
      (fun i acc hi h => camFactorStep_spec hP cur hs₀ hcl hhs₀l h0g hi h)).mono
      fun res cl ⟨hinv, hcl'⟩ => ⟨hinv, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcl'
    have hw_cur := wt_encGroup_le_sq hcl
    have hw_hs0 := wt_encGroup_le_sq hhs₀l
    have w1 := wt_list2_le (encGroup cur) (encGroup hs₀)
    have w2 := wt_list2_le (.list []) (.nat 0)
    have w3 := wt_list3_le (.list [encGroup cur, encGroup hs₀]) (.nat n) (.list [.list [], .nat 0])
    have wn := wt_nat_le n
    have wn0 := wt_nat_le 0
    have wnil := wt_list_nil
    have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have hsum : (Val.list [.list [encGroup cur, encGroup hs₀], .nat n,
        .list [.list [], .nat 0]]).wt + n + 40 * (n + 1) ^ 6 + 1 ≤ 5000 * (n + 1) ^ 6 := by omega
    have hmul := Nat.mul_le_mul_left (loopModK * (n + 1)) hsum
    omega
  · obtain ⟨z, -, rfl⟩ := hBmem
    rw [hcur] at hbw hBgt hBmin
    obtain ⟨i₀, hi₀S, hi₀eq⟩ := camFactorCand_min_is_single (e := e) hm hk1 hk x₀ z hBgt
      fun z' hz' => hBmin _ ⟨z', z'.isLt, rfl⟩ hz'
    refine ⟨⟨i₀, hi₀S, hi₀eq ▸ hbw⟩, ?_⟩
    have hw_cur := wt_encGroup_le_sq hcl
    have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have hb_ps : (pointwiseStabPrim hp).boundSize (2 * (encGroup cur).wt + 30 * (n + 1)) ≤
        (pointwiseStabPrim hp).boundSize (camLoopB n) :=
      camDirect_boundSize_mono (pointwiseStabPrim hp) (by unfold camLoopB; omega)
    set S3 := (groupOrderPrim ho).boundSize (camLoopB n) +
      (pointwiseStabPrim hp).boundSize (camLoopB n) +
      (normalClosurePrim hncl).boundSize (camLoopB n)
    have hps_le_S3 : (pointwiseStabPrim hp).boundSize (camLoopB n) ≤ S3 := by
      unfold S3; omega
    have eStep : n * StepB = n * S3 + n * (camFactorStepK * (n + 1) ^ 15) := by
      unfold StepB; ring
    have hStep16 : n * (camFactorStepK * (n + 1) ^ 15) ≤ camFactorStepK * (n + 1) ^ 16 := by
      calc n * (camFactorStepK * (n + 1) ^ 15)
          ≤ (n + 1) * (camFactorStepK * (n + 1) ^ 15) := Nat.mul_le_mul_right _ (by omega)
        _ = camFactorStepK * (n + 1) ^ 16 := by ring
    have hLoop7 : loopModK * (n + 1) * (5000 * (n + 1) ^ 6) =
        5000 * loopModK * (n + 1) ^ 7 := by ring
    have eS3 : (n + 1) * S3 = n * S3 + S3 := by ring
    have p616 : (n + 1) ^ 6 ≤ (n + 1) ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
    have p716 : (n + 1) ^ 7 ≤ (n + 1) ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
    have p916 : (n + 1) ^ 9 ≤ (n + 1) ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
    unfold camFactorCost
    rw [eS3]
    unfold LCost at hc
    rw [eStep, hLoop7] at hc
    simp only [camFactorK, camFactorStepK, camSearchEntryK, loopModK] at *
    clear_value S3 StepB LCost
    generalize (n + 1) ^ 16 = Q16 at *
    generalize (n + 1) ^ 9 = Q9 at *
    generalize (n + 1) ^ 7 = Q7 at *
    generalize (n + 1) ^ 6 = Q6 at *
    omega

end GI.Impl
