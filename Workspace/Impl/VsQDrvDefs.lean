import Workspace.Impl.VsQPaste
import Workspace.Impl.VsQApp
import Workspace.Impl.VsWProgKer

/-!
# The driver, definitions

The driver solves the problem of a state (`GI.Proved.VsQSt`) by asking the analysis program for a
leaf answer or a split, and in the second case by solving, for every coset representative `t`,
the problems of the chain of the split for the coset group, then pasting.

* `vsQStV`: the value of a state, `[Γ, ⟨hs⟩, W', W, x, y]`.
* `vsQCV`: the value of a chain state, `[Γ, x, lows, [⟨K⟩, upper, y, i]]`.
* `vsQDrvE` (the driver), `vsQDrvCE` (the chain), `vsQTfE` (one coset), `vsQDrvFuns`.
* `VsQSplitOK`, `VsQAnaOut`: what the analysis must return.
* `VsQDSz`: the size bound `S` used in all weight bounds.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-! ### Values -/

/-- The value of a state. -/
def vsQStV (I : VecStabInst) (s : VsQSt I) : Val :=
  .list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]

/-- The value of a list of bases. -/
def vsQLowsV (lows : List (List (List ℕ))) : Val := .list (lows.map vsWVs)

/-- The value of a chain state: the group `K`, the upper space, the target `y` and the position
`i` in the list of lower spaces. -/
def vsQCV (I : VecStabInst) (K : List (Perm (Fin I.n))) (upper : List (List ℕ))
    (lows : List (List (List ℕ))) (x y : List ℕ) (i : ℕ) : Val :=
  .list [vsQGam I, natList x, vsQLowsV lows, .list [encGroup K, vsWVs upper, natList y, .nat i]]

/-- The value of a leaf of the analysis. -/
def vsQLeafV (a : Option (Perm (Fin I.n) × List (Perm (Fin I.n)))) : Val := .list [.nat 0, vsQAnsV a]

/-- The value of a split: coset representatives, the coset group, and the lower spaces. -/
def vsQSplitV (ts cs : List (Perm (Fin I.n))) (lows : List (List (List ℕ))) : Val :=
  .list [.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows]

/-! ### What the analysis returns -/

/-- A correct split of the problem of `s`. -/
structure VsQSplitOK (s : VsQSt I) (E Tm : ℕ) (ts cs : List (Perm (Fin I.n)))
    (lows : List (List (List ℕ))) : Prop where
  csl : cs.length ≤ I.n ^ 2
  cle : gens cs ≤ gens s.hs
  tmem : ∀ t ∈ ts, t ∈ gens s.hs
  cov : ∀ h ∈ gens s.hs, ∃ t ∈ ts, t⁻¹ * h ∈ gens cs
  tl : ts.length ≤ Tm
  chain : VsQChain I (s.ws :: lows)
  ne : lows ≠ []
  last : vsQSp I (lows.getLast ne) = vsQSp I s.ws'
  fit : ∀ u ∈ lows, VsWFit I.p I.d u ∧ u.length ≤ I.d
  inv : ∀ u ∈ lows, VsQInv I (gens cs) (vsQSp I u)
  case : (ts.length = 1 ∧ 2 ≤ lows.length) ∨
    (¬ s.Ab ∧ 2 ≤ lows.length ∧ (∃ e, ∀ x ∈ vsQDims I (s.ws :: lows), x = e) ∧
      ts.length ≤ (lows.length + 1) ^ E) ∨
    (¬ s.Ab ∧ lows.length = 1 ∧ VsQAb I (gens cs) (vsQSp I s.ws) (vsQSp I s.ws') ∧ 2 ≤ s.dim ∧
      ts.length ≤ 24 * s.dim)

/-- What the analysis returns on a valid state: a correct leaf answer or a correct split. -/
def VsQAnaOut {s : VsQSt I} (hs : VsQStOK s) (E Tm : ℕ) (w : Val) : Prop :=
  (∃ a, w = vsQLeafV a ∧ VsQAnsOK hs.prob a) ∨
    (∃ ts cs lows, w = vsQSplitV ts cs lows ∧ VsQSplitOK s E Tm ts cs lows)

/-! ### Programs -/

/-- The list of six values. -/
def mk6 (a b c d e f : Expr) : Expr := .snoc (.snoc (mk4 a b c d) e) f

/-- The driver, on a state. -/
def vsQDrvE (ana mp paste : ℕ) : Expr :=
  .letE (.call ana (.var 0))
    (.ite (.get (.var 1) (.nat 0))
      (.call paste (.call mp (mk2 (mk2 (.var 0) (.var 1)) (.get (.var 1) (.nat 1)))))
      (.get (.var 1) (.nat 1)))

/-- Entry `k` of the last part of a chain state. -/
def vsQCur (k : ℕ) : Expr := .get (arg 3) (.nat k)

/-- The chain, on a chain state. -/
def vsQDrvCE (drv drvc ai cmp : ℕ) : Expr :=
  .ite (.arith .sub (.length (arg 2)) (vsQCur 3))
    (.letE (.call drv (mk6 (arg 0) (vsQCur 0) (.get (arg 2) (vsQCur 3)) (vsQCur 1) (arg 1)
        (vsQCur 2)))
      (.ite (.get (.var 1) (.nat 0))
        (.letE (.call ai (mk3 (arg 0) (.get (.var 1) (.nat 1)) (vsQCur 2)))
          (.letE (.call drvc (mk4 (arg 0) (arg 1) (arg 2)
              (mk4 (.get (.var 1) (.nat 2)) (.get (arg 2) (vsQCur 3)) (.var 2)
                (.arith .add (vsQCur 3) (.nat 1)))))
            (.ite (.get (.var 3) (.nat 0))
              (mk3 (.nat 1) (.call cmp (mk2 (.get (.var 1) (.nat 1)) (.get (.var 3) (.nat 1))))
                (.get (.var 3) (.nat 2)))
              (mk1 (.nat 0)))))
        (mk1 (.nat 0))))
    (mk3 (.nat 1) (.get (.get (vsQCur 0) (.nat 1)) (.nat 0)) (vsQCur 0))

/-- Entry `k` of the state in the context of a coset. -/
def vsQS0 (k : ℕ) : Expr := .get (.get (arg 0) (.nat 0)) (.nat k)

/-- Entry `k` of the split in the context of a coset. -/
def vsQA0 (k : ℕ) : Expr := .get (.get (arg 0) (.nat 1)) (.nat k)

/-- One coset, on `[[state, split], t]`. -/
def vsQTfE (drvc ai cmp : ℕ) : Expr :=
  .letE (.call ai (mk3 (vsQS0 0) (arg 1) (vsQS0 5)))
    (.letE (.call drvc (mk4 (vsQS0 0) (vsQS0 4) (vsQA0 3) (mk4 (vsQA0 2) (vsQS0 3) (.var 1) (.nat 0))))
      (.ite (.get (.var 2) (.nat 0))
        (mk3 (.nat 1) (.call cmp (mk2 (arg 1) (.get (.var 2) (.nat 1)))) (.get (.var 2) (.nat 2)))
        (mk1 (.nat 0))))

/-- The driver at base `b` (6 functions): driver at `b`, chain at `b + 1`, coset at `b + 2`, map
at `b + 3`. -/
def vsQDrvFuns (b ana ai cmp paste : ℕ) : List Expr :=
  [vsQDrvE ana (b + 3) paste, vsQDrvCE b (b + 1) ai cmp, vsQTfE (b + 1) ai cmp] ++
    mapFuns (b + 3) (b + 2)

/-! ### Sizes -/

/-- The size bound. -/
structure VsQDSz (I : VecStabInst) (S Tm : ℕ) : Prop where
  n : I.n + 1 ≤ S
  d : I.d + 1 ≤ S
  p : I.p ≤ S
  g : (vsQGam I).wt ≤ S
  t : Tm + 1 ≤ S

namespace VsQDSz

variable {S Tm : ℕ} (h : VsQDSz I S Tm)
include h

theorem one_le : 1 ≤ S := by have := h.n; omega

theorem pow_le {a b : ℕ} (hab : a ≤ b) : S ^ a ≤ S ^ b := Nat.pow_le_pow_right h.one_le hab

theorem wt_vec {y : List ℕ} (hy : VsWFit I.p I.d [y]) : (natList y).wt ≤ 20 * S ^ 2 := by
  have h1 := wt_natList_le_sq (B := S) (xs := y) (fun z hz => ((hy y (by simp)).1 z hz).le.trans h.p)
    (by rw [(hy y (by simp)).2]; have := h.d; omega)
  have : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by have := h.one_le; nlinarith
  omega

theorem wt_bas {us : List (List ℕ)} (hu : VsWFit I.p I.d us) (hl : us.length ≤ I.d) :
    (vsWVs us).wt ≤ 100 * S ^ 3 := by
  have h1 := wt_vsWVs_le (N := S) (VsWFit.bnd hu h.p (by have := h.d; omega)) (by have := h.d; omega)
  have : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
    have := h.one_le
    have : S + 1 ≤ 2 * S := by omega
    calc (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 * S ^ 3 := by ring
  have := h.pow_le (show 0 ≤ 3 by omega)
  simp at this
  omega

theorem wt_lows {lows : List (List (List ℕ))} (hf : ∀ u ∈ lows, VsWFit I.p I.d u ∧ u.length ≤ I.d)
    (hl : lows.length ≤ I.d) : (vsQLowsV lows).wt ≤ 300 * S ^ 4 := by
  have h1 := vs_wt_list_le_of (lows.map vsWVs) (c := 100 * S ^ 3) (by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact h.wt_bas (hf u hu).1 (hf u hu).2)
  rw [List.length_map] at h1
  have : lows.length * (2 * (100 * S ^ 3) + 1) ≤ S * (201 * S ^ 3) :=
    Nat.mul_le_mul (by have := h.d; omega) (by have := h.pow_le (show 0 ≤ 3 by omega); simp at this; omega)
  have e : S * (201 * S ^ 3) = 201 * S ^ 4 := by ring
  have := h.pow_le (show 0 ≤ 4 by omega); simp at this
  unfold vsQLowsV
  omega

theorem wt_group {hs : List (Perm (Fin I.n))} (hl : hs.length ≤ I.n ^ 2) :
    (encGroup hs).wt ≤ 320 * S ^ 6 :=
  (wt_encGroup_le_sq hl).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.n 6))

theorem wt_perm (g : Perm (Fin I.n)) : (encPerm g).wt ≤ 4 * S ^ 2 :=
  (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.n 2))

theorem wt_ans {a : Option (Perm (Fin I.n) × List (Perm (Fin I.n)))}
    (ha : ∀ r ∈ a, r.2.length ≤ I.n ^ 2) : (vsQAnsV a).wt ≤ 700 * S ^ 6 :=
  (wt_vsQAnsV_le ha).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.n 6))

theorem wt_st {s : VsQSt I} (hs : VsQStOK s) : (vsQStV I s).wt ≤ 2000 * S ^ 6 := by
  have h1 := wt_list_le [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]
  have := h.g
  have := h.wt_group hs.hsl
  have := h.wt_bas hs.fit' hs.wl'
  have := h.wt_bas hs.fit hs.wl
  have := h.wt_vec hs.fx
  have := h.wt_vec hs.fy
  have := h.pow_le (show 2 ≤ 6 by omega)
  have := h.pow_le (show 3 ≤ 6 by omega)
  have := h.pow_le (show 1 ≤ 6 by omega)
  have := h.pow_le (show 0 ≤ 6 by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, pow_one, pow_zero] at *
  unfold vsQStV
  omega

theorem wt_cv {K : List (Perm (Fin I.n))} {upper : List (List ℕ)} {lows : List (List (List ℕ))}
    {x y : List ℕ} {i : ℕ} (hK : K.length ≤ I.n ^ 2) (hu : VsWFit I.p I.d upper)
    (hul : upper.length ≤ I.d) (hf : ∀ u ∈ lows, VsWFit I.p I.d u ∧ u.length ≤ I.d)
    (hl : lows.length ≤ I.d) (hx : VsWFit I.p I.d [x]) (hy : VsWFit I.p I.d [y]) (hi : i ≤ S) :
    (vsQCV I K upper lows x y i).wt ≤ 3000 * S ^ 6 := by
  have h1 := wt_list4_le (vsQGam I) (natList x) (vsQLowsV lows)
    (.list [encGroup K, vsWVs upper, natList y, .nat i])
  have h2 := wt_list4_le (encGroup K) (vsWVs upper) (natList y) (.nat i)
  have := h.g
  have := h.wt_group hK
  have := h.wt_bas hu hul
  have := h.wt_lows hf hl
  have := h.wt_vec hx
  have := h.wt_vec hy
  have := wt_nat_le i
  have := h.pow_le (show 2 ≤ 6 by omega)
  have := h.pow_le (show 3 ≤ 6 by omega)
  have := h.pow_le (show 4 ≤ 6 by omega)
  have := h.pow_le (show 1 ≤ 6 by omega)
  have := h.pow_le (show 0 ≤ 6 by omega)
  simp only [pow_one, pow_zero] at *
  unfold vsQCV
  omega

end VsQDSz

end GI.Impl
