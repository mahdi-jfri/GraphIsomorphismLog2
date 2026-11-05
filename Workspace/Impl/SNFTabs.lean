module

public import Workspace.Impl.HNFTabs
public import Workspace.Proved.SNFEmb

@[expose] public section

/-!
# Tables for the Smith form program

Two tables built with `hnfTab`:

* the transpose of a square matrix (`snfTrTab_spec`), cell `M j i` on context `[M]`;
* the matrix `snfEmb p q α β γ δ` (`snfEmbTab_spec`), on context `[α, β, γ, δ, p, q]`. With
  `p = q = n` it is the identity.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-! ### Transpose -/

/-- The cell of the transpose: entry `(j, i)` of the matrix in the context. -/
def snfTrCellF : Expr := .get (.get (hnfCx 0) hnfCellJE) hnfCellIE

theorem snfTrCell_spec {P : Program} {f n : ℕ} (hf : P.funs[f]? = some snfTrCellF)
    (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) (i j : Fin n) :
    FunDet P f (hnfCellArg [encIntMatrix M] r n i j) (encInt (M j i))
      (hnfHCellCost (hnfCellArg [encIntMatrix M] r n i j).wt) := by
  set C : List Val := [encIntMatrix M] with hC
  set Z := (hnfCellArg C r n i j).wt with hZ
  have di := hnf_det_ci (P := P) (C := C) (r := r) (n := n) (i := i) (j := j) []
  have dj := hnf_det_cj (P := P) (C := C) (r := r) (n := n) (i := i) (j := j) []
  have dM := hnf_det_cx (P := P) (C := C) (r := r) (n := n) (i := i) (j := j) (k := 0) []
    (show C[0]? = some (encIntMatrix M) from rfl)
  have dx := Det.get' (Det.get' dM dj (hnf_mat_get M j)) di (hnf_vec_get (M j) i)
  apply FunDet.intro hf
  refine dx.mono ?_
  have wC : (Val.list C).wt < Z := (hnfCellArg_wt C r n i j).1
  have wM : (encIntMatrix M).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC])
  have wrow := hnf_row_wt_lt M j
  have went := linVecEntryWt (M j) i
  have e2 : (Val.list ((List.finRange n).map fun y => encInt (M j y))).wt = (linVecVal (M j)).wt := rfl
  unfold hnfHCellCost
  omega

/-- **The transpose table.** -/
theorem snfTrTab_spec {P : Program} {tb cell n : ℕ} (ht : hnfTabAt P tb cell)
    (hf : P.funs[cell]? = some snfTrCellF) (M : Matrix (Fin n) (Fin n) ℤ) {X : ℕ}
    (hX : (Val.list [.list [encIntMatrix M], .nat n, .nat n]).wt ≤ X) (hnX : n ≤ X) :
    FunDet P tb (.list [.list [encIntMatrix M], .nat n, .nat n]) (encIntMatrix M.transpose)
      (hnfTabCost X (hnfHCellCost (10 * X + 18))) :=
  hnfTab_spec ht _ n n (fun i j => encInt (M j i)) _ X hX hnX hnX fun i j =>
    (snfTrCell_spec hf M n i j).mono (hnfHCellCost_mono (hnfCellArg_wt_le i.isLt j.isLt hX))

/-! ### Blocks inside the identity -/

/-- `snfEmb` on natural indices. -/
def snfEmbV (p q : ℕ) (α β γ δ : ℤ) (i j : ℕ) : ℤ :=
  if i = p then (if j = p then α else if j = q then β else 0)
  else if i = q then (if j = p then γ else if j = q then δ else 0)
  else if i = j then 1 else 0

theorem snfEmb_eq {n : ℕ} (p q : ℕ) (α β γ δ : ℤ) (i j : Fin n) :
    snfEmb (n := n) p q α β γ δ i j = snfEmbV p q α β γ δ i j := by
  simp only [snfEmb, snfEmbV, Fin.ext_iff]

/-- Row `p` or `q` of the block. -/
def snfEmbRowE (a b : ℕ) : Expr :=
  .ite (.arith .eq hnfCellJE (hnfCx 4)) (hnfCx a)
    (.ite (.arith .eq hnfCellJE (hnfCx 5)) (hnfCx b) hnfZeroE)

/-- The cell of `snfEmb p q α β γ δ` on context `[α, β, γ, δ, p, q]`. -/
def snfEmbCellF : Expr :=
  .ite (.arith .eq hnfCellIE (hnfCx 4)) (snfEmbRowE 0 1)
    (.ite (.arith .eq hnfCellIE (hnfCx 5)) (snfEmbRowE 2 3)
      (.ite (.arith .eq hnfCellIE hnfCellJE) hnfOneE hnfZeroE))

/-- The context of the block table. -/
def snfEmbCtx (p q : ℕ) (α β γ δ : ℤ) : List Val :=
  [encInt α, encInt β, encInt γ, encInt δ, .nat p, .nat q]

def snfEmbCellCost (Z : ℕ) : ℕ := 1000 * (Z + 40)

theorem snfEmbCellCost_mono {Y Z : ℕ} (h : Y ≤ Z) : snfEmbCellCost Y ≤ snfEmbCellCost Z := by
  unfold snfEmbCellCost; omega

set_option maxHeartbeats 2000000 in
theorem snfEmbCell_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some snfEmbCellF)
    (p q : ℕ) (α β γ δ : ℤ) (r nn i j : ℕ) :
    FunDet P f (hnfCellArg (snfEmbCtx p q α β γ δ) r nn i j) (encInt (snfEmbV p q α β γ δ i j))
      (snfEmbCellCost (hnfCellArg (snfEmbCtx p q α β γ δ) r nn i j).wt) := by
  set C := snfEmbCtx p q α β γ δ with hC
  set Z := (hnfCellArg C r nn i j).wt with hZ
  have di := hnf_det_ci (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) []
  have dj := hnf_det_cj (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) []
  have d0 := hnf_det_cx (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) (k := 0) []
    (show C[0]? = some (encInt α) from rfl)
  have d1 := hnf_det_cx (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) (k := 1) []
    (show C[1]? = some (encInt β) from rfl)
  have d2 := hnf_det_cx (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) (k := 2) []
    (show C[2]? = some (encInt γ) from rfl)
  have d3 := hnf_det_cx (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) (k := 3) []
    (show C[3]? = some (encInt δ) from rfl)
  have d4 := hnf_det_cx (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) (k := 4) []
    (show C[4]? = some (.nat p) from rfl)
  have d5 := hnf_det_cx (P := P) (C := C) (r := r) (n := nn) (i := i) (j := j) (k := 5) []
    (show C[5]? = some (.nat q) from rfl)
  have wC : (Val.list C).wt < Z := (hnfCellArg_wt C r nn i j).1
  have wa : (encInt α).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, snfEmbCtx])
  have wb : (encInt β).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, snfEmbCtx])
  have wc : (encInt γ).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, snfEmbCtx])
  have wd : (encInt δ).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, snfEmbCtx])
  have w0 : (encInt 0).wt ≤ 15 := by decide
  have w1 : (encInt 1).wt ≤ 21 := by decide
  have hrow : ∀ (a b : ℕ) (x y : ℤ), (encInt x).wt < Z → (encInt y).wt < Z →
      (hcx : Det P [hnfCellArg C r nn i j] (hnfCx a) (encInt x) (5 * Z + a + 30)) →
      (hcy : Det P [hnfCellArg C r nn i j] (hnfCx b) (encInt y) (5 * Z + b + 30)) →
      a ≤ 3 → b ≤ 3 →
      Det P [hnfCellArg C r nn i j] (snfEmbRowE a b)
        (encInt (if j = p then x else if j = q then y else 0)) (100 * (Z + 40)) := by
    intro a b x y hx hy hcx hcy ha hb
    refine (hnf_det_ite_eq dj d4 (ct := 6 * Z + 40) (ce := 30 * (Z + 40)) ?_ ?_).mono ?_
    · intro h; rw [if_pos h]; exact hcx.mono (by omega)
    · intro h
      rw [if_neg h]
      refine (hnf_det_ite_eq dj d5 (ct := 6 * Z + 40) (ce := 50) ?_ ?_).mono ?_
      · intro h'; rw [if_pos h']; exact hcy.mono (by omega)
      · intro h'; rw [if_neg h']; exact hnf_det_zero
      · split_ifs <;> omega
    · split_ifs <;> omega
  have r1 := hrow 0 1 α β (by omega) (by omega) d0 d1 (by omega) (by omega)
  have r2 := hrow 2 3 γ δ (by omega) (by omega) d2 d3 (by omega) (by omega)
  have hv : ∀ x : ℤ, x = α ∨ x = β ∨ x = γ ∨ x = δ ∨ x = 0 ∨ x = 1 → (encInt x).wt ≤ Z + 21 := by
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  have hval := hv (snfEmbV p q α β γ δ i j) (by unfold snfEmbV; split_ifs <;> simp)
  apply FunDet.intro hf
  refine (hnf_det_ite_eq di d4 (ct := 100 * (Z + 40)) (ce := 300 * (Z + 40)) ?_ ?_).mono ?_
  · intro h; unfold snfEmbV; rw [if_pos h]; exact r1
  · intro h
    have hv2 := hv (if i = q then (if j = p then γ else if j = q then δ else 0)
      else if i = j then 1 else 0) (by split_ifs <;> simp)
    unfold snfEmbV; rw [if_neg h]
    refine (hnf_det_ite_eq di d5 (ct := 100 * (Z + 40)) (ce := 100 * (Z + 40)) ?_ ?_).mono ?_
    · intro h'; rw [if_pos h']; exact r2
    · intro h'
      rw [if_neg h']
      refine (hnf_det_ite_eq di dj (ct := 100) (ce := 50) ?_ ?_).mono ?_
      · intro h''; rw [if_pos h'']; exact hnf_det_one
      · intro h''; rw [if_neg h'']; exact hnf_det_zero
      · split_ifs <;> omega
    · omega
  · unfold snfEmbCellCost; omega

/-- **The block table.** -/
theorem snfEmbTab_spec {P : Program} {tb cell n : ℕ} (ht : hnfTabAt P tb cell)
    (hf : P.funs[cell]? = some snfEmbCellF) (p q : ℕ) (α β γ δ : ℤ) {X : ℕ}
    (hX : (Val.list [.list (snfEmbCtx p q α β γ δ), .nat n, .nat n]).wt ≤ X) (hnX : n ≤ X) :
    FunDet P tb (.list [.list (snfEmbCtx p q α β γ δ), .nat n, .nat n])
      (encIntMatrix (snfEmb (n := n) p q α β γ δ))
      (hnfTabCost X (snfEmbCellCost (10 * X + 18))) := by
  have h := hnfTab_spec ht _ n n (fun i j => encInt (snfEmbV p q α β γ δ i j)) _ X hX hnX hnX
    fun i j => (snfEmbCell_spec hf p q α β γ δ n n i j).mono
      (snfEmbCellCost_mono (hnfCellArg_wt_le i.isLt j.isLt hX))
  show FunDet P tb _ (.list ((List.finRange n).map fun i =>
    .list ((List.finRange n).map fun j => encInt (snfEmb (n := n) p q α β γ δ i j)))) _
  simp only [snfEmb_eq]
  exact h

end GI.Impl
