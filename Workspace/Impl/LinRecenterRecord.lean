module

public import Workspace.Impl.LinRecenterOffset
public import Workspace.Impl.LinIntAffineMatrix

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linRecenterModuli_snoc {d : ℕ} (m : Fin d → ℕ) :
    linVecVal (linFiniteModuli m) =
      .list (((List.finRange d).map fun i => encInt (m i : ℤ)) ++ [encInt 0]) :=
  congrArg Val.list (linExtend_value encInt (fun i => (m i : ℤ)) 0)

def linRecenterRecordF (offset matrix : ℕ) : Expr :=
  .letE (.call offset (mk4 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0))
    (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 1))))
    (.letE (.call matrix (mk2 (.get (arg 1) (.nat 0)) (.var 1)))
      (.letE (.call offset (mk4 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 2))
        (.get (arg 1) (.nat 3)) (.get (arg 0) (.nat 1))))
        (.letE (.call matrix (mk2 (.get (arg 1) (.nat 2)) (.var 3)))
          (mk3 (.snoc (.get (arg 0) (.nat 0)) linIntZeroE) (.var 2) (.var 4)))))

def linRecenterRecordFuns (b : ℕ) : List Expr :=
  [linRecenterRecordF (b + 1) (b + 54)] ++ linRecenterOffsetFuns (b + 1) ++ linIntAffineMatrixFuns (b + 54)

theorem linRecenterRecordFuns_length (b : ℕ) : (linRecenterRecordFuns b).length = 61 := rfl

structure linRecenterRecordAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linRecenterRecordF (b + 1) (b + 54))
  offset : linRecenterOffsetAt P (b + 1)
  matrix : linIntAffineMatrixAt P (b + 54)

theorem linRecenterRecordAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linRecenterRecordFuns b)) : linRecenterRecordAt P b where
  entry := (h.block (gs := [linRecenterRecordF (b + 1) (b + 54)]) 0 rfl).single
  offset := linRecenterOffsetAt_of (h.block 1 rfl)
  matrix := linIntAffineMatrixAt_of (h.block 54 rfl)

def linRecenterRecordOffsetBudget (W : ℕ) : ℕ := linRecenterOffsetCost (100 * (W + 1))
def linRecenterRecordMatrixArg (W : ℕ) : ℕ := 100 * (W + linRecenterRecordOffsetBudget W + 1)
def linRecenterRecordMatrixBudget (W : ℕ) : ℕ := linIntAffineMatrixCost (linRecenterRecordMatrixArg W) W
def linRecenterRecordCost (W : ℕ) : ℕ :=
  1000000 * (W + linRecenterRecordOffsetBudget W + linRecenterRecordMatrixBudget W + 1)

noncomputable def linPlainAffineVal {G : Type*} [Group G] {d : ℕ} (m : Fin d → ℕ)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m) (g : G) : Val :=
  .list [encIntMatrix (linFiniteIntMatrix m (ρ g).toAddMonoidHom), linVecVal (fun i => ((c g i).val : ℤ)),
    encIntMatrix (linFiniteIntMatrix m (ρ g⁻¹).toAddMonoidHom), linVecVal (fun i => ((c g⁻¹ i).val : ℤ))]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
theorem linRecenterRecord_spec {P : Program} {b d : ℕ} {G : Type*} [Group G]
    (h : linRecenterRecordAt P b) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (w : linFiniteVec m) (g : G) :
    let ctx := Val.list [linVecVal (fun i => (m i : ℤ)), linVecVal (fun i => ((w i).val : ℤ))]
    let a := Val.list [ctx, linPlainAffineVal m ρ c g]
    FunDet P b a (linFiniteAffineVal m ρ (linFiniteRecenter ρ c w) g) (linRecenterRecordCost a.wt) := by
  let orders := linVecVal (fun i => (m i : ℤ))
  let wv := linVecVal (fun i => ((w i).val : ℤ))
  let ctx := Val.list [orders, wv]
  let record := linPlainAffineVal m ρ c g
  let a := Val.list [ctx, record]
  let W := a.wt
  let c' := linFiniteRecenter ρ c w
  let U := linVecVal (fun i => ((c' g i).val : ℤ))
  let Ui := linVecVal (fun i => ((c' g⁻¹ i).val : ℤ))
  let M := encIntMatrix (linFiniteActionMatrix m ρ c' g)
  let Mi := encIntMatrix (linFiniteActionMatrix m ρ c' g⁻¹)
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wr : record.wt < W := wt_le_wt_list (by simp [a, W])
  have wo : orders.wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have ww : wv.wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wmat (k : G) (hk : k = g ∨ k = g⁻¹) :
      (encIntMatrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom)).wt < record.wt := by
    rcases hk with rfl | rfl <;> exact wt_le_wt_list (by simp [record, linPlainAffineVal])
  have woff (k : G) (hk : k = g ∨ k = g⁻¹) :
      (linVecVal (fun i => ((c k i).val : ℤ))).wt < record.wt := by
    rcases hk with rfl | rfl <;> exact wt_le_wt_list (by simp [record, linPlainAffineVal])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (m i : ℤ))
    simp only [List.length_map, List.length_finRange] at hh
    change d < orders.wt at hh
    omega
  have ho (k : G) (hk : k = g ∨ k = g⁻¹) :
      FunDet P (b + 1) (.list [orders, encIntMatrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom),
        linVecVal (fun i => ((c k i).val : ℤ)), wv])
        (linVecVal (fun i => ((c' k i).val : ℤ))) (linRecenterRecordOffsetBudget W) := by
    have wm := wmat k hk
    have wu := woff k hk
    have hh := wt_list4_le orders (encIntMatrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom))
      (linVecVal (fun i => ((c k i).val : ℤ))) wv
    have hb : (Val.list [orders, encIntMatrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom),
        linVecVal (fun i => ((c k i).val : ℤ)), wv]).wt ≤ 100 * (W + 1) := by omega
    exact (linRecenterOffset_action_spec h.offset m hm ρ c w k).mono (linRecenterOffsetCost_mono hb)
  have hoF := ho g (Or.inl rfl)
  have hoI := ho g⁻¹ (Or.inr rfl)
  have wU : U.wt ≤ linRecenterRecordOffsetBudget W := hoF.wt_lt.le
  have wUi : Ui.wt ≤ linRecenterRecordOffsetBudget W := hoI.wt_lt.le
  have hmat (k : G) (hk : k = g ∨ k = g⁻¹)
      (hu : (linVecVal (fun i => ((c' k i).val : ℤ))).wt ≤ linRecenterRecordOffsetBudget W) :
      FunDet P (b + 54) (.list [encIntMatrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom),
        linVecVal (fun i => ((c' k i).val : ℤ))]) (encIntMatrix (linFiniteActionMatrix m ρ c' k))
        (linRecenterRecordMatrixBudget W) := by
    have wm := wmat k hk
    have hh := wt_list2_le (encIntMatrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom))
      (linVecVal (fun i => ((c' k i).val : ℤ)))
    have hb : (Val.list [encIntMatrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom),
        linVecVal (fun i => ((c' k i).val : ℤ))]).wt ≤ linRecenterRecordMatrixArg W := by
      unfold linRecenterRecordMatrixArg
      omega
    exact (linIntAffineMatrix_spec h.matrix (linFiniteIntMatrix m (ρ k).toAddMonoidHom)
      (fun i => ((c' k i).val : ℤ))).mono (linIntAffineMatrixCost_mono hb hd)
  have hmF := hmat g (Or.inl rfl) wU
  have hmI := hmat g⁻¹ (Or.inr rfl) wUi
  have wM : M.wt ≤ linRecenterRecordMatrixBudget W := hmF.wt_lt.le
  have wMi : Mi.wt ≤ linRecenterRecordMatrixBudget W := hmI.wt_lt.le
  have dc (rest : List Val) := Det.arg' (P := P) (vs := [ctx, record]) (rest := rest) (j := 0) rfl
  have dr (rest : List Val) := Det.arg' (P := P) (vs := [ctx, record]) (rest := rest) (j := 1) rfl
  have doF := Det.call (Det.mk4 (Det.get' (dc []) (Det.nat 0) rfl)
    (Det.get' (dr []) (Det.nat 0) rfl) (Det.get' (dr []) (Det.nat 1) rfl)
    (Det.get' (dc []) (Det.nat 1) rfl)) hoF
  have dmF := Det.call (Det.mk2 (Det.get' (dr [U]) (Det.nat 0) rfl)
    (Det.var' (P := P) (env := [a, U]) (i := 1) rfl)) hmF
  have doI := Det.call (Det.mk4 (Det.get' (dc [U, M]) (Det.nat 0) rfl)
    (Det.get' (dr [U, M]) (Det.nat 2) rfl) (Det.get' (dr [U, M]) (Det.nat 3) rfl)
    (Det.get' (dc [U, M]) (Det.nat 1) rfl)) hoI
  have dmI := Det.call (Det.mk2 (Det.get' (dr [U, M, Ui]) (Det.nat 2) rfl)
    (Det.var' (P := P) (env := [a, U, M, Ui]) (i := 3) rfl)) hmI
  have dz : Det P [a, U, M, Ui, Mi] linIntZeroE (encInt 0) 100 :=
    (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  have dorders := Det.snoc (Det.get' (dc [U, M, Ui, Mi]) (Det.nat 0) rfl) dz
  rw [← linRecenterModuli_snoc m] at dorders
  have dout := Det.mk3 dorders
    (Det.var' (P := P) (env := [a, U, M, Ui, Mi]) (i := 2) rfl)
    (Det.var' (P := P) (env := [a, U, M, Ui, Mi]) (i := 4) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE doF (Det.letE dmF (Det.letE doI (Det.letE dmI dout)))).mono ?_
  have worders := linFiniteModuli_wt m
  have wout := wt_list3_le (linVecVal (linFiniteModuli m)) M Mi
  have wargF := wt_list4_le orders (encIntMatrix (linFiniteIntMatrix m (ρ g).toAddMonoidHom))
    (linVecVal (fun i => ((c g i).val : ℤ))) wv
  have wargI := wt_list4_le orders (encIntMatrix (linFiniteIntMatrix m (ρ g⁻¹).toAddMonoidHom))
    (linVecVal (fun i => ((c g⁻¹ i).val : ℤ))) wv
  have wmargF := wt_list2_le (encIntMatrix (linFiniteIntMatrix m (ρ g).toAddMonoidHom)) U
  have wmargI := wt_list2_le (encIntMatrix (linFiniteIntMatrix m (ρ g⁻¹).toAddMonoidHom)) Ui
  have wmF := wmat g (Or.inl rfl)
  have wmI := wmat g⁻¹ (Or.inr rfl)
  have wuF := woff g (Or.inl rfl)
  have wuI := woff g⁻¹ (Or.inr rfl)
  change _ ≤ linRecenterRecordCost W
  unfold linRecenterRecordCost
  dsimp only [W, a, ctx, record, U, Ui, M, Mi, orders, wv, c', linRecenterRecordOffsetBudget,
    linRecenterRecordMatrixBudget, linVecVal] at *
  omega

theorem linRecenterRecordCost_mono {W V : ℕ} (h : W ≤ V) :
    linRecenterRecordCost W ≤ linRecenterRecordCost V := by
  have ho : linRecenterRecordOffsetBudget W ≤ linRecenterRecordOffsetBudget V :=
    linRecenterOffsetCost_mono (by omega)
  have hm : linRecenterRecordMatrixBudget W ≤ linRecenterRecordMatrixBudget V :=
    linIntAffineMatrixCost_mono (show linRecenterRecordMatrixArg W ≤ linRecenterRecordMatrixArg V by
      unfold linRecenterRecordMatrixArg; omega) h
  unfold linRecenterRecordCost
  omega

set_option maxRecDepth 16000 in
theorem linRecenterRecordCost_poly : PBU (fun _ W _ => linRecenterRecordCost W) := by
  have ho := linPoly_subst linRecenterOffsetCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ha : PBU (fun _ W _ => linRecenterRecordMatrixArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W ho) 1)
  have hm := linPoly_subst linIntAffineMatrixCost_poly PBU.W ha (PBU.const 0)
  exact PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add PBU.W ho) hm) 1)

end GI.Impl
