module

public import Workspace.Impl.AggItemCiSojPull
public import Workspace.Impl.AggItemCiSojSG

@[expose] public section

/-!
# Tabulating the pulled rectangle colors

The map traverses the stored cell table on the original positions. Zero remains
zero. Every cell reads the matrix entry at its actual labels after applying the
specified alignment and twist.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q k : ℕ} {W R : Finset (Fin q)}

/-- The map context consists of the original table, edge color, label size and permutation. -/
def itcsPullCtx (X : PairCfg q) (v : ℕ) (p : Perm (Fin q)) : Val :=
  .list [rcColVal X, .nat v, .nat q, encPerm p]

/-- Adapt one cell-table entry to the literal bit reader. -/
def itcsPullB (pull : ℕ) : Expr :=
  .call pull (itcsMk5 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (.get (arg 0) (.nat 2)) (arg 1) (.get (arg 0) (.nat 3)))

/-- The cell map callback preserves the literal pullback. -/
theorem itcs_pullB_spec {Pg : Program} {f pull Bw : ℕ}
    (hf : Pg.funs[f]? = some (itcsPullB pull)) (hp : Pg.funs[pull]? = some itcsPullF)
    (X : PairCfg q) (v : ℕ) (p : Perm (Fin q)) (cell : Option (W × R))
    (hin : (Val.list [itcsPullCtx X v p, .nat (rcCellCode cell)]).wt ≤ Bw)
    (hflat : (Val.list [rcColVal X, .nat v, .nat q, .nat (rcCellCode cell), encPerm p]).wt ≤ Bw)
    (hq : q * q + q + 10 ≤ Bw) :
    FunDet Pg f (.list [itcsPullCtx X v p, .nat (rcCellCode cell)])
      (.nat (itcsQCode (cell.map fun c => decide (X.col (p c.1.val) (p c.2.val) = v))))
      (200 * (Bw + 1)) := by
  let env : List Val := [.list [itcsPullCtx X v p, .nat (rcCellCode cell)]]
  have hc : (itcsPullCtx X v p).wt ≤ Bw := (st_wt_mem (by simp)).trans hin
  have g0 : StDC Pg env (arg 0) (itcsPullCtx X v p) 3 0 Bw := StDC.arg rfl hin (by omega) hc
  have g1 : StDC Pg env (arg 1) (.nat (rcCellCode cell)) 3 0 Bw :=
    StDC.arg rfl hin (by omega) ((st_wt_mem (by simp)).trans hin)
  have get {i : ℕ} {w : Val} (hi : [rcColVal X, .nat v, .nat q, encPerm p][i]? = some w)
      (hii : i + 2 ≤ Bw) : StDC Pg env (.get (arg 0) (.nat i)) w 5 0 Bw :=
    StDC.get g0 (StDC.nat i hii) hi ((st_wt_mem (List.mem_of_getElem? hi)).trans hc)
  have args := itcs_mk5 (get (i := 0) rfl (by omega)) (get (i := 1) rfl (by omega))
    (get (i := 2) rfl (by omega)) g1 (get (i := 3) rfl (by omega)) hflat (by omega)
  have out := StDC.call args (itcs_pull_spec hp X v p cell hflat hq)
    ((wt_nat_le _).trans (by
      have hh := itcs_qcode_le (cell.map fun c => decide (X.col (p c.1.val) (p c.2.val) = v))
      omega))
  exact StDC.funDet hf out (by omega)

/-- Exact bulk pullback on the stored physical cell table. -/
theorem itcs_pull_table {Pg : Program} {mp f pull Bw : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some (itcsPullB pull))
    (hp : Pg.funs[pull]? = some itcsPullF)
    (X : PairCfg q) (v : ℕ) (p : Perm (Fin q)) (cells : Fin k → Option (W × R))
    (hin : ∀ i, (Val.list [itcsPullCtx X v p, .nat (rcCellCode (cells i))]).wt ≤ Bw)
    (hflat : ∀ i, (Val.list [rcColVal X, .nat v, .nat q,
      .nat (rcCellCode (cells i)), encPerm p]).wt ≤ Bw)
    (hq : q * q + q + 10 ≤ Bw) :
    FunDet Pg mp (.list [itcsPullCtx X v p, encFun (fun i => rcCellCode (cells i))])
      (encFun fun i => itcsQCode ((cells i).map fun c => decide (X.col (p c.1.val) (p c.2.val) = v)))
      (k * (200 * (Bw + 1)) + mapK * (k + 1) *
        ((Val.list [itcsPullCtx X v p, encFun (fun i => rcCellCode (cells i))]).wt +
          (k * 9 + 4) + 1)) := by
  classical
  let F : Val → Val := fun a => match a with
    | .nat n => if hn : ∃ i, rcCellCode (cells i) = n then
        .nat (itcsQCode ((cells hn.choose).map fun c => decide (X.col (p c.1.val) (p c.2.val) = v)))
      else .nat 0
    | _ => .nat 0
  have he (i : Fin k) : F (.nat (rcCellCode (cells i))) =
      .nat (itcsQCode ((cells i).map fun c => decide (X.col (p c.1.val) (p c.2.val) = v))) := by
    have hx : ∃ j, rcCellCode (cells j) = rcCellCode (cells i) := ⟨i, rfl⟩
    dsimp only [F]
    rw [dif_pos hx, rcCellCode_injective hx.choose_spec]
  have hm' := map_det hm (c := itcsPullCtx X v p)
    (xs := (List.finRange k).map fun i => Val.nat (rcCellCode (cells i)))
    (F := F) (B := 200 * (Bw + 1)) (fun a ha => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      rw [he]
      exact itcs_pullB_spec hf hp X v p (cells i) (hin i) (hflat i) hq)
  have hemap : ((List.finRange k).map (fun i => Val.nat (rcCellCode (cells i)))).map F =
      (List.finRange k).map (fun i => .nat (itcsQCode ((cells i).map fun c =>
        decide (X.col (p c.1.val) (p c.2.val) = v)))) := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ => he i
  rw [hemap] at hm'
  refine hm'.mono ?_
  simp only [List.length_map, List.length_finRange]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have hw := wt_encFun_le (fun i => itcsQCode ((cells i).map fun c =>
    decide (X.col (p c.1.val) (p c.2.val) = v))) (fun _ => itcs_qcode_le _)
  dsimp only [encFun] at hw ⊢
  omega

end GI.Impl
