module

public import Workspace.Impl.HNFSize

@[expose] public section

/-!
# The three tables of the Hermite program

`hnfTab` with the cells of `Impl/HNFCells.lean`: the big matrix mod `m`, the transform `U` and
the Hermite form `H`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved
open GI.Machine (BinOp len len_le_iff)

variable {r c : ℕ}

theorem hnf_wt_nat_lt {i n : ℕ} (h : i < n) : (Val.nat i).wt ≤ (Val.nat n).wt := by
  rw [wt_nat, wt_nat]; have := GI.Machine.len_mono h.le; omega

theorem hnfCellArg_wt_le {C : List Val} {a n i j X : ℕ} (hi : i < a) (hj : j < n)
    (hX : (Val.list [.list C, .nat a, .nat n]).wt ≤ X) : (hnfCellArg C a n i j).wt ≤ 10 * X + 18 := by
  have w1 : (Val.nat a).wt < (Val.list [.list C, .nat a, .nat n]).wt := wt_le_wt_list (by simp)
  have w2 : (Val.nat n).wt < (Val.list [.list C, .nat a, .nat n]).wt := wt_le_wt_list (by simp)
  have w3 := hnf_wt_nat_lt hi
  have w4 := hnf_wt_nat_lt hj
  have w5 := wt_list2_le (.list [.list C, .nat a, .nat n]) (.nat i)
  have w6 := wt_list2_le (.list [.list [.list C, .nat a, .nat n], .nat i]) (.nat j)
  unfold hnfCellArg
  omega

theorem hnfBigCellCost_mono {Y Z : ℕ} (h : Y ≤ Z) : hnfBigCellCost Y ≤ hnfBigCellCost Z := by
  unfold hnfBigCellCost
  have := linIntBinaryCost_mono (show 4 * Y + 100 ≤ 4 * Z + 100 by omega)
  omega

theorem hnfHCellCost_mono {Y Z : ℕ} (h : Y ≤ Z) : hnfHCellCost Y ≤ hnfHCellCost Z := by
  unfold hnfHCellCost; omega

/-- **The big matrix mod `m`.** -/
theorem hnfBigTab_spec {P : Program} {tb cell ints : ℕ} (hI : linIntSpec P ints)
    (ht : hnfTabAt P tb cell) (hf : P.funs[cell]? = some (hnfBigCellF ints))
    (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (hs : s.Nodup) (hsc : s.length = c)
    (hcr : c ≤ r) (K m : ℤ) {X : ℕ}
    (hX : (Val.list [.list (hnfBigCtx A s K m), .nat (r + r), .nat (r + r)]).wt ≤ X)
    (hrX : r + r ≤ X) :
    FunDet P tb (.list [.list (hnfBigCtx A s K m), .nat (r + r), .nat (r + r)])
      (encIntMatrix (fun i j => hnfBig (hnfAp A s) K i j % m))
      (hnfTabCost X (hnfBigCellCost (10 * X + 18))) :=
  hnfTab_spec ht _ (r + r) (r + r) (fun i j => encInt (hnfBig (hnfAp A s) K i j % m)) _ X hX hrX hrX
    fun i j => (hnfBigCell_spec hI hf A s hs hsc hcr K m (r + r) i j).mono
      (hnfBigCellCost_mono (hnfCellArg_wt_le i.isLt j.isLt hX))

/-- **The transform.** -/
theorem hnfUTab_spec {P : Program} {tb cell ints : ℕ} (hI : linIntSpec P ints)
    (ht : hnfTabAt P tb cell) (hf : P.funs[cell]? = some (hnfUCellF ints))
    (Hb : Matrix (Fin (r + r)) (Fin (r + r)) ℤ) (K : ℤ) {L X : ℕ}
    (hL : ∀ a b, (Hb a b).natAbs < 2 ^ L) (hK : K.natAbs < 2 ^ L)
    (hX : (Val.list [.list (hnfOutCtx Hb K), .nat r, .nat r]).wt ≤ X) (hrX : r ≤ X) :
    FunDet P tb (.list [.list (hnfOutCtx Hb K), .nat r, .nat r])
      (encIntMatrix (fun i j => hnfLift K (Hb (Fin.castAdd r i) (Fin.natAdd r j))))
      (hnfTabCost X (hnfUCellCost (10 * X + 18 + 100 * (L + 1)))) :=
  hnfTab_spec ht _ r r (fun i j => encInt (hnfLift K (Hb (Fin.castAdd r i) (Fin.natAdd r j)))) _ X
    hX hrX hrX fun i j => hnfUCell_spec hI hf Hb K r i j hL hK
      (by have := hnfCellArg_wt_le i.isLt j.isLt hX; omega)

/-- **The Hermite form.** -/
theorem hnfHTab_spec {P : Program} {tb cell : ℕ} (ht : hnfTabAt P tb cell)
    (hf : P.funs[cell]? = some hnfHCellF) (hcr : c ≤ r)
    (Hb : Matrix (Fin (r + r)) (Fin (r + r)) ℤ) (K : ℤ) {X : ℕ}
    (hX : (Val.list [.list (hnfOutCtx Hb K), .nat r, .nat c]).wt ≤ X) (hrX : r ≤ X) :
    FunDet P tb (.list [.list (hnfOutCtx Hb K), .nat r, .nat c])
      (encIntMatrix (fun i j => Hb (Fin.castAdd r i) (Fin.castAdd r (Fin.castLE hcr j))))
      (hnfTabCost X (hnfHCellCost (10 * X + 18))) :=
  hnfTab_spec ht _ r c (fun i j => encInt (Hb (Fin.castAdd r i) (Fin.castAdd r (Fin.castLE hcr j))))
    _ X hX hrX (hcr.trans hrX) fun i j => (hnfHCell_spec hf hcr Hb K r i j).mono
      (hnfHCellCost_mono (hnfCellArg_wt_le i.isLt j.isLt hX))

end GI.Impl
