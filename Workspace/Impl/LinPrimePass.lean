import Workspace.Impl.LinPrimePrepareSpec
import Workspace.Impl.LinPrimaryLoopSpec
import Workspace.Impl.LinAffineRestrict
import Workspace.Lang.Prims.BlockHom

/-! One primary pass retains the full mixed-order context. After solving the
primary projection, it lifts the cover representative and subgroup through
constructive membership and evaluates them in that retained full action. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimePassF (prepare loop tail item point restrict compose : ℕ) : Expr :=
  .letE (.call prepare (.snoc (mk4 (arg 0) (arg 1)
    (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 0)) (arg 3)) (arg 4)))
    (.letE (.call loop (.var 1))
      (.ite (.length (.var 2))
        (.letE (.call tail (.get (.get (.get (.var 2) (.nat 0)) (.nat 0)) (.nat 1)))
          (.letE (.call item (mk2 (arg 0) (.get (.var 2) (.nat 2))))
            (.letE (.call point (mk2 (.var 4) (arg 1)))
              (.letE (.call restrict (mk2 (arg 0) (.var 3)))
                (.letE (.call compose (mk2 (.get (.var 2) (.nat 2)) (arg 2)))
                  (mk3 (.var 6) (.var 5) (.var 7))))))) .nil))

def linPrimePassFuns (b jm jv : ℕ) : List Expr :=
  [linPrimePassF (b + 1) (b + 88) (b + 525) (b + 528) (b + 595) (b + 642) (b + 720)] ++
    linPrimePrepareFuns (b + 1) ++ linPrimaryLoopFuns (b + 88) jm jv ++
    tailFuns (b + 525) ++ linActionItemFuns (b + 528) jm ++
    linFinitePointApplyFuns (b + 595) ++ linAffineRestrictFuns (b + 642) jm ++
    composeFuns (b + 720)

theorem linPrimePassFuns_length (b jm jv : ℕ) : (linPrimePassFuns b jm jv).length = 724 := by
  simp only [linPrimePassFuns, List.length_append, linPrimePrepareFuns_length,
    linPrimaryLoopFuns_length, linActionItemFuns_length, linFinitePointApplyFuns_length,
    linAffineRestrictFuns_length]
  rfl

structure linPrimePassAt (P : Program) (b jm jv : ℕ)
    (hm : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linPrimePassF (b + 1) (b + 88) (b + 525) (b + 528) (b + 595) (b + 642) (b + 720))
  prepare : linPrimePrepareAt P (b + 1)
  loop : linPrimaryLoopAt P (b + 88) jm jv hm hv
  tail : P.HasAt (b + 525) (tailFuns (b + 525))
  item : linActionItemAt P (b + 528) jm hm
  point : linFinitePointApplyAt P (b + 595)
  restrict : linAffineRestrictAt P (b + 642) jm hm
  compose : P.HasAt (b + 720) (composeFuns (b + 720))

set_option maxHeartbeats 300000 in
set_option maxRecDepth 32000 in
theorem linPrimePassAt_of (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv : ℕ} (h : P.HasAt b (linPrimePassFuns b jm jv))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) : linPrimePassAt P b jm jv hm hv := by
  have h0 : P.HasAt b ([linPrimePassF (b + 1) (b + 88) (b + 525) (b + 528) (b + 595) (b + 642) (b + 720)] ++
      (linPrimePrepareFuns (b + 1) ++ (linPrimaryLoopFuns (b + 88) jm jv ++
      (tailFuns (b + 525) ++ (linActionItemFuns (b + 528) jm ++
      (linFinitePointApplyFuns (b + 595) ++ (linAffineRestrictFuns (b + 642) jm ++
      composeFuns (b + 720)))))))) := by
    simpa only [linPrimePassFuns, List.append_assoc] using h
  have h1 := h0.right
  simp only [List.length_singleton, Nat.add_assoc] at h1
  have h2 := h1.right
  simp only [linPrimePrepareFuns_length, Nat.add_assoc, Nat.reduceAdd] at h2
  have h3 := h2.right
  simp only [linPrimaryLoopFuns_length, Nat.add_assoc, Nat.reduceAdd] at h3
  have h4 := h3.right
  have htail : (tailFuns (b + 525)).length = 3 := rfl
  simp only [htail, Nat.add_assoc, Nat.reduceAdd] at h4
  have h5 := h4.right
  simp only [linActionItemFuns_length, Nat.add_assoc, Nat.reduceAdd] at h5
  have h6 := h5.right
  simp only [linFinitePointApplyFuns_length, Nat.add_assoc, Nat.reduceAdd] at h6
  have h7 := h6.right
  simp only [linAffineRestrictFuns_length, Nat.add_assoc, Nat.reduceAdd] at h7
  exact ⟨h0.left.single, linPrimePrepareAt_of h1.left,
    linPrimaryLoopAt_of hm hv h2.left hjm hjv, h3.left,
    linActionItemAt_of h4.left hjm, linFinitePointApplyAt_of h5.left,
    linAffineRestrictAt_of hm h6.left hjm, h7⟩

end GI.Impl
