import Workspace.Impl.LinAffineCaller

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

structure linAffineTransportAllAt (P : Program) (b jmem jm jv : ℕ)
    (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  top : P.funs[b]? = some (linAffineCallerTopF (b + 1) (b + 2))
  main : P.funs[b + 1]? = some
    (linAffineCallerMainF (b + 1010) (b + 244) (b + 979))
  small : P.funs[b + 2]? = some (linAffineCallerSmallF (b + 128) (b + 153))
  context : linRecenterContextAt P (b + 3)
  difference : linFiniteDifferenceAt P (b + 128)
  zero : linZeroIntVectorAt P (b + 153)
  reduce : P.HasAt (b + 158) (reduceFuns (b + 158) jmem)
  member : P.prims[jmem]? = some (membershipPrim hmem)
  tail : P.HasAt (b + 163) (tailFuns (b + 163))
  restrict : linAffineRestrictAt P (b + 166) jm hm
  mixed : linMixedLoopAt P (b + 244) jm jv hm hv
  left : linAffineLeftAt P (b + 979)
  prepare : P.funs[b + 1010]? = some (linAffineCallerPrepF (b + 3) (b + 128) (b + 158) (b + 163) (b + 166))

set_option maxHeartbeats 500000 in
theorem linAffineTransportAllAt_of (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jmem jm jv : ℕ} (h : P.HasAt b (linAffineTransportAllFuns b jmem jm jv))
    (hjmem : P.prims[jmem]? = some (membershipPrim hmem))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) : linAffineTransportAllAt P b jmem jm jv hmem hm hv := by
  have h0 : P.HasAt b ([linAffineCallerTopF (b + 1) (b + 2),
      linAffineCallerMainF (b + 1010) (b + 244) (b + 979),
      linAffineCallerSmallF (b + 128) (b + 153)] ++
      (linRecenterContextFuns (b + 3) ++ (linFiniteDifferenceFuns (b + 128) ++
      (linZeroIntVectorFuns (b + 153) ++ (reduceFuns (b + 158) jmem ++
      (tailFuns (b + 163) ++ (linAffineRestrictFuns (b + 166) jm ++
      (linMixedLoopFuns (b + 244) jm jv ++ (linAffineLeftFuns (b + 979) ++
      [linAffineCallerPrepF (b + 3) (b + 128) (b + 158) (b + 163) (b + 166)]))))))))) := by
    simpa only [linAffineTransportAllFuns, List.append_assoc] using h
  have h1 := h0.right
  simp only [List.length_cons, List.length_nil] at h1
  have h2 := h1.right
  simp only [linRecenterContextFuns_length, Nat.add_assoc, Nat.reduceAdd] at h2
  have h3 := h2.right
  simp only [linFiniteDifferenceFuns_length, Nat.add_assoc, Nat.reduceAdd] at h3
  have h4 := h3.right
  simp only [linZeroIntVectorFuns_length, Nat.add_assoc, Nat.reduceAdd] at h4
  have h5 := h4.right
  have hr : (reduceFuns (b + 158) jmem).length = 5 := rfl
  simp only [hr, Nat.add_assoc, Nat.reduceAdd] at h5
  have h6 := h5.right
  have ht : (tailFuns (b + 163)).length = 3 := rfl
  simp only [ht, Nat.add_assoc, Nat.reduceAdd] at h6
  have h7 := h6.right
  simp only [linAffineRestrictFuns_length, Nat.add_assoc, Nat.reduceAdd] at h7
  have h8 := h7.right
  simp only [linMixedLoopFuns_length, Nat.add_assoc, Nat.reduceAdd] at h8
  have h9 := h8.right
  simp only [linAffineLeftFuns_length, Nat.add_assoc, Nat.reduceAdd] at h9
  exact ⟨h0.left 0 (by simp), h0.left 1 (by simp), h0.left 2 (by simp),
    linRecenterContextAt_of h1.left, linFiniteDifferenceAt_of h2.left, linZeroIntVectorAt_of h3.left,
    h4.left, hjmem, h5.left, linAffineRestrictAt_of hm h6.left hjm,
    linMixedLoopAt_of hm hv h7.left hjm hjv, linAffineLeftAt_of h8.left, h9.single⟩

end GI.Impl
