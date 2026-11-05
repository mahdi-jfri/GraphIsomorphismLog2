module

public import Workspace.Impl.LinAffineCallerSpec

@[expose] public section

/-! The shared finite abelian affine procedure is implemented from the cited
permutation membership, constructive membership and vector stabilizer tasks. -/
namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 16000 in
theorem linAffineTransportAll_iface (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    ∃ K D : ℕ, ∀ {P : Program} {b jmem jm jv : ℕ},
      linAffineTransportAllAt P b jmem jm jv hmem hm hv → Iface.TmGLAffineSpec P K D b := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linAffineCallerCost_poly hmem hm hv)
  refine ⟨K, D, ?_⟩
  intro P b jmem jm jv hat n d gs m ρ c v w hs hmpos hprime hc
  refine FunAll.mono (linAffineTransportAll_spec hmem hm hv hat gs m ρ c v w hs hmpos hprime hc) ?_
  intro out cost ho
  refine ⟨?_, ho.2.trans (hKD 0 _ _ (Nat.zero_le _) le_rfl)⟩
  rcases ho.1 with hno | ⟨t, ks, he, _, hT⟩
  · exact Or.inl hno
  · exact Or.inr ⟨t, ks, he, hT⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 16000 in
theorem linAffineTransportAll_iface_of (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    ∃ K D : ℕ, ∀ {P : Program} {b jmem jm jv : ℕ},
      P.HasAt b (linAffineTransportAllFuns b jmem jm jv) →
      P.prims[jmem]? = some (membershipPrim hmem) →
      P.prims[jm]? = some (linMembershipPrim hm) →
      P.prims[jv]? = some (vectorStabilizerPrim hv) → Iface.TmGLAffineSpec P K D b := by
  obtain ⟨K, D, hKD⟩ := linAffineTransportAll_iface hmem hm hv
  exact ⟨K, D, fun h hjmem hjm hjv => hKD (linAffineTransportAllAt_of hmem hm hv h hjmem hjm hjv)⟩

end GI.Impl
