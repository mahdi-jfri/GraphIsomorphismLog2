module

public import Workspace.Impl.LinPrimePassSpec
public import Workspace.Impl.LinPrimeTestSpec
public import Workspace.Impl.LinMixedInvariant

@[expose] public section

/-! Process the prime characteristics up to the explicit cover degree. Every
successful pass returns a full mixed-order context for the next pass. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linMixedLoopStepF (prime pass : ℕ) : Expr :=
  .ite (.length (arg 2))
    (.ite (.call prime (.arith .add (arg 1) (.nat 1)))
      (.call pass (.snoc (mk4 (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1))
        (.get (arg 2) (.nat 2)) (.arith .add (arg 1) (.nat 1))) (.get (arg 0) (.nat 3))))
      (arg 2)) .nil

def linMixedLoopFuns (b jm jv : ℕ) : List Expr :=
  loopFuns b (.get (.get (arg 0) (.nat 0)) (.nat 0)) (mk3 (arg 0) (arg 1) (arg 2))
    (linMixedLoopStepF (b + 3) (b + 11)) ++
    linPrimeTestFuns (b + 3) ++ linPrimePassFuns (b + 11) jm jv

theorem linMixedLoopFuns_length (b jm jv : ℕ) : (linMixedLoopFuns b jm jv).length = 735 := by
  simp only [linMixedLoopFuns, List.length_append, linPrimeTestFuns_length, linPrimePassFuns_length]
  rfl

structure linMixedLoopAt (P : Program) (b jm jv : ℕ)
    (hm : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  loop : P.HasAt b (loopFuns b (.get (.get (arg 0) (.nat 0)) (.nat 0))
    (mk3 (arg 0) (arg 1) (arg 2)) (linMixedLoopStepF (b + 3) (b + 11)))
  prime : linPrimeTestAt P (b + 3)
  pass : linPrimePassAt P (b + 11) jm jv hm hv

set_option maxHeartbeats 300000 in
theorem linMixedLoopAt_of (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv : ℕ} (h : P.HasAt b (linMixedLoopFuns b jm jv))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) : linMixedLoopAt P b jm jv hm hv := by
  have h0 : P.HasAt b (loopFuns b (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (mk3 (arg 0) (arg 1) (arg 2)) (linMixedLoopStepF (b + 3) (b + 11)) ++
      (linPrimeTestFuns (b + 3) ++ linPrimePassFuns (b + 11) jm jv)) := by
    simpa only [linMixedLoopFuns, List.append_assoc] using h
  have h1 := h0.right
  have hlen : (loopFuns b (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (mk3 (arg 0) (arg 1) (arg 2)) (linMixedLoopStepF (b + 3) (b + 11))).length = 3 := rfl
  simp only [hlen] at h1
  have h2 := h1.right
  simp only [linPrimeTestFuns_length, Nat.add_assoc, Nat.reduceAdd] at h2
  exact ⟨h0.left, linPrimeTestAt_of h1.left, linPrimePassAt_of hm hv h2 hjm hjv⟩

noncomputable def linMixedLoopInputVal {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) : Val :=
  .list [linActionContext gs m ρ c, linFinitePointVal m x, encPerm r,
    linVecVal (fun i => (m i : ℤ))]

end GI.Impl
