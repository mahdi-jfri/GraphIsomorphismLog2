import Workspace.Impl.VsQPoly

/-!
# Sizes in terms of the input weight

With `X` the weight of the task input, the context `Γ` has weight at most `2000 (X + 1)^7` and the
exponent `E = n! - 2` has weight at most `X² + X + 3`.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The weight of the exponent. -/
theorem vsQ_wt_exp : (Val.nat (vsQExp I)).wt ≤ (vsQTaskIn I).wt ^ 2 + (vsQTaskIn I).wt + 3 := by
  obtain ⟨hnX, -, -⟩ := vsQ_in_sizes I
  have h1 := vsQ_wt_fact I.n
  have h2 : (Val.nat (vsQExp I)).wt ≤ (Val.nat I.n.factorial).wt := by
    rw [wt_nat, wt_nat]
    exact Nat.add_le_add_right (GI.Machine.len_mono (Nat.sub_le _ _)) _
  have h3 : I.n ^ 2 ≤ (vsQTaskIn I).wt ^ 2 := Nat.pow_le_pow_left hnX 2
  omega

/-- The weight of the context `Γ`. -/
theorem vsQ_wt_gam : (vsQGam I).wt ≤ 2000 * ((vsQTaskIn I).wt + 1) ^ 7 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  obtain ⟨hnX, hdX, hgX⟩ := vsQ_in_sizes I
  set X := (vsQTaskIn I).wt with hX
  set E := vsQExp I
  set Z := natList (List.replicate I.d 0)
  have hpX : I.p ≤ X := I.p_le.trans hnX
  have pw : ∀ i j, i ≤ j → (X + 1) ^ i ≤ (X + 1) ^ j := fun i j h => Nat.pow_le_pow_right (by omega) h
  have wp := wt_nat_le I.p
  have hEw : (Val.nat E).wt ≤ X ^ 2 + X + 3 := vsQ_wt_exp
  have wZ : Z.wt ≤ 5 * (X + 1) ^ 2 := wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
  have hX2 : X ^ 2 + X + 3 ≤ 3 * (X + 1) ^ 2 := by nlinarith
  have wE1 : ∀ M : Matrix (Fin I.d) (Fin I.d) (ZMod I.p), (vsQE I.p I.d E M).wt ≤ 100 * (X + 1) ^ 6 := by
    intro M
    have wMt : (Val.list ((vsQL Mᵀ).map natList)).wt ≤ 11 * (X + 1) ^ 3 + 4 :=
      wt_vsFSq_le (by omega) hdX (vsQL_sq Mᵀ)
    have l4 := wt_list4_le (.nat I.p) Z (.nat E) (.list ((vsQL Mᵀ).map natList))
    have eE : (vsQE I.p I.d E M).wt = (Val.list [.nat I.p, Z, .nat E,
      .list ((vsQL Mᵀ).map natList)]).wt := rfl
    have := pw 3 6 (by omega); have := pw 2 6 (by omega); have := pw 0 6 (by omega)
    simp at this
    omega
  set ML := I.gs.attach.map fun g => ((I.φ ⟨g.1, Subgroup.subset_closure g.2⟩ : GL (Fin I.d) (ZMod I.p)) :
    Matrix (Fin I.d) (Fin I.d) (ZMod I.p))
  have hML : ML.length = I.gs.length := by simp [ML]
  have eTB : vsQTable I = Val.list (ML.map (vsQE I.p I.d E)) := by
    simp only [ML, vsQTable, List.map_map]; rfl
  have wTB : (vsQTable I).wt ≤ 300 * (X + 1) ^ 7 := by
    have h1 := vs_wt_list_le_of (ML.map (vsQE I.p I.d E)) (c := 100 * (X + 1) ^ 6) (by
      intro v hv
      obtain ⟨M, -, rfl⟩ := List.mem_map.1 hv
      exact wE1 M)
    rw [List.length_map, hML] at h1
    have h2 : I.gs.length * (2 * (100 * (X + 1) ^ 6) + 1) ≤ (X + 1) * (201 * (X + 1) ^ 6) :=
      Nat.mul_le_mul (by omega) (by have := pw 0 6 (by omega); simp at this; omega)
    have e : (X + 1) * (201 * (X + 1) ^ 6) = 201 * (X + 1) ^ 7 := by ring
    have := pw 0 7 (by omega); simp at this
    rw [eTB]
    omega
  have l3 := wt_list3_le (encGroup I.gs) (vsQTable I) (vsQE I.p I.d E 1)
  have e : (vsQGam I).wt = (Val.list [encGroup I.gs, vsQTable I, vsQE I.p I.d E 1]).wt := rfl
  have hEG : (encGroup I.gs).wt < X := wt_le_wt_list (by simp)
  have := wE1 1; have := pw 6 7 (by omega); have : X + 1 ≤ (X + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
  omega

/-- A bound on the weight of the membership input `[encGroup gs, encPerm x]`. -/
def vsQMI (N : ℕ) : ℕ := 2 * (N + 4 * (N + 1) ^ 2) + 6

/-- A bound on the weight of the output of constructive membership. -/
def vsQLW (deg N : ℕ) : ℕ := 400 * (vsQMI N ^ deg + 1) * (N + vsQMI N ^ deg + 2) + 100

/-- A uniform bound on the cost of `φ`. -/
noncomputable def vsQCphi (hcm : ConstructiveMembership) (N : ℕ) : ℕ :=
  vsQPhiCost ((linMembershipPrim hcm).c * (vsQMI N + 2) ^ (linMembershipPrim hcm).k + vsQMI N +
      vsQLW (linMembershipDegree hcm) N + 2)
    (4 * (2 * (N + 4 * (N + 1) ^ 2) + 6) + 2 * vsQLW (linMembershipDegree hcm) N + 10)
    (vsQMI N ^ linMembershipDegree hcm) N

/-- **`φ` with a uniform cost.** -/
theorem vsQPhi_unif (hcm : ConstructiveMembership) {P : Program} {b j gl N : ℕ}
    (hb : P.HasAt b (vsQPhiFuns b j gl (gl + 2)))
    (hj : P.prims[j]? = some (linMembershipPrim hcm)) (hgl : P.HasAt gl (vsQGLFuns gl))
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hΓ : (vsQGam I).wt ≤ N) (hn : I.n ≤ N)
    (hG : (encGroup I.gs).wt ≤ N) (hl : I.gs.length ≤ N) :
    ∀ x ∈ gens I.gs, FunDet P b (.list [vsQGam I, encPerm x]) (vsQE I.p I.d (vsQExp I) (vsQPhi I x))
      (vsQCphi hcm N) := by
  intro x hx
  refine (vsQPhi_spec hcm hb hj hgl hsz hx).mono ?_
  unfold vsQCphi vsQPhiCost
  have wx : (encPerm x).wt ≤ 4 * (N + 1) ^ 2 :=
    (wt_encPerm_le x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wmi : (memberInput ⟨I.n, I.gs, x⟩).wt ≤ vsQMI N := by
    have := wt_list2_le (encGroup I.gs) (encPerm x)
    have e : (memberInput ⟨I.n, I.gs, x⟩).wt = (Val.list [encGroup I.gs, encPerm x]).wt := rfl
    unfold vsQMI; omega
  have hc : (memberInput ⟨I.n, I.gs, x⟩).cells.length ≤ vsQMI N :=
    ((memberInput ⟨I.n, I.gs, x⟩).size_le_wt).trans wmi
  have hL : (memberInput ⟨I.n, I.gs, x⟩).cells.length ^ (linMembershipDegree hcm) ≤ vsQMI N ^ (linMembershipDegree hcm) := Nat.pow_le_pow_left hc _
  have hLW : linMembershipWt (linMembershipDegree hcm) ⟨I.n, I.gs, x⟩ ≤ vsQLW (linMembershipDegree hcm) N := by
    unfold linMembershipWt vsQLW
    have : I.gs.length ≤ N := hl
    simp only at hL ⊢
    gcongr
  have hW : 4 * (Val.list [vsQGam I, encPerm x]).wt + 2 * linMembershipWt (linMembershipDegree hcm) ⟨I.n, I.gs, x⟩ + 10 ≤
      4 * (2 * (N + 4 * (N + 1) ^ 2) + 6) + 2 * vsQLW (linMembershipDegree hcm) N + 10 := by
    have := wt_list2_le (vsQGam I) (encPerm x)
    omega
  have hcm' : linMembershipCost hcm ⟨I.n, I.gs, x⟩ ≤ (linMembershipPrim hcm).c * (vsQMI N + 2) ^
      (linMembershipPrim hcm).k + vsQMI N + vsQLW (linMembershipDegree hcm) N + 2 := by
    unfold linMembershipCost Prim.bound
    have : (memberInput ⟨I.n, I.gs, x⟩).size ≤ vsQMI N := hc
    have h1 : (linMembershipPrim hcm).c * ((memberInput ⟨I.n, I.gs, x⟩).size + 2) ^ (linMembershipPrim hcm).k ≤
        (linMembershipPrim hcm).c * (vsQMI N + 2) ^ (linMembershipPrim hcm).k := by gcongr
    omega
  have := linGroupSlpCost_mono2 (B := vsQW N) (C := 10 ^ 8 * (N + 1) ^ 6) hW hL
  omega

end GI.Impl
