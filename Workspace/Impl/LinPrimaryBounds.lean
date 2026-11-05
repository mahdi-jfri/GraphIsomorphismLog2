module

public import Workspace.Impl.LinPrimaryLoop

@[expose] public section

/-! Uniform sizes throughout the filtration. Every newly chosen cover element
has canonical finite affine records, so repeated restrictions do not compound
intermediate polynomial bounds. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryRecordWeight (W : ℕ) : ℕ := linFiniteActionWeight W W

def linPrimaryContextWeight (W : ℕ) : ℕ :=
  100 * (groupW W + linVectorAccWt (W ^ 2) (linPrimaryRecordWeight W) + linPrimaryRecordWeight W + 1)
def linPrimaryPointWeight (W : ℕ) : ℕ := 1000 * (W + 101) ^ 2

def linPrimaryAccumulatorWeight (W : ℕ) : ℕ :=
  100 * (linPrimaryContextWeight W + linPrimaryPointWeight W + 4 * (W + 1) ^ 2 + 1)
def linPrimaryIterationWeight (W : ℕ) : ℕ :=
  100 * (linPrimaryAccumulatorWeight W + W * (2 * W + 5) + W + 10)

theorem linFiniteActionWeight_mono {W V d e : ℕ} (hw : W ≤ V) (hd : d ≤ e) :
    linFiniteActionWeight W d ≤ linFiniteActionWeight V e := by
  unfold linFiniteActionWeight linFiniteActionMatrixWeight linFiniteScalarBudget linVectorAccWt
  gcongr

theorem linPrimaryContext_wt {n d W : ℕ} (gs : List (Equiv.Perm (Fin n))) (hlen : gs.length ≤ n ^ 2)
    (hn : n ≤ W) (hd : d ≤ W) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (hwm : (linVecVal (fun i => (m i : ℤ))).wt ≤ W)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) :
    (linActionContext gs m ρ c).wt ≤ linPrimaryContextWeight W := by
  let R := linPrimaryRecordWeight W
  let dict := linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs)
  have hf (g : gens gs) : (linFiniteAffineVal m ρ c g).wt ≤ R :=
    (linFiniteAffineVal_wt m hm ρ c g).trans (linFiniteActionWeight_mono hwm hd)
  have hl : (linActionGens gs).length ≤ W ^ 2 := by
    simp only [linActionGens, List.length_map]
    exact hlen.trans (Nat.pow_le_pow_left hn 2)
  have hdct : dict.wt ≤ linVectorAccWt (W ^ 2) R := by
    have hh := linWtList (vs := (linActionGens gs).map (linFiniteAffineVal m ρ c)) (B := R) (by
      intro v hv
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv
      exact hf g)
    simp only [List.length_map] at hh
    change dict.wt ≤ 2 * ((linActionGens gs).length * R) + (linActionGens gs).length + 4 at hh
    exact hh.trans (linVectorAccWt_mono hl le_rfl)
  have hg0 := GroupValC.wt_le (show GroupValC n (encGroup gs) (gens gs) from ⟨gs, rfl, rfl, hlen⟩)
  have hg : (encGroup gs).wt ≤ groupW W := hg0.trans (by unfold groupW; gcongr)
  have hi := hf 1
  have hh := wt_list3_le (encGroup gs) dict (linFiniteAffineVal m ρ c 1)
  change (Val.list [encGroup gs, dict, linFiniteAffineVal m ρ c 1]).wt ≤ linPrimaryContextWeight W
  unfold linPrimaryContextWeight
  dsimp only [R] at *
  omega

theorem linPrimaryPoint_wt {d W : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (hwm : (linVecVal (fun i => (m i : ℤ))).wt ≤ W) (x : linFiniteVec m) :
    (linFinitePointVal m x).wt ≤ linPrimaryPointWeight W := by
  have hmod := linFiniteModuli_wt m
  exact (linFinitePointVal_wt m hm x).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega : (linVecVal (linFiniteModuli m)).wt + 1 ≤ W + 101) 2))

theorem linPrimaryAccumulator_wt {n d W : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hlen : gs.length ≤ n ^ 2) (hn : n ≤ W) (hd : d ≤ W) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (hwm : (linVecVal (fun i => (m i : ℤ))).wt ≤ W)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) :
    (Val.list [linActionContext gs m ρ c, linFinitePointVal m x, encPerm r]).wt ≤ linPrimaryAccumulatorWeight W := by
  have hc := linPrimaryContext_wt gs hlen hn hd m hm hwm ρ c
  have hp := linPrimaryPoint_wt m hm hwm x
  have hr := (wt_encPerm_le r).trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2))
  have hh := wt_list3_le (linActionContext gs m ρ c) (linFinitePointVal m x) (encPerm r)
  unfold linPrimaryAccumulatorWeight
  omega

theorem linPrimaryIteration_wt {n p d W : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hlen : gs.length ≤ n ^ 2) (hn : n ≤ W) (hd : d ≤ W) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (hwm : (linVecVal (fun i => (m i : ℤ))).wt ≤ W)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) (ν : Fin d → ℕ) (hν : ∀ i, ν i ≤ W)
    (hp : p ≤ W) (level : ℕ) (hl : level ≤ W) :
    (linPrimaryIterationVal gs m ρ c x r p ν level).wt ≤ linPrimaryIterationWeight W := by
  have ha := linPrimaryAccumulator_wt gs hlen hn hd m hm hwm ρ c x r
  have hc : (linActionContext gs m ρ c).wt ≤ linPrimaryAccumulatorWeight W :=
    (wt_le_wt_list (by simp)).le.trans ha
  have hx : (linFinitePointVal m x).wt ≤ linPrimaryAccumulatorWeight W :=
    (wt_le_wt_list (by simp)).le.trans ha
  have hr : (encPerm r).wt ≤ linPrimaryAccumulatorWeight W :=
    (wt_le_wt_list (by simp)).le.trans ha
  have hv := (wt_encFun_le ν hν).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hd) 4)
  have wp := (wt_nat_le p).trans (Nat.add_le_add_right hp 2)
  have wl := (wt_nat_le level).trans (Nat.add_le_add_right hl 2)
  have hh := wt_list_le [linActionContext gs m ρ c, linFinitePointVal m x, encPerm r, .nat p, encFun ν, .nat level]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hh
  change (Val.list [linActionContext gs m ρ c, linFinitePointVal m x, encPerm r, .nat p, encFun ν, .nat level]).wt ≤ _
  unfold linPrimaryIterationWeight
  omega

theorem linPrimaryAccumulatorWeight_poly : PBU (fun _ W _ => linPrimaryAccumulatorWeight W) := by
  unfold linPrimaryAccumulatorWeight linPrimaryContextWeight linPrimaryPointWeight linPrimaryRecordWeight
    linFiniteActionWeight linFiniteActionMatrixWeight linFiniteScalarBudget linVectorAccWt groupW
  norm_poly

theorem linPrimaryIterationWeight_poly : PBU (fun _ W _ => linPrimaryIterationWeight W) := by
  exact PBU.smul 100 (PBU.addc (PBU.add (PBU.add linPrimaryAccumulatorWeight_poly
    (PBU.mul PBU.W (PBU.addc (PBU.smul 2 PBU.W) 5))) PBU.W) 10)

end GI.Impl
