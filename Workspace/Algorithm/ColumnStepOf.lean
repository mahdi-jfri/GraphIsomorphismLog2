module

public import Workspace.Algorithm.DomainRestriction
public import Workspace.Paper.NormalTranspose

@[expose] public section

/-!
# Tools for the column step (Lemma A.14 with Theorem A.18)

The column step itself is `GI.Algorithm.ColumnStep` (`Workspace/Algorithm/RowSteps.lean`).
This file has its tools.

* `State.domKer`: a partition of the domain given by a label function, extended to `Ω` by
  one extra class off the domain; `State.domKer_inv`: it is invariant when the faithful image
  permutes the labels.
* The refactored hierarchy. Algorithm 4: "Refactor the old hierarchy by splitting and
  reordering its interval factors. Inherit every interval bound, clamped by its new interval
  ratio." The proof of Lemma A.14 splits each ratio `d_i = [L_i : L_{i-1}]` of the old local
  tower by eq. `modular-index-split`,
  `d_i = [L_i ∩ N : L_{i-1} ∩ N] [NL_i : NL_{i-1}]`, into a lower factor (inside the
  columns) and an upper factor (on the column quotient). `towerSplit` is that split, with
  the old bound clamped by each new ratio and the old origin label; `towerSplit_ok` checks it
  (`SplitOK`). `ρ` does not increase by the inequality `f(a) + f(b) ≤ f(ab)` of the proof of
  Lemma A.14 (`splitHier_rho_le`); `Q` does not increase because the logarithms of the
  ratios add and the bounds do not grow (`splitHier_Q_le`, Section 7.1).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω C : Type}

/-! ### Partitions of the domain, extended to `Ω` -/

namespace State

open Classical in
/-- The partition of `Ω` whose classes on the domain are the fibers of `c`, with one extra
class for the points off the domain. -/
noncomputable def domKer {X : Type*} (S : State Ω C) (c : S.dom → X) : Setoid Ω :=
  Setoid.ker fun a => if h : a ∈ S.dom then some (c ⟨a, h⟩) else none

/-- A fiber partition of the domain that the faithful image permutes is invariant under the
group of the state. -/
theorem domKer_inv {X : Type*} {S : State Ω C} (c : S.dom → X)
    (hc : ∀ g : S.G, ∀ v w, c v = c w → c (S.domHom g v) = c (S.domHom g w)) :
    ∀ g ∈ S.G, ∀ v w, (S.domKer c).r (g v) (g w) ↔ (S.domKer c).r v w := by
  classical
  intro g hg v w
  -- `g` and `g⁻¹` both carry fibers to fibers.
  have hc' : ∀ a b : S.dom, c (S.domHom ⟨g, hg⟩ a) = c (S.domHom ⟨g, hg⟩ b) ↔ c a = c b := by
    intro a b
    refine ⟨fun h => ?_, hc ⟨g, hg⟩ a b⟩
    have h' := hc ⟨g, hg⟩⁻¹ _ _ h
    rwa [← Perm.mul_apply, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Perm.one_apply, Perm.one_apply] at h'
  have hmem : ∀ a, g a ∈ S.dom ↔ a ∈ S.dom := S.dom_inv g hg
  change (if h : g v ∈ S.dom then some (c ⟨g v, h⟩) else none) =
      (if h : g w ∈ S.dom then some (c ⟨g w, h⟩) else none) ↔
    (if h : v ∈ S.dom then some (c ⟨v, h⟩) else none) =
      (if h : w ∈ S.dom then some (c ⟨w, h⟩) else none)
  by_cases hv : v ∈ S.dom <;> by_cases hw : w ∈ S.dom
  · rw [dif_pos ((hmem v).2 hv), dif_pos ((hmem w).2 hw), dif_pos hv, dif_pos hw,
      Option.some_inj, Option.some_inj]
    exact hc' ⟨v, hv⟩ ⟨w, hw⟩
  · rw [dif_pos ((hmem v).2 hv), dif_neg (fun h => hw ((hmem w).1 h)), dif_pos hv, dif_neg hw]
    simp
  · rw [dif_neg (fun h => hv ((hmem v).1 h)), dif_pos ((hmem w).2 hw), dif_neg hv, dif_pos hw]
    simp
  · rw [dif_neg (fun h => hv ((hmem v).1 h)), dif_neg (fun h => hw ((hmem w).1 h)),
      dif_neg hv, dif_neg hw]

theorem domKer_r_of_mem {X : Type*} {S : State Ω C} (c : S.dom → X) {v w : Ω}
    (hv : v ∈ S.dom) (hw : w ∈ S.dom) : (S.domKer c).r v w ↔ c ⟨v, hv⟩ = c ⟨w, hw⟩ := by
  classical
  change (if h : v ∈ S.dom then some (c ⟨v, h⟩) else none) =
      (if h : w ∈ S.dom then some (c ⟨w, h⟩) else none) ↔ _
  rw [dif_pos hv, dif_pos hw, Option.some_inj]

end State

/-! ### The refactored hierarchy -/

/-- A split of an old interval `I` into a lower and an upper interval: the new ratios are
positive with product `d_I`, and the new bounds are at most the old bound. -/
def SplitOK (I : Interval Ω) (p : Interval Ω × Interval Ω) : Prop :=
  p.1.ratio * p.2.ratio = I.ratio ∧ 0 < p.1.ratio ∧ 0 < p.2.ratio ∧
    p.1.cap ≤ I.cap ∧ p.2.cap ≤ I.cap

/-- The refactored hierarchy: the lower intervals, then the upper intervals. -/
def splitHier (sp : List (Interval Ω × Interval Ω)) : List (Interval Ω) :=
  sp.map Prod.fst ++ sp.map Prod.snd

theorem hierRho_append (l l' : List (Interval Ω)) :
    State.hierRho (l ++ l') = State.hierRho l + State.hierRho l' := by
  simp [State.hierRho]

theorem hierQ_append (l l' : List (Interval Ω)) :
    State.hierQ (l ++ l') = State.hierQ l + State.hierQ l' := by
  simp [State.hierQ]

/-- `ρ` does not increase under a split (proof of Lemma A.14: "The inequality
`f(a) + f(b) ≤ f(ab)` … shows that `ρ` does not increase"). -/
theorem splitHier_rho_le {l : List (Interval Ω)} {sp : List (Interval Ω × Interval Ω)}
    (h : List.Forall₂ SplitOK l sp) : State.hierRho (splitHier sp) ≤ State.hierRho l := by
  rw [splitHier, hierRho_append]
  induction h with
  | nil => simp [State.hierRho]
  | @cons I p l sp hIp _ ih =>
    obtain ⟨hprod, ha, hb, -, -⟩ := hIp
    have h1 := GI.Paper.lem_normal_transpose_rho [(p.1.ratio, p.2.ratio)] (by simpa using ⟨ha, hb⟩)
    simp only [GI.NormalTranspose.rho, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, hprod] at h1
    have h1' : ((GI.towerRank p.1.ratio : ℤ) : ℝ) + ((GI.towerRank p.2.ratio : ℤ) : ℝ) ≤
        ((GI.towerRank I.ratio : ℤ) : ℝ) := by exact_mod_cast h1
    simp only [State.hierRho, List.map_cons, List.sum_cons] at ih ⊢
    linarith

/-- `Q` does not increase under a split (Section 7.1: "Splitting or restricting intervals
also cannot increase `Q`, because the logarithms of the interval ratios add and every child
inherits its old width bound"). -/
theorem splitHier_Q_le {l : List (Interval Ω)} {sp : List (Interval Ω × Interval Ω)}
    (h : List.Forall₂ SplitOK l sp) : State.hierQ (splitHier sp) ≤ State.hierQ l := by
  rw [splitHier, hierQ_append]
  induction h with
  | nil => simp [State.hierQ]
  | @cons I p l sp hIp _ ih =>
    obtain ⟨hprod, ha, hb, hca, hcb⟩ := hIp
    have hlogmax : ∀ c c' : ℕ, c ≤ c' →
        Real.log (max c 2 : ℕ) ≤ Real.log (max c' 2 : ℕ) := by
      intro c c' hcc
      apply Real.log_le_log
      · have : (2 : ℝ) ≤ (max c 2 : ℕ) := by exact_mod_cast le_max_right c 2
        linarith
      · exact_mod_cast max_le_max hcc le_rfl
    have hla : 0 ≤ Real.log p.1.ratio := Real.log_natCast_nonneg _
    have hlb : 0 ≤ Real.log p.2.ratio := Real.log_natCast_nonneg _
    have hmul : Real.log I.ratio = Real.log p.1.ratio + Real.log p.2.ratio := by
      rw [← hprod, Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
    have h1 := mul_le_mul_of_nonneg_left (hlogmax _ _ hca) hla
    have h2 := mul_le_mul_of_nonneg_left (hlogmax _ _ hcb) hlb
    simp only [State.hierQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [hmul]
    nlinarith

/-! ### The split of a local tower (eq. `modular-index-split`) -/

section Tower

variable {H : Type*} [Group H] (L : ℕ → Subgroup H) (N : Subgroup H) (p₁ p₂ : ℕ → Setoid Ω)

/-- The split of the hierarchy `l` whose `i`-th ratio (counted from `j`) is
`[L_{i+1} : L_i]`: the lower interval has ratio `[L_{i+1} ∩ N : L_i ∩ N]`, the upper one
`[N L_{i+1} : N L_i]`, both with the old bound clamped by the new ratio and the old origin
label. -/
noncomputable def towerSplit : ℕ → List (Interval Ω) → List (Interval Ω × Interval Ω)
  | _, [] => []
  | j, I :: l =>
    (⟨p₁ j, (L j ⊓ N).relIndex (L (j + 1) ⊓ N), min I.cap ((L j ⊓ N).relIndex (L (j + 1) ⊓ N)),
        I.origin⟩,
      ⟨p₂ j, (N ⊔ L j).relIndex (N ⊔ L (j + 1)),
        min I.cap ((N ⊔ L j).relIndex (N ⊔ L (j + 1))), I.origin⟩) :: towerSplit (j + 1) l

theorem relIndex_pos_of_finite [Finite H] (A B : Subgroup H) : 0 < A.relIndex B := by
  unfold Subgroup.relIndex
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

/-- The tower split is a split (eq. `modular-index-split`, `GI.Paper.eq_modular_index_split`):
`[L_{i+1} : L_i] = [L_{i+1} ∩ N : L_i ∩ N] [N L_{i+1} : N L_i]`. -/
theorem towerSplit_ok [Finite H] [N.Normal] (hmono : ∀ i, L i ≤ L (i + 1)) :
    ∀ (j : ℕ) (l : List (Interval Ω)),
      (∀ (i : ℕ) (hi : i < l.length), l[i].ratio = (L (j + i)).relIndex (L (j + i + 1))) →
      List.Forall₂ SplitOK l (towerSplit L N p₁ p₂ j l)
  | _, [], _ => List.Forall₂.nil
  | j, I :: l, hr => by
    refine List.Forall₂.cons ⟨?_, relIndex_pos_of_finite _ _, relIndex_pos_of_finite _ _,
      min_le_left _ _, min_le_left _ _⟩ (towerSplit_ok hmono (j + 1) l fun i hi => ?_)
    · have h0 := hr 0 (by simp)
      simp only [List.getElem_cons_zero, add_zero] at h0
      rw [h0, GI.Paper.eq_modular_index_split N (hmono j)]
    · have := hr (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at this
      rw [this]
      congr 2 <;> omega

end Tower

end GI.Algorithm
