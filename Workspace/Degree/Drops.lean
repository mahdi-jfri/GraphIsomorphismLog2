module

public import Workspace.Degree.Potential
public import Workspace.FiniteBudget

@[expose] public section

/-!
# How `ψ` changes at a child

The operations of the paper lower `ψ` in three ways. These results are the ones that the shapes of
`Workspace/Degree/Spine.lean` use.

* `psi_mono`: a child under a subgroup, on a part of the domain, has no larger `ψ`.
* `psi_drop_of_orbits`: if the orbits of the child have at most `3 s / 4` points, `ψ` falls by
  `log(8/7)`. This covers a normalized group with orbits of at most `s / 2` points.
* `psi_drop_charged`: a charged call lowers `ψ` by `log(8/7)`.
* `psi_drop_kernel`: a block kernel on `d` blocks lowers `ψ` by `(log d) / 3`.

All three use that the parent is transitive with a nonempty domain, which gives
`ψ = log(s + 2) + σ` (`psi_eq`).
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly Equiv

variable {Ω C C' : Type}

/-- The constant `c₀ = log(8/7)`. -/
noncomputable def cZero : ℝ := Real.log (8 / 7)

theorem cZero_pos : 0 < cZero := Real.log_pos (by norm_num)

theorem cZero_le : cZero ≤ 1 / 7 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 / 7 by norm_num)
  unfold cZero
  linarith

theorem five_le_κ : 5 ≤ P₀.κ := le_trans (by norm_num) P₀_κ

theorem card_orb_eq (G : Subgroup (Perm Ω)) (v : Ω) : Nat.card (orb G v) = (orb G v).ncard :=
  _root_.Nat.card_coe_set_eq _

theorem pointValue_mono [Finite Ω] {G H : Subgroup (Perm Ω)} (h : H ≤ G) (v : Ω) :
    pointValue H v ≤ pointValue G v := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have h1 : (orb H v).ncard ≤ (orb G v).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro w ⟨g, hg, rfl⟩
    exact ⟨g, h hg, rfl⟩
  have h2 : GI.sigma P₀.κ v H ≤ GI.sigma P₀.κ v G :=
    GI.sigma_subgroup_mono five_le_κ v h
  have h1' : ((orb H v).ncard : ℝ) ≤ ((orb G v).ncard : ℝ) := by exact_mod_cast h1
  have h2' : (GI.sigma P₀.κ v H : ℝ) ≤ (GI.sigma P₀.κ v G : ℝ) := by exact_mod_cast h2
  have h3 : Real.log (((orb H v).ncard : ℝ) + 2) ≤ Real.log (((orb G v).ncard : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  unfold pointValue
  linarith

/-- A child under a subgroup, on a part of the domain, has no larger `ψ`. The cases of the
orbit chain, of a product, and of a transitive normalized group are of this form. -/
theorem psi_mono [Finite Ω] {S : State Ω C} {T : State Ω C'} (hG : T.G ≤ S.G)
    (hD : T.dom ⊆ S.dom) : T.psi ≤ S.psi :=
  State.psi_le S.psi_nonneg fun v hv =>
    (pointValue_mono hG v).trans (S.point_le_psi (hD hv))

/-- On a transitive state with a nonempty domain, `ψ = log(s + 2) + σ`. -/
theorem psi_eq [Finite Ω] {S : State Ω C} (ht : S.Transitive) (h1 : 1 ≤ S.size) :
    S.psi = Real.log ((S.size : ℝ) + 2) + (S.sigma P₀.κ : ℝ) := by
  have hle : S.psi ≤ Real.log ((S.size : ℝ) + 2) + (S.sigma P₀.κ : ℝ) := by
    refine State.psi_le ?_ fun v hv => ?_
    · have h0 : 0 ≤ Real.log ((S.size : ℝ) + 2) :=
        Real.log_nonneg (by have : (0 : ℝ) ≤ S.size := Nat.cast_nonneg _; linarith)
      positivity
    · have h2 : (orb S.G v).ncard ≤ S.size := by
        unfold State.size
        rw [_root_.Nat.card_coe_set_eq]
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro w ⟨g, hg, rfl⟩
        exact (S.dom_inv g hg v).2 hv
      have h2' : ((orb S.G v).ncard : ℝ) ≤ S.size := by exact_mod_cast h2
      have h3 : Real.log (((orb S.G v).ncard : ℝ) + 2) ≤ Real.log ((S.size : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h4 : (GI.sigma P₀.κ v S.G : ℝ) ≤ (S.sigma P₀.κ : ℝ) := by
        exact_mod_cast S.sigma_point_le P₀.κ hv
      unfold pointValue
      linarith
  refine le_antisymm hle ?_
  obtain ⟨v, hv⟩ := exists_mem_dom h1
  have h5 := S.point_le_psi hv
  have hsub : S.dom ⊆ orb S.G v := fun w hw => ht v hv w hw
  have hc : S.size ≤ (orb S.G v).ncard := by
    unfold State.size
    rw [_root_.Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hc' : (S.size : ℝ) ≤ ((orb S.G v).ncard : ℝ) := by exact_mod_cast hc
  have h3 : Real.log ((S.size : ℝ) + 2) ≤ Real.log (((orb S.G v).ncard : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [State.sigma_eq_point P₀.κ ht hv]
  unfold pointValue at h5
  linarith

/-- A pointwise bound gives a drop of `ψ`. -/
theorem psi_add_le {S : State Ω C} {T : State Ω C'} {c : ℝ} [Finite Ω] (ht : S.Transitive)
    (h1 : 1 ≤ S.size) (hc : c ≤ Real.log ((S.size : ℝ) + 2))
    (h : ∀ v ∈ T.dom, pointValue T.G v + c ≤ Real.log ((S.size : ℝ) + 2) + (S.sigma P₀.κ : ℝ)) :
    T.psi + c ≤ S.psi := by
  rw [psi_eq ht h1]
  have h2 : T.psi ≤ Real.log ((S.size : ℝ) + 2) + (S.sigma P₀.κ : ℝ) - c := by
    refine State.psi_le ?_ fun v hv => by linarith [h v hv]
    have : (0 : ℝ) ≤ (S.sigma P₀.κ : ℝ) := Nat.cast_nonneg _
    linarith
  linarith

theorem sigma_le_parent [Finite Ω] {S : State Ω C} {T : State Ω C'} (hG : T.G ≤ S.G)
    (hD : T.dom ⊆ S.dom) {v : Ω} (hv : v ∈ T.dom) :
    (GI.sigma P₀.κ v T.G : ℝ) ≤ (S.sigma P₀.κ : ℝ) := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  exact_mod_cast (GI.sigma_subgroup_mono five_le_κ v hG).trans (S.sigma_point_le P₀.κ (hD hv))

theorem log_add_cZero_le {s x : ℝ} (hs : 2 ≤ s) (hx0 : 0 ≤ x) (hx : 4 * x ≤ 3 * s) :
    Real.log (x + 2) + cZero ≤ Real.log (s + 2) := by
  unfold cZero
  rw [← Real.log_mul (by positivity) (by norm_num)]
  exact Real.log_le_log (by positivity) (by nlinarith)

/-- If the child's orbits have at most `3 s / 4` points, `ψ` falls by `c₀`. -/
theorem psi_drop_of_orbits [Finite Ω] {S : State Ω C} {T : State Ω C'} (ht : S.Transitive)
    (h2 : 2 ≤ S.size) (hG : T.G ≤ S.G) (hD : T.dom ⊆ S.dom)
    (h : ∀ v ∈ T.dom, 4 * Nat.card (orb T.G v) ≤ 3 * S.size) : T.psi + cZero ≤ S.psi := by
  have hs : (2 : ℝ) ≤ S.size := by exact_mod_cast h2
  have hl : 1 ≤ Real.log ((S.size : ℝ) + 2) := one_le_log_three.trans
    (Real.log_le_log (by norm_num) (by linarith))
  refine psi_add_le ht (by omega) (by linarith [cZero_le]) fun v hv => ?_
  have h3 : (4 : ℝ) * ((orb T.G v).ncard : ℝ) ≤ 3 * (S.size : ℝ) := by
    have := h v hv
    rw [card_orb_eq] at this
    exact_mod_cast this
  have h4 := log_add_cZero_le hs (Nat.cast_nonneg _) h3
  have h5 := sigma_le_parent hG hD hv
  unfold pointValue
  linarith

/-- **A charged call lowers `ψ`.** The call is charged at each point in one of two ways: a small
orbit lowers the first term of the point's value, and a marked step lowers the second. -/
theorem psi_drop_charged [Finite Ω] {S : State Ω C} {T : State Ω C'} (ht : S.Transitive)
    (h2 : 2 ≤ S.size) (hc : ChargedCall P₀ S T) : T.psi + cZero ≤ S.psi := by
  have hs : (2 : ℝ) ≤ S.size := by exact_mod_cast h2
  have hl : 1 ≤ Real.log ((S.size : ℝ) + 2) := one_le_log_three.trans
    (Real.log_le_log (by norm_num) (by linarith))
  refine psi_add_le ht (by omega) (by linarith [cZero_le]) fun v hv => ?_
  have hsub : (orb T.G v).ncard ≤ S.size := by
    unfold State.size
    rw [_root_.Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro w ⟨g, hg, rfl⟩
    exact hc.sub ((T.dom_inv g hg v).2 hv)
  have hsub' : ((orb T.G v).ncard : ℝ) ≤ S.size := by exact_mod_cast hsub
  rcases hc.types v hv with h | h
  · have h3 : (4 : ℝ) * ((orb T.G v).ncard : ℝ) ≤ 3 * (S.size : ℝ) := by
      rw [card_orb_eq] at h
      have e : P₀.θ = 3 / 4 := rfl
      rw [e] at h
      linarith
    have h4 := log_add_cZero_le hs (Nat.cast_nonneg _) h3
    have h5 := sigma_le_parent hc.le hc.sub hv
    unfold pointValue
    linarith
  · have h3 : Real.log (((orb T.G v).ncard : ℝ) + 2) ≤ Real.log ((S.size : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have h4 : (GI.sigma P₀.κ v T.G : ℝ) + (P₀.κ : ℝ) ≤ (S.sigma P₀.κ : ℝ) := by exact_mod_cast h
    have h5 : (5 : ℝ) ≤ (P₀.κ : ℝ) := by exact_mod_cast five_le_κ
    have := cZero_le
    unfold pointValue
    linarith

/-- The inequality behind the kernel drop: `log(s/d + 2) + (log d)/3 ≤ log(s + 2)`. -/
theorem log_add_third_le {s d x : ℝ} (hd : 2 ≤ d) (hds : d ≤ s) (hx0 : 0 ≤ x)
    (hx : d * x ≤ s) : Real.log (x + 2) + Real.log d / 3 ≤ Real.log (s + 2) := by
  have hd0 : 0 < d := by linarith
  have ht : ∀ {a b : ℝ}, 0 < a → 0 < b → b * (a ^ 3) ≤ (s + 2) ^ 3 →
      Real.log a + Real.log b / 3 ≤ Real.log (s + 2) := by
    intro a b ha hb h
    have hs0 : 0 < s + 2 := by linarith
    have h1 := Real.log_le_log (by positivity) h
    rw [Real.log_mul hb.ne' (by positivity), Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  refine ht (by linarith) hd0 ?_
  -- Monotone in `x`, so take `x = s / d`, then monotone in `s`, so take `s = d`.
  have hkey : (s + 2) * 3 ≥ (d + 2) * (x + 2) := by nlinarith
  have hmain : 27 * d ≤ (d + 2) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (d - 1)) (by linarith : 0 ≤ d + 8)]
  have h3 : ((d + 2) * (x + 2)) ^ 3 ≤ ((s + 2) * 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hkey 3
  have hpos : 0 ≤ (x + 2) ^ 3 := by positivity
  have h4 : 27 * d * (x + 2) ^ 3 ≤ (d + 2) ^ 3 * (x + 2) ^ 3 :=
    mul_le_mul_of_nonneg_right hmain hpos
  nlinarith

/-- **A block kernel lowers `ψ`**, by `(log d) / 3` on `d` blocks. -/
theorem psi_drop_kernel [Finite Ω] {S : State Ω C} {T : State Ω C'} (ht : S.Transitive)
    {d : ℕ} (hd : 2 ≤ d) (hds : d ≤ S.size) (hG : T.G ≤ S.G) (hD : T.dom ⊆ S.dom)
    (h : ∀ v ∈ T.dom, d * Nat.card (orb T.G v) ≤ S.size) :
    T.psi + Real.log d / 3 ≤ S.psi := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hds' : (d : ℝ) ≤ S.size := by exact_mod_cast hds
  have hlg : Real.log d ≤ Real.log ((S.size : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  refine psi_add_le ht (by omega) (by linarith) fun v hv => ?_
  have h3 : (d : ℝ) * ((orb T.G v).ncard : ℝ) ≤ S.size := by
    have := h v hv
    rw [card_orb_eq] at this
    exact_mod_cast this
  have h4 := log_add_third_le hd' hds' (Nat.cast_nonneg _) h3
  have h5 := sigma_le_parent hG hD hv
  unfold pointValue
  linarith

end GI.Degree
