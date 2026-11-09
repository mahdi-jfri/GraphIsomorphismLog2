module

public import Workspace.Degree.GraphLevels
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Workspace.Statement.Main

/-!
# Distance levels and rooted isomorphisms

The layers and rooted isomorphisms of Section 9.1 of the paper.

* `lev X v u`: the distance from `v` to `u`, or `n` if `u` is not connected to `v`.
* `lev_hasLevels`: the distance levels are levels up to `n - 1`.
* `IsRooted X v Y w g`: `g` maps `v` to `w`, and it is an isomorphism from the component of `v` to
  the component of `w`.
* `IsRooted.inv`, `IsRooted.lev_eq`: its inverse is rooted, and it keeps levels.
* `IsRooted.mem_ball`, `rooted_of_mem_ball`: the link with `C_{n-1}`.
-/

@[expose] public section

namespace GI.Degree

open Equiv GI.Statement

variable {n : ℕ} {X Y : SimpleGraph (Fin n)} {v w u : Fin n}

open Classical in
/-- The distance level. -/
noncomputable def lev (X : SimpleGraph (Fin n)) (v u : Fin n) : ℕ :=
  if X.Reachable v u then X.dist v u else n

theorem lev_of_reach (h : X.Reachable v u) : lev X v u = X.dist v u := by
  simp [lev, h]

theorem lev_of_not_reach (h : ¬X.Reachable v u) : lev X v u = n := by
  simp [lev, h]

theorem dist_lt_of_reach (h : X.Reachable v u) : X.dist v u < n := by
  classical
  obtain ⟨p, -⟩ := h.exists_walk_length_eq_dist
  have h1 : X.dist v u ≤ p.bypass.length := SimpleGraph.dist_le _
  have h2 := p.bypass_isPath.length_lt
  simp only [Fintype.card_fin] at h2
  omega

theorem lev_lt_iff : lev X v u < n ↔ X.Reachable v u := by
  by_cases h : X.Reachable v u
  · simp [h, lev_of_reach h, dist_lt_of_reach h]
  · simp [h, lev_of_not_reach h]

theorem lev_le (X : SimpleGraph (Fin n)) (v u : Fin n) : lev X v u ≤ n := by
  by_cases h : X.Reachable v u
  · rw [lev_of_reach h]; exact (dist_lt_of_reach h).le
  · rw [lev_of_not_reach h]

theorem dist_succ_le {a b : Fin n} (h : X.Reachable v a) (hab : X.Adj a b) :
    X.dist v b ≤ X.dist v a + 1 := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  have := SimpleGraph.dist_le (p.concat hab)
  rw [SimpleGraph.Walk.length_concat, hp] at this
  exact this

/-- **The distance levels.** -/
theorem lev_hasLevels (X : SimpleGraph (Fin n)) (v : Fin n) : HasLevels X (lev X v) (n - 1) := by
  have hn : 0 < n := v.pos
  refine ⟨⟨v, fun u => ?_⟩, fun a b hab ha => ?_, fun b h1 h2 => ?_⟩
  · by_cases h : X.Reachable v u
    · rw [lev_of_reach h, h.dist_eq_zero_iff, eq_comm]
    · rw [lev_of_not_reach h]
      constructor
      · omega
      · rintro rfl
        exact absurd (SimpleGraph.Reachable.refl _) h
  · have hr : X.Reachable v a := lev_lt_iff.1 (by omega)
    have hb : X.Reachable v b := hr.trans hab.reachable
    rw [lev_of_reach hr, lev_of_reach hb]
    exact dist_succ_le hr hab
  · have hb : X.Reachable v b := lev_lt_iff.1 (by omega)
    rw [lev_of_reach hb] at h1 ⊢
    obtain ⟨p, hp⟩ := hb.symm.exists_walk_length_eq_dist
    cases p with
    | nil => simp at h1
    | @cons _ a _ hba q =>
      have hra : X.Reachable v a := q.reverse.reachable
      refine ⟨a, hba.symm, ?_⟩
      rw [lev_of_reach hra]
      have h3 := SimpleGraph.dist_le q.reverse
      have h4 := dist_succ_le hra hba.symm
      rw [SimpleGraph.Walk.length_reverse] at h3
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.dist_comm] at hp
      omega

/-- `g` maps `v` to `w`, and it is an isomorphism from the component of `v` to the component of
`w`. -/
structure IsRooted (X : SimpleGraph (Fin n)) (v : Fin n) (Y : SimpleGraph (Fin n)) (w : Fin n)
    (g : Perm (Fin n)) : Prop where
  root : g v = w
  adj : ∀ a b, X.Reachable v a → (X.Adj a b ↔ Y.Adj (g a) (g b))

variable {g : Perm (Fin n)}

/-- A rooted map sends walks that start in the component to walks of the same length. -/
theorem IsRooted.walk (hg : IsRooted X v Y w g) {a b : Fin n} (ha : X.Reachable v a)
    (p : X.Walk a b) : ∃ q : Y.Walk (g a) (g b), q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons a c b hac p ih =>
    obtain ⟨q, hq⟩ := ih (ha.trans hac.reachable)
    exact ⟨.cons ((hg.adj _ _ ha).1 hac) q, by simp [hq]⟩

theorem IsRooted.reach (hg : IsRooted X v Y w g) {a : Fin n} (ha : X.Reachable v a) :
    Y.Reachable w (g a) := by
  obtain ⟨p⟩ := ha
  obtain ⟨q, -⟩ := hg.walk (SimpleGraph.Reachable.refl _) p
  rw [hg.root] at q
  exact ⟨q⟩

/-- The inverse of a rooted map is rooted. -/
theorem IsRooted.inv (hg : IsRooted X v Y w g) : IsRooted Y w X v g⁻¹ := by
  have hroot : g⁻¹ w = v := by rw [← hg.root]; simp
  have hr : ∀ a b, Y.Walk a b → X.Reachable v (g⁻¹ a) → X.Reachable v (g⁻¹ b) := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a c b hac p ih =>
      intro ha
      refine ih (ha.trans (SimpleGraph.Adj.reachable ?_))
      refine (hg.adj _ _ ha).2 ?_
      simpa using hac
  refine ⟨hroot, fun a b ha => ?_⟩
  obtain ⟨p⟩ := ha
  have h1 := hr _ _ p (by rw [hroot])
  have := hg.adj (g⁻¹ a) (g⁻¹ b) h1
  simpa using this.symm

theorem IsRooted.reach_iff (hg : IsRooted X v Y w g) {a : Fin n} :
    Y.Reachable w (g a) ↔ X.Reachable v a := by
  refine ⟨fun h => ?_, hg.reach⟩
  simpa using hg.inv.reach h

theorem IsRooted.dist_le (hg : IsRooted X v Y w g) {a : Fin n} (ha : X.Reachable v a) :
    Y.dist w (g a) ≤ X.dist v a := by
  obtain ⟨p, hp⟩ := ha.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hg.walk (SimpleGraph.Reachable.refl _) p
  obtain rfl := hg.root
  have h1 := SimpleGraph.dist_le q
  omega

theorem IsRooted.lev_eq (hg : IsRooted X v Y w g) (a : Fin n) : lev Y w (g a) = lev X v a := by
  by_cases ha : X.Reachable v a
  · have hb := hg.reach ha
    rw [lev_of_reach ha, lev_of_reach hb]
    have h2 := hg.inv.dist_le hb
    have e : g⁻¹ (g a) = a := by simp
    rw [e] at h2
    exact le_antisymm (hg.dist_le ha) h2
  · rw [lev_of_not_reach ha, lev_of_not_reach (fun h => ha (hg.reach_iff.1 h))]

/-- The transport of levels along a relabeling. -/
theorem HasLevels.relabel {ℓ ℓ' : Fin n → ℕ} {R : ℕ} {ρ : Perm (Fin n)} (hY : HasLevels Y ℓ' R)
    (hρ : ∀ u, ℓ' (ρ u) = ℓ u) : HasLevels (pull ρ Y) ℓ R := by
  have hρ' : ∀ u, ℓ' u = ℓ (ρ⁻¹ u) := fun u => by rw [← hρ]; simp
  refine ⟨?_, fun u b h hu => ?_, fun b h1 h2 => ?_⟩
  · obtain ⟨o, ho⟩ := hY.root
    refine ⟨ρ⁻¹ o, fun u => ?_⟩
    rw [← hρ, ho, Perm.eq_inv_iff_eq]
  · have := hY.step _ _ h (by rwa [hρ])
    rwa [hρ, hρ] at this
  · obtain ⟨u, hu, he⟩ := hY.back (ρ b) (by rwa [hρ]) (by rwa [hρ])
    refine ⟨ρ⁻¹ u, by simpa using hu, ?_⟩
    rw [← hρ b, ← he, hρ']

/-- A rooted map gives an element of `C_{n-1}`. Here `ρ` is a relabeling of `Y` onto the levels of
`X`. -/
theorem IsRooted.mem_ball {ρ : Perm (Fin n)} (hg : IsRooted X v Y w g)
    (hρ : ∀ u, lev Y w (ρ u) = lev X v u) : ∃ T, T ∈ Ball (lev X v) (n - 1) X (pull ρ Y) := by
  have hρ' : ∀ u, lev X v (ρ⁻¹ u) = lev Y w u := fun u => by rw [← hρ]; simp
  have hl : ∀ u, lev X v ((ρ⁻¹ * g) u) = lev X v u := fun u => by
    rw [Perm.mul_apply, hρ', hg.lev_eq]
  have hn : 0 < n := v.pos
  refine ⟨ballCut (lev X v) (n - 1) (ρ⁻¹ * g) hl, fun u => ?_, fun u hu => ?_, fun a b ha hb => ?_⟩
  · rcases le_or_gt (lev X v u) (n - 1) with h | h
    · rw [ballCut_apply_of_le hl h, hl]
    · rw [ballCut_apply_of_lt hl h]
  · exact ballCut_apply_of_lt hl hu
  · rw [ballCut_apply_of_le hl ha, ballCut_apply_of_le hl hb, pull_adj]
    simp only [Perm.mul_apply]
    have e : ∀ c, ρ (ρ⁻¹ c) = c := fun c => by simp
    rw [e, e]
    exact hg.adj a b (lev_lt_iff.1 (by omega))

/-- An element of `C_{n-1}` gives a rooted map. Here `Y₀` is `Y` relabeled by `ρ`. -/
theorem rooted_of_mem_ball {ρ T : Perm (Fin n)} {Y₀ : SimpleGraph (Fin n)}
    (hY₀ : ∀ a b, Y₀.Adj a b ↔ Y.Adj (ρ a) (ρ b)) (hρ : ∀ u, lev Y w (ρ u) = lev X v u)
    (hT : T ∈ Ball (lev X v) (n - 1) X Y₀) : IsRooted X v Y w (ρ * T) := by
  obtain ⟨t1, -, t3⟩ := hT
  have hn : 0 < n := v.pos
  have hlev : ∀ a, lev Y w ((ρ * T) a) = lev X v a := fun a => by
    rw [Perm.mul_apply, hρ, t1]
  have hroot : ∀ {a}, lev Y w a = 0 → a = w := fun {a} h => (((lev_hasLevels Y w).root.choose_spec a).1 h).trans
    ((((lev_hasLevels Y w).root.choose_spec w).1 (by
      rw [lev_of_reach (SimpleGraph.Reachable.refl _)]; simp))).symm
  have h0 : lev X v v = 0 := by
    rw [lev_of_reach (SimpleGraph.Reachable.refl _)]; simp
  refine ⟨hroot (by rw [hlev, h0]), fun a b ha => ?_⟩
  have hla : lev X v a ≤ n - 1 := by
    have := lev_lt_iff.2 ha
    omega
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hb : lev X v b ≤ n - 1
  · rw [t3 a b hla hb, hY₀]
  · have hb' : ¬X.Reachable v b := fun h => hb (by have := lev_lt_iff.2 h; omega)
    constructor
    · intro h
      exact absurd (ha.trans h.reachable) hb'
    · intro h
      exfalso
      have h1 : Y.Reachable w (ρ (T a)) := by
        refine lev_lt_iff.1 ?_
        have := hlev a
        rw [Perm.mul_apply] at this
        rw [this]
        omega
      have h2 : Y.Reachable w (ρ (T b)) := h1.trans h.reachable
      have h3 := lev_lt_iff.2 h2
      have h4 := hlev b
      rw [Perm.mul_apply] at h4
      rw [h4] at h3
      exact hb' (lev_lt_iff.1 h3)

/-- A rooted map from `X` to itself cut at `n - 1` is in `A_{n-1}`. -/
theorem ball_of_rooted_cut (hg : IsRooted X v X v g) :
    ballCut (lev X v) (n - 1) g hg.lev_eq ∈ ballGroup (lev X v) (n - 1) X := by
  have hn : 0 < n := v.pos
  have hl := hg.lev_eq
  refine ⟨fun u => ?_, fun u hu => ballCut_apply_of_lt hl hu, fun a b ha hb => ?_⟩
  · rcases le_or_gt (lev X v u) (n - 1) with h | h
    · rw [ballCut_apply_of_le hl h, hl]
    · rw [ballCut_apply_of_lt hl h]
  · rw [ballCut_apply_of_le hl ha, ballCut_apply_of_le hl hb]
    exact hg.adj a b (lev_lt_iff.1 (by omega))

/-- An element of `A_{n-1}` is an automorphism of `X`, and it fixes all points outside the component
of `v`. -/
theorem ballGroup_top_mem_aut (hg : g ∈ ballGroup (lev X v) (n - 1) X) : g ∈ autGroup X ∧
    IsRooted X v X v g ∧ ∀ u, ¬X.Reachable v u → g u = u := by
  have hn : 0 < n := v.pos
  have hr : IsRooted X v X v g := by
    have := rooted_of_mem_ball (ρ := 1) (Y₀ := X) (Y := X) (w := v) (X := X) (v := v)
      (fun _ _ => Iff.rfl) (fun _ => rfl) hg
    simpa using this
  have hfix : ∀ u, ¬X.Reachable v u → g u = u := fun u hu =>
    hg.2.1 u (by rw [lev_of_not_reach hu]; omega)
  refine ⟨fun a b => ?_, hr, hfix⟩
  by_cases ha : X.Reachable v a
  · exact (hr.adj a b ha).symm
  by_cases hb : X.Reachable v b
  · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm X a b]
    exact (hr.adj b a hb).symm
  · rw [hfix a ha, hfix b hb]

end GI.Degree
