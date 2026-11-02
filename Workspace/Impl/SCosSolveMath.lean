import Workspace.Impl.SCosSpec
import Workspace.Proved.SCosCount

/-!
# The cost bound of the recursion

The bound of a call on a problem `(𝒢, Φ)` is
`scosT Q c 𝒢 Φ = min (scosBnd Q c |Φ|) (scosSmall Q c (scosMo 𝒢 Φ) |Φ|)`: the bound of
`Proved/SCosCount.lean` for `|Φ|` points, and the better bound for problems whose orbits have at
most `scosMo 𝒢 Φ` points. Here `Q` bounds the own work of one node. The four lemmas
`scosT_empty`, `scosT_split`, `scosT_base`, `scosT_big` are the four cases of the recursion; they
only combine the count lemmas `scosCount_*` with the facts on `scosMo` proved first.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

/-! ### The largest orbit -/

section Mo

open Classical

/-- The points of `Φ` in the orbit of `a`. -/
theorem scosMo_orbit_le {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {a : Fin n}
    (ha : a ∈ Φ) : (Φ.filter fun b => ∃ g ∈ 𝒢, g.1 a = b).card ≤ scosMo 𝒢 Φ := by
  classical
  unfold scosMo
  exact Finset.le_sup (f := fun a => (Φ.filter fun b => ∃ g ∈ 𝒢, g.1 a = b).card) ha

/-- Every orbit of a transitive group is all of `Φ`. -/
theorem scosMo_trans {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (h : ScosTrans 𝒢 Φ) :
    scosMo 𝒢 Φ = Φ.card := by
  classical
  apply le_antisymm
  · unfold scosMo
    exact Finset.sup_le fun a _ => Finset.card_filter_le _ _
  · rcases Φ.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · refine le_trans (le_of_eq ?_) (scosMo_orbit_le (𝒢 := 𝒢) ha)
      congr 1
      exact (Finset.filter_true_of_mem fun b hb => h a ha b hb).symm

/-- A subgroup on a subset has smaller orbits. -/
theorem scosMo_mono {𝒢 L : Subgroup (ScosPair n)} {Φ Φ' : Finset (Fin n)} (hL : L ≤ 𝒢)
    (hΦ : Φ' ⊆ Φ) : scosMo L Φ' ≤ scosMo 𝒢 Φ := by
  classical
  unfold scosMo
  refine Finset.sup_le fun a ha => le_trans ?_ (scosMo_orbit_le (𝒢 := 𝒢) (hΦ ha))
  refine Finset.card_le_card fun b hb => ?_
  simp only [Finset.mem_filter] at hb ⊢
  obtain ⟨hb, g, hg, rfl⟩ := hb
  exact ⟨hΦ hb, g, hL hg, rfl⟩

/-- The size of the orbit of a point is at most the largest orbit. -/
theorem scosMo_orbit_card {𝒢 : Subgroup (ScosPair n)} {Φ O : Finset (Fin n)} {a : Fin n}
    (ha : a ∈ O) (hO : ∀ b, b ∈ O ↔ b ∈ Φ ∧ ∃ g ∈ 𝒢, g.1 a = b) : O.card ≤ scosMo 𝒢 Φ := by
  classical
  have haΦ : a ∈ Φ := ((hO a).mp ha).1
  refine le_trans (le_of_eq (congrArg Finset.card ?_)) (scosMo_orbit_le (𝒢 := 𝒢) haΦ)
  ext b
  simp only [Finset.mem_filter, hO]

end Mo

/-! ### The bound -/

/-- **The bound of a call.** -/
noncomputable def scosT (Q c : ℕ) (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) : ℕ :=
  min (scosBnd Q c Φ.card) (scosSmall Q c (scosMo 𝒢 Φ) Φ.card)

theorem scosT_le_bnd (Q c : ℕ) (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) :
    scosT Q c 𝒢 Φ ≤ scosBnd Q c Φ.card := min_le_left _ _

theorem scosT_le_small (Q c : ℕ) (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) :
    scosT Q c 𝒢 Φ ≤ scosSmall Q c (scosMo 𝒢 Φ) Φ.card := min_le_right _ _

theorem scosSmall_mono (Q c j : ℕ) {s s' : ℕ} (h : s ≤ s') :
    scosSmall Q c s j ≤ scosSmall Q c s' j := by
  unfold scosSmall
  have := Nat.mul_le_mul_right j (Nat.pow_le_pow_left h (2 * c + 3))
  exact Nat.mul_le_mul_left _ (by omega)

theorem le_scosT {Q c q : ℕ} {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)}
    (h1 : q ≤ scosBnd Q c Φ.card) (h2 : q ≤ scosSmall Q c (scosMo 𝒢 Φ) Φ.card) :
    q ≤ scosT Q c 𝒢 Φ := le_min h1 h2

theorem scos_Q_le_bnd (Q c k : ℕ) : Q ≤ scosBnd Q c k := by
  unfold scosBnd; nlinarith [Nat.zero_le (k ^ (2 * c + 4))]

theorem scos_Q_le_small (Q c s j : ℕ) : Q ≤ scosSmall Q c s j := by
  unfold scosSmall; nlinarith [Nat.zero_le (s ^ (2 * c + 3) * j)]

/-- **The empty set.** -/
theorem scosT_empty {Q c q : ℕ} (𝒢 : Subgroup (ScosPair n)) (hq : q ≤ Q) :
    q ≤ scosT Q c 𝒢 ∅ :=
  le_scosT (hq.trans (scos_Q_le_bnd _ _ _)) (hq.trans (scos_Q_le_small _ _ _ _))

/-- **One point.** -/
theorem scosT_base {Q c q : ℕ} (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (hq : q ≤ Q) :
    q ≤ scosT Q c 𝒢 Φ :=
  le_scosT (hq.trans (scos_Q_le_bnd _ _ _)) (hq.trans (scos_Q_le_small _ _ _ _))

/-- **An intransitive node**: the orbit `O` of a point, then the rest `Φ \ O` under
`L ≤ 𝒢`. -/
theorem scosT_split {Q c q : ℕ} {𝒢 L : Subgroup (ScosPair n)} {Φ O : Finset (Fin n)}
    (hq : q ≤ Q) (hL : L ≤ 𝒢) (hOΦ : O ⊂ Φ) (hO1 : O.Nonempty)
    (hOmo : O.card ≤ scosMo 𝒢 Φ) :
    q + scosT Q c 𝒢 O + scosT Q c L (Φ \ O) ≤ scosT Q c 𝒢 Φ := by
  have hsub := hOΦ.subset
  have hcard : (Φ \ O).card = Φ.card - O.card := Finset.card_sdiff_of_subset hsub
  have hlt : O.card < Φ.card := Finset.card_lt_card hOΦ
  have ha : 1 ≤ O.card := Finset.card_pos.mpr hO1
  have hb : 1 ≤ (Φ \ O).card := by omega
  have t1 := scosT_le_bnd Q c 𝒢 O
  have t2 := scosT_le_bnd Q c L (Φ \ O)
  have t3 := scosT_le_small Q c L (Φ \ O)
  have hmo : scosMo L (Φ \ O) ≤ scosMo 𝒢 Φ := scosMo_mono hL Finset.sdiff_subset
  have t4 := scosSmall_mono Q c (Φ \ O).card hmo
  refine le_scosT ?_ ?_
  · have := scosCount_split Q c O.card (Φ \ O).card ha hb
    have e : O.card + (Φ \ O).card = Φ.card := by omega
    rw [e] at this
    omega
  · have := scosCount_small_step Q c (scosMo 𝒢 Φ) Φ.card O.card ha hOmo hlt.le
    rw [← hcard] at this
    omega

/-- **A transitive node with at least two points**: `ℓ` children on `Φ` under `K`, whose
orbits have at most `s` points, `m ≥ 2` blocks of `s` points. -/
theorem scosT_big {Q c q q' m s ℓ : ℕ} {𝒢 K : Subgroup (ScosPair n)} {Φ : Finset (Fin n)}
    (hq : q ≤ Q) (hq' : q' ≤ Q) (ht : ScosTrans 𝒢 Φ) (h2 : 2 ≤ Φ.card) (hm : 2 ≤ m)
    (hs : 1 ≤ s) (hms : m * s ≤ Φ.card) (hℓ : ℓ ≤ (m + 1) ^ c) (hK : scosMo K Φ ≤ s) :
    q + ℓ * (q' + scosT Q c K Φ) ≤ scosT Q c 𝒢 Φ := by
  have t1 : scosT Q c K Φ ≤ scosSmall Q c s Φ.card :=
    (scosT_le_small Q c K Φ).trans (scosSmall_mono Q c _ hK)
  have hb := scosCount_trans Q c Φ.card m s ℓ h2 hm hs hms hℓ
  have h1 : q + ℓ * (q' + scosT Q c K Φ) ≤ Q + ℓ * (Q + scosSmall Q c s Φ.card) :=
    Nat.add_le_add hq (Nat.mul_le_mul_left _ (Nat.add_le_add hq' t1))
  refine le_scosT (h1.trans hb) ?_
  rw [scosMo_trans ht]
  exact (h1.trans hb).trans (scosCount_small_trans Q c Φ.card Φ.card le_rfl)

end GI.Impl
