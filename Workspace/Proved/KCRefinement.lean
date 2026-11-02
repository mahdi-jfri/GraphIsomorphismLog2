import Workspace.Cited.CoherentConfig
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Fintype.Basic

/-!
# Canonical `k`-ary coherent refinement (`k`-ary Weisfeiler–Leman)

We prove `GI.Cited.KaryCoherentRefinement`, following [H, Sections 2.3–2.5]
(Helfgott–Bajpai–Dona, arXiv:1710.04574v1): the functors `F₂`, `F₃` and `k`-ary
Weisfeiler–Leman ([H, Algorithm 3]).

One round `kcrRound` sends a coloring `c` of `k`-tuples to the coloring whose value at `x` is a
fixed injective code in `ℕ` of four pieces of data: the old color `c x`, the equality pattern of
`x`, the colors `c (x ∘ τ)` for all `τ : Fin k → Fin k`, and the multiset over `z : Fin n` of the
color vectors `(c (update x i z))_i`. The map `F` runs `n^k + 1` rounds, the same number for
every input.

* The code contains the old color, so colors of `F` determine colors of the input across inputs.
* Each round commutes with relabelings of `Fin n`, so `F` does too.
* A coloring is *stable* if one round does not split any color class. Stability persists, and a
  round on an unstable coloring adds a color class. There are at most `n^k` classes, so after
  `n^k + 1` rounds the coloring is stable.
* A stable coloring is a coherent configuration (`kcr_isConfiguration_of_stable`,
  `kcr_isCoherent_of_stable`).

The only result used later is `GI.Proved.karyCoherentRefinement`.
-/

namespace GI.Proved

open Equiv Function

variable {n k : ℕ}

/-- The data one round records about a tuple. -/
abbrev KcrData (k : ℕ) : Type :=
  ℕ × (Fin k → Fin k → Bool) × ((Fin k → Fin k) → ℕ) × Multiset (Fin k → ℕ)

/-- A fixed injective code of the round data in `ℕ`. It depends only on `k`, never on the input. -/
noncomputable def kcrCode (k : ℕ) : KcrData k → ℕ :=
  Classical.choose (Countable.exists_injective_nat (KcrData k))

theorem kcrCode_injective (k : ℕ) : Injective (kcrCode k) :=
  Classical.choose_spec (Countable.exists_injective_nat (KcrData k))

/-- The color vector `(c (update x i z))_i`, used for the counts in `IsCoherent`. -/
def kcrVec (c : (Fin k → Fin n) → ℕ) (x : Fin k → Fin n) (z : Fin n) : Fin k → ℕ :=
  fun i => c (update x i z)

/-- The round data of the tuple `x` under the coloring `c`. -/
def kcrData (c : (Fin k → Fin n) → ℕ) (x : Fin k → Fin n) : KcrData k :=
  (c x, fun i j => decide (x i = x j), fun τ => c (x ∘ τ),
    (Finset.univ : Finset (Fin n)).val.map (kcrVec c x))

/-- One round of `k`-ary Weisfeiler–Leman. -/
noncomputable def kcrRound (c : (Fin k → Fin n) → ℕ) : (Fin k → Fin n) → ℕ :=
  fun x => kcrCode k (kcrData c x)

theorem kcrData_eq_of_round_eq {c d : (Fin k → Fin n) → ℕ} {x y : Fin k → Fin n}
    (h : kcrRound c x = kcrRound d y) : kcrData c x = kcrData d y :=
  kcrCode_injective k h

/-- The relabeling of a coloring by `σ`. -/
def kcrAct (σ : Perm (Fin n)) (c : (Fin k → Fin n) → ℕ) : (Fin k → Fin n) → ℕ :=
  fun x => c (σ.symm ∘ x)

/-! ### Equivariance and the palette clause -/

theorem kcrRound_act (σ : Perm (Fin n)) (c : (Fin k → Fin n) → ℕ) :
    kcrRound (kcrAct σ c) = kcrAct σ (kcrRound c) := by
  funext x
  simp only [kcrRound, kcrAct]
  congr 1
  simp only [kcrData, kcrAct]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
  · -- `σ.symm` is injective, so it keeps the equality pattern.
    funext i j
    simp
  · -- `σ.symm ∘ update x i z = update (σ.symm ∘ x) i (σ.symm z)`, and `σ.symm` permutes `Fin n`.
    have hv : kcrVec (kcrAct σ c) x = kcrVec c (σ.symm ∘ x) ∘ σ.symm := by
      funext z i
      simp only [kcrVec, kcrAct, comp_apply, comp_update]
    show Multiset.map (kcrVec (kcrAct σ c) x) Finset.univ.val =
      Multiset.map (kcrVec c (σ.symm ∘ x)) Finset.univ.val
    rw [hv, ← Multiset.map_map]
    congr 1
    exact (Finset.map_val σ.symm.toEmbedding _).symm.trans
      (congrArg Finset.val (Finset.map_univ_equiv σ.symm))

theorem kcrIter_act (σ : Perm (Fin n)) (c : (Fin k → Fin n) → ℕ) (m : ℕ) :
    kcrRound^[m] (kcrAct σ c) = kcrAct σ (kcrRound^[m] c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iterate_succ_apply', iterate_succ_apply', ih, kcrRound_act]

theorem kcrIter_color (m : ℕ) (c c' : (Fin k → Fin n) → ℕ) (x y : Fin k → Fin n)
    (h : kcrRound^[m] c x = kcrRound^[m] c' y) : c x = c' y := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply'] at h
    exact ih (congrArg Prod.fst (kcrData_eq_of_round_eq h))

/-! ### Stable colorings are coherent configurations -/

/-- `c` is stable if one round splits no color class. -/
def KcrStable (c : (Fin k → Fin n) → ℕ) : Prop :=
  ∀ x y, c x = c y → kcrRound c x = kcrRound c y

theorem kcr_isConfiguration_of_stable {c : (Fin k → Fin n) → ℕ} (hc : KcrStable c) :
    GI.Cited.IsConfiguration c := by
  refine ⟨fun x y hxy i j => ?_, fun x y hxy τ => ?_⟩
  · have h := congrArg (fun d => d.2.1 i j) (kcrData_eq_of_round_eq (hc x y hxy))
    simpa [kcrData] using h
  · exact congrArg (fun d => d.2.2.1 τ) (kcrData_eq_of_round_eq (hc x y hxy))

/-- The count in `IsCoherent` is the multiplicity of `κ` in the multiset of color vectors. -/
theorem kcr_card_filter_eq_count (c : (Fin k → Fin n) → ℕ) (x : Fin k → Fin n)
    (κ : Fin k → ℕ) :
    (Finset.univ.filter fun z : Fin n => ∀ i, c (update x i z) = κ i).card =
      Multiset.count κ ((Finset.univ : Finset (Fin n)).val.map (kcrVec c x)) := by
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  refine Multiset.filter_congr fun z _ => ?_
  simp only [kcrVec, funext_iff]
  exact ⟨fun h i => (h i).symm, fun h i => (h i).symm⟩

theorem kcr_isCoherent_of_stable {c : (Fin k → Fin n) → ℕ} (hc : KcrStable c) :
    GI.Cited.IsCoherent c := by
  intro x y hxy κ
  rw [kcr_card_filter_eq_count, kcr_card_filter_eq_count]
  exact congrArg (Multiset.count κ) (congrArg (fun d => d.2.2.2)
    (kcrData_eq_of_round_eq (hc x y hxy)))

/-! ### Stability is reached after `n^k + 1` rounds -/

/-- A round refines: equal new colors give equal old colors. -/
theorem kcrRound_refines {c : (Fin k → Fin n) → ℕ} {x y : Fin k → Fin n}
    (h : kcrRound c x = kcrRound c y) : c x = c y :=
  congrArg Prod.fst (kcrData_eq_of_round_eq h)

/-- Stability persists. If `c` is stable, then `kcrRound c` is a function `g` of `c`, so every
piece of the round data of `kcrRound c` is `g` applied to the round data of `c`. -/
theorem kcrStable_round {c : (Fin k → Fin n) → ℕ} (hc : KcrStable c) :
    KcrStable (kcrRound c) := by
  classical
  let g : ℕ → ℕ := fun a => if h : ∃ u, c u = a then kcrRound c h.choose else 0
  have hg : ∀ u, kcrRound c u = g (c u) := by
    intro u
    have h : ∃ v, c v = c u := ⟨u, rfl⟩
    simp only [g, dif_pos h]
    exact hc _ _ h.choose_spec.symm
  intro x y hxy
  have hd := kcrData_eq_of_round_eq hxy
  simp only [kcrData, Prod.mk.injEq] at hd
  obtain ⟨h1, h2, h3, h4⟩ := hd
  have hv : ∀ u, kcrVec (kcrRound c) u = (g ∘ ·) ∘ kcrVec c u := by
    intro u; funext z i; simp [kcrVec, hg]
  simp only [kcrRound, kcrData]
  congr 1
  refine Prod.ext hxy (Prod.ext h2 (Prod.ext ?_ ?_))
  · funext τ
    exact hc _ _ (congrFun h3 τ)
  · dsimp only
    rw [hv, hv, ← Multiset.map_map, ← Multiset.map_map, h4]

/-- The number of color classes. -/
def kcrClasses (c : (Fin k → Fin n) → ℕ) : ℕ :=
  (Finset.univ.image c).card

theorem kcrClasses_le (c : (Fin k → Fin n) → ℕ) :
    kcrClasses c ≤ Fintype.card (Fin k → Fin n) :=
  Finset.card_image_le.trans (le_of_eq Finset.card_univ)

/-- A round on an unstable coloring adds a color class. Since a round refines, the old
coloring is a function `h` of the new one, and `h` merges two distinct new colors. -/
theorem kcrClasses_lt {c : (Fin k → Fin n) → ℕ} (hc : ¬ KcrStable c) :
    kcrClasses c < kcrClasses (kcrRound c) := by
  classical
  simp only [KcrStable, not_forall] at hc
  obtain ⟨x, y, hxy, hne⟩ := hc
  let h : ℕ → ℕ := fun b => if hb : ∃ u, kcrRound c u = b then c hb.choose else 0
  have hh : ∀ u, c u = h (kcrRound c u) := by
    intro u
    have hb : ∃ v, kcrRound c v = kcrRound c u := ⟨u, rfl⟩
    simp only [h, dif_pos hb]
    exact kcrRound_refines hb.choose_spec.symm
  have himg : Finset.univ.image c = (Finset.univ.image (kcrRound c)).image h := by
    rw [Finset.image_image]
    exact Finset.image_congr fun u _ => hh u
  unfold kcrClasses
  rw [himg]
  refine lt_of_le_of_ne Finset.card_image_le fun heq => hne ?_
  have hinj := Finset.card_image_iff.mp heq
  exact hinj (by simp) (by simp) (by rw [← hh, ← hh, hxy])

theorem kcrIter_stable_or (c : (Fin k → Fin n) → ℕ) (m : ℕ) :
    KcrStable (kcrRound^[m] c) ∨ m ≤ kcrClasses (kcrRound^[m] c) := by
  induction m with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ m ih =>
    rw [iterate_succ_apply']
    by_cases hs : KcrStable (kcrRound^[m] c)
    · exact Or.inl (kcrStable_round hs)
    · exact Or.inr ((ih.resolve_left hs).trans_lt (kcrClasses_lt hs))

theorem kcrIter_stable (c : (Fin k → Fin n) → ℕ) :
    KcrStable (kcrRound^[Fintype.card (Fin k → Fin n) + 1] c) := by
  refine (kcrIter_stable_or c _).resolve_right fun h => ?_
  exact absurd (h.trans (kcrClasses_le _)) (Nat.not_succ_le_self _)

/-! ### The theorem -/

/-- **Canonical `k`-ary coherent refinement** ([H, Sections 2.3–2.5]): `k`-ary Weisfeiler–Leman
run for `n^k + 1` rounds. -/
theorem karyCoherentRefinement : GI.Cited.KaryCoherentRefinement := by
  intro n k
  refine ⟨fun c => kcrRound^[Fintype.card (Fin k → Fin n) + 1] c,
    fun c => ⟨kcr_isConfiguration_of_stable (kcrIter_stable c),
      kcr_isCoherent_of_stable (kcrIter_stable c)⟩,
    fun c c' x y h => kcrIter_color _ c c' x y h,
    fun c σ => kcrIter_act σ c _⟩

end GI.Proved
