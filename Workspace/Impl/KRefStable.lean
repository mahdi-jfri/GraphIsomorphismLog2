module

public import Workspace.Impl.KRefRef

@[expose] public section

/-!
# After `2 n^k` rounds the colorings are a correct output

`kref_joint`: the colorings `d, d'` after `2 n^k` rounds (`krefIter`) are coherent
configurations that refine `c, c'` with one palette, have colors below `2 n^k`, and are carried
along by every relabeling that carries the inputs. This is `JointRefinement` of
`Workspace/Cited/AlgoRefinement.lean` together with the bounds of `KaryRefinementTask`.

*Why `2 n^k` rounds suffice.* Each round refines the joint partition of the `2 n^k` tuples of
both inputs into color classes (the signature contains the old color). By `krefStep_eq_iff` and
`krefRef_congr`, the partition after a round depends only on the partition before it, so a
round that does not split a class is followed only by such rounds. A round that splits a class
adds a class, and there are at most `2 n^k` classes. So round `2 n^k` splits nothing: the
coloring is stable, and stability is what makes it a coherent configuration.
-/

namespace GI.Impl

open GI.Cited Equiv

variable {n k : ℕ}

/-! ### Counting classes -/

/-- If `g` is finer than `f`, it has at least as many values, and more if it is strictly finer. -/
theorem kref_card_image {α : Type} [Fintype α] [DecidableEq α] (f g : α → ℕ)
    (hfine : ∀ a b, g a = g b → f a = f b) :
    (Finset.univ.image f).card ≤ (Finset.univ.image g).card ∧
      ((∃ a b, f a = f b ∧ g a ≠ g b) →
        (Finset.univ.image f).card < (Finset.univ.image g).card) := by
  classical
  let φ : ℕ → ℕ := fun v => if h : ∃ a, g a = v then f h.choose else 0
  have hφ : ∀ a, φ (g a) = f a := by
    intro a
    have h : ∃ a', g a' = g a := ⟨a, rfl⟩
    simp only [φ, dif_pos h]
    exact hfine _ _ h.choose_spec
  have himg : Finset.univ.image f = (Finset.univ.image g).image φ := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨g a, ⟨a, rfl⟩, hφ a⟩
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (hφ a).symm⟩
  rw [himg]
  refine ⟨Finset.card_image_le, ?_⟩
  rintro ⟨a, b, hab, hg⟩
  refine lt_of_le_of_ne Finset.card_image_le fun h => hg ?_
  have hinj := Finset.card_image_iff.mp h
  refine hinj (by simp) (by simp) ?_
  rw [hφ, hφ, hab]

/-- The number of colors of a joint coloring. -/
def krefCls (col : KCol n k) : ℕ :=
  (Finset.univ.image fun a : Bool × (Fin k → Fin n) => col a.1 a.2).card

theorem krefCls_le (col : KCol n k) : krefCls col ≤ 2 * n ^ k := by
  unfold krefCls
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]

/-! ### The rounds -/

section Iter

variable (c c' : (Fin k → Fin n) → ℕ)

theorem krefIter_small (hc : ∀ x, c x ≤ n ^ k) (hc' : ∀ x, c' x ≤ n ^ k) :
    ∀ t, KrefSmall (krefIter c c' t)
  | 0 => fun β x => by
    cases β
    · have := hc x; simp only [krefIter, krefJoin]; simp; omega
    · have := hc' x; simp only [krefIter, krefJoin]; simp; omega
  | t + 1 => fun β x => (krefStep_lt (col := krefIter c c' t) β x).le

variable {c c'} (hc : ∀ x, c x ≤ n ^ k) (hc' : ∀ x, c' x ≤ n ^ k)
include hc hc'

/-- Round `t + 1` refines round `t`. -/
theorem krefIter_refines (t : ℕ) (a b : Bool × (Fin k → Fin n))
    (h : krefIter c c' (t + 1) a.1 a.2 = krefIter c c' (t + 1) b.1 b.2) :
    krefIter c c' t a.1 a.2 = krefIter c c' t b.1 b.2 :=
  ((krefStep_eq_iff (krefIter_small c c' hc hc' t) a.1 b.1 a.2 b.2).mp h).1

/-- Round `t` refines the input. -/
theorem krefIter_refines_zero (t : ℕ) (a b : Bool × (Fin k → Fin n))
    (h : krefIter c c' t a.1 a.2 = krefIter c c' t b.1 b.2) :
    krefJoin c c' a.1 a.2 = krefJoin c c' b.1 b.2 := by
  induction t with
  | zero => exact h
  | succ t ih => exact ih (krefIter_refines hc hc' t a b h)

/-- Round `t + 1` makes the same color classes as round `t`. -/
def KrefStableAt (c c' : (Fin k → Fin n) → ℕ) (t : ℕ) : Prop :=
  ∀ a b : Bool × (Fin k → Fin n),
    krefIter c c' (t + 1) a.1 a.2 = krefIter c c' (t + 1) b.1 b.2 ↔
      krefIter c c' t a.1 a.2 = krefIter c c' t b.1 b.2

/-- A round that splits no class is followed by another one. -/
theorem krefStableAt_succ {t : ℕ} (h : KrefStableAt c c' t) : KrefStableAt c c' (t + 1) := by
  intro a b
  rw [show krefIter c c' (t + 1 + 1) = krefStep (krefIter c c' (t + 1)) from rfl,
    krefStep_eq_iff (krefIter_small c c' hc hc' (t + 1)), krefRef_congr h,
    ← krefStep_eq_iff (krefIter_small c c' hc hc' t)]
  rfl

theorem krefStableAt_add {t : ℕ} (h : KrefStableAt c c' t) (s : ℕ) :
    KrefStableAt c c' (t + s) := by
  induction s with
  | zero => exact h
  | succ s ih => exact krefStableAt_succ hc hc' ih

/-- A round that splits a class adds a class. -/
theorem krefCls_lt {t : ℕ} (h : ¬ KrefStableAt c c' t) :
    krefCls (krefIter c c' t) < krefCls (krefIter c c' (t + 1)) := by
  refine (kref_card_image (fun a : Bool × (Fin k → Fin n) => krefIter c c' t a.1 a.2)
    (fun a => krefIter c c' (t + 1) a.1 a.2) (krefIter_refines hc hc' t)).2 ?_
  by_contra hne
  push Not at hne
  exact h fun a b => ⟨krefIter_refines hc hc' t a b, hne a b⟩

/-- **Round `2 n^k` splits no class.** -/
theorem krefIter_stable : KrefStableAt c c' (2 * n ^ k) := by
  by_contra hR
  have hall : ∀ t, t ≤ 2 * n ^ k → ¬ KrefStableAt c c' t := fun t ht hs => hR (by
    have := krefStableAt_add hc hc' hs (2 * n ^ k - t)
    rwa [Nat.add_sub_cancel' ht] at this)
  have hgrow : ∀ t, t ≤ 2 * n ^ k + 1 → t ≤ krefCls (krefIter c c' t) := by
    intro t ht
    induction t with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      have := krefCls_lt hc hc' (hall t (by omega))
      have := ih (by omega)
      omega
  have h1 := hgrow (2 * n ^ k + 1) le_rfl
  have h2 := krefCls_le (krefIter c c' (2 * n ^ k + 1))
  omega

/-- The stable round compares tuples by `KrefRef`. -/
theorem krefIter_ref (a b : Bool × (Fin k → Fin n))
    (h : krefIter c c' (2 * n ^ k) a.1 a.2 = krefIter c c' (2 * n ^ k) b.1 b.2) :
    KrefRef (krefIter c c' (2 * n ^ k)) a b :=
  (krefStep_eq_iff (krefIter_small c c' hc hc' _) a.1 b.1 a.2 b.2).mp
    ((krefIter_stable hc hc' a b).mpr h)

end Iter

/-! ### Relabelings -/

theorem krefPat_comp (σ : Perm (Fin n)) (x : Fin k → Fin n) : krefPat (σ ∘ x) = krefPat x :=
  (krefPat_eq_iff _ _).mpr fun _ _ => σ.injective.eq_iff

/-- A relabeling that carries input `a` to input `b` before a round does so after it. -/
theorem krefStep_carry {col : KCol n k} {σ : Perm (Fin n)} {a b : Bool}
    (h : ∀ x, col b (σ ∘ x) = col a x) (x : Fin k → Fin n) :
    krefStep col b (σ ∘ x) = krefStep col a x := by
  have hupd : ∀ (y : Fin k → Fin n) i z,
      Function.update (σ ∘ y) i z = σ ∘ Function.update y i (σ.symm z) := by
    intro y i z
    rw [Function.comp_update, Equiv.apply_symm_apply]
  have hvec : ∀ z, krefVec col b (σ ∘ x) z = krefVec col a x (σ.symm z) := by
    intro z
    unfold krefVec
    congr 1
    funext i
    rw [hupd, h]
  have hcnt : krefCounts col b (σ ∘ x) = krefCounts col a x := by
    rw [krefCounts_eq_iff, krefRl, krefRl, kref_count_eq_iff]
    exact ⟨σ.symm, fun z => by rw [hvec]⟩
  have htau : krefTauCols col b (σ ∘ x) = krefTauCols col a x := by
    unfold krefTauCols
    exact List.map_congr_left fun τ _ => h (x ∘ τ)
  unfold krefStep krefSig
  rw [h x, krefPat_comp, htau, hcnt]

theorem krefIter_carry {c c' : (Fin k → Fin n) → ℕ} {σ : Perm (Fin n)} {a b : Bool}
    (h : ∀ x, krefJoin c c' b (σ ∘ x) = krefJoin c c' a x) :
    ∀ t x, krefIter c c' t b (σ ∘ x) = krefIter c c' t a x
  | 0 => h
  | t + 1 => krefStep_carry (krefIter_carry h t)

/-! ### The result -/

/-- Tuples with the same color in the stable round have the same counts. -/
theorem kref_coherent_of {col : KCol n k} {β : Bool} {x y : Fin k → Fin n}
    (h : KrefRef col (β, x) (β, y)) (κ : Fin k → ℕ) :
    (Finset.univ.filter fun z : Fin n => ∀ i, col β (Function.update x i z) = κ i).card =
      (Finset.univ.filter fun z : Fin n => ∀ i, col β (Function.update y i z) = κ i).card := by
  obtain ⟨π, hπ⟩ := h.2.2.2
  refine Finset.card_equiv π fun z => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact forall_congr' fun i => by rw [hπ z i]

theorem kref_config_of {col : KCol n k} {β : Bool}
    (h : ∀ x y, col β x = col β y → KrefRef col (β, x) (β, y)) :
    IsConfiguration (col β) ∧ IsCoherent (col β) :=
  ⟨⟨fun x y hxy => (h x y hxy).2.1, fun x y hxy => (h x y hxy).2.2.1⟩,
    fun x y hxy => kref_coherent_of (h x y hxy)⟩

/-- **The joint refinement.** -/
theorem kref_joint (c c' : (Fin k → Fin n) → ℕ) (hc : ∀ x, c x ≤ n ^ k)
    (hc' : ∀ x, c' x ≤ n ^ k) :
    (∀ x, krefIter c c' (2 * n ^ k) false x < 2 * n ^ k) ∧
      (∀ x, krefIter c c' (2 * n ^ k) true x < 2 * n ^ k) ∧
      JointRefinement c c' (krefIter c c' (2 * n ^ k) false) (krefIter c c' (2 * n ^ k) true) := by
  have hlt : ∀ β x, krefIter c c' (2 * n ^ k) β x < 2 * n ^ k := by
    intro β x
    have hpos : 0 < n ^ k := (finFunctionFinEquiv x).pos
    obtain ⟨t, ht⟩ : ∃ t, 2 * n ^ k = t + 1 := ⟨2 * n ^ k - 1, by omega⟩
    rw [ht]
    exact (krefStep_lt (col := krefIter c c' t) β x).trans_le (by omega)
  have href := krefIter_ref hc hc'
  have hz := krefIter_refines_zero hc hc' (2 * n ^ k)
  refine ⟨hlt false, hlt true, ?_⟩
  obtain ⟨h1, h2⟩ := kref_config_of (β := false) fun x y h => href (false, x) (false, y) h
  obtain ⟨h3, h4⟩ := kref_config_of (β := true) fun x y h => href (true, x) (true, y) h
  refine ⟨h1, h2, h3, h4, fun x y h => hz (false, x) (false, y) h,
    fun x y h => hz (true, x) (true, y) h, fun x y h => hz (false, x) (true, y) h,
    fun σ => ⟨fun hσ x => ?_, fun hσ x => ?_, fun hσ x => ?_⟩⟩
  · exact krefIter_carry (c := c) (c' := c') (a := false) (b := true) hσ _ x
  · exact krefIter_carry (c := c) (c' := c') (a := false) (b := false) hσ _ x
  · exact krefIter_carry (c := c) (c' := c') (a := true) (b := true) hσ _ x

end GI.Impl
