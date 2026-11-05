module

public import Workspace.Cited.AlgoPermGroups
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# A minimal block system, the mathematics

The algorithm of Luks (*Permutation groups and polynomial-time computation*, DIMACS 11 (1993),
item (3.2), p. 143), iterated as in [H, Section 2.1.2] ("By iterating the procedure, we will
obtain a system of minimal blocks in polynomial time"). This is Atkinson's method.

A partition of the points is kept as a map `lab : Fin n → Fin n` that sends each point to a
chosen point of its class (`MRepr`: `lab (lab x) = lab x`).

* `mblkMerge lab u v` joins the classes of `u` and `v`.
* `mblkClos gs lab` is the finest partition that is coarser than `lab` and invariant under the
  generators `gs`: as long as some `x` has `g x` and `g (lab x)` in different classes, join
  them. One round goes once over all generators and points (`mblkRound`); `n` rounds suffice.
* `mblkResult gs z` starts from the partition into points. One outer round goes over the points
  `b`; it replaces `lab` by the closure of `lab` with the classes of `z` and `b` joined, when this
  closure still has at least two classes. `n` outer rounds suffice.

Every step either keeps `lab` or lowers the number of classes `mblkPot lab` (`MLe`). So after
`n` rounds a round changes nothing. The main result is `mblkResult_spec`: for a transitive group
on at least two points, `mblkResult` is a minimal block system.
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n : ℕ}

/-! ### Partitions by representatives -/

/-- Every point is sent to a point of its class, and that point to itself. -/
def MRepr (lab : Fin n → Fin n) : Prop := ∀ x, lab (lab x) = lab x

/-- The number of classes: the number of points that are their own representative. -/
def mblkPot (lab : Fin n → Fin n) : ℕ := (Finset.univ.filter fun x => lab x = x).card

/-- `lab'` is `lab`, or has fewer classes. -/
def MLe (lab lab' : Fin n → Fin n) : Prop :=
  mblkPot lab' ≤ mblkPot lab ∧ (mblkPot lab' = mblkPot lab → lab' = lab)

/-- `lab'` is coarser than `lab`. -/
def MFiner {β γ : Type} (lab : Fin n → β) (lab' : Fin n → γ) : Prop :=
  ∀ x y, lab x = lab y → lab' x = lab' y

theorem MLe.refl (lab : Fin n → Fin n) : MLe lab lab := ⟨le_rfl, fun _ => rfl⟩

theorem MLe.trans {a b c : Fin n → Fin n} (h1 : MLe a b) (h2 : MLe b c) : MLe a c := by
  refine ⟨h2.1.trans h1.1, fun h => ?_⟩
  have e1 : mblkPot b = mblkPot a := le_antisymm h1.1 (h ▸ h2.1)
  have e2 : mblkPot c = mblkPot b := e1 ▸ h
  rw [h2.2 e2, h1.2 e1]

theorem MFiner.trans {β γ δ : Type} {a : Fin n → β} {b : Fin n → γ} {c : Fin n → δ}
    (h1 : MFiner a b) (h2 : MFiner b c) : MFiner a c :=
  fun x y h => h2 x y (h1 x y h)

theorem mblkPot_le (lab : Fin n → Fin n) : mblkPot lab ≤ n := by
  unfold mblkPot
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem one_le_mblkPot {lab : Fin n → Fin n} (h : MRepr lab) (z : Fin n) : 1 ≤ mblkPot lab :=
  Finset.card_pos.mpr ⟨lab z, by simp [h z]⟩

/-! ### Joining two classes -/

/-- Join the classes of `u` and `v`: the class of `v` gets the representative of `u`. -/
def mblkMerge (lab : Fin n → Fin n) (u v : Fin n) : Fin n → Fin n :=
  fun x => if lab x = lab v then lab u else lab x

theorem mblkMerge_repr {lab : Fin n → Fin n} (h : MRepr lab) (u v : Fin n) :
    MRepr (mblkMerge lab u v) := by
  intro x
  unfold mblkMerge
  by_cases hx : lab x = lab v
  · rw [if_pos hx, h u]; split <;> rfl
  · rw [if_neg hx, h x, if_neg hx]

theorem mblkMerge_eq_of {lab : Fin n → Fin n} {u v : Fin n} (huv : lab u = lab v) :
    mblkMerge lab u v = lab := by
  funext x
  unfold mblkMerge
  by_cases hx : lab x = lab v
  · rw [if_pos hx, hx, huv]
  · rw [if_neg hx]

theorem mblkMerge_le {lab : Fin n → Fin n} (h : MRepr lab) (u v : Fin n) :
    MLe lab (mblkMerge lab u v) := by
  by_cases huv : lab u = lab v
  · rw [mblkMerge_eq_of huv]; exact MLe.refl _
  -- the fixed points of the merge are fixed points of `lab`, without `lab v`
  have hsub : (Finset.univ.filter fun x => mblkMerge lab u v x = x) ⊂
      Finset.univ.filter fun x => lab x = x := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨lab v, by simp [h v], ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [mblkMerge, h v, if_pos]
      exact huv
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simp only [mblkMerge] at hx
      by_cases hxv : lab x = lab v
      · rw [if_pos hxv] at hx
        exact absurd (by rw [← hxv, ← hx, h u]) huv
      · rwa [if_neg hxv] at hx
  have := Finset.card_lt_card hsub
  exact ⟨this.le, fun he => absurd he (by unfold mblkPot; omega)⟩

theorem mblkMerge_finer (lab : Fin n → Fin n) (u v : Fin n) : MFiner lab (mblkMerge lab u v) := by
  intro x y h
  simp only [mblkMerge, h]

theorem mblkMerge_join (lab : Fin n → Fin n) (u v : Fin n) :
    mblkMerge lab u v u = mblkMerge lab u v v := by
  simp only [mblkMerge]
  by_cases h : lab u = lab v <;> simp [h]

/-- The merge is finer than every coarser partition that joins `u` and `v`. -/
theorem mblkMerge_below {γ : Type} {lab : Fin n → Fin n} {L : Fin n → γ} (hL : MFiner lab L)
    {u v : Fin n} (huv : L u = L v) : MFiner (mblkMerge lab u v) L := by
  intro x y h
  simp only [mblkMerge] at h
  by_cases hx : lab x = lab v <;> by_cases hy : lab y = lab v <;>
    simp only [hx, hy, if_true, if_false] at h
  · rw [hL x v hx, hL y v hy]
  · rw [hL x v hx, ← huv, hL u y h]
  · rw [hL x u h, huv, hL y v hy]
  · exact hL x y h

theorem mblkMerge_eq_self {lab : Fin n → Fin n} {u v : Fin n} (h : mblkMerge lab u v = lab) :
    lab u = lab v := by
  have := congrFun h v
  simp only [mblkMerge, if_true] at this
  exact this

/-! ### Folds and iterations of steps that keep or coarsen -/

theorem mblk_foldl_inv {α : Type} {Q : (Fin n → Fin n) → Prop} (f : (Fin n → Fin n) → α → Fin n → Fin n)
    (l : List α) (hf : ∀ lab, ∀ a ∈ l, Q lab → Q (f lab a)) (lab : Fin n → Fin n) (h : Q lab) :
    Q (l.foldl f lab) := by
  induction l generalizing lab with
  | nil => exact h
  | cons a l ih =>
    exact ih (fun lab b hb => hf lab b (List.mem_cons_of_mem _ hb)) _ (hf lab a (by simp) h)

/-- A step that keeps a partition by representatives, and keeps it or lowers its classes. -/
def MStep {α : Type} (f : (Fin n → Fin n) → α → Fin n → Fin n) : Prop :=
  ∀ lab a, MRepr lab → MRepr (f lab a) ∧ MLe lab (f lab a)

theorem MStep.foldl {α : Type} {f : (Fin n → Fin n) → α → Fin n → Fin n} (hf : MStep f)
    (l : List α) (lab : Fin n → Fin n) (h : MRepr lab) :
    MRepr (l.foldl f lab) ∧ MLe lab (l.foldl f lab) := by
  induction l generalizing lab with
  | nil => exact ⟨h, MLe.refl _⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := hf lab a h
    obtain ⟨h3, h4⟩ := ih _ h1
    exact ⟨h3, h2.trans h4⟩

/-- If a fold of such steps changes nothing, then no step changes anything. -/
theorem MStep.foldl_fixed {α : Type} {f : (Fin n → Fin n) → α → Fin n → Fin n} (hf : MStep f)
    (l : List α) (lab : Fin n → Fin n) (h : MRepr lab) (hfix : l.foldl f lab = lab) :
    ∀ a ∈ l, f lab a = lab := by
  induction l generalizing lab with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := hf lab a h
    obtain ⟨-, h4⟩ := hf.foldl l _ h1
    rw [List.foldl_cons] at hfix
    rw [hfix] at h4
    have e : f lab a = lab := h2.2 (le_antisymm h2.1 h4.1)
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact e
    · rw [e] at hfix
      exact ih lab h hfix b hb

/-- After `n` rounds of such a map, a round changes nothing. -/
theorem mblk_iterate_fixed {F : (Fin n → Fin n) → Fin n → Fin n}
    (hF : ∀ lab, MRepr lab → MRepr (F lab) ∧ MLe lab (F lab)) (z : Fin n) (lab : Fin n → Fin n)
    (h : MRepr lab) : F (F^[n] lab) = F^[n] lab := by
  have key : ∀ k, MRepr (F^[k] lab) ∧
      (F (F^[k] lab) = F^[k] lab ∨ mblkPot (F^[k] lab) + k ≤ mblkPot lab) := by
    intro k
    induction k with
    | zero => exact ⟨h, Or.inr (by simp)⟩
    | succ k ih =>
      obtain ⟨hr, hk⟩ := ih
      rw [Function.iterate_succ_apply']
      obtain ⟨hr', hle⟩ := hF _ hr
      refine ⟨hr', ?_⟩
      rcases hk with hk | hk
      · left; rw [hk, hk]
      · by_cases he : mblkPot (F (F^[k] lab)) = mblkPot (F^[k] lab)
        · left; rw [hle.2 he, hle.2 he]
        · right; have := hle.1; omega
  obtain ⟨hr, hk⟩ := key n
  rcases hk with hk | hk
  · exact hk
  · have h1 := one_le_mblkPot hr z
    have h2 := mblkPot_le lab
    omega

theorem mblk_iterate_inv {F : (Fin n → Fin n) → Fin n → Fin n} {Q : (Fin n → Fin n) → Prop}
    (hF : ∀ lab, Q lab → Q (F lab)) (k : ℕ) (lab : Fin n → Fin n) (h : Q lab) : Q (F^[k] lab) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact hF _ ih

theorem mblk_iterate_le {F : (Fin n → Fin n) → Fin n → Fin n}
    (hF : ∀ lab, MRepr lab → MRepr (F lab) ∧ MLe lab (F lab)) (k : ℕ) (lab : Fin n → Fin n)
    (h : MRepr lab) : MRepr (F^[k] lab) ∧ MLe lab (F^[k] lab) := by
  induction k with
  | zero => exact ⟨h, MLe.refl _⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := hF _ ih.1
    exact ⟨h1, ih.2.trans h2⟩

/-! ### The closure under the generators -/

/-- One point step for the generator `g`: join the classes of `g x` and `g (lab x)`. -/
def mblkPt (g : Perm (Fin n)) (lab : Fin n → Fin n) (x : Fin n) : Fin n → Fin n :=
  mblkMerge lab (g x) (g (lab x))

/-- The point steps of `g`, for all points in order. -/
def mblkGen (lab : Fin n → Fin n) (g : Perm (Fin n)) : Fin n → Fin n :=
  (List.finRange n).foldl (mblkPt g) lab

/-- One round: `mblkGen` for all generators in order. -/
def mblkRound (gs : List (Perm (Fin n))) (lab : Fin n → Fin n) : Fin n → Fin n :=
  gs.foldl mblkGen lab

/-- The closure: `n` rounds. -/
def mblkClos (gs : List (Perm (Fin n))) (lab : Fin n → Fin n) : Fin n → Fin n :=
  (mblkRound gs)^[n] lab

theorem mblkPt_step (g : Perm (Fin n)) : MStep (mblkPt g) :=
  fun lab x h => ⟨mblkMerge_repr h _ _, mblkMerge_le h _ _⟩

theorem mblkGen_step : MStep (mblkGen (n := n)) :=
  fun lab g h => (mblkPt_step g).foldl _ lab h

theorem mblkRound_le (gs : List (Perm (Fin n))) (lab : Fin n → Fin n) (h : MRepr lab) :
    MRepr (mblkRound gs lab) ∧ MLe lab (mblkRound gs lab) :=
  mblkGen_step.foldl gs lab h

theorem mblkClos_le (gs : List (Perm (Fin n))) (lab : Fin n → Fin n) (h : MRepr lab) :
    MRepr (mblkClos gs lab) ∧ MLe lab (mblkClos gs lab) :=
  mblk_iterate_le (mblkRound_le gs) n lab h

theorem mblkClos_finer (gs : List (Perm (Fin n))) (lab : Fin n → Fin n) :
    MFiner lab (mblkClos gs lab) := by
  have hpt : ∀ g : Perm (Fin n), ∀ (l : Fin n → Fin n) x, MFiner l (mblkPt g l x) :=
    fun g l x => mblkMerge_finer _ _ _
  have hgen : ∀ (l : Fin n → Fin n) (g : Perm (Fin n)), MFiner l (mblkGen l g) := fun l g =>
    mblk_foldl_inv (Q := fun l' => MFiner l l') _ _ (fun l' x _ h => h.trans (hpt g l' x)) l
      (fun _ _ h => h)
  have hround : ∀ l : Fin n → Fin n, MFiner l (mblkRound gs l) := fun l =>
    mblk_foldl_inv (Q := fun l' => MFiner l l') _ _ (fun l' g _ h => h.trans (hgen l' g)) l
      (fun _ _ h => h)
  exact mblk_iterate_inv (Q := fun l' => MFiner lab l') (fun l' h => h.trans (hround l')) n lab
    (fun _ _ h => h)

/-- Invariance of a labeling under a generator, in the one-directional form. -/
def MInvGen {γ : Type} (gs : List (Perm (Fin n))) (L : Fin n → γ) : Prop :=
  ∀ g ∈ gs, ∀ x y, L x = L y → L (g x) = L (g y)

/-- The closure is finer than every coarser invariant labeling. -/
theorem mblkClos_below {γ : Type} {gs : List (Perm (Fin n))} {lab : Fin n → Fin n}
    {L : Fin n → γ} (h : MRepr lab) (hL : MFiner lab L) (hinv : MInvGen gs L) :
    MFiner (mblkClos gs lab) L := by
  have Q : ∀ l : Fin n → Fin n, MRepr l ∧ MFiner l L → MRepr (mblkRound gs l) ∧
      MFiner (mblkRound gs l) L := by
    intro l hl
    refine ⟨(mblkRound_le gs l hl.1).1, ?_⟩
    refine (mblk_foldl_inv (Q := fun l' => MRepr l' ∧ MFiner l' L) mblkGen gs ?_ l hl).2
    intro l' g hg hl'
    refine mblk_foldl_inv (Q := fun l' => MRepr l' ∧ MFiner l' L) (mblkPt g) _ ?_ l' hl'
    intro l'' x _ hl''
    refine ⟨mblkMerge_repr hl''.1 _ _, mblkMerge_below hl''.2 ?_⟩
    exact hinv g hg _ _ (hl''.2 _ _ (hl''.1 x).symm)
  exact (mblk_iterate_inv (Q := fun l => MRepr l ∧ MFiner l L) Q n lab ⟨h, hL⟩).2

/-- The closure is invariant under the generators. -/
theorem mblkClos_inv (gs : List (Perm (Fin n))) {lab : Fin n → Fin n} (h : MRepr lab)
    (z : Fin n) : MInvGen gs (mblkClos gs lab) := by
  set c := mblkClos gs lab
  have hr : MRepr c := (mblkClos_le gs lab h).1
  have hfix : mblkRound gs c = c := mblk_iterate_fixed (mblkRound_le gs) z lab h
  have hg := mblkGen_step.foldl_fixed gs c hr hfix
  have stab : ∀ g ∈ gs, ∀ x, c (g x) = c (g (c x)) := by
    intro g hgs x
    have := (mblkPt_step g).foldl_fixed _ c hr (hg g hgs) x (List.mem_finRange x)
    exact mblkMerge_eq_self this
  intro g hgs x y hxy
  rw [stab g hgs x, stab g hgs y, hxy]

/-! ### Invariance under the generated group -/

theorem mblk_invariant {gs : List (Perm (Fin n))} {L : Fin n → ℕ} (h : MInvGen gs L) :
    InvariantLabeling (gens gs) L := by
  let T : Submonoid (Perm (Fin n)) :=
    { carrier := {g | ∀ x y, L x = L y → L (g x) = L (g y)}
      one_mem' := fun x y h => h
      mul_mem' := fun ha hb x y h => ha _ _ (hb _ _ h) }
  have hT : ∀ g ∈ gens gs, g ∈ T := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => g ∈ T) (fun x hx => h x hx)
      T.one_mem (fun x y _ _ hx hy => T.mul_mem hx hy) (fun x _ hx => ?_) hg
    have e : x ^ (orderOf x - 1) = x⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    show x⁻¹ ∈ T
    rw [← e]
    exact T.pow_mem hx _
  intro g hg i j
  refine ⟨fun hij => ?_, hT g hg i j⟩
  have := hT g⁻¹ (Subgroup.inv_mem _ hg) _ _ hij
  simpa using this

/-! ### The outer rounds -/

/-- The closure of `lab` with the classes of `z` and `b` joined. -/
def mblkTry (gs : List (Perm (Fin n))) (z : Fin n) (lab : Fin n → Fin n) (b : Fin n) :
    Fin n → Fin n :=
  mblkClos gs (mblkMerge lab z b)

/-- One outer step: take the closure if it still has at least two classes. -/
def mblkOuterStep (gs : List (Perm (Fin n))) (z : Fin n) (lab : Fin n → Fin n) (b : Fin n) :
    Fin n → Fin n :=
  if ∃ x, mblkTry gs z lab b x ≠ mblkTry gs z lab b z then mblkTry gs z lab b else lab

/-- One outer round: the outer steps for all points in order. -/
def mblkOuterRound (gs : List (Perm (Fin n))) (z : Fin n) (lab : Fin n → Fin n) : Fin n → Fin n :=
  (List.finRange n).foldl (mblkOuterStep gs z) lab

/-- The result: `n` outer rounds from the partition into points. -/
def mblkResult (gs : List (Perm (Fin n))) (z : Fin n) : Fin n → Fin n :=
  (mblkOuterRound gs z)^[n] id

theorem mblkOuterStep_step (gs : List (Perm (Fin n))) (z : Fin n) : MStep (mblkOuterStep gs z) := by
  intro lab b h
  unfold mblkOuterStep
  split_ifs
  · obtain ⟨h1, h2⟩ := mblkClos_le gs _ (mblkMerge_repr h z b)
    exact ⟨h1, (mblkMerge_le h z b).trans h2⟩
  · exact ⟨h, MLe.refl _⟩

/-- What the outer steps keep: representatives, invariance, and two classes. -/
def MGood (gs : List (Perm (Fin n))) (z : Fin n) (lab : Fin n → Fin n) : Prop :=
  MRepr lab ∧ MInvGen gs lab ∧ ∃ x, lab x ≠ lab z

theorem mblkOuterStep_good {gs : List (Perm (Fin n))} {z : Fin n} {lab : Fin n → Fin n}
    (h : MGood gs z lab) (b : Fin n) : MGood gs z (mblkOuterStep gs z lab b) := by
  unfold mblkOuterStep
  split_ifs with hs
  · exact ⟨(mblkClos_le gs _ (mblkMerge_repr h.1 z b)).1,
      mblkClos_inv gs (mblkMerge_repr h.1 z b) z, hs⟩
  · exact h

theorem mblkResult_good {gs : List (Perm (Fin n))} {z : Fin n} (h2 : ∃ x, x ≠ z) :
    MGood gs z (mblkResult gs z) := by
  refine mblk_iterate_inv (Q := MGood gs z) (fun lab h => mblk_foldl_inv (Q := MGood gs z) (mblkOuterStep gs z)
    (List.finRange n) (fun l b _ hl => mblkOuterStep_good hl b) lab h) n id
    ⟨fun _ => rfl, fun g _ x y h => by simp only [id] at h ⊢; rw [h], h2⟩

theorem mblkResult_fixed (gs : List (Perm (Fin n))) (z : Fin n) :
    mblkOuterRound gs z (mblkResult gs z) = mblkResult gs z :=
  mblk_iterate_fixed (fun lab h => (mblkOuterStep_step gs z).foldl _ lab h) z id fun _ => rfl

/-- **The result is a minimal block system.** -/
theorem mblkResult_spec (gs : List (Perm (Fin n))) (z : Fin n) (h2 : ∃ x, x ≠ z)
    (htr : ∀ i j : Fin n, ∃ g ∈ gens gs, g i = j) :
    IsMinimalBlocks (gens gs) (fun x => (mblkResult gs z x : ℕ)) := by
  set R := mblkResult gs z with hR
  obtain ⟨hr, hinv, hsplit⟩ := mblkResult_good (gs := gs) h2
  have hinvR : MInvGen gs (fun x => (R x : ℕ)) := fun g hg x y h =>
    congrArg Fin.val (hinv g hg x y (Fin.ext h))
  have hInv := mblk_invariant hinvR
  refine ⟨hInv, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsplit
    exact ⟨x, z, fun h => hx (Fin.ext h)⟩
  intro L hL hfin
  by_cases hc : ∀ i j, L i = L j → R i = R j
  · left
    intro i j
    exact ⟨fun h => congrArg Fin.val (hc i j h), fun h => hfin i j h⟩
  right
  push Not at hc
  obtain ⟨i, j, hLij, hRij⟩ := hc
  obtain ⟨g, hg, hgi⟩ := htr i z
  have hLz : L z = L (g j) := by rw [← hgi]; exact (hL g hg i j).mpr hLij
  have hRz : R z ≠ R (g j) := by
    intro h
    apply hRij
    have := (hInv g hg i j).mp (by rw [hgi]; exact congrArg Fin.val h)
    exact Fin.ext this
  -- the closure of `R` with `z` and `g j` joined is finer than `L`
  have hLinv : MInvGen gs L := fun h hh x y hxy =>
    (hL h (Subgroup.subset_closure hh) x y).mpr hxy
  have hfinR : MFiner R L := fun x y h => hfin x y (congrArg Fin.val h)
  have hbelow : MFiner (mblkTry gs z R (g j)) L :=
    mblkClos_below (mblkMerge_repr hr z (g j)) (mblkMerge_below hfinR hLz) hLinv
  -- since `R` is fixed, that closure has one class
  have hstep := (mblkOuterStep_step gs z).foldl_fixed _ R hr (mblkResult_fixed gs z) (g j)
    (List.mem_finRange _)
  have hone : ∀ x, mblkTry gs z R (g j) x = mblkTry gs z R (g j) z := by
    by_contra hne
    push Not at hne
    unfold mblkOuterStep at hstep
    rw [if_pos hne] at hstep
    apply hRz
    have := mblkClos_finer gs (mblkMerge R z (g j)) z (g j) (mblkMerge_join R z (g j))
    unfold mblkTry at hstep
    rwa [hstep] at this
  intro x y
  rw [hbelow x z (hone x), hbelow y z (hone y)]

end GI.Impl
