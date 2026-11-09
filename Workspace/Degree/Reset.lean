module

public import Workspace.Degree.Spine
public import Workspace.Degree.Drops
public import Workspace.Algorithm.FreshState

@[expose] public section

/-!
# The reset

At a large transitive state `T`, the program moves to the faithful image on the domain and sets
`N := s`. This gives `q ≤ D < N^α`, so the rounds of the general algorithm apply with no change. The
state is `State.freshOn` of the general algorithm, with the hierarchy of `T` carried to the domain,
instead of a new one. A fresh call of the general algorithm forgets the hierarchy, so its weight
would not be under control.

The stored ratios are upper bounds, and they may exceed the new `N`. So they are clamped to `s`, and
the caps with them. The cap stays valid because the ratio bounds a count of classes
(`capAt_min_count`), and the origin labels are clamped too, which matters only for `Small`.

Main results, all for `resetState T`:

* `resetState_hierInv`: the hierarchy invariant;
* `resetState_res_le`: no more resources;
* `resetState_measure`: a measure below that of the reset state is below that of `T`;
* `resetState_dGood`: the invariant of the recursion.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl Equiv Equiv.Perm

variable {Ω C : Type}

/-- An interval carried to the domain and clamped to `s`. -/
def resetInterval (D : Set Ω) (s : ℕ) (I : Interval Ω) : Interval D :=
  ⟨Setoid.comap Subtype.val I.part, min I.ratio s, min I.cap (min I.ratio s), min I.origin s⟩

/-- The hierarchy of the reset state. -/
noncomputable def resetHier (T : State Ω C) : List (Interval T.dom) := T.hier.map (resetInterval T.dom T.size)

/-- **The reset state**: the faithful image on the domain, with `N = s`, no rows, and the carried
hierarchy. -/
noncomputable def resetState (T : State Ω C) : State T.dom C := T.freshOn (resetHier T)

variable (T : State Ω C)

@[simp] theorem resetState_G : (resetState T).G = T.domGroup := rfl
@[simp] theorem resetState_dom : (resetState T).dom = Set.univ := rfl
@[simp] theorem resetState_N : (resetState T).N = T.size := rfl
@[simp] theorem resetState_hier : (resetState T).hier = resetHier T := rfl
@[simp] theorem resetState_rows : (resetState T).rows = none := rfl
@[simp] theorem resetState_floor : (resetState T).floor = false := rfl
@[simp] theorem resetState_h : (resetState T).h = 2 := rfl

theorem resetState_size : (resetState T).size = T.size := by
  unfold State.size
  rw [resetState_dom]
  exact Nat.card_congr (Equiv.Set.univ _)

theorem resetState_transitive (ht : T.Transitive) : (resetState T).Transitive := by
  intro a _ b _
  obtain ⟨g, hg, hgab⟩ := ht a.1 a.2 b.1 b.2
  exact ⟨T.domHom ⟨g, hg⟩, ⟨_, rfl⟩, Subtype.ext hgab⟩

/-- An element of the image moves points as an element of `G` does. -/
theorem exists_lift {g : Perm T.dom} (hg : g ∈ T.domGroup) :
    ∃ g₀ ∈ T.G, ∀ v : T.dom, (g v : Ω) = g₀ v := by
  obtain ⟨⟨g₀, hg₀⟩, rfl⟩ := hg
  exact ⟨g₀, hg₀, fun _ => rfl⟩

theorem val_mem_orb {a w : T.dom} (h : w ∈ orb T.domGroup a) : (w : Ω) ∈ orb T.G a := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g₀, hg₀, h₀⟩ := exists_lift T hg
  exact ⟨g₀, hg₀, (h₀ a).symm⟩

theorem val_mem_classIn {c : Setoid Ω} {a w : T.dom}
    (h : w ∈ classIn T.domGroup Set.univ (Setoid.comap Subtype.val c) a) :
    (w : Ω) ∈ classIn T.G T.dom c a :=
  ⟨w.2, val_mem_orb T h.2.1, h.2.2⟩

/-- The count of classes does not grow on the image. -/
theorem classCount_reset_le [Finite Ω] (f c : Setoid Ω) (a : T.dom) :
    classCount (Setoid.comap Subtype.val f)
        (classIn T.domGroup Set.univ (Setoid.comap Subtype.val c) a) ≤
      classCount f (classIn T.G T.dom c a) := by
  unfold classCount
  refine Nat.card_le_card_of_injective
    (Quotient.map (fun w => ⟨(w.1 : Ω), val_mem_classIn T w.2⟩) (fun _ _ h => h)) ?_
  intro x y hxy
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  simp only [Quotient.map_mk] at hxy
  have h := Quotient.exact hxy
  exact Quotient.sound h

theorem classCount_le_size [Finite Ω] (f : Setoid T.dom) (X : Set T.dom) :
    classCount f X ≤ T.size := by
  unfold classCount State.size
  calc Nat.card (Quotient (Setoid.comap (Subtype.val : X → T.dom) f)) ≤ Nat.card X :=
        Nat.card_le_card_of_surjective _ Quotient.mk_surjective
    _ ≤ Nat.card T.dom := Nat.card_le_card_of_injective _ Subtype.val_injective

/-- The cap of an interval passes to the image: a section of a subgroup of the image comes from a
section of its lift. -/
theorem capAt_reset [Finite Ω] {f c : Setoid Ω} {b : ℕ} {a : T.dom}
    (h : CapAt T.G T.dom f c b a) :
    CapAt T.domGroup Set.univ (Setoid.comap Subtype.val f) (Setoid.comap Subtype.val c) b a := by
  intro U hU hUa t ht φ hφ hk
  have hlift : ∀ u : T.liftGroup U, T.domHom ⟨u, T.liftGroup_le U u.2⟩ ∈ U := fun u =>
    (State.mem_liftGroup.1 u.2).2
  let ρ : T.liftGroup U →* U :=
    { toFun := fun u => ⟨T.domHom ⟨u, T.liftGroup_le U u.2⟩, hlift u⟩
      map_one' := Subtype.ext (map_one T.domHom)
      map_mul' := fun x y => Subtype.ext (map_mul T.domHom ⟨x, T.liftGroup_le U x.2⟩
        ⟨y, T.liftGroup_le U y.2⟩) }
  have hρ : Function.Surjective ρ := by
    intro u
    obtain ⟨⟨g, hg⟩, hgu⟩ := hU u.2
    refine ⟨⟨g, State.mem_liftGroup.2 ⟨hg, ?_⟩⟩, Subtype.ext hgu⟩
    rw [show T.domHom ⟨g, hg⟩ = (u : Perm T.dom) from hgu]
    exact u.2
  refine h (T.liftGroup U) (T.liftGroup_le U) ?_ t ht (φ.comp ρ) (hφ.comp hρ) ?_
  · intro u hu
    exact val_mem_classIn T (hUa _ (hlift ⟨u, hu⟩))
  · intro u hfix
    refine hk (ρ u) fun w hw => ?_
    exact hfix w (val_mem_classIn T hw)

theorem resetInterval_invariant {I : Interval Ω}
    (h : ∀ g ∈ T.G, ∀ v ∈ T.dom, ∀ w ∈ T.dom, I.part.r (g v) (g w) ↔ I.part.r v w) :
    ∀ g ∈ T.domGroup, ∀ v ∈ (Set.univ : Set T.dom), ∀ w ∈ (Set.univ : Set T.dom),
      (Setoid.comap Subtype.val I.part).r (g v) (g w) ↔
        (Setoid.comap Subtype.val I.part).r v w := by
  intro g hg v _ w _
  obtain ⟨g₀, hg₀, h₀⟩ := exists_lift T hg
  change I.part.r (g v : Ω) (g w : Ω) ↔ I.part.r (v : Ω) w
  rw [h₀, h₀]
  exact h g₀ hg₀ v v.2 w w.2

theorem chain_reset [Finite Ω] :
    ∀ {f : Setoid Ω} {l : List (Interval Ω)}, Chain T.G T.dom f l →
      Chain T.domGroup Set.univ (Setoid.comap Subtype.val f) (l.map (resetInterval T.dom T.size))
  | _, [], _ => trivial
  | f, I :: l, ⟨h1, h2, h3, h4, h5⟩ => by
    refine ⟨resetInterval_invariant T h1, fun v _ w _ hvw => h2 v v.2 w w.2 hvw, fun a _ => ?_,
      min_le_right _ _, chain_reset h5⟩
    refine le_min ((classCount_reset_le T f I.part a).trans (h3 a a.2)) ?_
    exact classCount_le_size T _ _

theorem caps_reset [Finite Ω] :
    ∀ {f : Setoid Ω} {l : List (Interval Ω)},
      (∀ g ∈ T.G, ∀ v ∈ T.dom, ∀ w ∈ T.dom, f.r (g v) (g w) ↔ f.r v w) →
      Chain T.G T.dom f l → Caps T.G T.dom f l →
      Caps T.domGroup Set.univ (Setoid.comap Subtype.val f) (l.map (resetInterval T.dom T.size))
  | _, [], _, _, _ => trivial
  | f, I :: l, hf, ⟨h1, _, h3, _, h5⟩, ⟨hc, hc'⟩ => by
    refine ⟨fun a _ => ?_, caps_reset h1 h5 hc'⟩
    have h0 := capAt_reset T (hc a a.2)
    have hcount : classCount (Setoid.comap Subtype.val f)
        (classIn T.domGroup Set.univ (Setoid.comap Subtype.val I.part) a) ≤ min I.ratio T.size :=
      le_min ((classCount_reset_le T f I.part a).trans (h3 a a.2)) (classCount_le_size T _ _)
    exact capAt_min_count h0 (State.invariant_univ _)
      (fun g hg v _ w _ => by
        obtain ⟨g₀, hg₀, h₀⟩ := exists_lift T hg
        change f.r (g v : Ω) (g w : Ω) ↔ f.r (v : Ω) w
        rw [h₀, h₀]
        exact hf g₀ hg₀ v v.2 w w.2)
      (resetInterval_invariant T h1) hcount

theorem comap_bot : Setoid.comap (Subtype.val : T.dom → Ω) ⊥ = ⊥ := by
  ext a b
  exact Subtype.ext_iff.symm

theorem fineEnd_reset : ∀ (f : Setoid Ω) (l : List (Interval Ω)),
    fineEnd (Setoid.comap Subtype.val f) (l.map (resetInterval T.dom T.size)) =
      Setoid.comap Subtype.val (fineEnd f l)
  | _, [] => rfl
  | _, I :: l => fineEnd_reset I.part l

/-- **The hierarchy invariant passes to the reset state**. -/
theorem resetState_hierInv [Finite Ω] (h : T.HierInv) : (resetState T).HierInv := by
  obtain ⟨h1, h2, h3⟩ := h
  have hbot : ∀ g ∈ T.G, ∀ v ∈ T.dom, ∀ w ∈ T.dom,
      (⊥ : Setoid Ω).r (g v) (g w) ↔ (⊥ : Setoid Ω).r v w := fun g _ v _ w _ =>
    ⟨fun e => g.injective e, fun e => congrArg g e⟩
  refine ⟨?_, ?_, ?_⟩
  · have := chain_reset T h1
    rwa [comap_bot] at this
  · intro a _ w _ hw
    change (fineEnd ⊥ (resetHier T)).r a w
    rw [resetHier, ← comap_bot T, fineEnd_reset]
    exact h2 a a.2 w w.2 (val_mem_orb T hw)
  · have := caps_reset T hbot h1 h3
    rwa [comap_bot] at this

/-! ### The resources -/

theorem pointValue_reset [Finite Ω] (a : T.dom) :
    pointValue T.domGroup a ≤ pointValue T.G a := by
  have h1 : (orb T.domGroup a).ncard ≤ (orb T.G (a : Ω)).ncard := by
    have h2 : (Subtype.val '' orb T.domGroup a) ⊆ orb T.G (a : Ω) := by
      rintro _ ⟨w, hw, rfl⟩
      exact val_mem_orb T hw
    have h3 := Set.ncard_le_ncard h2 (Set.toFinite _)
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective] at h3
  have h1' : ((orb T.domGroup a).ncard : ℝ) ≤ ((orb T.G (a : Ω)).ncard : ℝ) := by
    exact_mod_cast h1
  have h2 := T.sigma_domGroup P₀.κ a.2
  have h3 : Real.log (((orb T.domGroup a).ncard : ℝ) + 2) ≤
      Real.log (((orb T.G (a : Ω)).ncard : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  unfold pointValue
  rw [h2]
  linarith

theorem resetState_psi_le [Finite Ω] : (resetState T).psi ≤ T.psi :=
  State.psi_le T.psi_nonneg fun a _ =>
    (pointValue_reset T a).trans (T.point_le_psi a.2)

theorem towerRank_mono {a b : ℕ} (h : a ≤ b) :
    (GI.towerRank a).toNat ≤ (GI.towerRank b).toNat := by
  unfold GI.towerRank
  by_cases ha : a ≤ 1
  · rw [if_pos ha]; simp
  · have hb : ¬ b ≤ 1 := by omega
    rw [if_neg ha, if_neg hb]
    have := Nat.log_mono_right (b := 2) h
    omega

theorem rhoNat_reset_le : ∀ l : List (Interval Ω),
    rhoNat (l.map (resetInterval T.dom T.size)) ≤ rhoNat l
  | [] => le_rfl
  | I :: l => by
    have h1 := rhoNat_reset_le l
    have h2 := towerRank_mono (min_le_left I.ratio T.size)
    simp only [rhoNat, List.map_cons, List.sum_cons] at h1 ⊢
    exact Nat.add_le_add h2 h1

theorem capSum_reset_le : ∀ l : List (Interval Ω),
    capSum (l.map (resetInterval T.dom T.size)) ≤ capSum l
  | [] => le_rfl
  | I :: l => by
    have h1 := capSum_reset_le l
    simp only [capSum, List.map_cons, List.sum_cons] at h1 ⊢
    exact Nat.add_le_add (min_le_left _ _) h1

theorem log_nat_mono {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

theorem hierQ_reset_le : ∀ l : List (Interval Ω),
    State.hierQ (l.map (resetInterval T.dom T.size)) ≤ State.hierQ l
  | [] => le_rfl
  | I :: l => by
    have h1 := hierQ_reset_le l
    simp only [State.hierQ, List.map_cons, List.sum_cons] at h1 ⊢
    refine add_le_add (mul_le_mul (log_nat_mono (min_le_left _ _)) (log_nat_mono ?_)
      (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)) h1
    exact max_le_max (min_le_left _ _) le_rfl

/-- **The reset state has no more resources.** -/
theorem resetState_res_le [Finite Ω] : (resetState T).dres.Le T.dres :=
  ⟨(resetState_size T).le, resetState_psi_le T, by
    have : rhoNat (resetState T).hier ≤ rhoNat T.hier := rhoNat_reset_le T T.hier
    exact (Nat.cast_le (α := ℝ)).2 this, hierQ_reset_le T T.hier⟩

theorem resetState_sigma_le [Finite Ω] : (resetState T).sigma P₀.κ ≤ T.sigma P₀.κ := by
  refine State.sigma_le_of_forall fun a _ => ?_
  have h := T.sigma_domGroup P₀.κ a.2
  change GI.sigma P₀.κ a T.domGroup ≤ _
  rw [← h]
  exact T.sigma_point_le P₀.κ a.2

/-- Entry by entry at most: then anything below the first is below the second. -/
theorem mlt_of_entries {μ a b : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (h : MLt μ a)
    (h1 : a.1 ≤ b.1) (h2 : a.2.1 ≤ b.2.1) (h3 : a.2.2.1 ≤ b.2.2.1)
    (h4 : a.2.2.2.1 ≤ b.2.2.2.1) (h5 : a.2.2.2.2.1 ≤ b.2.2.2.2.1)
    (h6 : a.2.2.2.2.2.1 ≤ b.2.2.2.2.2.1) (h7 : a.2.2.2.2.2.2.1 ≤ b.2.2.2.2.2.2.1)
    (h8 : a.2.2.2.2.2.2.2.1 ≤ b.2.2.2.2.2.2.2.1)
    (h9 : a.2.2.2.2.2.2.2.2 ≤ b.2.2.2.2.2.2.2.2) : MLt μ b := by
  rw [mlt_iff] at h ⊢
  omega

/-- **A measure below that of the reset state is below that of `T`.** -/
theorem resetState_measure [Finite Ω] {D Nm : ℕ} (hd : DGood D Nm T) (ht : T.Transitive)
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (h : MLt μ (measure P₀ .cont (resetState T))) :
    MLt μ (measure P₀ .cont T) := by
  have hR := resetState_transitive T ht
  have hs : (resetState T).size = T.size := resetState_size T
  refine mlt_of_entries h hd.size_le le_rfl hs.le ?_ (resetState_sigma_le T)
    (rhoNat_reset_le T T.hier) ?_ (capSum_reset_le T T.hier) le_rfl
  · change trInd (resetState T) ≤ trInd T
    rw [trInd_of _ hR, trInd_of _ ht]
  · change 3 * flInd (resetState T) + 2 ≤ 3 * flInd T + T.h
    have e : flInd (resetState T) = 0 := by simp [flInd]
    rw [e, hd.h]
    omega

/-- `Small` for the reset state. Here `ρ < s` is used: it is why the threshold has `ρ` in it. -/
theorem resetState_small (hsm : SmallInv T) (h2 : 2 ≤ T.size) (hρ : rhoNat T.hier ≤ T.size) :
    SmallInv (resetState T) := by
  refine ⟨?_, (rhoNat_reset_le T T.hier).trans hρ, fun R hR => by simp at hR⟩
  intro I hI
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hI
  obtain ⟨h3, -, -, -⟩ := hsm.1 J hJ
  exact ⟨le_min h3 h2, min_le_right _ _, (min_le_right _ _).trans (min_le_right _ _),
    min_le_right _ _⟩

/-- **The reset state has the invariant of the recursion.** -/
theorem resetState_dGood {D Nm : ℕ} (hd : DGood D Nm T) (hN : P₀.N₀ < T.size) :
    DGood D Nm (resetState T) := by
  have hfin : Finite Ω := hd.finite
  refine ⟨inferInstance, hN, hd.size_le.trans hd.N_le, (resetState_size T).le,
    resetState_hierInv T hd.hier, rfl, rfl, rfl, ?_, ?_⟩
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hI
    exact (min_le_left _ _).trans (hd.caps J hJ)
  · refine GammaHat.of_surjective (G := T.G) (H := T.domGroup)
      T.domHom.rangeRestrict T.domHom.rangeRestrict_surjective hd.gamma

/-- The bound `D < N^α` at a state with `D⁵ < N²`: this is what makes the existing round apply. -/
theorem le_rpow_of_pow_lt {D N : ℕ} (h : D ^ 5 < N ^ 2) : (D : ℝ) ≤ (N : ℝ) ^ P₀.α := by
  have e : P₀.α = 2 / 5 := by norm_num [P₀]
  rw [e]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have h1 : (D : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 := by exact_mod_cast h.le
  have h2 : ((D : ℝ) ^ 5) ^ (1 / 5 : ℝ) ≤ ((N : ℝ) ^ 2) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h3 : ((D : ℝ) ^ 5) ^ (1 / 5 : ℝ) = D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD]
    norm_num
  have h4 : ((N : ℝ) ^ 2) ^ (1 / 5 : ℝ) = (N : ℝ) ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
    norm_num
  rwa [h3, h4] at h2

end GI.Degree
