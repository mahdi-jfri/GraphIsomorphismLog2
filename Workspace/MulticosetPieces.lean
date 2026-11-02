import Workspace.MulticosetDerived
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pieces, abelian coordinates and the affine action (proof of Theorem A.20)

Let `A` be normalized by `H`. A *piece* of a multiset `X` is a nonempty intersection of
`X` with an `A`-orbit ("partition `X` into its nonempty intersections `S_1, …, S_r` with
`A`-orbits").

For a target `Y` with pieces `T`, a configuration `Z` with the profiles of `Y` is
`Z = ∑_T T^{w_T}` with `w_T ∈ A` (`Conf A Y Z`). The coordinate `w_T` is determined
modulo `B_T = Aut_A(T)` (`coord`). This is the paper's `W = ⊕ A/B_i`, written with
representatives in `A` instead of quotient groups. A coordinate vector lies in the
"diagonal" `D = δ(A)` after the shift by `a` when `w_T a ∈ B_T` for all `T`
(`DCond`): this is `w + δ(a) = 0` in `W`.

For `g` in the profile stabilizer of `Y`, the action on configurations is affine:
`(∑ T^{w_T})^g = ∑_T T^{u_T · w_{T'}^g}`, where `T'` is the piece carried to the orbit of
`T` (`src`) and `u = coord(Y^g)` is the offset (`affine_law`).
-/

namespace GI.Multicoset

open Classical

universe u v

variable {G : Type u} [Group G] {Ω : Type v} [RAct G Ω]

/-! ### Orbits of `A` -/

/-- `x` and `y` lie in one `A`-orbit. -/
def SameOrb (A : Subgroup G) (x y : Ω) : Prop := ∃ a ∈ A, x ↼ a = y

theorem sameOrb_refl (A : Subgroup G) (x : Ω) : SameOrb A x x := ⟨1, A.one_mem, act_one x⟩

theorem SameOrb.symm {A : Subgroup G} {x y : Ω} (h : SameOrb A x y) : SameOrb A y x := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a⁻¹, A.inv_mem ha, act_act_inv x a⟩

theorem SameOrb.trans {A : Subgroup G} {x y z : Ω} (h : SameOrb A x y) (h' : SameOrb A y z) :
    SameOrb A x z := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨a * b, A.mul_mem ha hb, (act_act x a b).symm⟩

theorem sameOrb_act_self {A : Subgroup G} (x : Ω) {a : G} (ha : a ∈ A) : SameOrb A x (x ↼ a) :=
  ⟨a, ha, rfl⟩

/-- `H` permutes the `A`-orbits when it normalizes `A`. -/
theorem sameOrb_act_iff {H A : Subgroup G} (hn : Normalizes H A) {h : G} (hh : h ∈ H)
    {x y : Ω} : SameOrb A (x ↼ h) (y ↼ h) ↔ SameOrb A x y := by
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨h * a * h⁻¹, hn h hh a ha, ?_⟩
    have := congrArg (fun z => z ↼ h⁻¹) he
    simpa [act_act, mul_assoc] using this
  · rintro ⟨a, ha, rfl⟩
    refine ⟨h⁻¹ * a * h, hn.inv hh ha, ?_⟩
    simp [act_act, mul_assoc]

/-! ### Parts of a multiset in given orbits -/

/-- The part of `Z` lying in the `A`-orbits met by `T`. -/
noncomputable def partAt (A : Subgroup G) (Z T : Multiset Ω) : Multiset Ω :=
  Z.filter (fun z => ∃ t ∈ T, SameOrb A t z)

/-- The pieces of `X`: its intersections with `A`-orbits, each listed once. -/
noncomputable def pieces (A : Subgroup G) (X : Multiset Ω) : Finset (Multiset Ω) :=
  X.toFinset.image (fun x => partAt A X {x})

theorem partAt_le (A : Subgroup G) (Z T : Multiset Ω) : partAt A Z T ≤ Z :=
  Multiset.filter_le _ _

theorem mem_partAt {A : Subgroup G} {Z T : Multiset Ω} {z : Ω} :
    z ∈ partAt A Z T ↔ z ∈ Z ∧ ∃ t ∈ T, SameOrb A t z := Multiset.mem_filter

theorem partAt_add (A : Subgroup G) (Z₁ Z₂ T : Multiset Ω) :
    partAt A (Z₁ + Z₂) T = partAt A Z₁ T + partAt A Z₂ T := Multiset.filter_add _ _ _

theorem partAt_zero (A : Subgroup G) (T : Multiset Ω) : partAt A 0 T = 0 := rfl

theorem partAt_sum {ι : Type*} (A : Subgroup G) (s : Finset ι) (f : ι → Multiset Ω)
    (T : Multiset Ω) : partAt A (∑ i ∈ s, f i) T = ∑ i ∈ s, partAt A (f i) T := by
  induction s using Finset.induction_on with
  | empty => simp [partAt_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, partAt_add, ih]

/-- The part only depends on the orbits met: two nonempty multisets inside one common
`A`-orbit cut out the same part. -/
theorem partAt_congr {A : Subgroup G} {Z T T' : Multiset Ω} {t₀ : Ω}
    (hT : ∀ t ∈ T, SameOrb A t₀ t) (hT' : ∀ t ∈ T', SameOrb A t₀ t) (hne : T ≠ 0)
    (hne' : T' ≠ 0) : partAt A Z T = partAt A Z T' := by
  apply Multiset.filter_congr
  intro z _
  obtain ⟨s, hs⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨s', hs'⟩ := Multiset.exists_mem_of_ne_zero hne'
  constructor
  · rintro ⟨t, ht, htz⟩
    exact ⟨s', hs', ((hT' s' hs').symm.trans (hT t ht)).trans htz⟩
  · rintro ⟨t, ht, htz⟩
    exact ⟨s, hs, ((hT s hs).symm.trans (hT' t ht)).trans htz⟩

theorem partAt_act {H A : Subgroup G} (hn : Normalizes H A) {h : G} (hh : h ∈ H)
    (Z T : Multiset Ω) : partAt A (Z ↼ h) (T ↼ h) = partAt A Z T ↼ h := by
  unfold partAt
  rw [filter_act]
  congr 1
  apply Multiset.filter_congr
  intro z _
  constructor
  · rintro ⟨t, ht, htz⟩
    rw [mem_act] at ht
    refine ⟨t ↼ h⁻¹, ht, ?_⟩
    rw [← sameOrb_act_iff hn hh]
    simpa using htz
  · rintro ⟨t, ht, htz⟩
    exact ⟨t ↼ h, act_mem_act h ht, (sameOrb_act_iff hn hh).mpr htz⟩

/-! ### Basic facts about pieces -/

theorem mem_pieces {A : Subgroup G} {X S : Multiset Ω} :
    S ∈ pieces A X ↔ ∃ x ∈ X, S = partAt A X {x} := by
  simp only [pieces, Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem mem_piece_iff {A : Subgroup G} {X : Multiset Ω} {x z : Ω} :
    z ∈ partAt A X {x} ↔ z ∈ X ∧ SameOrb A x z := by
  rw [mem_partAt]; simp

theorem piece_ne_zero {A : Subgroup G} {X S : Multiset Ω} (hS : S ∈ pieces A X) : S ≠ 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_pieces.mp hS
  intro h0
  have hm : x ∈ partAt A X {x} := mem_piece_iff.mpr ⟨hx, sameOrb_refl A x⟩
  rw [h0] at hm
  simp at hm

theorem piece_le {A : Subgroup G} {X S : Multiset Ω} (hS : S ∈ pieces A X) : S ≤ X := by
  obtain ⟨x, _, rfl⟩ := mem_pieces.mp hS
  exact partAt_le _ _ _

/-- All points of a piece lie in one `A`-orbit. -/
theorem piece_sameOrb {A : Subgroup G} {X S : Multiset Ω} (hS : S ∈ pieces A X) {s s' : Ω}
    (hs : s ∈ S) (hs' : s' ∈ S) : SameOrb A s s' := by
  obtain ⟨x, _, rfl⟩ := mem_pieces.mp hS
  exact (mem_piece_iff.mp hs).2.symm.trans (mem_piece_iff.mp hs').2

/-- A point of `X` in the orbit of a piece belongs to that piece. -/
theorem mem_piece_of_sameOrb {A : Subgroup G} {X S : Multiset Ω} (hS : S ∈ pieces A X)
    {s z : Ω} (hs : s ∈ S) (hz : z ∈ X) (hsz : SameOrb A s z) : z ∈ S := by
  obtain ⟨x, _, rfl⟩ := mem_pieces.mp hS
  exact mem_piece_iff.mpr ⟨hz, (mem_piece_iff.mp hs).2.trans hsz⟩

/-- A piece is its own part: `partAt X S = S`. -/
theorem partAt_piece {A : Subgroup G} {X S : Multiset Ω} (hS : S ∈ pieces A X) :
    partAt A X S = S := by
  obtain ⟨x, hx, rfl⟩ := mem_pieces.mp hS
  exact partAt_congr (t₀ := x) (fun t ht => (mem_piece_iff.mp ht).2)
    (fun t ht => by rw [Multiset.mem_singleton.mp ht]; exact sameOrb_refl A x)
    (piece_ne_zero hS) (by simp)

/-- Distinct pieces lie in distinct `A`-orbits. -/
theorem piece_eq_of_sameOrb {A : Subgroup G} {X S S' : Multiset Ω} (hS : S ∈ pieces A X)
    (hS' : S' ∈ pieces A X) {s s' : Ω} (hs : s ∈ S) (hs' : s' ∈ S') (hss : SameOrb A s s') :
    S = S' := by
  obtain ⟨x, _, rfl⟩ := mem_pieces.mp hS
  obtain ⟨x', _, rfl⟩ := mem_pieces.mp hS'
  have hxx : SameOrb A x x' :=
    ((mem_piece_iff.mp hs).2.trans hss).trans (mem_piece_iff.mp hs').2.symm
  apply Multiset.filter_congr
  intro z _
  simp only [Multiset.mem_singleton, exists_eq_left]
  exact ⟨fun h => hxx.symm.trans h, fun h => hxx.trans h⟩

/-- The part of `Z` at a point's orbit, for a point of a piece. -/
theorem partAt_piece_eq_single {A : Subgroup G} {X S : Multiset Ω} (hS : S ∈ pieces A X)
    {s : Ω} (hs : s ∈ S) (Z : Multiset Ω) : partAt A Z S = partAt A Z {s} :=
  partAt_congr (t₀ := s) (fun t ht => piece_sameOrb hS hs ht)
    (fun t ht => by rw [Multiset.mem_singleton.mp ht]; exact sameOrb_refl A s)
    (piece_ne_zero hS) (by simp)

/-- Decomposition into parts: if every point of `Z` lies in the orbit of a point of `Y`,
then `Z` is the sum of its parts at the pieces of `Y`. In particular (with `Z = X = Y`),
`X` is the sum of its pieces. -/
theorem sum_partAt_pieces {A : Subgroup G} {Y Z : Multiset Ω}
    (hZ : ∀ z ∈ Z, ∃ y ∈ Y, SameOrb A y z) : ∑ T ∈ pieces A Y, partAt A Z T = Z := by
  apply Multiset.ext'
  intro z
  rw [Multiset.count_sum']
  by_cases hz : z ∈ Z
  · obtain ⟨y, hy, hyz⟩ := hZ z hz
    have hT : partAt A Y {y} ∈ pieces A Y := mem_pieces.mpr ⟨y, hy, rfl⟩
    rw [Finset.sum_eq_single (partAt A Y {y})]
    · rw [partAt, Multiset.count_filter, if_pos]
      exact ⟨y, mem_piece_iff.mpr ⟨hy, sameOrb_refl A y⟩, hyz⟩
    · intro T hT' hne
      rw [partAt, Multiset.count_filter, if_neg]
      rintro ⟨t, ht, htz⟩
      apply hne
      exact piece_eq_of_sameOrb hT' hT ht (mem_piece_iff.mpr ⟨hy, sameOrb_refl A y⟩)
        (htz.trans hyz.symm)
    · intro h; exact absurd hT h
  · rw [Multiset.count_eq_zero_of_notMem hz]
    apply Finset.sum_eq_zero
    intro T _
    exact Multiset.count_eq_zero_of_notMem (fun h => hz (Multiset.mem_of_le (partAt_le _ _ _) h))

theorem sum_pieces (A : Subgroup G) (X : Multiset Ω) : ∑ S ∈ pieces A X, S = X := by
  conv_rhs => rw [← sum_partAt_pieces (A := A) (Y := X) (Z := X)
    (fun z hz => ⟨z, hz, sameOrb_refl A z⟩)]
  exact Finset.sum_congr rfl (fun S hS => (partAt_piece hS).symm)

theorem card_pieces_le (A : Subgroup G) (X : Multiset Ω) :
    (pieces A X).card ≤ Multiset.card X :=
  Finset.card_image_le.trans (Multiset.toFinset_card_le X)

/-- The pieces of `X^h` are the images of the pieces of `X`. -/
theorem pieces_act {H A : Subgroup G} (hn : Normalizes H A) {h : G} (hh : h ∈ H)
    (X : Multiset Ω) : pieces A (X ↼ h) = (pieces A X).image (fun S => S ↼ h) := by
  ext S
  simp only [mem_pieces, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_act] at hz
    refine ⟨partAt A X {z ↼ h⁻¹}, ⟨_, hz, rfl⟩, ?_⟩
    rw [← partAt_act hn hh]
    congr 1
    simp [multiset_act_def]
  · rintro ⟨S', ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x ↼ h, act_mem_act h hx, ?_⟩
    rw [← partAt_act hn hh]
    congr 1

theorem sum_act {ι : Type*} (s : Finset ι) (f : ι → Multiset Ω) (g : G) :
    (∑ i ∈ s, f i) ↼ g = ∑ i ∈ s, (f i ↼ g) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_act, ih]

theorem act_ne_zero {X : Multiset Ω} (h : X ≠ 0) (g : G) : X ↼ g ≠ 0 := by
  intro h0; apply h
  have := congrArg Multiset.card h0
  simpa using this

/-! ### Abelian action on one orbit -/

open scoped commutatorElement in
/-- "For an abelian action on one orbit, the stabilizer of one point fixes that entire
orbit": if every commutator of `A` lies in a subgroup `N` fixing the orbit of `x`, an
element of `A` fixing `x` fixes every `x^a`, `a ∈ A`. -/
theorem abelian_stabilizer_fixes_orbit {A N : Subgroup G} {x : Ω}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ N) (hfix : ∀ a ∈ A, ∀ n ∈ N, x ↼ a ↼ n = x ↼ a)
    {c : G} (hc : c ∈ A) (hcx : x ↼ c = x) {a : G} (ha : a ∈ A) : x ↼ a ↼ c = x ↼ a := by
  -- `a c = c a ⁅a⁻¹, c⁻¹⁆`
  have he : a * c = c * a * ⁅a⁻¹, c⁻¹⁆ := by
    rw [commutatorElement_def]; group
  rw [act_act, he, ← act_act, ← act_act, hcx]
  exact hfix a ha _ (hcomm _ (A.inv_mem ha) _ (A.inv_mem hc))

/-! ### Coordinates -/

/-- Configurations with the profiles of `Y`: `Z = ∑_T T^{w_T}` with every `w_T ∈ A`. -/
def Conf (A : Subgroup G) (Y Z : Multiset Ω) : Prop :=
  ∃ w : Multiset Ω → G, (∀ T ∈ pieces A Y, w T ∈ A) ∧ Z = ∑ T ∈ pieces A Y, T ↼ w T

/-- The coordinate of `Z` at the piece `T`: some `c ∈ A` with `partAt Z T = T^c`. It is
determined modulo `B_T = Aut_A(T)` (`coord_unique`). -/
noncomputable def coord (A : Subgroup G) (Z T : Multiset Ω) : G :=
  if h : ∃ c ∈ A, partAt A Z T = T ↼ c then h.choose else 1

/-- `w + δ(a) = 0` in `W = ⊕_T A/B_T`: `w_T a ∈ B_T` for every piece `T` of `Y`. The
condition `DCond A Y w` says that `w ∈ D = δ(A)`, with a witness `a` (the negative). -/
def DCond (A : Subgroup G) (Y : Multiset Ω) (w : Multiset Ω → G) : Prop :=
  ∃ a ∈ A, ∀ T ∈ pieces A Y, w T * a ∈ Aut A T

/-- Coordinates are unique modulo `B_T`: "there is a unique offset". -/
theorem coord_unique {A : Subgroup G} {T : Multiset Ω} {c c' : G} (hc : c ∈ A) (hc' : c' ∈ A)
    (he : T ↼ c = T ↼ c') : c * c'⁻¹ ∈ Aut A T :=
  ⟨A.mul_mem hc (A.inv_mem hc'), by rw [← act_act, he, act_act_inv]⟩

/-- A piece moved by an element of `A` stays inside its orbit and keeps its part. -/
theorem partAt_piece_act {A : Subgroup G} {Y T T' : Multiset Ω} (hT : T ∈ pieces A Y)
    (hT' : T' ∈ pieces A Y) {c : G} (hc : c ∈ A) :
    partAt A (T' ↼ c) T = if T' = T then T' ↼ c else 0 := by
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
  split_ifs with hTT
  · subst hTT
    rw [partAt, Multiset.filter_eq_self]
    intro z hz
    rw [mem_act] at hz
    refine ⟨t, ht, (piece_sameOrb hT ht hz).trans ?_⟩
    exact ⟨c, hc, by simp⟩
  · rw [partAt, Multiset.filter_eq_nil]
    rintro z hz ⟨s, hs, hsz⟩
    rw [mem_act] at hz
    apply hTT
    refine piece_eq_of_sameOrb hT' hT hz hs ?_
    exact (SameOrb.symm (⟨c⁻¹, A.inv_mem hc, rfl⟩ : SameOrb A z (z ↼ c⁻¹))).trans hsz.symm

theorem partAt_conf {A : Subgroup G} {Y T : Multiset Ω} (hT : T ∈ pieces A Y)
    {w : Multiset Ω → G} (hw : ∀ T ∈ pieces A Y, w T ∈ A) :
    partAt A (∑ T' ∈ pieces A Y, T' ↼ w T') T = T ↼ w T := by
  rw [partAt_sum, Finset.sum_eq_single T]
  · rw [partAt_piece_act hT hT (hw T hT), if_pos rfl]
  · intro T' hT' hne
    rw [partAt_piece_act hT hT' (hw T' hT'), if_neg hne]
  · intro h; exact absurd hT h

theorem coord_spec {A : Subgroup G} {Y Z T : Multiset Ω} (hZ : Conf A Y Z)
    (hT : T ∈ pieces A Y) : coord A Z T ∈ A ∧ partAt A Z T = T ↼ coord A Z T := by
  obtain ⟨w, hw, rfl⟩ := hZ
  have hex : ∃ c ∈ A, partAt A (∑ T' ∈ pieces A Y, T' ↼ w T') T = T ↼ c :=
    ⟨w T, hw T hT, partAt_conf hT hw⟩
  rw [coord, dif_pos hex]
  exact hex.choose_spec

theorem conf_coord {A : Subgroup G} {Y Z : Multiset Ω} (hZ : Conf A Y Z) :
    Z = ∑ T ∈ pieces A Y, T ↼ coord A Z T := by
  obtain ⟨w, hw, hZw⟩ := id hZ
  conv_lhs => rw [hZw]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [← partAt_conf hT hw, ← hZw]
  exact (coord_spec hZ hT).2

/-- `Y` itself is a configuration (all coordinates `1`). -/
theorem conf_self (A : Subgroup G) (Y : Multiset Ω) : Conf A Y Y :=
  ⟨fun _ => 1, fun _ _ => A.one_mem, by simp [sum_pieces]⟩

/-- Changing coordinates within their classes modulo `B_T` does not change `DCond`. -/
theorem dcond_congr {A : Subgroup G} {Y : Multiset Ω} {w w' : Multiset Ω → G}
    (hw : ∀ T ∈ pieces A Y, w T * (w' T)⁻¹ ∈ Aut A T) (hd : DCond A Y w') : DCond A Y w := by
  obtain ⟨a, ha, h⟩ := hd
  refine ⟨a, ha, fun T hT => ?_⟩
  have := (Aut A T).mul_mem (hw T hT) (h T hT)
  simpa [mul_assoc] using this

/-- A witness of `DCond` for the coordinates of `Z` translates `Z` onto `Y`. -/
theorem dcond_witness {A : Subgroup G} {Y Z : Multiset Ω} (hZ : Conf A Y Z) {a : G}
    (h : ∀ T ∈ pieces A Y, coord A Z T * a ∈ Aut A T) : Z ↼ a = Y := by
  rw [conf_coord hZ, sum_act]
  conv_rhs => rw [← sum_pieces A Y]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [act_act]; exact (h T hT).2

/-- A multiset is a configuration of `Y` as soon as it lies in the orbits of `Y` and each of
its parts is an `A`-translate of the corresponding piece. -/
theorem conf_of_parts {A : Subgroup G} {Y Z : Multiset Ω}
    (horb : ∀ z ∈ Z, ∃ y ∈ Y, SameOrb A y z)
    (hpart : ∀ T ∈ pieces A Y, ∃ c ∈ A, partAt A Z T = T ↼ c) : Conf A Y Z := by
  have hspec : ∀ T ∈ pieces A Y, coord A Z T ∈ A ∧ partAt A Z T = T ↼ coord A Z T := by
    intro T hT
    rw [coord, dif_pos (hpart T hT)]
    exact (hpart T hT).choose_spec
  refine ⟨coord A Z, fun T hT => (hspec T hT).1, ?_⟩
  conv_lhs => rw [← sum_partAt_pieces horb]
  exact Finset.sum_congr rfl (fun T hT => (hspec T hT).2)

/-- The diagonal criterion: a configuration `Z` is an `A`-translate of `Y` exactly when its
coordinate vector lies in `D`. -/
theorem dcond_iff {A : Subgroup G} {Y Z : Multiset Ω} (hZ : Conf A Y Z) :
    DCond A Y (coord A Z) ↔ ∃ a ∈ A, Z ↼ a = Y := by
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, dcond_witness hZ h⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, fun T hT => ⟨A.mul_mem (coord_spec hZ hT).1 ha, ?_⟩⟩
    have h1 : partAt A (Z ↼ a) (T ↼ a) = partAt A Z T ↼ a :=
      partAt_act (normalizes_self A) ha Z T
    have h2 : partAt A Y (T ↼ a) = partAt A Y T := by
      obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
      apply partAt_congr (t₀ := t)
      · intro s hs; rw [mem_act] at hs
        exact (piece_sameOrb hT ht hs).trans ⟨a, ha, by simp⟩
      · intro s hs; exact piece_sameOrb hT ht hs
      · exact act_ne_zero (piece_ne_zero hT) a
      · exact piece_ne_zero hT
    rw [he, h2, partAt_piece hT, (coord_spec hZ hT).2, act_act] at h1
    exact h1.symm

/-! ### The affine action -/

/-- For `g` in the profile stabilizer of `Y`, the piece `T'` of `Y` with `T'^g` in the orbit
of `T`. -/
noncomputable def src (A : Subgroup G) (Y : Multiset Ω) (g : G) (T : Multiset Ω) : Multiset Ω :=
  if h : ∃ T' ∈ pieces A Y, partAt A (Y ↼ g) T = T' ↼ g then h.choose else 0

/-- The affine action `w ↦ R_g(w) + u(g)`: at the piece `T`, the new coordinate is
`u_T · g⁻¹ w_{T'} g`, where `u = coord(Y^g)` is the offset and `T' = src g T`. -/
noncomputable def affine (A : Subgroup G) (Y : Multiset Ω) (g : G) (w : Multiset Ω → G) :
    Multiset Ω → G :=
  fun T => coord A (Y ↼ g) T * (g⁻¹ * w (src A Y g T) * g)

/-- Every point of a configuration lies in the orbit of a point of `Y`. -/
theorem conf_mem_orbit {A : Subgroup G} {Y Z : Multiset Ω} (hZ : Conf A Y Z) {z : Ω}
    (hz : z ∈ Z) : ∃ y ∈ Y, SameOrb A y z := by
  obtain ⟨w, hw, rfl⟩ := hZ
  obtain ⟨T, hT, hzT⟩ := Multiset.mem_sum.mp hz
  rw [mem_act] at hzT
  exact ⟨_, Multiset.mem_of_le (piece_le hT) hzT, ⟨w T, hw T hT, by simp⟩⟩

theorem src_spec {H A : Subgroup G} (hn : Normalizes H A) {Y T : Multiset Ω} {g : G}
    (hg : g ∈ H) (hYg : Conf A Y (Y ↼ g)) (hT : T ∈ pieces A Y) :
    src A Y g T ∈ pieces A Y ∧ partAt A (Y ↼ g) T = src A Y g T ↼ g := by
  have hex : ∃ T' ∈ pieces A Y, partAt A (Y ↼ g) T = T' ↼ g := by
    obtain ⟨hc, hpart⟩ := coord_spec hYg hT
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
    have htc : t ↼ coord A (Y ↼ g) T ∈ partAt A (Y ↼ g) T := by
      rw [hpart]; exact act_mem_act _ ht
    obtain ⟨hz, _⟩ := mem_partAt.mp htc
    rw [mem_act] at hz
    set y := t ↼ coord A (Y ↼ g) T ↼ g⁻¹ with hy
    have h2 : y ↼ g = t ↼ coord A (Y ↼ g) T := by rw [hy]; simp
    refine ⟨partAt A Y {y}, mem_pieces.mpr ⟨y, hz, rfl⟩, ?_⟩
    rw [← partAt_act hn hg]
    apply partAt_congr (t₀ := t)
    · intro s hs; exact piece_sameOrb hT ht hs
    · intro s hs
      rw [mem_act, Multiset.mem_singleton] at hs
      have : s = y ↼ g := by rw [← hs]; simp
      rw [this, h2]
      exact ⟨_, hc, rfl⟩
    · exact piece_ne_zero hT
    · simp [multiset_act_def]
  rw [src, dif_pos hex]
  exact hex.choose_spec

/-- The affine law: for `g ∈ H` with `Y^g` a configuration of `Y` (that is, `g` preserves
the profiles of `Y`), a configuration `Z` is moved to the configuration whose
coordinates are `affine A Y g (coord Z)`, exactly (not only modulo `B_T`). -/
theorem affine_law {H A : Subgroup G} (hn : Normalizes H A) {Y Z : Multiset Ω}
    {g : G} (hg : g ∈ H) (hYg : Conf A Y (Y ↼ g)) (hZ : Conf A Y Z) :
    (∀ T ∈ pieces A Y, partAt A (Z ↼ g) T = T ↼ affine A Y g (coord A Z) T) ∧
      (∀ T ∈ pieces A Y, affine A Y g (coord A Z) T ∈ A) ∧ Conf A Y (Z ↼ g) := by
  have hpart : ∀ T ∈ pieces A Y, partAt A (Z ↼ g) T = T ↼ affine A Y g (coord A Z) T := by
    intro T hT
    obtain ⟨hsrc, hsrcY⟩ := src_spec hn hg hYg hT
    obtain ⟨hu, hu'⟩ := coord_spec hYg hT
    -- the part of `Z^g` at `T` is the image of the part of `Z` at `T' = src g T`
    have hcong : partAt A (Z ↼ g) T = partAt A (Z ↼ g) (src A Y g T ↼ g) := by
      obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
      apply partAt_congr (t₀ := t)
      · intro s hs; exact piece_sameOrb hT ht hs
      · intro s hs
        have : s ∈ partAt A (Y ↼ g) T := by rw [hsrcY]; exact hs
        obtain ⟨_, t', ht', ht's⟩ := mem_partAt.mp this
        exact (piece_sameOrb hT ht ht').trans ht's
      · exact piece_ne_zero hT
      · exact act_ne_zero (piece_ne_zero hsrc) g
    rw [hcong, partAt_act hn hg, (coord_spec hZ hsrc).2, affine, act_act]
    have : src A Y g T ↼ (coord A Z (src A Y g T) * g) =
        src A Y g T ↼ g ↼ (g⁻¹ * coord A Z (src A Y g T) * g) := by
      rw [act_act]; congr 1; group
    rw [this, ← hsrcY, hu', act_act]
  have hw : ∀ T ∈ pieces A Y, affine A Y g (coord A Z) T ∈ A := by
    intro T hT
    obtain ⟨hsrc, _⟩ := src_spec hn hg hYg hT
    exact A.mul_mem (coord_spec hYg hT).1 (by
      simpa using hn.inv hg (coord_spec hZ hsrc).1)
  refine ⟨hpart, hw, affine A Y g (coord A Z), hw, ?_⟩
  have hdec := sum_partAt_pieces (A := A) (Y := Y) (Z := Z ↼ g) (by
    intro z hz
    rw [mem_act] at hz
    obtain ⟨y, hy, hyz⟩ := conf_mem_orbit hZ hz
    obtain ⟨y', hy', hy'z⟩ := conf_mem_orbit hYg (act_mem_act g hy)
    refine ⟨y', hy', hy'z.trans ?_⟩
    have := (sameOrb_act_iff hn hg).mpr hyz
    simpa using this)
  rw [← hdec]
  exact Finset.sum_congr rfl hpart

/-- Under the affine law, the actual coordinates of `Z^g` agree with the affine image of
those of `Z` modulo each `B_T`. -/
theorem coord_act_equiv {H A : Subgroup G} (hn : Normalizes H A) {Y Z : Multiset Ω}
    {g : G} (hg : g ∈ H) (hYg : Conf A Y (Y ↼ g)) (hZ : Conf A Y Z) :
    ∀ T ∈ pieces A Y, coord A (Z ↼ g) T * (affine A Y g (coord A Z) T)⁻¹ ∈ Aut A T ∧
      affine A Y g (coord A Z) T * (coord A (Z ↼ g) T)⁻¹ ∈ Aut A T := by
  obtain ⟨hpart, hw, hconf⟩ := affine_law hn hg hYg hZ
  intro T hT
  obtain ⟨hc, hc'⟩ := coord_spec hconf hT
  have he : T ↼ coord A (Z ↼ g) T = T ↼ affine A Y g (coord A Z) T := by
    rw [← hc', hpart T hT]
  exact ⟨coord_unique hc (hw T hT) he, coord_unique (hw T hT) hc he.symm⟩

/-- An element of `A` fixing `X` fixes each piece of `X`: "`Aut_A(X) = ⋂_i B_i`". -/
theorem piece_act_of_fix {A : Subgroup G} {X S : Multiset Ω} (hS : S ∈ pieces A X) {a : G}
    (ha : a ∈ A) (hX : X ↼ a = X) : S ↼ a = S := by
  have h1 := partAt_act (normalizes_self A) ha X S
  have h2 : partAt A X (S ↼ a) = partAt A X S := by
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hS)
    apply partAt_congr (t₀ := t)
    · intro s hs; rw [mem_act] at hs
      exact (piece_sameOrb hS ht hs).trans ⟨a, ha, by simp⟩
    · intro s hs; exact piece_sameOrb hS ht hs
    · exact act_ne_zero (piece_ne_zero hS) a
    · exact piece_ne_zero hS
  rw [hX, h2, partAt_piece hS] at h1
  exact h1.symm

theorem fix_of_pieces {A : Subgroup G} {X : Multiset Ω} {a : G}
    (h : ∀ S ∈ pieces A X, S ↼ a = S) : X ↼ a = X := by
  conv_lhs => rw [← sum_pieces A X]
  rw [sum_act]
  conv_rhs => rw [← sum_pieces A X]
  exact Finset.sum_congr rfl h

end GI.Multicoset
