import Workspace.MulticosetPieces
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The recursion of Theorem A.20, as a procedure on mathematical objects

`proc ℓ H N X Y` follows the proof of Theorem A.20 (`thm:solvable-multicoset`) with
fuel `ℓ`, a bound on the derived length of `H/N`:

* `ℓ = 0`: the action is trivial, and equality of the multisets decides.
* `ℓ + 1`: put `A = relDerived H N ℓ` (the last derived subgroup of `H/N`, abelian
  modulo `N`). Partition `X` and `Y` into pieces (intersections with `A`-orbits).
  For every ordered pair of pieces `(S, T)` of both inputs, compute `Iso_H(S, T)`
  (`pairStep`): fix `x ∈ S`; for each distinct `y ∈ T` with a point transporter `τ`,
  `x^τ = y`, call the recursion on `(H_x, A ∩ H_x, S, T^{τ⁻¹})` and multiply its answer
  by `τ` on the right. The profile of a piece `S` is the coset object
  `(r, A·Iso_H(r, S))`, where `r` is a chosen piece of its `H`-class (`profObj`); its
  color is `r` and its coset is the profile transporter `A·Iso_H(r, S)`. Recursively
  transport the multisets of profiles under `H` with kernel `A`. Finally impose the
  affine compatibility condition (`glue`).

Each call returns its set and the number of procedure calls it made (`Out.calls`, this
call included). Point stabilizers, point transporters and the vector-transporter step
(cited: [LM, Proposition 3.9, Theorem 1.4, Section 5.2], Kannan-Bachem) appear only
through their mathematical results (`Aut H x`, a chosen `τ`, a chosen `g` solving the
affine condition). Their polynomial running time is a stage-2 obligation.
-/

namespace GI.Multicoset

open Classical

universe u

variable {G : Type u} [Group G]

/-- The result of one call: the returned set of group elements and the number of
procedure calls made in its recursion tree (the call itself included). -/
structure Out (G : Type u) where
  /-- The returned set. -/
  set : Set G
  /-- The number of calls of the procedure in this recursion tree. -/
  calls : ℕ

/-- Pairwise subconfiguration transport `Iso_H(S, T)` from point-stabilizer calls `rec`. -/
noncomputable def pairStep {Ω : Type u} [RAct G Ω]
    (rec : Subgroup G → Subgroup G → Multiset Ω → Multiset Ω → Out G)
    (H A : Subgroup G) (S T : Multiset Ω) : Out G :=
  if hS : ∃ x, x ∈ S then
    let sub : Ω → Out G := fun y =>
      if hy : ∃ τ ∈ H, hS.choose ↼ τ = y then
        let r := rec (Aut H hS.choose) (A ⊓ Aut H hS.choose) S (T ↼ hy.choose⁻¹)
        ⟨(fun k => k * hy.choose) '' r.set, r.calls⟩
      else ⟨∅, 0⟩
    ⟨⋃ y ∈ T.toFinset, (sub y).set, ∑ y ∈ T.toFinset, (sub y).calls⟩
  else ⟨if T = 0 then (H : Set G) else ∅, 0⟩

/-- The chosen representative of the `H`-class of a piece among the pieces `P`. -/
noncomputable def classRep {Ω : Type u} (P : Finset (Multiset Ω))
    (pair : Multiset Ω → Multiset Ω → Set G) (S : Multiset Ω) : Multiset Ω :=
  Classical.epsilon (fun S' => S' ∈ P ∧ (pair S' S).Nonempty)

/-- The profile of a piece as an explicit coset object: color `r`, coset `A·Iso_H(r, S)`. -/
noncomputable def profObj {Ω : Type u} (A : Subgroup G) (P : Finset (Multiset Ω))
    (pair : Multiset Ω → Multiset Ω → Set G) (S : Multiset Ω) : CObj (Multiset Ω) G :=
  ⟨classRep P pair S, {z | ∃ a ∈ A, ∃ g ∈ pair (classRep P pair S) S, z = a * g}⟩

/-- The correction `a` with `δ(a) = -u(g)`, when it exists. -/
noncomputable def corr {Ω : Type u} [RAct G Ω] (A : Subgroup G) (X : Multiset Ω) (g : G) : G :=
  if h : DCond A X (coord A (X ↼ g)) then h.choose else 1

/-- `Aut_H(X)` from the profile stabilizer `B`: the corrected lifts `c·a_c` of the elements
`c` of the full preimage `C` of the stabilizer of zero in `W/D`, together with
`Aut_A(X) = A ∩ ⋂_i B_i`. -/
noncomputable def autGlue {Ω : Type u} [RAct G Ω] (A : Subgroup G) (X : Multiset Ω)
    (B : Set G) : Subgroup G :=
  Subgroup.closure ((fun g => g * corr A X g) '' {g | g ∈ B ∧ DCond A X (coord A (X ↼ g))})
    ⊔ (A ⊓ ⨅ S ∈ pieces A X, Aut A S)

/-- The affine gluing step, from the profile transporter `R = B τ`. -/
noncomputable def glue {Ω : Type u} [RAct G Ω] (A : Subgroup G) (X Y : Multiset Ω)
    (R : Set G) : Set G :=
  if hR : R.Nonempty then
    if hg : ∃ g ∈ (fun r => hR.some⁻¹ * r) '' R,
        DCond A Y (affine A Y g (coord A (X ↼ hR.some))) then
      (fun k => k * (hR.some * hg.choose * hg.choose_spec.2.choose)) ''
        (autGlue A X ((fun r => r * hR.some⁻¹) '' R) : Set G)
    else ∅
  else ∅

/-- The procedure of Theorem A.20 with fuel `ℓ`. -/
noncomputable def proc : ℕ → {Ω : Type u} → [RAct G Ω] → Subgroup G → Subgroup G →
    Multiset Ω → Multiset Ω → Out G
  | 0, _, _, H, _, X, Y => ⟨if X = Y then (H : Set G) else ∅, 1⟩
  | ℓ + 1, Ω, _, H, N, X, Y =>
    let A := relDerived H N ℓ
    let pair : Multiset Ω → Multiset Ω → Out G :=
      fun S T => pairStep (fun H' N' X' Y' => proc ℓ H' N' X' Y') H A S T
    let P := pieces A X ∪ pieces A Y
    let prof := profObj A P (fun S T => (pair S T).set)
    let pc := proc ℓ H A ((pieces A X).val.map prof) ((pieces A Y).val.map prof)
    ⟨glue A X Y pc.set, 1 + ∑ p ∈ P ×ˢ P, (pair p.1 p.2).calls + pc.calls⟩

/-! ### Correctness of the pairwise step -/

section Pair

variable {Ω : Type u} [RAct G Ω]

theorem pairStep_set {H N A : Subgroup G} (hNn : Normalizes H N)
    (hAH : A ≤ H) (hAn : Normalizes H A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ N)
    (rec : Subgroup G → Subgroup G → Multiset Ω → Multiset Ω → Out G)
    (hrec : ∀ (K : Subgroup G) (X' Y' : Multiset Ω), K ≤ H →
      Normalizes K (A ⊓ K) → Fixes (A ⊓ K) X' → Fixes (A ⊓ K) Y' →
        (rec K (A ⊓ K) X' Y').set = Iso K X' Y')
    {S T : Multiset Ω} (hS : ∀ s ∈ S, ∀ s' ∈ S, SameOrb A s s')
    (hT : ∀ t ∈ T, ∀ t' ∈ T, SameOrb A t t') (hNS : Fixes N S) (hNT : Fixes N T) :
    (pairStep rec H A S T).set = Iso H S T := by
  unfold pairStep
  by_cases hex : ∃ x, x ∈ S
  · rw [dif_pos hex]
    set x := hex.choose with hxdef
    have hx : x ∈ S := hex.choose_spec
    -- the kernel `A ∩ H_x` fixes the whole `A`-orbit of `x`
    have hfixorb : ∀ z, SameOrb A x z → ∀ c ∈ A ⊓ Aut H x, z ↼ c = z := by
      rintro z ⟨a, ha, rfl⟩ c ⟨hcA, hcx⟩
      refine abelian_stabilizer_fixes_orbit (N := N) ?_ ?_ hcA hcx.2 ha
      · intro a ha b hb
        have := hcomm a ha b hb
        simpa [commutatorElement_def] using this
      · intro a' ha' n hn
        exact fixes_point_act (fun n hn => hNS n hn x hx) hNn (hAH ha') n hn
    ext h
    simp only [Set.mem_iUnion, Multiset.mem_toFinset]
    constructor
    · rintro ⟨y, hy, hh⟩
      by_cases hyτ : ∃ τ ∈ H, x ↼ τ = y
      · rw [dif_pos hyτ] at hh
        obtain ⟨hτH, hτ⟩ := hyτ.choose_spec
        set τ := hyτ.choose
        obtain ⟨k, hk, rfl⟩ := hh
        have hsub := hrec (Aut H x) S (T ↼ τ⁻¹) (aut_le H x)
          ((hAn.mono (aut_le H x)).inf (normalizes_self _))
          (fun c hc s hs => hfixorb s (hS x hx s hs) c hc)
          (by
            intro c hc z hz
            refine hfixorb z ?_ c hc
            rw [mem_act] at hz
            have h1 : SameOrb A (x ↼ τ) (z ↼ τ⁻¹⁻¹) := by
              rw [hτ]; exact hT y hy _ hz
            rw [inv_inv] at h1
            exact (sameOrb_act_iff hAn hτH).mp h1)
        rw [hsub] at hk
        obtain ⟨hkH, hkS⟩ := hk
        refine ⟨H.mul_mem (aut_le H x hkH) hτH, ?_⟩
        rw [← act_act, hkS, act_inv_act]
      · rw [dif_neg hyτ] at hh; exact absurd hh (Set.notMem_empty _)
    · rintro ⟨hhH, hhS⟩
      have hyT : x ↼ h ∈ T := by rw [← hhS]; exact act_mem_act h hx
      have hyτ : ∃ τ ∈ H, x ↼ τ = x ↼ h := ⟨h, hhH, rfl⟩
      refine ⟨x ↼ h, hyT, ?_⟩
      rw [dif_pos hyτ]
      obtain ⟨hτH, hτ⟩ := hyτ.choose_spec
      set τ := hyτ.choose
      have hsub := hrec (Aut H x) S (T ↼ τ⁻¹) (aut_le H x)
        ((hAn.mono (aut_le H x)).inf (normalizes_self _))
        (fun c hc s hs => hfixorb s (hS x hx s hs) c hc)
        (by
          intro c hc z hz
          refine hfixorb z ?_ c hc
          rw [mem_act] at hz
          have h1 : SameOrb A (x ↼ τ) (z ↼ τ⁻¹⁻¹) := by
            rw [hτ]; exact hT _ hyT _ hz
          rw [inv_inv] at h1
          exact (sameOrb_act_iff hAn hτH).mp h1)
      refine ⟨h * τ⁻¹, ?_, by simp⟩
      rw [hsub]
      refine ⟨⟨H.mul_mem hhH (H.inv_mem hτH), ?_⟩, ?_⟩
      · rw [← act_act, ← hτ, act_act_inv]
      · rw [← act_act, hhS]
  · rw [dif_neg hex]
    have hS0 : S = 0 := by
      by_contra h
      exact hex (Multiset.exists_mem_of_ne_zero h)
    subst hS0
    ext h
    simp only [mem_iso, zero_act]
    by_cases hT0 : T = 0
    · subst hT0; simp
    · rw [if_neg hT0]
      simp only [Set.mem_empty_iff_false, false_iff, not_and]
      intro _ h0; exact hT0 h0.symm

theorem pairStep_calls_le (rec : Subgroup G → Subgroup G → Multiset Ω → Multiset Ω → Out G)
    (H A : Subgroup G) (S T : Multiset Ω) (K : ℕ)
    (hK : ∀ H' N' (Y' : Multiset Ω), Multiset.card Y' = Multiset.card T →
      (rec H' N' S Y').calls ≤ K) :
    (pairStep rec H A S T).calls ≤ Multiset.card T * K := by
  unfold pairStep
  split_ifs with hex
  · refine (Finset.sum_le_sum (g := fun _ => K) ?_).trans ?_
    · intro y _
      dsimp only
      split_ifs with hy
      · exact hK _ _ _ (card_act _ _)
      · exact Nat.zero_le _
    · rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Multiset.toFinset_card_le T)
  all_goals exact Nat.zero_le _

end Pair

/-! ### Correctness of the affine gluing -/

section Glue

variable {Ω Ω' : Type u} [RAct G Ω] [RAct G Ω']

theorem corr_spec {A : Subgroup G} {X : Multiset Ω} {g : G}
    (hD : DCond A X (coord A (X ↼ g))) :
    corr A X g ∈ A ∧ ∀ S ∈ pieces A X, coord A (X ↼ g) S * corr A X g ∈ Aut A S := by
  rw [corr, dif_pos hD]
  exact hD.choose_spec

theorem mem_inf_iInf_pieces {A : Subgroup G} {X : Multiset Ω} {x : G} :
    x ∈ A ⊓ ⨅ S ∈ pieces A X, Aut A S ↔ x ∈ A ∧ ∀ S ∈ pieces A X, x ∈ Aut A S := by
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]

/-- "These corrected generators, together with `Aut_A(X) = ⋂_i B_i`, generate all of
`Aut_H(X)`": the output of `autGlue` is the full stabilizer, given that the profile
stabilizer `B` preserves the profiles of `X` and contains `Aut_H(X)`. -/
theorem autGlue_eq {H A : Subgroup G} (hAH : A ≤ H) {X : Multiset Ω} {B : Set G}
    (hBH : B ⊆ H) (hBconf : ∀ g ∈ B, Conf A X (X ↼ g)) (hautB : ∀ g ∈ Aut H X, g ∈ B) :
    autGlue A X B = Aut H X := by
  have hle : autGlue A X B ≤ Aut H X := by
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, ⟨hgB, hD⟩, rfl⟩
      obtain ⟨hcA, hc⟩ := corr_spec hD
      refine ⟨H.mul_mem (hBH hgB) (hAH hcA), ?_⟩
      rw [← act_act]
      exact dcond_witness (hBconf g hgB) hc
    · intro x hx
      obtain ⟨hxA, hxS⟩ := mem_inf_iInf_pieces.mp hx
      exact ⟨hAH hxA, fix_of_pieces (fun S hS => (hxS S hS).2)⟩
  refine le_antisymm hle (le_of_cover (A := A) hle ?_ ?_)
  · rintro x ⟨hxX, hxA⟩
    refine Subgroup.mem_sup_right (mem_inf_iInf_pieces.mpr ⟨hxA, fun S hS => ?_⟩)
    exact ⟨hxA, piece_act_of_fix hS hxA hxX.2⟩
  · intro t ht
    have hD : DCond A X (coord A (X ↼ t)) := by
      rw [ht.2]
      exact (dcond_iff (conf_self A X)).mpr ⟨1, A.one_mem, act_one X⟩
    obtain ⟨hcA, _⟩ := corr_spec hD
    refine ⟨t * corr A X t, Subgroup.mem_sup_left (Subgroup.subset_closure
      ⟨t, ⟨hautB t ht, hD⟩, rfl⟩), (corr A X t)⁻¹, A.inv_mem hcA, by group⟩

/-- The gluing step returns the full transporter. Its inputs are the profile transporter
`Iso_H(U, V)` of some profile objects `U, V` with the five properties proved below for the
multisets of profiles. -/
theorem glue_eq {H A : Subgroup G} (hAH : A ≤ H) (hAn : Normalizes H A)
    {X Y : Multiset Ω} {U V : Ω'}
    (hP1 : ∀ g ∈ Aut H U, Conf A X (X ↼ g)) (hP2 : ∀ τ ∈ Iso H U V, Conf A Y (X ↼ τ))
    (hP3 : ∀ g ∈ Aut H V, Conf A Y (Y ↼ g)) (hP4 : Iso H X Y ⊆ Iso H U V)
    (hP5 : ∀ g ∈ Aut H X, g ∈ Aut H U) :
    glue A X Y (Iso H U V) = Iso H X Y := by
  unfold glue
  by_cases hR : (Iso H U V).Nonempty
  · rw [dif_pos hR]
    have hτ : hR.some ∈ Iso H U V := hR.some_mem
    set τ := hR.some with hτdef
    have hBX : ∀ g, g ∈ (fun r => r * τ⁻¹) '' Iso H U V ↔ g ∈ Aut H U := by
      intro g
      constructor
      · rintro ⟨r, hr, rfl⟩; exact (mem_iso_iff_of_mem hτ).mp hr
      · intro hg; exact ⟨g * τ, (mem_iso_iff_of_mem hτ).mpr (by simpa using hg), by simp⟩
    have haut : autGlue A X ((fun r => r * τ⁻¹) '' Iso H U V) = Aut H X :=
      autGlue_eq hAH (fun g hg => aut_le H U ((hBX g).mp hg))
        (fun g hg => hP1 g ((hBX g).mp hg)) (fun g hg => (hBX g).mpr (hP5 g hg))
    have hBY : ∀ g ∈ (fun r => τ⁻¹ * r) '' Iso H U V, g ∈ Aut H V := by
      rintro _ ⟨r, hr, rfl⟩
      exact iso_comp (iso_inv hτ) hr
    have hconfτ : Conf A Y (X ↼ τ) := hP2 τ hτ
    by_cases hg : ∃ g ∈ (fun r => τ⁻¹ * r) '' Iso H U V,
        DCond A Y (affine A Y g (coord A (X ↼ τ)))
    · rw [dif_pos hg]
      obtain ⟨hgB, hgD⟩ := hg.choose_spec
      set g := hg.choose
      obtain ⟨haA, ha⟩ := hgD.choose_spec
      set a := hgD.choose
      have hgV := hBY g hgB
      have hgH : g ∈ H := aut_le H V hgV
      have hequiv := coord_act_equiv hAn hgH (hP3 g hgV) hconfτ
      obtain ⟨_, _, hconfg⟩ := affine_law hAn hgH (hP3 g hgV) hconfτ
      have hfinal : X ↼ τ ↼ g ↼ a = Y := by
        refine dcond_witness hconfg (fun T hT => ?_)
        have := (Aut A T).mul_mem (hequiv T hT).1 (ha T hT)
        simpa [mul_assoc] using this
      have ht : τ * g * a ∈ Iso H X Y :=
        ⟨H.mul_mem (H.mul_mem hτ.1 hgH) (hAH haA), by rw [← act_act, ← act_act, hfinal]⟩
      rw [haut, iso_eq_aut_mul ht]
    · rw [dif_neg hg]
      ext h
      simp only [Set.mem_empty_iff_false, false_iff]
      intro hh
      apply hg
      refine ⟨τ⁻¹ * h, ⟨h, hP4 hh, rfl⟩, ?_⟩
      have hgV := hBY _ ⟨h, hP4 hh, rfl⟩
      have hgH : τ⁻¹ * h ∈ H := aut_le H V hgV
      have hequiv := coord_act_equiv hAn hgH (hP3 _ hgV) hconfτ
      have hXY : X ↼ τ ↼ (τ⁻¹ * h) = Y := by rw [act_act, mul_inv_cancel_left]; exact hh.2
      refine dcond_congr (fun T hT => (hequiv T hT).2) ?_
      rw [hXY]
      exact (dcond_iff (conf_self A Y)).mpr ⟨1, A.one_mem, act_one Y⟩
  · rw [dif_neg hR]
    ext h
    simp only [Set.mem_empty_iff_false, false_iff]
    exact fun hh => hR ⟨h, hP4 hh⟩

end Glue

/-! ### Profiles as explicit coset objects -/

section Profiles

variable {Ω : Type u} [RAct G Ω] {H A : Subgroup G} {P : Finset (Multiset Ω)}
  {pairf : Multiset Ω → Multiset Ω → Set G}

theorem classRep_spec (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) {S : Multiset Ω}
    (hS : S ∈ P) : classRep P pairf S ∈ P ∧ (Iso H (classRep P pairf S) S).Nonempty := by
  have hex : ∃ S', S' ∈ P ∧ (pairf S' S).Nonempty :=
    ⟨S, hS, ⟨1, by rw [hpair S hS S hS]; exact (Aut H S).one_mem⟩⟩
  have h : classRep P pairf S ∈ P ∧ (pairf (classRep P pairf S) S).Nonempty :=
    Classical.epsilon_spec hex
  refine ⟨h.1, ?_⟩
  rw [← hpair _ h.1 S hS]
  exact h.2

theorem classRep_eq (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) {S S' : Multiset Ω}
    (hS : S ∈ P) (hS' : S' ∈ P) (hSS : (Iso H S S').Nonempty) :
    classRep P pairf S = classRep P pairf S' := by
  unfold classRep
  congr 1
  funext R
  apply propext
  obtain ⟨j, hj⟩ := hSS
  constructor
  · rintro ⟨hR, i, hi⟩
    rw [hpair R hR S hS] at hi
    refine ⟨hR, i * j, ?_⟩
    rw [hpair R hR S' hS']
    exact iso_comp hi hj
  · rintro ⟨hR, i, hi⟩
    rw [hpair R hR S' hS'] at hi
    refine ⟨hR, i * j⁻¹, ?_⟩
    rw [hpair R hR S hS]
    exact iso_comp hi (iso_inv hj)

theorem profObj_act (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) {S : Multiset Ω}
    (hS : S ∈ P) {h : G} (hh : h ∈ H) (hSh : S ↼ h ∈ P) :
    profObj A P pairf (S ↼ h) = profObj A P pairf S ↼ h := by
  have hrep : classRep P pairf S = classRep P pairf (S ↼ h) :=
    classRep_eq hpair hS hSh ⟨h, hh, rfl⟩
  have hrP := (classRep_spec hpair hS).1
  apply CObj.ext
  · exact hrep.symm
  · rw [cobj_act_coset]
    simp only [profObj, ← hrep]
    rw [hpair _ hrP _ hSh, hpair _ hrP _ hS]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, g, hg, rfl⟩
      refine ⟨a * (g * h⁻¹), ⟨a, ha, g * h⁻¹, ?_, rfl⟩, by group⟩
      have := (mem_iso_shift hh).mp hg
      simpa using this
    · rintro ⟨_, ⟨a, ha, g, hg, rfl⟩, rfl⟩
      exact ⟨a, ha, g * h, iso_comp hg ⟨hh, rfl⟩, by group⟩

theorem profObj_fix (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) (hAn : Normalizes H A)
    {S : Multiset Ω} (hS : S ∈ P) {a : G} (ha : a ∈ A) :
    profObj A P pairf S ↼ a = profObj A P pairf S := by
  have hrP := (classRep_spec hpair hS).1
  apply CObj.ext
  · rfl
  · rw [cobj_act_coset]
    simp only [profObj]
    rw [hpair _ hrP _ hS]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨a', ha', g, hg, rfl⟩, rfl⟩
      exact ⟨a' * (g * a * g⁻¹), A.mul_mem ha' (hAn g hg.1 a ha), g, hg, by group⟩
    · rintro ⟨a', ha', g, hg, rfl⟩
      refine ⟨a' * (g * a⁻¹ * g⁻¹) * g, ⟨a' * (g * a⁻¹ * g⁻¹),
        A.mul_mem ha' (hAn g hg.1 _ (A.inv_mem ha)), g, hg, rfl⟩, by group⟩

theorem profObj_eq (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) (hAn : Normalizes H A)
    {S T : Multiset Ω} (hS : S ∈ P) (hT : T ∈ P) {τ : G}
    (he : profObj A P pairf S ↼ τ = profObj A P pairf T) : ∃ c ∈ A, S ↼ τ = T ↼ c := by
  have htag : classRep P pairf S = classRep P pairf T := congrArg CObj.tag he
  obtain ⟨hrP, i, hi⟩ := classRep_spec hpair hS
  have hmem : i * τ ∈ (profObj A P pairf S ↼ τ).coset := by
    rw [cobj_act_coset]
    refine ⟨i, ⟨1, A.one_mem, i, ?_, by simp⟩, rfl⟩
    rw [hpair _ hrP _ hS]; exact hi
  rw [he] at hmem
  obtain ⟨a, ha, j, hj, hij⟩ := hmem
  rw [← htag, hpair _ hrP _ hT] at hj
  refine ⟨j⁻¹ * a * j, hAn.inv hj.1 ha, ?_⟩
  rw [← hi.2, act_act, hij, ← hj.2, act_act]
  congr 1; group

/-- The multiset of profiles of `U`. -/
noncomputable def hat (A : Subgroup G) (P : Finset (Multiset Ω))
    (pairf : Multiset Ω → Multiset Ω → Set G) (U : Multiset Ω) : Multiset (CObj (Multiset Ω) G) :=
  (pieces A U).val.map (profObj A P pairf)

theorem hat_act (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) (hAn : Normalizes H A)
    {U : Multiset Ω} (hU : pieces A U ⊆ P) {h : G} (hh : h ∈ H) (hUh : pieces A (U ↼ h) ⊆ P) :
    hat A P pairf U ↼ h = hat A P pairf (U ↼ h) := by
  unfold hat
  rw [multiset_act_def, Multiset.map_map, pieces_act hAn hh,
    Finset.image_val_of_injOn (fun x _ y _ hxy => act_injective h hxy), Multiset.map_map]
  apply Multiset.map_congr rfl
  intro S hS
  have hS' : S ∈ pieces A U := hS
  simp only [Function.comp_apply]
  refine (profObj_act hpair (hU hS') hh (hUh ?_)).symm
  rw [pieces_act hAn hh]
  exact Finset.mem_image_of_mem _ hS'

theorem hat_fix (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) (hAn : Normalizes H A)
    {U : Multiset Ω} (hU : pieces A U ⊆ P) : Fixes A (hat A P pairf U) := by
  intro a ha o ho
  obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp ho
  exact profObj_fix hpair hAn (hU hS) ha

/-- Equal profile multisets give configurations: "`X^τ` has an explicitly computed offset
in `W_Y`". -/
theorem hat_conf (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) (hAn : Normalizes H A)
    {U V : Multiset Ω} (hU : pieces A U ⊆ P) (hV : pieces A V ⊆ P) {τ : G} (hτ : τ ∈ H)
    (he : hat A P pairf U ↼ τ = hat A P pairf V) : Conf A V (U ↼ τ) := by
  have hfwd : ∀ S ∈ pieces A U, ∃ T ∈ pieces A V, ∃ c ∈ A, S ↼ τ = T ↼ c := by
    intro S hS
    have hm : profObj A P pairf S ↼ τ ∈ hat A P pairf V := by
      rw [← he]; exact act_mem_act τ (Multiset.mem_map_of_mem _ hS)
    obtain ⟨T, hT, hTe⟩ := Multiset.mem_map.mp hm
    exact ⟨T, hT, profObj_eq hpair hAn (hU hS) (hV hT) hTe.symm⟩
  have hbwd : ∀ T ∈ pieces A V, ∃ S ∈ pieces A U, ∃ c ∈ A, S ↼ τ = T ↼ c := by
    intro T hT
    have hm : profObj A P pairf T ∈ hat A P pairf U ↼ τ := by
      rw [he]; exact Multiset.mem_map_of_mem _ hT
    rw [mem_act] at hm
    obtain ⟨S, hS, hSe⟩ := Multiset.mem_map.mp hm
    refine ⟨S, hS, profObj_eq hpair hAn (hU hS) (hV hT) ?_⟩
    rw [hSe, act_inv_act]
  apply conf_of_parts
  · intro z hz
    rw [mem_act] at hz
    have hS : partAt A U {z ↼ τ⁻¹} ∈ pieces A U := mem_pieces.mpr ⟨_, hz, rfl⟩
    obtain ⟨T, hT, c, hc, hSc⟩ := hfwd _ hS
    have hzS : z ∈ partAt A U {z ↼ τ⁻¹} ↼ τ := by
      rw [mem_act]; exact mem_piece_iff.mpr ⟨hz, sameOrb_refl A _⟩
    rw [hSc, mem_act] at hzS
    exact ⟨z ↼ c⁻¹, Multiset.mem_of_le (piece_le hT) hzS, ⟨c, hc, by simp⟩⟩
  · intro T hT
    obtain ⟨S, hS, c, hc, hSc⟩ := hbwd T hT
    refine ⟨c, hc, ?_⟩
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
    have hcong : partAt A (U ↼ τ) T = partAt A (U ↼ τ) (S ↼ τ) := by
      apply partAt_congr (t₀ := t)
      · intro s hs; exact piece_sameOrb hT ht hs
      · intro s hs
        rw [hSc, mem_act] at hs
        exact (piece_sameOrb hT ht hs).trans ⟨c, hc, by simp⟩
      · exact piece_ne_zero hT
      · exact act_ne_zero (piece_ne_zero hS) τ
    rw [hcong, partAt_act hAn hτ, partAt_piece hS, hSc]

end Profiles

/-! ### Correctness of the recursion -/

open scoped commutatorElement in
/-- **The recursion of Theorem A.20 returns the full transporter.** With fuel `ℓ` at least
the derived length of the acting quotient (`relDerived H N ℓ ≤ N`), a kernel `N ◁ H`, and
`N` fixing every listed object, `proc ℓ H N X Y` returns `Iso_H(X, Y)`. -/
theorem proc_set : ∀ (ℓ : ℕ) {Ω : Type u} [RAct G Ω] (H N : Subgroup G) (X Y : Multiset Ω),
    N ≤ H → Normalizes H N → relDerived H N ℓ ≤ N → Fixes N X → Fixes N Y →
    (proc ℓ H N X Y).set = Iso H X Y
  | 0, Ω, _, H, N, X, Y, _, _, hd, hX, _ => by
    have hHN : H ≤ N := hd
    show (if X = Y then (H : Set G) else ∅) = Iso H X Y
    ext h
    split_ifs with hXY
    · subst hXY
      exact ⟨fun hh => ⟨hh, hX.act_eq (hHN hh)⟩, fun hh => hh.1⟩
    · simp only [Set.mem_empty_iff_false, false_iff]
      intro hh
      exact hXY ((hX.act_eq (hHN hh.1)).symm.trans hh.2)
  | ℓ + 1, Ω, _, H, N, X, Y, hNH, hn, hd, hX, hY => by
    set A := relDerived H N ℓ with hAdef
    have hAH : A ≤ H := relDerived_le hNH ℓ
    have hAn : Normalizes H A := relDerived_normalizes hn ℓ
    have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ N := by
      intro a ha b hb
      have := relDerived_commutator_mem hd ha hb
      rwa [commutatorElement_def] at this
    set pair : Multiset Ω → Multiset Ω → Out G :=
      fun S T => pairStep (fun H' N' X' Y' => proc ℓ H' N' X' Y') H A S T with hpairdef
    set P := pieces A X ∪ pieces A Y with hPdef
    have hrec : ∀ (K : Subgroup G) (X' Y' : Multiset Ω), K ≤ H →
        Normalizes K (A ⊓ K) → Fixes (A ⊓ K) X' → Fixes (A ⊓ K) Y' →
          (proc ℓ K (A ⊓ K) X' Y').set = Iso K X' Y' := by
      intro K X' Y' hKH hKn hX' hY'
      refine proc_set ℓ K (A ⊓ K) X' Y' inf_le_right hKn ?_ hX' hY'
      exact le_inf (relDerived_mono hNH hKH inf_le_left ℓ le_rfl)
        (relDerived_le inf_le_right ℓ)
    have hfixP : ∀ S ∈ P, Fixes N S := by
      intro S hS
      rcases Finset.mem_union.mp hS with h | h
      · exact hX.of_le (piece_le h)
      · exact hY.of_le (piece_le h)
    have hpair : ∀ S ∈ P, ∀ T ∈ P, (pair S T).set = Iso H S T := by
      intro S hS T hT
      have hsS : ∀ S ∈ P, ∀ s ∈ S, ∀ s' ∈ S, SameOrb A s s' := by
        intro S hS s hs s' hs'
        rcases Finset.mem_union.mp hS with h | h
        · exact piece_sameOrb h hs hs'
        · exact piece_sameOrb h hs hs'
      exact pairStep_set hn hAH hAn hcomm _ hrec (hsS S hS) (hsS T hT) (hfixP S hS)
        (hfixP T hT)
    set pairf : Multiset Ω → Multiset Ω → Set G := fun S T => (pair S T).set with hpairfdef
    have hpairf : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T := hpair
    have hXP : pieces A X ⊆ P := Finset.subset_union_left
    have hYP : pieces A Y ⊆ P := Finset.subset_union_right
    have hpc : (proc ℓ H A (hat A P pairf X) (hat A P pairf Y)).set =
        Iso H (hat A P pairf X) (hat A P pairf Y) :=
      proc_set ℓ H A _ _ hAH hAn (relDerived_mono hNH le_rfl le_rfl ℓ le_rfl)
        (hat_fix hpairf hAn hXP) (hat_fix hpairf hAn hYP)
    show glue A X Y (proc ℓ H A (hat A P pairf X) (hat A P pairf Y)).set = Iso H X Y
    rw [hpc]
    apply glue_eq hAH hAn
    · intro g hg
      exact hat_conf hpairf hAn hXP hXP (aut_le H _ hg) hg.2
    · intro τ hτ
      exact hat_conf hpairf hAn hXP hYP hτ.1 hτ.2
    · intro g hg
      exact hat_conf hpairf hAn hYP hYP (aut_le H _ hg) hg.2
    · rintro h ⟨hh, he⟩
      refine ⟨hh, ?_⟩
      rw [hat_act hpairf hAn hXP hh (by rw [he]; exact hYP), he]
    · rintro g ⟨hg, he⟩
      refine ⟨hg, ?_⟩
      rw [hat_act hpairf hAn hXP hg (by rw [he]; exact hXP), he]

/-! ### Counting -/

/-- **The recursion bound.** Each call makes at most `4M²` pairwise comparisons, each with at
most `M` point-stabilizer calls, and one profile call; every call keeps at most `M` listed
objects per side. Hence the recursion tree of `proc ℓ` has at most `(4M³ + 2)^ℓ` calls. -/
theorem proc_calls_le : ∀ (ℓ : ℕ) {Ω : Type u} [RAct G Ω] (H N : Subgroup G)
    (X Y : Multiset Ω) (M : ℕ), Multiset.card X ≤ M → Multiset.card Y ≤ M →
    (proc ℓ H N X Y).calls ≤ (4 * M ^ 3 + 2) ^ ℓ
  | 0, _, _, _, _, _, _, _, _, _ => le_refl 1
  | ℓ + 1, Ω, _, H, N, X, Y, M, hX, hY => by
    set K := (4 * M ^ 3 + 2) ^ ℓ with hKdef
    have hK1 : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
    set A := relDerived H N ℓ
    set P := pieces A X ∪ pieces A Y with hPdef
    have hPcard : P.card ≤ 2 * M := by
      refine (Finset.card_union_le _ _).trans ?_
      have := card_pieces_le A X
      have := card_pieces_le A Y
      omega
    have hPmem : ∀ S ∈ P, Multiset.card S ≤ M := by
      intro S hS
      rcases Finset.mem_union.mp hS with h | h
      · exact (Multiset.card_le_card (piece_le h)).trans hX
      · exact (Multiset.card_le_card (piece_le h)).trans hY
    have hpair : ∀ p ∈ P ×ˢ P,
        (pairStep (fun H' N' X' Y' => proc ℓ H' N' X' Y') H A p.1 p.2).calls ≤ M * K := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      refine (pairStep_calls_le _ H A p.1 p.2 K ?_).trans
        (Nat.mul_le_mul_right _ (hPmem _ h2))
      intro H' N' Y' hY'
      exact proc_calls_le ℓ H' N' p.1 Y' M (hPmem _ h1) (hY' ▸ hPmem _ h2)
    have hsum : ∑ p ∈ P ×ˢ P,
        (pairStep (fun H' N' X' Y' => proc ℓ H' N' X' Y') H A p.1 p.2).calls ≤
          (2 * M) * (2 * M) * (M * K) := by
      refine (Finset.sum_le_sum hpair).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Finset.card_product]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hPcard hPcard)
    have hprof : ∀ (pf : Multiset Ω → Multiset Ω → Set G),
        (proc ℓ H A ((pieces A X).val.map (profObj A P pf))
          ((pieces A Y).val.map (profObj A P pf))).calls ≤ K := by
      intro pf
      refine proc_calls_le ℓ H A _ _ M ?_ ?_
      · simpa using (card_pieces_le A X).trans hX
      · simpa using (card_pieces_le A Y).trans hY
    show 1 + ∑ p ∈ P ×ˢ P,
        (pairStep (fun H' N' X' Y' => proc ℓ H' N' X' Y') H A p.1 p.2).calls +
        (proc ℓ H A _ _).calls ≤ (4 * M ^ 3 + 2) ^ (ℓ + 1)
    refine le_trans (Nat.add_le_add (Nat.add_le_add_left hsum 1) (hprof _)) ?_
    rw [pow_succ, ← hKdef]
    have e1 : (2 * M) * (2 * M) * (M * K) = 4 * M ^ 3 * K := by ring
    have e2 : K * (4 * M ^ 3 + 2) = 4 * M ^ 3 * K + 2 * K := by ring
    rw [e1, e2]
    omega

end GI.Multicoset
