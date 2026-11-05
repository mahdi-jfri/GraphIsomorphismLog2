module

public import Workspace.Impl.AggItemUpd
public import Workspace.Impl.AggKer
public import Workspace.Impl.AggLiftMath
public import Workspace.Impl.AggWin

@[expose] public section

/-!
# Case 2a: the mathematics of the halving item

The halving item of Lemma A.11 (`halvingItem`) needs, from the program:

* the alignment `τ₀ ∈ G` (its label image maps `Φ` onto `Φ'`) and the parity twist `t`; the
  round records them as its `halv` field (`itHvChoice`);
* generators of the kernel `K = π⁻¹(1_Φ × Alt(C))`: it is the part of `G` whose label image fixes
  `Φ` pointwise (`it_hv_ker_graph`), so one pointwise stabilizer of the label points of `Φ` in
  the graph group gives it;
* generators of `A = certLift ⊓ π⁻¹(Alt(Φ) × Alt(C))`: inside the graph of `certLift`, `A` is the
  kernel of the sign of the `Φ`-side, so Schreier's lemma for index two gives it
  (`it_hv_schreier`, with a list free of inverses).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.Rectangle
open GI.Cited (Val encPerm gens)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### The recorded halving choices -/

section Choice

variable {S : State Ω C} {L : GiantLabels S}

/-- Every element whose label image maps `Φ` onto `Φ'` lies in the coset of an aligner
`t'` modulo the permitted group (`alignment_coset`). -/
theorem it_hv_align_all {Φ Φ' : Finset (Fin L.q)} (t' : S.G)
    (ht : (L.π t' : Perm (Fin L.q)) '' (Φ : Set (Fin L.q)) = Φ') :
    ∀ g : S.G, (L.π g : Perm (Fin L.q)) '' (Φ : Set (Fin L.q)) = Φ' →
      t'⁻¹ * g ∈ (permitted Φ Φᶜ).comap L.π := by
  intro g hg
  have compl : ∀ x : S.G, (L.π x : Perm (Fin L.q)) '' (Φ : Set (Fin L.q)) = Φ' →
      (L.π x : Perm (Fin L.q)) '' ((Φᶜ : Finset (Fin L.q)) : Set (Fin L.q)) =
        ((Φ'ᶜ : Finset (Fin L.q)) : Set (Fin L.q)) := by
    intro x hx
    rw [Finset.coe_compl, Finset.coe_compl, Set.image_compl_eq (L.π x : Perm (Fin L.q)).bijective,
      hx]
  have := (alignment_coset (L.π t') ht (compl t' ht) (L.π g)).mp ⟨hg, compl g hg⟩
  rw [Subgroup.mem_comap, map_mul, map_inv]
  exact this

/-- The facts of the alignment that the program supplies: `τ₀ ∈ G` and its label image maps
`Φ` onto `Φ'`. -/
def ItHvAl (L : GiantLabels S) (Φ Φ' : Finset (Fin L.q)) (τ₀ : Perm Ω) : Prop :=
  ∃ t' : S.G, (t' : Perm Ω) = τ₀ ∧ (L.π t' : Perm (Fin L.q)) '' (Φ : Set (Fin L.q)) = Φ'

/-- The facts of the twist (the field `twist_spec` of `HalvingChoice` at `Φ`). -/
def ItHvTw (L : GiantLabels S) (Φ : Finset (Fin L.q)) (t : Perm Ω) : Prop :=
  t ∈ L.lift (permitted Φ Φᶜ) ∧ ∀ g ∈ L.lift (permitted Φ Φᶜ),
    g ∈ L.lift (evenSides Φ Φᶜ) ∨ t⁻¹ * g ∈ L.lift (evenSides Φ Φᶜ)

open Classical in
/-- **The halving choices of the program**: the alignment `τ₀` for `(Φ, Φ')` and the twist `t`
for `Φ`; the default choices elsewhere. -/
noncomputable def itHvChoice (L : GiantLabels S) (Φ Φ' : Finset (Fin L.q)) (τ₀ t : Perm Ω)
    (hal : Φ.card = Φ'.card → 2 ≤ Φ.card → ItHvAl L Φ Φ' τ₀)
    (htw : 2 ≤ Φ.card → ItHvTw L Φ t) : HalvingChoice S L where
  align a b := if a = Φ ∧ b = Φ' then τ₀ else (HalvingChoice.default S L).align a b
  align_spec a b h1 h2 := by
    by_cases hab : a = Φ ∧ b = Φ'
    · obtain ⟨rfl, rfl⟩ := hab
      obtain ⟨t', ht', him⟩ := hal h1 h2
      exact ⟨t', by rw [if_pos ⟨rfl, rfl⟩, ht'], him, it_hv_align_all t' him⟩
    · simp only [if_neg hab]
      exact (HalvingChoice.default S L).align_spec a b h1 h2
  twist a := if a = Φ then t else (HalvingChoice.default S L).twist a
  twist_spec a h2 := by
    by_cases ha : a = Φ
    · subst ha
      simp only [↓reduceIte]
      exact htw h2
    · simp only [if_neg ha]
      exact (HalvingChoice.default S L).twist_spec a h2

theorem itHvChoice_align (L : GiantLabels S) (Φ Φ' : Finset (Fin L.q)) (τ₀ t : Perm Ω) hal htw :
    (itHvChoice L Φ Φ' τ₀ t hal htw).align Φ Φ' = τ₀ := by
  simp [itHvChoice]

theorem itHvChoice_twist (L : GiantLabels S) (Φ Φ' : Finset (Fin L.q)) (τ₀ t : Perm Ω) hal htw :
    (itHvChoice L Φ Φ' τ₀ t hal htw).twist Φ = t := by
  simp [itHvChoice]

/-- **The twist of a paired transposition**: a lift `t ∈ G` of `(a b)(c d)` with `a, b ∈ Φ`,
`c, d ∉ Φ` is a twist (`Halving.twist_facts`). -/
theorem it_hv_tw_pair {Φ : Finset (Fin L.q)} {a b c d : Fin L.q} (ha : a ∈ Φ) (hb : b ∈ Φ)
    (hab : a ≠ b) (hc : c ∉ Φ) (hd : d ∉ Φ) (hcd : c ≠ d) {t : Perm Ω} (htG : t ∈ S.G)
    (ht : (L.π ⟨t, htG⟩ : Perm (Fin L.q)) = swap a b * swap c d) : ItHvTw L Φ t :=
  Halving.twist_facts (H := ⟨Φ, 1, t, ⊥⟩) ha hb hab hc hd hcd htG ht

/-- **No twist is needed when `C` has at most one point** (`Halving.no_twist_facts`). -/
theorem it_hv_tw_one {Φ : Finset (Fin L.q)} (hC : Φᶜ.card ≤ 1) : ItHvTw L Φ 1 :=
  Halving.no_twist_facts (H := ⟨Φ, 1, 1, ⊥⟩) hC rfl

end Choice

/-! ### Schreier's lemma for index two, without inverses -/

section Schreier

variable {M : Type*} [Group M]

/-- The Schreier list for the transversal `{1, t}` of the kernel of `χ`, with `t⁻¹` replaced
by `t` and the extra generator `t²`: for `χ s = 1`, `s` and `t s t`; otherwise `s t` and
`t s`. -/
def itHvSch (χ : M → ℤˣ) (t : M) (S : List M) : List M :=
  t * t :: S.flatMap fun s => if χ s = 1 then [s, t * s * t] else [s * t, t * s]

theorem it_hv_mem_sch {χ : M → ℤˣ} {t g : M} {S : List M} :
    g ∈ itHvSch χ t S ↔ g = t * t ∨ ∃ s ∈ S, (χ s = 1 ∧ (g = s ∨ g = t * s * t)) ∨
      (χ s ≠ 1 ∧ (g = s * t ∨ g = t * s)) := by
  simp only [itHvSch, List.mem_cons, List.mem_flatMap]
  refine or_congr Iff.rfl (exists_congr fun s => and_congr_right fun _ => ?_)
  split_ifs with h <;> simp [h]

theorem it_units_cases (u : ℤˣ) : u = 1 ∨ u = -1 := Int.units_eq_one_or u

variable (χ : M → ℤˣ) {S : List M}

/-- A function that is multiplicative on the group of `S` maps `1` to `1` and inverses to
inverses there. -/
theorem it_hv_chi_one (hmul : ∀ x ∈ Subgroup.closure {s | s ∈ S},
    ∀ y ∈ Subgroup.closure {s | s ∈ S}, χ (x * y) = χ x * χ y) : χ 1 = 1 := by
  have h := hmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
  rw [one_mul] at h
  exact mul_eq_left.mp h.symm

theorem it_hv_chi_inv (hmul : ∀ x ∈ Subgroup.closure {s | s ∈ S},
    ∀ y ∈ Subgroup.closure {s | s ∈ S}, χ (x * y) = χ x * χ y)
    {x : M} (hx : x ∈ Subgroup.closure {s | s ∈ S}) : χ x⁻¹ = (χ x)⁻¹ := by
  have h := hmul x hx x⁻¹ (Subgroup.inv_mem _ hx)
  rw [mul_inv_cancel, it_hv_chi_one χ hmul] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

/-- **Schreier's lemma for index two.** If `χ` is multiplicative on the group of `S` with values
`±1`, and `t` is in that group with `χ t = -1`, then `itHvSch χ t S` generates the kernel of `χ`
in the group of `S`. The cosets of the kernel are `1` and `t`; the proof goes along a word in `S`
and keeps the invariant "`x` is in the closure if `χ x = 1`, `x t` is if `χ x = -1`". -/
theorem it_hv_schreier
    (hmul : ∀ x ∈ Subgroup.closure {s | s ∈ S},
      ∀ y ∈ Subgroup.closure {s | s ∈ S}, χ (x * y) = χ x * χ y)
    {t : M} (ht : t ∈ Subgroup.closure {s | s ∈ S}) (hχt : χ t = -1) (g : M) :
    g ∈ Subgroup.closure {g | g ∈ itHvSch χ t S} ↔
      g ∈ Subgroup.closure {s | s ∈ S} ∧ χ g = 1 := by
  set G := Subgroup.closure {s | s ∈ S}
  set K := Subgroup.closure {g | g ∈ itHvSch χ t S}
  have mem : ∀ g, g ∈ itHvSch χ t S → g ∈ K := fun g h => Subgroup.subset_closure h
  have hsG : ∀ s ∈ S, s ∈ G := fun s hs => Subgroup.subset_closure hs
  have m2 : ∀ {a b : ℤˣ}, a = -1 → b = -1 → a * b = 1 := by
    rintro _ _ rfl rfl; decide
  -- the generators lie in the kernel
  have hKG : K ≤ G ⊓ (⊤ : Subgroup M) := by
    refine (Subgroup.closure_le _).2 fun g hg => ⟨?_, trivial⟩
    obtain rfl | ⟨s, hs, h⟩ := it_hv_mem_sch.1 hg
    · exact G.mul_mem ht ht
    · rcases h with ⟨-, h2 | h2⟩ | ⟨-, h2 | h2⟩ <;> rw [h2]
      · exact hsG s hs
      · exact G.mul_mem (G.mul_mem ht (hsG s hs)) ht
      · exact G.mul_mem (hsG s hs) ht
      · exact G.mul_mem ht (hsG s hs)
  have hKχ : ∀ g ∈ K, χ g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain rfl | ⟨s, hs, h⟩ := it_hv_mem_sch.1 hg
      · rw [hmul _ ht _ ht, hχt]; decide
      · have hs' := hsG s hs
        rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> rw [h2]
        · exact h1
        · rw [hmul _ (G.mul_mem ht hs') _ ht, hmul _ ht _ hs', hχt, h1]; decide
        · rw [hmul _ hs' _ ht, m2 ((it_units_cases _).resolve_left h1) hχt]
        · rw [hmul _ ht _ hs', m2 hχt ((it_units_cases _).resolve_left h1)]
    | one => exact it_hv_chi_one χ hmul
    | mul x y hx hy ihx ihy =>
      rw [hmul _ ((hKG hx).1) _ ((hKG hy).1), ihx, ihy, one_mul]
    | inv x hx ih => rw [it_hv_chi_inv χ hmul (hKG hx).1, ih, inv_one]
  refine ⟨fun hg => ⟨(hKG hg).1, hKχ g hg⟩, fun ⟨hg, hgχ⟩ => ?_⟩
  have htt : t * t ∈ K := mem _ (it_hv_mem_sch.2 (Or.inl rfl))
  have hK : ∀ s ∈ S, (χ s = 1 → s ∈ K ∧ t * s * t ∈ K) ∧
      (χ s = -1 → s * t ∈ K ∧ t * s ∈ K) := by
    intro s hs
    refine ⟨fun h1 => ⟨mem _ (it_hv_mem_sch.2 (Or.inr ⟨s, hs, Or.inl ⟨h1, Or.inl rfl⟩⟩)),
      mem _ (it_hv_mem_sch.2 (Or.inr ⟨s, hs, Or.inl ⟨h1, Or.inr rfl⟩⟩))⟩, fun h1 => ?_⟩
    have h1' : χ s ≠ 1 := by rw [h1]; decide
    exact ⟨mem _ (it_hv_mem_sch.2 (Or.inr ⟨s, hs, Or.inr ⟨h1', Or.inl rfl⟩⟩)),
      mem _ (it_hv_mem_sch.2 (Or.inr ⟨s, hs, Or.inr ⟨h1', Or.inr rfl⟩⟩))⟩
  -- `t⁻¹ s t = (t t)⁻¹ (t s t)` and `t⁻¹ s = (t t)⁻¹ (t s)`
  have e1 : ∀ s : M, t⁻¹ * s * t = (t * t)⁻¹ * (t * s * t) := fun s => by group
  have e2 : ∀ s : M, t⁻¹ * s = (t * t)⁻¹ * (t * s) := fun s => by group
  have key : ∀ x ∈ G, (χ x = 1 → x ∈ K) ∧ (χ x = -1 → x * t ∈ K) := by
    intro x hx
    induction hx using Subgroup.closure_induction_right with
    | one =>
      refine ⟨fun _ => K.one_mem, fun h => ?_⟩
      rw [it_hv_chi_one χ hmul] at h; exact absurd h (by decide)
    | mul_right x hxG s hs ih =>
      have hsG' := hsG s hs
      obtain ⟨hs1, hs2⟩ := hK s hs
      have hχ := hmul x hxG s hsG'
      rcases it_units_cases (χ x) with hx | hx <;> rcases it_units_cases (χ s) with h | h
      · refine ⟨fun _ => K.mul_mem (ih.1 hx) (hs1 h).1, fun h' => ?_⟩
        rw [hχ, hx, h] at h'; exact absurd h' (by decide)
      · refine ⟨fun h' => ?_, fun _ => ?_⟩
        · rw [hχ, hx, h] at h'; exact absurd h' (by decide)
        · rw [mul_assoc]; exact K.mul_mem (ih.1 hx) (hs2 h).1
      · refine ⟨fun h' => ?_, fun _ => ?_⟩
        · rw [hχ, hx, h] at h'; exact absurd h' (by decide)
        · rw [show x * s * t = x * t * (t⁻¹ * s * t) by group, e1]
          exact K.mul_mem (ih.2 hx) (K.mul_mem (K.inv_mem htt) (hs1 h).2)
      · refine ⟨fun _ => ?_, fun h' => ?_⟩
        · rw [show x * s = x * t * (t⁻¹ * s) by group, e2]
          exact K.mul_mem (ih.2 hx) (K.mul_mem (K.inv_mem htt) (hs2 h).2)
        · rw [hχ, hx, h] at h'; exact absurd h' (by decide)
    | mul_inv_cancel x hxG s hs ih =>
      have hsG' := hsG s hs
      obtain ⟨hs1, hs2⟩ := hK s hs
      have hχ := hmul x hxG s⁻¹ (G.inv_mem hsG')
      rw [it_hv_chi_inv χ hmul hsG'] at hχ
      rcases it_units_cases (χ x) with hx | hx <;> rcases it_units_cases (χ s) with h | h
      · refine ⟨fun _ => K.mul_mem (ih.1 hx) (K.inv_mem (hs1 h).1), fun h' => ?_⟩
        rw [hχ, hx, h] at h'; exact absurd h' (by decide)
      · refine ⟨fun h' => ?_, fun _ => ?_⟩
        · rw [hχ, hx, h] at h'; exact absurd h' (by decide)
        · rw [show x * s⁻¹ * t = x * (t⁻¹ * s)⁻¹ by group, e2]
          exact K.mul_mem (ih.1 hx) (K.inv_mem (K.mul_mem (K.inv_mem htt) (hs2 h).2))
      · refine ⟨fun h' => ?_, fun _ => ?_⟩
        · rw [hχ, hx, h] at h'; exact absurd h' (by decide)
        · rw [show x * s⁻¹ * t = x * t * (t⁻¹ * s * t)⁻¹ by group, e1]
          exact K.mul_mem (ih.2 hx) (K.inv_mem (K.mul_mem (K.inv_mem htt) (hs1 h).2))
      · refine ⟨fun _ => ?_, fun h' => ?_⟩
        · rw [show x * s⁻¹ = x * t * (s * t)⁻¹ by group]
          exact K.mul_mem (ih.2 hx) (K.inv_mem (hs2 h).1)
        · rw [hχ, hx, h] at h'; exact absurd h' (by decide)
  exact (key g hg).1 hgχ

/-- **Without an odd generator the kernel is everything.** -/
theorem it_hv_chi_all
    (hmul : ∀ x ∈ Subgroup.closure {s | s ∈ S},
      ∀ y ∈ Subgroup.closure {s | s ∈ S}, χ (x * y) = χ x * χ y)
    (hS : ∀ s ∈ S, χ s = 1) : ∀ g ∈ Subgroup.closure {s | s ∈ S}, χ g = 1 := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hS g hg
  | one => exact it_hv_chi_one χ hmul
  | mul x y hx hy ihx ihy => rw [hmul _ hx _ hy, ihx, ihy, one_mul]
  | inv x hx ih => rw [it_hv_chi_inv χ hmul hx, ih, inv_one]

end Schreier

/-! ### The sign of the `Φ`-side -/

section Side

variable {q : ℕ}

open Classical in
/-- **The `Φ`-side of a label permutation**: `σ` on `Φ` and the identity elsewhere, when `σ`
maps `Φ` onto itself; otherwise `1`. -/
noncomputable def itHvR (Φ : Finset (Fin q)) (σ : Perm (Fin q)) : Perm (Fin q) :=
  if h : ∀ a, σ a ∈ Φ ↔ a ∈ Φ then ofSubtype (σ.subtypePerm h) else 1

/-- The sign of the `Φ`-side of the label part of a pair. -/
noncomputable def itHvChi (Φ : Finset (Fin q)) (p : Perm (Fin k) × Perm (Fin q)) : ℤˣ :=
  sign (itHvR Φ p.2)

theorem itHvR_apply {Φ : Finset (Fin q)} {σ : Perm (Fin q)} (h : ∀ a, σ a ∈ Φ ↔ a ∈ Φ)
    (a : Fin q) : itHvR Φ σ a = if a ∈ Φ then σ a else a := by
  classical
  rw [itHvR, dif_pos h]
  split_ifs with ha
  · exact ofSubtype_apply_of_mem _ ha
  · exact ofSubtype_apply_of_not_mem _ ha

theorem itHvR_mul {Φ : Finset (Fin q)} {σ τ : Perm (Fin q)} (hσ : ∀ a, σ a ∈ Φ ↔ a ∈ Φ)
    (hτ : ∀ a, τ a ∈ Φ ↔ a ∈ Φ) : itHvR Φ (σ * τ) = itHvR Φ σ * itHvR Φ τ := by
  have hστ : ∀ a, (σ * τ) a ∈ Φ ↔ a ∈ Φ := fun a => (hσ (τ a)).trans (hτ a)
  ext a
  rw [Perm.mul_apply, itHvR_apply hστ, itHvR_apply hσ, itHvR_apply hτ]
  by_cases ha : a ∈ Φ
  · rw [if_pos ha, if_pos ha, if_pos ((hτ a).2 ha)]; rfl
  · rw [if_neg ha, if_neg ha, if_neg ha]

/-- On a permitted permutation, the sign of the `Φ`-side is the sign of the side action. -/
theorem itHvR_sign_side {Φ : Finset (Fin q)} (g : permitted Φ Φᶜ) (h : ∀ a, (g : Perm (Fin q)) a ∈ Φ ↔ a ∈ Φ) :
    sign (itHvR Φ (g : Perm (Fin q))) = sign (sideAction g).1 := by
  classical
  rw [itHvR, dif_pos h, sign_ofSubtype]
  congr 1

/-- A permutation in the setwise stabilizer of `Φ` maps `Φ` onto itself, pointwise. -/
theorem it_hv_stab_iff {Φ : Finset (Fin q)} {σ : Perm (Fin q)}
    (h : σ ∈ MulAction.stabilizer (Perm (Fin q)) (Φ : Set (Fin q))) (a : Fin q) :
    σ a ∈ Φ ↔ a ∈ Φ := by
  have h' : σ • (Φ : Set (Fin q)) = Φ := h
  constructor
  · intro ha
    have : σ a ∈ σ • (Φ : Set (Fin q)) := by rw [h']; exact ha
    obtain ⟨b, hb, hba⟩ := this
    have hba' : σ b = σ a := hba
    exact (σ.injective hba') ▸ hb
  · intro ha
    have : σ a ∈ σ • (Φ : Set (Fin q)) := Set.smul_mem_smul_set ha
    rw [h'] at this; exact this

/-- A permutation that maps `Φ` onto itself is in the setwise stabilizers of `Φ` and `Φᶜ`. -/
theorem it_hv_mem_sides {Φ : Finset (Fin q)} {σ : Perm (Fin q)} (h : ∀ a, σ a ∈ Φ ↔ a ∈ Φ) :
    σ ∈ sides Φ Φᶜ := by
  refine mem_sides_of_maps σ (fun a ha => (h a).2 ha) fun a ha => ?_
  rw [Finset.mem_compl] at ha ⊢
  exact fun h' => ha ((h a).1 h')

/-- An even permutation that maps `Φ` onto itself is in `Alt(Φ) × Alt(C)` exactly when its
`Φ`-side is even. -/
theorem it_hv_evenSides_iff {Φ : Finset (Fin q)} (σ : alternatingGroup (Fin q))
    (h : ∀ a, (σ : Perm (Fin q)) a ∈ Φ ↔ a ∈ Φ) :
    σ ∈ evenSides Φ Φᶜ ↔ sign (itHvR Φ (σ : Perm (Fin q))) = 1 := by
  have hp : σ ∈ permitted Φ Φᶜ := it_hv_mem_sides h
  rw [show σ = ((⟨σ, hp⟩ : permitted Φ Φᶜ) : alternatingGroup (Fin q)) from rfl,
    mem_evenSides_compl_iff, itHvR_sign_side ⟨σ, hp⟩ h]

/-- **An even permutation that fixes `Φ` pointwise is in `Alt(Φ) × Alt(C)`.** -/
theorem it_hv_fix_evenSides {Φ : Finset (Fin q)} (σ : alternatingGroup (Fin q))
    (h : ∀ a ∈ Φ, (σ : Perm (Fin q)) a = a) : σ ∈ evenSides Φ Φᶜ := by
  have hi : ∀ a, (σ : Perm (Fin q)) a ∈ Φ ↔ a ∈ Φ := fun a => by
    constructor
    · intro ha
      by_contra hn
      have h2 := h _ ha
      exact hn (((σ : Perm (Fin q)).injective h2) ▸ ha)
    · intro ha; rw [h a ha]; exact ha
  rw [it_hv_evenSides_iff σ hi]
  have : itHvR Φ (σ : Perm (Fin q)) = 1 := by
    ext a
    rw [itHvR_apply hi]
    split_ifs with ha
    · rw [h a ha]; rfl
    · rfl
  rw [this, Perm.sign_one]

/-- **The pairs of a group whose label images map `Φ` onto itself**: the sign of the `Φ`-side is
multiplicative there. -/
theorem it_hv_chi_mul {Φ : Finset (Fin q)} {fs : List (Perm (Fin k) × Perm (Fin q))}
    (hinv : ∀ σ ∈ gens (fs.map Prod.snd), ∀ a, σ a ∈ Φ ↔ a ∈ Φ) :
    ∀ x ∈ Subgroup.closure {p | p ∈ fs}, ∀ y ∈ Subgroup.closure {p | p ∈ fs},
      itHvChi Φ (x * y) = itHvChi Φ x * itHvChi Φ y := by
  intro x hx y hy
  have m : ∀ z ∈ Subgroup.closure {p | p ∈ fs}, z.2 ∈ gens (fs.map Prod.snd) := fun z hz => by
    rw [gens_snd]; exact ⟨z, hz, rfl⟩
  unfold itHvChi
  rw [Prod.snd_mul, itHvR_mul (hinv _ (m x hx)) (hinv _ (m y hy)), Perm.sign_mul]

end Side

/-! ### The groups `K` and `A` in graph form -/

section Graph

variable (e : Ω ≃ Fin k) {S : State Ω C} (L : GiantLabels S)

/-- `K = π⁻¹(1_Φ × Alt(C))`. -/
def itHvKer (Φ : Finset (Fin L.q)) : Subgroup (Perm Ω) :=
  L.lift (evenSides Φ Φᶜ ⊓ fixingSubgroup (alternatingGroup (Fin L.q)) (Φ : Set (Fin L.q)))

variable {e L}

/-- **The kernel `K` is the part of `G` whose label image fixes `Φ` pointwise**: a pointwise
stabilizer of the label points of `Φ` in the graph group of `G` gives its graph. -/
theorem it_hv_ker_graph {Φ : Finset (Fin L.q)} {l : List (Fin L.q)} (hl : ∀ a, a ∈ l ↔ a ∈ Φ)
    {ps qs : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ fixPts k L.q (labPts k l)) :
    PairGens e L (itHvKer L Φ) qs := by
  unfold PairGens at *
  rw [hqs, hps]
  ext p
  rw [Subgroup.mem_inf, mem_fixPts_labPts, mem_graphOf, mem_graphOf]
  constructor
  · rintro ⟨⟨g, hg, -, h1, h2⟩, hfix⟩
    refine ⟨g, hg, (L.mem_lift).2 ⟨hg, ?_⟩, h1, h2⟩
    have hf : ∀ a ∈ Φ, ((L.π ⟨g, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) a = a :=
      fun a ha => by rw [h2]; exact hfix a ((hl a).2 ha)
    refine ⟨it_hv_fix_evenSides _ hf, ?_⟩
    show _ ∈ fixingSubgroup _ _
    rw [mem_fixingSubgroup_iff]
    intro a ha
    exact hf a ha
  · rintro ⟨g, hg, hK, h1, h2⟩
    refine ⟨⟨g, hg, hg, h1, h2⟩, fun c hc => ?_⟩
    obtain ⟨hg', hE⟩ := (L.mem_lift).1 hK
    have := (mem_fixingSubgroup_iff _).1 hE.2 c ((hl c).1 hc)
    rw [← h2]
    exact this

/-- **`A = certLift ⊓ π⁻¹(Alt(Φ) × Alt(C))` in graph form**: the pairs of the graph of a group
`F ≤ G` whose `Φ`-side is even, when every label image of `F` maps `Φ` onto itself. -/
theorem it_hv_A_graph {F : Subgroup (Perm Ω)} {Φ : Finset (Fin L.q)}
    {fs : List (Perm (Fin k) × Perm (Fin L.q))} (hfs : PairGens e L F fs)
    (hinv : ∀ σ ∈ gens (fs.map Prod.snd), ∀ a, σ a ∈ Φ ↔ a ∈ Φ) (p : Perm (Fin k) × Perm (Fin L.q)) :
    p ∈ graphOf e L (F ⊓ L.lift (evenSides Φ Φᶜ)) ↔
      p ∈ Subgroup.closure {p | p ∈ fs} ∧ itHvChi Φ p = 1 := by
  rw [hfs, mem_graphOf, mem_graphOf]
  constructor
  · rintro ⟨g, hg, ⟨hF, hE⟩, h1, h2⟩
    have hσ : p.2 ∈ gens (fs.map Prod.snd) := (mem_gens_snd hfs p.2).2 ⟨g, hg, hF, h2⟩
    obtain ⟨hg', hE'⟩ := (L.mem_lift).1 hE
    have hi := hinv _ hσ
    rw [← h2] at hi
    refine ⟨⟨g, hg, hF, h1, h2⟩, ?_⟩
    unfold itHvChi
    rw [← h2]
    exact (it_hv_evenSides_iff _ hi).1 hE'
  · rintro ⟨⟨g, hg, hF, h1, h2⟩, hχ⟩
    have hσ : p.2 ∈ gens (fs.map Prod.snd) := (mem_gens_snd hfs p.2).2 ⟨g, hg, hF, h2⟩
    have hi := hinv _ hσ
    rw [← h2] at hi
    refine ⟨g, hg, ⟨hF, (L.mem_lift).2 ⟨hg, (it_hv_evenSides_iff _ hi).2 ?_⟩⟩, h1, h2⟩
    unfold itHvChi at hχ
    rw [h2]; exact hχ

/-- The label images of a group map its dominant orbit onto itself (`apply_mem_domSet`). -/
theorem it_hv_dom_inv (H : Subgroup (Perm (Fin L.q))) {σ : Perm (Fin L.q)} (hσ : σ ∈ H)
    (a : Fin L.q) : σ a ∈ domSet H ↔ a ∈ domSet H := by
  constructor
  · intro h
    have := apply_mem_domSet (H := H) (H.inv_mem hσ) h
    rwa [Perm.inv_apply_self] at this
  · exact apply_mem_domSet (H := H) hσ

end Graph

/-! ### The pieces -/

section Piece

variable {S : State Ω C} {L : GiantLabels S} (H : Halving S L)

/-- **`K` is normal in `H₀`**: conjugation by an element of `H₀` keeps the label image in
`Alt(Φ) × Alt(C)` and keeps `Φ` fixed pointwise, since the label image of `H₀` maps `Φ` onto
itself. -/
theorem it_hv_ker_conj {g k' : Perm Ω} (hg : g ∈ H.even) (hk : k' ∈ H.ker) :
    g * k' * g⁻¹ ∈ H.ker := by
  obtain ⟨hgG, hgE⟩ := (L.mem_lift).1 hg
  obtain ⟨hkG, hkE, hkF⟩ := (L.mem_lift).1 hk
  have hm : g * k' * g⁻¹ ∈ S.G := S.G.mul_mem (S.G.mul_mem hgG hkG) (S.G.inv_mem hgG)
  refine (L.mem_lift).2 ⟨hm, ?_, ?_⟩
  · have e : L.π ⟨g * k' * g⁻¹, hm⟩ = L.π ⟨g, hgG⟩ * L.π ⟨k', hkG⟩ * (L.π ⟨g, hgG⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]
    exact (evenSides H.Φ H.Φᶜ).mul_mem ((evenSides H.Φ H.Φᶜ).mul_mem hgE hkE)
      ((evenSides H.Φ H.Φᶜ).inv_mem hgE)
  · have e : L.π ⟨g * k' * g⁻¹, hm⟩ = L.π ⟨g, hgG⟩ * L.π ⟨k', hkG⟩ * (L.π ⟨g, hgG⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    show _ ∈ fixingSubgroup _ _
    rw [e, mem_fixingSubgroup_iff]
    intro a ha
    have hst : ((L.π ⟨g, hgG⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
        MulAction.stabilizer (Perm (Fin L.q)) (H.Φ : Set (Fin L.q)) := (evenSides_le hgE).1
    have hinv := it_hv_stab_iff hst
    set σ := ((L.π ⟨g, hgG⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q))
    have ha' : σ⁻¹ a ∈ H.Φ := (hinv _).1 (by rw [Perm.apply_inv_self]; exact ha)
    have hfix := (mem_fixingSubgroup_iff _).1 hkF _ ha'
    have hfix' : ((L.π ⟨k', hkG⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) (σ⁻¹ a) =
        σ⁻¹ a := hfix
    show ((L.π ⟨g, hgG⟩ * L.π ⟨k', hkG⟩ * (L.π ⟨g, hgG⟩)⁻¹ : alternatingGroup (Fin L.q)) :
      Perm (Fin L.q)) a = a
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [hfix']
    exact Perm.apply_inv_self σ a

/-- The automorphism group `Aut_K(x)` of the kernel state. -/
noncomputable def itHvAK : Subgroup (Perm Ω) :=
  autGroup H.ker S.dom (S.dom_inv.mono H.ker_le) S.x

/-- **`A` normalizes `Aut_K(x)`**: `A ≤ H₀` normalizes `K`, and `A` preserves `x` on the
domain. -/
theorem it_hv_A_normalizes (hA : H.A ≤ H.even) (hAx : ∀ a ∈ H.A, ∀ v ∈ S.dom, S.x (a v) = S.x v) :
    H.A ≤ Subgroup.normalizer (itHvAK H : Set (Perm Ω)) := by
  have hD := S.dom_inv
  have key : ∀ a ∈ H.A, ∀ g ∈ itHvAK H, a * g * a⁻¹ ∈ itHvAK H := by
    intro a ha g hg
    obtain ⟨hgK, hgx⟩ := hg
    have haG : a ∈ S.G := ((L.mem_lift).1 (hA ha)).1
    refine ⟨it_hv_ker_conj H (hA ha) hgK, fun v hv => ?_⟩
    have h1 : a⁻¹ v ∈ S.dom := hD.inv_mem haG hv
    have h2 : g (a⁻¹ v) ∈ S.dom := (hD g (H.ker_le hgK) _).2 h1
    have h3 := hAx a ha _ h2
    have h4 := hgx _ h1
    have h5 := hAx a ha _ h1
    rw [Perm.apply_inv_self] at h5
    simp only [Perm.mul_apply]
    rw [h3, h4, h5]
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key a ha g, fun h => ?_⟩
  have := key a⁻¹ (H.A.inv_mem ha) _ h
  simpa [mul_assoc] using this

/-- `Aut_K(x) · A` is the group generated by both. -/
theorem it_hv_AK_mul (hA : H.A ≤ H.even) (hAx : ∀ a ∈ H.A, ∀ v ∈ S.dom, S.x (a v) = S.x v) :
    ((itHvAK H : Set (Perm Ω)) * (H.A : Set (Perm Ω))) = ((itHvAK H ⊔ H.A : Subgroup (Perm Ω)) :
      Set (Perm Ω)) :=
  (Subgroup.coe_mul_of_right_le_normalizer_left _ _ (it_hv_A_normalizes H hA hAx)).symm

variable (e : Ω ≃ Fin k)

/-- A canonical answer of a subgroup has the generators of the subgroup's image. -/
theorem it_hv_ansC_group {G : Subgroup (Perm Ω)} {x : Perm (Fin k)} {gs : List (Perm (Fin k))}
    (h : toFin e '' (G : Set (Perm Ω)) = x • (gens gs : Set (Perm (Fin k)))) :
    gens gs = groupFin e G := by
  have h1 : (1 : Perm (Fin k)) ∈ x • (gens gs : Set (Perm (Fin k))) := by
    rw [← h]; exact ⟨1, G.one_mem, map_one _⟩
  obtain ⟨y, hy, hxy⟩ := h1
  replace hxy : x * y = 1 := hxy
  have hx : x ∈ gens gs := by
    have : x = y⁻¹ := eq_inv_of_mul_eq_one_left hxy
    rw [this]; exact (gens gs).inv_mem hy
  have hs : x • (gens gs : Set (Perm (Fin k))) = gens gs := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (gens gs).mul_mem hx hw
    · intro hz
      exact ⟨x⁻¹ * z, (gens gs).mul_mem ((gens gs).inv_mem hx) hz, by simp⟩
  rw [hs] at h
  ext z
  constructor
  · intro hz
    rw [← SetLike.mem_coe, ← h] at hz
    obtain ⟨g, hg, rfl⟩ := hz
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rw [← SetLike.mem_coe, ← h]
    exact ⟨g, hg, rfl⟩

/-- **The piece of a parity class, in combine form.** Let `u₀` be a canonical answer
`[x₀, ⟨gs₀⟩]` of `Aut_K(x)` and `u₁ = [x₁, ⟨gs₁⟩]` a nonempty canonical answer of the
`K`-transporters to `z`. Then the piece `ρ b · Aut_K(x) · A` is the coset of `e ρ · x₁` of the
group generated by `gs₀` and generators `gA` of `A`. -/
theorem it_hv_piece_some (hA : H.A ≤ H.even) (hAx : ∀ a ∈ H.A, ∀ v ∈ S.dom, S.x (a v) = S.x v)
    (ρ : Perm Ω) (z : Ω → C) {x₀ x₁ : Perm (Fin k)} {gs₀ gs₁ : List (Perm (Fin k))}
    (h₀ : toFin e '' (H.kerState S.x).answer = x₀ • (gens gs₀ : Set (Perm (Fin k))))
    (h₁ : toFin e '' (H.kerState z).answer = x₁ • (gens gs₁ : Set (Perm (Fin k))))
    {gA : List (Perm (Fin k))} (hgA : gens gA = groupFin e H.A) :
    ceSet (toFin e ρ * x₁, some (1, gs₀ ++ gA)) =
      toFin e '' H.piece ρ (H.kerState S.x).answer (H.kerState z).answer := by
  have hD : Invariant H.ker S.dom := S.dom_inv.mono H.ker_le
  have hAK : (H.kerState S.x).answer = (itHvAK H : Set (Perm Ω)) := by
    rw [Halving.kerState_answer]; rfl
  rw [hAK] at h₀ ⊢
  have hg0 := it_hv_ansC_group e h₀
  -- the group of the piece
  have hgen : gens (gs₀ ++ gA) = groupFin e (itHvAK H ⊔ H.A) := by
    unfold gens groupFin at *
    rw [Subgroup.map_sup, ← hg0, ← hgA, ← Subgroup.closure_union]
    congr 1
    ext g; simp
  -- `x₁` is the image of a transporter `b'`
  have hx1 : x₁ ∈ toFin e '' (H.kerState z).answer := by
    rw [h₁]; exact ⟨1, (gens gs₁).one_mem, mul_one _⟩
  obtain ⟨b', hb', hb'x⟩ := hx1
  have hne : (H.kerState z).answer.Nonempty := ⟨b', hb'⟩
  rw [Halving.piece, dif_pos hne, it_hv_AK_mul H hA hAx, image_toFin_smul]
  set b := hne.some
  have hb : b ∈ (H.kerState z).answer := hne.some_mem
  have hB : (H.kerState z).answer = b • (itHvAK H : Set (Perm Ω)) := by
    rw [Halving.kerState_answer] at hb ⊢
    exact answer_eq_smul_aut hD hb
  -- `b⁻¹ b'` lies in `Aut_K(x)`
  have hbb : b⁻¹ * b' ∈ itHvAK H := by
    rw [hB] at hb'
    obtain ⟨c, hc, rfl⟩ := hb'
    simpa [smul_eq_mul] using hc
  set G' := itHvAK H ⊔ H.A
  have hbbG : b⁻¹ * b' ∈ G' := Subgroup.mem_sup_left hbb
  have himg : toFin e '' (G' : Set (Perm Ω)) = (groupFin e G' : Set (Perm (Fin k))) := by
    ext y; simp [groupFin]
  rw [himg, ceSet, accSet, one_smul, hgen, ← hb'x, ← map_mul]
  show toFin e (ρ * b') • (groupFin e G' : Set (Perm (Fin k))) = _
  -- both cosets are equal since `b⁻¹ b' ∈ G'`
  have hc : toFin e (b⁻¹ * b') ∈ groupFin e G' := ⟨_, hbbG, rfl⟩
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨toFin e (b⁻¹ * b') * w, (groupFin e G').mul_mem hc hw, ?_⟩
    simp only [smul_eq_mul, map_mul, map_inv]
    group
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(toFin e (b⁻¹ * b'))⁻¹ * w, (groupFin e G').mul_mem ((groupFin e G').inv_mem hc) hw, ?_⟩
    simp only [smul_eq_mul, map_mul, map_inv]
    group

/-- **An empty transporter set gives the empty piece.** -/
theorem it_hv_piece_none (ρ : Perm Ω) (z : Ω → C) (h₁ : (H.kerState z).answer = ∅) :
    ceSet ((1 : Perm (Fin k)), (none : Acc k)) =
      toFin e '' H.piece ρ (H.kerState S.x).answer (H.kerState z).answer := by
  have hne : ¬ (H.kerState z).answer.Nonempty := by
    rw [h₁]; exact Set.not_nonempty_empty
  rw [Halving.piece, dif_neg hne, Set.image_empty, ceSet, accSet, Set.smul_set_empty]

end Piece

/-! ### The calls -/

section Calls

variable {S : State Ω C} {L : GiantLabels S}

/-- **The kernel calls may be made**: they are charged calls (Lemma A.11: "inherited half-domain
calls"), so `Good` for `Continue` with a smaller measure. -/
theorem it_hv_call [Finite Ω] (hgood : Good P₀ .giant S) (H : Halving S L) (hv : H.Valid P₀)
    (z : Ω → C) :
    Good P₀ .cont (H.kerState z) ∧ MLt (measure P₀ .cont (H.kerState z)) (measure P₀ .giant S) :=
  chargedCall_good_mlt hgood ⟨by simp, by simpa using H.ker_le, by simp, by simp, fun v hv' =>
    Or.inl (by simp only [Halving.kerState_G]; exact hv.orb_small v (by simpa using hv'))⟩

/-- **The value of a kernel call is canonical**: the value of the parent with the group of `K`,
the colors `z` as target, no row record, floor mode off and `h = 2` (`State.queryChild`). -/
theorem it_hv_canon {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ}
    (hS : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (H : Halving S L) {z : Ω → C} {gv' yv' : Val} (hg : GroupValC k gv' (groupFin e H.ker))
    (hy : ColorVal e c yv' z) (hz : ∀ a, c (z a) < 2 * k) :
    Canon e c (winVal' k gv' dv xv yv' hv N) (H.kerState z) := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, hd, hx, -, hh', -, heq⟩ := hS.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, rfl, rfl, -, rfl, -, -, -, hNe, -⟩ := heq
  refine ⟨⟨gv', dv, xv, yv', hv, .list [], ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩,
    fun a => ⟨(hS.colors a).1, hz a⟩, hS.fits, ⟨hS.small.1, hS.small.2.1, fun R hR => by cases hR⟩⟩
  · simpa using hg
  · simpa using hd
  · simpa using hx
  · simpa using hy
  · simpa using hh'
  · simp only [winVal', Halving.kerState, State.queryChild_floor, State.queryChild_h,
      State.queryChild_N, hNe]

end Calls

end GI.Impl
