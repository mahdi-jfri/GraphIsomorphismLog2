import Workspace.PrimitiveWidth
import Workspace.CoherentCliqueBound
import Workspace.PairActions
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The width of a configuration automorphism group (Lemma A.12, cap bound)

A group `K ≤ Sym(Γ)` that preserves the image `C = ι(Fin n)` of a nontrivial
homogeneous coherent configuration and its colors has alternating-section width
at most `β q`, `q = |Γ|`, when `|C| ≥ δ q`, `β > 1 - δ`, `β ≥ 1/2 + 1/N` and `q` is
large. This is the cap argument of the proof of Lemma A.12.
-/

namespace GI.ExactConfiguration

open Equiv GI.PairRefinement

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {n : ℕ}

/-- `g` preserves the configuration `c`, placed on `C = ι(Fin n) ⊆ Γ`: it maps `C`
onto itself and keeps the colors of pairs in `C`. -/
def PreservesConfig (ι : Fin n ↪ Γ) (c : Coloring n) (side : Bool) (g : Perm Γ) : Prop :=
  (∀ a, g a ∈ Set.range ι ↔ a ∈ Set.range ι) ∧
    ∀ a b a' b' : Fin n, g (ι a) = ι a' → g (ι b) = ι b' → c (side, a', b') = c (side, a, b)

/-- The configuration group as a subgroup of `Sym(Γ)`. -/
def configGroup (ι : Fin n ↪ Γ) (c : Coloring n) (side : Bool) : Subgroup (Perm Γ) where
  carrier := {g | PreservesConfig ι c side g}
  one_mem' := ⟨fun _ => Iff.rfl, fun a b a' b' ha hb => by
    have ha' : a = a' := ι.injective ha
    have hb' : b = b' := ι.injective hb
    rw [ha', hb']⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun a => (hg1 _).trans (hh1 a), fun a b a' b' ha hb => ?_⟩
    obtain ⟨a'', ha''⟩ := (hh1 (ι a)).mpr ⟨a, rfl⟩
    obtain ⟨b'', hb''⟩ := (hh1 (ι b)).mpr ⟨b, rfl⟩
    have e1 := hh2 a b a'' b'' ha''.symm hb''.symm
    have e2 := hg2 a'' b'' a' b' (by rw [ha'']; exact ha) (by rw [hb'']; exact hb)
    exact e2.trans e1
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun a => ?_, fun a b a' b' ha hb => ?_⟩
    · have := hg1 (g⁻¹ a)
      rw [Perm.apply_inv_self] at this
      exact this.symm
    · have ha2 : g (ι a') = ι a := by rw [← ha, Perm.apply_inv_self]
      have hb2 : g (ι b') = ι b := by rw [← hb, Perm.apply_inv_self]
      exact (hg2 a' b' a b ha2 hb2).symm

/-- The isomorphism set of two aligned configurations on `C = ι(Fin n)`: permutations
of `Γ` that map `C` onto itself and carry the source colors to the target colors. -/
def configTransporter (ι : Fin n ↪ Γ) (c : Coloring n) (source target : Bool) :
    Set (Perm Γ) :=
  {g | (∀ a, g a ∈ Set.range ι ↔ a ∈ Set.range ι) ∧
    ∀ a b a' b' : Fin n, g (ι a) = ι a' → g (ι b) = ι b' →
      c (target, a', b') = c (source, a, b)}

omit [Fintype Γ] [DecidableEq Γ] in
/-- A nonempty configuration transporter is a left coset of the configuration group. -/
theorem configTransporter_coset (ι : Fin n ↪ Γ) (c : Coloring n) (source target : Bool)
    {g₀ : Perm Γ} (h₀ : g₀ ∈ configTransporter ι c source target) (g : Perm Γ) :
    g ∈ configTransporter ι c source target ↔ g₀⁻¹ * g ∈ configGroup ι c source := by
  obtain ⟨r₀, c₀⟩ := h₀
  have r₀' : ∀ a, g₀⁻¹ a ∈ Set.range ι ↔ a ∈ Set.range ι := by
    intro a
    have := r₀ (g₀⁻¹ a)
    rw [Perm.apply_inv_self] at this
    exact this.symm
  constructor
  · rintro ⟨r, cg⟩
    refine ⟨fun a => (r₀' _).trans (r a), fun a b a' b' ha hb => ?_⟩
    have ha' : g (ι a) = g₀ (ι a') := by rw [← ha]; simp [Perm.mul_apply]
    have hb' : g (ι b) = g₀ (ι b') := by rw [← hb]; simp [Perm.mul_apply]
    obtain ⟨a'', ha''⟩ := (r₀ (ι a')).mpr ⟨a', rfl⟩
    obtain ⟨b'', hb''⟩ := (r₀ (ι b')).mpr ⟨b', rfl⟩
    have e1 := cg a b a'' b'' (ha'.trans ha''.symm) (hb'.trans hb''.symm)
    have e2 := c₀ a' b' a'' b'' ha''.symm hb''.symm
    exact e2.symm.trans e1
  · rintro ⟨r, cg⟩
    have hg : g = g₀ * (g₀⁻¹ * g) := by group
    refine ⟨fun a => ?_, fun a b a' b' ha hb => ?_⟩
    · rw [hg, Perm.mul_apply]
      exact (r₀ _).trans (r a)
    · obtain ⟨a'', ha''⟩ := (r (ι a)).mpr ⟨a, rfl⟩
      obtain ⟨b'', hb''⟩ := (r (ι b)).mpr ⟨b, rfl⟩
      have e1 := cg a b a'' b'' ha''.symm hb''.symm
      have ha2 : g₀ (ι a'') = ι a' := by
        rw [ha'', ← ha, Perm.mul_apply, Perm.apply_inv_self]
      have hb2 : g₀ (ι b'') = ι b' := by
        rw [hb'', ← hb, Perm.mul_apply, Perm.apply_inv_self]
      exact (c₀ a'' b'' a' b' ha2 hb2).trans e1

/-- **The cap bound of Lemma A.12.** -/
theorem config_cap (c : Coloring n) (hc : Coherent c) (side : Bool)
    (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side) (ι : Fin n ↪ Γ)
    (K : Subgroup (Perm Γ)) (hK : K ≤ configGroup ι c side)
    {δ β : ℝ} {N : ℕ} (hN : 4 ≤ N) (hβN : 1 / 2 + 1 / (N : ℝ) ≤ β) (hδβ : 1 - δ < β)
    (hC : δ * Fintype.card Γ ≤ n) (hq : 2 * (4 * 4 ^ N + 8) ≤ Fintype.card Γ) :
    SectionCaps.Cap K ⌊β * Fintype.card Γ⌋₊ := by
  classical
  set q := Fintype.card Γ with hqdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hβ12 : (1 : ℝ) / 2 ≤ β := by
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  -- Points of `C` and points outside `C` stay apart under `K`.
  have hKC : ∀ g : K, ∀ x : Γ, (g : Perm Γ) x ∈ Set.range ι ↔ x ∈ Set.range ι :=
    fun g x => (hK g.property).1 x
  by_cases hbig : ∃ a : Γ, β * q < Nat.card (MulAction.orbit K a)
  swap
  · -- "If every `K`-orbit has size at most `β q`, then `K` embeds in a product of
    -- symmetric groups of those degrees."
    push Not at hbig
    apply GI.Carrier.cap_of_fixed_labels K.subtype Subtype.val_injective
      (fun x => MulAction.orbit K x)
    · intro g x
      exact MulAction.orbit_smul g x
    · intro b
      by_cases hb : ∃ a, MulAction.orbit K a = b
      · obtain ⟨a, rfl⟩ := hb
        have e : Nat.card {x // MulAction.orbit K x = MulAction.orbit K a} =
            Nat.card (MulAction.orbit K a) :=
          Nat.card_congr (Equiv.subtypeEquivRight fun x => MulAction.orbit_eq_iff)
        rw [e]
        exact Nat.le_floor (hbig a)
      · push Not at hb
        have : IsEmpty {x // MulAction.orbit K x = b} := ⟨fun x => hb x.val x.property⟩
        rw [Nat.card_of_isEmpty]
        exact Nat.zero_le _
  obtain ⟨a, ha⟩ := hbig
  set O := MulAction.orbit K a with hO
  -- "Otherwise its unique dominant orbit `D` lies in `C`": the outer points number
  -- at most `(1 - δ) q < β q`.
  have haC : a ∈ Set.range ι := by
    by_contra haC
    have hsub : ∀ x : O, x.val ∉ Set.range ι := by
      rintro ⟨x, g, rfl⟩
      exact fun hx => haC ((hKC g a).mp hx)
    have hle : Nat.card O ≤ Fintype.card {x : Γ // x ∉ Set.range ι} :=
      Nat.card_eq_fintype_card (α := O) ▸
        Fintype.card_le_of_injective (fun x : O => (⟨x.val, hsub x⟩ : {x : Γ // x ∉ Set.range ι}))
          (by intro x y h; exact Subtype.ext (by simpa using congrArg Subtype.val h))
    have hcompl : Fintype.card {x : Γ // x ∉ Set.range ι} = q - n := by
      rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin]
    rw [hcompl] at hle
    have hnq : n ≤ q := by simpa using Fintype.card_le_of_injective ι ι.injective
    have hle' : (Nat.card O : ℝ) ≤ q - n := by
      have := (Nat.cast_le (α := ℝ)).mpr hle
      rwa [Nat.cast_sub hnq] at this
    nlinarith
  have hOC : ∀ x ∈ O, x ∈ Set.range ι := by
    rintro x ⟨g, rfl⟩
    exact (hKC g a).mpr haC
  set d := Nat.card O with hd
  have hdq : d ≤ q := by
    rw [hd, Nat.card_eq_fintype_card]; exact Fintype.card_subtype_le _
  have hdβ : β * q < d := ha
  -- The action on `D` and its image `P = K^D`.
  let ρ : K →* Perm O := MulAction.toPermHom K O
  let P : Subgroup (Perm O) := ρ.range
  -- "The kernel of this induced action has width at most `q - |D| < (1 - β) q`."
  have hker : SectionCaps.Cap ρ.rangeRestrict.ker (max 1 (q - d)) := by
    let label : Γ → Option Γ := fun x => if x ∈ O then some x else none
    apply GI.Carrier.cap_of_fixed_labels (K.subtype.comp ρ.rangeRestrict.ker.subtype)
      (Subtype.val_injective.comp Subtype.val_injective) label
    · intro g x
      have hg : ρ g.val = 1 := by
        have := g.property
        rw [MonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      by_cases hx : x ∈ O
      · have hfix : (g.val.val : Perm Γ) x = x := by
          have := congrArg (fun p : Perm O => (p ⟨x, hx⟩).val) hg
          exact this
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hfix]
      · have hgx : (g.val.val : Perm Γ) x ∉ O := by
          intro hm
          apply hx
          have := MulAction.orbit_smul g.val x
          have hx' : x ∈ MulAction.orbit K x := MulAction.mem_orbit_self x
          rw [← this] at hx'
          have e : MulAction.orbit K (g.val • x) = O := MulAction.orbit_eq_iff.mpr hm
          rw [e] at hx'
          exact hx'
        simp only [label, MonoidHom.comp_apply, Subgroup.coe_subtype, hx, hgx, if_false]
    · intro b
      rcases b with _ | y
      · have e : Nat.card {x // label x = none} = Fintype.card {x : Γ // x ∉ O} := by
          rw [Nat.card_eq_fintype_card]
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight fun x => by by_cases hx : x ∈ O <;> simp [label, hx]
        have hOd : Fintype.card O = d := by rw [hd, Nat.card_eq_fintype_card]
        rw [e, Fintype.card_subtype_compl, hOd]
        exact le_max_right _ _
      · have : Nat.card {x // label x = some y} ≤ 1 := by
          rw [Finite.card_le_one_iff_subsingleton]
          constructor
          rintro ⟨x, hx⟩ ⟨z, hz⟩
          apply Subtype.ext
          simp only [label] at hx hz
          split_ifs at hx hz
          simp_all
        exact le_max_of_le_left this
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
  have hkerq : max 1 (q - d) ≤ ⌊β * q⌋₊ := by
    apply max_le
    · apply Nat.le_floor
      push_cast
      nlinarith
    · apply Nat.le_floor
      rw [Nat.cast_sub hdq]
      nlinarith
  -- `P` is transitive on `D`.
  haveI hPtrans : MulAction.IsPretransitive P O := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K x y
    exact ⟨⟨ρ g, g, rfl⟩, hg⟩
  have hdlarge : 4 * 4 ^ N + 8 ≤ d := by
    have h1 : ((2 * (4 * 4 ^ N + 8) : ℕ) : ℝ) ≤ q := by exact_mod_cast hq
    have h2 : ((4 * 4 ^ N + 8 : ℕ) : ℝ) < d := by push_cast at h1 ⊢; nlinarith
    exact_mod_cast h2.le
  have hdcard : Fintype.card O = d := by rw [hd, Nat.card_eq_fintype_card]
  have himage : SectionCaps.Cap P ⌊β * q⌋₊ := by
    by_cases hprim : MulAction.IsPreprimitive P O
    · -- "If `P` is primitive, it cannot contain `Alt(D)`: its two-transitivity would
      -- make the configuration on `D` a clique, contrary to [H, Exercise 2.15]."
      have halt : ¬ alternatingGroup O ≤ P := by
        intro hle
        have h4 : 4 ≤ Fintype.card O := by omega
        obtain ⟨i₀, hi₀⟩ := haC
        -- a second point of `D`
        obtain ⟨y, hy, hya⟩ : ∃ y ∈ O, y ≠ a := by
          by_contra hcon
          push Not at hcon
          have : Fintype.card O ≤ 1 := Fintype.card_le_one_iff.mpr fun u v => Subtype.ext
            ((hcon u.val u.property).trans (hcon v.val v.property).symm)
          omega
        obtain ⟨j₀, hj₀⟩ := hOC y hy
        let S : Finset (Fin n) := Finset.univ.filter fun i => ι i ∈ O
        have hclique : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c (side, i, j) = c (side, i₀, j₀) := by
          intro i hi j hj hij
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
          have hne₀ : (⟨a, MulAction.mem_orbit_self a⟩ : O) ≠ ⟨y, hy⟩ :=
            fun h => hya (congrArg Subtype.val h).symm
          have hne : (⟨ι i, hi⟩ : O) ≠ ⟨ι j, hj⟩ :=
            fun h => hij (ι.injective (congrArg Subtype.val h))
          obtain ⟨σ, hσ1, hσ2⟩ := GI.Pairs.exists_even_pair_map h4 hne₀ hne
          obtain ⟨g, hg⟩ := hle σ.property
          have e1 : (g : Perm Γ) (ι i₀) = ι i := by
            have := congrArg (fun p : Perm O => (p ⟨a, MulAction.mem_orbit_self a⟩).val) hg
            simp only at this
            rw [hi₀]
            exact this.trans (congrArg Subtype.val hσ1)
          have e2 : (g : Perm Γ) (ι j₀) = ι j := by
            have := congrArg (fun p : Perm O => (p ⟨y, hy⟩).val) hg
            simp only at this
            rw [hj₀]
            exact this.trans (congrArg Subtype.val hσ2)
          exact (hK g.property).2 i₀ j₀ i j e1 e2
        have hhalf := coherent_clique_half c hc side hh hn S _ hclique
        have hScard : S.card = d := by
          rw [← hdcard, ← Set.toFinset_card]
          rw [← Finset.card_map ι]
          congr 1
          ext x
          simp only [S, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_toFinset]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact hi
          · intro hx
            obtain ⟨i, rfl⟩ := hOC x hx
            exact ⟨i, hx, rfl⟩
        rw [hScard] at hhalf
        have hnq : (n : ℝ) ≤ q := by exact_mod_cast (by simpa using Fintype.card_le_of_injective ι ι.injective)
        have : (2 * d : ℝ) ≤ n := by exact_mod_cast hhalf
        nlinarith
      have hcap := GI.PrimitiveWidth.primitive_cap hprim halt hN (by rw [hdcard]; exact hdlarge)
      apply SectionCaps.mono hcap
      apply Nat.le_floor
      rw [hdcard]
      have h1 : (((N + 2) * d / (2 * N) : ℕ) : ℝ) ≤ ((N + 2) * d : ℕ) / ((2 * N : ℕ) : ℝ) :=
        Nat.cast_div_le
      have h2 : (((N + 2) * d : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) = (1 / 2 + 1 / (N : ℝ)) * d := by
        push_cast; field_simp
      have h3 : (1 / 2 + 1 / (N : ℝ)) * d ≤ β * d :=
        mul_le_mul_of_nonneg_right hβN (Nat.cast_nonneg _)
      have h4 : β * (d : ℝ) ≤ β * q :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hdq) (by linarith)
      linarith
    · -- "If `P` is imprimitive, it embeds in `Sym(u) ≀ Sym(v)` ... its width is at most
      -- `q/2`."
      have hcap := GI.PrimitiveWidth.imprimitive_cap hprim
      apply SectionCaps.mono hcap
      apply Nat.le_floor
      rw [hdcard]
      have h1 : ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.cast_div_le
      have h2 : (d : ℝ) ≤ q := by exact_mod_cast hdq
      nlinarith
  -- "Extension closure bounds the width of `P`, and then of `K`, by `β q`."
  have hext := SectionCaps.extension ρ.rangeRestrict hker himage
  exact SectionCaps.mono hext (max_le hkerq le_rfl)

end GI.ExactConfiguration
