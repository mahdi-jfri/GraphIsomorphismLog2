module

public import Workspace.Impl.AggRectRepOut

@[expose] public section

/-!
# The orbit table of the base tuple

The program computes the orbit of the base tuple `(x, d₁, d₂)` (`rcRTup`) under the graph pairs
(`graphTup_spec`), as the list `Lk` of its keys `[g x, k + π g d₁, k + π g d₂]` (`RcRTab`). For
single labels it takes `d₁ = d₂ = a`. It reads two things off the table.

* **The entry at a position** (`rcRLook`): the first key with head `i`. For `i = g x` it is the key
  of some `g'` with `g' x = g x` (`rcR_look`).
* **The label action of an element** `h ∈ G` given on positions only (`rcRPiN`): this is how the
  program turns generators of `H` on positions back into graph pairs. For a label `j` it takes a
  key `(v₁, j, a)`, a key `(v₂, j, b)` with `b ≠ a`, and the keys at `h v₁`, `h v₂`. Their label
  sets are `{π h j, π h a}` and `{π h j, π h b}` (the stabilizer of `x` keeps `{d₁, d₂}`), and
  `π h j` is their common label (`rcR_piN`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {k : ℕ} (e : Ω ≃ Fin k)

/-- The label permutation of `g`. -/
abbrev rcRPi (L : GiantLabels S) (g : S.G) : Perm (Fin L.q) := (L.π g : Perm (Fin L.q))

/-- The key of the tuple of `g`: `[g x, k + π g d₁, k + π g d₂]`. -/
def rcRKeyOf (x : Ω) (d₁ d₂ : Fin L.q) (g : S.G) : List ℕ :=
  [(e ((g : Perm Ω) x) : ℕ), k + (rcRPi L g d₁ : ℕ), k + (rcRPi L g d₂ : ℕ)]

/-- **The orbit table**: its keys are the keys of the elements of `G`, and all of them occur. -/
structure RcRTab (x : Ω) (d₁ d₂ : Fin L.q) (Lk : List (List ℕ)) : Prop where
  mem : ∀ y ∈ Lk, ∃ g : S.G, y = rcRKeyOf e x d₁ d₂ g
  all : ∀ g : S.G, rcRKeyOf e x d₁ d₂ g ∈ Lk

/-- The first key with head `i`. -/
def rcRLook (Lk : List (List ℕ)) (i : ℕ) : List ℕ :=
  Lk.getD (Lk.findIdx fun y => y.getD 0 0 == i) []

/-- The first key with first label `t`. -/
def rcRLook1 (Lk : List (List ℕ)) (t : ℕ) : List ℕ :=
  Lk.getD (Lk.findIdx fun y => y.getD 1 0 == t) []

/-- The first key with first label `t` and second label not `a`. -/
def rcRLook2 (Lk : List (List ℕ)) (t a : ℕ) : List ℕ :=
  Lk.getD (Lk.findIdx fun y => y.getD 1 0 == t && !(y.getD 2 0 == a)) []

/-- **The label action read from the table**, for an element given on positions by `h`. -/
def rcRPiN (Lk : List (List ℕ)) (k : ℕ) (h : ℕ → ℕ) (j : ℕ) : ℕ :=
  (if (rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0))).getD 1 0 =
      (rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0))).getD 2 0 then
    (rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0))).getD 1 0
  else if (rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0))).getD 1 0 =
        (rcRLook Lk (h ((rcRLook2 Lk (k + j) ((rcRLook1 Lk (k + j)).getD 2 0)).getD 0 0))).getD 1 0 ∨
      (rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0))).getD 1 0 =
        (rcRLook Lk (h ((rcRLook2 Lk (k + j) ((rcRLook1 Lk (k + j)).getD 2 0)).getD 0 0))).getD 2 0
    then (rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0))).getD 1 0
  else (rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0))).getD 2 0) - k

/-! ### Finding a key -/

/-- The first entry passing a test, when some entry passes it. -/
theorem rcR_find {Lk : List (List ℕ)} {p : List ℕ → Bool} {y : List ℕ} (hy : y ∈ Lk)
    (hp : p y = true) : Lk.getD (Lk.findIdx p) [] ∈ Lk ∧ p (Lk.getD (Lk.findIdx p) []) = true := by
  have hlt : Lk.findIdx p < Lk.length := List.findIdx_lt_length_of_exists ⟨y, hy, hp⟩
  rw [List.getD_eq_getElem _ _ hlt]
  exact ⟨List.getElem_mem hlt, List.findIdx_getElem (w := hlt)⟩

variable {e}

theorem rcR_key_getD0 {x : Ω} {d₁ d₂ : Fin L.q} (g : S.G) :
    (rcRKeyOf e x d₁ d₂ g).getD 0 0 = e ((g : Perm Ω) x) := rfl

theorem rcR_key_getD1 {x : Ω} {d₁ d₂ : Fin L.q} (g : S.G) :
    (rcRKeyOf e x d₁ d₂ g).getD 1 0 = k + (rcRPi L g d₁ : ℕ) := rfl

theorem rcR_key_getD2 {x : Ω} {d₁ d₂ : Fin L.q} (g : S.G) :
    (rcRKeyOf e x d₁ d₂ g).getD 2 0 = k + (rcRPi L g d₂ : ℕ) := rfl

/-- **The entry at a position `g x`** is the key of some `g'` with `g' x = g x`. -/
theorem rcR_look {x : Ω} {d₁ d₂ : Fin L.q} {Lk : List (List ℕ)} (hT : RcRTab e x d₁ d₂ Lk)
    (g : S.G) : ∃ g' : S.G, (g' : Perm Ω) x = (g : Perm Ω) x ∧
      rcRLook Lk (e ((g : Perm Ω) x)) = rcRKeyOf e x d₁ d₂ g' := by
  obtain ⟨hm, hp⟩ := rcR_find (p := fun y => y.getD 0 0 == (e ((g : Perm Ω) x) : ℕ)) (hT.all g)
    (by exact beq_self_eq_true _)
  obtain ⟨g', hg'⟩ := hT.mem _ hm
  refine ⟨g', ?_, hg'⟩
  rw [hg', rcR_key_getD0, beq_iff_eq] at hp
  exact e.injective (Fin.ext hp)

/-! ### The label action -/

section Pi

variable {x : Ω} {d₁ d₂ : Fin L.q}

/-- An element of `G` with given label image of `d₁` (and of `d₂`, if `d₁ ≠ d₂`). -/
theorem rcR_hit (hq : 8 ≤ L.q) (hd : d₁ ≠ d₂) {j b : Fin L.q} (hjb : j ≠ b) :
    ∃ g : S.G, rcRPi L g d₁ = j ∧ rcRPi L g d₂ = b := by
  classical
  obtain ⟨σ₁, hσ₁, -, h1⟩ := rcR_alt_move (q := L.q) ∅ (by simp; omega) (c := d₁) (d := j)
    (by simp) (by simp)
  have hne : σ₁ d₂ ≠ j := fun h => hd (σ₁.injective (h1.trans h.symm))
  obtain ⟨σ₂, hσ₂, hfix, h2⟩ := rcR_alt_move (q := L.q) {j} (by simp; omega) (c := σ₁ d₂) (d := b)
    (by simpa using hne) (by simpa using hjb.symm)
  obtain ⟨g, hg⟩ := L.π_surj ⟨σ₂ * σ₁, mul_mem hσ₂ hσ₁⟩
  refine ⟨g, ?_, ?_⟩
  · show ((L.π g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) d₁ = j
    rw [hg]
    show σ₂ (σ₁ d₁) = j
    rw [h1, hfix j (by simp)]
  · show ((L.π g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) d₂ = b
    rw [hg]
    exact h2

/-- Two elements with the same image of `x` have the same labels on `{d₁, d₂}`, up to a swap. -/
theorem rcR_same_labels
    (hstab : ∀ σ ∈ rcRStab S L x, (σ d₁ = d₁ ∧ σ d₂ = d₂) ∨ (σ d₁ = d₂ ∧ σ d₂ = d₁))
    {g g' : S.G} (h : (g' : Perm Ω) x = (g : Perm Ω) x) :
    (rcRPi L g' d₁ = rcRPi L g d₁ ∧ rcRPi L g' d₂ = rcRPi L g d₂) ∨
      (rcRPi L g' d₁ = rcRPi L g d₂ ∧ rcRPi L g' d₂ = rcRPi L g d₁) := by
  have hu : (g⁻¹ * g' : S.G) ∈ MulAction.stabilizer S.G x := by
    rw [MulAction.mem_stabilizer_iff]
    show (g : Perm Ω)⁻¹ ((g' : Perm Ω) x) = x
    rw [h, Perm.inv_apply_self]
  have hσ : rcRPi L (g⁻¹ * g') ∈ rcRStab S L x := (rcR_mem_stab).2 ⟨_, hu, rfl⟩
  have hsplit : ∀ d, rcRPi L g' d = rcRPi L g (rcRPi L (g⁻¹ * g') d) := by
    intro d
    show ((L.π g' : alternatingGroup _) : Perm _) d =
      ((L.π g : alternatingGroup _) : Perm _) (((L.π (g⁻¹ * g') : alternatingGroup _) : Perm _) d)
    rw [map_mul, map_inv]
    simp
  rcases hstab _ hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [hsplit d₁, hsplit d₂, h1, h2]; exact ⟨rfl, rfl⟩
  · right; rw [hsplit d₁, hsplit d₂, h1, h2]; exact ⟨rfl, rfl⟩

theorem rcR_pi_mul (g g₁ : S.G) (d : Fin L.q) :
    rcRPi L (g * g₁) d = rcRPi L g (rcRPi L g₁ d) := by
  show ((L.π (g * g₁) : alternatingGroup _) : Perm _) d = _
  rw [map_mul]; rfl

/-- **The label action read from the table** is the label action of the element. -/
theorem rcR_piN {Lk : List (List ℕ)} (hT : RcRTab e x d₁ d₂ Lk) (hq : 8 ≤ L.q)
    (hstab : ∀ σ ∈ rcRStab S L x, (σ d₁ = d₁ ∧ σ d₂ = d₂) ∨ (σ d₁ = d₂ ∧ σ d₂ = d₁))
    (g₀ : S.G) {h : ℕ → ℕ} (hh : ∀ v : Fin k, h v = e ((g₀ : Perm Ω) (e.symm v))) (j : Fin L.q) :
    rcRPiN Lk k h j = rcRPi L g₀ j := by
  classical
  -- the key `(v₁, j, a)`
  obtain ⟨gj, hgj⟩ : ∃ g : S.G, rcRPi L g d₁ = j := by
    rcases eq_or_ne d₁ d₂ with hd | hd
    · obtain ⟨σ, hσ, -, h1⟩ := rcR_alt_move (q := L.q) ∅ (by simp; omega) (c := d₁) (d := j)
        (by simp) (by simp)
      obtain ⟨g, hg⟩ := L.π_surj ⟨σ, hσ⟩
      refine ⟨g, ?_⟩
      show ((L.π g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) d₁ = j
      rw [hg]; exact h1
    · obtain ⟨b, hb⟩ : ∃ b : Fin L.q, b ≠ j := by
        obtain ⟨b, hb⟩ := GI.NaturalGiant.exists_outside ({j} : Finset (Fin L.q)) (by
          simp only [Finset.card_singleton, Fintype.card_fin]; omega)
        exact ⟨b, by simpa using hb⟩
      obtain ⟨g, hg, -⟩ := rcR_hit hq hd (Ne.symm hb)
      exact ⟨g, hg⟩
  obtain ⟨hm1, hp1⟩ := rcR_find (p := fun y => y.getD 1 0 == k + (j : ℕ)) (hT.all gj)
    (by
      show ((rcRKeyOf e x d₁ d₂ gj).getD 1 0 == k + (j : ℕ)) = true
      rw [rcR_key_getD1, hgj]; exact beq_self_eq_true _)
  obtain ⟨g₁, hy1⟩ := hT.mem _ hm1
  change rcRLook1 Lk (k + j) = _ at hy1
  have hj1 : rcRPi L g₁ d₁ = j := by
    change ((rcRLook1 Lk (k + j)).getD 1 0 == k + (j : ℕ)) = true at hp1
    rw [hy1, rcR_key_getD1, beq_iff_eq] at hp1
    exact Fin.ext (by omega)
  -- the key at `h v₁ = g₀ g₁ x`
  have hv1 : h ((rcRLook1 Lk (k + j)).getD 0 0) = e ((g₀ * g₁ : S.G) • x) := by
    rw [hy1, rcR_key_getD0, hh]
    simp; rfl
  obtain ⟨g₂, hg₂x, hz1⟩ := rcR_look hT (g₀ * g₁)
  have hz1' : rcRLook Lk (h ((rcRLook1 Lk (k + j)).getD 0 0)) = rcRKeyOf e x d₁ d₂ g₂ := by
    rw [hv1]; exact hz1
  have hlab1 := rcR_same_labels hstab hg₂x
  simp only [rcR_pi_mul] at hlab1
  rw [hj1] at hlab1
  unfold rcRPiN
  rw [hz1', rcR_key_getD1, rcR_key_getD2]
  rcases eq_or_ne d₁ d₂ with hd | hd
  · -- single labels: both labels are `π g₀ j`
    subst hd
    have : rcRPi L g₂ d₁ = rcRPi L g₀ j := by
      rcases hlab1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> rw [hj1]
    rw [if_pos rfl, this]; omega
  · -- pairs: the key `(v₂, j, b)` with `b ≠ a`
    set a := rcRPi L g₁ d₂ with ha
    have haj : a ≠ j := fun h' => hd (by
      have := h'.trans hj1.symm
      exact ((rcRPi L g₁).injective this).symm)
    obtain ⟨b, hb⟩ : ∃ b : Fin L.q, b ≠ j ∧ b ≠ a := by
      classical
      obtain ⟨b, hb⟩ := GI.NaturalGiant.exists_outside ({j, a} : Finset (Fin L.q)) (by
        have := Finset.card_le_two (a := j) (b := a); simp only [Fintype.card_fin]; omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      exact ⟨b, hb⟩
    obtain ⟨gb, hgb1, hgb2⟩ := rcR_hit hq hd hb.1.symm
    have hrow1 : (rcRLook1 Lk (k + j)).getD 2 0 = k + (a : ℕ) := by rw [hy1, rcR_key_getD2]
    obtain ⟨hm2, hp2⟩ := rcR_find (p := fun y => y.getD 1 0 == k + (j : ℕ) &&
      !(y.getD 2 0 == k + (a : ℕ))) (hT.all gb) (by
        simp only [rcR_key_getD1, rcR_key_getD2, hgb1, hgb2, beq_self_eq_true, Bool.true_and,
          Bool.not_eq_true', beq_eq_false_iff_ne]
        intro h'; exact hb.2 (Fin.ext (by omega)))
    obtain ⟨g₃, hy2⟩ := hT.mem _ hm2
    change rcRLook2 Lk (k + j) (k + a) = _ at hy2
    have hp2' := hp2
    change ((rcRLook2 Lk (k + j) (k + a)).getD 1 0 == k + (j : ℕ) &&
      !((rcRLook2 Lk (k + j) (k + a)).getD 2 0 == k + (a : ℕ))) = true at hp2'
    rw [hy2, rcR_key_getD1, rcR_key_getD2, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      beq_eq_false_iff_ne] at hp2'
    have hj3 : rcRPi L g₃ d₁ = j := Fin.ext (by omega)
    have hb3 : rcRPi L g₃ d₂ ≠ a := fun h' => hp2'.2 (by rw [h'])
    have hv2 : h ((rcRLook2 Lk (k + j) ((rcRLook1 Lk (k + j)).getD 2 0)).getD 0 0) =
        e ((g₀ * g₃ : S.G) • x) := by
      rw [hrow1, hy2, rcR_key_getD0, hh]
      simp; rfl
    obtain ⟨g₄, hg₄x, hz2⟩ := rcR_look hT (g₀ * g₃)
    have hlab2 := rcR_same_labels hstab hg₄x
    simp only [rcR_pi_mul] at hlab2
    rw [hj3] at hlab2
    rw [hv2, show rcRLook Lk (e ((g₀ * g₃ : S.G) • x)) = rcRKeyOf e x d₁ d₂ g₄ from hz2,
      rcR_key_getD1, rcR_key_getD2]
    have hinj := (rcRPi L g₀).injective
    have hja : rcRPi L g₀ j ≠ rcRPi L g₀ a := fun h' => haj (hinj h').symm
    have hab : rcRPi L g₀ a ≠ rcRPi L g₀ (rcRPi L g₃ d₂) := fun h' => hb3 (hinj h').symm
    have hjb : rcRPi L g₀ a ≠ rcRPi L g₀ j := fun h' => hja h'.symm
    rcases hlab1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      rw [if_neg (by intro h'; exact hja (Fin.ext (by omega)))]
      rcases hlab2 with ⟨h3, -⟩ | ⟨-, h4⟩
      · rw [if_pos (Or.inl (by rw [h3]))]; omega
      · rw [if_pos (Or.inr (by rw [h4]))]; omega
    · rw [h1, h2]
      rw [if_neg (by intro h'; exact hjb (Fin.ext (by omega)))]
      rw [if_neg (by
        rintro (h' | h') <;> rcases hlab2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact hjb (Fin.ext (by rw [h3] at h'; omega))
        · exact hab (Fin.ext (by rw [h3] at h'; omega))
        · exact hab (Fin.ext (by rw [h4] at h'; omega))
        · exact hjb (Fin.ext (by rw [h4] at h'; omega)))]
      omega

end Pi

end GI.Impl
