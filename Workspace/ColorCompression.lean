module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Lex
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace GI.ColorCompression

variable {A B : Type*} [Fintype A] [LinearOrder B]

def palette (f : A → B) : Finset B := Finset.univ.image f

def rank (f : A → B) (a : A) : ℕ :=
  ((palette f).filter (fun b => b < f a)).card

theorem rank_strict {f : A → B} {a b : A} (h : f a < f b) : rank f a < rank f b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
      lt_trans (Finset.mem_filter.mp hx).2 h⟩
  · intro heq
    have hm : f a ∈ (palette f).filter (fun x => x < f b) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, h⟩
    rw [← heq] at hm
    exact (lt_irrefl (f a)) (Finset.mem_filter.mp hm).2

theorem rank_eq_iff (f : A → B) (a b : A) : rank f a = rank f b ↔ f a = f b := by
  constructor
  · intro he
    rcases lt_trichotomy (f a) (f b) with h | h | h
    · exact False.elim ((ne_of_lt (rank_strict h)) he)
    · exact h
    · exact False.elim ((ne_of_lt (rank_strict h)) he.symm)
  · intro h
    simp only [rank, h]

theorem rank_le_card (f : A → B) (a : A) : rank f a ≤ Fintype.card A := by
  exact (Finset.card_filter_le _ _).trans
    ((Finset.card_image_le).trans (by simp))

def compress (f : A → B) (a : A) : Fin (Fintype.card A + 1) :=
  ⟨rank f a, Nat.lt_succ_of_le (rank_le_card f a)⟩

theorem compress_eq_iff (f : A → B) (a b : A) : compress f a = compress f b ↔ f a = f b := by
  rw [Fin.ext_iff]
  exact rank_eq_iff f a b

variable {A' : Type*} [Fintype A']

theorem palette_transport (f : A → B) (g : A' → B) (e : A ≃ A')
    (h : ∀ a, g (e a) = f a) : palette g = palette f := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨e.symm a, Finset.mem_univ _, ?_⟩
    simpa only [Equiv.apply_symm_apply] using (h (e.symm a)).symm
  · intro hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨e a, Finset.mem_univ _, h a⟩

theorem rank_transport (f : A → B) (g : A' → B) (e : A ≃ A')
    (h : ∀ a, g (e a) = f a) (a : A) : rank g (e a) = rank f a := by
  unfold rank
  rw [palette_transport f g e h, h]

theorem compress_transport (f g : A → B) (e : Equiv.Perm A)
    (h : ∀ a, g (e a) = f a) (a : A) : compress g (e a) = compress f a :=
  Fin.ext (rank_transport f g e h a)

end GI.ColorCompression

example : GI.ColorCompression.rank (fun i : Fin 3 => [i.val, 0]) 2 = 2 := by decide
