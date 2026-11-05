module

public import Workspace.ColorCompression
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Init.Data.Vector.OfFn
public import Init.Data.Vector.Lemmas

@[expose] public section

/-! Pair refinement uses a shared palette on two tagged domains. This keeps
distinct source/target colors distinct, even if one color occurs on only one side. -/

namespace GI.PairRefinement

abbrev Domain (n : ℕ) := Bool × (Fin n × Fin n)
abbrev Color (n : ℕ) := Fin (Fintype.card (Domain n) + 1)
abbrev Coloring (n : ℕ) := Domain n → Color n

variable {n : ℕ}

def transpose (a : Domain n) : Domain n := (a.1, a.2.2, a.2.1)
def diagonal (a : Domain n) : Bool := decide (a.2.1 = a.2.2)

def intersection (c : Coloring n) (a : Domain n) (i j : Color n) : ℕ :=
  (Finset.univ.filter (fun z : Fin n => c (a.1, a.2.1, z) = i ∧
    c (a.1, z, a.2.2) = j)).card

theorem intersection_le (c : Coloring n) (a : Domain n) (i j : Color n) :
    intersection c a i j ≤ n := by
  exact (Finset.card_filter_le _ _).trans (by simp)

def signature (c : Coloring n) (a : Domain n) : List (List ℕ) :=
  [c a |>.val] :: [c (transpose a) |>.val] :: [diagonal a |>.toNat] ::
    List.ofFn (fun i : Color n => List.ofFn (fun j : Color n => intersection c a i j))

theorem signature_eq_iff (c : Coloring n) (a b : Domain n) :
    signature c a = signature c b ↔
      c a = c b ∧ c (transpose a) = c (transpose b) ∧ diagonal a = diagonal b ∧
        ∀ i j : Color n, intersection c a i j = intersection c b i j := by
  have hbool : (diagonal a).toNat = (diagonal b).toNat ↔ diagonal a = diagonal b := by
    cases diagonal a <;> cases diagonal b <;> decide
  simp only [signature, List.cons.injEq, and_true,
    List.ofFn_inj, funext_iff, hbool, Fin.ext_iff]

/-- Materialize both pair-color arrays before returning the lookup function. -/
def materialize {C : Type*} (f : Domain n → C) : Domain n → C :=
  let left := Vector.ofFn (fun x : Fin n => Vector.ofFn (fun y : Fin n => f (false, x, y)))
  let right := Vector.ofFn (fun x : Fin n => Vector.ofFn (fun y : Fin n => f (true, x, y)))
  fun a => if a.1 then (right.get a.2.1).get a.2.2 else (left.get a.2.1).get a.2.2

theorem materialize_eq {C : Type*} (f : Domain n → C) : materialize f = f := by
  funext a
  rcases a with ⟨b, x, y⟩
  cases b <;> simp [materialize, Vector.get, Fin.cast]

def step (c : Coloring n) : Coloring n :=
  materialize (ColorCompression.compress (signature c))

theorem step_eq_iff (c : Coloring n) (a b : Domain n) :
    step c a = step c b ↔ signature c a = signature c b := by
  rw [step, materialize_eq]
  exact ColorCompression.compress_eq_iff (signature c) a b

theorem step_refines (c : Coloring n) {a b : Domain n} (h : step c a = step c b) :
    c a = c b := ((signature_eq_iff c a b).mp ((step_eq_iff c a b).mp h)).1

def Transports (c : Coloring n) (source target : Bool) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ x y : Fin n, c (target, p x, p y) = c (source, x, y)

theorem intersection_transport (c : Coloring n) {source target : Bool}
    {p : Equiv.Perm (Fin n)} (h : Transports c source target p)
    (x y : Fin n) (i j : Color n) :
    intersection c (target, p x, p y) i j = intersection c (source, x, y) i j := by
  symm
  apply Finset.card_bij (fun z _ => p z)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    simpa only [h x z, h z y] using hz
  · intro z _ w _ he
    exact p.injective he
  · intro z hz
    refine ⟨p.symm z, ?_, p.apply_symm_apply z⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hx := h x (p.symm z)
    have hy := h (p.symm z) y
    simp only [Equiv.apply_symm_apply] at hx hy
    rwa [← hx, ← hy]

theorem signature_transport (c : Coloring n) {source target : Bool}
    {p : Equiv.Perm (Fin n)} (h : Transports c source target p) (x y : Fin n) :
    signature c (target, p x, p y) = signature c (source, x, y) := by
  apply (signature_eq_iff c _ _).mpr
  refine ⟨h x y, h y x, ?_, fun i j => intersection_transport c h x y i j⟩
  simp [diagonal, p.injective.eq_iff]

/-- Joint refinement preserves exactly every source-target transporter and,
by allowing equal tags, every within-side automorphism. -/
theorem step_transports_iff (c : Coloring n) (source target : Bool)
    (p : Equiv.Perm (Fin n)) : Transports (step c) source target p ↔
      Transports c source target p := by
  constructor
  · intro h x y
    exact step_refines c (h x y)
  · intro h x y
    exact (step_eq_iff c _ _).mpr (signature_transport c h x y)

end GI.PairRefinement
