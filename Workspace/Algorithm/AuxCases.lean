module

public import Workspace.Algorithm.AuxRectangle
public import Workspace.Algorithm.AuxBlocks

@[expose] public section

/-!
# The item of the configuration branch (Cases 2b and 3)

Section A.3 ends Cases 2b and 3 with one of two objects on the labels:

* a colored partition with small blocks (Case 3(a): "`ℬ_T` has at most `|T| ≤ q/2` points, so its
  stabilizer has width at most `q/2`"; the twin classes of Case 3), whose full overcoset is
  lifted ("No index of a colored-partition stabilizer is enumerated: its full overcoset is
  lifted");
* a nontrivial homogeneous coherent configuration on a fiber `C` with `|C| ≥ δq`, and the source
  vertex `x₀` of the first rectangle (Case 2b: "the canonical coherent refinement … on
  `C = Φ \ A`"; Case 3(b): "the vertex class `C` … as a nontrivial coherent configuration").

Then Algorithm `alg:auxiliary` runs, on both strings at once:
"**if** `q ≤ λ` **then** solve the exact configuration-isomorphism instance of Lemma A.12 …
**else** **for each** source--target choice in the first-rectangle construction …".

`CfgOut` is this object, `cfgOutItem` is the item built from the objects of the two strings,
and `cfgOutItem_valid` proves the item valid from three facts: the source object is good
(`CfgOut.Good`), every parent isomorphism of the branch maps the source object to the target
object, and the labels are many. The objects are produced from the canonical structures by
`Aggregation.out` (see `Workspace/Algorithm/Aggregation.lean`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

/-- **The object that ends Cases 2b and 3**: a colored partition of the labels, or a pair
configuration with the source vertex of its first rectangle, or nothing (an empty branch). -/
inductive CfgOut (q : ℕ) : Type
  | part (z : ColPart (Fin q))
  | pair (X : PairCfg q) (x₀ : Fin q)
  | none

namespace CfgOut

variable {q : ℕ}

/-- Relabeling acts on each kind of object. -/
def smul (σ : Perm (Fin q)) : CfgOut q → CfgOut q
  | part z => part (σ • z)
  | pair X x₀ => pair (σ • X) (σ x₀)
  | none => none

instance : MulAction (Perm (Fin q)) (CfgOut q) where
  smul := smul
  one_smul o := by
    cases o with
    | part z => exact congrArg part (one_smul _ z)
    | pair X x₀ =>
      show pair (1 • X) ((1 : Perm (Fin q)) x₀) = pair X x₀
      rw [one_smul]; rfl
    | none => rfl
  mul_smul σ τ o := by
    cases o with
    | part z => exact congrArg part (mul_smul σ τ z)
    | pair X x₀ =>
      show pair ((σ * τ) • X) ((σ * τ) x₀) = pair (σ • τ • X) (σ (τ x₀))
      rw [mul_smul]; rfl
    | none => rfl

@[simp] theorem smul_part (σ : Perm (Fin q)) (z : ColPart (Fin q)) :
    σ • (part z : CfgOut q) = part (σ • z) := rfl

@[simp] theorem smul_pair (σ : Perm (Fin q)) (X : PairCfg q) (x₀ : Fin q) :
    σ • (pair X x₀ : CfgOut q) = pair (σ • X) (σ x₀) := rfl

@[simp] theorem smul_none (σ : Perm (Fin q)) : σ • (none : CfgOut q) = none := rfl

/-- **A good object**: a colored partition whose even stabilizer has the cap `⌊βq⌋`, or a good
pair configuration on at least `q/4` labels with its source vertex in the fiber. -/
def Good (β : ℝ) : CfgOut q → Prop
  | part z => GI.SectionCaps.Cap (evenStab (q := q) z) ⌊β * q⌋₊
  | pair X x₀ => X.Good deltaB ∧ x₀ ∈ X.fiber
  | none => False

end CfgOut

section Item

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

open Classical in
/-- **The item of the configuration branch** from the objects of the two strings: the overcoset
of a colored partition; for a pair configuration, the configuration query of Lemma A.12 when
`q ≤ λ` and the first-rectangle item of Lemma 5.1 when `q > λ`. Objects of different kinds give
an empty branch. -/
noncomputable def cfgOutItem (O : RectOracle P S L) (ch : SojChoice) :
    CfgOut L.q → CfgOut L.q → AuxItem P S L
  | .part zX, .part zY => objItem zX zY
  | .pair X x₀, .pair Y y₀ =>
      if (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α then cfgItem X Y else sojItem O ch X Y x₀ y₀
  | _, _ => .none

end Item

/-- **The item of the configuration branch is valid** (Lemma A.12, Lemma 5.1, Lemma A.28): for
`β ≥ 13/16` there is a label threshold `q₀` such that for `q ≥ q₀`, a good source object and a
branch whose parent isomorphisms map the source object to the target object, the item is valid. -/
theorem cfgOutItem_valid {P : Params} (hβ : 13 / 16 ≤ P.β) :
    ∃ q₀ : ℕ, ∀ {Ω C : Type} {S : State Ω C} (L : GiantLabels S) (O : RectOracle P S L)
      (ch : SojChoice)
      {B : Set (Perm Ω)} (oX oY : CfgOut L.q), oX.Good P.β → q₀ ≤ L.q →
      (∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • oX = oY) →
      (cfgOutItem O ch oX oY).Valid B := by
  obtain ⟨q₀, hq₀⟩ := cfgItem_valid (P := P) (δ := deltaB)
    (by rw [max_lt_iff]; norm_num [deltaB]; constructor <;> linarith)
  refine ⟨max q₀ 16, fun {Ω C S} L O ch B oX oY hgood hq hB => ?_⟩
  classical
  have hq16 : 16 ≤ L.q := le_of_max_le_right hq
  have h1 : 1 ≤ P.β * L.q := by
    have : (16 : ℝ) ≤ L.q := by exact_mod_cast hq16
    nlinarith
  -- objects of different kinds: the branch is empty
  have hempty : ∀ (hne : ∀ σ : Perm (Fin L.q), σ • oX ≠ oY), S.answer ∩ B = ∅ := by
    intro hne
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_
    obtain ⟨hgG, he⟩ := hB g hg
    exact hne _ he
  cases oX with
  | none => exact absurd hgood id
  | part zX =>
    cases oY with
    | part zY =>
      refine objItem_valid (fun g hg => ?_) hgood
      obtain ⟨hgG, he⟩ := hB g hg
      exact ⟨hgG, by simpa using he⟩
    | pair Y y₀ => exact hempty fun σ h => by simp at h
    | none => exact hempty fun σ h => by simp at h
  | pair X x₀ =>
    cases oY with
    | part zY => exact hempty fun σ h => by simp at h
    | none => exact hempty fun σ h => by simp at h
    | pair Y y₀ =>
      have hB' : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
          (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y ∧ (L.π ⟨g, hg⟩ : Perm (Fin L.q)) x₀ = y₀ := by
        intro g hg
        obtain ⟨hgG, he⟩ := hB g hg
        simp only [CfgOut.smul_pair, CfgOut.pair.injEq] at he
        exact ⟨hgG, he⟩
      show (if (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α then cfgItem X Y else sojItem O ch X Y x₀ y₀).Valid B
      split_ifs with hlam
      · exact hq₀ L X Y hgood.1 (le_of_max_le_left hq) hlam fun g hg =>
          (hB' g hg).imp fun _ h => h.1
      · exact sojItem_valid O ch hgood.1 hgood.2 hβ h1 hq16 (lt_of_not_ge hlam) hB'

end GI.Algorithm
