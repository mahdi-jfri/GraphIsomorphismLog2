module

public import Workspace.CleanComplementReindex

@[expose] public section

/-! From the paper's hypotheses of Theorem A.17 (a block labelling, a block
action with image `Alt(m)`, a block kernel transitive on each block, and
(LG1)) to a clean complement. The construction splits on the parity of `m`
and renames the blocks to the index types of the odd and even completions. -/

namespace GI

open Equiv

variable {V : Type} {I : Type} [Fintype I] [DecidableEq I]

/-- The paper's data as a `CleanBlockAction`: `φ` is the action on blocks,
with image `Alt(I)`. -/
def cleanBlockActionOf (G : Subgroup (Perm V)) (label : V → I)
    (hlabel : Function.Surjective label) (φ : G →* Perm I)
    (hφ : ∀ (g : G) (x : V), label (g.val x) = φ g (label x))
    (hAlt : φ.range = alternatingGroup I) : CleanBlockAction G I where
  label := label
  label_surjective := hlabel
  top := φ.codRestrict (alternatingGroup I) (fun g => hAlt ▸ ⟨g, rfl⟩)
  top_surjective := by
    rintro ⟨p, hp⟩
    rw [← hAlt] at hp
    obtain ⟨g, hg⟩ := hp
    exact ⟨g, Subtype.ext hg⟩
  action := hφ

theorem cleanBlockActionOf_ker (G : Subgroup (Perm V)) (label : V → I)
    (hlabel : Function.Surjective label) (φ : G →* Perm I)
    (hφ : ∀ (g : G) (x : V), label (g.val x) = φ g (label x))
    (hAlt : φ.range = alternatingGroup I) :
    (cleanBlockActionOf G label hlabel φ hφ hAlt).top.ker = φ.ker :=
  MonoidHom.ker_codRestrict _ _ _

/-- A clean complement exists for every block action satisfying the
hypotheses of Theorem A.17. Odd `m = 2r + 1`: the odd completion. Even
`m = 2r + 2`: the even completion. -/
theorem pureComplement_nonempty_log [Fintype V]
    {G : Subgroup (Perm V)} (A : CleanBlockAction G I) (hker : A.KernelTransitive)
    {k : ℕ} (hthr : A.BelowLogThreshold k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card I) : Nonempty (PureComplement A) := by
  classical
  have hk : 1 ≤ k := hodd.pos
  rcases Nat.even_or_odd (Fintype.card I) with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- `m` is even; `m ≥ 2k - 1 ≥ 1` gives `m = 2 (r - 1) + 2`.
    have hc : Fintype.card I = Fintype.card (Option (Option (Fin (r - 1) × Bool))) := by
      simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      omega
    let σ := Fintype.equivOfCardEq hc
    exact ⟨(logEvenComplement (A.reindex σ) (hker.reindex A σ) (hthr.reindex A σ)
      hodd (by rw [← hc]; exact hm)).ofReindex⟩
  · have hc : Fintype.card I = Fintype.card (Option (Fin r × Bool)) := by
      simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      omega
    let σ := Fintype.equivOfCardEq hc
    exact ⟨(logOddComplement (A.reindex σ) (hker.reindex A σ) (hthr.reindex A σ)
      hodd (by rw [← hc]; exact hm)).ofReindex⟩

namespace PureComplement
variable {G : Subgroup (Perm V)} {A : CleanBlockAction G I} (c : PureComplement A)

theorem sectionHom_injective : Function.Injective c.sectionHom := by
  intro p q hpq
  have ht := congrArg A.top hpq
  simpa only [c.top_section] using ht

/-- In clean coordinates, one block is a copy of the fiber. -/
noncomputable def fiberEquivBlock (i : I) : c.Fiber ≃ {x : V // A.label x = i} :=
  Equiv.ofBijective (fun b => ⟨c.coordinates (b, i), c.label_coordinates b i⟩) (by
    constructor
    · intro b b' h
      have h' := c.coordinates.injective (congrArg Subtype.val h)
      exact congrArg Prod.fst h'
    · rintro ⟨x, hx⟩
      obtain ⟨⟨b, j⟩, rfl⟩ := c.coordinates.surjective x
      have hj : j = i := (c.label_coordinates b j).symm.trans hx
      subst hj
      exact ⟨b, rfl⟩)

end PureComplement
end GI
