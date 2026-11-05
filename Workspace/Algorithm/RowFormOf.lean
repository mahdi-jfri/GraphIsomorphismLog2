module

public import Workspace.Algorithm.RowExpose
public import Workspace.Algorithm.Counter
public import Workspace.Paper.RowNormalForm

@[expose] public section

/-!
# The row normal form of a giant step, and the two row branches

Algorithm 4 (RowStep): "Put the action into row normal form, possibly after recoordinatizing
rows. … if `L` is transitive on a row then … else …". This file builds the data of the row
normal form (`RowForm`) from Theorem A.18 (`GI.Paper.thm_logarithmic_gat_normal_form`) and
then the data of each branch:

* `exists_rowForm`: the natural row labels of the row case, on the faithful image of the
  group on its domain, satisfy the hypotheses of Theorem A.18. The fibers of the labels have
  one size `f` (the group moves rows onto each other), the kernel of the top action is
  transitive on each row (the fibers are the kernel orbits), and the logarithmic threshold
  holds when `2 max{63, 12 log₂ s} + 3 ≤ q`. The kernel of the top action is the block
  kernel of the coordinates (`ker_eq_blockKernel`).
* `RowForm.rowTerminal`: when `N` is transitive on `B`, the terminal data, with
  `A = N/N*` (abelian by the row normal form) and the row size bound of Section 6.2.
* `RowForm.columnStep` (`Workspace/Algorithm/RowExpose.lean`): otherwise, the column step.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper
open scoped Pointwise

variable {Ω C : Type}

/-! ### The top action on the faithful image -/

section Top

variable {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q} (hnat : NaturalRows S L label)

/-- The giant labels on the faithful image `G|_dom` (they factor through it, `labels_kill`). -/
noncomputable def topHom : S.domGroup →* alternatingGroup (Fin L.q) :=
  GI.HomDescent.factor S.domHom.rangeRestrict S.domHom.rangeRestrict_surjective L.π
    ((MonoidHom.ker_rangeRestrict S.domHom).le.trans (labels_kill hnat))

theorem topHom_apply (g : S.G) : topHom hnat (S.domHom.rangeRestrict g) = L.π g :=
  GI.HomDescent.factor_apply _ _ _ _ g

theorem topHom_surjective : Function.Surjective (topHom hnat) :=
  GI.HomDescent.factor_surjective _ S.domHom.rangeRestrict_surjective _ _ L.π_surj

theorem topHom_equivariant (g : S.domGroup) (v : S.dom) :
    label (g.val v) = (topHom hnat g).val (label v) := by
  obtain ⟨g', rfl⟩ := S.domHom.rangeRestrict_surjective g
  rw [topHom_apply]
  exact hnat.equivariant g' v v.2

/-- An element of `G|_dom` with trivial top action keeps every label. -/
theorem topHom_eq_one_iff (g : S.domGroup) :
    topHom hnat g = 1 ↔ ∀ v : S.dom, label (g.val v) = label v := by
  constructor
  · intro h v
    rw [topHom_equivariant hnat, h]
    rfl
  · intro h
    ext i
    obtain ⟨v, hv, rfl⟩ := hnat.onto i
    have := h ⟨v, hv⟩
    rw [topHom_equivariant hnat] at this
    exact congrArg Fin.val this

/-- **The kernel of the top action is the block kernel** of any coordinates in which the
labels are the second coordinate. -/
theorem ker_eq_blockKernel {B : Type} (e : B × Fin L.q ≃ S.dom)
    (he : ∀ b i, label (e (b, i)) = i) :
    ((alternatingGroup (Fin L.q)).subtype.comp (topHom hnat)).ker = blockKernel e := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
    OneMemClass.coe_eq_one, topHom_eq_one_iff]
  unfold blockKernel
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · intro h
    have hk : ∀ b i, (e.symm (g.val (e (b, i)))).2 = i := by
      intro b i
      have h1 := h (e (b, i))
      rw [he] at h1
      have h2 := he (e.symm (g.val (e (b, i)))).1 (e.symm (g.val (e (b, i)))).2
      simp only [Prod.mk.eta, apply_symm_apply] at h2
      rw [← h2, h1]
    let Pm : Perm (B × Fin L.q) := (e.trans g.val).trans e.symm
    have hP : ∀ z, (Pm z).2 = z.2 := fun z => hk z.1 z.2
    refine ⟨GI.rowComponents Pm hP, ?_⟩
    change relabelPerm e (GI.rowCoordinatePerm (GI.rowComponents Pm hP)) = g.val
    rw [GI.rowCoordinatePerm_components Pm hP]
    ext v
    change (e (e.symm (g.val (e (e.symm v)))) : Ω) = _
    simp
  · rintro ⟨x, hx⟩ v
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective v
    rw [← hx, cleanRowPerm_apply, he, he]

end Top

/-! ### The data of the row normal form -/

/-- **The row normal form exists** (Theorem A.18 applied to the faithful image). The
hypothesis `hthr` is the logarithmic threshold (LG1) for the row size `f ≤ s`, in the form of
`thm_logarithmic_clean_complement_threshold`. -/
theorem exists_rowForm [Finite Ω] (S : State Ω C)
    (L : GiantLabels S) {label : Ω → Fin L.q} (hnat : NaturalRows S L label)
    (hthr : 2 * max 63 (12 * Real.logb 2 S.size) + 3 ≤ (L.q : ℝ)) :
    ∃ F : RowForm S L, F.label = label ∧ Fintype.card F.B * L.q = S.size := by
  classical
  haveI : Fintype S.dom := Fintype.ofFinite _
  have hq19 : 19 ≤ L.q := by
    have h63 : (63 : ℝ) ≤ max 63 (12 * Real.logb 2 S.size) := le_max_left _ _
    have : (19 : ℝ) ≤ L.q := by linarith
    exact_mod_cast this
  let lab : S.dom → Fin L.q := fun v => label v
  let φ : S.domGroup →* Perm (Fin L.q) := (alternatingGroup (Fin L.q)).subtype.comp (topHom hnat)
  have hφ : ∀ (g : S.domGroup) (x : S.dom), lab (g.val x) = φ g (lab x) :=
    topHom_equivariant hnat
  have hAlt : φ.range = alternatingGroup (Fin L.q) := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      exact (topHom hnat g).2
    · intro hp
      obtain ⟨g, hg⟩ := topHom_surjective hnat ⟨p, hp⟩
      exact ⟨g, by simp [φ, hg]⟩
  have hq0 : 0 < L.q := by omega
  let i₀ : Fin L.q := ⟨0, hq0⟩
  -- The rows have one size `f`: the group moves the row `i₀` onto every row.
  have hfib : ∀ i, Fintype.card {x : S.dom // lab x = i} =
      Fintype.card {x : S.dom // lab x = i₀} := by
    intro i
    haveI := alternatingGroup.isPretransitive_of_three_le_card (Fin L.q)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin L.q)) i₀ i
    have ha' : a.val i₀ = i := ha
    obtain ⟨g, hg⟩ := topHom_surjective hnat a
    symm
    refine Fintype.card_congr (Equiv.subtypeEquiv g.val fun x => ?_)
    have hx : lab (g.val x) = a.val (lab x) := by
      rw [← hg]; exact topHom_equivariant hnat g x
    rw [hx, ← ha']
    exact ⟨fun h => h ▸ rfl, fun h => a.val.injective h⟩
  set f := Fintype.card {x : S.dom // lab x = i₀}
  have hcard : f * L.q = S.size := by
    have h1 : S.size = Fintype.card S.dom := Nat.card_eq_fintype_card
    rw [h1, Fintype.card_congr (Equiv.sigmaFiberEquiv lab).symm, Fintype.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hf : 0 < f := by
    obtain ⟨v, hv, hvi⟩ := hnat.onto i₀
    exact Fintype.card_pos_iff.2 ⟨⟨⟨v, hv⟩, hvi⟩⟩
  -- The kernel of the top action is transitive on each row (the rows are the kernel orbits).
  have htrans : ∀ x y : S.dom, lab x = lab y → ∃ g : S.domGroup, g ∈ φ.ker ∧ g.val x = y := by
    intro x y hxy
    obtain ⟨k, hk1, hkx⟩ := (hnat.fibers x x.2 y y.2).1 hxy
    refine ⟨S.domHom.rangeRestrict k, ?_, Subtype.ext hkx⟩
    show (alternatingGroup (Fin L.q)).subtype (topHom hnat (S.domHom.rangeRestrict k)) = 1
    rw [topHom_apply, hk1]
    rfl
  -- The logarithmic threshold (LG1) for the row size `f ≤ s`.
  have hLG : 2 * max 63 (12 * Real.logb 2 f) + 3 ≤ (L.q : ℝ) := by
    have hfs : f ≤ S.size := by rw [← hcard]; exact Nat.le_mul_of_pos_right f hq0
    have hlog : Real.logb 2 f ≤ Real.logb 2 S.size :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hf) (by exact_mod_cast hfs)
    have : max 63 (12 * Real.logb 2 f) ≤ max 63 (12 * Real.logb 2 S.size) :=
      max_le_max le_rfl (by linarith)
    linarith
  obtain ⟨k, hodd, hLG1, hm⟩ := thm_logarithmic_clean_complement_threshold f L.q hLG
  obtain ⟨B, fB, e, s, hB, hlab, -, hpure, hcompl, hrnf⟩ :=
    thm_logarithmic_gat_normal_form S.domGroup lab f
      (fun i => by rw [hfib i]) hf φ hφ hAlt htrans k hodd hLG1 (by rw [Fintype.card_fin]; exact hm)
  obtain ⟨Nl, Nstar, hN, hNs, hr⟩ := hrnf i₀
  have hker : φ.ker = blockKernel e := ker_eq_blockKernel hnat e hlab
  rw [hker] at hcompl hr
  let F : RowForm S L :=
    { B := B
      fin := fB
      dec := Classical.decEq _
      label := label
      natural := hnat
      e := e
      e_label := hlab
      four_le := by omega
      s := s
      pure := hpure
      complement := hcompl
      i0 := i₀
      Nl := Nl
      Nstar := Nstar
      Nl_normal := hN
      Nstar_normal := hNs
      rnf := hr }
  refine ⟨F, rfl, ?_⟩
  change @Fintype.card B fB * L.q = S.size
  rw [hB, hcard]

end GI.Algorithm
