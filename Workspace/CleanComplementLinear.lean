module

public import Workspace.CleanComplementFinite
public import Workspace.CleanComplementOdd
public import Workspace.CleanComplementAssemble

@[expose] public section

/-! Genuine clean complements under a linear fiber threshold. These conclusions
are constructed from numeric bounds and the supplied top action alone; the
paper's logarithmic threshold remains a separate theorem to prove. -/
universe u v w
namespace GI
variable {I : Type u} {V : Type v} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm V)} (A : CleanBlockAction G I)

theorem localizedPair_exists_linear [Fintype V] {k : ℕ} (hk : 5 ≤ k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card I)
    (hdegree : ∀ i, Fintype.card {x : V // A.label x = i} < k) :
    Nonempty (LocalizedBlockPair A) := by
  classical
  obtain ⟨T, U, a, hT, hU, hmeet⟩ := CleanLocalization.exists_pair_sets (by omega) hm
  obtain ⟨p, hp⟩ := CleanLocalization.even_full_support T (by omega) (by simpa [hT] using hodd)
  obtain ⟨q, hq⟩ := CleanLocalization.even_full_support U (by omega) (by simpa [hU] using hodd)
  have hLT : LocalLiftAvailable A (T : Set I) := CleanLocalization.localLiftAvailable_linear A T
    (by omega) (fun i _ => by simpa only [hT] using hdegree i)
  have hLU : LocalLiftAvailable A (U : Set I) := CleanLocalization.localLiftAvailable_linear A U
    (by omega) (fun i _ => by simpa only [hU] using hdegree i)
  obtain ⟨d, _⟩ := localized_pair_of_LG2 A T U hLT hLU p q a hp hq hmeet
  exact ⟨d⟩

structure PureComplement where
  Fiber : Type v
  base : Fiber
  coordinates : Fiber × I ≃ V
  sectionHom : alternatingGroup I →* G
  label_coordinates : ∀ b i, A.label (coordinates (b, i)) = i
  pure : ∀ (p : alternatingGroup I) b i,
    (sectionHom p).val (coordinates (b, i)) = coordinates (b, p.val i)
  top_section : ∀ p, A.top (sectionHom p) = p
  isComplement : A.top.ker.IsComplement' sectionHom.range

noncomputable def PureComplement.rangeEquiv (c : PureComplement A) :
    alternatingGroup I ≃* c.sectionHom.range :=
  MonoidHom.ofInjective (by
    intro p q hpq
    have ht := congrArg A.top hpq
    simpa only [c.top_section] using ht)

def CleanBlockAction.relabelFiberEquiv {W : Type w} (e : V ≃ W) (i : I) :
    {x : V // A.label x = i} ≃ {y : W // (A.relabel e).label y = i} where
  toFun x := ⟨e x.val, by change A.label (e.symm (e x.val)) = i; rw [e.symm_apply_apply]; exact x.property⟩
  invFun y := ⟨e.symm y.val, y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

end GI

namespace GI.CleanEvenConstruction
variable {I B W : Type*} [Fintype I] [DecidableEq I] [Fintype B] [Fintype W]
variable {G : Subgroup (Equiv.Perm ((B × I) ⊕ W))}
variable (A : CleanBlockAction G (Option I))

theorem extraLift_exists_linear {k : ℕ} (hk : 5 ≤ k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card (Option I))
    (hdegree : ∀ i, Fintype.card {x : (B × I) ⊕ W // A.label x = i} < k)
    (a b c : I) (hab : a ≠ b) (hac : a ≠ c) : Nonempty (ExtraLift A a b c) := by
  classical
  obtain ⟨T, hT, ha, hz, hb, hc⟩ := CleanLocalization.exists_two_containing_avoiding
    (k := k) (by omega) (by omega) (some a) none (some b) (some c)
    (by simp) (by simpa using Ne.symm hab) (by simp) (by simpa using Ne.symm hac) (by simp)
  obtain ⟨p, hp, hsend⟩ := CleanLocalization.even_full_support_send T (by omega)
    (by simpa [hT] using hodd) (some a) none ha hz (by simp)
  apply extraLift_of_LG2 A T _ p a b c hp hsend hb hc
  exact CleanLocalization.localLiftAvailable_linear A T (by omega)
    (fun i _ => by simpa only [hT] using hdegree i)

end GI.CleanEvenConstruction

namespace GI
variable {J : Type u} {V : Type v} [Fintype J] [DecidableEq J] [Fintype V]
variable {G : Subgroup (Equiv.Perm V)}

noncomputable def linearOddComplement (A : CleanBlockAction G (Option (J × Bool)))
    {k : ℕ} (hk : 5 ≤ k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card (Option (J × Bool)))
    (hdegree : ∀ i, Fintype.card {x : V // A.label x = i} < k) : PureComplement A := by
  classical
  let d := Classical.choice (localizedPair_exists_linear A hk hodd hm hdegree)
  have hc : 5 ≤ Fintype.card (Option (J × Bool)) := by omega
  exact {
    Fiber := (CleanOddConstruction.system d hc).Center
    base := (CleanOddConstruction.system d hc).centerBase
    coordinates := (CleanOddConstruction.system d hc).coordinates
    sectionHom := CleanOddConstruction.sectionHom d hc
    label_coordinates := CleanOddConstruction.coordinates_label d hc
    pure := CleanOddConstruction.section_pure d hc
    top_section := CleanOddConstruction.top_section d hc
    isComplement := CleanOddConstruction.kernel_complement d hc }

noncomputable def linearEvenComplement (A : CleanBlockAction G (Option (Option (J × Bool))))
    {k : ℕ} (hk : 5 ≤ k) (hodd : Odd k)
    (hm : 2 * k - 1 ≤ Fintype.card (Option (Option (J × Bool))))
    (hdegree : ∀ i, Fintype.card {x : V // A.label x = i} < k) : PureComplement A := by
  classical
  let d := Classical.choice (localizedPair_exists_linear A hk hodd hm hdegree)
  have hc : 5 ≤ Fintype.card (Option (Option (J × Bool))) := by omega
  have holdcard : 2 < (Finset.univ : Finset (Option (J × Bool))).card := by
    rw [Finset.card_univ]
    have he := Fintype.card_option (α := Option (J × Bool))
    omega
  have hex : ∃ t : Option (J × Bool) × Option (J × Bool) × Option (J × Bool),
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
    obtain ⟨a, b, c, _, _, _, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp holdcard
    exact ⟨(a, b, c), hab, hac, hbc⟩
  let a := (Classical.choose hex).1
  let b := (Classical.choose hex).2.1
  let c := (Classical.choose hex).2.2
  have hab : a ≠ b := (Classical.choose_spec hex).1
  have hac : a ≠ c := (Classical.choose_spec hex).2.1
  have hbc : b ≠ c := (Classical.choose_spec hex).2.2
  have hbound : ∀ i, Fintype.card
      {x : ((CleanOldRows.system d hc).Center × Option (J × Bool)) ⊕ CleanOldRows.New (A := A) //
        (CleanEvenAssembly.oldAction d hc).label x = i} < k := by
    intro i
    have he := Fintype.card_congr (A.relabelFiberEquiv (CleanOldRows.coordinates d hc).symm i)
    change Fintype.card {x // (A.relabel (CleanOldRows.coordinates d hc).symm).label x = i} < k
    rw [← he]
    exact hdegree i
  let z := Classical.choice (CleanEvenConstruction.extraLift_exists_linear (CleanEvenAssembly.oldAction d hc)
    hk hodd hm hbound a b c hab hac)
  exact {
    Fiber := (CleanOldRows.system d hc).Center
    base := (CleanOldRows.system d hc).centerBase
    coordinates := CleanEvenAssembly.coordinates d hc z hab hbc
    sectionHom := CleanEvenAssembly.sectionHom d hc z hab hac hbc
    label_coordinates := CleanEvenAssembly.coordinates_label d hc z hab hbc
    pure := CleanEvenAssembly.section_pure d hc z hab hac hbc
    top_section := CleanEvenAssembly.top_section d hc z hab hac hbc
    isComplement := CleanEvenAssembly.kernel_complement d hc z hab hac hbc }

end GI
