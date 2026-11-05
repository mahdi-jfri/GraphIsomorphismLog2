module

public import Workspace.CleanComplementLocal
public import Workspace.CleanComplementSplit
public import Workspace.RowTransfers

@[expose] public section

/-! Lifted conjugation constructs each needed clean cycle from one actual local pair. -/
namespace GI
variable {I V : Type*} [Fintype I] [DecidableEq I]

theorem even_perm_maps_triple (hcard : 5 ≤ Fintype.card I)
    {a b c i j k : I} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ t : Equiv.Perm I, t ∈ alternatingGroup I ∧ t a = i ∧ t b = j ∧ t c = k := by
  obtain ⟨q, _, hqa, hqb⟩ := even_perm_maps_pair (by omega) hab hij
  have hqci : q c ≠ i := fun he => hac (q.injective (hqa.trans he.symm))
  have hqcj : q c ≠ j := fun he => hbc (q.injective (hqb.trans he.symm))
  let p : Equiv.Perm I := Equiv.swap (q c) k * q
  have hpa : p a = i := by
    change Equiv.swap (q c) k (q a) = i
    rw [hqa, Equiv.swap_apply_of_ne_of_ne (Ne.symm hqci) hik]
  have hpb : p b = j := by
    change Equiv.swap (q c) k (q b) = j
    rw [hqb, Equiv.swap_apply_of_ne_of_ne (Ne.symm hqcj) hjk]
  have hpc : p c = k := by simp [p, Equiv.Perm.mul_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with heven | hodd
  · exact ⟨p, Equiv.Perm.mem_alternatingGroup.mpr heven, hpa, hpb, hpc⟩
  · have hspare : 1 < ({a, b, c} : Finset I)ᶜ.card := by
      rw [Finset.card_compl]
      have hs : ({a, b, c} : Finset I).card ≤ 3 := Finset.card_le_three
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hspare
    have hu' : u ≠ a ∧ u ≠ b ∧ u ≠ c := by simpa using hu
    have hv' : v ≠ a ∧ v ≠ b ∧ v ≠ c := by simpa using hv
    refine ⟨p * Equiv.swap u v, ?_, ?_, ?_, ?_⟩
    · simp [Equiv.Perm.mem_alternatingGroup, map_mul, hodd, Equiv.Perm.sign_swap huv]
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hu'.1) (Ne.symm hv'.1), hpa]
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hu'.2.1) (Ne.symm hv'.2.1), hpb]
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hu'.2.2) (Ne.symm hv'.2.2), hpc]

/-- Concrete localized elements of the supplied group. LG2 must construct this data. -/
structure LocalizedBlockPair {G : Subgroup (Equiv.Perm V)} (A : CleanBlockAction G I) where
  g : G
  h : G
  center : I
  left : LocalizedBlockLift A.label (A.top g).val g.val
  right : LocalizedBlockLift A.label (A.top h).val h.val
  meet : ∀ i, ((A.top g).val i ≠ i ∧ (A.top h).val i ≠ i) ↔ i = center

namespace LocalizedBlockPair
variable {G : Subgroup (Equiv.Perm V)} {A : CleanBlockAction G I} (d : LocalizedBlockPair A)

def cycle : Equiv.Perm V := rightLocalCommutator d.g.val d.h.val

theorem cycle_mem : d.cycle ∈ G := local_commutator_mem G d.g.property d.h.property

theorem clean : CleanBlockCycle A.label d.center ((A.top d.h).val d.center)
    ((A.top d.g).val d.center) d.cycle :=
  cleanBlockCycle_of_localized d.left d.right d.center d.meet

theorem distinct : d.center ≠ (A.top d.h).val d.center ∧
    d.center ≠ (A.top d.g).val d.center ∧
    (A.top d.h).val d.center ≠ (A.top d.g).val d.center :=
  local_triple_distinct _ _ (top_pair_separated _ _ d.center d.meet) ((d.meet d.center).mpr rfl)

theorem exists_conjugator (hcard : 5 ≤ Fintype.card I) (a b c : I)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ r : G, (A.top r).val d.center = a ∧
      (A.top r).val ((A.top d.h).val d.center) = b ∧
      (A.top r).val ((A.top d.g).val d.center) = c := by
  obtain ⟨t, ht, hta, htb, htc⟩ := even_perm_maps_triple hcard
    d.distinct.1 d.distinct.2.1 d.distinct.2.2 hab hac hbc
  obtain ⟨r, hr⟩ := A.top_surjective ⟨t, ht⟩
  exact ⟨r, by simpa [hr] using hta, by simpa [hr] using htb, by simpa [hr] using htc⟩

end LocalizedBlockPair
end GI
