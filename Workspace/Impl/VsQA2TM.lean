import Workspace.Impl.VsQASpinP
import Workspace.Impl.VsHPowIt
import Workspace.Impl.VsQTSplit

/-!
# Facts for the transitive case

* `vsQA_tblGroup`: the tables of `1 :: hs` form the value `encGroup` of the permutations of the
  pieces.
* `VsQDSz.sq`: the size bound `S` may be replaced by `S²`.
* `vsQABlks_length_le`, `vsQABlks_sum_le`: sizes of the list of block sums.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

theorem vsQA_tblGroup [Fact I.p.Prime] {hs : VsQStOK s} {as : List (Perm (Fin I.n))}
    {Lb : List (List (List ℕ))} (h : VsQAHyp hs as Lb) :
    Val.list [.nat (vsQAPcs s Lb).length, .list ((vsQMs s).map fun A => natList (vsQATb s Lb A))] =
      encGroup (s.hs.map (vsQAPiG h)) := by
  have hl : ((vsQMs s).map fun A => natList (vsQATb s Lb A)) =
      (1 :: s.hs.map (vsQAPiG h)).map encPerm := by
    rw [vsQMs, List.map_map, List.map_cons, List.map_cons, List.map_map]
    refine List.cons_eq_cons.2 ⟨?_, ?_⟩
    · have := vsQATb_eq h (one_mem (gens s.hs))
      rw [vsQAPiG_one] at this
      exact this
    · refine List.map_congr_left fun g hg => ?_
      exact vsQATb_eq h (Subgroup.subset_closure hg)
  rw [encGroup, encPerms, hl]

theorem VsQDSz.sq {S Tm : ℕ} (h : VsQDSz I S Tm) : VsQDSz I (S ^ 2) Tm := by
  have h1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  exact ⟨h.n.trans h1, h.d.trans h1, h.p.trans h1, h.g.trans h1, h.t.trans h1⟩

theorem vsQABlks_length_le (Pcs : List (List (List ℕ))) (labL : List ℕ) :
    (vsQABlks Pcs labL).length ≤ Pcs.length := by
  unfold vsQABlks
  exact (List.length_filter_le _ _).trans (by simp)

theorem vsQABlks_sum_le {Pcs : List (List (List ℕ))} {labL : List ℕ} {D : ℕ}
    (hsum : (Pcs.map List.length).sum ≤ D) :
    ((vsQABlks Pcs labL).map List.length).sum ≤ Pcs.length * D := by
  have h1 := List.sum_le_card_nsmul ((vsQABlks Pcs labL).map List.length) D (by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    unfold vsQABlks at hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hb)
    exact (vsQABlk_len c).trans hsum)
  simp only [List.length_map, smul_eq_mul] at h1
  exact h1.trans (Nat.mul_le_mul_right _ (vsQABlks_length_le Pcs labL))

end GI.Impl
