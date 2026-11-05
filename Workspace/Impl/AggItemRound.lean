module

public import Workspace.Impl.AggItemCase
public import Workspace.Impl.AggStructDes

@[expose] public section

/-!
# The round that the items fix

The items choose three fields of the round that the certificate and comparison scripts do not
read (`ItHand`): the class numbers `num`, the joint refinement `hK` and the source tuple `src`.
This file names the choice and shows that it gives a member of the candidate set.

* `num`: the numbers by first occurrence along all `κ`-tuples, `stNum (stTs q κ) x`. The program
  computes exactly these colors (`stCz_tcol`).
* `hK`: any joint refinement `J`; the program fixes its value at the pair of class colorings to
  the output `(d, d')` of the cited call (`stSetJ`), and in Case 2b later at binary arguments.
* `src` (`itSrc`): by the case of `π(F_x)` (which does not depend on the choices,
  `st_structX_grp`): in Case 2b the eight smallest points of the dominant orbit (`stSrc2b`), in
  Case 3 the first tuple that passes the test of the Design Lemma on the refined colors of `x`
  (`stSrc3`), otherwise the zero tuple. It is good for every `J` (`itSrc_good`), by
  `stSrcGood_twoB'`, `stSrcGood_three'` and `stSrcGood_other`; the cited fact used is the
  round's own field `hD` (Case 3).

`itRound Ag J := stRound Ag (stNum …) _ J (itSrc Ag J) _`; `it_round_mem`: it lies in the
candidate set of `ItHand`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm

variable {Ω C : Type} {k : ℕ}

section Round

variable {S : State Ω C} {L : GiantLabels S}

/-- The class numbers that the items use. -/
noncomputable def itNum (Ag : Aggregation P₀ S L) : ClassNum S P₀.κ L.q :=
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  stNum S P₀.κ (stTs L.q P₀.κ) (dstr S S.x)

theorem itNum_ok (Ag : Aggregation P₀ S L) : ClassNum.OK Ag.fin S L Ag.πd P₀.κ (itNum Ag) :=
  stNum_ok Ag.fin S L Ag.πd P₀.κ _ mem_stTs

theorem it_q_pos (Ag : Aggregation P₀ S L) : 0 < L.q := by have := Ag.q_two; omega

theorem it_q_large (Ag : Aggregation P₀ S L) : 4 * P₀.κ + 2 < L.q :=
  lt_of_le_of_lt Ag.params.q₀_cert Ag.q_large

/-- The structure of `x` with the zero tuple (its group and colors do not depend on the
tuple). -/
noncomputable def itX0 (Ag : Aggregation P₀ S L) (J : JointFn) : GI.Algorithm.Canon L.q P₀.κ (P₀.κ + 1) :=
  structX Ag.fin S L Ag.πd J P₀.κ (itNum Ag) fun _ => ⟨0, it_q_pos Ag⟩

/-- **The source tuple that the items choose.** -/
noncomputable def itSrc (Ag : Aggregation P₀ S L) (J : JointFn) : Fin (P₀.κ + 1) → Fin L.q :=
  match aggCase (itX0 Ag J).grp with
  | .twoB => if h : 8 ≤ (domSet (itX0 Ag J).grp).card then stSrc2b _ h else fun _ => ⟨0, it_q_pos Ag⟩
  | .three => stSrc3 (itX0 Ag J).col (Nat.lt_succ_self _) (it_q_pos Ag)
  | .one => fun _ => ⟨0, it_q_pos Ag⟩
  | .twoA => fun _ => ⟨0, it_q_pos Ag⟩

/-- **The chosen source tuple is good** for every joint refinement `J`. -/
theorem itSrc_good (Ag : Aggregation P₀ S L) (J : JointFn) :
    StSrcGood Ag.fin S L Ag.πd J P₀.κ (itNum Ag) P₀.β (itSrc Ag J) := by
  have hq := it_q_large Ag
  have hκ := Ag.κ_five
  have hκ7 : 7 ≤ P₀.κ := by norm_num [P₀]
  have hgrp : ∀ t : Fin (P₀.κ + 1) → Fin L.q,
      (structX Ag.fin S L Ag.πd J P₀.κ (itNum Ag) t).grp = (itX0 Ag J).grp := fun _ => rfl
  unfold itSrc
  cases h : aggCase (itX0 Ag J).grp with
  | one => exact stSrcGood_other _ _ _ _ _ _ _ _ (Or.inl (by rw [hgrp]; exact h))
  | twoA => exact stSrcGood_other _ _ _ _ _ _ _ _ (Or.inr (by rw [hgrp]; exact h))
  | twoB =>
    have h8 : 8 ≤ (domSet (itX0 Ag J).grp).card := st_domSet_eight (by omega) h
    simp only [dif_pos h8]
    exact stSrcGood_twoB' Ag.fin S L Ag.πd J P₀.κ (itNum Ag) (by omega) (by omega) h h8
  | three =>
    exact stSrcGood_three' Ag.hD Ag.fin S L Ag.πd J (itNum Ag) (itNum_ok Ag)
      (le_trans (by norm_num) Ag.β_cfg) hκ (by omega) (by omega) (Nat.lt_succ_self _) h

/-- **The round that the items fix**, for the joint refinement `J`. -/
noncomputable def itRound
    (Ag : Aggregation P₀ S L) (J : JointFn) : Aggregation P₀ S L :=
  stRound Ag (itNum Ag) (itNum_ok Ag) J (itSrc Ag J) (itSrc_good Ag J)

theorem itRound_certScript (Ag : Aggregation P₀ S L) (J : JointFn) :
    (itRound Ag J).certScript = Ag.certScript := rfl

theorem itRound_compScript (Ag : Aggregation P₀ S L) (J : JointFn) :
    (itRound Ag J).compScript = Ag.compScript := rfl

theorem itRound_hK
    (Ag : Aggregation P₀ S L) (J : JointFn) : (itRound Ag J).hK = J := rfl

theorem itRound_src (Ag : Aggregation P₀ S L) (J : JointFn) :
    (itRound Ag J).src = itSrc Ag J := rfl

/-- **The class colors of the program are those of the round**: the colors `stCz (stRel …) z`
that `it_col_spec` refines are the tuple colorings of `x` and `y` under `itNum`. -/
theorem it_cz_tcol (Ag : Aggregation P₀ S L) :
    haveI := Ag.fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq S.dom := Classical.decEq _
    stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 0 =
        tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.x) ∧
      stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 1 =
        tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.y) :=
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  stCz_tcol S Ag.πd P₀.κ _ _

end Round

/-- **The chosen round is a candidate**: for the round `Ag₀` of `ItHand`, `itRound Ag₀ J`
lies in the candidate set, since it has the certificate and comparison scripts of `Ag₀` and the
interval and constituent of the labels. -/
theorem it_round_mem {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {Ag₀ : Aggregation P₀ S L.toGiantLabels}
    (hsub : Cs ⊆ asRounds L) (h0 : Ag₀ ∈ Cs)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag.compScript = Ag₀.compScript →
      Ag ∈ Cs) (J : JointFn) : itRound Ag₀ J ∈ Cs := by
  have h1 : Ag₀ ∈ asRounds L := hsub h0
  exact hcl (itRound Ag₀ J) h1 rfl rfl

end GI.Impl
