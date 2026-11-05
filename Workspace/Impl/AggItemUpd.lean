module

public import Workspace.Impl.AggItemSrcP

@[expose] public section

/-!
# Updating the round's free choices during the items

The items fix, besides `num`, `hK` and `src` (`itRound`), the order of the branch tuples (`tups`),
the choices of the halving items (`halv`), of the first-rectangle items (`soj`) and the rectangle
representations (`rep`). None of them enters the certificate or comparison script, so a round
with these fields replaced is still a candidate of `ItHand` (`it_upd_mem`).

The joint refinement is fixed one argument at a time (`stSetJ`): first at the class colorings
(`κ`-ary), later at binary arguments in Cases 2b and 3. The source tuple reads only the `κ`-ary
value at the class colorings, so a later binary update keeps it (`itSrc_stSetJ_two`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm

variable {Ω C : Type} {P : Params} {S : State Ω C} {L : GiantLabels S}

/-- **The round `I` with the branch order, the halving choices, the first-rectangle choices and
the rectangle representations replaced**; every other field is that of `I`. -/
noncomputable def itUpd (I : Aggregation P S L) (tups : List (Fin (P.κ + 1) → Fin L.q))
    (hn : tups.Nodup) (hm : ∀ b, b ∈ tups) (hv : HalvingChoice S L) (sj : SojChoice)
    (rp : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R) :
    Aggregation P S L :=
  { I with tups := tups, tups_nodup := hn, mem_tups := hm, halv := hv, soj := sj, rep := rp }

section Upd

variable (I : Aggregation P S L) (tups : List (Fin (P.κ + 1) → Fin L.q)) (hn : tups.Nodup)
  (hm : ∀ b, b ∈ tups) (hv : HalvingChoice S L) (sj : SojChoice)
  (rp : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R)

theorem itUpd_certScript : (itUpd I tups hn hm hv sj rp).certScript = I.certScript := rfl
theorem itUpd_compScript : (itUpd I tups hn hm hv sj rp).compScript = I.compScript := rfl
theorem itUpd_tuples : (itUpd I tups hn hm hv sj rp).tuples = tups := rfl
theorem itUpd_halv : (itUpd I tups hn hm hv sj rp).halv = hv := rfl
theorem itUpd_soj : (itUpd I tups hn hm hv sj rp).soj = sj := rfl
theorem itUpd_hK : (itUpd I tups hn hm hv sj rp).hK = I.hK := rfl
theorem itUpd_src : (itUpd I tups hn hm hv sj rp).src = I.src := rfl
theorem itUpd_sel : (itUpd I tups hn hm hv sj rp).sel = I.sel := rfl
theorem itUpd_con : (itUpd I tups hn hm hv sj rp).con = I.con := rfl

end Upd

/-- **The updated round is a candidate** of `ItHand`, as `it_round_mem`. -/
theorem it_upd_mem {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {Ag₀ : Aggregation P₀ S L.toGiantLabels}
    (hsub : Cs ⊆ asRounds L) (h0 : Ag₀ ∈ Cs)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag.compScript = Ag₀.compScript →
      Ag ∈ Cs) (J : JointFn) (tups : List (Fin (P₀.κ + 1) → Fin L.q)) (hn : tups.Nodup)
    (hm : ∀ b, b ∈ tups) (hv : HalvingChoice S L.toGiantLabels) (sj : SojChoice)
    (rp : ∀ W R : Finset (Fin L.q), RectConds P₀ S L.toGiantLabels W R →
      RectRep P₀ S L.toGiantLabels W R) :
    itUpd (itRound Ag₀ J) tups hn hm hv sj rp ∈ Cs := by
  have h1 : Ag₀ ∈ asRounds L := hsub h0
  exact hcl _ h1 rfl rfl

/-- **A binary update of the joint refinement keeps the source tuple**: the source tuple reads
only the `κ`-ary value of `J` (`κ ≥ 5`). -/
theorem itSrc_stSetJ_two (Ag : Aggregation P₀ S L) (J : JointFn) (n : ℕ)
    (c c' d d' : (Fin 2 → Fin n) → ℕ) (h : JointOK c c' d d') :
    itSrc Ag (stSetJ J n 2 c c' d d' h) = itSrc Ag J := by
  have hκ : P₀.κ ≠ 2 := by have := Ag.κ_five; omega
  have e : stSetJ J n 2 c c' d d' h L.q P₀.κ = J L.q P₀.κ := stSetJ_ne J n 2 c c' d d' h hκ L.q
  rw [itSrc_eq_of, itSrc_eq_of]
  have hg : (itX0 Ag (stSetJ J n 2 c c' d d' h)).grp = (itX0 Ag J).grp := rfl
  have hc : (itX0 Ag (stSetJ J n 2 c c' d d' h)).col = (itX0 Ag J).col := by
    show (stSetJ J n 2 c c' d d' h L.q P₀.κ _ _).1.1 = (J L.q P₀.κ _ _).1.1
    rw [e]
  rw [hg, hc]

end GI.Impl
