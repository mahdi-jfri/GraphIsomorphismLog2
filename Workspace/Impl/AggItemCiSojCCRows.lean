module

public import Workspace.Impl.AggItemCiSojCC

@[expose] public section

/-!
# Complete answer cosets indexed by query occurrence

The representation contract allows its recorded twist to be identity. The two
queries can then be equal states with different canonical representatives. Keep
one row per query occurrence, in order, without identifying equal twists.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Project representatives in query order, preserving repeated twists. -/
noncomputable def itcsAnswerReps (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R×Option rep.H)) : List (permitted W R) :=
  rows.filterMap fun row=>row.2.map fun h=>row.1*itcsRepMap rep h

/-- Complete projected cosets cover the transporter, including repeated query states. -/
theorem itcs_answer_rows_cover (rep : RectRep P₀ S L W R) (M N : W→R→Bool)
    (rows : List (permitted W R×Option rep.H))
    (horder : rows.map Prod.fst=itcsTwists rep)
    (hr : ∀ row∈rows,match row.2 with
      | none => (rep.state M N row.1).answer=∅
      | some g => g.val∈(rep.state M N row.1).answer)
    (p : permitted W R) :
    MatrixTransports M N p ↔ ∃ r∈itcsAnswerReps rep rows,
      p∈r • (((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep):Set (permitted W R)) := by
  rw [itcs_transporter_union]
  constructor
  · rintro ⟨t,ht,hp⟩
    rw [←horder] at ht
    obtain ⟨⟨t',r⟩,hrow,he⟩:=List.mem_map.1 ht
    change t'=t at he
    subst t'
    cases r with
    | none =>
      have hempty:=hr (t,none) hrow
      obtain ⟨_,⟨h,hh,-⟩,-⟩:=hp
      exact False.elim (show h.val∈(∅:Set (Perm Ω)) from hempty ▸ hh)
    | some g =>
      have hg:=hr (t,some g) hrow
      refine ⟨t*itcsRepMap rep g,?_,?_⟩
      · exact List.mem_filterMap.2 ⟨(t,some g),hrow,rfl⟩
      · rwa [itcs_twisted_answer_coset rep M N t g hg] at hp
  · rintro ⟨r,hrmem,hp⟩
    obtain ⟨⟨t,g⟩,hrow,he⟩:=List.mem_filterMap.1 hrmem
    cases g with
    | none => simp only [Option.map_none,reduceCtorEq] at he
    | some g =>
      simp only [Option.map_some,Option.some.injEq] at he
      subst r
      have hg:=hr (t,some g) hrow
      refine ⟨t,?_,?_⟩
      · rw [←horder]
        exact List.mem_map.2 ⟨(t,some g),hrow,rfl⟩
      · rwa [itcs_twisted_answer_coset rep M N t g hg]

/-- Representative differences recover all matrix automorphisms from the actual
query-occurrence rows and the common source generators. -/
theorem itcs_answer_rows_gens (rep : RectRep P₀ S L W R) (M N : W→R→Bool)
    (rows : List (permitted W R×Option rep.H))
    (horder : rows.map Prod.fst=itcsTwists rep)
    (hr : ∀ row∈rows,match row.2 with
      | none => (rep.state M N row.1).answer=∅
      | some g => g.val∈(rep.state M N row.1).answer)
    (sg : List (permitted W R))
    (hsg : itcsClosure sg=((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep))
    {p₀ : permitted W R} (h₀ : p₀∈itcsAnswerReps rep rows) :
    itcsClosure (itcsDiffGens p₀ (itcsAnswerReps rep rows) sg)=itcsMatrixAut M := by
  apply itcs_matrix_aut_gens M N _ sg h₀
  intro p
  rw [hsg]
  exact itcs_answer_rows_cover rep M N rows horder hr p

end GI.Impl
