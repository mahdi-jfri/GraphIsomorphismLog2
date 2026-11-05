module

public import Workspace.Impl.LinObjectPairTable
public import Workspace.Impl.LinObjectOffsetMath
public import Workspace.Impl.LinForallList

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

def linObjectTableRow {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (targets : List (List (TmRiO n))) (S : List (TmRiO n)) (row : List Val) : Prop :=
  List.Forall₂ (fun T v => CosetC n v (Iso A (tmGlMs S) (tmGlMs T))) targets row

theorem linObjectPairTable_rows {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))}
    {Ps : List (List (TmRiO n))} {tab : List Val} (ht : TmRiTab A Ps tab) :
    ∃ rows : List (List Val), tab = rows.map Val.list ∧ List.Forall₂ (linObjectTableRow A Ps) Ps rows := by
  have hs : List.Forall₂ (fun sv rv => ∃ S, sv = tmGlObjsVal S ∧
      ∃ row, rv = .list row ∧ linObjectTableRow A Ps S row) (Ps.map tmGlObjsVal) tab := by
    refine ht.imp fun sv rv ⟨S, _, he, row, hv, hr⟩ => ⟨S, he, row, hv, ?_⟩
    exact linForall₂_source tmGlObjsVal linObjectListEncoding_injective _
      (hr.imp fun tv u ⟨T, _, he, hC⟩ => ⟨T, he, hC⟩)
  exact linForall₂_encoded Val.list _
    (linForall₂_source tmGlObjsVal linObjectListEncoding_injective _ hs)

theorem linObjectTableRow_window {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))}
    {refs targets : List (List (TmRiO n))} {S : List (TmRiO n)} {row : List Val}
    (hr : linObjectTableRow A (refs ++ targets) S row) :
    linObjectTableRow A targets S ((row.drop refs.length).take targets.length) := by
  have hh := linForall₂_drop hr refs.length
  rw [List.drop_left] at hh
  have hh' := linForall₂_take hh targets.length
  simpa only [linObjectTableRow, List.take_length] using hh'

theorem linObjectCoset_rep_mem {n : ℕ} {a : Equiv.Perm (Fin n)}
    {gs : List (Equiv.Perm (Fin n))} {C : Set (Equiv.Perm (Fin n))}
    (hc : CosetC n (.list [encPerm a, encGroup gs]) C) : a ∈ C := by
  rcases hc with ⟨he, _⟩ | ⟨b, bs, hv, _, hC⟩
  · simp at he
  · exact CosetVal.rep_mem ⟨b, bs, hv, hC⟩

def linObjectOffsetRowRel {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (refs targets : List (List (TmRiO n))) (Z : Multiset (GI.Multicoset.CObj ℕ (Equiv.Perm (Fin n))))
    (row : List Val) (a : Equiv.Perm (Fin n)) : Prop :=
  ∀ S ∈ refs, linObjectTableRow A (refs ++ targets) S row →
    a ∈ A ∧ tmGlMs S ↼ a = partAt A Z (tmGlMs S)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectOffsetRow_shapes {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (Y Z : Multiset (GI.Multicoset.CObj ℕ (Equiv.Perm (Fin n))))
    (refs targets : List (List (TmRiO n))) (row : List Val)
    (hRef : ∀ S ∈ refs, tmGlMs S ∈ pieces A Y)
    (hTar : ∀ T ∈ targets, tmGlMs T ∈ pieces A Z)
    (hr : ∃ S ∈ refs, linObjectTableRow A (refs ++ targets) S row) :
    ∀ v ∈ (row.drop refs.length).take targets.length,
      v = .list [] ∨ ∃ (a : Equiv.Perm (Fin n)) (gs : List (Equiv.Perm (Fin n))),
        v = .list [encPerm a, encGroup gs] ∧ linObjectOffsetRowRel A refs targets Z row a := by
  intro v hv
  obtain ⟨S, hS, hrow⟩ := hr
  obtain ⟨T, hT, hC⟩ := linForall₂_mem_right (linObjectTableRow_window hrow) hv
  rcases hC with ⟨he, _⟩ | ⟨a, gs, rfl, _, _⟩
  · exact Or.inl he
  · refine Or.inr ⟨a, gs, rfl, ?_⟩
    intro S' hS' hrow'
    obtain ⟨T', hT', hC'⟩ := linForall₂_mem_right (linObjectTableRow_window hrow') hv
    have ha := linObjectCoset_rep_mem hC'
    exact ⟨ha.1, ha.2.trans (linObjectConfig_piece_transport_unique (hRef S' hS') (hTar T' hT') ha)⟩

set_option maxHeartbeats 1000000 in
theorem linObjectOffsetRow_exists {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (Y Z : Multiset (GI.Multicoset.CObj ℕ (Equiv.Perm (Fin n)))) (hZ : Conf A Y Z)
    (refs targets : List (List (TmRiO n))) (S : List (TmRiO n)) (row : List Val)
    (hS : tmGlMs S ∈ pieces A Y)
    (hTar : ∀ T ∈ pieces A Z, ∃ Tl ∈ targets, tmGlMs Tl = T)
    (hr : linObjectTableRow A (refs ++ targets) S row) :
    ∃ v ∈ (row.drop refs.length).take targets.length, v ≠ .list [] := by
  obtain ⟨T, hT, hne⟩ := linObjectConfig_piece_transport hZ hS
  obtain ⟨Tl, hTl, he⟩ := hTar T hT
  obtain ⟨v, hv, hC⟩ := linForall₂_mem_left (linObjectTableRow_window hr) hTl
  refine ⟨v, hv, ?_⟩
  intro hv0
  rw [he] at hC
  rcases hC with ⟨_, hEmpty⟩ | ⟨a, gs, hval, _, _⟩
  · exact hne.ne_empty hEmpty
  · rw [hv0] at hval
    simp at hval

theorem linObjectOffsetRows_sound {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))}
    {refs targets : List (List (TmRiO n))}
    {Z : Multiset (GI.Multicoset.CObj ℕ (Equiv.Perm (Fin n)))}
    {rows : List (List Val)} {gs : List (Equiv.Perm (Fin n))}
    (hr : List.Forall₂ (linObjectTableRow A (refs ++ targets)) refs rows)
    (hg : List.Forall₂ (linObjectOffsetRowRel A refs targets Z) rows gs) :
    List.Forall₂ (fun S a => a ∈ A ∧ tmGlMs S ↼ a = partAt A Z (tmGlMs S)) refs gs := by
  apply List.forall₂_iff_get.mpr
  refine ⟨hr.length_eq.trans hg.length_eq, ?_⟩
  intro i hi hj
  have hirow : i < rows.length := by rw [← hr.length_eq]; exact hi
  have hs := hr.get hi hirow
  have ha := hg.get hirow hj
  exact ha _ (List.get_mem _ _) hs

end GI.Impl
