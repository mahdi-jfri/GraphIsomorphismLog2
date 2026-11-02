import Workspace.Impl.AggItemCiCfgA
import Workspace.Impl.AggItemC1Sch

/-!
# The configuration query: the even representative and the item

With `p₁` a map of the fibers that keeps the pair colors, and `S` the generators of the
automorphisms on the fiber (`itci_mg_closure`):
* `itcqRep (itciExt X Y p₁) S`: `σ₀ = itciExt X Y p₁` if it is even, else `σ₀ t` for the first odd
  generator `t`, else nothing. Every permutation that maps `X` to `Y` on the fiber is `σ₀ g` with
  `g` an automorphism (`itcq_maps_iff`), so this finds an even one exactly when one exists.
* `itcqEG S`: the Schreier list of the first odd generator `t` in the form of the Case 1
  program (`itSchE`: `s`, `t s t` for even `s`; `s t`, `t s` for odd `s`), or `S` if all are
  even; it generates `autE X` (`itcq_eg_gens`). Since `t ∈ S` is odd, `t²` is in both lists, so
  this list and the textbook list `itciSch` (with `t⁻¹`) generate the same group
  (`itcq_sch_closure`).
* `itcq_item`: the item script `cfgItem X Y` asks the pair structure, and its result for the
  exact answer is the overcoset of the program's representative.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup)

noncomputable section

variable {q : ℕ}

/-- The first odd permutation of a list. -/
def itcqOdd (S : List (Perm (Fin q))) : Option (Perm (Fin q)) := S.find? fun s => sign s ≠ 1

/-- The even representative. -/
def itcqRep (σ₀ : Perm (Fin q)) (S : List (Perm (Fin q))) : Option (Perm (Fin q)) :=
  if sign σ₀ = 1 then some σ₀ else (itcqOdd S).map (σ₀ * ·)

/-- The generators of the even part. -/
def itcqEG (S : List (Perm (Fin q))) : List (Perm (Fin q)) :=
  match itcqOdd S with
  | some t => (List.range (2 * S.length)).map (itSchE t S)
  | none => S

theorem itcqOdd_some {S : List (Perm (Fin q))} {t : Perm (Fin q)} (h : itcqOdd S = some t) :
    t ∈ S ∧ sign t = -1 := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [ne_eq, decide_eq_true_eq] at h2
  exact ⟨h1, (itp_sign_cases t).resolve_left h2⟩

theorem itcqOdd_none {S : List (Perm (Fin q))} (h : itcqOdd S = none) :
    ∀ s ∈ S, sign s = 1 := by
  intro s hs
  have := List.find?_eq_none.1 h s hs
  simpa using this

/-- **The two Schreier lists generate the same group** when the odd element `t` is in `S`. -/
theorem itcq_sch_closure {t : Perm (Fin q)} {S : List (Perm (Fin q))} (ht : t ∈ S)
    (hs : sign t = -1) :
    Subgroup.closure {g | g ∈ (List.range (2 * S.length)).map (itSchE t S)} =
      Subgroup.closure {g | g ∈ itciSch t S} := by
  have hto : sign t ≠ 1 := by rw [hs]; decide
  have h1 : t * t ∈ itciSch t S := itci_mem_sch.2 ⟨t, ht, Or.inr ⟨hto, Or.inr rfl⟩⟩
  have h2 : t * t ∈ itpSch t S := itp_mem_sch.2 ⟨t, ht, Or.inr ⟨hto, Or.inr rfl⟩⟩
  have e : {g | g ∈ (List.range (2 * S.length)).map (itSchE t S)} = {g | g ∈ itpSch t S} := by
    ext g; exact itSchE_mem t S g
  rw [e]
  refine le_antisymm ((Subgroup.closure_le _).2 fun g hg => ?_)
    ((Subgroup.closure_le _).2 fun g hg => ?_)
  · have htt : t * t ∈ Subgroup.closure {g | g ∈ itciSch t S} := Subgroup.subset_closure h1
    obtain ⟨s, hsS, (⟨hse, rfl | rfl⟩ | ⟨hso, rfl | rfl⟩)⟩ := itp_mem_sch.1 hg
    · exact Subgroup.subset_closure (itci_mem_sch.2 ⟨_, hsS, Or.inl ⟨hse, Or.inl rfl⟩⟩)
    · have hm : t * s * t⁻¹ ∈ Subgroup.closure {g | g ∈ itciSch t S} :=
        Subgroup.subset_closure (itci_mem_sch.2 ⟨s, hsS, Or.inl ⟨hse, Or.inr rfl⟩⟩)
      have := Subgroup.mul_mem _ hm htt
      simpa [mul_assoc] using this
    · have hm : s * t⁻¹ ∈ Subgroup.closure {g | g ∈ itciSch t S} :=
        Subgroup.subset_closure (itci_mem_sch.2 ⟨s, hsS, Or.inr ⟨hso, Or.inl rfl⟩⟩)
      have := Subgroup.mul_mem _ hm htt
      simpa [mul_assoc] using this
    · exact Subgroup.subset_closure (itci_mem_sch.2 ⟨s, hsS, Or.inr ⟨hso, Or.inr rfl⟩⟩)
  · have htt : (t * t)⁻¹ ∈ Subgroup.closure {g | g ∈ itpSch t S} :=
      Subgroup.inv_mem _ (Subgroup.subset_closure h2)
    obtain ⟨s, hsS, (⟨hse, rfl | rfl⟩ | ⟨hso, rfl | rfl⟩)⟩ := itci_mem_sch.1 hg
    · exact Subgroup.subset_closure (itp_mem_sch.2 ⟨_, hsS, Or.inl ⟨hse, Or.inl rfl⟩⟩)
    · have hm : t * s * t ∈ Subgroup.closure {g | g ∈ itpSch t S} :=
        Subgroup.subset_closure (itp_mem_sch.2 ⟨s, hsS, Or.inl ⟨hse, Or.inr rfl⟩⟩)
      have := Subgroup.mul_mem _ hm htt
      simpa [mul_assoc] using this
    · have hm : s * t ∈ Subgroup.closure {g | g ∈ itpSch t S} :=
        Subgroup.subset_closure (itp_mem_sch.2 ⟨s, hsS, Or.inr ⟨hso, Or.inl rfl⟩⟩)
      have := Subgroup.mul_mem _ hm htt
      simpa [mul_assoc] using this
    · exact Subgroup.subset_closure (itp_mem_sch.2 ⟨s, hsS, Or.inr ⟨hso, Or.inr rfl⟩⟩)

/-- **The generators of the even part.** -/
theorem itcq_eg_gens (S : List (Perm (Fin q))) :
    gens (itcqEG S) = gens S ⊓ alternatingGroup (Fin q) := by
  unfold itcqEG
  cases h : itcqOdd S with
  | some t =>
    obtain ⟨ht, hs⟩ := itcqOdd_some h
    show Subgroup.closure _ = _
    rw [itcq_sch_closure ht hs]
    exact itci_schreier (Subgroup.subset_closure ht) hs
  | none =>
    have hle : gens S ≤ alternatingGroup (Fin q) :=
      (Subgroup.closure_le _).2 fun s hs => itcqOdd_none h s hs
    exact (inf_eq_left.2 hle).symm

/-- **The maps from `X` to `Y` on the fiber** are `σ₀ g` with `g` an automorphism. -/
theorem itcq_maps_iff {X Y : PairCfg q} {σ₀ σ : Perm (Fin q)} (h₀ : PairCfg.Maps X Y σ₀) :
    PairCfg.Maps X Y σ ↔ σ₀⁻¹ * σ ∈ itciMG X :=
  ⟨fun h => PairCfg.Maps.coset h₀ h, fun h => by
    have := PairCfg.Maps.comp (itci_mem_mg.1 h) h₀
    rwa [mul_inv_cancel_left] at this⟩

/-- **The representative is an even map**, when there is one. -/
theorem itcq_rep_some {X Y : PairCfg q} {σ₀ : Perm (Fin q)} (h₀ : PairCfg.Maps X Y σ₀)
    {S : List (Perm (Fin q))} (hS : gens S = itciMG X) {σ : Perm (Fin q)}
    (h : itcqRep σ₀ S = some σ) : sign σ = 1 ∧ PairCfg.Maps X Y σ := by
  unfold itcqRep at h
  split_ifs at h with h1
  · cases h; exact ⟨h1, h₀⟩
  · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨htS, hts⟩ := itcqOdd_some ht
    refine ⟨?_, (itcq_maps_iff h₀).2 ?_⟩
    · rw [Perm.sign_mul, (itp_sign_cases σ₀).resolve_left h1, hts]; decide
    · rw [inv_mul_cancel_left, ← hS]; exact Subgroup.subset_closure htS

/-- **No representative: no even map.** -/
theorem itcq_rep_none {X Y : PairCfg q} {σ₀ : Perm (Fin q)} (h₀ : PairCfg.Maps X Y σ₀)
    {S : List (Perm (Fin q))} (hS : gens S = itciMG X) (h : itcqRep σ₀ S = none)
    {σ : Perm (Fin q)} (hσ : PairCfg.Maps X Y σ) : sign σ ≠ 1 := by
  unfold itcqRep at h
  split_ifs at h with h1
  have hn : itcqOdd S = none := Option.map_eq_none_iff.1 h
  have hle : gens S ≤ alternatingGroup (Fin q) :=
    (Subgroup.closure_le _).2 fun s hs => itcqOdd_none hn s hs
  have hg : σ₀⁻¹ * σ ∈ alternatingGroup (Fin q) := hle (hS ▸ (itcq_maps_iff h₀).1 hσ)
  intro hs
  apply h1
  have : sign (σ₀⁻¹ * σ) = 1 := hg
  rw [Perm.sign_mul, Perm.sign_inv, hs, mul_one] at this
  have h2 := congrArg (·⁻¹) this
  simpa using h2

/-- The program's overcosets of the configuration query. -/
def itcqOs (X : PairCfg q) (σ₀ : Perm (Fin q)) (S : List (Perm (Fin q))) : List (LcOver q) :=
  match itcqRep σ₀ S with
  | some σ => if h : sign σ = 1 then [(⟨σ, h⟩, X.autE, itcqEG S)] else []
  | none => []

theorem itcqOs_gens {X : PairCfg q} {σ₀ : Perm (Fin q)} {S : List (Perm (Fin q))}
    (hS : gens S = itciMG X) :
    ∀ o ∈ itcqOs X σ₀ S, gens o.2.2 = o.2.1.map (alternatingGroup (Fin q)).subtype := by
  intro o ho
  unfold itcqOs at ho
  split at ho
  · split_ifs at ho
    · rw [List.mem_singleton] at ho
      subst ho
      rw [itcq_eg_gens, hS, itci_autE_map]
    · simp at ho
  · simp at ho

variable {Ω C : Type} {S : State Ω C}

/-- **The item of a configuration branch with fibers of the same size**: it asks the pair
structure, and for the exact answer its result is the program's overcoset (`asOvAt`). -/
theorem itcq_item (L : GiantLabels S) {X Y : PairCfg L.q} (hc : X.fiber.card = Y.fiber.card)
    {p₁ : Perm (Fin X.fiber.card)} (hp₁ : ItciKeeps X Y hc p₁) (hal : ItciAl X Y)
    {Sg : List (Perm (Fin L.q))} (hS : gens Sg = itciMG X) :
    (cfgItem (P := P₀) X Y : AuxItem P₀ S L).script =
        Script.ask .solve (itcqPT X Y hc) (fun A => Script.done
          ⟨[], [(cfgQuery (P := P₀) X Y hc).read A].reduceOption.map
            (AuxItem.liftOver L X.autE)⟩) ∧
      ∃ ovs, [(cfgQuery (P := P₀) (S := S) (L := L) X Y hc).read (itcqPT X Y hc).answer].reduceOption.map
          (AuxItem.liftOver L X.autE) = ovs ∧
        List.Forall₂ (asOvAt L) (itcqOs X (itciExt X Y p₁) Sg) ovs := by
  classical
  refine ⟨?_, _, rfl, ?_⟩
  · simp only [cfgItem, dif_pos hc]
    rfl
  have h₀ := itci_ext_maps hc hp₁ hal
  have hcov := cfgQuery_covers (P := P₀) (S := S) (L := L) hc
  unfold itcqOs
  cases hr : itcqRep (itciExt X Y p₁) Sg with
  | some σ =>
    obtain ⟨hs, hm⟩ := itcq_rep_some h₀ hS hr
    obtain ⟨τ, hτ⟩ := hcov σ ⟨⟨σ, hs⟩, rfl, hm⟩
    have hτm := cfgQuery_read_maps (P := P₀) (S := S) (L := L) hc hτ
    simp only [dif_pos hs]
    change List.Forall₂ _ _ ([(cfgQuery X Y hc).read (cfgQuery X Y hc).T.answer].reduceOption.map _)
    rw [hτ]
    simp only [List.reduceOption_cons_of_some, List.reduceOption_nil, List.map_cons, List.map_nil]
    refine List.Forall₂.cons (it_ovAt_of_mem L ?_ _) List.Forall₂.nil
    show ((τ : Perm (Fin L.q))⁻¹ * σ) ∈ itciMG X
    exact (itcq_maps_iff hτm).1 hm
  | none =>
    have hnone : (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).read
        (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).T.answer = none := by
      cases h : (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).read
          (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).T.answer with
      | none => rfl
      | some τ =>
        exact absurd τ.2 (itcq_rep_none h₀ hS hr (cfgQuery_read_maps hc h))
    change List.Forall₂ _ _ ([(cfgQuery X Y hc).read (cfgQuery X Y hc).T.answer].reduceOption.map _)
    rw [hnone]
    simp only [List.reduceOption_cons_of_none, List.reduceOption_nil, List.map_nil]
    exact List.Forall₂.nil

/-- **When the outer classes cannot be aligned, the query reads nothing** ("align those
classes", Lemma A.12): every map it could read keeps the outer classes. -/
theorem itcq_read_nal (L : GiantLabels S) {X Y : PairCfg L.q} (hc : X.fiber.card = Y.fiber.card)
    (hal : ¬ ItciAl X Y) :
    (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).read
      (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).T.answer = none := by
  cases h : (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).read
      (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).T.answer with
  | none => rfl
  | some τ => exact absurd (itci_al_of_maps (cfgQuery_read_maps hc h)) hal

end

end GI.Impl
