module

public import Workspace.JohnsonForest

@[expose] public section

namespace GI.Johnson.RefinementTree

variable {α : Type*} [DecidableEq α]

def regionsUnion : List (RefinementTree α) → Finset α
  | [] => ∅
  | t :: ts => t.region ∪ regionsUnion ts

/-- Attach fresh branches while the accumulating branch continues the original
token. Its region always contains the initially selected largest region. -/
def mergeTrees (main : RefinementTree α) : List (RefinementTree α) → RefinementTree α
  | [] => main
  | t :: ts => mergeTrees (.fork (main.region ∪ t.region) main t) ts

theorem mergeTrees_region (main : RefinementTree α) (fresh : List (RefinementTree α)) :
    (mergeTrees main fresh).region = main.region ∪ regionsUnion fresh := by
  induction fresh generalizing main with
  | nil => simp [mergeTrees, regionsUnion]
  | cons t ts ih =>
    rw [mergeTrees, ih]
    simp only [region, regionsUnion, Finset.union_assoc]

theorem mergeTrees_extraStarts (main : RefinementTree α) (fresh : List (RefinementTree α)) :
    (mergeTrees main fresh).extraStarts = main.extraStarts ++ fresh.flatMap starts := by
  induction fresh generalizing main with
  | nil => simp [mergeTrees]
  | cons t ts ih =>
    simp only [mergeTrees, ih, extraStarts, List.flatMap_cons, starts, List.append_assoc]

theorem mergeTrees_leaves (main : RefinementTree α) (fresh : List (RefinementTree α)) :
    (mergeTrees main fresh).leaves = main.leaves + (fresh.map leaves).sum := by
  induction fresh generalizing main with
  | nil => simp [mergeTrees]
  | cons t ts ih =>
    simp only [mergeTrees, ih, leaves, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem regionsUnion_subset {fresh : List (RefinementTree α)} {E : Finset α}
    (hsub : ∀ t ∈ fresh, t.region ⊆ E) : regionsUnion fresh ⊆ E := by
  induction fresh with
  | nil => exact Finset.empty_subset E
  | cons t ts ih =>
    exact Finset.union_subset (hsub t (List.mem_cons_self ..))
      (ih (fun u hu => hsub u (List.mem_cons_of_mem _ hu)))

theorem mergeTrees_valid {anchors : Finset α} (main : RefinementTree α)
    (fresh : List (RefinementTree α)) (hm : main.Valid anchors)
    (hv : ∀ t ∈ fresh, t.Valid anchors)
    (hd : (main :: fresh).Pairwise (fun t u => Disjoint t.region u.region))
    (hl : ∀ t ∈ fresh, t.region.card ≤ main.region.card) :
    (mergeTrees main fresh).Valid anchors := by
  induction fresh generalizing main with
  | nil => exact hm
  | cons t ts ih =>
    obtain ⟨hdmain, hdtail⟩ := List.pairwise_cons.mp hd
    obtain ⟨hdt, hdts⟩ := List.pairwise_cons.mp hdtail
    let node := RefinementTree.fork (main.region ∪ t.region) main t
    have hn : node.Valid anchors := by
      refine ⟨(valid_card hm).trans (Finset.card_le_card Finset.subset_union_left),
        hm, hv t (List.mem_cons_self ..), Finset.subset_union_left,
        Finset.subset_union_right, hdmain t (List.mem_cons_self ..),
        hl t (List.mem_cons_self ..)⟩
    have hdn : (node :: ts).Pairwise (fun a b => Disjoint a.region b.region) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, hdts⟩
      intro u hu
      exact Finset.disjoint_union_left.mpr
        ⟨hdmain u (List.mem_cons_of_mem _ hu), hdt u hu⟩
    have hln : ∀ u ∈ ts, u.region.card ≤ node.region.card := by
      intro u hu
      exact (hl u (List.mem_cons_of_mem _ hu)).trans
        (Finset.card_le_card Finset.subset_union_left)
    exact ih node hn (fun u hu => hv u (List.mem_cons_of_mem _ hu)) hdn hln

def mergeAt (E : Finset α) (main : RefinementTree α) (fresh : List (RefinementTree α)) :
    RefinementTree α := .shrink E (mergeTrees main fresh)

theorem mergeAt_region (E : Finset α) (main : RefinementTree α)
    (fresh : List (RefinementTree α)) : (mergeAt E main fresh).region = E := rfl

theorem mergeAt_extraStarts (E : Finset α) (main : RefinementTree α)
    (fresh : List (RefinementTree α)) :
    (mergeAt E main fresh).extraStarts = main.extraStarts ++ fresh.flatMap starts :=
  mergeTrees_extraStarts main fresh

theorem mergeAt_leaves (E : Finset α) (main : RefinementTree α)
    (fresh : List (RefinementTree α)) :
    (mergeAt E main fresh).leaves = main.leaves + (fresh.map leaves).sum :=
  mergeTrees_leaves main fresh

theorem mergeAt_valid {anchors E : Finset α} (main : RefinementTree α)
    (fresh : List (RefinementTree α)) (hm : main.Valid anchors)
    (hv : ∀ t ∈ fresh, t.Valid anchors)
    (hd : (main :: fresh).Pairwise (fun t u => Disjoint t.region u.region))
    (hl : ∀ t ∈ fresh, t.region.card ≤ main.region.card)
    (hmE : main.region ⊆ E) (hfE : ∀ t ∈ fresh, t.region ⊆ E) :
    (mergeAt E main fresh).Valid anchors := by
  refine ⟨(valid_card hm).trans (Finset.card_le_card hmE),
    mergeTrees_valid main fresh hm hv hd hl, ?_⟩
  rw [mergeTrees_region]
  exact Finset.union_subset hmE (regionsUnion_subset hfE)

theorem mergeAt_extra_allowance (E : Finset α) (main : RefinementTree α)
    (fresh : List (RefinementTree α)) (C B : ℝ) :
    ((mergeAt E main fresh).extraStarts.map (fun (w : ℕ) => C * Real.log (w : ℝ) - B)).sum =
      (main.extraStarts.map (fun (w : ℕ) => C * Real.log (w : ℝ) - B)).sum +
      (fresh.map (fun t => (t.starts.map (fun (w : ℕ) => C * Real.log (w : ℝ) - B)).sum)).sum := by
  rw [mergeAt_extraStarts, List.map_append, List.sum_append]
  congr 1
  induction fresh with
  | nil => rfl
  | cons t ts ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

end GI.Johnson.RefinementTree
