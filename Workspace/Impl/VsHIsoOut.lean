module

public import Workspace.Impl.VsHIso

@[expose] public section

/-!
# What the two passes compute

From the hand-off of step 4 (`VsMHard H̄ Ā Ȳ r` with `Ȳ = ⟨ȳs⟩ S`):

1. the basis pass over `ys` gives `B`, with `r ^ |B| ≤ D²` (`vsHBas_out`);
2. the words `E = vsPEnum r B` cover `Ȳ` modulo `S` (`vsH_cover_E`);
3. the isotropic pass over `E` gives `K` with `VsMIso Ā Ȳ r (ρ ∘ K)` and `r ^ |prefix| ≤ D²`
   along the pass (`vsHIso_out`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]

/-- The data of the hard case: the hand-off of step 4 with its hypotheses. -/
structure VsHHyp (hs : VsQStOK s) (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ)))
    (ys : List (Perm (Fin I.n))) (r : ℕ) : Prop where
  has : gens as ≤ gens s.hs
  hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M
  hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
    (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s))))
  hys : ∀ y ∈ ys, y ∈ gens s.hs
  hard : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as))
    (vsPBar hs (gens ys) ⊔ vsMScal (vsPBar hs (gens as))) r

variable {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
  {ys : List (Perm (Fin I.n))} {r : ℕ}

/-- The scalars `S`. -/
noncomputable abbrev vsHS (hs : VsQStOK s) (as : List (Perm (Fin I.n))) :
    Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ :=
  vsMScal (vsPBar hs (gens as))

/-- `Ȳ`. -/
noncomputable abbrev vsHY (hs : VsQStOK s) (as ys : List (Perm (Fin I.n))) :
    Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ :=
  vsPBar hs (gens ys) ⊔ vsHS hs as

/-- The basis of `Ȳ` modulo `S`. -/
noncomputable def vsHB (s : VsQSt I) (Lb : List (List (List ℕ))) (r : ℕ) (ys : List (Perm (Fin I.n))) :
    List (Perm (Fin I.n)) :=
  vsHGreedy (vsHBT I s.ws' (vsQCs s) (vsPRows I.p Lb) r) ys

/-- The test of the isotropic pass, with `Q = p^(dim L) - 1`. -/
noncomputable def vsHT2 (s : VsQSt I) (Lb : List (List (List ℕ))) (r : ℕ) :
    List (Perm (Fin I.n)) → Perm (Fin I.n) → Bool :=
  vsHIT I s.ws' (vsQCs s) (vsPRows I.p Lb) r (I.p ^ (vsPRows I.p Lb).length - 1)
    (decide (r ∣ I.p ^ (vsPRows I.p Lb).length - 1))

theorem VsHHyp.inY (h : VsHHyp hs as Lb ys r) : ∀ y ∈ ys, VsHIn hs (vsHY hs as ys) y :=
  fun y hy => ⟨h.hys y hy, Subgroup.mem_sup_left
    (vsPRho_mem_vsPBar hs (Subgroup.subset_closure hy) (h.hys y hy))⟩

/-- **The basis.** -/
theorem VsHHyp.bas (h : VsHHyp hs as Lb ys r) :
    (∀ e ∈ vsHB s Lb r ys, e ∈ ys) ∧
    vsHY hs as ys = Subgroup.closure (vsPRho hs '' {e | e ∈ vsHB s Lb r ys}) ⊔ vsHS hs as ∧
    r ^ (vsHB s Lb r ys).length ≤ vsQD s ^ 2 ∧
    ∀ i ≤ ys.length, r ^ (vsHGreedy (vsHBT I s.ws' (vsQCs s) (vsPRows I.p Lb) r)
      (ys.take i)).length ≤ vsQD s ^ 2 := by
  obtain ⟨h1, -, h3, h4⟩ := vsHBas_out hs h.has h.hLb h.hspan h.hys h.hard ys h.inY
  refine ⟨h1, ?_, h4, fun i _ => ?_⟩
  · show vsPBar hs (gens ys) ⊔ vsHS hs as = _
    rw [vsPBar_gens hs h.hys]; exact h3
  · exact (vsHBas_out hs h.has h.hLb h.hspan h.hys h.hard (ys.take i)
      fun y hy => h.inY y (List.mem_of_mem_take hy)).2.2.2

/-- The cover list. -/
noncomputable def vsHE (s : VsQSt I) (Lb : List (List (List ℕ))) (r : ℕ) (ys : List (Perm (Fin I.n))) :
    List (Perm (Fin I.n)) :=
  vsPEnum r (vsHB s Lb r ys)

theorem VsHHyp.inE (h : VsHHyp hs as Lb ys r) :
    ∀ z ∈ vsHE s Lb r ys, VsHIn hs (vsHY hs as ys) z := by
  intro z hz
  have hB := h.bas.1
  have hzB : z ∈ gens (vsHB s Lb r ys) := vsPEnum_mem _ z hz
  have hle : gens (vsHB s Lb r ys) ≤ gens ys :=
    (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure (hB g hg)
  have hys : gens ys ≤ gens s.hs := (Subgroup.closure_le _).2 fun g hg => h.hys g hg
  exact ⟨hys (hle hzB), Subgroup.mem_sup_left (vsPRho_mem_vsPBar hs (hle hzB) (hys (hle hzB)))⟩

/-- **The words cover `Ȳ` modulo `S`.** -/
theorem VsHHyp.cover (h : VsHHyp hs as Lb ys r) :
    ∀ y ∈ vsHY hs as ys, ∃ z ∈ vsHE s Lb r ys, (vsPRho hs z)⁻¹ * y ∈ vsHS hs as := by
  intro y hy
  obtain ⟨hB, hYB, -, -⟩ := h.bas
  have hBs : ∀ g ∈ vsHB s Lb r ys, g ∈ gens s.hs := fun g hg => h.hys g (hB g hg)
  have hQ := vsH_quotHyp h.hard
  set B := vsHB s Lb r ys
  have hN : Subgroup.closure (vsPRho hs '' {e | e ∈ B}) =
      Subgroup.closure {g | g ∈ B.map (vsPRho hs)} := by rw [vsH_image_list]
  have hQB : VsPQuotHyp (Subgroup.closure (vsPRho hs '' {e | e ∈ B})) (vsHS hs as) r :=
    hQ.mono (by
      have : vsHY hs as ys = vsPBar hs (gens ys) ⊔ vsMScal (vsPBar hs (gens as)) := rfl
      rw [← this, hYB]; exact le_sup_left)
  rw [hYB] at hy
  obtain ⟨e, hel, her, he⟩ := vsH_cover_W h.hard.2.2.2.1.pos hQB hN y hy
  rw [List.length_map] at hel
  refine ⟨vsPW B e, vsPEnum_W_mem B e hel her, ?_⟩
  rw [vsPRho_W hs hBs]
  exact he

theorem VsHHyp.E_length (h : VsHHyp hs as Lb ys r) : (vsHE s Lb r ys).length ≤ vsQD s ^ 2 := by
  rw [vsHE, vsPEnum_length]; exact h.bas.2.2.1

/-- The kept family. -/
noncomputable def vsHK (s : VsQSt I) (Lb : List (List (List ℕ))) (r : ℕ) (ys : List (Perm (Fin I.n))) :
    List (Perm (Fin I.n)) :=
  vsHGreedy (vsHT2 s Lb r) (vsHE s Lb r ys)

theorem VsHHyp.test (h : VsHHyp hs as Lb ys r) :
    ∀ kept y, (∀ e ∈ kept, VsHIn hs (vsHY hs as ys) e) → VsHIn hs (vsHY hs as ys) y →
      VsHTest (vsPRho hs) (vsHS hs as) (vsMGood (vsPBar hs (gens as)) r) (vsHT2 s Lb r) kept y := by
  haveI := vsH_nontrivial h.hard
  exact vsHIT_test hs h.has h.hLb h.hspan h.hard.2.1.2.2 h.hard.2.2.1 h.hard.2.2.2.1
    (vsH_quotHyp h.hard)

/-- **The prefixes of the isotropic pass are small.** -/
theorem VsHHyp.iso_bound (h : VsHHyp hs as Lb ys r) (L : List (Perm (Fin I.n)))
    (hL : ∀ y ∈ L, VsHIn hs (vsHY hs as ys) y) :
    r ^ (vsHGreedy (vsHT2 s Lb r) L).length ≤ vsQD s ^ 2 := by
  have hQ := vsH_quotHyp h.hard
  have hr := h.hard.2.2.2.1
  have hinv := vsHGreedy_inv (VsHIn hs (vsHY hs as ys)) h.test [] L (by simpa using hL) []
    ⟨by simp, by simp, by simp, by simp, fun z hz => by simp at hz⟩
  simp only [List.nil_append] at hinv
  set K := vsHGreedy (vsHT2 s Lb r) L
  have hK : L.foldl (fun kept y => if vsHT2 s Lb r kept y then kept ++ [y] else kept) [] = K := rfl
  rw [hK] at hinv
  haveI : Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :=
    Module.finite_of_finite (ZMod I.p)
  have := vsH_pow_le_index hr (S := vsHS hs as) (Y := vsHY hs as ys) (gs := K.map (vsPRho hs))
    (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact (hL e (hinv.sub e he)).2)
    (fun a ha b hb => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
      exact hinv.comm e he e' he')
    (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      obtain ⟨l, hl, hel⟩ := hinv.hgood e he
      rw [hel]; exact pow_mem hl r)
    (fun t ht a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact hQ.sc t ht _ (hL e (hinv.sub e he)).2)
    (fun i hi => by
      rw [List.length_map] at hi
      rw [List.getElem_map, ← List.map_take, ← vsH_image_list]
      exact hinv.indep i hi)
  rw [List.length_map] at this
  exact this.trans (vsH_index_le_D h.hard)

/-- **The isotropic family.** -/
theorem VsHHyp.iso (h : VsHHyp hs as Lb ys r) :
    VsMIso (vsPBar hs (gens as)) (vsHY hs as ys) r
      (fun i : Fin (vsHK s Lb r ys).length => vsPRho hs (vsHK s Lb r ys)[i]) ∧
    ∀ k ∈ vsHK s Lb r ys, k ∈ vsHE s Lb r ys := by
  have hQ := vsH_quotHyp h.hard
  have hA := h.hard.2.1.2.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := vsH_greedy_iso (VsHIn hs (vsHY hs as ys)) h.test
    (Y := (vsHY hs as ys : Set _)) (vsHE s Lb r ys) h.inE (fun y hy => (h.inE y hy).2) h.cover
    (fun y hy t ht hg => vsH_good_mul hA ht (hQ.sc t ht y hy).symm hg)
    (fun t ht y hy => hQ.sc t ht y hy)
  set K := vsHK s Lb r ys
  have hKE : ∀ k ∈ K, k ∈ vsHE s Lb r ys := fun k hk => (vsHGreedy_sublist _ _).subset hk
  refine ⟨⟨fun i => h1 _ (List.getElem_mem i.2), fun i => h2 _ (List.getElem_mem i.2),
    fun i j => h3 _ (List.getElem_mem i.2) _ (List.getElem_mem j.2), fun i => ?_,
    fun y hy hg hc => ?_⟩, hKE⟩
  · have e : (fun i : Fin K.length => vsPRho hs K[i]) '' {j | j < i} =
        vsPRho hs '' {x | x ∈ K.take i} := by
      ext u
      simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_take_iff_getElem]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨K[j], ⟨j, by have := j.2; simp only [lt_min_iff]; exact ⟨hj, this⟩, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨j, hj, rfl⟩, rfl⟩
        rw [lt_min_iff] at hj
        exact ⟨⟨j, hj.2⟩, hj.1, rfl⟩
    rw [e]; exact h4 i i.2
  · have e : Set.range (fun i : Fin K.length => vsPRho hs K[i]) = vsPRho hs '' {x | x ∈ K} := by
      ext u
      simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨K[i], List.getElem_mem i.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [e]
    exact h5 y hy hg fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact hc ⟨i, hi⟩

end GI.Impl
