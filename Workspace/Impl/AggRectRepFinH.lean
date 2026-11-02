import Workspace.Impl.AggRectRepFin

/-!
# The group of the representation, as the program computes it

* `rcR_stab_keep`: the stabilizer of `x` keeps the set `{d₁, d₂}` of the base tuple (pairs) or
  fixes `a` (single labels, `d₁ = d₂ = a`); this is what `rcR_piN` needs.
* `rcR_H_pair`, `rcR_H_car`: the first parts of the Preimage output generate `H` on positions,
  with the precondition of the Preimage call (`rcR_pre_pair`, `rcR_pre_car`).
* `rcR_hs_final`: the generators on positions with the label parts read from the table are graph
  pairs of `H`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

section Final

variable [Finite Ω] {k : ℕ} (e : Ω ≃ Fin k) (I : AggregationData P₀ S L) {x : Ω}
  (hx : x ∈ S.dom) {W R : Finset (Fin L.q)} (hc : RectConds P₀ S L W R)

include I hx in
/-- **The stabilizer of `x` keeps the labels of the base tuple** (up to a swap). -/
theorem rcR_stab_keep (hlam : (S.N : ℝ) ^ P₀.α < L.q) {d₁ d₂ : Fin L.q}
    (hsm : rcRSmall (rcRStab S L x) = [d₁, d₂] ∨ (d₁ = d₂ ∧ rcRSmall (rcRStab S L x) = [d₁])) :
    ∀ σ ∈ rcRStab S L x, (σ d₁ = d₁ ∧ σ d₂ = d₂) ∨ (σ d₁ = d₂ ∧ σ d₂ = d₁) := by
  have hq8 := rcR_q8 I
  intro σ hσ
  rcases I.kq_cases hlam with hf | hf | hf <;> obtain ⟨f⟩ := hf
  · rw [rcR_stab_one I.πd_spec f hx] at hσ hsm
    rw [rcR_small_one hq8] at hsm
    rcases hsm with h | ⟨rfl, h⟩
    · simp at h
    · simp only [List.cons.injEq, and_true] at h
      subst h
      exact Or.inl ⟨hσ.2, hσ.2⟩
  · rw [rcR_stab_pt I.πd_spec f hx] at hσ hsm
    rw [rcR_small_pt (f.map ⟨x, hx⟩).2 hq8] at hsm
    rcases hsm with h | ⟨-, h⟩
    · rcases rcR_pair_mem h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hσ.2.1, hσ.2.2⟩
      · exact Or.inl ⟨hσ.2.2, hσ.2.1⟩
    · unfold rcRPair at h; split_ifs at h <;> simp at h
  · obtain ⟨⟨⟨a, b⟩, hab⟩, hab'⟩ := GI.Pairs.unorderedOfOrdered_surjective (f.map ⟨x, hx⟩)
    rw [rcR_stab_set I.πd_spec f hx hab hab'.symm] at hσ hsm
    rw [rcR_small_set hab hq8] at hsm
    rcases hsm with h | ⟨-, h⟩
    · rcases rcR_pair_mem h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hσ.2
      · rcases hσ.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h2, h1⟩
        · exact Or.inr ⟨h2, h1⟩
    · unfold rcRPair at h; split_ifs at h <;> simp at h

/-! ### Pairs -/

include hc in
/-- The precondition of the Preimage call in the pair cases. -/
theorem rcR_pre_pair {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {w₀ w₁ : Fin L.q} (hw : w₀ ≠ w₁) :
    ∀ m ∈ rcRGens W R w₀ w₁, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m := by
  intro m hm
  obtain ⟨a, b, rfl⟩ := rcR_mem_gens.1 hm
  exact rcR_gens_in_graph e hps (rcR_gen_mem_alt hw a b)

include hc in
/-- **The first parts of the Preimage output generate `H` (pairs).** -/
theorem rcR_H_pair {d₁ d₂ : Fin L.q} (hsm : rcRSmall (rcRStab S L x) = [d₁, d₂])
    {ps qs : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {w₀ w₁ : Fin L.q} (hw0 : w₀ ∈ W) (hw1 : w₁ ∈ W) (hw : w₀ ≠ w₁)
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ (gens (rcRGens W R w₀ w₁)).comap (MonoidHom.snd _ _)) :
    gens (qs.map Prod.fst) = ((rcRRf e I hx W R hc).H.subgroupOf S.G).map (rcRPos e) := by
  obtain ⟨hH, -, -⟩ := rcR_pair_cells I hx (rcRNat e I) hc hsm
  have hg : PairGens e L (L.lift (permitted W R)) qs :=
    rcR_pairGens_H e hps (rcR_closure_gens hc.2.1 hw0 hw1 hw) hqs
  rw [rcR_fst_graph e hg]
  unfold rcRRf
  rw [hH]

/-! ### Single labels -/

open Classical in
/-- A preimage in `G` of a graph pair. -/
noncomputable def rcRPre (p : Perm (Fin k) × Perm (Fin L.q)) : S.G :=
  if h : ∃ g : S.G, gpair e L g = p then h.choose else 1

theorem rcR_pre_spec {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) :
    ∀ p ∈ ps, gpair e L (rcRPre e p) = p := by
  intro p hp
  have hmem : p ∈ graphOf e L S.G := by rw [← hps]; exact Subgroup.subset_closure hp
  obtain ⟨g, hg, -, h1, h2⟩ := (mem_graphOf e L).1 hmem
  have hex : ∃ g' : S.G, gpair e L g' = p := ⟨⟨g, hg⟩, Prod.ext h1 h2⟩
  unfold rcRPre
  rw [dif_pos hex]
  exact hex.choose_spec

/-- The generators of `P` as elements of `Alt(q)`. -/
noncomputable def rcRGensA (W R : Finset (Fin L.q)) (w₀ w₁ : Fin L.q) (hw : w₀ ≠ w₁) :
    List (alternatingGroup (Fin L.q)) :=
  (rcRGens W R w₀ w₁).attach.map fun σ =>
    ⟨σ.1, by obtain ⟨a, b, h⟩ := rcR_mem_gens.1 σ.2; rw [← h]; exact rcR_gen_mem_alt hw a b⟩

theorem rcR_gensA_closure {w₀ w₁ : Fin L.q} (hd : Disjoint W R) (hw0 : w₀ ∈ W) (hw1 : w₁ ∈ W)
    (hw : w₀ ≠ w₁) :
    Subgroup.closure {a | a ∈ rcRGensA W R w₀ w₁ hw} = permitted W R := by
  apply Subgroup.map_injective (alternatingGroup (Fin L.q)).subtype_injective
  rw [MonoidHom.map_closure, ← rcR_closure_gens hd hw0 hw1 hw]
  unfold rcRK gens
  congr 1
  ext σ
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    exact s.2
  · intro hs
    exact ⟨_, List.mem_map.2 ⟨⟨σ, hs⟩, List.mem_attach _ _, rfl⟩, rfl⟩

variable (hlam : (S.N : ℝ) ^ P₀.α < L.q) (f : KernelQuotient I.πd S.dom (Fin L.q))

/-- The precondition of the Preimage call for single labels. -/
theorem rcR_pre_car {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {w₀ w₁ : Fin L.q} (hw : w₀ ≠ w₁) :
    ∀ m ∈ (rcRGensA W R w₀ w₁ hw).map (rcREmb e I hlam f), ∃ p ∈ Subgroup.closure
      {p | p ∈ ps.map fun p => rcRPhi e I hlam f (rcRPre e p)}, MonoidHom.snd _ _ p = m := by
  intro m hm
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hm
  obtain ⟨g, h1, h2⟩ := rcR_car_lift e I hlam f a
  refine ⟨rcRPhi e I hlam f g, ?_, ?_⟩
  · rw [rcR_closure_phi e hps _ _ (rcR_pre_spec e hps)]
    exact ⟨g, rfl⟩
  · show encPairHom _ L.q _ = encPairHom _ L.q _
    congr 1
    refine Prod.ext ?_ ?_
    · show (rcRRhoN e I hlam f g).1 = ((rcRCarD e I hlam f).d.embedAlt a).1
      rw [h2]
    · show (L.π g).1 = a.1
      rw [h1]

/-- **The first parts of the Preimage output generate `H` (single labels).** -/
theorem rcR_H_car {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {w₀ w₁ : Fin L.q} (hd : Disjoint W R) (hw0 : w₀ ∈ W) (hw1 : w₁ ∈ W) (hw : w₀ ≠ w₁)
    {qs : List (Perm (Fin k) × Perm (Fin ((rcRCarD e I hlam f).m + L.q)))}
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps.map fun p => rcRPhi e I hlam f (rcRPre e p)} ⊓
        (gens ((rcRGensA W R w₀ w₁ hw).map (rcREmb e I hlam f))).comap (MonoidHom.snd _ _)) :
    gens (qs.map Prod.fst) = (((rcRCarD e I hlam f).H W R).subgroupOf S.G).map (rcRPos e) := by
  have h1 : gens (qs.map Prod.fst) = (Subgroup.closure {p | p ∈ qs}).map (MonoidHom.fst _ _) := by
    unfold gens
    rw [MonoidHom.map_closure]
    congr 1
    ext σ
    simp
  have h2 : gens ((rcRGensA W R w₀ w₁ hw).map (rcREmb e I hlam f)) =
      (permitted W R).map (rcREmb e I hlam f) := by
    unfold gens
    rw [← rcR_gensA_closure hd hw0 hw1 hw, MonoidHom.map_closure]
    congr 1
    ext σ
    simp
  rw [h1, hqs, rcR_closure_phi e hps _ _ (rcR_pre_spec e hps), h2, rcR_fst_pre, rcR_car_fst]

/-! ### The graph pairs of `H` -/

omit [Finite Ω] in
open Classical in
/-- The label part of an element of `A` given on positions. -/
noncomputable def rcRPiT (A : Subgroup (Perm Ω)) (h : Perm (Fin k)) : Perm (Fin L.q) :=
  if hh : ∃ g : S.G, g.1 ∈ A ∧ rcRPos e g = h then rcRPi L hh.choose else 1

omit [Finite Ω] in
theorem rcR_piT_pos {A : Subgroup (Perm Ω)} (g : S.G) (hg : g.1 ∈ A) :
    rcRPiT e A (rcRPos e g) = rcRPi L g := by
  classical
  have hex : ∃ g' : S.G, g'.1 ∈ A ∧ rcRPos e g' = rcRPos e g := ⟨g, hg, rfl⟩
  unfold rcRPiT
  rw [dif_pos hex]
  have := hex.choose_spec.2
  have heq : hex.choose = g := Subtype.ext ((toFin e).injective this)
  rw [heq]

include hx in
/-- **The program's graph pairs of `H`.** The generators `hs` of `A` on positions, with the label
parts read from the orbit table, are graph pairs of `A`, and the table gives these label parts. -/
theorem rcR_hs_final {A : Subgroup (Perm Ω)} (hA : A ≤ S.G) {hs : List (Perm (Fin k))}
    (hg : gens hs = (A.subgroupOf S.G).map (rcRPos e)) {d₁ d₂ : Fin L.q} {Lk : List (List ℕ)}
    (hT : RcRTab e x d₁ d₂ Lk) (hq : 8 ≤ L.q)
    (hstab : ∀ σ ∈ rcRStab S L x, (σ d₁ = d₁ ∧ σ d₂ = d₂) ∨ (σ d₁ = d₂ ∧ σ d₂ = d₁)) :
    PairGens e L A (hs.map fun h => (h, rcRPiT e A h)) ∧
      ∀ h ∈ hs, (List.finRange L.q).map (fun j : Fin L.q =>
        rcRPiN Lk k (fun v => (rcRL fun i => (h i : ℕ)).getD v 0) (j : ℕ)) =
        (List.finRange L.q).map fun j => (rcRPiT e A h j : ℕ) := by
  refine ⟨rcR_hs_pairs e hA hg _ fun g hg => rcR_piT_pos e g hg, fun h hh => ?_⟩
  have hmem : h ∈ gens hs := Subgroup.subset_closure hh
  rw [hg] at hmem
  obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.1 hmem
  rw [Subgroup.mem_subgroupOf] at hgA
  apply List.map_congr_left
  intro j _
  rw [rcR_piT_pos e g hgA]
  refine rcR_piN hT hq hstab g (fun v => ?_) j
  rw [rcR_L_getD]
  rfl

/-! ### The orbit table from the tuple orbit -/

omit [Finite Ω] in
theorem rcR_ptsKey_tup (i : Fin k) (c d : Fin L.q) :
    ptsKey (rcRTup i [c, d]) = [(i : ℕ), k + (c : ℕ), k + (d : ℕ)] := by
  simp [ptsKey, rcRTup]

omit [Finite Ω] in
/-- Every element of `G` gives a tuple of the orbit. -/
theorem rcR_tup_mem {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    (d₁ d₂ : Fin L.q) (g : S.G) :
    rcRTup (e ((g : Perm Ω) x)) [rcRPi L g d₁, rcRPi L g d₂] ∈
      actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (ps.map encPair)
        (rcRTup (e x) [d₁, d₂]) := by
  have hp : gpair e L g ∈ Subgroup.closure {p | p ∈ ps} := by
    rw [hps, mem_graphOf]; exact ⟨g.1, g.2, g.2, rfl, rfl⟩
  refine ⟨encPair (gpair e L g), mem_gens_encPair.2 ⟨_, hp, rfl⟩, ?_⟩
  show (rcRTup (e x) [d₁, d₂]).map (encPair (gpair e L g)) = _
  rw [rcR_map_tup]
  congr 1
  · show toFin e g.1 (e x) = _
    rw [toFin_apply]; simp

omit [Finite Ω] in
/-- **The keys of the tuple orbit are an orbit table.** -/
theorem rcR_tab_of {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {d₁ d₂ : Fin L.q} {Lt : List (List (Fin (k + L.q)) × Perm (Fin (k + L.q)))}
    (hL : ∀ y, y ∈ Lt.map Prod.fst ↔ y ∈ actOrbit (fun g (xs : List (Fin (k + L.q))) =>
      xs.map g) (ps.map encPair) (rcRTup (e x) [d₁, d₂])) :
    RcRTab e x d₁ d₂ (Lt.map fun p => ptsKey p.1) := by
  constructor
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    have hpo := (hL p.1).1 (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨g, hg⟩ := rcR_tup_entry e hps hpo
    refine ⟨g, ?_⟩
    rw [hg]
    simp only [List.map_cons, List.map_nil]
    rw [rcR_ptsKey_tup]
    rfl
  · intro g
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 ((hL _).2 (rcR_tup_mem e hps d₁ d₂ g))
    refine List.mem_map.2 ⟨p, hp, ?_⟩
    rw [hpe, rcR_ptsKey_tup]
    rfl

omit [Finite Ω] in
/-- **The tuple orbit has at most `k q²` tuples.** -/
theorem rcR_tup_ncard {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    (d₁ d₂ : Fin L.q) :
    (actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (ps.map encPair)
      (rcRTup (e x) [d₁, d₂])).ncard ≤ k * L.q * L.q := by
  have hsub : actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (ps.map encPair)
      (rcRTup (e x) [d₁, d₂]) ⊆
      (fun t : Fin k × Fin L.q × Fin L.q => rcRTup t.1 [t.2.1, t.2.2]) '' Set.univ := by
    intro y hy
    obtain ⟨g, rfl⟩ := rcR_tup_entry e hps hy
    exact ⟨(e ((g : Perm Ω) x), rcRPi L g d₁, rcRPi L g d₂), trivial, rfl⟩
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_image_le
    (Set.toFinite _)).trans ?_)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_fin, mul_assoc]

/-! ### The base point -/

include I in
/-- The domain is not empty: otherwise `π` would be trivial. -/
theorem rcR_dom_ne : S.dom.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hq8 := rcR_q8 I
  obtain ⟨σ, hσ, h1, -⟩ := rcR_alt_swap (q := L.q) (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩)
    (by simp [Fin.ext_iff]) (by omega)
  obtain ⟨g, hg⟩ := L.π_surj ⟨σ, hσ⟩
  have hsub : Subsingleton S.dom := by rw [hne]; infer_instance
  have h1' : (⟨S.domHom g, g, rfl⟩ : S.domGroup) = 1 := Subtype.ext (Subsingleton.elim _ _)
  have := I.πd_spec g
  rw [h1', map_one, hg] at this
  have h2 : σ (⟨0, by omega⟩ : Fin L.q) = ⟨0, by omega⟩ := by
    have := congrArg (fun t : alternatingGroup (Fin L.q) => (t : Perm (Fin L.q)) ⟨0, by omega⟩) this
    simpa using this.symm
  rw [h1] at h2
  simp [Fin.ext_iff] at h2

include I in
/-- **The base point**: the first position of the domain. -/
theorem rcR_first_dom : ∃ x ∈ S.dom,
    (rcRL (rcRDom e S)).findIdx (fun t => t == 1) = (e x : ℕ) := by
  classical
  obtain ⟨v, hv⟩ := rcR_dom_ne I
  have htest : ∀ i : Fin k, ((rcRL (rcRDom e S)).getD i 0 == 1) = true ↔ e.symm i ∈ S.dom := by
    intro i
    rw [rcR_L_getD, beq_iff_eq]
    unfold rcRDom
    split_ifs with h <;> simp [h]
  have hlt : (rcRL (rcRDom e S)).findIdx (fun t => t == 1) < (rcRL (rcRDom e S)).length := by
    refine List.findIdx_lt_length_of_exists ⟨1, ?_, rfl⟩
    have h := (htest (e v)).2 (by simpa using hv)
    rw [beq_iff_eq] at h
    rw [← h, List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_mem _
  have hlen : (rcRL (rcRDom e S)).length = k := by simp
  set j := (rcRL (rcRDom e S)).findIdx (fun t => t == 1)
  have hjk : j < k := hlen ▸ hlt
  have hp := List.findIdx_getElem (w := hlt)
  refine ⟨e.symm ⟨j, hjk⟩, ?_, by simp⟩
  refine (htest ⟨j, hjk⟩).1 ?_
  rw [List.getD_eq_getElem _ _ hlt]
  exact hp

end Final

end GI.Impl
