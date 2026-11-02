import Workspace.Impl.AggItemCfSpec
import Workspace.Impl.AggItemStepC1

/-!
# Cases 2b and 3: the rounds and the objects of a branch

The program of Cases 2b and 3 fixes, branch by branch, the values of the joint refinement at the
binary orbital colorings (Section A.3, Case 2b: "apply the canonical coherent refinement … to
this binary coloring"). It keeps them in a cache: a list of entries `(c_Y, d, d')`, one for each
orbital coloring `c_Y` of a target structure met so far, with the answer `(d, d')` of the
`KaryRefinement 2` call on `(c_X, c_Y)` (`c_X` the orbital coloring of the source structure). A
key met again is not asked again, so the values form one function.

* `itCfJ`: the joint refinement `J` with the values of the cache set (`stSetJ`, one entry at a
  time). It keeps the `κ`-ary values (`itCfJ_ne`) and has the cache values at their keys
  (`itCfJ_mem`).
* `itCfD K cache E`: the rounds of the base set whose binary values agree with the cache and
  whose item choices lie in `E`. It is not empty (`itCfD_nonempty`).
* `itCf_cols`, `itCf_items`: the colors of the structures of a base round are `K.d`, `K.d'`,
  and in Cases 2b and 3 its item is the configuration item `cfg`.
* `itCf_out_twoB`, `itCf_out_three`: the objects of the branch of `b`, from the cache entry of
  the key `c_Y` (Case 2b) or from the refined tuple colors (Case 3).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-! ### The object of Case 2b depends on the refiner only through one coloring -/

theorem itCf_orbitalOut_congr {q ℓ : ℕ} {R R' : Refiner2 q} {H : Subgroup (Perm (Fin q))}
    {t : Fin ℓ → Fin q} (h : R (orbColOut H t) = R' (orbColOut H t)) :
    orbitalOut R H t = orbitalOut R' H t := by
  unfold orbitalOut orbitalAt orbitalCfg
  unfold orbColOut orbColAt at h
  split_ifs with hd
  · rw [dif_pos hd] at h
    rw [h]
  · rfl

/-- The orbital coloring takes values at most `q + 6`: the colors `0, …, 7`, and the anchor
colors `8 + i` for the positions `i < d - 1 ≤ q - 1` of the anchors. -/
theorem itCf_orbColOut_le {q ℓ : ℕ} (H : Subgroup (Perm (Fin q))) (t : Fin ℓ → Fin q)
    (w : Fin 2 → Fin q) : orbColOut H t w ≤ q + 6 := by
  classical
  have hdq : transDeg H (domSet H) ≤ q := by
    have h1 := (transDeg_spec H (domSet H)).2
    have h2 := Finset.card_le_univ (domSet H)
    rw [Fintype.card_fin] at h2
    omega
  have hq : 0 < q := (w 0).pos
  unfold orbColOut orbColAt
  split_ifs
  · simp only [orbCol]
    split_ifs with ha
    · have h1 := List.idxOf_lt_length_iff.2 ha.2
      have h2 : (ancList t (transDeg H (domSet H))).length ≤ transDeg H (domSet H) - 1 := by
        unfold ancList; exact List.length_take_le _ _
      omega
    all_goals omega
  · simp

/-- For `q ≥ 3`, the orbital coloring takes values at most `q²`. -/
theorem itCf_orbColOut_le_sq {q ℓ : ℕ} (hq : 3 ≤ q) (H : Subgroup (Perm (Fin q)))
    (t : Fin ℓ → Fin q) (w : Fin 2 → Fin q) : orbColOut H t w ≤ q ^ 2 := by
  have h := itCf_orbColOut_le H t w
  have h3 : 3 * q ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hq
  omega

/-! ### The cache -/

/-- A cache entry `(key, d, d')`. -/
abbrev ItCfEnt (q : ℕ) : Type :=
  ((Fin 2 → Fin q) → ℕ) × ((Fin 2 → Fin q) → ℕ) × ((Fin 2 → Fin q) → ℕ)

open Classical in
/-- **The joint refinement with the cache values set**, one entry at a time. -/
noncomputable def itCfJ (J : JointFn) (q : ℕ) (cX : (Fin 2 → Fin q) → ℕ) :
    List (ItCfEnt q) → JointFn
  | [] => J
  | a :: l => if h : JointOK cX a.1 a.2.1 a.2.2 then
      stSetJ (itCfJ J q cX l) q 2 cX a.1 a.2.1 a.2.2 h else itCfJ J q cX l

theorem itCfJ_ne (J : JointFn) (q : ℕ) (cX : (Fin 2 → Fin q) → ℕ) (l : List (ItCfEnt q))
    {k' : ℕ} (hk : k' ≠ 2) (n : ℕ) : itCfJ J q cX l n k' = J n k' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    unfold itCfJ
    split_ifs with h
    · rw [stSetJ_ne _ _ _ _ _ _ _ h hk, ih]
    · exact ih

theorem itCfJ_mem (J : JointFn) (q : ℕ) (cX : (Fin 2 → Fin q) → ℕ) (l : List (ItCfEnt q))
    (hok : ∀ a ∈ l, JointOK cX a.1 a.2.1 a.2.2) (hnd : (l.map Prod.fst).Nodup) :
    ∀ a ∈ l, (itCfJ J q cX l q 2 cX a.1).1 = (a.2.1, a.2.2) := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    intro a ha
    have hb := hok b (by simp)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    unfold itCfJ
    rw [dif_pos hb]
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact stSetJ_same _ _ _ _ _ _ _ hb
    · have hne : ¬ (cX = cX ∧ a.1 = b.1) := fun ⟨_, h⟩ => hnd.1 ⟨a, ha', h⟩
      rw [stSetJ_other _ _ _ _ _ _ _ hb _ _ hne]
      exact ih (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hnd.2 a ha'

/-! ### The data of the context -/

section Ctx

variable {S : State Ω C} {L : SuppliedLabels S}

/-- The group of the source structures. -/
noncomputable def itCfHX (K : ItSCtx k S L) : Subgroup (Perm (Fin L.q)) :=
  gens (K.fx.map Prod.snd)

/-- The group of the target structures. -/
noncomputable def itCfHY (K : ItSCtx k S L) : Subgroup (Perm (Fin L.q)) :=
  gens (K.fy.map Prod.snd)

/-- The source tuple. -/
noncomputable def itCfSrc (K : ItSCtx k S L) : Fin (P₀.κ + 1) → Fin L.q := itSrc K.Ag₀ K.J

/-- The orbital coloring of the source structure. -/
noncomputable def itCfcX (K : ItSCtx k S L) : (Fin 2 → Fin L.q) → ℕ :=
  orbColOut (itCfHX K) (itCfSrc K)

/-- The orbital coloring of the target structure of the branch of `b`. -/
noncomputable def itCfcY (K : ItSCtx k S L) (b : Fin (P₀.κ + 1) → Fin L.q) :
    (Fin 2 → Fin L.q) → ℕ :=
  orbColOut (itCfHY K) b

/-- **A good cache**: keys without repeats, each the orbital coloring of some target structure,
with a joint refinement of `(c_X, key)` with colors below `2 q²`. -/
def ItCfCache (K : ItSCtx k S L) (cache : List (ItCfEnt L.q)) : Prop :=
  (cache.map Prod.fst).Nodup ∧ ∀ a ∈ cache, JointOK (itCfcX K) a.1 a.2.1 a.2.2 ∧
    (∀ x, a.2.1 x < 2 * L.q ^ 2) ∧ (∀ x, a.2.2 x < 2 * L.q ^ 2) ∧ ∃ b, a.1 = itCfcY K b

/-- **The rounds of a cache and a set of item choices**: rounds of the base set whose binary
values at the cache keys are the cache values, and whose first-rectangle choices and rectangle
representations lie in `E`. -/
def itCfD (K : ItSCtx k S L) (cache : List (ItCfEnt L.q))
    (E : Set (ItCfCh S L.toGiantLabels)) : Set (Aggregation P₀ S L.toGiantLabels) :=
  {Ag | Ag ∈ itSBase K ∧ (∀ a ∈ cache, (Ag.hK L.q 2 (itCfcX K) a.1).1 = (a.2.1, a.2.2)) ∧
    (Ag.soj, Ag.rep) ∈ E}

theorem itCfD_sub_base (K : ItSCtx k S L) (cache : List (ItCfEnt L.q))
    (E : Set (ItCfCh S L.toGiantLabels)) : itCfD K cache E ⊆ itSBase K := fun _ h => h.1

theorem itCfD_mono (K : ItSCtx k S L) {cache cache' : List (ItCfEnt L.q)}
    {E E' : Set (ItCfCh S L.toGiantLabels)} (hc : ∀ a ∈ cache, a ∈ cache') (hE : E' ⊆ E) :
    itCfD K cache' E' ⊆ itCfD K cache E :=
  fun _ ⟨h1, h2, h3⟩ => ⟨h1, fun a ha => h2 a (hc a ha), hE h3⟩

variable {e : Ω ≃ Fin k} {c : C → ℕ} {K : ItSCtx k S L}

/-- **The rounds of a good cache and a nonempty choice set exist**: `Ag₀` with the cache values
set in its joint refinement and the choices of `E`. -/
theorem itCfD_nonempty (hK : K.OK e c) {cache : List (ItCfEnt L.q)} (hc : ItCfCache K cache)
    {E : Set (ItCfCh S L.toGiantLabels)} (hE : E.Nonempty) : (itCfD K cache E).Nonempty := by
  obtain ⟨ch, hch⟩ := hE
  have hκ : P₀.κ ≠ 2 := by decide
  have hJ' : itCfJ K.J L.q (itCfcX K) cache L.q P₀.κ = K.J L.q P₀.κ :=
    itCfJ_ne _ _ _ _ hκ _
  refine ⟨_, itSBase_upd hK hJ' (HalvingChoice.default S L.toGiantLabels) ch.1 ch.2,
    fun a ha => ?_, hch⟩
  exact itCfJ_mem K.J L.q (itCfcX K) cache (fun x hx => (hc.2 x hx).1) hc.1 a ha

/-- **A good cache is short**: at most one entry per branch tuple. -/
theorem itCfCache_length {cache : List (ItCfEnt L.q)} (hc : ItCfCache K cache) : cache.length ≤ L.q ^ (P₀.κ + 1) := by
  classical
  have h1 : (cache.map Prod.fst).toFinset ⊆ Finset.univ.image (itCfcY K) := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb⟩ := (hc.2 a ha).2.2.2
    exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, hb.symm⟩
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hc.1, List.length_map] at h2
  have h3 := Finset.card_image_le (s := (Finset.univ : Finset (Fin (P₀.κ + 1) → Fin L.q)))
    (f := itCfcY K)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h3
  omega

/-! ### The structures of a base round -/

/-- **The colors of the structures of a base round** are the refined colors of the context. -/
theorem itCf_cols (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ itSBase K)
    (t : Fin (P₀.κ + 1) → Fin L.q) : (Ag.strX t).col = K.d ∧ (Ag.strY t).col = K.d' := by
  obtain ⟨h, hJ⟩ := hK.hJ
  have hR : Ag ∈ asRounds L := hK.sub (itSBase_sub hAg)
  have hR0 : K.Ag₀ ∈ asRounds L := hK.sub hK.mem
  have hπ : Ag.πd = K.Ag₀.πd := it_πd_eq hR hR0
  have hnum : Ag.num = itNum K.Ag₀ := hAg.2.2.1
  have hhK : Ag.hK L.q P₀.κ = K.J L.q P₀.κ := hAg.2.2.2.1
  have e1 := stSetJ_same K.Ag₀.hK L.q P₀.κ _ _ K.d K.d' h
  rw [← hJ] at e1
  unfold Aggregation.strX Aggregation.strY structX structY canon canon' rcol rcol'
  simp only
  rw [hhK, hnum, hπ]
  exact ⟨congrArg (fun p => p.1) e1, congrArg (fun p => p.2) e1⟩

/-- In Cases 2b and 3 the item of a round of the base set is its configuration item. -/
theorem itCf_items (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels}
    (hAg : Ag ∈ itSBase K) (hc : K.case = .twoB ∨ K.case = .three)
    (b : Fin (P₀.κ + 1) → Fin L.q) :
    Ag.items b = Ag.cfg (Ag.strX Ag.src) (Ag.strY b) := by
  have h := itS_case_eq hK hAg
  unfold Aggregation.items plan
  rcases hc with hc | hc <;> rw [hc] at h <;> rw [h]

/-- **The item script of a base round** in Cases 2b and 3: the configuration item of its
objects, for its own choices. -/
theorem itCf_script (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels}
    (hAg : Ag ∈ itSBase K) (hc : K.case = .twoB ∨ K.case = .three)
    (b : Fin (P₀.κ + 1) → Fin L.q) {oX oY : CfgOut L.q}
    (ho : Ag.out (Ag.strX Ag.src) (Ag.strY b) = (oX, oY)) :
    (Ag.items b).script = itCfSb e oX oY (Ag.soj, Ag.rep) := by
  rw [itCf_items hK hAg hc b]
  unfold Aggregation.cfg
  rw [ho]
  rfl

/-- The source tuple of a base round. -/
theorem itCf_src {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ itSBase K) :
    Ag.src = itCfSrc K := hAg.2.2.2.2

/-- **The objects of Case 2b**: from the binary values `(d, d')` of the round at the key of the
branch. -/
theorem itCf_out_twoB (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels}
    (hAg : Ag ∈ itSBase K) (hc : K.case = .twoB) (b : Fin (P₀.κ + 1) → Fin L.q)
    {d d' : (Fin 2 → Fin L.q) → ℕ}
    (hd : (Ag.hK L.q 2 (itCfcX K) (itCfcY K b)).1 = (d, d')) :
    Ag.out (Ag.strX Ag.src) (Ag.strY b) =
      (orbitalOut (fun _ => d) (itCfHX K) (itCfSrc K),
        orbitalOut (fun _ => d') (itCfHY K) b) := by
  obtain ⟨hX, hY⟩ := itS_grps hK hAg b
  have hcase : aggCase (Ag.strX Ag.src).grp = .twoB := (itS_case_eq hK hAg).trans hc
  unfold AggregationData.out
  rw [outPair_twoB _ _ hcase, hX, hY]
  have htX : (Ag.strX Ag.src).tup = itCfSrc K := itCf_src hAg
  have htY : (Ag.strY b).tup = b := rfl
  rw [htX, htY]
  refine Prod.ext (itCf_orbitalOut_congr ?_) (itCf_orbitalOut_congr ?_)
  · exact congrArg (fun p => p.1) hd
  · exact congrArg (fun p => p.2) hd

/-- **The objects of Case 3**: the objects of the Design Lemma for the refined tuple colors. -/
theorem itCf_out_three (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels}
    (hAg : Ag ∈ itSBase K) (hc : K.case = .three) (b : Fin (P₀.κ + 1) → Fin L.q) :
    Ag.out (Ag.strX Ag.src) (Ag.strY b) = (designOut K.d (itCfSrc K), designOut K.d' b) := by
  have hcase : aggCase (Ag.strX Ag.src).grp = .three := (itS_case_eq hK hAg).trans hc
  unfold AggregationData.out
  rw [outPair_three _ _ hcase, (itCf_cols hK hAg Ag.src).1, (itCf_cols hK hAg b).2]
  have htX : (Ag.strX Ag.src).tup = itCfSrc K := itCf_src hAg
  rw [htX]
  rfl

end Ctx

end GI.Impl
