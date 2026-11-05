module

public import Workspace.Impl.AggCertHand
public import Workspace.Impl.AggImg
public import Workspace.Impl.AggCertMvInd

@[expose] public section

/-!
# The graph forms of the certificate groups: the mathematics

After the loop of the certificate phase, the program knows, for every test set `T` and both
strings `z`, a graph form of the lift of the final group `A_final(z, T)` and the log of the
increments. The comparison phase and the items need a graph form of the lift of the certificate
group `F_z = ⟨K(T) : T full⟩` (`certGroup`, Section 4.1, "Aggregate the full certificates";
`itCertLift`). This file says how to get it.

* The final window is the union of the increments of the log (`win_succ`), so the points outside
  it are known.
* `K(T) = (A_final)_{(Ω \ W_final)}` is a pointwise stabilizer (`graphOf_lift_fix`); the test
  "`T` is full" is `|φ_T(A_final)| = |Alt(T)|` (`full_iff_card`).
* `F_z` is a join. The lift of a join of subgroups of `G|_dom` is the join of the lifts and of the
  kernel `G_(dom)` of the restriction (`cp_lift_iSup`): the restriction `G → G|_dom` is onto.
  So the first parts of the graph forms of `G_(dom)` and of the lifts of the `K(T)` generate the
  lift of `F_z` on positions (`cp_fz_gens`), and one `clos_spec` call on the graph form of `G`
  gives its graph form (`posPre_eq`, `graphOf_posPre`), with at most `(k + q)²` pairs. Including
  `G_(dom)` also covers the case that no `T` is full (`F_z = 1`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

section Lift

variable {Ω C : Type} (S : State Ω C)

/-- **The lift of a join** of subgroups of `G|_dom` is the join of the lifts and of the kernel of
the restriction. -/
theorem cp_lift_iSup {ι : Sort*} (H : ι → Subgroup (Perm S.dom)) (hH : ∀ i, H i ≤ S.domGroup) :
    S.liftGroup (⨆ i, H i) = S.liftGroup ⊥ ⊔ ⨆ i, S.liftGroup (H i) := by
  apply le_antisymm
  · set M := S.liftGroup ⊥ ⊔ ⨆ i, S.liftGroup (H i) with hM
    set K := M.comap S.G.subtype with hK
    have hker : S.domHom.ker ≤ K := by
      intro g hg
      show (g : Perm Ω) ∈ M
      refine le_sup_left (a := S.liftGroup ⊥) ?_
      exact State.mem_liftGroup.2 ⟨g.2, by simpa using hg⟩
    have hsup : (⨆ i, H i) ≤ K.map S.domHom := by
      refine iSup_le fun i => ?_
      intro y hy
      obtain ⟨g, rfl⟩ := hH i hy
      refine ⟨g, ?_, rfl⟩
      show (g : Perm Ω) ∈ M
      refine le_sup_right (a := S.liftGroup ⊥) ?_
      exact le_iSup (fun i => S.liftGroup (H i)) i (State.mem_liftGroup.2 ⟨g.2, hy⟩)
    have hc : (⨆ i, H i).comap S.domHom ≤ K := by
      calc (⨆ i, H i).comap S.domHom ≤ (K.map S.domHom).comap S.domHom := Subgroup.comap_mono hsup
        _ = K ⊔ S.domHom.ker := Subgroup.comap_map_eq _ _
        _ = K := sup_eq_left.2 hker
    intro g hg
    obtain ⟨hgG, hgH⟩ := State.mem_liftGroup.1 hg
    exact hc (show (⟨g, hgG⟩ : S.G) ∈ (⨆ i, H i).comap S.domHom from hgH)
  · refine sup_le ?_ (iSup_le fun i => ?_)
    · intro g hg
      obtain ⟨hgG, hgH⟩ := State.mem_liftGroup.1 hg
      exact State.mem_liftGroup.2 ⟨hgG, (bot_le : ⊥ ≤ ⨆ i, H i) hgH⟩
    · intro g hg
      obtain ⟨hgG, hgH⟩ := State.mem_liftGroup.1 hg
      exact State.mem_liftGroup.2 ⟨hgG, le_iSup H i hgH⟩

/-- **The lift of a join under a condition**, the form of `certGroup`. -/
theorem cp_lift_iSup₂ {ι : Type*} (p : ι → Prop) (H : ι → Subgroup (Perm S.dom))
    (hH : ∀ i, H i ≤ S.domGroup) :
    S.liftGroup (⨆ i, ⨆ (_ : p i), H i) =
      S.liftGroup ⊥ ⊔ ⨆ i, ⨆ (_ : p i), S.liftGroup (H i) := by
  apply le_antisymm
  · set M := S.liftGroup ⊥ ⊔ ⨆ i, ⨆ (_ : p i), S.liftGroup (H i) with hM
    set K := M.comap S.G.subtype with hK
    have hker : S.domHom.ker ≤ K := by
      intro g hg
      show (g : Perm Ω) ∈ M
      refine le_sup_left (a := S.liftGroup ⊥) ?_
      exact State.mem_liftGroup.2 ⟨g.2, by simpa using hg⟩
    have hsup : (⨆ i, ⨆ (_ : p i), H i) ≤ K.map S.domHom := by
      refine iSup₂_le fun i hi => ?_
      intro y hy
      obtain ⟨g, rfl⟩ := hH i hy
      refine ⟨g, ?_, rfl⟩
      show (g : Perm Ω) ∈ M
      refine le_sup_right (a := S.liftGroup ⊥) ?_
      exact le_iSup₂ (f := fun i (_ : p i) => S.liftGroup (H i)) i hi
        (State.mem_liftGroup.2 ⟨g.2, hy⟩)
    have hc : (⨆ i, ⨆ (_ : p i), H i).comap S.domHom ≤ K := by
      calc (⨆ i, ⨆ (_ : p i), H i).comap S.domHom ≤ (K.map S.domHom).comap S.domHom :=
            Subgroup.comap_mono hsup
        _ = K ⊔ S.domHom.ker := Subgroup.comap_map_eq _ _
        _ = K := sup_eq_left.2 hker
    intro g hg
    obtain ⟨hgG, hgH⟩ := State.mem_liftGroup.1 hg
    exact hc (show (⟨g, hgG⟩ : S.G) ∈ (⨆ i, ⨆ (_ : p i), H i).comap S.domHom from hgH)
  · refine sup_le ?_ (iSup₂_le fun i hi => ?_)
    · intro g hg
      obtain ⟨hgG, hgH⟩ := State.mem_liftGroup.1 hg
      exact State.mem_liftGroup.2 ⟨hgG, (bot_le : ⊥ ≤ ⨆ i, ⨆ (_ : p i), H i) hgH⟩
    · intro g hg
      obtain ⟨hgG, hgH⟩ := State.mem_liftGroup.1 hg
      exact State.mem_liftGroup.2 ⟨hgG, le_iSup₂ (f := fun i (_ : p i) => H i) i hi hgH⟩

end Lift

section Gens

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- The first parts of a graph form of `A` generate `A ∩ G` on positions. -/
theorem cp_gens_fst {A : Subgroup (Perm Ω)} {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L A ps) :
    gens (ps.map Prod.fst) = (A ⊓ S.G).map (toFin e).toMonoidHom := by
  ext a
  rw [mem_gens_fst hps, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, hA, rfl⟩; exact ⟨g, ⟨hA, hg⟩, rfl⟩
  · rintro ⟨g, ⟨hA, hg⟩, rfl⟩; exact ⟨g, hg, hA, rfl⟩

theorem cp_gens_append (ms ns : List (Perm (Fin k))) : gens (ms ++ ns) = gens ms ⊔ gens ns := by
  unfold gens
  rw [← Subgroup.closure_union]
  congr 1
  ext x
  simp

/-- The generators of a flattened list of lists. -/
theorem cp_gens_flatten {ι : Type} (l : List ι) (f : ι → List (Perm (Fin k))) :
    gens (l.map f).flatten = ⨆ i ∈ l, gens (f i) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.flatten_nil, List.not_mem_nil, iSup_of_empty', iSup_bot]
    unfold gens
    simp
  | cons a l ih =>
    rw [List.map_cons, List.flatten_cons, cp_gens_append, ih]
    apply le_antisymm
    · refine sup_le (le_biSup (fun i => gens (f i)) (List.mem_cons_self ..)) ?_
      exact iSup₂_le fun i hi => le_biSup (fun i => gens (f i)) (List.mem_cons_of_mem _ hi)
    · refine iSup₂_le fun i hi => ?_
      rcases List.mem_cons.1 hi with rfl | hi
      · exact le_sup_left
      · exact le_sup_of_le_right (le_biSup (fun i => gens (f i)) hi)

end Gens

section Fz

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **The first parts that generate the lift of `F_z`**: those of a graph form of `G_(dom)`, and,
for each test set `T` of a list of all `κ`-subsets, those of a graph form of the lift of `K(T)`
when `T` is full (none when it is not). -/
theorem cp_fz_gens (z : S.dom → C) (Ts : List (Finset (Fin L.q)))
    (hTs : ∀ T, T ∈ Ts ↔ T.card = P₀.κ) {ks : List (Perm (Fin k))}
    (hks : gens ks = (S.liftGroup ⊥).map (toFin e).toMonoidHom)
    (fs : Finset (Fin L.q) → List (Perm (Fin k)))
    (hfs : ∀ T ∈ Ts, (IsFull (phiT S.domGroup πd T) z →
        gens (fs T) = (S.liftGroup (fullCert (phiT S.domGroup πd T) z)).map
          (toFin e).toMonoidHom) ∧
      (¬ IsFull (phiT S.domGroup πd T) z → fs T = [])) :
    gens (ks ++ (Ts.map fs).flatten) =
      (S.liftGroup (certGroup S πd P₀.κ z)).map (toFin e).toMonoidHom := by
  have hle : ∀ T, fullCert (phiT S.domGroup πd T) z ≤ S.domGroup := fun T _ hg =>
    Pgrp_le ((fullCert_le_automorphisms _ z) hg).1
  have hlift : S.liftGroup (certGroup S πd P₀.κ z) = S.liftGroup ⊥ ⊔
      ⨆ (T : Finset (Fin L.q)) (_ : T.card = P₀.κ ∧ IsFull (phiT S.domGroup πd T) z),
        S.liftGroup (fullCert (phiT S.domGroup πd T) z) :=
    cp_lift_iSup₂ S (fun T : Finset (Fin L.q) => T.card = P₀.κ ∧ IsFull (phiT S.domGroup πd T) z)
      (fun T => fullCert (phiT S.domGroup πd T) z) hle
  rw [cp_gens_append, cp_gens_flatten, hks, hlift, Subgroup.map_sup, Subgroup.map_iSup]
  congr 1
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun T hT => ?_
    by_cases hf : IsFull (phiT S.domGroup πd T) z
    · rw [(hfs T hT).1 hf]
      exact le_iSup₂_of_le (f := fun (T : Finset (Fin L.q))
        (_ : T.card = P₀.κ ∧ IsFull (phiT S.domGroup πd T) z) =>
          (S.liftGroup (fullCert (phiT S.domGroup πd T) z)).map (toFin e).toMonoidHom)
        T ⟨(hTs T).1 hT, hf⟩ le_rfl
    · rw [(hfs T hT).2 hf]
      unfold gens
      simp
  · refine iSup₂_le fun T hT => ?_
    have hm : T ∈ Ts := (hTs T).2 hT.1
    rw [← (hfs T hm).1 hT.2]
    exact le_iSup₂_of_le (f := fun T (_ : T ∈ Ts) => gens (fs T)) T hm le_rfl

/-- **From the generators to the graph form**: the output of `clos_spec` on a graph form of `G`
and first parts generating the lift of `F` on positions is a graph form of the lift of `F`. -/
theorem cp_pairGens_clos {gp : List (Perm (Fin k) × Perm (Fin L.q))} (hgp : PairGens e L S.G gp)
    {H : Subgroup (Perm Ω)} (hH : H ≤ S.G) {ms : List (Perm (Fin k))}
    (hms : gens ms = H.map (toFin e).toMonoidHom) {qs : List (Perm (Fin k) × Perm (Fin L.q))}
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ gp} ⊓ (gens ms).comap (MonoidHom.fst _ _)) :
    PairGens e L H qs := by
  have h1 : PairGens e L (posPre (e := e) (S := S) ms) qs := by
    unfold PairGens
    rw [hqs, hgp, graphOf_posPre]
  rwa [posPre_eq hH hms] at h1

/-- The lift of `G_(dom)`: the first parts of a graph form of the pointwise stabilizer in `G` of
all domain points. -/
theorem cp_gens_ker {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L (S.liftGroup ⊥) ps) :
    gens (ps.map Prod.fst) = (S.liftGroup ⊥).map (toFin e).toMonoidHom := by
  rw [cp_gens_fst hps, inf_eq_left.2 (S.liftGroup_le _)]

end Fz

section Win

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- The window after `t` rounds is the union of the increments of the rounds `j < t`
(`win_succ`). -/
theorem cp_mem_win (T : Finset (Fin L.q)) (z : Ω → C) (v : S.dom) (t : ℕ) :
    v ∈ win (cpPhi S πd T) (dstr S z) t ↔ ∃ j < t, v ∈ inc (cpPhi S πd T) (dstr S z) j := by
  induction t with
  | zero => simp [win_zero]
  | succ t ih =>
    rw [win_succ, Finset.mem_union, ih]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨t, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h

/-- **Removing the increments one by one.** Each step keeps the points whose position is not
in the next list (the test of `cp_bud_filt`). -/
def cpOutF (e : Ω ≃ Fin k) (q : ℕ) (os : List S.dom) (incls : List (List S.dom)) :
    List S.dom :=
  incls.foldl (fun o i => o.filter fun v => decide ((cpPosN e q i).count (domPos e q v : ℕ) = 0))
    os

theorem cp_posN_mem (q : ℕ) (i : List S.dom) (v : S.dom) :
    (domPos e q v : ℕ) ∈ cpPosN e q i ↔ v ∈ i := by
  unfold cpPosN
  constructor
  · intro h
    obtain ⟨u, hu, huv⟩ := List.mem_map.1 h
    rwa [← posOf_injective e q (Fin.ext huv)]
  · intro h
    exact List.mem_map.2 ⟨v, h, rfl⟩

theorem cp_mem_outF (q : ℕ) (incls : List (List S.dom)) (os : List S.dom) (v : S.dom) :
    v ∈ cpOutF e q os incls ↔ v ∈ os ∧ ∀ i ∈ incls, v ∉ i := by
  induction incls generalizing os with
  | nil => simp [cpOutF]
  | cons i is ih =>
    have h1 : cpOutF e q os (i :: is) = cpOutF e q
        (os.filter fun v => decide ((cpPosN e q i).count (domPos e q v : ℕ) = 0)) is := rfl
    rw [h1, ih, List.mem_filter, decide_eq_true_iff, List.count_eq_zero, cp_posN_mem]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- **The points outside the final window**, from the increment lists of a complete log. -/
theorem cp_mem_outF_win {T : Finset (Fin L.q)} {z : Ω → C} {incls : List (List S.dom)}
    (hlen : incls.length = Fintype.card S.dom)
    (hinc : ∀ j (h : j < incls.length), ∀ v, v ∈ incls[j] ↔
      v ∈ inc (cpPhi S πd T) (dstr S z) j)
    {os : List S.dom} (hall : ∀ v, v ∈ os) (v : S.dom) :
    v ∈ cpOutF e L.q os incls ↔ v ∉ win (cpPhi S πd T) (dstr S z) (Fintype.card S.dom) := by
  rw [cp_mem_outF, cp_mem_win]
  constructor
  · rintro ⟨-, h⟩ ⟨j, hj, hv⟩
    have hj' : j < incls.length := by rw [hlen]; exact hj
    exact h _ (List.getElem_mem hj') ((hinc j hj' v).2 hv)
  · intro h
    refine ⟨hall v, fun i hi hv => h ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
    exact ⟨j, by rw [← hlen]; exact hj, (hinc j hj v).1 hv⟩

/-- The increment lists of a log: they exist, one for each round, of length at most `k`. -/
theorem cp_stgs_incls {T : Finset (Fin L.q)} {z : Ω → C} {l : List (CpStgD k L.q)}
    (hl : CpStgs e πd T z l) :
    ∃ incls : List (List S.dom), incls.length = l.length ∧
      (∀ j (h : j < incls.length), ∀ v, v ∈ incls[j] ↔ v ∈ inc (cpPhi S πd T) (dstr S z) j) ∧
      (∀ j (h1 : j < incls.length) (h2 : j < l.length),
        l[j].2 = incls[j].map (domPos e L.q) ∧ incls[j].Nodup) := by
  have key : ∀ j (h : j < l.length), ∃ incl : List S.dom, incl.Nodup ∧
      (∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S z) j) ∧ l[j].2 = incl.map (domPos e L.q) :=
    fun j h => (hl.2 j h).2.2
  choose f hf using key
  refine ⟨List.ofFn fun j : Fin l.length => f j j.2, by simp, fun j h v => ?_, fun j h1 h2 => ?_⟩
  · rw [List.getElem_ofFn]
    exact (hf j _).2.1 v
  · rw [List.getElem_ofFn]
    exact ⟨(hf j h2).2.2, (hf j h2).1⟩

/-- **The test "`T` is full"** as the order of the image of the final group, the number that
`imgCardDet` computes with no fixed points (`fix_empty`). -/
theorem cp_isFull_iff (T : Finset (Fin L.q)) (z : S.dom → C) :
    IsFull (cpPhi S πd T) z ↔
      cardFix (cpPhi S πd T) (finalGrp (cpPhi S πd T) z) ∅ = Nat.card (alternatingGroup T) := by
  unfold IsFull Full
  rw [← full_iff_cardFix, fix_empty]

end Win

end GI.Impl
