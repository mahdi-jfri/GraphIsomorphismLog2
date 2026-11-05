module

public import Workspace.Impl.AggItemCiSojComp

@[expose] public section

/-!
# The component-partition overcoset item

Case 1's generators and alignment depend on the blocks, rather than on the group
whose orbits supplied them. We use the same generators for component blocks. The
model colors interior blocks by `1` and omitted points by `0`. When interior
blocks have at least two points, their size distinguishes these two colors.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (gens)

variable {Ω C : Type} {P : Params} {S : State Ω C}

/-- Case 1's construction applies to any objects with the same transporters as
its size-colored partitions. This preserves its block swaps and parity correction. -/
theorem itcs_partition_item (L : GiantLabels S) (zX zY : ColPart (Fin L.q))
    {gx gy : List (Perm (Fin L.q))} {labX labY : Fin L.q → ℕ}
    (hlX : ItcLab gx labX) (_hlY : ItcLab gy labY)
    (hT : ∀ σ : Perm (Fin L.q), σ • zX = zY ↔ σ • itpPart labX = itpPart labY)
    (hS : ∀ σ : Perm (Fin L.q), σ • zX = zX ↔ σ • itpPart labX = itpPart labX)
    {a : Fin L.q} (ha : labX a ≠ a) :
    ∃ ovs, (objItem (P := P) zX zY : AuxItem P S L).script = Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L) (itcOs hlX labY ha (evenStab (q := L.q) zX)) ovs ∧
      ∀ o ∈ itcOs hlX labY ha (evenStab (q := L.q) zX),
        gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
  classical
  have hstab : MulAction.stabilizer (Perm (Fin L.q)) zX =
      MulAction.stabilizer (Perm (Fin L.q)) (itpPart labX) := by
    ext σ
    simpa only [MulAction.mem_stabilizer_iff] using hS σ
  have hgens : ∀ o ∈ itcOs hlX labY ha (evenStab (q := L.q) zX),
      gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
    intro o ho
    unfold itcOs at ho
    split_ifs at ho
    · rw [List.mem_singleton] at ho
      subst ho
      rw [itp_evenStab_map, hstab]
      exact itc_gens_even hlX ha
    · simp at ho
  have hal (hc : ∀ s, itpCnt labX s = itpCnt labY s) : itcSig labX labY a • zX = zY :=
    (hT _).2 (itcSig_smul hlX hc a)
  unfold objItem
  split_ifs with hex
  · obtain ⟨σ, hσ⟩ := hex
    have hc : ∀ s, itpCnt labX s = itpCnt labY s :=
      (itp_exists_smul_iff labY).1 ⟨_, (hT _).1 hσ⟩
    refine ⟨_, rfl, ?_, hgens⟩
    simp only [itcOs, if_pos hc]
    exact List.Forall₂.cons (itci_ovAt L ⟨σ, hσ⟩ (hal hc) _) List.Forall₂.nil
  · have hc : ¬ ∀ s, itpCnt labX s = itpCnt labY s := by
      intro hc
      exact hex ⟨⟨itcSig labX labY a, itcSig_sign hlX ha⟩, hal hc⟩
    refine ⟨[], rfl, ?_, hgens⟩
    simp only [itcOs, if_neg hc]
    exact List.Forall₂.nil

/-- The model's imprimitive partition item, with the program's Case 1 generators. -/
theorem itcs_imp_item (L : GiantLabels S) (X Y : PairCfg L.q) (v : ℕ)
    (hX : ∀ a ∈ X.fiber, 2 ≤ (X.comp v a).card)
    (hY : ∀ a ∈ Y.fiber, 2 ≤ (Y.comp v a).card)
    {a : Fin L.q} (ha : itcsLab X v a ≠ a) :
    ∃ ovs, (objItem (P := P) (X.impPart v) (Y.impPart v) : AuxItem P S L).script =
        Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L)
        (itcOsM (itcs_component_labels X v) (itcsLab Y v) ha
          (evenStab (q := L.q) (X.impPart v)) (itcMs (itcsLab X v) a)) ovs ∧
      ∀ o ∈ itcOsM (itcs_component_labels X v) (itcsLab Y v) ha
          (evenStab (q := L.q) (X.impPart v)) (itcMs (itcsLab X v) a),
        gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
  obtain ⟨ovs, h1, h2, h3⟩ := itcs_partition_item (P := P) L (X.impPart v) (Y.impPart v)
    (itcs_component_labels X v) (itcs_component_labels Y v)
    (itcs_imp_iff X Y v hX hY) (itcs_imp_iff X X v hX hX) ha
  refine ⟨ovs, h1, ?_, ?_⟩
  · rw [itcOsM, List.forall₂_map_left_iff]
    exact h2.imp fun _ _ h => h
  · intro o ho
    rw [itcOsM, List.mem_map] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    show gens (itcMs (itcsLab X v) a) = _
    rw [itcMs_gens, ← itcOs_snd ho', h3 o' ho']

end GI.Impl
