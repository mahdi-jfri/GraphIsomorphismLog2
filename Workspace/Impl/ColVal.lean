module

public import Workspace.Impl.ColStep
public import Workspace.Impl.GenCls

@[expose] public section

/-!
# Partition values and counts from the class numbering

The column step describes each partition of its child by a key of every position, and each
stored ratio by a count of distinct labels. Both come from the class numbering `cls_spec`
(`Workspace/Impl/GenCls.lean`) on a labeling `lab` and an indicator `dm`:

* `colPartVal`: if the labels of the domain points are above `n` and agree exactly when a
  function `c` of the domain agrees, the first-point labels `Cls.repOf (Cls.keyOf lab dm)` are a
  canonical partition value of `S.domKer c` (labels below `n`);
* `colCount`: with the labels `A + m + 1` on `Fin m`, the list of representatives has as many
  entries as `A` takes values on the support of `dm`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm

variable {Ω C : Type} {n : ℕ}

/-- **A partition value from keys.** -/
theorem colPartVal (e : Ω ≃ Fin n) (S : State Ω C) {X : Type*} (c : S.dom → X)
    (lab : Fin n → ℕ) (hgt : ∀ v : S.dom, n < lab (e v))
    (hlab : ∀ v w : S.dom, lab (e v) = lab (e w) ↔ c v = c w) :
    PartitionValC e (encFun (Cls.repOf (Cls.keyOf lab (indF e S.dom)))) (S.domKer c) := by
  classical
  refine ⟨_, rfl, fun i => Cls.repOf_lt _ i, fun i j => ?_⟩
  rw [Cls.repOf_eq_iff, Col.colDomKer_iff]
  unfold Cls.keyOf indF
  by_cases hi : e.symm i ∈ S.dom <;> by_cases hj : e.symm j ∈ S.dom
  · have := hlab ⟨_, hi⟩ ⟨_, hj⟩
    simp only [Equiv.apply_symm_apply] at this
    simp [hi, hj, this]
  · have := hgt ⟨_, hi⟩
    simp only [Equiv.apply_symm_apply] at this
    simp [hi, hj]
    omega
  · have := hgt ⟨_, hj⟩
    simp only [Equiv.apply_symm_apply] at this
    simp [hi, hj]
    omega
  · simp [hi, hj]

/-- **Counting values with the class numbering.** -/
theorem colCount {m : ℕ} (A : Fin m → ℕ) (dm : Fin m → ℕ) :
    (Cls.repsOf dm (Cls.keyOf (fun c => A c + m + 1) dm)).length =
      (A '' {c | dm c ≠ 0}).ncard := by
  classical
  set K := Cls.keyOf (fun c => A c + m + 1) dm with hK
  have hKon : ∀ c, dm c ≠ 0 → K c = A c + m + 1 := fun c h => by simp [hK, Cls.keyOf, h]
  have hKoff : ∀ c, dm c = 0 → K c = m := fun c h => by simp [hK, Cls.keyOf, h]
  set A' : ℕ → ℕ := fun j => if h : j < m then A ⟨j, h⟩ else 0 with hA'
  have himg : A '' {c | dm c ≠ 0} = A' '' {j | j ∈ Cls.repsOf dm K} := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      set j := Cls.repOf K c
      have hjlt : j < m := Cls.repOf_lt K c
      have hKj : K ⟨j, hjlt⟩ = K c := Cls.key_repOf K c
      have hdj : dm ⟨j, hjlt⟩ ≠ 0 := by
        intro h0
        rw [hKoff _ h0, hKon c hc] at hKj
        omega
      refine ⟨j, (Cls.mem_repsOf dm K).2 ⟨hjlt, hdj, Cls.repOf_idem K c⟩, ?_⟩
      simp only [hA', dif_pos hjlt]
      rw [hKon _ hdj, hKon c hc] at hKj
      omega
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hjlt, hdj, -⟩ := (Cls.mem_repsOf dm K).1 hj
      exact ⟨⟨j, hjlt⟩, hdj, by simp [hA', hjlt]⟩
  have hinj : Set.InjOn A' {j | j ∈ Cls.repsOf dm K} := by
    intro j hj j' hj' h
    obtain ⟨hjlt, hdj, hrj⟩ := (Cls.mem_repsOf dm K).1 hj
    obtain ⟨hjlt', hdj', hrj'⟩ := (Cls.mem_repsOf dm K).1 hj'
    simp only [hA', dif_pos hjlt, dif_pos hjlt'] at h
    have hk : K ⟨j, hjlt⟩ = K ⟨j', hjlt'⟩ := by rw [hKon _ hdj, hKon _ hdj', h]
    rw [← hrj, ← hrj', (Cls.repOf_eq_iff K _ _).2 hk]
  rw [himg, hinj.ncard_image]
  have : {j | j ∈ Cls.repsOf dm K} = ((Cls.repsOf dm K).toFinset : Set ℕ) := by
    ext; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup (Cls.nodup_repsOf dm K)]

end GI.Impl
