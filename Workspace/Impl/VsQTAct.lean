module

public import Workspace.Proved.VsQTMath
public import Workspace.Proved.VsQLoc
public import Workspace.Impl.VsQSot
public import Workspace.Impl.VsQChunk

@[expose] public section

/-!
# The action of `H` on tuples of local subspaces

Points are lists of subspaces of `𝔽_p^D`; `h ∈ H` maps each by `Λ(h)`. The key of a subspace is
the canonical key `vsWKey` of a spanning list (all of its vectors), flattened; the key of a
tuple is the concatenation. The small orbit transporter (`vsQSot_spec`) on such a tuple gives
the stabilizer of every subspace of the tuple.

* `vsQTAct`, `vsQTAct_act` (an action of `gens hs`), `vsQTKey`, `vsQTKey_injective`.
* `vsQTStab_iff`: `h` fixes the tuple iff it maps each subspace onto itself.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- A tuple of local subspaces. -/
abbrev VsQTup (s : VsQSt I) : Type := List (Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p))

instance (s : VsQSt I) : Countable (Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  exact SetLike.coe_injective.countable

/-- The action on tuples. -/
noncomputable def vsQTAct (s : VsQSt I) (h : Perm (Fin I.n)) (ys : VsQTup s) : VsQTup s :=
  ys.map fun U => U.map (Matrix.toLin' (vsQLam s h))

theorem vsQTAct_act {s : VsQSt I} (hs : VsQStOK s) : VsQPAct (gens s.hs) (vsQTAct s) where
  one ys := by
    unfold vsQTAct
    rw [vsQLam_one hs]
    conv_rhs => rw [← List.map_id ys]
    refine List.map_congr_left fun U _ => ?_
    simp
  mul g hg h hh ys := by
    unfold vsQTAct
    rw [List.map_map]
    refine List.map_congr_left fun U _ => ?_
    simp only [Function.comp_apply, vsQLam_mul hs hg hh, Matrix.toLin'_mul, Submodule.map_comp]

open Classical in
/-- The vectors of a subspace, as a list. -/
noncomputable def vsQTBas {s : VsQSt I} (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) : List (List ℕ) :=
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  (Finset.univ.filter (· ∈ U)).toList.map vsQVec

open Classical in
theorem vsQTBas_fit {s : VsQSt I} (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    VsWFit I.p (vsQD s) (vsQTBas U) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  intro u hu
  simp only [vsQTBas, List.mem_map] at hu
  obtain ⟨v, -, rfl⟩ := hu
  exact ⟨vsQVec_lt v, vsQVec_length v⟩

open Classical in
theorem vsQTBas_span {s : VsQSt I} (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    vsWSp I.p (vsQD s) (vsQTBas U) = U := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    simp only [vsQTBas, List.mem_map, Finset.mem_toList, Finset.mem_filter] at hu
    obtain ⟨v, ⟨-, hv⟩, rfl⟩ := hu
    rw [vsWV_vsQVec]; exact hv
  · intro v hv
    apply Submodule.subset_span
    refine ⟨vsQVec v, ?_, vsWV_vsQVec v⟩
    simp only [vsQTBas, List.mem_map, Finset.mem_toList, Finset.mem_filter]
    exact ⟨v, ⟨Finset.mem_univ _, hv⟩, rfl⟩

/-- The key of a subspace: `D` vectors of length `D`. -/
noncomputable def vsQTKeyU {s : VsQSt I} (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    List (List ℕ) :=
  vsWKey I.p (vsQD s) (vsQTBas U)

/-- The key of a subspace with a marker: `1` and then `D²` numbers. -/
noncomputable def vsQTKeyM {s : VsQSt I} (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) : List ℕ :=
  1 :: (vsQTKeyU U).flatten

/-- The key of a tuple. -/
noncomputable def vsQTKey {s : VsQSt I} (ys : VsQTup s) : List ℕ :=
  ys.flatMap vsQTKeyM

theorem vsQTKeyU_len {s : VsQSt I} (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    (vsQTKeyU U).flatten.length = vsQD s * vsQD s := by
  have hf : VsWFit I.p (vsQD s) (vsQTKeyU U) := vsWKey_fit I.prime.one_lt (vsQTBas U)
  rw [List.length_flatten, List.map_congr_left (g := fun _ => vsQD s) fun r hr => (hf r hr).2]
  simp [vsQTKeyU, vsWKey_length]

theorem vsQTKeyM_len {s : VsQSt I} (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    (vsQTKeyM U).length = vsQD s * vsQD s + 1 := by
  rw [vsQTKeyM, List.length_cons, vsQTKeyU_len]

theorem vsQTKeyM_injective {s : VsQSt I} :
    Function.Injective (vsQTKeyM (s := s)) := by
  intro U V he
  have he' : (vsQTKeyU U).flatten = (vsQTKeyU V).flatten := List.cons.inj he |>.2
  have hfU := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas U)
  have hfV := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas V)
  have e1 : vsQTKeyU U = vsQTKeyU V := by
    have hU := vsQChunk_flatten (0 : ℕ) (vsQD s) (vsQTKeyU U) fun r hr => (hfU r hr).2
    have hV := vsQChunk_flatten (0 : ℕ) (vsQD s) (vsQTKeyU V) fun r hr => (hfV r hr).2
    have lU : (vsQTKeyU U).length = vsQD s := vsWKey_length _ _
    have lV : (vsQTKeyU V).length = vsQD s := vsWKey_length _ _
    rw [lU] at hU; rw [lV] at hV
    rw [← hU, ← hV, he']
  have := (vsWKey_eq_iff I.prime (vsQTBas_fit U) (vsQTBas_fit V)).1 e1
  rwa [vsQTBas_span, vsQTBas_span] at this

/-- Cutting the key of a tuple gives the keys of the subspaces. -/
theorem vsQTKey_chunk {s : VsQSt I} (ys : VsQTup s) :
    vsQChunk 0 (vsQD s * vsQD s + 1) ys.length (vsQTKey ys) = ys.map vsQTKeyM := by
  have := vsQChunk_flatten (0 : ℕ) (vsQD s * vsQD s + 1) (ys.map vsQTKeyM) (by
    intro x hx; obtain ⟨U, -, rfl⟩ := List.mem_map.mp hx; exact vsQTKeyM_len U)
  rw [List.length_map] at this
  rw [vsQTKey]
  exact this

theorem vsQTKey_length {s : VsQSt I} (ys : VsQTup s) :
    (vsQTKey ys).length = ys.length * (vsQD s * vsQD s + 1) := by
  rw [vsQTKey, List.length_flatMap, List.map_congr_left (g := fun _ => vsQD s * vsQD s + 1)
    fun U _ => vsQTKeyM_len U]
  simp

theorem vsQTKey_injective {s : VsQSt I} : Function.Injective (vsQTKey (s := s)) := by
  intro xs ys he
  have hl : xs.length = ys.length := by
    have := congrArg List.length he
    rw [vsQTKey_length, vsQTKey_length] at this
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have h1 := vsQTKey_chunk xs
  rw [hl, he, vsQTKey_chunk ys] at h1
  exact (List.map_injective_iff.2 vsQTKeyM_injective) h1.symm

/-- **The stabilizer of a tuple** fixes each of its subspaces. -/
theorem vsQT_map_eq_self {α : Type*} (f : α → α) : ∀ l : List α, l.map f = l ↔ ∀ x ∈ l, f x = x
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.cons.injEq, vsQT_map_eq_self f l]
    simp

theorem vsQTStab_iff {s : VsQSt I} (h : Perm (Fin I.n)) (ys : VsQTup s) :
    vsQTAct s h ys = ys ↔ ∀ U ∈ ys, U.map (Matrix.toLin' (vsQLam s h)) = U := by
  unfold vsQTAct
  exact vsQT_map_eq_self _ ys

end GI.Impl
