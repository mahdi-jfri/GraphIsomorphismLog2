module

public import Workspace.Degree.JohnRFinal
public import Workspace.Degree.Interface
public import Workspace.Impl.CamFinal
public import Workspace.Proved.SSGroupOrder

@[expose] public section

/-!
# Recognition of Johnson products

`johnsonRecognition` proves `JohnsonRecognition` of `Degree/Interface.lean`. The program is the
Cameron recognition program of `Impl/CamFinal.lean`, with three changes.

* It starts at the tail (`camTailG_spec`): there is no test of the group order, since the promise
  already gives a Maróti structure.
* The test `m + 2 ≤ (k + 1)²` is off (`camTest false`).
* The Johnson identification is `johnsonIdentificationR`, which needs only `m ≥ 8` and `3k ≤ m`.

The tail reads `m`, `k` and `r` from the group, and these are the numbers of the identification
`e` of the promise. So the answer is `[1, m, k, r, E]` with `RecogRange m k`.
-/

namespace GI.Degree

open GI.Lang GI.Cited GI.Proved GI.Impl Equiv

/-- **Johnson identification for `m ≥ 8` and `3k ≤ m`** as a primitive. -/
noncomputable def johnsonRPrim : Prim := Prim.ofHyp _ _ johnsonIdentificationR

theorem johnsonRPrim_ok :
    JohnPrimOK johnsonRPrim (fun m k => 8 ≤ m ∧ 1 ≤ k ∧ 3 * k ≤ m) := by
  intro n m k gv G hG hQ hJ
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec johnsonIdentificationR
    (⟨n, m, k, gs, hQ.1, hQ.2.1, hQ.2.2, hJ⟩ : JohnsonRInst) (by
      rintro ⟨n', m', k', gs', _, _, _, _⟩ hy
      simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at hy
      obtain ⟨hg, rfl, rfl⟩ := hy
      obtain rfl := encGroup_deg hg
      obtain rfl := encGroup_injective hg
      rfl)

/-- The first function calls the tail, at `2`. -/
def recogEntry : Expr := .call 2 (.var 0)

/-- **The program.** The functions `camFunsG` at base `1` with the test off, and the six
algorithms as primitives `0, …, 5`. -/
noncomputable def recogProgram : Program :=
  ⟨[recogEntry] ++ camFunsG 1 0 1 2 3 4 5 false,
    [groupOrderPrim groupOrder, pointwiseStabPrim pointwiseStab, normalClosurePrim normalClosure,
      derivedSubgroupPrim derivedSubgroup, gmpNormalCentralizerPrim gmpNormalCentralizer,
      johnsonRPrim]⟩

theorem recogProgram_at :
    CamAt recogProgram 1 0 1 2 3 4 5 groupOrder pointwiseStab normalClosure derivedSubgroup
      gmpNormalCentralizer johnsonRPrim false := by
  refine camAt_of ?_ rfl rfl rfl rfl rfl rfl
  have h := Program.hasAt_append [recogEntry] (camFunsG 1 0 1 2 3 4 5 false) []
    [groupOrderPrim groupOrder, pointwiseStabPrim pointwiseStab, normalClosurePrim normalClosure,
      derivedSubgroupPrim derivedSubgroup, gmpNormalCentralizerPrim gmpNormalCentralizer,
      johnsonRPrim]
  simp only [List.append_nil, List.length_singleton] at h
  exact h

/-- The output of the tail, read as the output of the task. The numbers are those of `e`. -/
theorem recog_out {n m k r : ℕ} {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hR : RecogRange m k)
    (hr : 1 ≤ r) {v : Val} (h : CamTailOut false G e v) :
    ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
      RecogRange m k ∧ 1 ≤ r ∧ MarotiStructure G e ∧
        v = .list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e] := by
  rcases h with ⟨h, -⟩ | ⟨-, e', hM', rfl⟩
  · exact absurd h Bool.false_ne_true
  · exact ⟨m, k, r, e', hR, hr, hM', rfl⟩

/-- **Recognition of Johnson products.** -/
theorem johnsonRecognition : JohnsonRecognition := by
  refine polyTimeAt_ofVal_of_lang_cells recogProgram 0
    (camK groupOrder pointwiseStab normalClosure derivedSubgroup gmpNormalCentralizer johnsonRPrim)
    (camD groupOrder pointwiseStab normalClosure derivedSubgroup gmpNormalCentralizer johnsonRPrim)
    1 1 (fun I => cam_encGroup_cells I.gs) fun I => ?_
  obtain ⟨m, k, r, e, hR, hr, hM⟩ := I.promise
  set X := (encGroup I.gs).wt + 1 with hX
  have hX1 : 1 ≤ X := by omega
  refine FunAll.intro (show recogProgram.funs[0]? = some recogEntry from rfl)
    (EvalAll.call_funAll (Det.var' (P := recogProgram) (env := [encGroup I.gs]) (i := 0) rfl)
      fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  have hk : 2 * k < m := by have := hR.three_mul; have := hR.one_le; omega
  refine (camTailG_spec recogProgram_at johnsonRPrim_ok I.gs e hM I.primitive I.le_n
      (by have := hR.eight_le; omega) hR.one_le hk
      (fun _ => ⟨hR.eight_le, hR.one_le, hR.three_mul⟩)
      (fun _ h6 => by have := hR.eight_le; omega)).wt_lt.mono fun w cb hw => ?_
  obtain ⟨⟨hout, hcb⟩, hwl⟩ := hw
  refine ⟨recog_out hR hr hout, ?_⟩
  have hpoly := cam_main_cost_poly groupOrder pointwiseStab normalClosure derivedSubgroup
    gmpNormalCentralizer johnsonRPrim hX1
  have hX4 : X ≤ 10 ^ 10 * X ^ 4 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by norm_num)
      _ ≤ 10 ^ 10 * X ^ 4 := Nat.le_mul_of_pos_left _ (by norm_num)
  rw [← hX] at hcb
  unfold camMainCost at hpoly
  omega

end GI.Degree
