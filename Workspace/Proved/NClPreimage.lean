module

public import Workspace.Impl.NClPreEntry
public import Workspace.Proved.NClNormal
public import Workspace.Proved.SSPointwiseStab

@[expose] public section

/-!
# The preimage from the pointwise stabilizer

`preimage_of`: the pointwise stabilizer algorithm gives a polynomial-time algorithm for
`PreimageTask`. The program is `preFuns 0 0` with the pointwise stabilizer algorithm as
primitive `0` (`Workspace/Impl/NClPreProg.lean`). Write `D'` for the group of the instance on
`n + n'` points and `Δ` for its last `n'` points. The program
* computes the kernel `D'_(Δ)` with one pointwise stabilizer call;
* finds, for each `m ∈ 1 :: ms`, some `x ∈ D'` that acts as `m` on `Δ`, by constructive
  membership: it sifts through the chain of pointwise stabilizers of the first points of `Δ`,
  with a Schreier transversal at each level ([LM, Theorem 3.1(v)]; Seress, *Permutation Group
  Algorithms*, Section 4.1);
* restricts `1`, these lifts and the kernel generators to the first `n` points;
* returns at most `n²` generators of their group, with one pointwise stabilizer call at no points.
This is the method of [LM, Theorem 3.1(vi)(b), p. 67]: lift the generators of `M` and add the
kernel. The restrictions generate the preimage by `nclPreimage_gens`
(`Workspace/Impl/NClPreMath.lean`).
The specification is `preEntry_spec` (`Workspace/Impl/NClPreEntry.lean`).

`GI.Proved.preimage` applies `preimage_of` to the pointwise stabilizer algorithm.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv

/-- The cells of a list are at most its size plus one, if this holds for the cells of its
entries. -/
theorem nclPre_list_cells {vs : List Val}
    (h : ∀ v ∈ vs, ∀ a ∈ v.cells, a ≤ (Val.list vs).size + 1) :
    ∀ a ∈ (Val.list vs).cells, a ≤ (Val.list vs).size + 1 := by
  intro a ha
  have hsz : (Val.list vs).size = 3 + (Val.cellsList vs).length := by
    simp [size_eq_length]; omega
  have hlen : vs.length ≤ (Val.cellsList vs).length := by
    rw [length_cellsList]
    calc vs.length = (vs.map fun _ => 1).sum := by simp
      _ ≤ (vs.map Val.size).sum := List.sum_le_sum fun v _ => by
          have := v.two_le_size; omega
  simp only [cells_list, List.cons_append, List.nil_append, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
  exact h v hv a ha

theorem nclSize_le_list {vs : List Val} {v : Val} (hv : v ∈ vs) : v.size ≤ (Val.list vs).size := by
  have hsz : (Val.list vs).size = 3 + (Val.cellsList vs).length := by
    simp [size_eq_length]; omega
  rw [hsz, length_cellsList]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Val.size) hv)
  omega

theorem nclPre_cells (I : PreimageInst) :
    ∀ a ∈ (preimageEnc I).cells, a ≤ 1 * ((preimageEnc I).size + 1) ^ 1 := by
  rw [one_mul, pow_one]
  have eE : preimageEnc I = .list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms] := rfl
  rw [eE]
  refine nclPre_list_cells fun v hv a ha => ?_
  have hD := nclSize_le_list (show encGroup (nclPreDs I) ∈
    [Val.nat I.n, encGroup (nclPreDs I), encGroup I.ms] by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · -- the number `n` is at most `n + n'`, a cell of the second entry
    have hN : I.n + I.n' ∈ (encGroup (nclPreDs I)).cells := by
      simp [encGroup, encPerms, cells_list]
    have := ncl_encGroup_cells' (nclPreDs I) _ hN
    simp only [cells_nat, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  · have := ncl_encGroup_cells' (nclPreDs I) a ha; omega
  · have := ncl_encGroup_cells' I.ms a ha
    have := nclSize_le_list (show encGroup I.ms ∈
      [Val.nat I.n, encGroup (nclPreDs I), encGroup I.ms] by simp)
    omega

/-- The constant of the cost. -/
noncomputable def preK (h : PointwiseStab) : ℕ :=
  10 ^ 17 + (pointwiseStabPrim h).c * 21 ^ (pointwiseStabPrim h).k + 2 * 10 ^ 6 +
    2 * ((pointwiseStabPrim h).c * 200 ^ (pointwiseStabPrim h).k) + 10 ^ 12

/-- The degree of the cost. -/
noncomputable def preD (h : PointwiseStab) : ℕ := 4 * (pointwiseStabPrim h).k + 14

theorem pre_cost_poly (h : PointwiseStab) {Y : ℕ} (hY : 1 ≤ Y) :
    nclPreCost h Y ≤ preK h * Y ^ preD h := by
  set c := (pointwiseStabPrim h).c
  set k := (pointwiseStabPrim h).k
  have e : nclPreCost h Y = 10 ^ 17 * Y ^ 14 + c * 21 ^ k * Y ^ (2 * k + 2) + 2 * 10 ^ 6 * Y ^ 4 +
      2 * (c * 200 ^ k * Y ^ (4 * k)) + 10 ^ 12 * Y ^ 8 := by
    unfold nclPreCost nclLiftCost nclSiftCost
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  have h1 : Y ^ 14 ≤ Y ^ preD h := Nat.pow_le_pow_right hY (by unfold preD; omega)
  have h2 : Y ^ (2 * k + 2) ≤ Y ^ preD h := Nat.pow_le_pow_right hY (by unfold preD; omega)
  have h3 : Y ^ 4 ≤ Y ^ preD h := Nat.pow_le_pow_right hY (by unfold preD; omega)
  have h4 : Y ^ (4 * k) ≤ Y ^ preD h := Nat.pow_le_pow_right hY (by unfold preD; omega)
  have h5 : Y ^ 8 ≤ Y ^ preD h := Nat.pow_le_pow_right hY (by unfold preD; omega)
  have m2 := Nat.mul_le_mul_left (c * 21 ^ k) h2
  have m4 := Nat.mul_le_mul_left (c * 200 ^ k) h4
  have e2 : preK h * Y ^ preD h = 10 ^ 17 * Y ^ preD h + c * 21 ^ k * Y ^ preD h +
      2 * 10 ^ 6 * Y ^ preD h + 2 * (c * 200 ^ k * Y ^ preD h) + 10 ^ 12 * Y ^ preD h := by
    unfold preK; ring
  rw [e, e2]
  omega

/-- **The program.** -/
noncomputable def preProgram (h : PointwiseStab) : Program := ⟨preFuns 0 0, [pointwiseStabPrim h]⟩

theorem preProgram_at (h : PointwiseStab) : PreAt (preProgram h) 0 0 h := by
  refine preAt_of ?_ rfl
  have hA := Program.hasAt_append [] (preFuns 0 0) [] [pointwiseStabPrim h]
  simpa [preProgram] using hA

/-- **The preimage from the pointwise stabilizer.** -/
theorem preimage_of (h : PointwiseStab) : Preimage := by
  refine polyTimeAt_ofVal_of_lang_cells (preProgram h) 0 (preK h) (preD h) 1 1
    (fun I => nclPre_cells I) fun I => ?_
  refine FunAll.mono (preEntry_spec (preProgram_at h) I) fun v c hv => ⟨?_, ?_⟩
  · obtain ⟨hs, rfl, hl, he⟩ := hv.1
    exact ⟨hs, rfl, hl, by rw [he]; rfl⟩
  · exact hv.2.trans (pre_cost_poly h (by omega))

end GI.Impl

namespace GI.Proved

/-- **Preimage** (`GI.Cited.Preimage`), proved from the pointwise stabilizer algorithm. This is
the one place where the pointwise stabilizer algorithm is supplied to it. -/
theorem preimage : GI.Cited.Preimage := GI.Impl.preimage_of GI.Proved.pointwiseStab

end GI.Proved
