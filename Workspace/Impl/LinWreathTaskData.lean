module

public import Workspace.Impl.LinWreathMatrices
public import Workspace.Impl.LinWreathBlockGenerator
public import Workspace.Impl.LinWreathVector

@[expose] public section

/-! The table constructors produce the encoding of the actual two-copy vector
instance, including its representation on the original permutation cover. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

private theorem linWreathAttachMap {G α : Type*} [Group G] (K : Subgroup G)
    (xs : List G) (hx : ∀ x ∈ xs, x ∈ K) (F : K → α) :
    xs.attach.map (fun x => F ⟨x.val, hx x.val x.property⟩) =
      xs.map (fun x => F (linIntoSubgroup K x)) := by
  calc _ = xs.attach.map (fun x => F (linIntoSubgroup K x.val)) := by
          apply List.map_congr_left
          intro x _
          apply congrArg F
          apply Subtype.ext
          exact (linIntoSubgroup_val K x.val (hx x.val x.property)).symm
    _ = _ := List.attach_map_val (l := xs) (f := fun x : G => F (linIntoSubgroup K x))

noncomputable def linWreathOldMatrices (I : VecStabInst) :
    List (Matrix (Fin I.d) (Fin I.d) (ZMod I.p)) :=
  (linWreathSubgens I.gs).map fun g => (I.φ g).val

theorem linWreathOldMatrices_attach (I : VecStabInst) :
    I.gs.attach.map (fun g => (I.φ ⟨g.val, Subgroup.subset_closure g.property⟩).val) =
      linWreathOldMatrices I := by
  simpa only [linWreathOldMatrices, linWreathSubgens, List.map_map, Function.comp_def] using
    linWreathAttachMap (gens I.gs) I.gs (fun g hg => Subgroup.subset_closure hg)
      (fun g => (I.φ g).val)

private theorem linWreathIntoCover (I : VecStabInst) [Nonempty (Fin I.n)]
    (a : gens I.gs ≀ᵣ linTwo) :
    linIntoSubgroup (gens (linWreathCoverGenerators I.gs))
      (linWreathFinCover (n := I.n) (gens I.gs) a) = linWreathCoverEquiv I.gs a := by
  apply Subtype.ext
  exact linIntoSubgroup_val _ _ (linWreathCoverEquiv I.gs a).property

private theorem linWreathVecInst_cover_matrix (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (a : gens I.gs ≀ᵣ linTwo) :
    (linWreathVecInst I w).φ (linWreathCoverEquiv I.gs a) = linWreathMatrixRep I.φ a := by
  change linWreathMatrixRep I.φ ((linWreathCoverEquiv I.gs).symm
    (linWreathCoverEquiv I.gs a)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The list of block matrices is exactly the representation data read by
VectorStabilizer, in the order of the generated permutation list. -/
theorem linWreathVecInst_matrices (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (hd : 0 < I.d) :
    .list ((linWreathCoverGenerators I.gs).attach.map fun g =>
      encModMatrix ((linWreathVecInst I w).φ
        ⟨g.val, Subgroup.subset_closure g.property⟩).val) =
      linWreathMatrices hd (linWreathOldMatrices I) := by
  have he : (linWreathCoverGenerators I.gs).attach.map (fun g =>
      encModMatrix ((linWreathVecInst I w).φ
        ⟨g.val, Subgroup.subset_closure g.property⟩).val) =
      (linWreathCoverGenerators I.gs).map (fun g => encModMatrix
        ((linWreathVecInst I w).φ
          (linIntoSubgroup (gens (linWreathCoverGenerators I.gs)) g)).val) := by
    exact linWreathAttachMap (gens (linWreathCoverGenerators I.gs))
      (linWreathCoverGenerators I.gs) (fun g hg => Subgroup.subset_closure hg)
      (fun g => encModMatrix ((linWreathVecInst I w).φ g).val)
  rw [he]
  change Val.list (((linWreathGenerators (linWreathSubgens I.gs)).map
    (linWreathFinCover (n := I.n) (gens I.gs))).map _) = _
  simp only [List.map_map, Function.comp_def, linWreathIntoCover, linWreathVecInst_cover_matrix]
  have hf (g : gens I.gs) :
      (linWreathMatrixRep I.φ (linWreathSingle 1 g)).val =
        linWreathBlock hd (I.φ g).val 0 := by
    exact (linWreathBlock_generator hd I.φ g (0 : Fin 3)).symm
  have hs (g : gens I.gs) :
      (linWreathMatrixRep I.φ (linWreathSingle linTwoSwap g)).val =
        linWreathBlock hd (I.φ g).val 1 := by
    simpa [Matrix, linWreathGeneratorElement] using (linWreathBlock_generator hd I.φ g (1 : Fin 3)).symm
  have hw : (linWreathMatrixRep I.φ linWreathSwap).val =
      linWreathBlock hd (0 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)) 2 := by
    have hh := (linWreathBlock_generator hd I.φ (1 : gens I.gs) (2 : Fin 3)).symm
    have he : linWreathBlock hd (I.φ (1 : gens I.gs)).val 2 =
        linWreathBlock hd (0 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)) 2 := by
      funext i j
      simp only [linWreathBlock, show ¬ (2 < 2) by decide, if_false]
    change (linWreathMatrixRep I.φ linWreathSwap).val =
      linWreathBlock hd (I.φ (1 : gens I.gs)).val 2 at hh
    exact hh.trans he
  simp only [linWreathGenerators, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def, hf, hs, hw, linWreathMatrices, linWreathOldMatrices]
  rfl

/-- The pair vector is the concatenation of the two explicit coordinate lists. -/
theorem linWreathVecInst_vector (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) :
    encVec (linWreathVecInst I w).v =
      .list (((List.finRange I.d).map fun i => Val.nat (I.v i).val) ++
        ((List.finRange I.d).map fun i => Val.nat (w i).val)) := by
  change encVec (linWreathNumberLinear (R := ZMod I.p) (linWreathPair I.v w)) = _
  apply congrArg Val.list
  have hcast (i : Fin I.d) : Fin.castLE (Nat.le_add_right I.d I.d) i = i.castAdd I.d := rfl
  simp only [← List.ofFn_eq_map, List.ofFn_add, hcast, ← linWreathNumber_one,
    ← linWreathNumber_swap, linWreathNumberLinear_apply, linWreathPair_one,
    linWreathPair_swap]

theorem linWreathOldMatrices_value (I : VecStabInst) :
    Val.list (I.gs.attach.map (fun g =>
      encModMatrix (I.φ ⟨g.val, Subgroup.subset_closure g.property⟩).val)) =
      .list ((linWreathOldMatrices I).map encModMatrix) := by
  rw [← linWreathOldMatrices_attach]
  simp only [List.map_map, Function.comp_def]

theorem linWreathVecInst_encoding (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (hd : 0 < I.d) :
    vecStabEnc (linWreathVecInst I w) =
      .list [encGroup (linWreathCoverGenerators I.gs), .nat I.p,
        linWreathMatrices hd (linWreathOldMatrices I),
        .list (((List.finRange I.d).map fun i => Val.nat (I.v i).val) ++
          ((List.finRange I.d).map fun i => Val.nat (w i).val))] := by
  change Val.list [encGroup (linWreathCoverGenerators I.gs), .nat I.p,
    .list ((linWreathCoverGenerators I.gs).attach.map fun g =>
      encModMatrix ((linWreathVecInst I w).φ
        ⟨g.val, Subgroup.subset_closure g.property⟩).val), encVec (linWreathVecInst I w).v] = _
  rw [linWreathVecInst_matrices I w hd, linWreathVecInst_vector]

end GI.Impl
