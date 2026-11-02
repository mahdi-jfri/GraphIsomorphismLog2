import Workspace.Impl.MBlkOuter
import Workspace.Impl.CamCells

/-!
# The whole program

`mblkProgram` has 32 functions and no primitives. On `encGroup gs = encPerms (1 :: gs)` it
computes the list of the points, then runs `n` outer rounds from the partition into points, and
returns `mlab (mblkResult (1 :: gs) 0)` (`mblkEntry_spec`). Its cost is at most
`2000000 * S ^ 8` with `S = (m + 1) (n + 1)`, for `m = gs.length + 1` generators, and `S` is at
most the weight of the input (`mblk_S_le_wt`). `mblk_main_spec` is the statement the bridge
`polyTimeAt_ofVal_of_lang_cells` needs.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

variable {n : ℕ}

/-- The entry: on `encPerms gs = [n, gens]`, compute `mids n`, then run `n` outer rounds with
context `[[mids n, gens], n]`, starting from `mids n`. -/
def mblkEntry (rng oi : ℕ) : Expr :=
  .letE (.call rng (.get (.var 0) (.nat 0)))
    (.call oi (mk3 (mk2 (mk2 (.var 1) (.get (.var 0) (.nat 1))) (.get (.var 0) (.nat 0)))
      (.get (.var 0) (.nat 0)) (.var 1)))

/-- **The functions of the program.** -/
def mblkFuns : List Expr :=
  [mblkEntry 1 4] ++ rangeFuns 1 ++ mblkOuterIterFuns 4 8 ++ mblkOuterFoldFuns 8 12 16 28 ++
    mblkMergeFuns 12 ++ mblkClosFuns 16 20 ++ mblkRoundFuns 20 24 ++ mblkGenFuns 24 12 ++
    mblkTestFuns 28

/-- **The program.** -/
def mblkProgram : Program := ⟨mblkFuns, []⟩

theorem mblkP_entry : mblkProgram.funs[0]? = some (mblkEntry 1 4) := rfl

theorem mblkP_range : mblkProgram.HasAt 1 (rangeFuns 1) := by
  intro j hj
  have : (rangeFuns 1).length = 3 := rfl
  rw [this] at hj
  interval_cases j <;> rfl

theorem mblkP_outerIter : mblkProgram.HasAt 4 (mblkOuterIterFuns 4 8) := by
  intro j hj
  have : (mblkOuterIterFuns 4 8).length = 4 := rfl
  rw [this] at hj
  interval_cases j <;> rfl

theorem mblkP_outerFold : mblkProgram.HasAt 8 (mblkOuterFoldFuns 8 12 16 28) := by
  intro j hj
  have : (mblkOuterFoldFuns 8 12 16 28).length = 4 := rfl
  rw [this] at hj
  interval_cases j <;> rfl

theorem mblkP_outerAt : MOuterAt mblkProgram 12 16 20 24 28 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have : (mblkMergeFuns 12).length = 4 := rfl
    rw [this] at hj
    interval_cases j <;> rfl
  · intro j hj
    have : (mblkClosFuns 16 20).length = 4 := rfl
    rw [this] at hj
    interval_cases j <;> rfl
  · intro j hj
    have : (mblkRoundFuns 20 24).length = 4 := rfl
    rw [this] at hj
    interval_cases j <;> rfl
  · intro j hj
    have : (mblkGenFuns 24 12).length = 4 := rfl
    rw [this] at hj
    interval_cases j <;> rfl
  · intro j hj
    have : (mblkTestFuns 28).length = 4 := rfl
    rw [this] at hj
    interval_cases j <;> rfl

/-- **The program computes `mblkResult`.** -/
theorem mblkEntry_spec (gs : List (Perm (Fin n))) (hn : 0 < n) :
    FunDet mblkProgram 0 (encPerms gs) (mlab (mblkResult gs ⟨0, hn⟩))
      (2000000 * ((gs.length + 1) * (n + 1)) ^ 8) := by
  set P := mblkProgram
  set E := encPerms gs with hE
  have hR : FunDet P 1 (.nat n) (mids n) (8000 * (n + 1) ^ 3) := by
    refine FunAll.mono (range_spec mblkP_range n) fun w c hw => ?_
    obtain ⟨rfl, hc⟩ := hw
    refine ⟨encFun_id.symm, ?_⟩
    · have e : (natList (List.range n)).wt = (mids n).wt := by rw [mids, encFun_id]
      have := wt_mids_le n
      have := wt_nat_le n
      rw [e] at hc
      have h1 : loopModK * (n + 1) * ((Val.nat n).wt + n + (mids n).wt + 1) ≤
          loopModK * (n + 1) * (8 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
      have e : loopModK * (n + 1) * (8 * (n + 1) ^ 2) = 8000 * (n + 1) ^ 3 := by
        simp only [loopModK]; ring
      omega
  have d0 : Det P [E] (.get (.var 0) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.var' (i := 0) rfl) (Det.nat 0) (show [Val.nat n, _][0]? = some _ from rfl)
  have d1 := Det.call d0 hR
  have g1 : Det P [E, mids n] (.get (.var 0) (.nat 1)) (.list (gs.map encPerm)) _ :=
    Det.get' (Det.var' (i := 0) rfl) (Det.nat 1)
      (show [Val.nat n, .list (gs.map encPerm)][1]? = some _ from rfl)
  have g0 : Det P [E, mids n] (.get (.var 0) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.var' (i := 0) rfl) (Det.nat 0) (show [Val.nat n, _][0]? = some _ from rfl)
  have dv1 := Det.var' (P := P) (env := [E, mids n]) (i := 1) rfl
  have d2 := Det.call (Det.mk3 (Det.mk2 (Det.mk2 dv1 g1) g0) g0 dv1)
    (mblkOuterIter_spec mblkP_outerIter mblkP_outerFold mblkP_outerAt gs hn)
  refine FunDet.intro mblkP_entry ((Det.letE d1 d2).mono ?_)
  -- the cost
  have w1 := wt_mids_le n
  have w2 := wt_mlab_le (mblkResult gs ⟨0, hn⟩)
  have w3 := wt_list_encPerms_le gs
  have w4 := wt_list2_le (.nat n) (.list (gs.map encPerm))
  have w5 := wt_list2_le (mids n) (.list (gs.map encPerm))
  have w6 := wt_list2_le (.list [mids n, .list (gs.map encPerm)]) (.nat n)
  have w7 := wt_list3_le (.list [.list [mids n, .list (gs.map encPerm)], .nat n]) (.nat n) (mids n)
  have w8 := wt_nat_le n
  have eE : E.wt = (Val.list [.nat n, .list (gs.map encPerm)]).wt := rfl
  generalize hS : (gs.length + 1) * (n + 1) = S at w3 ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hN3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hNS 3
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
  have hS38 : S ^ 3 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by omega)
  omega

/-! ### The size of the input -/

theorem mblk_encPerm_wt (σ : Perm (Fin n)) : 2 * n + 3 ≤ (encPerm σ).wt := by
  have h1 := (encPerm σ).size_le_wt
  have h2 := cam_encPerm_size σ
  rw [size_eq_length] at h1
  omega

/-- `S` is at most the weight of the input. -/
theorem mblk_S_le_wt (gs : List (Perm (Fin n))) :
    ((gs.length + 1 + 1) * (n + 1)) ≤ (encGroup gs).wt := by
  have h1 : (((1 :: gs).map encPerm).map Val.wt).length • (2 * n + 3) ≤
      (((1 :: gs).map encPerm).map Val.wt).sum :=
    List.card_nsmul_le_sum (((1 :: gs).map encPerm).map Val.wt) _ (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hy
      exact mblk_encPerm_wt g)
  have h2 := sum_wt_lt_wt_list ((1 :: gs).map encPerm)
  have h3 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: gs).map encPerm)]) (by simp)
  simp only [List.length_map, List.length_cons, smul_eq_mul] at h1
  have h4 : (gs.length + 1 + 1) * (n + 1) ≤ (gs.length + 1) * (2 * n + 3) := by nlinarith
  omega

/-! ### The generators with the identity -/

theorem mblk_gens_cons_one (gs : List (Perm (Fin n))) : gens (1 :: gs) = gens gs := by
  unfold gens
  have : {g : Perm (Fin n) | g ∈ 1 :: gs} = insert 1 {g | g ∈ gs} := by
    ext g; simp
  rw [this, Subgroup.closure_insert_one]

/-- **The specification the bridge needs.** -/
theorem mblk_main_spec (I : TransitiveInst) :
    FunAll mblkProgram 0 (encGroup I.gs) (fun v c =>
      LabelsOf (IsMinimalBlocks (gens I.gs)) v ∧ c ≤ 2000000 * ((encGroup I.gs).wt + 1) ^ 8) := by
  have hn : 0 < I.n := by have := I.two_le; omega
  have hS := mblk_S_le_wt I.gs
  refine FunAll.mono (mblkEntry_spec (1 :: I.gs) hn) fun v c hv => ⟨?_, ?_⟩
  · rw [hv.1]
    refine ⟨fun x => (mblkResult (1 :: I.gs) ⟨0, hn⟩ x : ℕ), rfl, fun x => (Fin.isLt _), ?_⟩
    rw [← mblk_gens_cons_one]
    refine mblkResult_spec _ _ ⟨⟨1, by have := I.two_le; omega⟩, fun h => by simp [Fin.ext_iff] at h⟩
      ?_
    rw [mblk_gens_cons_one]
    exact I.transitive
  · refine hv.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    simp only [List.length_cons]
    omega

end GI.Impl
