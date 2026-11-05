module

public import Workspace.Impl.TermRepsStep

@[expose] public section

/-!
# Coset enumeration for the chief-factor action

The input is `[encGroup vs, us]`, with `us` encoded as a list of
permutations. The closure loop starts from the identity stored in the
group encoding and stops once every listed representative is processed.
The program never needs to know the index in advance.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

/-- One representative per right coset, in the original permutation domain. -/
structure GmpCosetReps {G : Type*} [Group G] (U V : Subgroup G) (rs : List G) : Prop where
  sub : ∀ r ∈ rs, r ∈ U
  distinct : rs.Pairwise (fun a b => a * b⁻¹ ∉ V)
  cover : ∀ u ∈ U, ∃ r ∈ rs, ∃ v ∈ V, u = v * r
  length : rs.length = (V.subgroupOf U).index

/-- Initialize the growing-list loop from the identity in `encGroup vs`. -/
def gmpRepsEntryF (wh : ℕ) : Expr :=
  .call wh (mk3 (.var 0) (.nat 0)
    (mk1 (.get (.get (arg 0) (.nat 1)) (.nat 0))))

def gmpRepsFuns (b jm : ℕ) : List Expr :=
  [gmpRepsEntryF (b + 1), tmRpWhileF (b + 1) (b + 2), tmRpStepF (b + 3)] ++
  foldlFuns (b + 3) (b + 6) ++ [tmRpTestF (b + 7) (b + 11)] ++
  anyFuns (b + 7) (b + 10) ++ [tmRpPredF jm (b + 11) (b + 15)] ++
  composeFuns (b + 11) ++ invFuns (b + 15)

structure GmpRepsAt (P : Program) (hm : Membership) (b jm : ℕ) : Prop where
  entry : P.funs[b]? = some (gmpRepsEntryF (b + 1))
  loop : P.funs[b + 1]? = some (tmRpWhileF (b + 1) (b + 2))
  round : TmRpRoundAt P hm (b + 2) (b + 3) (b + 6) (b + 7) (b + 10) jm (b + 11) (b + 15)

theorem gmpRepsAt_of {P : Program} {hm : Membership} {b jm : ℕ}
    (h : P.HasAt b (gmpRepsFuns b jm))
    (hjm : P.prims[jm]? = some (membershipPrim hm)) : GmpRepsAt P hm b jm := by
  refine ⟨?_, ?_, ?_⟩
  · exact (h.block 0 (gs := [gmpRepsEntryF (b + 1)]) rfl).single
  · exact (h.block 1 (gs := [tmRpWhileF (b + 1) (b + 2)]) rfl).single
  · exact ⟨(h.block 2 (gs := [tmRpStepF (b + 3)]) rfl).single,
      h.block 3 rfl, (h.block 6 (gs := [tmRpTestF (b + 7) (b + 11)]) rfl).single,
      h.block 7 rfl, (h.block 10 (gs := [tmRpPredF jm (b + 11) (b + 15)]) rfl).single,
      hjm, h.block 11 rfl, h.block 15 rfl⟩

/-- A common bound for the loop context and all permutation encodings. -/
def gmpRepsWeight (W : ℕ) : ℕ := 100 * (W + 1) ^ 4

/-- Cost of enumerating `q` cosets, with no promise that `q` is known to the program. -/
noncomputable def gmpRepsCost (hm : Membership) (W q : ℕ) : ℕ :=
  (q + 1) * (tmRpRoundC hm (gmpRepsWeight W) (q + 2) +
    tmRpWK * (gmpRepsWeight W + q + 10 * ((q + 2) * gmpRepsWeight W) + 10)) +
      10000 * ((q + 2) * gmpRepsWeight W)

/-- Executable coset enumeration. All membership tests are supplied by
the proved membership program, and all other functions are explicit language code. -/
theorem gmpReps_spec {P : Program} {hm : Membership} {b jm n : ℕ}
    (h : GmpRepsAt P hm b jm) (vs us : List (Perm (Fin n))) :
    FunAll P b (.list [encGroup vs, .list (us.map encPerm)]) (fun w cost =>
      ∃ rs : List (Perm (Fin n)), w = .list (rs.map encPerm) ∧
        GmpCosetReps (gens us) (gens vs) rs ∧
        cost ≤ gmpRepsCost hm (Val.list [encGroup vs, .list (us.map encPerm)]).wt
          (((gens vs).subgroupOf (gens us)).index)) := by
  let c := Val.list [encGroup vs, .list (us.map encPerm)]
  let W := c.wt
  let Y := gmpRepsWeight W
  let q := ((gens vs).subgroupOf (gens us)).index
  have hgW : (encGroup vs).wt < W := wt_le_wt_list (by simp [c, W])
  have hnW : n + 1 ≤ W := by
    have hsize := S_le_wt_encGroup vs
    have hbase : n + 1 ≤ (vs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hWY : W + 1 ≤ Y := by
    have hp := Nat.le_self_pow (by decide : 4 ≠ 0) (W + 1)
    dsimp [Y, gmpRepsWeight]
    omega
  have hnY : (n + 1) ^ 4 ≤ Y := by
    have hp := Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 4
    dsimp [Y, gmpRepsWeight]
    omega
  have hgs : ∀ g ∈ us, g ∈ gens us := fun g hg => Subgroup.subset_closure hg
  have hloop := tmRpLoop_spec hm h.loop h.round
    (R := gens vs) (H := gens us) (gs := us) ⟨vs, rfl, rfl⟩ hgs hnY (show c.wt ≤ Y by omega)
  have d0 := Det.var' (P := P) (env := [c]) (i := 0) rfl
  have dg := Det.arg' (P := P) (vs := [encGroup vs, .list (us.map encPerm)])
    (rest := []) (j := 0) rfl
  have dl := Det.get' dg (Det.nat 1)
    (show [Val.nat n, Val.list ((1 :: vs).map encPerm)][1]? =
      some (.list ((1 :: vs).map encPerm)) from rfl)
  have di := Det.get' dl (Det.nat 0)
    (show ((1 :: vs).map encPerm)[0]? = some (encPerm (1 : Perm (Fin n))) from rfl)
  have da := Det.mk3 d0 (Det.nat 0) (Det.mk1 di)
  have hwid : (encPerm (1 : Perm (Fin n))).wt < W := by
    have h1 : (encPerm (1 : Perm (Fin n))).wt <
        (Val.list ((1 :: vs).map encPerm)).wt := wt_le_wt_list (by simp)
    have h2 : (Val.list ((1 :: vs).map encPerm)).wt < (encGroup vs).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    omega
  have hwl : (Val.list ((1 :: vs).map encPerm)).wt < W := by
    have h2 : (Val.list ((1 :: vs).map encPerm)).wt < (encGroup vs).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    omega
  have hw1 := wt_list1_le (encPerm (1 : Perm (Fin n)))
  have hwarg := wt_list3_le c (.nat 0) (.list [encPerm (1 : Perm (Fin n))])
  have hwc : (Val.list [encGroup vs, .list (us.map encPerm)]).wt = c.wt := rfl
  have da' := da.mono (c' := 1000 * Y) (by
    have hw0 := wt_nat_le 0
    have hwN := wt_nat_le 1
    dsimp only [W] at hgW hnW hWY hwid hwl
    omega)
  refine FunAll.intro h.entry (EvalAll.call_funAll da' fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine hloop.mono fun w cb hb => ?_
  obtain ⟨rs, rfl, ⟨j, hinv, hj⟩, hcb⟩ := hb
  have hfinal := tmRp_final (H := gens us) (R := gens vs) rfl hinv hj
  have hrs : GmpCosetReps (gens us) (gens vs) rs :=
    ⟨hinv.sub, hinv.distinct, hfinal.1, hfinal.2⟩
  have hwr := tmRp_wt_reps (L := q + 2) hnY rs (by
    have hlen : rs.length = q := hfinal.2
    omega)
  refine ⟨rs, rfl, hrs, ?_⟩
  change ca + cb + (Val.list (rs.map encPerm)).wt + 1 ≤ _
  change cb ≤ (q + 1) * (tmRpRoundC hm Y (q + 2) +
    tmRpWK * (Y + q + 10 * ((q + 2) * Y) + 10)) at hcb
  change (Val.list (rs.map encPerm)).wt ≤ 10 * ((q + 2) * Y) at hwr
  have hY1 : 1 ≤ Y := by omega
  have hYq : Y ≤ (q + 2) * Y := Nat.le_mul_of_pos_left _ (by omega)
  change ca + cb + (Val.list (rs.map encPerm)).wt + 1 ≤
    (q + 1) * (tmRpRoundC hm Y (q + 2) +
      tmRpWK * (Y + q + 10 * ((q + 2) * Y) + 10)) + 10000 * ((q + 2) * Y)
  omega

end GI.Impl
