module

public import Workspace.Impl.GMPRepsCost

@[expose] public section

/-! # Computing the label of a coset by membership tests -/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

variable {n : ℕ}

/-- The first representative in the same right coset as `y`. -/
noncomputable def gmpCosetIndex (V : Subgroup (Perm (Fin n)))
    (rs : List (Perm (Fin n))) (y : Perm (Fin n)) : ℕ :=
  (rs.map encPerm).findIdx (tmRpB V y)

theorem gmpCosetIndex_lt {U V : Subgroup (Perm (Fin n))}
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    {y : Perm (Fin n)} (hy : y ∈ U) : gmpCosetIndex V rs y < rs.length := by
  obtain ⟨r, hr, v, hv, he⟩ := hrs.cover y hy
  have hmem : y * r⁻¹ ∈ V := by rw [he, mul_assoc, mul_inv_cancel, mul_one]; exact hv
  have h := List.findIdx_lt_length_of_exists
    (xs := rs.map encPerm) (p := tmRpB V y)
    ⟨encPerm r, List.mem_map.mpr ⟨r, hr, rfl⟩, (tmRpB_encPerm V y r).mpr hmem⟩
  simpa only [gmpCosetIndex, List.length_map] using h

theorem gmpCosetIndex_mem {U V : Subgroup (Perm (Fin n))}
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    {y : Perm (Fin n)} (hy : y ∈ U) :
    y * (rs[gmpCosetIndex V rs y]'(gmpCosetIndex_lt hrs hy))⁻¹ ∈ V := by
  have hi := gmpCosetIndex_lt hrs hy
  have hie : (rs.map encPerm).findIdx (tmRpB V y) < (rs.map encPerm).length := by
    simpa only [gmpCosetIndex, List.length_map] using hi
  have h := List.findIdx_getElem (w := hie)
  rw [List.getElem_map] at h
  exact (tmRpB_encPerm V y _).mp h

/-- A listed coset representative has a unique index. -/
theorem gmpCosetIndex_eq {U V : Subgroup (Perm (Fin n))}
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    {y : Perm (Fin n)} (hy : y ∈ U) {j : ℕ} (hj : j < rs.length)
    (hmem : y * rs[j]⁻¹ ∈ V) : gmpCosetIndex V rs y = j := by
  have hi := gmpCosetIndex_lt hrs hy
  have hiy := gmpCosetIndex_mem hrs hy
  have hij : rs[gmpCosetIndex V rs y]'hi * rs[j]⁻¹ ∈ V := by
    have h := V.mul_mem (V.inv_mem hiy) hmem
    convert h using 1 <;> group
  have hd := tmRpQuot_nodup hrs.sub hrs.distinct
  have he := (tmRpQ_eq_iff (hrs.sub _ (List.getElem_mem hi))
    (hrs.sub _ (List.getElem_mem hj))).mpr hij
  have hi' : gmpCosetIndex V rs y < (rs.map (tmRpQ U V)).length := by simpa using hi
  have hj' : j < (rs.map (tmRpQ U V)).length := by simpa using hj
  apply (hd.getElem_inj (hi := hi') (hj := hj')).mp
  simpa only [List.getElem_map] using he

/-- Cost of a scan over `L` representatives. -/
noncomputable def gmpIndexCost (hm : Membership) (Y L : ℕ) : ℕ :=
  L * tmRpPredC hm Y + 10 ^ 6 * (L + 1) ^ 2 * (Y + 1)

/-- A concrete search program labels a right coset using only the
membership primitive and the permutation operations. -/
theorem gmpCosetIndex_spec (hm : Membership) {P : Program}
    {fd pt jm comp inv : ℕ} (hfd : P.HasAt fd (findFuns fd pt))
    (hpt : P.funs[pt]? = some (tmRpPredF jm comp inv))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    {gv : Val} {V : Subgroup (Perm (Fin n))} (hV : GroupVal n gv V)
    {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y) (hgY : gv.wt ≤ Y)
    (rs : List (Perm (Fin n))) (y : Perm (Fin n)) :
    FunDet P fd (.list [.list [gv, encPerm y], .list (rs.map encPerm)])
      (.nat (gmpCosetIndex V rs y)) (gmpIndexCost hm Y rs.length) := by
  have hp : ∀ x ∈ rs.map encPerm, FunDet P pt (.list [.list [gv, encPerm y], x])
      (boolVal (tmRpB V y x)) (tmRpPredC hm Y) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact tmRpPred_spec hm hpt hjm hcomp hinv hV hY hgY y r
  have hf := find_spec hfd hp
  have hY1 : 1 ≤ Y := (Nat.one_le_pow 4 (n + 1) (by omega)).trans hY
  have hn2 : (n + 1) ^ 2 ≤ Y :=
    (Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ 4)).trans hY
  have hyW : (encPerm y).wt ≤ 4 * Y := (wt_encPerm_le y).trans (Nat.mul_le_mul_left _ hn2)
  have hrsW := tmRp_wt_reps (L := rs.length + 1) hY rs (by omega)
  have hc := wt_list2_le gv (encPerm y)
  have ha := wt_list2_le (.list [gv, encPerm y]) (.list (rs.map encPerm))
  let Z := (rs.length + 1) * (Y + 1)
  have hLY : (rs.length + 1) * Y ≤ Z := Nat.mul_le_mul_left _ (Nat.le_add_right Y 1)
  have hYZ : Y ≤ Z := le_trans (Nat.le_add_right Y 1) (Nat.le_mul_of_pos_left _ (by omega))
  have hLZ : rs.length + 1 ≤ Z := Nat.le_mul_of_pos_right _ (by omega)
  have hZ1 : 1 ≤ Z := by omega
  have harg : (Val.list [.list [gv, encPerm y], .list (rs.map encPerm)]).wt +
      2 * rs.length + 3 ≤ 100 * Z := by omega
  have hover : loopModK * (rs.length + 1) *
      ((Val.list [.list [gv, encPerm y], .list (rs.map encPerm)]).wt + 2 * rs.length + 3) ≤
      10 ^ 6 * (rs.length + 1) ^ 2 * (Y + 1) := by
    calc
      _ ≤ loopModK * (rs.length + 1) * (100 * Z) := Nat.mul_le_mul_left _ harg
      _ = 100000 * (rs.length + 1) ^ 2 * (Y + 1) := by dsimp [Z, loopModK]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  refine hf.mono fun w c ⟨hw, hcost⟩ => ⟨hw, ?_⟩
  simp only [List.map_const', List.length_map, List.sum_replicate, smul_eq_mul] at hcost
  exact hcost.trans (Nat.add_le_add_left hover _)

theorem gmpIndexCost_poly (hm : Membership) : PBU (fun L Y _ => gmpIndexCost hm Y L) := by
  have hp : PBU (fun _ Y _ => tmRpPredC hm Y) :=
    (PBU.W.smul (10 ^ 6)).add
      ((((PBU.W.smul 20).addc 2).pow (membershipPrim hm).k).smul (membershipPrim hm).c)
  exact (PBU.k.mul hp).add ((((PBU.k.addc 1).pow 2).smul (10 ^ 6)).mul (PBU.W.addc 1))

end GI.Impl
