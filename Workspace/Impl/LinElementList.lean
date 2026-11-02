import Workspace.Impl.LinElementMap
import Workspace.Impl.LinMapAll

/-! Integer coordinates of a list of known elements of the same group.
The output rows have the right images in every abelian quotient. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linElementListFuns (b jm : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ linElementCoordinatesFuns (b + 3) jm

theorem linElementListFuns_length (b jm : ℕ) : (linElementListFuns b jm).length = 45 := rfl

structure linElementListAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  element : linElementCoordinatesAt P (b + 3) jm hm

theorem linElementListAt_of {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (linElementListFuns b jm))
    (hj : P.prims[jm]? = some (linMembershipPrim hm)) : linElementListAt P b jm hm where
  map := h.block 0 rfl
  element := linElementCoordinatesAt_of (h.block 3 rfl) hj

noncomputable def linElementListCoefficient (hm : ConstructiveMembership) : ℕ :=
  (linElementBudget_poly hm).choose
noncomputable def linElementListDegree (hm : ConstructiveMembership) : ℕ :=
  (linElementBudget_poly hm).choose_spec.choose
noncomputable def linElementListBudget (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linElementListCoefficient hm * (100 * (W + 1) + 2) ^ linElementListDegree hm
noncomputable def linElementListCost (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linMapBudget W (linElementListBudget hm W)

theorem linElementListBudget_bound (hm : ConstructiveMembership) (I : MemberInst) (W : ℕ)
    (hw : (memberInput I).wt ≤ 100 * (W + 1)) :
    linElementCoordinatesCost hm I ≤ linElementListBudget hm W := by
  have hh := (linElementBudget_poly hm).choose_spec.choose_spec 0 (memberInput I).wt 0
  have hc := linElementCoordinatesCost_le hm I
  exact hc.trans (hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))

theorem linForall₂_vecMatrix {α : Type*} {d : ℕ} (R : α → (Fin d → ℤ) → Prop)
    {xs : List α} {ws : List Val}
    (h : List.Forall₂ (fun x w => ∃ z : Fin d → ℤ, w = linVecVal z ∧ R x z) xs ws) :
    ∃ Z : Matrix (Fin xs.length) (Fin d) ℤ,
      ws = (List.finRange xs.length).map (fun i => linVecVal (Z i)) ∧
      ∀ i : Fin xs.length, R xs[i.val] (Z i) := by
  classical
  have hi (i : Fin xs.length) : ∃ z : Fin d → ℤ,
      ws[i.val]'(by rw [← h.length_eq]; exact i.isLt) = linVecVal z ∧ R xs[i.val] z :=
    h.get i.isLt (by rw [← h.length_eq]; exact i.isLt)
  choose Z hZ using hi
  refine ⟨Z, ?_, fun i => (hZ i).2⟩
  apply List.ext_getElem (by simp [h.length_eq])
  intro i hi hj
  simpa only [List.getElem_map, List.getElem_finRange] using (hZ ⟨i, by simpa using hj⟩).1

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8000 in
theorem linElementList_spec (hm : ConstructiveMembership) {P : Program} {b jm n : ℕ}
    (h : linElementListAt P b jm hm) (as bs : List (Equiv.Perm (Fin n)))
    (hbs : ∀ x ∈ bs, x ∈ gens as) {Q : Type*} [CommGroup Q] (π : gens as →* Q) :
    let a := Val.list [encGroup as, .list (bs.map encPerm)]
    FunAll P b a (fun out cost =>
      (∃ Z : Matrix (Fin bs.length) (Fin as.length) ℤ, out = encIntMatrix Z ∧
        ∀ i : Fin bs.length,
          linCoordHom (fun j : Fin as.length => π (linIntoSubgroup (gens as) as[j.val]))
            (Multiplicative.ofAdd (Z i)) = π (linIntoSubgroup (gens as) bs[i.val])) ∧
      cost ≤ linElementListCost hm a.wt) := by
  let a := Val.list [encGroup as, .list (bs.map encPerm)]
  let W := a.wt
  let R (x : Equiv.Perm (Fin n)) (z : Fin as.length → ℤ) :=
    linCoordHom (fun j : Fin as.length => π (linIntoSubgroup (gens as) as[j.val]))
      (Multiplicative.ofAdd z) = π (linIntoSubgroup (gens as) x)
  have hs (x : Equiv.Perm (Fin n)) (hx : x ∈ bs) :
      FunAll P (b + 3) (.list [encGroup as, encPerm x]) (fun out cost =>
        (∃ z : Fin as.length → ℤ, out = linVecVal z ∧ R x z) ∧
        cost ≤ linElementListBudget hm W) := by
    let I : MemberInst := ⟨n, as, x⟩
    have ha : (encGroup as).wt < W := wt_le_wt_list (by simp [a, W])
    have hb : (Val.list (bs.map encPerm)).wt < W := wt_le_wt_list (by simp [a, W])
    have hxw : (encPerm x).wt < (Val.list (bs.map encPerm)).wt := wt_le_wt_list (by
      exact List.mem_map.mpr ⟨x, hx, rfl⟩)
    have hw : (memberInput I).wt ≤ 100 * (W + 1) := by
      have hh := wt_list2_le (encGroup as) (encPerm x)
      dsimp only [memberInput, I]; omega
    refine (linElementCoordinates_spec hm h.element I (hbs x hx)).mono fun out cost ho => ?_
    obtain ⟨⟨prog, z, rfl, hp, hz⟩, hc⟩ := ho
    refine ⟨⟨z, rfl, ?_⟩, hc.trans (linElementListBudget_bound hm I W hw)⟩
    have he := linElementCoordinates_map as π x (hbs x hx) prog z hp hz
    simpa only [R, linIntoSubgroup, dif_pos (hbs x hx)] using he
  refine (linMapAll_spec h.map encPerm encPerm_injective
    (fun x out => ∃ z : Fin as.length → ℤ, out = linVecVal z ∧ R x z)
    (encGroup as) bs (linElementListBudget hm W) hs).mono fun out cost ho => ?_
  obtain ⟨⟨ws, rfl, hws⟩, hc⟩ := ho
  obtain ⟨Z, rfl, hZ⟩ := linForall₂_vecMatrix R hws
  exact ⟨⟨Z, rfl, hZ⟩, hc⟩

theorem linElementListCost_poly (hm : ConstructiveMembership) :
    PBU (fun _ W _ => linElementListCost hm W) := by
  unfold linElementListCost linElementListBudget linMapBudget
  norm_poly

end GI.Impl
