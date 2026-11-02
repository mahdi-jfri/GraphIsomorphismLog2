import Workspace.Impl.TermRecProgDer

/-!
# T5, the pieces of a transporter by the image of one point, and the shift of a list

The pairwise step computes `Iso_H(S, T)` from the target: it fixes `x ∈ T` and splits the
transporter by the preimage `x^{h⁻¹} ∈ S` of `x` (`tmRi_union_eq`). For one `y ∈ S`, the part
`{h ∈ Iso_H(S, T) : x^{h⁻¹} = y}` is empty when no element of `H` carries `x` to `y`
(`tmRi_piece_empty`), and otherwise it is `τ⁻¹ Iso_{H_x}(S^{τ⁻¹}, T)` for any `τ ∈ H` with
`x^τ = y` (`tmRi_piece_eq`). This is the mirror of the paper's step, in which a point of the
source is fixed.

`tmRi_shift_spec`, `tmRi_mapShift_spec`: the shift `[c, gens L, h] ↦ [c, gens L, h τ]` of an
object and of a list; on multisets it is the action of `τ` (`tmRi_ms_shift`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open scoped Pointwise
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

section Math

variable {G : Type} [Group G] {Ω : Type} [RAct G Ω]

/-- The part of a transporter with a given preimage of `x`. -/
def tmRiPart (H : Subgroup G) (S T : Multiset Ω) (x y : Ω) : Set G :=
  {h | h ∈ Iso H S T ∧ x ↼ h⁻¹ = y}

theorem tmRi_piece_eq {H : Subgroup G} {S T : Multiset Ω} {x y : Ω} {τ : G} (hτ : τ ∈ H)
    (hxy : x ↼ τ = y) :
    τ⁻¹ • (Iso (Aut H x) (S ↼ τ⁻¹) T : Set G) = tmRiPart H S T x y := by
  ext h
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_inv]
  have key : x ↼ (τ * h) = x ↔ x ↼ h⁻¹ = y := by
    rw [← act_act, hxy]
    constructor
    · intro e; rw [← e, act_act_inv]
    · intro e; rw [← e, act_act, inv_mul_cancel, act_one]
  have hH : τ * h ∈ H ↔ h ∈ H := ⟨fun h1 => by simpa using H.mul_mem (H.inv_mem hτ) h1,
    fun h1 => H.mul_mem hτ h1⟩
  show ((τ * h ∈ H ∧ x ↼ (τ * h) = x) ∧ S ↼ τ⁻¹ ↼ (τ * h) = T) ↔ ((h ∈ H ∧ S ↼ h = T) ∧ _)
  rw [act_act, inv_mul_cancel_left, key, hH]
  tauto

theorem tmRi_piece_empty {H : Subgroup G} {S T : Multiset Ω} {x y : Ω}
    (hno : ∀ g ∈ H, x ↼ g ≠ y) : tmRiPart H S T x y = ∅ := by
  ext h
  simp only [tmRiPart, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hh
  exact hno _ (H.inv_mem hh.1)

theorem tmRi_union_eq {H : Subgroup G} {S T : Multiset Ω} {x : Ω} (hx : x ∈ T) :
    {h | ∃ y ∈ S, h ∈ tmRiPart H S T x y} = Iso H S T := by
  ext h
  simp only [tmRiPart, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, -, hh, -⟩
    exact hh
  · intro hh
    refine ⟨x ↼ h⁻¹, ?_, hh, rfl⟩
    have : x ∈ S ↼ h := by rw [hh.2]; exact hx
    exact mem_act.1 this

end Math

variable {n : ℕ}

/-- The shift of an object by `τ`. -/
def tmRiSh (τ : Perm (Fin n)) (o : TmRiO n) : TmRiO n := (o.1, o.2.1, o.2.2 * τ)

theorem tmRi_ms_shift (τ : Perm (Fin n)) (L : List (TmRiO n)) :
    tmGlMs (L.map (tmRiSh τ)) = tmGlMs L ↼ τ := by
  simp only [tmGlMs, multiset_act_def, Multiset.map_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro o _
  simp [tmRiSh, tmRi_obj_act]

theorem tmRiOK_shift {C : ℕ} {L : List (TmRiO n)} (h : TmRiOK C L) (τ : Perm (Fin n)) :
    TmRiOK C (L.map (tmRiSh τ)) := by
  intro o ho
  obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.1 ho
  refine ⟨(h o₀ ho₀).1, (h o₀ ho₀).2.1, fun o' ho' => ?_⟩
  obtain ⟨o₁, ho₁, rfl⟩ := List.mem_map.1 ho'
  exact (h o₀ ho₀).2.2 o₁ ho₁

/-- The cost bound of a shift. -/
def tmRiShC (n C : ℕ) : ℕ := permK * (n + 1) ^ 3 + 10 ^ 5 * (n + 1) ^ 6 + 100 * C

/-- **The shift of an object.** -/
theorem tmRi_shift_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) (τ : Perm (Fin n)) (o : TmRiO n)
    (hl : o.2.1.length ≤ n ^ 2) {C : ℕ} (hC : o.1 ≤ C) :
    FunDet P (b + 12) (.list [encPerm τ, tmGlObjVal o]) (tmGlObjVal (tmRiSh τ o))
      (tmRiShC n C) := by
  set vs : List Val := [encPerm τ, tmGlObjVal o]
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dc := Det.get' d1 (Det.nat 0) (v := .nat o.1) rfl
  have dg := Det.get' d1 (Det.nat 1) (v := encGroup o.2.1) rfl
  have dh := Det.get' d1 (Det.nat 2) (v := encPerm o.2.2) rfl
  have dm := Det.call (Det.mk2 dh d0) (compose_spec hP.comp o.2.2 τ)
  refine FunDet.intro hP.sh ((Det.mk3 dc dg dm).mono ?_)
  have hwo := tmRi_wt_obj o hl
  have hwo' := tmRi_wt_obj (tmRiSh τ o) hl
  have hwt := wt_encPerm_le τ
  have hwh := wt_encPerm_le o.2.2
  have hwh' := wt_encPerm_le (o.2.2 * τ)
  have hwg := wt_encGroup_le_sq hl
  have hcw := wt_nat_le o.1
  have hvw := wt_list2_le (encPerm τ) (tmGlObjVal o)
  have h2w := wt_list2_le (encPerm o.2.2) (encPerm τ)
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [tmRiSh] at hwo'
  unfold tmRiShC
  show _ ≤ permK * (n + 1) ^ 3 + 10 ^ 5 * (n + 1) ^ 6 + 100 * C
  have h3 := wt_list3_le (.nat o.1) (encGroup o.2.1) (encPerm (o.2.2 * τ))
  have hvs : (Val.list vs).wt = (Val.list [encPerm τ, tmGlObjVal o]).wt := rfl
  have h1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The cost bound of the shift of a list of `m` objects. -/
def tmRiMapShC (n C m : ℕ) : ℕ := (m + 1) * tmRiShC n C + mapK * (m + 1) * (10 ^ 4 * (m + 1) * ((n + 1) ^ 6 + C + 1))

theorem tmRi_wt_objs {L : List (TmRiO n)} {C : ℕ} (hok : TmRiOK C L) :
    (tmGlObjsVal L).wt ≤ L.length * (2 * (1000 * (n + 1) ^ 6 + 2 * C) + 1) + 4 := by
  have := tmRi_wt_list_le (L.map tmGlObjVal) (c := 1000 * (n + 1) ^ 6 + 2 * C) (by
    intro v hv
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hv
    have := tmRi_wt_obj o (hok o ho).1
    have := (hok o ho).2.1
    omega)
  simpa [tmGlObjsVal] using this

/-- **The shift of a list.** -/
theorem tmRi_mapShift_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) (τ : Perm (Fin n)) {C : ℕ}
    {L : List (TmRiO n)} (hok : TmRiOK C L) :
    FunDet P (b + 75) (.list [encPerm τ, tmGlObjsVal L]) (tmGlObjsVal (L.map (tmRiSh τ)))
      (tmRiMapShC n C L.length) := by
  have hm := map_spec hP.mapSh (c := encPerm τ) (xs := L.map tmGlObjVal)
    (R := fun x w => ∀ o : TmRiO n, x = tmGlObjVal o → w = tmGlObjVal (tmRiSh τ o))
    (B := fun _ => tmRiShC n C) (fun x hx => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
      refine FunAll.mono (tmRi_shift_spec hP τ o (hok o ho).1 (hok o ho).2.1) fun w c hw => ⟨?_, hw.2⟩
      intro o' ho'
      rw [tmRi_objVal_inj ho'.symm, hw.1])
  refine hm.mono fun w cost ⟨ws, hw, hR, hc⟩ => ⟨?_, ?_⟩
  · have : ∀ (L : List (TmRiO n)) (ws : List Val),
        List.Forall₂ (fun x w => ∀ o : TmRiO n, x = tmGlObjVal o → w = tmGlObjVal (tmRiSh τ o))
          (L.map tmGlObjVal) ws → ws = (L.map (tmRiSh τ)).map tmGlObjVal := by
      intro L
      induction L with
      | nil => intro ws h; simpa using h
      | cons a L ih =>
        intro ws h
        rw [List.map_cons] at h
        obtain ⟨w, ws', hw, hws, rfl⟩ := List.forall₂_cons_left_iff.1 h
        simp [hw a rfl, ih ws' hws]
    rw [hw, this L ws hR]; rfl
  · have hws : w = tmGlObjsVal (L.map (tmRiSh τ)) := by
      have : ∀ (L : List (TmRiO n)) (ws : List Val),
          List.Forall₂ (fun x w => ∀ o : TmRiO n, x = tmGlObjVal o → w = tmGlObjVal (tmRiSh τ o))
            (L.map tmGlObjVal) ws → ws = (L.map (tmRiSh τ)).map tmGlObjVal := by
        intro L
        induction L with
        | nil => intro ws h; simpa using h
        | cons a L ih =>
          intro ws h
          rw [List.map_cons] at h
          obtain ⟨w, ws', hw, hws, rfl⟩ := List.forall₂_cons_left_iff.1 h
          simp [hw a rfl, ih ws' hws]
      rw [hw, this L ws hR]; rfl
    rw [hws] at hc
    have hs := tmRi_sum_const (L.map tmGlObjVal) (fun _ => tmRiShC n C) (K := tmRiShC n C)
      (fun _ _ => le_rfl)
    rw [List.length_map] at hs
    have h1 := tmRi_wt_objs hok
    have h2 := tmRi_wt_objs (tmRiOK_shift hok τ)
    rw [List.length_map] at h2
    have h3 := wt_list2_le (encPerm τ) (tmGlObjsVal L)
    have h4 := wt_encPerm_le τ
    have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hX : (Val.list [encPerm τ, .list (L.map tmGlObjVal)]).wt + (tmGlObjsVal (L.map (tmRiSh τ))).wt + 1 ≤
        10 ^ 4 * (L.length + 1) * ((n + 1) ^ 6 + C + 1) := by
      have hm1 : L.length * (2 * (1000 * (n + 1) ^ 6 + 2 * C) + 1) ≤
          (L.length + 1) * (2000 * ((n + 1) ^ 6 + C + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hm2 : (L.length + 1) * (2000 * ((n + 1) ^ 6 + C + 1)) =
          2000 * ((L.length + 1) * ((n + 1) ^ 6 + C + 1)) := by ring
      have hm3 : 10 ^ 4 * (L.length + 1) * ((n + 1) ^ 6 + C + 1) =
          10 ^ 4 * ((L.length + 1) * ((n + 1) ^ 6 + C + 1)) := by ring
      have hm4 : (n + 1) ^ 6 + C + 1 ≤ (L.length + 1) * ((n + 1) ^ 6 + C + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have e : (tmGlObjsVal L) = .list (L.map tmGlObjVal) := rfl
      rw [e] at h1 h3
      omega
    have hmk : mapK * ((L.map tmGlObjVal).length + 1) *
        ((Val.list [encPerm τ, .list (L.map tmGlObjVal)]).wt + (tmGlObjsVal (L.map (tmRiSh τ))).wt + 1) ≤
        mapK * (L.length + 1) * (10 ^ 4 * (L.length + 1) * ((n + 1) ^ 6 + C + 1)) := by
      rw [List.length_map]; exact Nat.mul_le_mul_left _ hX
    have hB : L.length * tmRiShC n C ≤ (L.length + 1) * tmRiShC n C := Nat.mul_le_mul_right _ (by omega)
    unfold tmRiMapShC
    omega


end GI.Impl
