module

public import Workspace.Algorithm.CarrierKeep
public import Workspace.Algorithm.DispatchInv

@[expose] public section

/-!
# The dispatcher's children keep the carrier

A dispatcher step (`DispatchStep`) runs its children under the block kernel (enumeration) or
the coordinate subgroup (product refinement), with the exposed or the split hierarchy. The
children keep the row record, the floor mode and `h` of the parent (`Run.dispatch`, `hbk`),
which needs the child group to keep the carrier of the retained rows (`CarrierOK`, the field
`hkeep` of `DispatchStep`). This holds when the quotient lies above the retained columns
(`KillsCols`) and the exposure keeps the old levels (`KeepsLevels`):

* every element that fixes every retained column acts trivially on the blocks, so it lies in
  the block kernel, and hence in the coordinate subgroup (Section A.4: "use full preimages of all
  quotient restrictions. This keeps the entire kernel `J`");
* the column partition is a level of the exposed hierarchy, and splitting the interval `top`
  into the coordinate intervals keeps every level: the last coordinate interval ends where `top`
  ends, at the whole domain.

Both conditions are what the existence proof's exposed quotient has (`State.expose_killsCols`,
`State.expose_keepsLevels`), and what a program can establish for the quotient it computes
(`exists_primitiveQuotient_of_cand`). No cited result is used.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)

namespace PrimitiveQuotient

/-- A column-fixing element of `G` lies in the block kernel, when the blocks lie above the
retained columns. -/
theorem mem_kernel_of_fixesCols (hkc : Q.KillsCols) {R : RowRecord Ω} {c : Setoid Ω}
    (hR : S.rows = some R) (hc : R.cols = some c) {g : Perm Ω} (hg : g ∈ S.G)
    (hf : FixesCols c S.dom g) : g ∈ Q.kernel :=
  ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 (hkc R c hR hc ⟨g, hg⟩ hf), rfl⟩

/-- **The block kernel keeps the carrier** with the exposed hierarchy. -/
theorem kernel_keeps (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) :
    CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post) :=
  S.carrier.mono Q.kernel_le (fun _ _ hR hc _ hg hf => Q.mem_kernel_of_fixesCols hkc hR hc hg hf)
    hkl

/-- The block kernel lies in the coordinate subgroup: an element that fixes every block fixes
every coordinate. -/
theorem kernel_le_coordinateGroup {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k))
    (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k) :
    Q.kernel ≤ Q.coordinateGroup e hS hb := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
  have h1 : Q.ρ.rangeRestrict g = 1 := Subtype.ext (MonoidHom.mem_ker.1 hg)
  rw [h1, map_one]

/-- **Splitting `top` into the coordinate intervals keeps every level** of the exposed
hierarchy on the domain. -/
theorem colsLevel_coordHier {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) (hr : 1 ≤ r)
    (c : Setoid Ω) (h : ColsLevel S.dom (Q.pre ++ Q.top :: Q.post) c) :
    ColsLevel S.dom (Q.pre ++ Q.coordHier e ++ Q.post) c := by
  obtain ⟨p0, p1, h0, hc⟩ := h
  rcases List.append_eq_append_iff.1 h0.symm with ⟨a', h1, -⟩ | ⟨c', h1, h2⟩
  · exact ⟨p0, a' ++ Q.coordHier e ++ Q.post, by rw [h1]; simp, hc⟩
  · cases c' with
    | nil => exact ⟨p0, Q.coordHier e ++ Q.post, by rw [h1]; simp, hc⟩
    | cons K c'' =>
      obtain ⟨rfl, h3⟩ := List.cons_eq_cons.1 h2
      have h3' : Q.post = c'' ++ p1 := h3
      -- the prefix ends inside `post` (or at `top`)
      obtain ⟨L, hL⟩ : ∃ L, Q.coordHier e = L ++ [Q.coordHier e |>.getLast (by
          simp [coordHier]; omega)] := ⟨_, (List.dropLast_append_getLast _).symm⟩
      set J := (Q.coordHier e).getLast (by simp [coordHier]; omega) with hJ
      have hlist : Q.pre ++ Q.coordHier e ++ Q.post = (Q.pre ++ L ++ J :: c'') ++ p1 := by
        rw [h3', hL]; simp
      refine ⟨Q.pre ++ L ++ J :: c'', p1, hlist, fun v hv w hw => ?_⟩
      have := hc v hv w hw
      rw [h1, hierLevel_append_cons] at this
      rw [show Q.pre ++ L ++ J :: c'' = (Q.pre ++ L) ++ J :: c'' by simp,
        hierLevel_append_cons]
      rw [← this]
      -- both levels are the last partition of `c''`, or the end of `top` / of `J`
      cases c'' using List.reverseRecOn with
      | nil =>
        show J.part.r v w ↔ Q.top.part.r v w
        have hJr : J.part = Q.coordPart e r := by
          rw [hJ, List.getLast_eq_getElem]
          simp [coordHier]
          congr 1
          omega
        rw [hJr]
        constructor
        · intro _; exact Q.top_univ v hv w hw
        · intro _; exact Or.inl ⟨hv, hw, fun j hj => absurd j.2 (by omega)⟩
      | append_singleton l x _ =>
        rw [List.foldl_append, List.foldl_append]
        rfl

/-- **The coordinate subgroup keeps the carrier** with the split hierarchy. -/
theorem productRed_keeps [Finite Ω] (P : Params) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (c : Q.ProductChoice) :
    CarrierOK (Q.productRed P c).K S.dom S.rows (Q.productRed P c).hier' := by
  have hb := Q.two_le_choose c.e
  have hK : (Q.productRed P c).K = Q.coordinateGroup c.e c.hS hb := rfl
  have hH : (Q.productRed P c).hier' = Q.pre ++ Q.coordHier c.e ++ Q.post := rfl
  rw [hK, hH]
  exact S.carrier.mono (Subgroup.map_subtype_le _)
    (fun _ _ hR hc _ hg hf =>
      Q.kernel_le_coordinateGroup c.e c.hS hb (Q.mem_kernel_of_fixesCols hkc hR hc hg hf))
    (fun col h => Q.colsLevel_coordHier c.e (by have := c.hr; omega) col (hkl col h))

end PrimitiveQuotient

end GI.Algorithm
