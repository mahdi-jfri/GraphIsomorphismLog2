module

public import Workspace.Impl.LinObjectConfigAction
public import Workspace.Impl.LinAffineFromAction

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Multicoset
variable {n : ℕ} {Q Ω : Type*} [CommGroup Q] [RAct (Equiv.Perm (Fin n)) Ω]

noncomputable def linObjectConfigOf (A : Subgroup (Equiv.Perm (Fin n)))
    (Y : Multiset Ω) (w : Multiset Ω → Equiv.Perm (Fin n)) : Multiset Ω :=
  ∑ T ∈ pieces A Y, T ↼ w T

theorem linObjectConfigOf_conf (A : Subgroup (Equiv.Perm (Fin n))) (Y : Multiset Ω)
    (w : Multiset Ω → Equiv.Perm (Fin n)) (hw : ∀ T ∈ pieces A Y, w T ∈ A) :
    Conf A Y (linObjectConfigOf A Y w) := ⟨w, hw, rfl⟩

theorem linObjectConfigOf_coord (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (Y : Multiset Ω) (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (w : Multiset Ω → Equiv.Perm (Fin n)) (hw : ∀ T ∈ pieces A Y, w T ∈ A)
    (T : {T // T ∈ pieces A Y}) :
    linObjectConfigCoord A π Y (linObjectConfigOf A Y w) T =
      (linObjectGroupImage A π (Aut A T.val)).mkQ
        (Additive.ofMul (π ⟨w T.val, hw T.val T.property⟩)) :=
  linObjectConfigCoord_of_repr A π Y _ (linObjectConfigOf_conf A Y w hw) hker w hw
    (fun _ hT => partAt_conf hT hw) T

theorem linObjectConfigOf_mul_coord (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (Y : Multiset Ω) (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (w v : Multiset Ω → Equiv.Perm (Fin n))
    (hw : ∀ T ∈ pieces A Y, w T ∈ A) (hv : ∀ T ∈ pieces A Y, v T ∈ A) :
    linObjectConfigCoord A π Y (linObjectConfigOf A Y (fun T => w T * v T)) =
      linObjectConfigCoord A π Y (linObjectConfigOf A Y w) +
        linObjectConfigCoord A π Y (linObjectConfigOf A Y v) := by
  funext T
  rw [linObjectConfigOf_coord A π Y hker _ (fun T hT => A.mul_mem (hw T hT) (hv T hT)),
    Pi.add_apply, linObjectConfigOf_coord A π Y hker w hw,
    linObjectConfigOf_coord A π Y hker v hv]
  change (linObjectGroupImage A π (Aut A T.val)).mkQ
    (Additive.ofMul (π ((⟨w T.val, hw T.val T.property⟩ : A) * ⟨v T.val, hv T.val T.property⟩))) = _
  rw [map_mul]
  exact map_add _ _ _

theorem linObjectConfigCoord_act_repr {H A : Subgroup (Equiv.Perm (Fin n))}
    (π : A →* Q) (hn : Normalizes H A) (Y Z : Multiset Ω)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ H) (hy : Conf A Y (Y ↼ g)) (hZ : Conf A Y Z)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (w : Multiset Ω → Equiv.Perm (Fin n)) (hw : ∀ S ∈ pieces A Y, w S ∈ A)
    (he : ∀ S ∈ pieces A Y, partAt A Z S = S ↼ w S) :
    ∀ T : {T // T ∈ pieces A Y},
      ∃ ha : coord A (Y ↼ g) T.val * (g⁻¹ * w (src A Y g T.val) * g) ∈ A,
      linObjectConfigCoord A π Y (Z ↼ g) T =
        (linObjectGroupImage A π (Aut A T.val)).mkQ
          (Additive.ofMul (π ⟨coord A (Y ↼ g) T.val * (g⁻¹ * w (src A Y g T.val) * g), ha⟩)) := by
  have hmem : ∀ T ∈ pieces A Y,
      coord A (Y ↼ g) T * (g⁻¹ * w (src A Y g T) * g) ∈ A := by
    intro T hT
    exact A.mul_mem (coord_spec hy hT).1 (by
      simpa using hn.inv hg (hw _ (src_spec hn hg hy hT).1))
  intro T
  refine ⟨hmem T.val T.property, ?_⟩
  exact linObjectConfigCoord_of_repr A π Y _ (affine_law hn hg hy hZ).2.2 hker
    (fun T => coord A (Y ↼ g) T * (g⁻¹ * w (src A Y g T) * g)) hmem
    (fun T hT => linObject_partAt_act_repr hn hg hy w he hT) T

theorem linObjectConfigCoord_self (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (Y : Multiset Ω) (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    linObjectConfigCoord A π Y Y = 0 := by
  have he : linObjectConfigOf A Y (fun _ => 1) = Y := by
    simp [linObjectConfigOf, sum_pieces]
  funext T
  have hh := linObjectConfigOf_coord A π Y hker (fun _ => 1) (fun _ _ => A.one_mem) T
  have hh' : linObjectConfigCoord A π Y Y T =
      (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π 1)) := by
    have h_one : (⟨1, A.one_mem⟩ : A) = 1 := rfl
    simpa only [he, h_one] using hh
  simpa using hh'

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectConfig_act_add {H A : Subgroup (Equiv.Perm (Fin n))}
    (π : A →* Q) (hn : Normalizes H A) (Y : Multiset Ω)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ H) (hy : Conf A Y (Y ↼ g))
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (w v : Multiset Ω → Equiv.Perm (Fin n))
    (hw : ∀ T ∈ pieces A Y, w T ∈ A) (hv : ∀ T ∈ pieces A Y, v T ∈ A) :
    linObjectConfigCoord A π Y ((linObjectConfigOf A Y (fun T => w T * v T)) ↼ g) +
      linObjectConfigCoord A π Y (Y ↼ g) =
    linObjectConfigCoord A π Y ((linObjectConfigOf A Y w) ↼ g) +
      linObjectConfigCoord A π Y ((linObjectConfigOf A Y v) ↼ g) := by
  have hp : ∀ T ∈ pieces A Y, w T * v T ∈ A := fun T hT => A.mul_mem (hw T hT) (hv T hT)
  have hcw := linObjectConfigCoord_act_repr π hn Y _ hg hy
    (linObjectConfigOf_conf A Y w hw) hker w hw (fun T hT => partAt_conf hT hw)
  have hcv := linObjectConfigCoord_act_repr π hn Y _ hg hy
    (linObjectConfigOf_conf A Y v hv) hker v hv (fun T hT => partAt_conf hT hv)
  have hcp := linObjectConfigCoord_act_repr π hn Y _ hg hy
    (linObjectConfigOf_conf A Y _ hp) hker (fun T => w T * v T) hp
    (fun T hT => partAt_conf hT hp)
  funext T
  obtain ⟨hwg, hew⟩ := hcw T
  obtain ⟨hvg, hev⟩ := hcv T
  obtain ⟨hpg, hep⟩ := hcp T
  simp only [Pi.add_apply]
  rw [hew, hev, hep]
  let S := src A Y g T.val
  have hS : S ∈ pieces A Y := (src_spec hn hg hy T.property).1
  let u : A := ⟨coord A (Y ↼ g) T.val, (coord_spec hy T.property).1⟩
  have hwc : g⁻¹ * w S * g ∈ A := by simpa using hn.inv hg (hw S hS)
  have hvc : g⁻¹ * v S * g ∈ A := by simpa using hn.inv hg (hv S hS)
  let a : A := ⟨g⁻¹ * w S * g, hwc⟩
  let b : A := ⟨g⁻¹ * v S * g, hvc⟩
  have hu : linIntoSubgroup A (coord A (Y ↼ g) T.val) = u :=
    Subtype.ext (linIntoSubgroup_val A _ (coord_spec hy T.property).1)
  have hprod : (⟨coord A (Y ↼ g) T.val *
      (g⁻¹ * (w S * v S) * g), hpg⟩ : A) = u * (a * b) := by
    apply Subtype.ext
    change coord A (Y ↼ g) T.val * (g⁻¹ * (w S * v S) * g) =
      coord A (Y ↼ g) T.val * ((g⁻¹ * w S * g) * (g⁻¹ * v S * g))
    group
  change (linObjectGroupImage A π (Aut A T.val)).mkQ
      (Additive.ofMul (π ⟨_, hpg⟩)) +
      (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π (linIntoSubgroup A _))) = _
  rw [hu, hprod]
  change (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π (u * (a * b)))) +
      (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π u)) =
    (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π (u * a))) +
      (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π (u * b)))
  simp only [map_mul]
  change (linObjectGroupImage A π (Aut A T.val)).mkQ
      (Additive.ofMul (π u) + (Additive.ofMul (π a) + Additive.ofMul (π b))) + _ =
    (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π u) + Additive.ofMul (π a)) +
      (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π u) + Additive.ofMul (π b))
  simp only [map_add]
  abel

end GI.Impl
