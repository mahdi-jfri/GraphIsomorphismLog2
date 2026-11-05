module

public import Workspace.Impl.LinObjectImageMath
public import Workspace.Impl.LinObjectQuotient

@[expose] public section

/-! The configuration space is exactly the product of local abelian
quotients. This makes coordinates independent of transporter choices. -/
namespace GI.Impl
open GI.Cited GI.Multicoset

variable {n : ℕ} {Q Ω : Type*} [CommGroup Q] [RAct (Equiv.Perm (Fin n)) Ω]

noncomputable def linObjectConfigCoord (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (Y Z : Multiset Ω) :
    ∀ T : {T // T ∈ pieces A Y}, Additive Q ⧸ linObjectGroupImage A π (Aut A T.val) :=
  fun T => (linObjectGroupImage A π (Aut A T.val)).mkQ
    (Additive.ofMul (π (linIntoSubgroup A (coord A Z T.val))))

theorem linObject_mkQ_eq_iff {V : Type*} [AddCommGroup V]
    (B : Submodule ℤ V) (x y : V) : B.mkQ x = B.mkQ y ↔ x - y ∈ B := by
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem linObjectConfigCoord_eq_iff (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (Y Z Z' : Multiset Ω) (hZ : Conf A Y Z) (hZ' : Conf A Y Z')
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    linObjectConfigCoord A π Y Z = linObjectConfigCoord A π Y Z' ↔ Z = Z' := by
  constructor
  · intro he
    rw [conf_coord hZ, conf_coord hZ']
    apply Finset.sum_congr rfl
    intro T hT
    let a : A := ⟨coord A Z T, (coord_spec hZ hT).1⟩
    let b : A := ⟨coord A Z' T, (coord_spec hZ' hT).1⟩
    have hi := congrFun he ⟨T, hT⟩
    have ha : linIntoSubgroup A (coord A Z T) = a := Subtype.ext
      (linIntoSubgroup_val A _ (coord_spec hZ hT).1)
    have hb : linIntoSubgroup A (coord A Z' T) = b := Subtype.ext
      (linIntoSubgroup_val A _ (coord_spec hZ' hT).1)
    simp only [linObjectConfigCoord, ha, hb] at hi
    exact (linObject_act_eq_iff_image A π T (hker T hT) a b).mpr
      ((linObject_mkQ_eq_iff _ _ _).mp hi)
  · rintro rfl
    rfl

theorem linObjectConfigCoord_surjective (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (hπ : Function.Surjective π) (Y : Multiset Ω)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    ∀ w : (∀ T : {T // T ∈ pieces A Y},
      Additive Q ⧸ linObjectGroupImage A π (Aut A T.val)),
      ∃ Z, Conf A Y Z ∧ linObjectConfigCoord A π Y Z = w := by
  classical
  intro w
  have hx (T : {T // T ∈ pieces A Y}) : ∃ a : A,
      (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π a)) = w T := by
    obtain ⟨q, hq⟩ := Submodule.mkQ_surjective (linObjectGroupImage A π (Aut A T.val)) (w T)
    obtain ⟨a, ha⟩ := hπ q.toMul
    refine ⟨a, ?_⟩
    rw [ha]
    exact hq
  choose a ha using hx
  let v : Multiset Ω → Equiv.Perm (Fin n) := fun T =>
    if hT : T ∈ pieces A Y then (a ⟨T, hT⟩).val else 1
  let Z := ∑ T ∈ pieces A Y, T ↼ v T
  have hv : ∀ T ∈ pieces A Y, v T ∈ A := by
    intro T hT
    simpa only [v, dif_pos hT] using (a ⟨T, hT⟩).property
  have hZ : Conf A Y Z := ⟨v, hv, rfl⟩
  refine ⟨Z, hZ, ?_⟩
  funext T
  rw [← ha T]
  apply (linObject_mkQ_eq_iff _ _ _).mpr
  apply (linObject_act_eq_iff_image A π T.val (hker T.val T.property) _ (a T)).mp
  have hc := (coord_spec hZ T.property).2
  have hp := partAt_conf T.property hv
  have he : T.val ↼ coord A Z T.val = T.val ↼ (a T).val := by
    rw [← hc]
    simpa only [Z, v, dif_pos T.property] using hp
  change T.val ↼ (linIntoSubgroup A (coord A Z T.val)).val = T.val ↼ (a T).val
  have hh := linIntoSubgroup_val A _ (coord_spec hZ T.property).1
  change (linIntoSubgroup A (coord A Z T.val)).val = coord A Z T.val at hh
  rw [hh]
  exact he

noncomputable def linObjectConfigEquiv (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (hπ : Function.Surjective π) (Y : Multiset Ω)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    {Z // Conf A Y Z} ≃ (∀ T : {T // T ∈ pieces A Y},
      Additive Q ⧸ linObjectGroupImage A π (Aut A T.val)) :=
  Equiv.ofBijective (fun Z => linObjectConfigCoord A π Y Z.val)
    ⟨fun Z Z' he => Subtype.ext ((linObjectConfigCoord_eq_iff A π Y Z.val Z'.val
      Z.property Z'.property hker).mp he), by
      intro w
      obtain ⟨Z, hZ, he⟩ := linObjectConfigCoord_surjective A π hπ Y hker w
      exact ⟨⟨Z, hZ⟩, he⟩⟩

end GI.Impl
