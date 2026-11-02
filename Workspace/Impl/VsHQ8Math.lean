import Workspace.Impl.VsHConjT
import Workspace.Proved.VsMQ8
import Workspace.Proved.VsMHardB

/-!
# The `Q₈` centralizer as a stabilizer

For the tuple `y₀ = (T(b))_{b ∈ B}`:

* `vsH_q8_fix`: `g ∈ ⟨hs⟩` fixes `y₀` iff `ρ g` commutes with every `ρ b`;
* `vsH_q8_orbit`: the orbit of `y₀` under `⟨cs⟩ ≤ ⟨hs⟩` has at most `|C̄ : C_{C̄}(Ȳ)|` points,
  for any `C̄ ≥ ρ⟨cs⟩` with `ρ B ⊆ Ȳ`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- **Fixed points of the tuple.** -/
theorem vsH_q8_fix (hs : VsQStOK s) {B : List (Perm (Fin I.n))} (hB : ∀ b ∈ B, b ∈ gens s.hs)
    {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    vsHAlT s g (B.map (vsHT s)) = B.map (vsHT s) ↔
      ∀ b ∈ B, vsPRho hs g * vsPRho hs b = vsPRho hs b * vsPRho hs g := by
  unfold vsHAlT
  rw [List.map_map]
  constructor
  · intro h b hb
    have := List.map_eq_map_iff.1 h b hb
    exact (vsH_conj_fix hs hg (hB b hb)).1 this
  · intro h
    exact List.map_congr_left fun b hb => (vsH_conj_fix hs hg (hB b hb)).2 (h b hb)

/-- The conjugate tuple, as a function of the local unit. -/
noncomputable def vsHPhi (hs : VsQStOK s) (B : List (Perm (Fin I.n)))
    (u : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) :
    List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :=
  B.map fun b => (LinearMap.toMatrix' ((u * vsPRho hs b * u⁻¹ :
    (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)))ᵀ

theorem vsHT_eq (hs : VsQStOK s) {x : Perm (Fin I.n)} (hx : x ∈ gens s.hs) :
    vsHT s x = (LinearMap.toMatrix' ((vsPRho hs x : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) :
      Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)))ᵀ := by
  rw [vsHT, vsPRho_of hs hx, vsQRho_eq_toLin' hs hx, LinearMap.toMatrix'_toLin']

theorem vsHAlT_eq (hs : VsQStOK s) {B : List (Perm (Fin I.n))} (hB : ∀ b ∈ B, b ∈ gens s.hs)
    {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    vsHAlT s g (B.map (vsHT s)) = vsHPhi hs B (vsPRho hs g) := by
  unfold vsHAlT vsHPhi
  rw [List.map_map]
  refine List.map_congr_left fun b hb => ?_
  have hb' := hB b hb
  have e : vsHAl s g (vsHT s b) = vsHT s (g * b * g⁻¹) := by
    rw [vsHAl, vsHT_mul hs (mul_mem hg hb') (inv_mem hg), vsHT_mul hs hg hb', _root_.mul_assoc]
  simp only [Function.comp_apply]
  rw [e, vsHT_eq hs (mul_mem (mul_mem hg hb') (inv_mem hg)), vsPRho_conj hs hb' hg]

/-- **The orbit is small.** -/
theorem vsH_q8_orbit (hs : VsQStOK s) {B cs : List (Perm (Fin I.n))}
    (hB : ∀ b ∈ B, b ∈ gens s.hs) (hcs : genGroup cs ≤ gens s.hs)
    {Cb Y : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hCb : ∀ g ∈ genGroup cs, vsPRho hs g ∈ Cb) (hBY : ∀ b ∈ B, vsPRho hs b ∈ Y) :
    (vsQOrb (vsHAlT s) cs (B.map (vsHT s))).ncard ≤
      (Subgroup.centralizer (Y : Set (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)).relIndex Cb := by
  classical
  set Z := Subgroup.centralizer (Y : Set (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  haveI : Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) := Module.finite_of_finite (ZMod I.p)
  -- `Φ` is constant on cosets of `Z`
  have hconst : ∀ u v : Cb, (QuotientGroup.mk u : Cb ⧸ Z.subgroupOf Cb) = QuotientGroup.mk v →
      vsHPhi hs B u = vsHPhi hs B v := by
    intro u v huv
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at huv
    set z := ((u⁻¹ * v : Cb) : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
    have hv : (v : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) = u * z := by
      simp [z]
    unfold vsHPhi
    refine List.map_congr_left fun b hb => ?_
    have hzb : z * vsPRho hs b = vsPRho hs b * z :=
      (Subgroup.mem_centralizer_iff.1 huv _ (hBY b hb)).symm
    have : (v : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) * vsPRho hs b * (↑v)⁻¹ =
        ↑u * vsPRho hs b * (↑u)⁻¹ := by
      rw [hv]
      calc ↑u * z * vsPRho hs b * (↑u * z)⁻¹ = ↑u * (z * vsPRho hs b) * z⁻¹ * (↑u)⁻¹ := by group
        _ = ↑u * vsPRho hs b * (↑u)⁻¹ := by rw [hzb]; group
    rw [this]
  let F : Cb ⧸ Z.subgroupOf Cb → List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :=
    Quotient.lift (fun u : Cb => vsHPhi hs B u) (fun u v h => hconst u v (Quotient.sound h))
  have hsub : vsQOrb (vsHAlT s) cs (B.map (vsHT s)) ⊆ Set.range F := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨QuotientGroup.mk ⟨vsPRho hs g, hCb g hg⟩, ?_⟩
    show vsHPhi hs B (vsPRho hs g) = _
    rw [vsHAlT_eq hs hB (hcs hg)]
  calc (vsQOrb (vsHAlT s) cs (B.map (vsHT s))).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (Cb ⧸ Z.subgroupOf Cb) := by
      rw [← Set.image_univ, ← Set.ncard_univ]
      exact Set.ncard_image_le (Set.toFinite _)
    _ = Z.relIndex Cb := rfl

section

variable [Fact I.p.Prime] {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
  {ys : List (Perm (Fin I.n))} {r : ℕ}

/-- **The `Q₈` case.** With no isotropic element, `r = 2` and the centralizer of `Ȳ` has index at
most `24` in `C̄`. -/
theorem VsHHyp.q8 (h : VsHHyp hs as Lb ys r) (hK0 : (vsHK s Lb r ys).length = 0)
    {ccs : List (Perm (Fin I.n))}
    (hccC : vsPBar hs (gens ccs) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _)) :
    r = 2 ∧ (Subgroup.centralizer (vsHY hs as ys : Set (Module.End (ZMod I.p)
      (Fin (vsQD s) → ZMod I.p))ˣ)).relIndex (vsPBar hs (gens ccs)) ≤ 24 := by
  haveI := vsH_nontrivial h.hard
  obtain ⟨hiso, -⟩ := h.iso
  set K := vsHK s Lb r ys
  have e : K.length = 0 := hK0
  haveI : IsEmpty (Fin K.length) := by rw [e]; infer_instance
  have hiso0 : VsMIso (vsPBar hs (gens as)) (vsHY hs as ys) r
      (Fin.elim0 : Fin 0 → (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) := by
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun y hy hg _ => ?_⟩
    have := hiso.2.2.2.2 y hy hg (fun i => isEmptyElim i)
    rw [Set.range_eq_empty] at this
    rwa [Set.range_eq_empty]
  have hHard := vsM_hard (p := I.p) (V := Fin (vsQD s) → ZMod I.p) _ _ _ r 0 Fin.elim0 h.hard hiso0
  have hr2 : r = 2 := hHard.2.1 rfl
  subst hr2
  refine ⟨rfl, vsM_q8Cent (p := I.p) (V := Fin (vsQD s) → ZMod I.p) _ _ _ _ Fin.elim0 h.hard hiso0
    ?_ hccC⟩
  -- `C̄ ≤ H̄`
  intro u hu
  obtain ⟨x, hx, hxs, rfl⟩ := (vsPBar_mem_iff hs).1 hu
  exact vsPRho_mem_vsPBar hs hxs hxs

end

end GI.Impl
