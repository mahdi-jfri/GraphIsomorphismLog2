module

public import Workspace.ComponentLocalization
public import Workspace.QuotientImage

@[expose] public section

namespace GI.CartesianCover

variable {I D : Type*} [Fintype I] [Fintype D]
variable {H L : Subgroup (Equiv.Perm (I → D))}

omit [Fintype I] [Fintype D] in
theorem pointStabilizer_onto {v : I → D} {k : ℕ} (s : VisibleStep v H L k) :
    Function.Surjective (s.quotient.comp (pointStabilizer H v).subtype) := by
  intro z
  obtain ⟨h, hz⟩ := s.onto z
  obtain ⟨l, hl⟩ := s.transitiveKernel h
  let n := Subgroup.inclusion s.lower l
  have hn : s.quotient n = 1 := (s.kernel n).mpr l.property
  have hm : ((n⁻¹ * h : H) : Equiv.Perm (I → D)) v = v := by
    change (l : Equiv.Perm (I → D))⁻¹ ((h : Equiv.Perm (I → D)) v) = v
    rw [← hl]
    exact (l : Equiv.Perm (I → D)).symm_apply_apply v
  refine ⟨⟨n⁻¹ * h, hm⟩, ?_⟩
  change s.quotient (n⁻¹ * h) = z
  rw [map_mul, map_inv, hn, inv_one, one_mul]
  exact hz

/-- One actual Cartesian mark is charged either to the position images of
the tuple stabilizers or to one fixed coordinate's actual component image. -/
theorem visible_step_split {v : I → D} {k : ℕ}
    [IsSimpleGroup (alternatingGroup (Fin k))]
    (nonabelian : ∃ s t : alternatingGroup (Fin k), s * t ≠ t * s)
    (c : CartesianCover H) (s : VisibleStep v H L k) :
    Nonempty (AlternatingQuotientStep (c.rowProject v).range
      ((c.restrict s.lower).rowProject v).range k) ∨
    ∃ i : I, Nonempty (VisibleStep (v i) (c.component i).range
      ((c.restrict s.lower).component i).range k) := by
  let R := pointStabilizer H v
  let q := s.quotient.comp R.subtype
  let Kv := (c.rowProject v).ker
  have hq : Function.Surjective q := pointStabilizer_onto s
  rcases ((inferInstance : Kv.Normal).map q hq).eq_bot_or_eq_top with hbot | htop
  · left
    let N := (L.comap H.subtype).comap R.subtype
    have hk : ∀ h : R, q h = 1 ↔ h ∈ N := fun h => s.kernel h.val
    have hkilled : (c.rowProject v).ker ≤ q.ker := by
      intro h hh
      have hm : q h ∈ Kv.map q := Subgroup.mem_map_of_mem q hh
      simpa only [hbot, Subgroup.mem_bot, MonoidHom.mem_ker] using hm
    have z := QuotientImage.step (c.rowProject v) q N hq hk hkilled
    change AlternatingQuotientStep (c.rowProject v).range
      (((L.comap H.subtype).comap R.subtype).map (c.rowProject v)) k at z
    rw [c.restrict_row_range s.lower v] at z
    exact ⟨z⟩
  · right
    have hKv : Function.Surjective (q.comp Kv.subtype) := by
      intro z
      have hz : z ∈ Kv.map q := by rw [htop]; exact Subgroup.mem_top z
      obtain ⟨u, hu, huz⟩ := hz
      exact ⟨⟨u, hu⟩, huz⟩
    have hK : Function.Surjective (s.quotient.comp c.positions.ker.subtype) := by
      intro z
      obtain ⟨u, hu⟩ := hKv z
      exact ⟨⟨u.val.val, u.property⟩, hu⟩
    have htrans : ∀ h : H, ∃ n : H, s.quotient n = 1 ∧ n • v = h • v := by
      intro h
      obtain ⟨l, hl⟩ := s.transitiveKernel h
      exact ⟨Subgroup.inclusion s.lower l, (s.kernel _).mpr l.property, hl⟩
    obtain ⟨i, hi⟩ := c.exists_component_kernel_killed s.quotient hK nonabelian v
      htrans s.visible
    refine ⟨i, ?_⟩
    let C := coordinateStabilizer c.positions i
    let qi := s.quotient.comp C.subtype
    let N := (L.comap H.subtype).comap C.subtype
    have hqi : Function.Surjective qi := by
      intro z
      obtain ⟨u, hu⟩ := hK z
      exact ⟨c.kernelCoordinate i u, hu⟩
    have hkernel : ∀ h : C, qi h = 1 ↔ h ∈ N := fun h => s.kernel h.val
    have hvisible : ∀ h : C,
        (∀ g : C, c.component i h (c.component i g (v i)) = c.component i g (v i)) →
        qi h = 1 := by
      intro h hh
      exact c.component_visible_of_kernel s.quotient hK nonabelian v i hi h hh
    have htransitive : ∀ h : C, ∃ n : N,
        c.component i n (v i) = c.component i h (v i) := by
      intro h
      obtain ⟨u, hu⟩ := hKv (qi h)
      let uk : c.positions.ker := ⟨u.val.val, u.property⟩
      let ui : C := c.kernelCoordinate i uk
      have hui : s.quotient ui.val = s.quotient h.val := hu
      have hufix : c.component i ui (v i) = v i := by
        rw [c.equivariant]
        have hp : ((u.val.val : H) : Equiv.Perm (I → D)) v = v := u.val.property
        exact congrArg (fun x : I → D => x i) hp
      have huinv : (c.component i ui)⁻¹ (v i) = v i := by
        have he := congrArg (fun x => (c.component i ui)⁻¹ x) hufix
        simpa using he.symm
      let n : C := h * ui⁻¹
      have hn : s.quotient n.val = 1 := by
        change s.quotient (h.val * ui.val⁻¹) = 1
        rw [map_mul, map_inv, hui, mul_inv_cancel]
      refine ⟨⟨n, (s.kernel n.val).mp hn⟩, ?_⟩
      change c.component i (h * ui⁻¹) (v i) = c.component i h (v i)
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, huinv]
    have z := VisibleImage.step (c.component i) qi N hqi hkernel (v i) htransitive hvisible
    change VisibleStep (v i) (c.component i).range
      (((L.comap H.subtype).comap C.subtype).map (c.component i)) k at z
    rw [c.restrict_component_range s.lower i] at z
    exact ⟨z⟩

end GI.CartesianCover
