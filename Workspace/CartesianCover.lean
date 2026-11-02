import Workspace.ActionOrbitKernel
import Workspace.BlockChain

namespace GI

variable {I D : Type*}

def coordinateStabilizer {H : Subgroup (Equiv.Perm (I → D))}
    (p : H →* Equiv.Perm I) (i : I) : Subgroup H :=
  (MulAction.stabilizer (Equiv.Perm I) i).comap p

/-- Actual position and component permutation representations of a Cartesian
action. The evaluation law does not assert independence of coordinates. -/
structure CartesianCover (H : Subgroup (Equiv.Perm (I → D))) where
  positions : H →* Equiv.Perm I
  component : ∀ i : I, coordinateStabilizer positions i →* Equiv.Perm D
  equivariant : ∀ (i : I) (h : coordinateStabilizer positions i) (x : I → D),
    component i h (x i) = ((h.val : Equiv.Perm (I → D)) x) i

namespace CartesianCover

variable {H L : Subgroup (Equiv.Perm (I → D))}

def coordinateInclusion (c : CartesianCover H) (hle : L ≤ H) (i : I) :
    coordinateStabilizer (c.positions.comp (Subgroup.inclusion hle)) i →*
      coordinateStabilizer c.positions i where
  toFun h := ⟨Subgroup.inclusion hle h.val, h.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def restrict (c : CartesianCover H) (hle : L ≤ H) : CartesianCover L where
  positions := c.positions.comp (Subgroup.inclusion hle)
  component i := (c.component i).comp (c.coordinateInclusion hle i)
  equivariant i h x := c.equivariant i (c.coordinateInclusion hle i h) x

theorem restrict_component_range_le (c : CartesianCover H) (hle : L ≤ H) (i : I) :
    ((c.restrict hle).component i).range ≤ (c.component i).range := by
  rintro p ⟨l, rfl⟩
  exact ⟨c.coordinateInclusion hle i l, rfl⟩

def pointStabilizer (H : Subgroup (Equiv.Perm (I → D))) (v : I → D) : Subgroup H :=
  (MulAction.stabilizer (Equiv.Perm (I → D)) v).comap H.subtype

def rowProject (c : CartesianCover H) (v : I → D) :
    pointStabilizer H v →* Equiv.Perm I :=
  c.positions.comp (pointStabilizer H v).subtype

def pointInclusion (hle : L ≤ H) (v : I → D) :
    pointStabilizer L v →* pointStabilizer H v where
  toFun l := ⟨Subgroup.inclusion hle l.val, l.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrict_row_range_le (c : CartesianCover H) (hle : L ≤ H) (v : I → D) :
    ((c.restrict hle).rowProject v).range ≤ (c.rowProject v).range := by
  rintro p ⟨l, rfl⟩
  exact ⟨pointInclusion hle v l, rfl⟩

def kernelCoordinate (c : CartesianCover H) (i : I) :
    c.positions.ker →* coordinateStabilizer c.positions i where
  toFun k := ⟨k.val, by
    change c.positions k.val i = i
    have hk : c.positions k.val = 1 := k.property
    rw [hk]
    rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def kernelComponent (c : CartesianCover H) (i : I) : c.positions.ker →* Equiv.Perm D :=
  (c.component i).comp (c.kernelCoordinate i)

theorem kernelComponent_apply (c : CartesianCover H) (i : I)
    (k : c.positions.ker) (x : I → D) :
    c.kernelComponent i k (x i) = ((k.val : Equiv.Perm (I → D)) x) i :=
  c.equivariant i (c.kernelCoordinate i k) x

theorem restrict_component_range (c : CartesianCover H) (hle : L ≤ H) (i : I) :
    ((L.comap H.subtype).comap (coordinateStabilizer c.positions i).subtype).map
      (c.component i) = ((c.restrict hle).component i).range := by
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨⟨h.val, hh⟩, h.property⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨c.coordinateInclusion hle i l, l.val.property, rfl⟩

theorem restrict_row_range (c : CartesianCover H) (hle : L ≤ H) (v : I → D) :
    ((L.comap H.subtype).comap (pointStabilizer H v).subtype).map
      (c.rowProject v) = ((c.restrict hle).rowProject v).range := by
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨⟨h.val, hh⟩, h.property⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨pointInclusion hle v l, l.val.property, rfl⟩

end CartesianCover

end GI
