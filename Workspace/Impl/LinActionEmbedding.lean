import Workspace.MulticosetPieces
import Mathlib.Logic.Function.Basic

/-! Relabeling implicit objects by an injective equivariant map preserves the
configurations used by A.20, as well as the full transporter. -/
namespace GI.Impl
open GI.Multicoset

variable {G Ω Ψ : Type*} [Group G] [RAct G Ω] [RAct G Ψ]

structure linActEmbedding where
  toFun : Ω → Ψ
  injective : Function.Injective toFun
  act : ∀ (x : Ω) (g : G), toFun (x ↼ g) = toFun x ↼ g

namespace linActEmbedding
variable (e : linActEmbedding (G := G) (Ω := Ω) (Ψ := Ψ))

def map : Multiset Ω →+ Multiset Ψ where
  toFun := Multiset.map e.toFun
  map_zero' := by simp
  map_add' X Y := by simp

theorem map_injective : Function.Injective e.map := Multiset.map_injective e.injective

theorem map_act (X : Multiset Ω) (g : G) : e.map (X ↼ g) = e.map X ↼ g := by
  simp only [map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, multiset_act_def, Multiset.map_map]
  congr 1
  funext x
  exact e.act x g

theorem sameOrb (A : Subgroup G) (x y : Ω) : SameOrb A (e.toFun x) (e.toFun y) ↔ SameOrb A x y := by
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, e.injective (by rw [e.act]; exact he)⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (e.act x a).symm⟩

theorem partAt (A : Subgroup G) (X T : Multiset Ω) :
    partAt A (e.map X) (e.map T) = e.map (partAt A X T) := by
  classical
  simp only [GI.Multicoset.partAt, map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Multiset.filter_map]
  apply congrArg (Multiset.map e.toFun)
  apply Multiset.filter_congr
  intro x hx
  simp only [Function.comp_apply, Multiset.mem_map, exists_exists_and_eq_and]
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, (e.sameOrb A t x).mp he⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, (e.sameOrb A t x).mpr he⟩

open Classical in
theorem pieces (A : Subgroup G) (X : Multiset Ω) :
    pieces A (e.map X) = (pieces A X).image e.map := by
  classical
  ext T
  simp only [mem_pieces, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    refine ⟨GI.Multicoset.partAt A X {x}, ⟨x, hx, rfl⟩, ?_⟩
    have hh := e.partAt A X {x}
    simpa [map] using hh.symm
  · rintro ⟨S, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e.toFun x, Multiset.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    have hh := e.partAt A X {x}
    simpa [map] using hh.symm

/-- Configuration compatibility is unchanged by an injective relabeling. -/
theorem conf (A : Subgroup G) (Y Z : Multiset Ω) :
    Conf A (e.map Y) (e.map Z) ↔ Conf A Y Z := by
  classical
  constructor
  · rintro ⟨w, hw, he⟩
    refine ⟨fun T => w (e.map T), fun T hT => hw _ (by rw [e.pieces]; exact Finset.mem_image.mpr ⟨T, hT, rfl⟩), ?_⟩
    apply e.map_injective
    rw [he, e.pieces, Finset.sum_image (fun T _ U _ he => e.map_injective he)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro T hT
    exact (e.map_act T _).symm
  · rintro ⟨w, hw, he⟩
    let w' := Function.extend e.map w (fun _ => 1)
    have hext (T : Multiset Ω) : w' (e.map T) = w T := e.map_injective.extend_apply _ _ _
    refine ⟨w', ?_, ?_⟩
    · intro T hT
      rw [e.pieces] at hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      rw [hext]
      exact hw S hS
    · rw [he, map_sum, e.pieces, Finset.sum_image (fun T _ U _ he => e.map_injective he)]
      apply Finset.sum_congr rfl
      intro T hT
      rw [hext]
      exact e.map_act T _

theorem iso (H : Subgroup G) (X Y : Multiset Ω) :
    Iso H (e.map X) (e.map Y) = Iso H X Y := by
  ext g
  simp only [mem_iso, ← e.map_act]
  exact and_congr_right (fun _ => e.map_injective.eq_iff)

theorem fixes (N : Subgroup G) (X : Multiset Ω) : Fixes N (e.map X) ↔ Fixes N X := by
  constructor
  · intro h n hn x hx
    apply e.injective
    rw [e.act]
    exact h n hn (e.toFun x) (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h n hn y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    rw [← e.act, h n hn x hx]

end linActEmbedding
end GI.Impl
