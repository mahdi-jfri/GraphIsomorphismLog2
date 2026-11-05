module

public import Workspace.Impl.AggRectRepSupp

@[expose] public section

/-!
# The kernel-orbit quotient from one point

Corollary A.25: "Fix `x ∈ Ω` and compute `P = φ(G_x)`. The stabilizer of the orbit `x^K` in
`G/K` is `KG_x/K = P`." Lemma A.26: "For the ordered action, choose one ordering of `D` at the
base point and transport it using `φ`. This is well defined because the base stabilizer fixes
both entries. … For the unordered action, transport `D` itself."

This file proves the two facts behind this construction and builds the quotient.

* `rcR_stab_map`: for any kernel-orbit quotient `f`, the image of a point stabilizer is the
  stabilizer of `f(x)` (`KG_x/K = φ(G_x)`).
* `rcR_stab_pt`, `rcR_stab_set`, `rcR_stab_one`: so `P = π(G_x)` is the pointwise stabilizer of
  `a, b`, the setwise stabilizer of `{a, b}`, or the stabilizer of `a`, for `f(x) = (a, b)`,
  `{a, b}` or `a`. Its small points (`rcRSmall`, `AggRectRepSupp.lean`) are the support `D`.
* `rcRKqO`: for ordered pairs, the quotient transported from the ordering of `D` in increasing
  order at `x` (`kernelQuotientOfImage`). Its value at `g x` is `(π g d₁, π g d₂)`
  (`rcR_kqO_map`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.StabilizerQuotient GI.Rectangle

/-! ### The stabilizer image -/

section Generic

variable {G Q V W : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q W]

/-- **`KG_x/K = φ(G_x)`**: for a kernel-orbit quotient `f`, the image of the stabilizer of `a` is
the stabilizer of `f(a)`. -/
theorem rcR_stab_map {φ : G →* Q} (onto : Function.Surjective φ) (f : KernelQuotient φ V W)
    (a : V) : (MulAction.stabilizer G a).map φ = MulAction.stabilizer Q (f.map a) := by
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : g • a = a := hg
    show φ g • f.map a = f.map a
    rw [← f.equivariant, hg']
  · intro hs
    have hs' : s • f.map a = f.map a := hs
    obtain ⟨g, rfl⟩ := onto s
    have hf : f.map (g • a) = f.map a := by rw [f.equivariant, hs']
    obtain ⟨k, hk, hka⟩ := (f.kernel_fibers _ _).1 hf
    refine ⟨k * g, ?_, ?_⟩
    · show (k * g) • a = a
      rw [mul_smul, hka]
    · rw [map_mul, hk, one_mul]

end Generic

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- **The label image of a point stabilizer**: `π(G_x)`, as label permutations. -/
def rcRStab (S : State Ω C) (L : GiantLabels S) (x : Ω) : Subgroup (Perm (Fin L.q)) :=
  ((MulAction.stabilizer S.G x).map L.π).map (alternatingGroup (Fin L.q)).subtype

theorem rcR_mem_stab {x : Ω} {σ : Perm (Fin L.q)} :
    σ ∈ rcRStab S L x ↔ ∃ g : S.G, (g : Perm Ω) x = x ∧ ((L.π g : alternatingGroup _) : Perm _) = σ := by
  simp only [rcRStab, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩

section Quot

variable {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)

include hπ in
/-- The label image of the stabilizer of `x` is the image under `πd` of the stabilizer in the
domain action, mapped to label permutations. -/
theorem rcR_stab_eq {x : Ω} (hx : x ∈ S.dom) :
    rcRStab S L x = ((MulAction.stabilizer S.domGroup (⟨x, hx⟩ : S.dom)).map πd).map
      (alternatingGroup (Fin L.q)).subtype := by
  ext σ
  rw [rcR_mem_stab]
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨_, ⟨⟨S.domHom g, g, rfl⟩, Subtype.ext hg, rfl⟩, ?_⟩
    rw [hπ]; rfl
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    obtain ⟨g, rfl⟩ := State.domGroup_elim k
    refine ⟨g, congrArg Subtype.val hk, ?_⟩
    rw [hπ]; rfl

include hπ in
/-- **`π(G_x)` is the stabilizer of `f(x)`**, for a kernel-orbit quotient `f`. -/
theorem rcR_stab_kq {Ξ : Type} [MulAction (alternatingGroup (Fin L.q)) Ξ]
    (f : KernelQuotient πd S.dom Ξ) {x : Ω} (hx : x ∈ S.dom) :
    rcRStab S L x = (MulAction.stabilizer (alternatingGroup (Fin L.q)) (f.map ⟨x, hx⟩)).map
      (alternatingGroup (Fin L.q)).subtype := by
  rw [rcR_stab_eq hπ hx, rcR_stab_map (πd_surjective hπ) f]

include hπ in
/-- Ordered pairs: `π(G_x)` is the pointwise stabilizer of the two entries of `f(x)`. -/
theorem rcR_stab_pt (f : KernelQuotient πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) {x : Ω}
    (hx : x ∈ S.dom) :
    rcRStab S L x = rcRPt (f.map ⟨x, hx⟩).1.1 (f.map ⟨x, hx⟩).1.2 := by
  rw [rcR_stab_kq hπ f hx]
  ext σ
  rw [rcR_mem_pt]
  set p := f.map ⟨x, hx⟩
  constructor
  · rintro ⟨s, hs, rfl⟩
    have := (GI.Pairs.mem_pointwise p.1.1 p.1.2 p.2 s).1 hs
    exact ⟨s.2, this⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨σ, h0⟩, (GI.Pairs.mem_pointwise p.1.1 p.1.2 p.2 ⟨σ, h0⟩).2 ⟨h1, h2⟩, rfl⟩

include hπ in
/-- Unordered pairs: `π(G_x)` is the setwise stabilizer of `f(x) = {a, b}`. -/
theorem rcR_stab_set (f : KernelQuotient πd S.dom (GI.Johnson.SubsetVertex (Fin L.q) 2))
    {x : Ω} (hx : x ∈ S.dom) {a b : Fin L.q} (hab : a ≠ b)
    (hfx : f.map ⟨x, hx⟩ = GI.Pairs.unorderedOfOrdered ⟨(a, b), hab⟩) :
    rcRStab S L x = rcRSet a b := by
  rw [rcR_stab_kq hπ f hx, hfx]
  ext σ
  rw [rcR_mem_set]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, (GI.Pairs.mem_setwise a b hab s).1 hs⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨σ, h0⟩, (GI.Pairs.mem_setwise a b hab ⟨σ, h0⟩).2 h1, rfl⟩

include hπ in
/-- Single labels: `π(G_x)` is the stabilizer of `f(x)`. -/
theorem rcR_stab_one (f : KernelQuotient πd S.dom (Fin L.q)) {x : Ω} (hx : x ∈ S.dom) :
    rcRStab S L x = rcROne (f.map ⟨x, hx⟩) := by
  rw [rcR_stab_kq hπ f hx]
  ext σ
  rw [rcR_mem_one]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨σ, h0⟩, h1, rfl⟩

/-! ### The ordered quotient transported from the increasing order at `x` -/

/-- The ordered pair of two distinct labels in increasing order. -/
def rcROrd {q : ℕ} (p : GI.Pairs.OrderedPair (Fin q)) : GI.Pairs.OrderedPair (Fin q) :=
  if p.1.1 < p.1.2 then p else ⟨(p.1.2, p.1.1), p.2.symm⟩

theorem rcR_ord_stab {q : ℕ} (p : GI.Pairs.OrderedPair (Fin q)) :
    MulAction.stabilizer (alternatingGroup (Fin q)) (rcROrd p) =
      MulAction.stabilizer (alternatingGroup (Fin q)) p := by
  unfold rcROrd
  split_ifs
  · rfl
  · ext s
    have h1 := GI.Pairs.mem_pointwise p.1.2 p.1.1 p.2.symm s
    have h2 := GI.Pairs.mem_pointwise p.1.1 p.1.2 p.2 s
    change s ∈ GI.Pairs.pointwise _ _ _ ↔ s ∈ GI.Pairs.pointwise p.1.1 p.1.2 p.2
    rw [h1, h2, and_comm]

theorem rcR_pair_ord {q : ℕ} (p : GI.Pairs.OrderedPair (Fin q)) :
    rcRPair p.1.1 p.1.2 = [(rcROrd p).1.1, (rcROrd p).1.2] := by
  unfold rcRPair rcROrd
  split_ifs <;> rfl

variable [Finite Ω] (htr : S.Transitive)

include htr in
theorem rcR_source {x : Ω} (hx : x ∈ S.dom) (y : S.dom) :
    ∃ g : S.domGroup, g • (⟨x, hx⟩ : S.dom) = y := by
  haveI := domGroup_pretransitive htr
  exact MulAction.exists_smul_eq S.domGroup _ y

/-- **The ordered quotient of Lemma A.26**, with the entries of `f₀(x)` in increasing order at
`x`. -/
noncomputable def rcRKqO (hq : 4 ≤ L.q)
    (f₀ : KernelQuotient πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) {x : Ω} (hx : x ∈ S.dom) :
    KernelQuotient πd S.dom (GI.Pairs.OrderedPair (Fin L.q)) :=
  kernelQuotientOfImage πd ⟨x, hx⟩ (rcROrd (f₀.map ⟨x, hx⟩)) (πd_surjective hπ)
    (rcR_source htr hx)
    (fun y => GI.Pairs.ordered_transitive (by simpa using hq) _ y)
    (by rw [rcR_ord_stab, rcR_stab_map (πd_surjective hπ) f₀])

include hπ in
/-- **The value of the ordered quotient at `g x`**: `(π g d₁, π g d₂)`. -/
theorem rcR_kqO_map (hq : 4 ≤ L.q)
    (f₀ : KernelQuotient πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) {x : Ω} (hx : x ∈ S.dom)
    (g : S.G) (hy : (g : Perm Ω) x ∈ S.dom) :
    ((rcRKqO hπ htr hq f₀ hx).map ⟨(g : Perm Ω) x, hy⟩).1 =
      ((L.π g : Perm (Fin L.q)) (rcROrd (f₀.map ⟨x, hx⟩)).1.1,
        (L.π g : Perm (Fin L.q)) (rcROrd (f₀.map ⟨x, hx⟩)).1.2) := by
  have e : (⟨(g : Perm Ω) x, hy⟩ : S.dom) =
      (⟨S.domHom g, g, rfl⟩ : S.domGroup) • (⟨x, hx⟩ : S.dom) := Subtype.ext rfl
  rw [e]
  simp only [rcRKqO, kernelQuotientOfImage]
  rw [Data.map_smul_base, hπ]
  rfl

omit [Finite Ω] in
include hπ in
/-- **The value of any quotient at `g x`**: `π g • f(x)`. -/
theorem rcR_kq_map {Ξ : Type} [MulAction (alternatingGroup (Fin L.q)) Ξ]
    (f : KernelQuotient πd S.dom Ξ) {x : Ω} (hx : x ∈ S.dom) (g : S.G)
    (hy : (g : Perm Ω) x ∈ S.dom) :
    f.map ⟨(g : Perm Ω) x, hy⟩ = L.π g • f.map ⟨x, hx⟩ := by
  have e : (⟨(g : Perm Ω) x, hy⟩ : S.dom) =
      (⟨S.domHom g, g, rfl⟩ : S.domGroup) • (⟨x, hx⟩ : S.dom) := Subtype.ext rfl
  rw [e, f.equivariant, hπ]

end Quot

end GI.Impl
