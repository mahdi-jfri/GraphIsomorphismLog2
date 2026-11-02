import Workspace.Algorithm.Interfaces

/-!
# The faithful action of a state on its domain

A state `S` has a group `G ≤ Sym(Ω)` and an invariant domain `dom ⊆ Ω`. Several proved
lemmas (Lemma 4.1, Lemma A.14, Theorem A.23) are stated for a group acting on a whole
finite type. This file restricts the group of a state to its domain, as a group of
permutations of the subtype `dom` (Section 3: "Every fresh call uses the faithful
permutation image on its own active domain"), and transports subgroups, orbits and the
budget `σ` back to `Ω`.

* `State.domHom`: the restriction `G → Sym(dom)`; `State.domGroup`: its image.
* `State.liftGroup N`: the elements of `G` whose restriction lies in `N ≤ Sym(dom)`.
* `State.orb_liftGroup`: for `N ≤ G|_dom`, the orbits of the lift are the orbits of `N`.
* `State.sigma_liftGroup`: for `N ≤ G|_dom`, `σ(v, lift N) = σ(v, N)` (Lemma A.3:
  `σ` only depends on the faithful action on the orbit).
* `State.domGroup_pretransitive`: a transitive state gives a transitive `G|_dom`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

namespace State

variable {Ω C : Type} (S : State Ω C)

/-- The restriction of the group of a state to its domain. -/
def domHom : S.G →* Perm S.dom := restrictHom S.G S.dom S.dom_inv

/-- The faithful image `G|_dom ≤ Sym(dom)` of the group of a state on its domain. -/
def domGroup : Subgroup (Perm S.dom) := S.domHom.range

/-- The elements of `G` whose restriction to the domain lies in `N`. -/
def liftGroup (N : Subgroup (Perm S.dom)) : Subgroup (Perm Ω) :=
  (N.comap S.domHom).map S.G.subtype

variable {S}

@[simp] theorem domHom_apply (g : S.G) (v : S.dom) : (S.domHom g v : Ω) = (g : Perm Ω) v := rfl

theorem liftGroup_le (N : Subgroup (Perm S.dom)) : S.liftGroup N ≤ S.G :=
  Subgroup.map_subtype_le _

theorem mem_liftGroup {N : Subgroup (Perm S.dom)} {g : Perm Ω} :
    g ∈ S.liftGroup N ↔ ∃ hg : g ∈ S.G, S.domHom ⟨g, hg⟩ ∈ N := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hN⟩
    exact ⟨⟨g, hg⟩, hN, rfl⟩

theorem liftGroup_domGroup : S.liftGroup S.domGroup = S.G := by
  ext g
  rw [mem_liftGroup]
  exact ⟨fun ⟨hg, _⟩ => hg, fun hg => ⟨hg, ⟨_, rfl⟩⟩⟩

/-- For `N ≤ G|_dom`, the orbits of the lift of `N` are the orbits of `N`. -/
theorem orb_liftGroup {N : Subgroup (Perm S.dom)} (hN : N ≤ S.domGroup) {v : Ω}
    (hv : v ∈ S.dom) : orb (S.liftGroup N) v = Subtype.val '' orb N ⟨v, hv⟩ := by
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgG, hgN⟩ := mem_liftGroup.1 hg
    exact ⟨_, ⟨_, hgN, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    obtain ⟨g, hg⟩ := hN hn
    refine ⟨(g : Perm Ω), mem_liftGroup.2 ⟨g.2, by rw [Subtype.coe_eta, hg]; exact hn⟩, ?_⟩
    rw [← hg]
    rfl

theorem card_orb_liftGroup {N : Subgroup (Perm S.dom)} (hN : N ≤ S.domGroup) {v : Ω}
    (hv : v ∈ S.dom) : Nat.card (orb (S.liftGroup N) v) = Nat.card (orb N ⟨v, hv⟩) := by
  rw [orb_liftGroup hN hv, Nat.card_image_of_injective Subtype.val_injective]

/-- The lift of `N` covers the action of `N` at a point of the domain. -/
def liftCover {N : Subgroup (Perm S.dom)} (v : Ω) (hv : v ∈ S.dom) :
    GI.ActionCover (S.liftGroup N) v (⟨v, hv⟩ : S.dom) where
  project := S.domHom.comp (Subgroup.inclusion (liftGroup_le N))
  embed := ⟨Subtype.val, Subtype.val_injective⟩
  base := rfl
  equivariant _ _ := rfl

theorem liftCover_range {N : Subgroup (Perm S.dom)} (hN : N ≤ S.domGroup) (v : Ω)
    (hv : v ∈ S.dom) : (liftCover (N := N) v hv).project.range = N := by
  ext n
  constructor
  · rintro ⟨h, rfl⟩
    exact (mem_liftGroup.1 h.2).2
  · intro hn
    obtain ⟨g, rfl⟩ := hN hn
    exact ⟨⟨(g : Perm Ω), mem_liftGroup.2 ⟨g.2, hn⟩⟩, rfl⟩

/-- **`σ` of a lift** (Lemma A.3: the budget depends only on the faithful action on the
orbit). For `N ≤ G|_dom` and `v` in the domain, `σ(v, lift N) = σ(v, N)`. -/
theorem sigma_liftGroup [Finite Ω] (κ : ℕ) {N : Subgroup (Perm S.dom)} (hN : N ≤ S.domGroup)
    {v : Ω} (hv : v ∈ S.dom) : GI.sigma κ v (S.liftGroup N) = GI.sigma κ ⟨v, hv⟩ N := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  rw [(liftCover v hv).sigma_eq κ, liftCover_range hN]

/-- `σ` of the group of a state at a point of its domain is `σ` of its faithful image. -/
theorem sigma_domGroup [Finite Ω] (κ : ℕ) {v : Ω} (hv : v ∈ S.dom) :
    GI.sigma κ v S.G = GI.sigma κ ⟨v, hv⟩ S.domGroup := by
  rw [← sigma_liftGroup κ le_rfl hv, liftGroup_domGroup]

/-- A transitive state has a transitive faithful image on its domain. -/
theorem domGroup_pretransitive (htr : S.Transitive) :
    MulAction.IsPretransitive S.domGroup S.dom := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg, hgab⟩ := htr a.1 a.2 b.1 b.2
  exact ⟨⟨S.domHom ⟨g, hg⟩, ⟨_, rfl⟩⟩, Subtype.ext hgab⟩

end State

end GI.Algorithm
