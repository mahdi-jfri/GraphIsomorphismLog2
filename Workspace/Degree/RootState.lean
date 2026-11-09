module

public import Workspace.Degree.Reset
public import Workspace.Impl.FreshMath

@[expose] public section

/-!
# The root state

The root starts as a fresh phase of the general algorithm: the faithful image on the domain, with
`N = s` and the orbit hierarchy `freshHier`. That hierarchy has one interval, of cap `M`, the size
of a largest orbit. The recursion needs caps at most `D` (`DGood`). So the root clamps the cap to
`min M D`. The cap `D` is valid because every alternating section `Alt(t)`, `t ≥ 5`, of a group in
`Γ̂_D` has `t ≤ D` (`GammaHat.le_of_alternating_section`).

Main results, for `rootState S D a`:

* `rootState_dGood`: the invariant of the recursion;
* `canon_root`: the clamped fresh value is canonical;
* `liftAnswer_root`: the lift of its answer is the answer of `S`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type}

/-- An interval with its cap clamped to `D`. -/
def clampIv (D : ℕ) (I : Interval Ω) : Interval Ω := ⟨I.part, I.ratio, min I.cap D, I.origin⟩

/-- **A cap of `D` is valid** in a group of `Γ̂_D`. -/
theorem capAt_of_gammaHat {G : Subgroup (Perm Ω)} {D : ℕ} (hG : GammaHat D G) (Dm : Set Ω)
    (f c : Setoid Ω) (a : Ω) : CapAt G Dm f c D a := by
  intro U hU _ t ht φ hφ _
  let A : Subgroup G := U.subgroupOf G
  let ι : A ≃* U := Subgroup.subgroupOfEquivOfLe hU
  exact hG.le_of_alternating_section ht A (φ.comp ι.toMonoidHom) (hφ.comp ι.surjective)

theorem caps_clamp {G : Subgroup (Perm Ω)} {Dm : Set Ω} {D : ℕ} (hG : GammaHat D G) :
    ∀ {f : Setoid Ω} {l : List (Interval Ω)}, Caps G Dm f l → Caps G Dm f (l.map (clampIv D))
  | _, [], _ => trivial
  | f, I :: l, ⟨h1, h2⟩ =>
    ⟨fun a ha => (h1 a ha).min (capAt_of_gammaHat hG Dm f I.part a), caps_clamp hG h2⟩

theorem capsBelow_clamp (D : ℕ) : ∀ l : List (Interval Ω), CapsBelow l (l.map (clampIv D))
  | [] => List.Forall₂.nil
  | _ :: l => List.Forall₂.cons ⟨rfl, rfl, min_le_left _ _⟩ (capsBelow_clamp D l)

/-- The hierarchy of the root state, for a point `a` of a largest orbit. -/
noncomputable def rootHier (S : State Ω C) (D : ℕ) (a : S.dom) : List (Interval S.dom) :=
  (freshHier S.domGroup (Nat.card (orb S.domGroup a))).map (clampIv D)

/-- **The root state.** -/
noncomputable def rootState (S : State Ω C) (D : ℕ) (a : S.dom) : State S.dom C :=
  S.freshOn (rootHier S D a)

variable (S : State Ω C) (D : ℕ) (a : S.dom)

theorem rootState_size : (rootState S D a).size = S.size := by
  unfold State.size
  exact Nat.card_congr (Equiv.Set.univ _)

theorem gammaHat_domGroup {D : ℕ} (h : GammaHat D S.G) : GammaHat D S.domGroup :=
  GammaHat.of_surjective (G := S.G) (H := S.domGroup) S.domHom.rangeRestrict
    S.domHom.rangeRestrict_surjective h

theorem rootState_hierInv [Finite Ω] (hG : GammaHat D S.G)
    (hmax : ∀ b, Nat.card (orb S.domGroup b) ≤ Nat.card (orb S.domGroup a)) :
    (rootState S D a).HierInv := by
  obtain ⟨-, h⟩ := freshHier_of_largest S.domGroup a hmax
  exact (capsBelow_clamp D _).hierInv h (caps_clamp (gammaHat_domGroup S hG) h.caps)

/-- **The invariant of the recursion** at the root. -/
theorem rootState_dGood [Finite Ω] {Nm : ℕ} (hG : GammaHat D S.G)
    (hmax : ∀ b, Nat.card (orb S.domGroup b) ≤ Nat.card (orb S.domGroup a))
    (hN : P₀.N₀ < S.size) (hNm : S.size ≤ Nm) : DGood D Nm (rootState S D a) := by
  refine ⟨inferInstance, hN, hNm, (rootState_size S D a).le, rootState_hierInv S D a hG hmax, rfl,
    rfl, rfl, ?_, gammaHat_domGroup S hG⟩
  intro I hI
  obtain ⟨J, -, rfl⟩ := List.mem_map.1 hI
  exact min_le_right _ _

/-- The lift of the answer of the root state is the answer of `S`. -/
theorem liftAnswer_root : S.liftAnswer (rootState S D a).answer = S.answer := by
  unfold State.liftAnswer State.answer
  change {g | ∃ hg : g ∈ S.G, S.domHom ⟨g, hg⟩ ∈
    answer S.domGroup Set.univ (S.x ∘ Subtype.val) (S.y ∘ Subtype.val)} = _
  rw [answer_restrict_image S.G S.dom S.dom_inv S.x S.y]
  rfl

/-- The value of the clamped hierarchy. -/
def clampHierVal (labv : Val) (M D : ℕ) : Val :=
  if M = 1 then .list [] else .list [.list [labv, .nat M, .nat (min M D), .nat 0]]

theorem hierValC_clamp {k : ℕ} {e' : S.dom ≃ Fin k} {labv : Val}
    (h : HierValC e' (fhierVal labv (Nat.card (orb S.domGroup a)))
      (freshHier S.domGroup (Nat.card (orb S.domGroup a)))) :
    HierValC e' (clampHierVal labv (Nat.card (orb S.domGroup a)) D) (rootHier S D a) := by
  unfold rootHier clampHierVal
  unfold fhierVal freshHier at h
  unfold freshHier
  by_cases h1 : Nat.card (orb S.domGroup a) = 1
  · simp only [h1, if_true, List.map_nil]
    exact ⟨[], rfl, List.Forall₂.nil⟩
  · simp only [h1, if_false] at h ⊢
    obtain ⟨vs, hvs, hf⟩ := h
    simp only [hierVal, Val.list.injEq] at hvs
    subst hvs
    simp only [orbitHier, List.map_cons, List.map_nil] at hf ⊢
    obtain ⟨⟨pv, hp, hpe⟩, -⟩ := List.forall₂_cons.1 hf
    simp only [Val.list.injEq, List.cons.injEq] at hpe
    obtain ⟨rfl, -⟩ := hpe
    exact ⟨_, rfl, List.Forall₂.cons ⟨_, hp, rfl⟩ List.Forall₂.nil⟩

/-- **The clamped fresh value is canonical.** -/
theorem canon_root {s : ℕ} {gv xv yv labv : Val} {c' : C → ℕ} {e' : S.dom ≃ Fin s}
    (h₀ : GI.Impl.Canon e' c' (freshVal s gv xv yv (fhierVal labv (Nat.card (orb S.domGroup a))))
      (S.freshOn (freshHier S.domGroup (Nat.card (orb S.domGroup a))))) :
    GI.Impl.Canon e' c' (freshVal s gv xv yv (clampHierVal labv (Nat.card (orb S.domGroup a)) D))
      (rootState S D a) where
  val := by
    obtain ⟨g', d', x', y', h', r', hg, hd, hx, hy, hh, -, hE⟩ := h₀.val
    simp only [freshVal, Val.list.injEq, List.cons.injEq, and_true] at hE
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -, -, -, hN⟩ := hE
    refine ⟨_, _, _, _, _, _, hg, hd, hx, hy, hierValC_clamp S D a hh, rfl, ?_⟩
    simp only [freshVal]
    rw [hN]
    rfl
  colors := h₀.colors
  fits := h₀.fits
  small := by
    obtain ⟨h1, h2, h3⟩ := h₀.small
    refine ⟨fun I hI => ?_, ?_, h3⟩
    · obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hI
      obtain ⟨j1, j2, j3, j4⟩ := h1 J hJ
      exact ⟨j1, j2, (min_le_left _ _).trans j3, j4⟩
    · have e : rhoNat (rootHier S D a) =
          rhoNat (freshHier S.domGroup (Nat.card (orb S.domGroup a))) := by
        unfold rootHier rhoNat
        rw [List.map_map]
        rfl
      change rhoNat (rootHier S D a) ≤ S.size
      rw [e]
      exact h2

end GI.Degree
