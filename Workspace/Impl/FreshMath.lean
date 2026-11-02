import Workspace.Impl.Reduce

/-!
# The mathematics of the fresh state value

A fresh phase (`Run.fresh`) starts `Continue` on the state `S.freshOn (orbitHier G' M)` on the
type `S.dom`: the group is the image `G' = G|_dom`, the domain is everything, the colorings
are those of `S` read on the domain, `N = |dom|`, `h = 2`, no rows, floor off, and the
hierarchy has one interval from the points to the orbits of `G'`, with ratio and bound the size
`M` of a largest orbit. This file proves what the program needs about it.

* `hier_of_largest`: for a largest orbit `D₁`, `orbitHier G' |D₁|` is an initial tower and
  meets the hierarchy invariant (as in `exists_orbitHier`, with the orbit the program finds).
* `cmpCode`: the color code of the fresh value. `Canon` asks for codes below `2s`, while the
  input codes may be large. The new code of a color is the position of its first occurrence in
  the list `L` of the codes of `x` and `y` on the domain (length `2s`), and `2s + c z` for a
  color that does not occur. It is injective (`cmpCode_injective`), so it is a valid code.
* `canon_fresh`: the fresh value is a canonical value of the fresh state.
* `good_fresh`, `mlt_fresh`: the fresh state may be passed to `Continue` by the induction
  hypothesis.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {Ω C : Type} {k : ℕ}

/-! ### The hierarchy of the orbits -/

/-- **The orbit hierarchy for a given largest orbit.** -/
theorem hier_of_largest [Finite Ω] (G : Subgroup (Perm Ω)) (a : Ω)
    (hmax : ∀ b, Nat.card (orb G b) ≤ Nat.card (orb G a)) :
    InitialTower G Set.univ (orbitHier G (Nat.card (orb G a))) ∧
      GI.Algorithm.HierInv G Set.univ (orbitHier G (Nat.card (orb G a))) := by
  classical
  have haO : a ∈ orb G a := ⟨1, G.one_mem, rfl⟩
  refine ⟨⟨⟨a, trivial, fun b _ => hmax b, ?_⟩, ?_⟩,
    orbitHier_hierInv G (fun _ _ _ => by simp) fun b _ => hmax b⟩
  · refine ⟨fun g hg v w => orbitSetoid_inv G g hg v w, fun v w h => ?_, ?_, fun w hw => hw⟩
    · have : v = w := h
      subst this
      exact (orbitSetoid G).refl v
    · change Nat.card (orb G a) * blockCard (orb G a) a ⊥ = blockCard (orb G a) a (orbitSetoid G)
      rw [blockCard_bot haO, mul_one, blockCard_of_forall (p := orbitSetoid G) fun w hw => hw]
  · intro I hI
    rw [orbitHier, List.mem_singleton] at hI
    subst hI
    rfl

/-- **The hierarchy that a fresh phase stores**: the orbit hierarchy, or no interval when the
largest orbit is a point. An interval of ratio `1` would break `SmallInv` (Section 7.1: "Only
nontrivial interval ratios occur"). -/
def freshHier (G : Subgroup (Perm Ω)) (M : ℕ) : List (Interval Ω) :=
  if M = 1 then [] else orbitHier G M

/-- **The stored hierarchy of a fresh phase** is an initial tower and meets the hierarchy
invariant. When the largest orbit is a point, every orbit is a point, so the empty hierarchy
already ends at the orbits. -/
theorem freshHier_of_largest [Finite Ω] (G : Subgroup (Perm Ω)) (a : Ω)
    (hmax : ∀ b, Nat.card (orb G b) ≤ Nat.card (orb G a)) :
    InitialTower G Set.univ (freshHier G (Nat.card (orb G a))) ∧
      GI.Algorithm.HierInv G Set.univ (freshHier G (Nat.card (orb G a))) := by
  unfold freshHier
  split_ifs with h1
  · -- every orbit is a point
    have hpt : ∀ b w, w ∈ orb G b → b = w := by
      intro b w hw
      have hb : Nat.card (orb G b) ≤ 1 := h1 ▸ hmax b
      have hbb : b ∈ orb G b := ⟨1, G.one_mem, rfl⟩
      haveI : Finite (orb G b) := Subtype.finite
      have := ((Finite.card_le_one_iff_subsingleton (α := orb G b)).1 hb).elim ⟨b, hbb⟩ ⟨w, hw⟩
      exact congrArg Subtype.val this
    refine ⟨⟨⟨a, trivial, fun b _ => hmax b, fun w hw => hpt a w hw⟩, fun I hI => by cases hI⟩,
      ⟨trivial, fun b _ w _ hw => hpt b w hw, trivial⟩⟩
  · exact hier_of_largest G a hmax

/-- The number of ones of the indicator of a set is its size. -/
theorem count_indF (e : Ω ≃ Fin k) (D : Set Ω) :
    ((List.finRange k).map (indF e D)).count 1 = Nat.card D := by
  classical
  rw [count_map_finRange, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun j => ⟨e.symm j.1, ?_⟩, fun w => ⟨e w.1, ?_⟩, fun j => ?_, fun w => ?_⟩
  · have := j.2
    simp only [indF] at this
    split_ifs at this with h
    · exact h
  · simp [indF, w.2]
  · simp
  · simp

/-! ### The color code -/

/-- The color code of the fresh value (see the module docstring). -/
def cmpCode (c : C → ℕ) (L : List ℕ) (s : ℕ) (z : C) : ℕ :=
  if c z ∈ L then posOf L (c z) else 2 * s + c z

theorem cmpCode_of_mem {c : C → ℕ} {L : List ℕ} {s : ℕ} {z : C} (h : c z ∈ L) :
    cmpCode c L s z = posOf L (c z) := if_pos h

theorem cmpCode_injective {c : C → ℕ} (hc : Function.Injective c) {L : List ℕ} {s : ℕ}
    (hL : L.length ≤ 2 * s) : Function.Injective (cmpCode c L s) := by
  intro z w h
  unfold cmpCode at h
  by_cases hz : c z ∈ L <;> by_cases hw : c w ∈ L <;> simp only [hz, hw, if_true, if_false] at h
  · apply hc
    have h1 := getElem_posOf hz
    have h2 := getElem_posOf hw
    simp only [h] at h1
    exact h1.symm.trans h2
  · have := posOf_lt hz; omega
  · have := posOf_lt hw; omega
  · exact hc (by omega)

/-! ### The fresh state -/

section Fresh

variable (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)

/-- The codes of a coloring on the domain, in the order of the domain positions. -/
noncomputable def domCodes (x : Ω → C) : List ℕ := (domFin e S.dom).map fun p => c (x (e.symm p))

/-- The list `L` of the codes of `x` and `y` on the domain. -/
noncomputable def codeList : List ℕ := domCodes e c S S.x ++ domCodes e c S S.y

theorem length_codeList : (codeList e c S).length = 2 * (domFin e S.dom).length := by
  simp [codeList, domCodes]; ring

/-- The fresh color code. -/
noncomputable def freshCode : C → ℕ := cmpCode c (codeList e c S) (domFin e S.dom).length

theorem freshCode_injective (hc : Function.Injective c) : Function.Injective (freshCode e c S) :=
  cmpCode_injective hc (length_codeList e c S).le

/-- The compressed codes of a coloring on the domain. -/
noncomputable def cmpCodes (x : Ω → C) : List ℕ := (domCodes e c S x).map (posOf (codeList e c S))

/-- The colors of the fresh state, with the fresh code. -/
theorem colorVal_fresh {x : Ω → C} (hx : ∀ p ∈ domFin e S.dom, c (x (e.symm p)) ∈ codeList e c S) :
    ColorVal (domEquiv e S.dom) (freshCode e c S) (natList (cmpCodes e c S x))
      (x ∘ Subtype.val) := by
  unfold ColorVal
  simp only [encFun, natList, cmpCodes, domCodes, List.map_map]
  rw [← map_finRange_getElem (domFin e S.dom)]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, domEquiv_symm_apply, freshCode]
  exact congrArg Val.nat (cmpCode_of_mem (hx _ (List.getElem_mem _))).symm

theorem mem_codeList_x (p : Fin k) (hp : p ∈ domFin e S.dom) :
    c (S.x (e.symm p)) ∈ codeList e c S :=
  List.mem_append_left _ (List.mem_map_of_mem hp)

theorem mem_codeList_y (p : Fin k) (hp : p ∈ domFin e S.dom) :
    c (S.y (e.symm p)) ∈ codeList e c S :=
  List.mem_append_right _ (List.mem_map_of_mem hp)

/-- The fresh codes of the colors on the domain are below `2s`. -/
theorem freshCode_lt {x : Ω → C} (a : S.dom) (ha : c (x a) ∈ codeList e c S) :
    freshCode e c S (x a) < 2 * (domFin e S.dom).length := by
  rw [freshCode, cmpCode_of_mem ha, ← length_codeList e c S]
  exact posOf_lt ha

theorem mem_codeList_of_dom_x (a : S.dom) : c (S.x a) ∈ codeList e c S := by
  have hp : e a ∈ domFin e S.dom := mem_domFin.2 (by simp)
  simpa using mem_codeList_x e c S (e a) hp

theorem mem_codeList_of_dom_y (a : S.dom) : c (S.y a) ∈ codeList e c S := by
  have hp : e a ∈ domFin e S.dom := mem_domFin.2 (by simp)
  simpa using mem_codeList_y e c S (e a) hp

/-- The value of the hierarchy `orbitHier G' M`: one interval `[labels, M, M, 0]`. -/
def hierVal (labv : Val) (M : ℕ) : Val := .list [.list [labv, .nat M, .nat M, .nat 0]]

/-- The value of the stored fresh hierarchy `freshHier G' M`. -/
def fhierVal (labv : Val) (M : ℕ) : Val := if M = 1 then .list [] else hierVal labv M

theorem wt_fhierVal_le (labv : Val) (M : ℕ) : (fhierVal labv M).wt ≤ (hierVal labv M).wt := by
  unfold fhierVal
  split_ifs
  · have := wt_list1_le (Val.list [labv, .nat M, .nat M, .nat 0])
    simp only [hierVal]
    have h4 : (Val.list []).wt = 4 := by simp
    have := wt_le_wt_list (vs := [Val.list [labv, .nat M, .nat M, .nat 0]])
      (v := Val.list [labv, .nat M, .nat M, .nat 0]) (by simp)
    have h5 : 4 ≤ (Val.list [labv, Val.nat M, Val.nat M, Val.nat 0]).wt := by
      have := length_lt_wt_list [labv, Val.nat M, Val.nat M, Val.nat 0]
      simp at this; omega
    omega
  · exact le_rfl

/-- **The fresh state value**: `[s, group, ones, x', y', hier, [], 0, 2, s]`. -/
def freshVal (s : ℕ) (gv xv yv hv : Val) : Val :=
  .list [.nat s, gv, .list (List.replicate s (.nat 1)), xv, yv, hv, .list [], .nat 0, .nat 2,
    .nat s]

theorem domVal_univ (e' : Ω ≃ Fin k) : DomVal e' (.list (List.replicate k (.nat 1))) Set.univ := by
  unfold DomVal
  simp only [encFun, Set.mem_univ, if_true]
  rw [List.map_const', List.length_finRange]

/-- **The fresh value is a canonical value of the fresh state.** -/
theorem canon_fresh (hs : List (Perm (Fin (domFin e S.dom).length)))
    (hg : gens hs = groupFin (domEquiv e S.dom) S.domGroup)
    (hl : hs.length ≤ (domFin e S.dom).length ^ 2) (lab : Fin (domFin e S.dom).length → ℕ)
    (hlab : ∀ i j, lab i = lab j ↔
      (orbitSetoid S.domGroup).r ((domEquiv e S.dom).symm i) ((domEquiv e S.dom).symm j))
    (hlab' : ∀ i, lab i < (domFin e S.dom).length) (M : ℕ) (hM1 : 1 ≤ M)
    (hM : M ≤ S.size) :
    Canon (domEquiv e S.dom) (freshCode e c S)
      (freshVal (domFin e S.dom).length (encGroup hs) (natList (cmpCodes e c S S.x))
        (natList (cmpCodes e c S S.y)) (fhierVal (encFun lab) M))
      (S.freshOn (freshHier S.domGroup M)) where
  val := by
    have hh : HierValC (domEquiv e S.dom) (fhierVal (encFun lab) M) (freshHier S.domGroup M) := by
      unfold fhierVal freshHier
      split_ifs
      · exact ⟨[], rfl, List.Forall₂.nil⟩
      · exact ⟨_, rfl, List.Forall₂.cons ⟨encFun lab, ⟨lab, rfl, hlab', hlab⟩, rfl⟩
          List.Forall₂.nil⟩
    refine ⟨encGroup hs, _, _, _, _, _, ⟨hs, rfl, hg, hl⟩, domVal_univ _,
      colorVal_fresh e c S fun p hp => mem_codeList_x e c S p hp,
      colorVal_fresh e c S fun p hp => mem_codeList_y e c S p hp, hh, rfl, ?_⟩
    have hN : (S.freshOn (freshHier S.domGroup M)).N = (domFin e S.dom).length :=
      card_dom_eq e S.dom
    simp only [freshVal, hN]
    rfl
  colors a := ⟨freshCode_lt e c S a (mem_codeList_of_dom_x e c S a),
    freshCode_lt e c S a (mem_codeList_of_dom_y e c S a)⟩
  fits := (card_dom_eq e S.dom).ge
  small := by
    by_cases h1 : M = 1
    · exact smallInv_nil (by simp [State.freshOn, freshHier, h1]) fun R hR => by cases hR
    · refine smallInv_fresh (I := ⟨orbitSetoid S.domGroup, M, M, 0⟩)
        (by simp [State.freshOn, freshHier, h1, orbitHier]) (show 2 ≤ M by omega) hM hM
        (Nat.zero_le _) fun R hR => by cases hR

/-- The fresh state may be passed to `Continue`. -/
theorem good_fresh (hs : P₀.N₀ < S.size) {l : List (Interval S.dom)}
    (hT : InitialTower S.domGroup Set.univ l)
    (hH : GI.Algorithm.HierInv S.domGroup Set.univ l) :
    Good P₀ .cont (S.freshOn l) := by
  have hS' := S.freshOn_freshOf hT hH
  exact ⟨hs, hS'.size_eq.le, hS'.hierInv⟩

theorem mlt_fresh (l : List (Interval S.dom)) :
    MLt (measure P₀ .cont (S.freshOn l)) (measure P₀ .solve S) := by
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd]
  have : (S.freshOn l).N = S.size := rfl
  omega

end Fresh

end GI.Impl
