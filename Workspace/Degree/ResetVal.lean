module

public import Workspace.Degree.Reset
public import Workspace.Impl.Fresh

@[expose] public section

/-!
# The canonical value of the reset state

The reset state has the group, colors and domain of a fresh phase, so `prep_spec` of the general
algorithm gives all of its value but the hierarchy. This file gives the hierarchy: an interval
`[pv, ratio, cap, origin]` becomes `[pv', min(ratio, s), min(cap, min(ratio, s)), min(origin, s)]`.
Here `pv'` lists, for each point of the domain, the first position in the domain with the same label
of `pv`. So the labels stay below `s`, as `PartitionValC` asks.

* `relab`: the new labels.
* `canon_reset`: the value is canonical.
* `liftAnswer_reset`: the lift of the answer of the reset state is the answer of `T`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

variable {Ω C : Type} {k : ℕ}

/-- The labels of a partition at the points of the domain, in the order of the domain. -/
noncomputable def domLabs (P : List ℕ) (labs : List ℕ) : List ℕ := P.map fun i => labs.getD i 0

/-- The new labels: each point gets the first position with the same old label. -/
noncomputable def relab (P : List ℕ) (labs : List ℕ) : List ℕ :=
  (domLabs P labs).map (posOf (domLabs P labs))

/-- An interval value, as data. -/
abbrev IvData := List ℕ × ℕ × ℕ × ℕ

/-- The value of an interval. -/
def ivEnc (a : IvData) : Val := .list [natList a.1, .nat a.2.1, .nat a.2.2.1, .nat a.2.2.2]

/-- The value of the reset interval. -/
noncomputable def ivReset (P : List ℕ) (s : ℕ) (a : IvData) : Val :=
  .list [natList (relab P a.1), .nat (min a.2.1 s), .nat (min a.2.2.1 (min a.2.1 s)),
    .nat (min a.2.2.2 s)]

theorem ivEnc_injective : Function.Injective ivEnc := by
  rintro ⟨l, r, c, o⟩ ⟨l', r', c', o'⟩ h
  simp only [ivEnc, natList, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
  obtain ⟨h1, rfl, rfl, rfl⟩ := h
  have : l = l' := List.map_injective_iff.2 (fun a b h => by simpa using h) h1
  subst this
  rfl

section Reset

variable (e : Ω ≃ Fin k) {D : Set Ω}

theorem domLabs_encFun (lab : Fin k → ℕ) :
    domLabs (domNat e D) ((List.finRange k).map lab) = (domFin e D).map lab := by
  unfold domLabs
  rw [domNat, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [p.isLt]

/-- **The new labels stand for the partition on the domain.** -/
theorem partitionValC_relab {lab : Fin k → ℕ} {R : Setoid Ω}
    (h : ∀ i j, lab i = lab j ↔ R.r (e.symm i) (e.symm j)) :
    PartitionValC (domEquiv e D) (natList (relab (domNat e D) ((List.finRange k).map lab)))
      (Setoid.comap Subtype.val R) := by
  set L := (domFin e D).map lab with hL
  have hlen : L.length = (domFin e D).length := by simp [hL]
  have hrel : relab (domNat e D) ((List.finRange k).map lab) = L.map (posOf L) := by
    unfold relab
    rw [domLabs_encFun]
  have hget : ∀ i : Fin (domFin e D).length, L[i.1]'(by omega) = lab (domFin e D)[i.1] := by
    intro i
    simp [hL]
  refine ⟨fun i => posOf L (L[i.1]'(by omega)), ?_, ?_, ?_⟩
  · rw [hrel]
    simp only [natList, encFun, List.map_map]
    congr 1
    apply List.ext_getElem (by simp [hL])
    intro i h1 h2
    simp only [List.getElem_map, Function.comp_apply, List.getElem_finRange]
    rfl
  · intro i
    have := posOf_lt (List.getElem_mem (l := L) (n := i.1) (by omega))
    change posOf L (L[i.1]'(by omega)) < _
    omega
  · intro i j
    have hi := getElem_posOf (List.getElem_mem (l := L) (n := i.1) (by omega))
    have hj := getElem_posOf (List.getElem_mem (l := L) (n := j.1) (by omega))
    constructor
    · intro he
      have h1 : L[i.1]'(by omega) = L[j.1]'(by omega) := by
        have h2 := hi
        simp only [he] at h2
        exact h2.symm.trans hj
      rw [hget, hget] at h1
      exact (h _ _).1 h1
    · intro hr
      have h1 : lab (domFin e D)[i.1] = lab (domFin e D)[j.1] := (h _ _).2 hr
      have h2 : L[i.1]'(by omega) = L[j.1]'(by omega) := by rw [hget, hget, h1]
      simp only [h2]

end Reset

section State

variable (e : Ω ≃ Fin k) (c : C → ℕ) (T : State Ω C)

/-- The data of a hierarchy value: `vs` lists the intervals of `l`. -/
theorem exists_ivData {l : List (Interval Ω)} {vs : List Val}
    (h : List.Forall₂ (IntervalValC e) vs l) :
    ∃ xs : List IvData, vs = xs.map ivEnc ∧ List.Forall₂ (fun a I =>
      (∃ lab : Fin k → ℕ, a.1 = (List.finRange k).map lab ∧ (∀ i, lab i < k) ∧
        ∀ i j, lab i = lab j ↔ I.part.r (e.symm i) (e.symm j)) ∧
      a.2 = (I.ratio, I.cap, I.origin)) xs l := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons v I vs l hv _ ih =>
    obtain ⟨xs, rfl, hxs⟩ := ih
    obtain ⟨pv, ⟨lab, rfl, hl, hr⟩, rfl⟩ := hv
    refine ⟨((List.finRange k).map lab, I.ratio, I.cap, I.origin) :: xs, ?_,
      .cons ⟨⟨lab, rfl, hl, hr⟩, rfl⟩ hxs⟩
    simp [ivEnc, natList, encFun, List.map_map]

/-- The hierarchy of the reset state, as a value. -/
theorem hierValC_reset {xs : List IvData} (hxs : List.Forall₂ (fun a I =>
      (∃ lab : Fin k → ℕ, a.1 = (List.finRange k).map lab ∧ (∀ i, lab i < k) ∧
        ∀ i j, lab i = lab j ↔ I.part.r (e.symm i) (e.symm j)) ∧
      a.2 = (I.ratio, I.cap, I.origin)) xs T.hier) :
    HierValC (domEquiv e T.dom) (.list (xs.map (ivReset (domNat e T.dom) T.size)))
      (resetHier T) := by
  refine ⟨_, rfl, ?_⟩
  unfold resetHier
  generalize T.hier = l at hxs
  induction hxs with
  | nil => exact .nil
  | @cons a I xs l ha _ ih =>
    refine .cons ?_ ih
    obtain ⟨⟨lab, h1, -, hr⟩, h2⟩ := ha
    obtain ⟨labs, r, cp, o⟩ := a
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp only at h1
    subst h1
    exact ⟨_, partitionValC_relab e hr, rfl⟩

/-- **The value of the reset state is canonical.** It is a fresh value with a new hierarchy. -/
theorem canon_reset {s : ℕ} {gv xv yv hv₀ hv : Val} {c' : C → ℕ} {e' : T.dom ≃ Fin s}
    {l : List (Interval T.dom)}
    (h₀ : Canon e' c' (freshVal s gv xv yv hv₀) (T.freshOn l))
    (hh : HierValC e' hv (resetHier T)) (hsm : SmallInv T) (h2 : 2 ≤ T.size)
    (hρ : rhoNat T.hier ≤ T.size) :
    Canon e' c' (freshVal s gv xv yv hv) (resetState T) where
  val := by
    obtain ⟨g', d', x', y', h', r', hg, hd, hx, hy, -, -, hE⟩ := h₀.val
    simp only [freshVal, Val.list.injEq, List.cons.injEq, and_true] at hE
    obtain ⟨-, rfl, rfl, rfl, rfl, -, -, -, -, hN⟩ := hE
    have hN' : (resetState T).N = s := (Val.nat.inj hN).symm
    refine ⟨_, _, _, _, _, _, hg, hd, hx, hy, hh, rfl, ?_⟩
    simp only [freshVal, hN']
    rfl
  colors := h₀.colors
  fits := h₀.fits
  small := resetState_small T hsm h2 hρ

/-- The lift of the answer of the reset state is the answer of `T`. -/
theorem liftAnswer_reset : T.liftAnswer (resetState T).answer = T.answer := by
  unfold State.liftAnswer State.answer
  change {g | ∃ hg : g ∈ T.G, T.domHom ⟨g, hg⟩ ∈
    answer T.domGroup Set.univ (T.x ∘ Subtype.val) (T.y ∘ Subtype.val)} = _
  rw [answer_restrict_image T.G T.dom T.dom_inv T.x T.y]
  rfl

end State

end GI.Degree
