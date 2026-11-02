import Workspace.Impl.AggImg

/-!
# The window increment from orders of images

Rules 1 to 4 of Algorithm 2 choose the increment `V_t` (`increment`). Each rule asks about the
image under `φ_T` of a pointwise stabilizer `A_{(U)}`: is it all of `Alt(T)`, or is it trivial?
Both questions are about the order `|φ_T(A_{(U)})|` (`full_iff_card`, `bot_iff_card`), and
`imgCardFuns` computes that order. This file rewrites `increment` with these orders, for a list
`os` of the points outside the window (`incList_toFinset`):

* rule 1: `|φ_T(A_{(∅)})| ≠ |Alt(T)|` gives `∅`;
* rule 2: the points `v` of `os` with `|φ_T(A_{({v})})| ≠ |Alt(T)|`, if there are any;
* rule 3: `|φ_T(A_{(Ω \ W)})| = |Alt(T)|` gives `∅`;
* rule 4: the points `v` of `os` with `|φ_T(A_{(v^A)})| = 1`.

It also gives the orbit of a position under a graph-form generating list (`mem_genOrbit_pairs`):
the program finds `v^A` from the orbit labels of the encoded pairs.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.LocalGroups GI.Endpoint
open GI.Cited (Val encPerm gens)

variable {V Q : Type} [Group Q] {P : Subgroup (Perm V)} (phi : P →* Q)

theorem fix_empty (A : Subgroup (Perm V)) : fix A ∅ = A := by
  ext g
  simp [mem_fix]

theorem fix_singleton (A : Subgroup (Perm V)) (v : V) : fix A {v} = stab A v := by
  ext g
  simp [mem_fix, mem_stab]

/-- The order of the image of a pointwise stabilizer. -/
noncomputable def cardFix (A : Subgroup (Perm V)) (U : Set V) : ℕ := Nat.card (img phi (fix A U))

open Classical in
/-- **The increment as a list**, from orders of images. Here `os` lists the points outside the
window and `a` is `|Q|`. -/
noncomputable def incList (A : Subgroup (Perm V)) (W : Set V) (os : List V) (a : ℕ) : List V :=
  if cardFix phi A ∅ ≠ a then []
  else if os.filter (fun v => cardFix phi A {v} ≠ a) ≠ [] then
    os.filter (fun v => cardFix phi A {v} ≠ a)
  else if cardFix phi A {v | v ∉ W} = a then []
  else os.filter (fun v => cardFix phi A (Endpoint.orb A v) = 1)

theorem full_iff_cardFix [Finite Q] (A : Subgroup (Perm V)) (U : Set V) :
    img phi (fix A U) = ⊤ ↔ cardFix phi A U = Nat.card Q := by
  unfold cardFix
  rw [← Subgroup.card_eq_iff_eq_top]

/-- **`incList` lists the increment** `V_t` of rules 1 to 4. -/
theorem incList_toFinset [Finite Q] [DecidableEq V] [Fintype V] (A : Subgroup (Perm V))
    (W : Finset V) {os : List V} (hos : ∀ v, v ∈ os ↔ v ∉ W) :
    (incList phi A (W : Set V) os (Nat.card Q)).toFinset = increment phi A W := by
  classical
  have hF : ∀ U, (img phi (fix A U) = ⊤ ↔ cardFix phi A U = Nat.card Q) :=
    full_iff_cardFix phi A
  have hfull : Full phi A ↔ cardFix phi A ∅ = Nat.card Q := by
    rw [← hF, fix_empty]; rfl
  have haff : ∀ v, (v ∈ affectedSet phi A W) ↔
      v ∈ os.filter (fun v => cardFix phi A {v} ≠ Nat.card Q) := by
    intro v
    rw [mem_affectedSet, List.mem_filter, hos, decide_eq_true_iff, Affected, ← fix_singleton,
      Ne, hF]
  have hout : Full phi (fix A (outside W)) ↔ cardFix phi A {v | v ∉ (W : Set V)} = Nat.card Q := by
    rw [← hF]; rfl
  have hext : ∀ v, (v ∈ extraSet phi A W) ↔
      v ∈ os.filter (fun v => cardFix phi A (Endpoint.orb A v) = 1) := by
    intro v
    rw [mem_extraSet, List.mem_filter, hos, decide_eq_true_iff, VisibleOrbit,
      ← Subgroup.card_eq_one]
    rfl
  unfold incList increment
  by_cases h1 : Full phi A
  · rw [if_neg (not_not.2 h1), if_neg (not_not.2 (hfull.1 h1))]
    by_cases h2 : (affectedSet phi A W).Nonempty
    · have h2' : os.filter (fun v => cardFix phi A {v} ≠ Nat.card Q) ≠ [] := by
        obtain ⟨v, hv⟩ := h2
        exact List.ne_nil_of_mem ((haff v).1 hv)
      rw [if_pos h2, if_pos h2']
      ext v
      rw [List.mem_toFinset, haff]
    · have h2' : ¬ os.filter (fun v => cardFix phi A {v} ≠ Nat.card Q) ≠ [] := by
        intro h
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h
        exact h2 ⟨v, (haff v).2 hv⟩
      rw [if_neg h2, if_neg h2']
      by_cases h3 : Full phi (fix A (outside W))
      · rw [if_pos h3, if_pos (hout.1 h3)]; rfl
      · rw [if_neg h3, if_neg (fun h => h3 (hout.2 h))]
        ext v
        rw [List.mem_toFinset, hext]
  · rw [if_pos h1, if_pos (fun h => h1 (hfull.2 h))]; rfl

/-! ### Orbits of positions under a graph-form generating list -/

section Orbit

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- **The orbit of the position of `v` under the encoded pairs** is the set of positions of the
orbit `v^A`. -/
theorem mem_genOrbit_pairs {A : Subgroup (Perm S.dom)} (hA : A ≤ S.domGroup)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps)
    (v : S.dom) (j : Fin (k + L.q)) :
    j ∈ genOrbit (ps.map encPair) (Fin.castAdd L.q (e v)) ↔
      ∃ u ∈ Endpoint.orb A v, Fin.castAdd L.q (e (u : Ω)) = j := by
  rw [mem_genOrbit]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, hp, rfl⟩ := mem_gens_encPair.1 hx
    rw [hps] at hp
    obtain ⟨g, hg, hA, h1, -⟩ := (mem_graphOf e L).1 hp
    obtain ⟨hg', hA'⟩ := State.mem_liftGroup.1 hA
    refine ⟨S.domHom ⟨g, hg⟩ v, ⟨_, hA', rfl⟩, ?_⟩
    rw [encPair_castAdd, ← h1, toFin_apply, Equiv.symm_apply_apply, State.domHom_apply]
  · rintro ⟨u, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨⟨g, hg⟩, rfl⟩ := hA ha
    have hgA : g ∈ S.liftGroup A := State.mem_liftGroup.2 ⟨hg, ha⟩
    have hp : ((toFin e g, (L.π ⟨g, hg⟩ : Perm (Fin L.q))) : Perm (Fin k) × Perm (Fin L.q)) ∈
        Subgroup.closure {p | p ∈ ps} := by
      rw [hps]; exact (mem_graphOf e L).2 ⟨g, hg, hgA, rfl, rfl⟩
    refine ⟨_, mem_gens_encPair.2 ⟨_, hp, rfl⟩, ?_⟩
    rw [encPair_castAdd, toFin_apply, Equiv.symm_apply_apply, State.domHom_apply]

end Orbit

end GI.Impl
