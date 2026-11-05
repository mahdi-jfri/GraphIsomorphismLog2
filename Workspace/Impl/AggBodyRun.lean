module

public import Workspace.Impl.AggLiftLoop
public import Workspace.Impl.ScriptRun
public import Workspace.Impl.GenEnum

@[expose] public section

/-!
# The run of an aggregation round, from the outputs of its phases

`aggBody` ends with `LiftAndContinue` and `CombineExact`. This file shows that the phase outputs fit `Run.aggregate`.

* The item phase hands over a run `ex : Exec P₀ I.script b` of the round's script whose
  overcosets are `b.overs = os.map abOv`: the representative `L.rep σ` and the group
  `π⁻¹(E₀) = L.lift E₀` of each overcoset `(σ, E₀, ms)` of `os` (item 3, `BranchV`).
* `lcMap_spec` gives, for each overcoset, a cost `cs i` and a run of `Continue` on the child
  `lcChild S E₀ τ sel ⌊β q⌋` for some `τ` in the overcoset with total at least `cs i`.

`ab_run`: from these, a run `Run.aggregate` of the round, whose child cost is at least
`execCost ex + ∑ cs i` (`childCost_aggregate`). The run takes these `τ`, which may differ from
the representatives in the output pieces; the translated answers agree (`lcChild_smul_answer`).

`ab_union`: the sets of the item pieces and of the continuation pieces (in the form `lc_cps`
gives them) together are the image of the parent answer. So `CombineExact` (`ce_spec`) applies
(its hypothesis is `image_answer_cases`) and returns a canonical answer of the round.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- The overcoset of the round of an overcoset value `(σ, E₀, ms)`: `(L.rep σ, π⁻¹(E₀))`. -/
noncomputable def abOv {S : State Ω C} (L : GiantLabels S) (o : LcOver L.q) : Perm Ω × Subgroup (Perm Ω) :=
  (L.rep o.1, L.lift o.2.1)

/-- The cap of the selected interval in the children of the round. -/
noncomputable def abCap {S : State Ω C} (L : GiantLabels S) : ℕ := ⌊P₀.β * L.q⌋₊

/-- **The run of the round.** -/
theorem ab_run (I : Iface) {S : State Ω C}
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive)
    (L : SuppliedLabels S) (hnot : ¬ RowCase P₀.α S L.toGiantLabels) (hq₀ : P₀.q₀ ≤ L.q)
    (Ag : Aggregation P₀ S L.toGiantLabels) (hsel : Ag.sel.val = L.sel.val) (hcon : Ag.con = L.con)
    (pieces : List (Set (Perm Ω))) (os : List (LcOver L.q))
    (ex : Exec P₀ Ag.script ⟨pieces, os.map (abOv L.toGiantLabels)⟩) (cs : ℕ → ℕ)
    (hrun : ∀ i (hi : i < os.length),
      ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)), ∃ (A : Set (Perm Ω))
        (r : Run P₀ .cont (lcChild S os[i].2.1 τ Ag.sel (abCap L.toGiantLabels)) none A),
          (cs i : ℝ) ≤ r.total I.work) :
    ∃ (A : Set (Perm Ω)) (r : Run P₀ .giant S (some L) A), r.kind = .aggregate ∧
      I.execCost ex + ∑ i ∈ Finset.range os.length, (cs i : ℝ) ≤ I.childCost r := by
  choose τ hτ A r hcs using hrun
  let b : Branches Ω := ⟨pieces, os.map (abOv L.toGiantLabels)⟩
  have hlen : b.overs.length = os.length := by simp [b]
  have hget : ∀ j : Fin b.overs.length, b.overs.get j = abOv L.toGiantLabels (os[(j : ℕ)]'(by
      have := j.2; omega)) := fun j => by simp [b, List.get_eq_getElem]
  let τ' : Fin b.overs.length → Perm Ω := fun j => τ j (by have := j.2; omega)
  have hτ' : ∀ j, τ' j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)) := fun j => by
    rw [hget j]; exact hτ j _
  let child : Fin b.overs.length → State Ω C := fun j =>
    lcChild S (os[(j : ℕ)]'(by have := j.2; omega)).2.1 (τ' j) Ag.sel (abCap L.toGiantLabels)
  have hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ' j) := fun j => by
    rw [hget j]; exact lcChild_inst S _ _ _ _
  have hhier : ∀ j, (child j).hier = Ag.newHier (b.overs.get j) := fun j => by
    rw [lcChild_hier]; exact lcHier_eq_newHier S Ag _
  have hbk : ∀ j, (child j).book = S.book := fun j => by
    exact lcChild_book S Ag.con _ _ _ _
  let A' : Fin b.overs.length → Set (Perm Ω) := fun j => A j (by have := j.2; omega)
  let r' : ∀ j, Run P₀ .cont (child j) none (A' j) := fun j => r j (by have := j.2; omega)
  refine ⟨_, Run.aggregate hs htr L hnot hq₀ Ag hsel hcon b ex τ' hτ' child hchild
    (fun j => lcChild_N S _ _ _ _) hhier hbk A' r', rfl, ?_⟩
  rw [Iface.childCost_aggregate]
  refine add_le_add le_rfl ?_
  rw [List.sum_ofFn, ← Fin.sum_univ_eq_sum_range (fun i => (cs i : ℝ)) os.length]
  rw [← Fin.sum_congr' (fun i => (cs i : ℝ)) hlen]
  exact Finset.sum_le_sum fun j _ => hcs j _

/-- **The pieces of the round cover the parent answer**: the item pieces `pcs` (sets of the
pieces of `b`) and the continuation pieces `cps` (translated child answers, as `lc_cps` gives
them) together are the image of the parent answer. -/
theorem ab_union (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} {P : Params}
    (Ag : Aggregation P S L) (pieces : List (Set (Perm Ω))) (os : List (LcOver L.q))
    (ex : Exec P Ag.script ⟨pieces, os.map (abOv L)⟩) (cap : ℕ)
    (pcs : List (Perm (Fin k) × Acc k)) (hl : pcs.length = pieces.length)
    (hp : ∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i])
    (cps : List (Perm (Fin k) × Acc k)) (hcl : cps.length = os.length)
    (hc : ∀ i (h1 : i < cps.length) (h2 : i < os.length),
      (toFin e).symm cps[i].1 ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
      ceSet cps[i] = toFin e '' ((toFin e).symm cps[i].1 •
        (lcChild S os[i].2.1 ((toFin e).symm cps[i].1) Ag.sel cap).answer)) :
    unionSet (pcs ++ cps) = toFin e '' S.answer := by
  let b : Branches Ω := ⟨pieces, os.map (abOv L)⟩
  have hcov : Branches.Covers S b := by
    have h := Ag.covers
    rwa [← ex.exact] at h
  have hlen : b.overs.length = os.length := by simp [b]
  have hget : ∀ j : Fin b.overs.length, b.overs.get j = abOv L (os[(j : ℕ)]'(by
      have := j.2; omega)) := fun j => by simp [b, List.get_eq_getElem]
  let τ : Fin b.overs.length → Perm Ω := fun j => (toFin e).symm (cps[(j : ℕ)]'(by
    have := j.2; omega)).1
  let child : Fin b.overs.length → State Ω C := fun j =>
    lcChild S (os[(j : ℕ)]'(by have := j.2; omega)).2.1 (τ j) Ag.sel cap
  have hτ : ∀ j, τ j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)) := fun j => by
    rw [hget j]; exact (hc j _ _).1
  have hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ j) := fun j => by
    rw [hget j]; exact lcChild_inst S _ _ _ _
  have hans := step_aggregate b hcov τ hτ child hchild (fun j => (child j).answer) fun _ => rfl
  rw [← hans]
  exact ce_union e pieces pcs hl hp τ (fun j => (child j).answer) cps (by omega)
    fun j h => (hc j h (by have := j.2; omega)).2

/-- **The continuation pieces** in the form `ab_union` asks, from the output of `lcMap_spec`. -/
theorem ab_cps (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} (os : List (LcOver L.q))
    (sel cap : ℕ) (ws : List Val) (hl : ws.length = os.length)
    (h : ∀ i (hi : i < os.length) (hw : i < ws.length), ∃ a u, ws[i] = .list [encPerm a, u] ∧
      (toFin e).symm a ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
      AnsC e u (lcChild S os[i].2.1 ((toFin e).symm a) sel cap).answer) :
    ∃ cps : List (Perm (Fin k) × Acc k), ws = cps.map encPiece ∧ cps.length = os.length ∧
      ∀ i (h1 : i < cps.length) (h2 : i < os.length),
        (toFin e).symm cps[i].1 ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
        ceSet cps[i] = toFin e '' ((toFin e).symm cps[i].1 •
          (lcChild S os[i].2.1 ((toFin e).symm cps[i].1) sel cap).answer) := by
  obtain ⟨cps, hws, hcps⟩ := lc_cps e
    (fun i τ => ∀ hi : i < os.length, τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)))
    (fun i τ => if hi : i < os.length then (lcChild S os[i].2.1 τ sel cap).answer else ∅) ws
    (fun i hw => by
      obtain ⟨a, u, h1, h2, h3⟩ := h i (by omega) hw
      exact ⟨a, u, h1, fun _ => h2, by rwa [dif_pos (by omega)]⟩)
  have hlen : cps.length = os.length := by rw [← hl, hws, List.length_map]
  refine ⟨cps, hws, hlen, fun i h1 h2 => ⟨(hcps i h1).1 h2, ?_⟩⟩
  have := (hcps i h1).2
  simp only [dif_pos h2] at this
  exact this

end GI.Impl
