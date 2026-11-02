import Workspace.Impl.AggItemCiSojMath
import Workspace.Impl.AggWin

/-!
# The canonical state value of an inherited rectangle query

A query keeps the parent's positions, hierarchy and phase size. Its group is the
first projection of the representation's graph pairs. Its domain is the positions
with cells, and its source and target colors are the pulled-back matrix bits.
The row record is cleared, floor mode is off, and `h = 2`, as in `State.queryChild`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encGroup gens)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Code of a pulled-back bit, with zero for positions without a cell. -/
def itcsQCode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

theorem itcs_qcode_inj : Function.Injective itcsQCode := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b <;> simp_all [itcsQCode]
  | some a => cases b with
    | none => cases a <;> simp_all [itcsQCode]
    | some b => cases a <;> cases b <;> simp_all [itcsQCode]

theorem itcs_qcode_le (a : Option Bool) : itcsQCode a ≤ 2 := by
  cases a with
  | none => decide
  | some a => cases a <;> decide

/-- The first parts of the representation's graph pairs generate its physical group. -/
theorem itcs_query_group (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    {hs : List (Perm (Fin k) × Perm (Fin L.q))} (hhs : PairGens e L rep.H hs) :
    gens (hs.map Prod.fst) = groupFin e rep.H := by
  ext a
  rw [mem_gens_fst hhs, mem_groupFin_iff]
  constructor
  · rintro ⟨g, -, hg, he⟩
    rwa [← he, MulEquiv.symm_apply_apply]
  · intro ha
    exact ⟨(toFin e).symm a, rep.le ha, ha, MulEquiv.apply_symm_apply _ _⟩

open Classical in
/-- The canonical value to pass to `Continue`. -/
noncomputable def itcsQVal (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (t : permitted W R)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hv : Val) : Val :=
  winVal' k (encGroup (hs.map Prod.fst))
    (encFun fun i => if e.symm i ∈ rep.Δ then 1 else 0)
    (encFun fun i => itcsQCode (rep.colors M (e.symm i)))
    (encFun fun i => itcsQCode (rep.colors (RectRep.twistMat t N) (e.symm i))) hv S.N

/-- Nonempty right side and three left points force enough physical positions
for the three color codes to be canonical. -/
theorem itcs_query_k (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (h3 : 3 ≤ W.card) (hR : R.Nonempty) : 2 ≤ k := by
  classical
  obtain ⟨r, hr⟩ := hR
  let pos (w : W) : Ω := (rep.onto (w, ⟨r, hr⟩)).choose
  have hp (w : W) : rep.cell (pos w) = some (w, ⟨r, hr⟩) :=
    (rep.onto (w, ⟨r, hr⟩)).choose_spec.2
  have hi : Function.Injective (fun w : W => e (pos w)) := by
    intro a b hab
    have hc := congrArg rep.cell (e.injective hab)
    rw [hp, hp] at hc
    exact congrArg Prod.fst (Option.some.inj hc)
  have hcard := Fintype.card_le_of_injective _ hi
  simp only [Fintype.card_coe, Fintype.card_fin] at hcard
  omega

/-- The value encodes the exact query state, including all inherited bookkeeping. -/
theorem itcs_query_canon (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (t : permitted W R) {c : C → ℕ} {sv hv : Val}
    (hcan : Canon e c sv S) (hhv : HierValC e hv S.hier)
    {hs : List (Perm (Fin k) × Perm (Fin L.q))} (hhs : PairGens e L rep.H hs)
    (hlen : hs.length ≤ k ^ 2) (hk : 2 ≤ k) :
    Canon e itcsQCode (itcsQVal e rep M N t hs hv) (rep.state M N t) := by
  classical
  have hgroup : GroupValC k (encGroup (hs.map Prod.fst)) (groupFin e rep.H) :=
    ⟨hs.map Prod.fst, rfl, itcs_query_group e rep hhs, by simpa using hlen⟩
  refine ⟨?_, fun a => ⟨lt_of_le_of_lt (itcs_qcode_le _) (by omega),
    lt_of_le_of_lt (itcs_qcode_le _) (by omega)⟩, hcan.fits, ?_⟩
  · refine ⟨_, _, _, _, hv, .list [], hgroup, rfl, rfl, rfl, hhv, rfl, rfl⟩
  · exact ⟨hcan.small.1, hcan.small.2.1, fun r hr => by cases hr⟩

/-- The rectangle queries have the charged call's goodness and measure decrease. -/
theorem itcs_query_call [Finite Ω] (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R)
    (hgood : Good P₀ .giant S) :
    Good P₀ .cont (rep.state M N t) ∧
      MLt (measure P₀ .cont (rep.state M N t)) (measure P₀ .giant S) := by
  have hc := rep.query_call M N a₀ t
  rcases hc with hc | ⟨_, _, hc⟩
  · cases hc.1
  · exact chargedCall_good_mlt hgood hc

end GI.Impl
