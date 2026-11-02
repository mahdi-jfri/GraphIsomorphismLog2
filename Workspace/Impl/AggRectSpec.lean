import Workspace.Impl.AggPairs
import Workspace.Impl.Canon
import Workspace.Algorithm.Aggregation

/-!
# The rectangle programs: the contracts

The first-rectangle items of the auxiliary algorithm (`sojItem`, `rectItem`,
`Workspace/Algorithm/AuxRectangle.lean`) use two pieces of model data that the round fixes as
fields (`Aggregation.soj`, `Aggregation.rep`), and that the paper leaves to the algorithm:

* the **rectangle certificate** `SojChoice.cert X i₀` at a source vertex of a pair
  configuration (Lemma 5.1: "a rectangle certificate exists"); any certificate works;
* the **rectangle representation** `rep W R h : RectRep` of a rectangle `W × R` on an inherited
  orbit (Algorithm `alg:auxiliary`: "Represent the rectangle on an actual inherited orbit `Δ`";
  Lemmas A.27 and A.30); any representation works.

Both are fields of `Aggregation`, and neither enters the certificate or the comparison script
(`ItHand`), so the items phase may set them to the program's choices. What it needs is that the
program's choices form *one function* (of `X, i₀`, resp. of `W, R`), so that the round's field
is that function. So each contract below says: there is a function `cf` (resp. `Rf`), and on
every input the program returns the value of that function. No weakening of the model is
needed.

## Encodings

* A set of labels `W ⊆ Fin q`: its indicator list (`rcSetVal`).
* A pair configuration `X`: the table of `X.col` by rows (`rcColVal`), with `X.j`.
* A certificate at `i₀`: `[v_L, v_R, v_E, a, b]` (`rcCertVal`): the pair colors of its left
  side, its right side and its edges (`certVals`, the values that `rectItem` reads), and the
  labels `a = emb(leftPoint)`, `b = emb(rightPoint)`. These determine the certificate
  (`rcCertVal_injective`). No certificate: `[]`.
* A rectangle representation: `[⟨hs⟩, cells, tw]` (`rcRepVal`): graph pairs `hs` of the group
  `H` (`PairGens e L H hs`, as the other phases keep subgroups of `G`), the cell table on the
  positions (`0` off `Δ`, `1 + w q + r` above the matrix entry `(w, r)`, `rcCellCode`), and the
  twist (`[]` or `[t]`). These determine the representation (`rcRepVal_injective`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance GI.Rectangle GI.PairRefinement Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {Ω C : Type} {k q : ℕ}

/-! ### Encodings -/

/-- The indicator list of a set of labels. -/
def rcSetVal (W : Finset (Fin q)) : Val := encFun fun i => if i ∈ W then 1 else 0

theorem rcSetVal_injective : Function.Injective (rcSetVal (q := q)) := by
  intro W W' h
  have h' := encFun_injective h
  ext i
  have := congrFun h' i
  by_cases h1 : i ∈ W <;> by_cases h2 : i ∈ W' <;> simp_all

/-- The table of the pair colors of a configuration, by rows. -/
def rcColVal (X : PairCfg q) : Val := .list ((List.finRange q).map fun a => encFun (X.col a))

/-- **The input of the certificate search**: `[col table, j, x₀]`. -/
def rcCertIn (X : PairCfg q) (x₀ : Fin q) : Val := .list [rcColVal X, .nat X.j, .nat x₀]

/-- **The value of a certificate**: `[v_L, v_R, v_E, a, b]`. -/
noncomputable def rcCertVal (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) : Val :=
  .list [.nat (certVals X i₀ cert).1, .nat (certVals X i₀ cert).2.1,
    .nat (certVals X i₀ cert).2.2, .nat (X.emb rfl cert.leftPoint.val),
    .nat (X.emb rfl cert.rightPoint.val)]

/-- A certificate is fixed by its data (the other fields are propositions). -/
theorem rc_cert_ext {n : ℕ} {c : Coloring n} {side : Bool} {x : Fin n} {η : ℝ}
    {a b : RectangleCertificate c side x η} (h1 : a.leftColor = b.leftColor)
    (h2 : a.rightColor = b.rightColor) (h3 : a.edgeColor = b.edgeColor)
    (h4 : a.leftPoint.val = b.leftPoint.val) (h5 : a.rightPoint.val = b.rightPoint.val) : a = b := by
  cases a with
  | mk l r e lp rp =>
    cases b with
    | mk l' r' e' lp' rp' =>
      simp only at h1 h2 h3 h4 h5
      subst h1 h2 h3
      have : lp = lp' := Subtype.ext h4
      have : rp = rp' := Subtype.ext h5
      subst lp rp
      rfl

/-- **The value of a certificate fixes it.** The left and right colors are the codes of the colors
at the two points, and the edge color is the code of `v_E` (`certVals_edge`). -/
theorem rcCertVal_injective (X : PairCfg q) (i₀ : Fin X.fiber.card)
    {a b : RectangleCertificate X.coloring false i₀ etaB}
    (h : rcCertVal X i₀ a = rcCertVal X i₀ b) : a = b := by
  simp only [rcCertVal, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
  obtain ⟨-, -, hE, hl, hr⟩ := h
  have hl' : a.leftPoint.val = b.leftPoint.val := (X.emb rfl).injective (Fin.ext hl)
  have hr' : a.rightPoint.val = b.rightPoint.val := (X.emb rfl).injective (Fin.ext hr)
  have h1 : a.leftColor = b.leftColor := by
    rw [← a.leftPoint.property, ← b.leftPoint.property, hl']
  have h2 : a.rightColor = b.rightColor := by
    rw [← a.rightPoint.property, ← b.rightPoint.property, hr']
  refine rc_cert_ext h1 h2 ?_ hl' hr'
  -- the edge colors: both are the code of `v_E`
  obtain ⟨u, -, hu, -⟩ := a.mixed
  obtain ⟨u', -, hu', -⟩ := b.mixed
  have ha : X.coloring (false, u.val, a.rightPoint.val) = a.edgeColor := by
    simpa [fiberMatrix] using hu
  have hb : X.coloring (false, u'.val, b.rightPoint.val) = b.edgeColor := by
    simpa [fiberMatrix] using hu'
  have ea := certVals_edge X i₀ a ha
  have eb := certVals_edge X i₀ b hb
  rw [← ha, ← hb]
  exact (X.coloring_eq_iff false false _ _ _ _).2 (ea.symm.trans (hE.trans eb))

/-- A certificate function: one certificate for every vertex at which one exists (the type of
`SojChoice.cert`). -/
def RcCertFn : Type :=
  ∀ {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card),
    Nonempty (RectangleCertificate X.coloring false i₀ etaB) →
    RectangleCertificate X.coloring false i₀ etaB

/-- The choices of a first-rectangle item with the certificate replaced by `cf`. -/
def SojChoice.withCert (ch : SojChoice) (cf : RcCertFn) : SojChoice :=
  { ch with cert := cf }

/-- **The certificate search** at `f`, within cost `B` of the input weight. There is one
certificate function `cf`; on `[col table, j, x₀]` for a vertex `x₀` of the fiber, the program
returns the value of `cf X (idx x₀)` when a certificate at `x₀` exists, and `[]` otherwise. -/
def RcCertSpec (P : Program) (f : ℕ) (B : ℕ → ℕ) : Prop :=
  ∃ cf : RcCertFn, ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (hx : x₀ ∈ X.fiber),
    FunAll P f (rcCertIn X x₀) fun w cost =>
      (∀ h : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB),
        w = rcCertVal X (X.idx hx) (cf X (X.idx hx) h)) ∧
      (IsEmpty (RectangleCertificate X.coloring false (X.idx hx) etaB) → w = .list []) ∧
      cost ≤ B (rcCertIn X x₀).wt ∧ w.wt ≤ B (rcCertIn X x₀).wt

/-! ### The rectangle representation -/

/-- The code of a cell: `0` off the orbit, `1 + w q + r` above the matrix entry `(w, r)`. -/
def rcCellCode {W R : Finset (Fin q)} : Option (W × R) → ℕ
  | none => 0
  | some c => 1 + (c.1.val : ℕ) * q + (c.2.val : ℕ)

theorem rcCellCode_injective {W R : Finset (Fin q)} :
    Function.Injective (rcCellCode (q := q) (W := W) (R := R)) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => simp [rcCellCode] at h; omega
  | some a => cases b with
    | none => simp [rcCellCode] at h
    | some b =>
      simp only [rcCellCode] at h
      have hr1 := a.2.val.isLt
      have hr2 := b.2.val.isLt
      have e1 : (a.1.val : ℕ) = b.1.val := by
        have h' : (a.1.val : ℕ) * q + a.2.val = b.1.val * q + b.2.val := by omega
        have := congrArg (· / q) h'
        simp only at this
        rwa [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.mul_comm, Nat.mul_add_div (by omega),
          Nat.div_eq_of_lt hr1, Nat.div_eq_of_lt hr2, add_zero, add_zero] at this
      have e2 : (a.2.val : ℕ) = b.2.val := by
        rw [e1] at h; omega
      congr 1
      exact Prod.ext (Subtype.ext (Fin.ext e1)) (Subtype.ext (Fin.ext e2))

/-- **The value of a rectangle representation**: `[⟨hs⟩, cells, tw]`, for graph pairs `hs` of its
group. -/
noncomputable def rcRepVal {S : State Ω C} {L : GiantLabels S} {W R : Finset (Fin L.q)}
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (hs : List (Perm (Fin k) × Perm (Fin L.q))) : Val :=
  .list [.list (hs.map pairV), encFun fun i => rcCellCode (rep.cell (e.symm i)),
    .list (rep.twist.toList.map fun t : ↥(permitted W R) => encPerm t.1.1)]

/-- A rectangle representation is fixed by its group, cells and twist. -/
theorem rc_rep_ext {S : State Ω C} {L : GiantLabels S} {W R : Finset (Fin L.q)}
    {a b : RectRep P₀ S L W R} (h1 : a.H = b.H) (h2 : a.cell = b.cell) (h3 : a.twist = b.twist) :
    a = b := by
  cases a; cases b
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- The group of a subgroup of `G` is the first projection of its graph. -/
theorem rc_mem_of_graph {S : State Ω C} {L : GiantLabels S} (e : Ω ≃ Fin k) {A : Subgroup (Perm Ω)}
    (hA : A ≤ S.G) {g : Perm Ω} : g ∈ A ↔ ∃ p ∈ graphOf e L A, p.1 = toFin e g := by
  constructor
  · intro hg
    exact ⟨(toFin e g, ((L.π ⟨g, hA hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q))),
      (mem_graphOf (e := e) (L := L)).2 ⟨g, hA hg, hg, rfl, rfl⟩, rfl⟩
  · rintro ⟨p, hp, hpg⟩
    obtain ⟨g', -, hg', h1, -⟩ := (mem_graphOf (e := e) (L := L)).1 hp
    have : g' = g := (toFin e).injective (h1.trans hpg)
    exact this ▸ hg'

/-- **The value of a representation fixes it**, given graph pairs of its group. -/
theorem rcRepVal_injective {S : State Ω C} {L : GiantLabels S} {W R : Finset (Fin L.q)}
    (e : Ω ≃ Fin k) {a b : RectRep P₀ S L W R} {hs hs' : List (Perm (Fin k) × Perm (Fin L.q))}
    (ha : PairGens e L a.H hs) (hb : PairGens e L b.H hs')
    (h : rcRepVal e a hs = rcRepVal e b hs') : a = b := by
  simp only [rcRepVal, Val.list.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hhs : hs = hs' := (List.map_injective_iff.2 pairV_injective) h1
  subst hhs
  have hH : a.H = b.H := by
    ext g
    rw [rc_mem_of_graph e a.le, rc_mem_of_graph e b.le, ← ha, ← hb]
  have hc : a.cell = b.cell := by
    funext v
    have := congrFun (encFun_injective h2) (e v)
    simp only [Equiv.symm_apply_apply] at this
    exact rcCellCode_injective this
  have ht : a.twist = b.twist := by
    have h3' := (List.map_injective_iff.2 fun (t t' : ↥(permitted W R))
      (h : encPerm t.1.1 = encPerm t'.1.1) => Subtype.ext (Subtype.ext (encPerm_injective h))) h3
    cases hat : a.twist <;> cases hbt : b.twist <;> simp_all
  exact rc_rep_ext hH hc ht

/-- **The input of the rectangle program**: `[sv, q, ⟨ps⟩, W, R]`, for the state value `sv` and
graph pairs `ps` of `G`. -/
noncomputable def rcRepIn (sv : Val) (q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q)))
    (W R : Finset (Fin q)) : Val :=
  .list [sv, .nat q, .list (ps.map pairV), rcSetVal W, rcSetVal R]

/-- **The rectangle program** at `f`, within cost `B` of the input weight. For a canonical state
value `sv` of a state of an aggregation round, with graph pairs `ps` of `G`, there is one
representation function `Rf` (any representations, as the field `Aggregation.rep` allows); on
`[sv, q, ⟨ps⟩, W, R]` for a rectangle with `RectConds` the program returns the value of
`Rf W R h`, with at most `k²` graph pairs of its group. -/
def RcRepSpec (P : Program) (f : ℕ) (B : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv : Val)
    (L : GiantLabels S) (_I : AggregationData P₀ S L)
    (ps : List (Perm (Fin k) × Perm (Fin L.q))),
    Function.Injective c → Canon e c sv S → PairGens e L S.G ps →
    ∃ Rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L W R → RectRep P₀ S L W R,
    ∀ (W R : Finset (Fin L.q)) (h : RectConds P₀ S L W R),
      FunAll P f (rcRepIn sv L.q ps W R) fun w cost =>
        ∃ hs : List (Perm (Fin k) × Perm (Fin L.q)),
          w = rcRepVal e (Rf W R h) hs ∧ PairGens e L (Rf W R h).H hs ∧ hs.length ≤ k ^ 2 ∧
          cost ≤ B (rcRepIn sv L.q ps W R).wt ∧ w.wt ≤ B (rcRepIn sv L.q ps W R).wt

end GI.Impl
