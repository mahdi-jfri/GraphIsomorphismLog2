module

public import Workspace.Impl.AggCertProg

@[expose] public section

/-!
# The move program: context and reading the program state

* `cpParV`: the parent data `par` of the phase.
* `CpCtx`: the facts about the parent that every move uses (canonical value, `Good`, the graph
  of `G`, the domain points, `D = |Alt(T)|`).
* `CpMvPost`: what a move must return (the condition of `stepOKC_of_move` for `CpRep`).
* `cp_rdK`, `cp_rdP`, `cp_rdS`, `cp_rdI`: reading an entry of `kst`, of `par`, of the parent's
  state value and of `inner`, at a cost of a few times the weight bound `W`.
* `cp_W_facts`: what the choice `W ≥ 10⁴ (Bw + 2)²` gives.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

/-- **The parent data of the phase.** -/
def cpParV (k q n D : ℕ) (sv gpv osv : Val) : Val :=
  .list [sv, .list [.nat k, .nat q], gpv, .nat n, .nat D, osv, pSplitCtx k q, .nat (k + q)]

section Ctx

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
  [Fintype S.dom] (L : GiantLabels S) (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **The facts about the parent** that the moves use. -/
structure CpCtx (sv : Val) (gp : GPairs k L.q) (osA : List (Fin (k + L.q))) (D : ℕ) : Prop where
  inj : Function.Injective c
  canon : Canon e c sv S
  good : Good P₀ .giant S
  tr : S.Transitive
  hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g
  hgp : PairGens e L S.G gp
  hgpl : gp.length ≤ (k + L.q) ^ 2
  hosA : CpAll e S L.q osA
  hD : ∀ T : Finset (Fin L.q), T.card = P₀.κ → Nat.card (alternatingGroup T) = D

/-- **What a move returns**: what the step returns (`StepPostC`), or `[2, st']` for a program
state `st'` of smaller measure that stands for a subset of the candidates. -/
def CpMvPost (par : Val) (D Bw M₀ NT m : ℕ) (Ss : Set (Script (List (StagePair S)))) (f : ℕ)
    (w : Val) : Prop :=
  Iface.StepPostC (measure P₀ .giant S) (CpOut e S L πd)
      (fun st Ss f => ∃ m, CpRep e πd par D Bw M₀ NT m st Ss f) Ss f w ∨
    ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ CpRep e πd par D Bw M₀ NT m' st' Ss' f ∧
      w = .list [.nat 2, st']

end Ctx

/-! ### Reading the program state -/

section Read

variable {P : Program} {W : ℕ} {env : List Val} {ks : List Val} {x : Val}

theorem cp_wt_get {vs : List Val} {j : ℕ} {v : Val} (h : vs[j]? = some v) :
    v.wt < (Val.list vs).wt := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact wt_getElem_lt vs j hj

theorem cp_rdKs (h0 : env[0]? = some (.list [.list ks, x])) (hw : (Val.list [.list ks, x]).wt ≤ W) :
    Det P env cpKs (.list ks) (2 * (W + 20)) :=
  Det.rd (Det.rv h0 hw) le_rfl rfl
    (le_of_lt (lt_of_lt_of_le (cp_wt_get (vs := [.list ks, x]) (j := 0) rfl) hw)) (by omega)

theorem cp_rdK (h0 : env[0]? = some (.list [.list ks, x])) (hw : (Val.list [.list ks, x]).wt ≤ W)
    {j : ℕ} {v : Val} (hv : ks[j]? = some v) (hj : j ≤ 15) :
    Det P env (cpKf j) v (3 * (W + 20)) := by
  have h1 : (Val.list ks).wt < W := lt_of_lt_of_le (cp_wt_get (vs := [.list ks, x]) (j := 0) rfl) hw
  exact Det.rd (cp_rdKs h0 hw) le_rfl hv ((cp_wt_get hv).trans h1).le hj

theorem cp_rdP (h0 : env[0]? = some (.list [.list ks, x])) (hw : (Val.list [.list ks, x]).wt ≤ W)
    {ps : List Val} (hp : ks[0]? = some (.list ps)) {j : ℕ} {v : Val} (hv : ps[j]? = some v)
    (hj : j ≤ 15) : Det P env (cpPf j) v (4 * (W + 20)) := by
  have h1 : (Val.list ks).wt < W := lt_of_lt_of_le (cp_wt_get (vs := [.list ks, x]) (j := 0) rfl) hw
  have h2 := (cp_wt_get hp).trans h1
  exact Det.rd (cp_rdK h0 hw hp (by omega)) le_rfl hv ((cp_wt_get hv).trans h2).le hj

theorem cp_rdS (h0 : env[0]? = some (.list [.list ks, x])) (hw : (Val.list [.list ks, x]).wt ≤ W)
    {ps ss : List Val} (hp : ks[0]? = some (.list ps)) (hs : ps[0]? = some (.list ss)) {j : ℕ}
    {v : Val} (hv : ss[j]? = some v) (hj : j ≤ 15) : Det P env (cpSf j) v (5 * (W + 20)) := by
  have h1 : (Val.list ks).wt < W := lt_of_lt_of_le (cp_wt_get (vs := [.list ks, x]) (j := 0) rfl) hw
  have h2 := (cp_wt_get hp).trans h1
  have h3 := (cp_wt_get hs).trans h2
  exact Det.rd (cp_rdP h0 hw hp hs (by omega)) le_rfl hv ((cp_wt_get hv).trans h3).le hj

theorem cp_rdI (h0 : env[0]? = some (.list [.list ks, x])) (hw : (Val.list [.list ks, x]).wt ≤ W)
    {is : List Val} (hi : ks[10]? = some (.list is)) {j : ℕ} {v : Val} (hv : is[j]? = some v)
    (hj : j ≤ 15) : Det P env (cpIf j) v (4 * (W + 20)) := by
  have h1 : (Val.list ks).wt < W := lt_of_lt_of_le (cp_wt_get (vs := [.list ks, x]) (j := 0) rfl) hw
  have h2 := (cp_wt_get hi).trans h1
  exact Det.rd (cp_rdK h0 hw hi (by omega)) le_rfl hv ((cp_wt_get hv).trans h2).le hj

/-- A list of deterministic pieces of uniform cost, with the list weight at most `W`. -/
theorem cp_mkList (ps : List (Expr × Val)) {c : ℕ} (h : ∀ p ∈ ps, Det P env p.1 p.2 c)
    (hw : (Val.list (ps.map Prod.snd)).wt ≤ W) :
    Det P env (Expr.mkList (ps.map Prod.fst)) (.list (ps.map Prod.snd))
      (ps.length * (c + W + 1) + 5) :=
  (Det.mkList ps h).mono (by
    have := Nat.mul_le_mul_left ps.length (show c + (Val.list (ps.map Prod.snd)).wt + 1 ≤
      c + W + 1 by omega)
    omega)

end Read

/-! ### The weight bound -/

/-- **What `W ≥ 10⁴ (Bw + 2)²` gives**, for `Bw ≥ cpBw`. -/
theorem cp_W_facts {k q P NT M₀ D Bw W : ℕ} (hBw : cpBw k q P NT M₀ D ≤ Bw)
    (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W) :
    100 * Bw + 1000 ≤ W ∧ 10 ^ 10 * (k + q + 1) ^ 12 ≤ W ∧
      10 ^ 6 * (D + 1) * (k + q + 1) ^ 6 ≤ Bw ∧ 4 * P ≤ Bw ∧ 1 ≤ W := by
  have h6 : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hB : 10 ^ 6 * (D + 1) * (k + q + 1) ^ 6 ≤ Bw := by
    have : (D + 1) * (k + q + 1) ^ 6 ≤ (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 := by
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    unfold cpBw at hBw
    have e : 10 ^ 6 * (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 =
      10 ^ 6 * ((NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6) := by ring
    have e2 : 10 ^ 6 * (D + 1) * (k + q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + q + 1) ^ 6) := by ring
    omega
  have hP : 4 * P ≤ Bw := by unfold cpBw at hBw; omega
  have hsq : (Bw + 2) ^ 2 = (Bw + 2) * (Bw + 2) := by ring
  have h1 : 100 * Bw + 1000 ≤ W := by nlinarith
  have h2 : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W := by
    have a : (k + q + 1) ^ 6 ≤ Bw := by
      have : (k + q + 1) ^ 6 ≤ (D + 1) * (k + q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
    have b : (k + q + 1) ^ 12 = (k + q + 1) ^ 6 * (k + q + 1) ^ 6 := by ring
    have c : (k + q + 1) ^ 6 * (k + q + 1) ^ 6 ≤ Bw * Bw := Nat.mul_le_mul a a
    have d : 10 ^ 6 * (k + q + 1) ^ 6 ≤ Bw := by
      have : (k + q + 1) ^ 6 ≤ (D + 1) * (k + q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
    have e : 10 ^ 6 * (k + q + 1) ^ 6 * (10 ^ 6 * (k + q + 1) ^ 6) ≤ Bw * Bw := Nat.mul_le_mul d d
    nlinarith
  exact ⟨h1, h2, hB, hP, by omega⟩

end GI.Impl
