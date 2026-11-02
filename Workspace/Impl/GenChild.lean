import Workspace.Algorithm.Existence
import Workspace.Algorithm.DispatchInv
import Workspace.Impl.DispatchSmall
import Workspace.Impl.Canon

/-!
# The children of a dispatcher reduction are smaller calls

A child of `Run.dispatch` runs under the child group `I.K` on the same domain, with the same
phase size, the exposed hierarchy `I.hier'` and the same bookkeeping. The step function calls
`Continue` on it through the induction hypothesis of the skeleton (`Iface.IH`), which asks that
the child is `Good` and has a smaller measure. Both facts are proved inside the existence proof
(`run_exists`, `Workspace/Algorithm/Existence.lean`) for the child `S.restrict …`; here they are
stated for any child state with these parts (`dispatch_child_good`, `dispatch_child_mlt`).

Why the measure drops: an enumeration child is intransitive (its orbits have at most `s/d`
points, `DispatchFacts`), so the transitivity entry drops; a product child keeps the transitivity
entry at most `1` and the size and `σ` at most those of `S`, and its `ρ` drops by at least
`r - 1 ≥ 1`.
-/

namespace GI.Algorithm

variable {Ω C : Type} {P : Params}

/-- A dispatcher child is a good `Continue` call. -/
theorem dispatch_child_good [Finite Ω] {S : State Ω C} (hgood : Good P .cont S)
    (I : DispatchStep P S) {T : State Ω C} {y' : Ω → C} (hT : T.Inst I.K S.dom S.x y')
    (hN : T.N = S.N) (hh : T.hier = I.hier') : Good P .cont T := by
  obtain ⟨hG, hD, -, -⟩ := hT
  obtain ⟨hN₀, hsN, -⟩ := hgood
  have hsz : T.size = S.size := by simp only [State.size, hD]
  refine ⟨hN ▸ hN₀, by rw [hsz, hN]; exact hsN, ?_⟩
  show HierInv T.G T.dom T.hier
  rw [hG, hD, hh]
  exact I.hierInv

/-- **A dispatcher child has a smaller measure.** -/
theorem dispatch_child_mlt [Finite Ω] (hκ : 5 ≤ P.κ) {S : State Ω C}
    (hth : (S.N : ℝ) ^ P.γ < S.size) (htr : S.Transitive)
    (I : DispatchStep P S) {T : State Ω C} {y' : Ω → C} (hT : T.Inst I.K S.dom S.x y')
    (hN : T.N = S.N) (hh : T.hier = I.hier') :
    MLt (measure P .cont T) (measure P .cont S) := by
  obtain ⟨hG, hD, -, -⟩ := hT
  have hσ : T.sigma P.κ ≤ S.sigma P.κ :=
    State.sigma_le_of hκ (hG ▸ I.K_le) (by rw [hD])
  have htrj := trInd_le T
  have htrS : trInd S = 1 := trInd_of S htr
  have hsz : T.size = S.size := by simp only [State.size, hD]
  rw [mlt_iff]
  simp only [measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
  cases hkind : I.kind with
  | enumeration d =>
    have hf := I.facts
    rw [hkind] at hf
    obtain ⟨hd2, -, -, -, hdorb⟩ := hf
    have hnt : ¬ T.Transitive := by
      intro htj
      obtain ⟨v, hv⟩ := dom_nonempty_of_large hth
      have hvT : v ∈ T.dom := by rw [hD]; exact hv
      have h1 := size_le_orb htj hvT
      have h2 := hdorb v hv
      rw [hG, hsz] at h1
      have : 2 * S.size ≤ S.size := (Nat.mul_le_mul hd2 h1).trans h2
      have hpos : 0 < S.size := by
        rw [State.size, Nat.card_pos_iff]
        exact ⟨⟨v, hv⟩, Set.toFinite _ |>.to_subtype⟩
      omega
    have := trInd_of_not _ hnt
    omega
  | product r =>
    have hf := I.facts
    rw [hkind] at hf
    obtain ⟨hr2, -, -, hρ⟩ := hf
    have hρ' : rhoNat I.hier' + 1 ≤ rhoNat S.hier := by
      have h1 : (rhoNat I.hier' : ℝ) + 1 ≤ rhoNat S.hier := by
        rw [rhoNat_cast, rhoNat_cast]
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
        linarith
      exact_mod_cast h1
    rw [hh]
    omega

end GI.Algorithm

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ}

/-- The value of a dispatcher child: the group, the target coloring and the hierarchy replaced;
the domain, the source coloring, the bookkeeping and `N` kept. -/
def dispChildVal (k : ℕ) (gv dv xv yv hv rv fv hh : Val) (N : ℕ) : Val :=
  .list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]

/-- **A dispatcher child has a canonical value**: the input with the kernel's group value, the
recolored target and the exposed hierarchy. -/
theorem canon_dispChild {P : Params} {e : Ω ≃ Fin k} {c : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (I : DispatchStep P S) {T : State Ω C} {y' : Ω → C} (hT : T.Inst I.K S.dom S.x y')
    (hN : T.N = S.N) (hh' : T.hier = I.hier') (hbk : T.book = S.book)
    {gv' yv' hv' : Val} (hg : GroupValC k gv' (groupFin e I.K)) (hy : ColorVal e c yv' y')
    (hyc : ∀ a, c (y' a) < 2 * k) (hhv : HierValC e hv' I.hier') :
    Canon e c (dispChildVal k gv' dv xv yv' hv' rv fv hh N) T := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, hd, hx, -, -, hr, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, rfl, rfl, -, -, rfl, rfl, rfl, hNe, -⟩ := heq
  obtain ⟨hG, hD, hX, hY⟩ := hT
  have hrows : T.rows = S.rows := congrArg Prod.fst hbk
  have hfl : T.floor = S.floor := congrArg (fun b => b.2.1) hbk
  have hhT : T.h = S.h := congrArg (fun b => b.2.2) hbk
  refine ⟨⟨gv', dv, xv, yv', hv', rv, hG ▸ hg, hD ▸ hd, hX ▸ hx, hY ▸ hy, hh' ▸ hhv,
    hrows ▸ hr, ?_⟩, fun a => ⟨hX ▸ (hcan.colors a).1, hY ▸ hyc a⟩, ?_, ?_⟩
  · simp only [dispChildVal, hfl, hhT, hN, hNe]
  · rw [hN]; exact hcan.fits
  · exact I.smallInv_child hcan.small hN hh' hbk

end GI.Impl
