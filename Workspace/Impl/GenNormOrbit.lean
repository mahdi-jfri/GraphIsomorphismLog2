import Workspace.Impl.GenNormChild
import Workspace.Impl.RestSel

/-!
# Deciding the normalization mode by orbits

The largest-orbit program returns the domain points outside one orbit. Their indicator is
zero everywhere exactly when the group is transitive. A maximum and an equality test decide
this, without a cited algorithm. Since all normalization children have the same group and
domain, this one test selects the mode of every child.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encGroup gens)

/-- On `[group, domain]`, return `1` for a transitive action and `0` otherwise. -/
def normOrbitF (lo mx : ℕ) : Expr :=
  .letE (.call lo (.var 0))
    (.arith .eq (.call mx (.get (.var 1) (.nat 1))) (.nat 0))

/-- The orbit test has polynomial own cost in its degree and input weight. -/
def normOrbitCost (k W : ℕ) : ℕ :=
  loK * (k + 1) ^ 15 + maxK * (k + 1) ^ 3 + 1000 * (W + k + 1)

open Classical in
/-- The orbit program decides the transitivity predicate used by `normMode_spec`. -/
theorem normOrbit_spec {Pg : Program} {f lo mx : ℕ}
    (hf : Pg.funs[f]? = some (normOrbitF lo mx))
    (hlo : Pg.HasAt lo (loFuns lo)) (hmx : Pg.HasAt mx (maxFuns mx))
    {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C)
    (hne : S.dom.Nonempty) {gv : Val} (hgv : GroupValC k gv (groupFin e S.G)) :
    FunDet Pg f (.list [gv, indVal e S.dom]) (boolVal (decide S.Transitive))
      (normOrbitCost k (Val.list [gv, indVal e S.dom]).wt) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨gs, rfl, hgen, hlen⟩ := hgv
  obtain ⟨D, hsub, horb, -, hD⟩ := lo_spec hlo e S.dom_inv hne hgen hlen
  let a := Val.list [encGroup gs, indVal e S.dom]
  let pair := Val.list [indVal e D, indVal e (S.dom \ D)]
  have d0 := Det.call (Det.var' (P := Pg) (env := [a]) (i := 0) rfl) hD
  have hm := max_spec hmx (xs := (List.finRange k).map (indF e (S.dom \ D))) (B := k)
    (by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      have := indF_le_one e (S.dom \ D) j
      have := j.2
      omega) (by simp)
  rw [foldl_max_indF] at hm
  have heq : indVal e (S.dom \ D) = natList ((List.finRange k).map (indF e (S.dom \ D))) :=
    encFun_eq_natList _
  have dp := Det.get' (Det.var' (P := Pg) (env := [a, pair]) (i := 1) rfl) (Det.nat 1)
    (show [indVal e D, indVal e (S.dom \ D)][1]? = some (indVal e (S.dom \ D)) from rfl)
  have dm := Det.call dp (heq ▸ hm)
  have ht := transitive_iff_diff_empty hsub horb
  have deq := Det.arith' (op := .eq) dm (Det.nat 0)
    (z := (decide S.Transitive).toNat) (by
      by_cases h : S.dom \ D = ∅
      · simp [GI.Machine.BinOp.eval, h, ht.mpr h]
      · have hn : ¬ S.Transitive := fun htr => h (ht.mp htr)
        simp [GI.Machine.BinOp.eval, h, hn])
  refine FunDet.intro hf ((Det.letE d0 deq).mono ?_)
  have wD := DomVal.wt_le (domVal_indVal e D)
  have wR := DomVal.wt_le (domVal_indVal e (S.dom \ D))
  have wp := wt_list2_le (indVal e D) (indVal e (S.dom \ D))
  have wb : (Val.nat (decide S.Transitive).toNat).wt ≤ 3 := wt_boolVal_le _
  have wb' : (boolVal (decide S.Transitive)).wt ≤ 3 := wt_boolVal_le _
  have wm : (Val.nat (if S.dom \ D = ∅ then 0 else 1)).wt ≤ 3 := by
    split_ifs <;> exact (wt_nat_le _).trans (by omega)
  have hb := Bool.toNat_le (decide S.Transitive)
  change _ ≤ normOrbitCost k a.wt
  unfold normOrbitCost
  have wpair : pair.wt = (Val.list [indVal e D, indVal e (S.dom \ D)]).wt := rfl
  omega

open Classical in
/-- One orbit computation justifies the common mode guard of `Run.normalize`. -/
theorem normOrbit_mode_spec {Pg : Program} {f lo mx : ℕ}
    (hf : Pg.funs[f]? = some (normOrbitF lo mx))
    (hlo : Pg.HasAt lo (loFuns lo)) (hmx : Pg.HasAt mx (maxFuns mx))
    {Ω C : Type} {k : ℕ} {P : Params} (e : Ω ≃ Fin k) {S : State Ω C}
    (N : NormAbove P S) (j : Fin N.I.k) (hne : S.dom.Nonempty)
    {gv : Val} (hgv : GroupValC k gv (groupFin e N.I.G')) :
    FunAll Pg f (.list [gv, indVal e S.dom]) (fun w cost =>
      ∃ b : Bool, w = boolVal b ∧
        (∀ t, (normMode b = .cont ∧ ¬ (N.child t).Transitive) ∨
          (normMode b = .giant ∧ (N.child t).Transitive)) ∧
        cost ≤ normOrbitCost k (Val.list [gv, indVal e S.dom]).wt) := by
  refine FunAll.mono (normOrbit_spec hf hlo hmx e (N.child j) hne hgv) fun w cost hw => ?_
  refine ⟨decide (N.child j).Transitive, hw.1, ?_, hw.2⟩
  apply normMode_spec
  simp only [decide_eq_true_eq]
  exact Iff.rfl

end GI.Impl
