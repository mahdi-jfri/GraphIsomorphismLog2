module

public import Workspace.Impl.LinListPick
public import Workspace.Impl.LinObjectConfigMath
public import Workspace.Impl.GenNormGlue

@[expose] public section

/-! Extract an offset permutation from a row of local transporter answers.
The row certificate fixes its effect on the whole piece. -/
namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

def linObjectOffsetRowF (pick : ℕ) : Expr :=
  .letE (.call pick (.var 0)) (.get (.var 1) (.nat 0))

def linObjectOffsetRowFuns (b : ℕ) : List Expr :=
  [linObjectOffsetRowF (b + 1)] ++ linListPickFuns (b + 1)

theorem linObjectOffsetRowFuns_length (b : ℕ) : (linObjectOffsetRowFuns b).length = 6 := rfl

def linObjectOffsetRowCost (W : ℕ) : ℕ := 100000 * (W + linListPickCost W + 1)

theorem linObjectOffsetRowCost_poly : PBU (fun _ W _ => linObjectOffsetRowCost W) := by
  unfold linObjectOffsetRowCost linListPickCost
  norm_poly

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectOffsetRow_spec {P : Program} {b n : ℕ}
    (h : P.HasAt b (linObjectOffsetRowFuns b))
    (xs : List Val) (R : Equiv.Perm (Fin n) → Prop)
    (hxs : ∀ v ∈ xs, v = .list [] ∨ ∃ (a : Equiv.Perm (Fin n)) (gs : List (Equiv.Perm (Fin n))),
      v = .list [encPerm a, encGroup gs] ∧ R a)
    (hex : ∃ v ∈ xs, v ≠ .list []) :
    FunAll P b (.list xs) (fun out cost => (∃ a, out = encPerm a ∧ R a) ∧
      cost ≤ linObjectOffsetRowCost (Val.list xs).wt) := by
  have hl : ∀ v ∈ xs, ∃ ys, v = .list ys := by
    intro v hv
    rcases hxs v hv with he | ⟨a, gs, he, _⟩
    · exact ⟨[], he⟩
    · exact ⟨_, he⟩
  have hn : ∃ v ∈ xs, linListNonempty v = true := by
    obtain ⟨v, hv, hne⟩ := hex
    rcases hxs v hv with he | ⟨a, gs, rfl, _⟩
    · exact False.elim (hne he)
    · exact ⟨_, hv, rfl⟩
  have hs : FunAll P (b + 1) (.list xs) (fun out cost =>
      (out ∈ xs ∧ linListNonempty out = true) ∧ cost ≤ linListPickCost (Val.list xs).wt) :=
    (linListPick_spec h.right xs hl hn).mono fun out cost ho => ⟨⟨ho.1, ho.2.1⟩, ho.2.2⟩
  have dc := Det.var' (P := P) (env := [.list xs]) (i := 0) rfl
  apply FunAll.intro h.left.single
  apply EvalAll.letE (normBound_call dc hs)
  intro v ca hv
  obtain ⟨⟨hmem, hnon⟩, wv, hca⟩ := hv
  rcases hxs v hmem with he | ⟨a, gs, rfl, ha⟩
  · simp [he, linListNonempty] at hnon
  · have dout := Det.get' (Det.var' (P := P)
      (env := [.list xs, .list [encPerm a, encGroup gs]]) (i := 1) rfl) (Det.nat 0) rfl
    refine dout.post fun cost hc => ⟨⟨a, rfl, ha⟩, ?_⟩
    have wa : (encPerm a).wt < (Val.list [encPerm a, encGroup gs]).wt :=
      wt_le_wt_list (by simp)
    have wz : (Val.nat 0).wt = 2 := rfl
    unfold linObjectOffsetRowCost
    omega

theorem linObjectOffsetRow_coordinate {n : ℕ} {Q Ω : Type*} [CommGroup Q]
    [RAct (Equiv.Perm (Fin n)) Ω] (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (Y Z T : Multiset Ω) (hZ : Conf A Y Z) (hT : T ∈ pieces A Y)
    (hker : π.ker ≤ (Aut A T).subgroupOf A)
    (a : Equiv.Perm (Fin n)) (ha : a ∈ A) (he : T ↼ a = partAt A Z T) :
    (linObjectGroupImage A π (Aut A T)).mkQ (Additive.ofMul (π ⟨a, ha⟩)) =
      (linObjectGroupImage A π (Aut A T)).mkQ
        (Additive.ofMul (π (linIntoSubgroup A (coord A Z T)))) := by
  apply (linObject_mkQ_eq_iff _ _ _).mpr
  apply (linObject_act_eq_iff_image A π T hker ⟨a, ha⟩ _).mp
  have hh := linIntoSubgroup_val A _ (coord_spec hZ hT).1
  change (linIntoSubgroup A (coord A Z T)).val = coord A Z T at hh
  rw [hh]
  exact he.trans (coord_spec hZ hT).2

end GI.Impl
