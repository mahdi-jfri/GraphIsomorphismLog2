module

public import Workspace.Impl.LinVectorTransportCost

@[expose] public section

/-! A vector transporter with a proved empty answer or a representative and
the target stabilizer, computed from the original group and matrix encodings. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 6000 in
theorem linVectorTransport_spec (h : VectorStabilizer) {P : Program} {b j : ℕ}
    (hp : linVectorTransportAt P b j h) (I : VecStabInst) [NeZero I.n]
    (hd : 0 < I.d) (w : Fin I.d → ZMod I.p) :
    FunAll P b (.list [vecStabEnc I, encVec w]) (fun out cost => linVectorTransportOut I w out ∧
      cost ≤ linVectorTransportCost h (Val.list [vecStabEnc I, encVec w]).wt) := by
  let a := Val.list [vecStabEnc I, encVec w]
  let W := a.wt
  let SB := linWreathStabCost h W
  let CB := linVectorTransportChoiceBudget h W
  let TB := linVectorTargetCost h W
  have hn : I.n ≤ W := (linWreathInput_dimensions I w).1
  have ws : (vecStabEnc I).wt < W := wt_le_wt_list (by simp [W, a])
  have wg : (encGroup I.gs).wt < (vecStabEnc I).wt := wt_le_wt_list (by simp [vecStabEnc])
  have wn : (Val.nat I.n).wt < (encGroup I.gs).wt := wt_le_wt_list (by simp [encGroup, encPerms])
  have hstab := linWreathStab_spec h hp.stab I hd w
  have cs := normBound_call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hstab
  apply FunAll.intro hp.entry
  apply EvalAll.letE cs
  intro sv cS hs
  obtain ⟨hsv, wsv, hcS⟩ := hs
  obtain ⟨gs, rfl, hlen, hgens⟩ := hsv
  let raw := Val.list (gs.map encPerm)
  have wraw : raw.wt ≤ SB := wsv
  have hcS' : cS ≤ W + 1 + 2 * SB + 1 := hcS
  have harg : (Val.list [.nat I.n, raw]).wt ≤ linVectorTransportChoiceArg h W := by
    have hh := wt_list2_le (.nat I.n) raw
    unfold linVectorTransportChoiceArg
    change raw.wt ≤ linWreathStabCost h W at wraw
    omega
  have hchoice : FunAll P (b + 73) (.list [.nat I.n, raw]) (fun out cost =>
      linWreathChoiceOut I w out ∧ cost ≤ CB) := by
    refine FunAll.mono (linWreathChoiceGens_spec hp.choice I w gs hlen hgens) ?_
    intro out cost ho
    exact ⟨ho.1, ho.2.trans (linWreathChoiceGensCost_mono harg hn)⟩
  have dsrc := Det.arg' (P := P) (vs := [vecStabEnc I, encVec w]) (rest := [raw]) (j := 0) rfl
  have dgroup := Det.get' dsrc (Det.nat 0) rfl
  have dn := Det.get' dgroup (Det.nat 0) rfl
  have draw := Det.var' (P := P) (env := [a, raw]) (i := 1) rfl
  have darg := (Det.mk2 dn draw).mono (c' := 1000 * (W + SB + 1)) (by
    have hh := wt_list2_le (.nat I.n) raw
    dsimp only [a, W, raw, SB] at *
    omega)
  have cc := normBound_call darg hchoice
  apply EvalAll.letE cc
  intro chosen cC hc
  obtain ⟨hchosen, wchosen, hcC⟩ := hc
  have hcC' : cC ≤ 1000 * (W + SB + 1) + 2 * CB + 1 := hcC
  rcases hchosen with ⟨rfl, hno⟩ | ⟨g, rfl, htrans⟩
  · have dlen := Det.length (Det.var' (P := P) (env := [a, raw, .list []]) (i := 2) rfl)
    have db : Det P [a, raw, .list []]
        (.ite (.length (.var 2))
          (mk2 (.get (.var 2) (.nat 0))
            (.prim j (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
              (.get (arg 0) (.nat 2)) (arg 1)))) .nil)
        (.list []) _ := Det.ite_zero dlen Det.nil
    refine db.post fun cost hcost => ⟨Or.inl ⟨rfl, hno⟩, ?_⟩
    change _ ≤ linVectorTransportCost h W
    dsimp only [linVectorTransportCost]
    dsimp only [SB, CB, TB, a, W] at *
    simp only [List.length_nil, wt_list_nil] at *
    omega
  · let chosen := Val.list [encPerm g.val]
    have wgval : (encPerm g.val).wt ≤ CB := by
      have hh : (encPerm g.val).wt < chosen.wt := wt_le_wt_list (by simp [chosen])
      change chosen.wt ≤ CB at wchosen
      omega
    have dlen := Det.length (Det.var' (P := P) (env := [a, raw, chosen]) (i := 2) rfl)
    have dget := Det.get' (Det.var' (P := P) (env := [a, raw, chosen]) (i := 2) rfl) (Det.nat 0) rfl
    have target := (linVectorTarget_call h hp.prim I w [raw, chosen]).wt_lt
    refine EvalAll.ite dlen (fun vc cl hv => ⟨1, hv.1⟩) ?_
    intro k cl hcl
    have hk : k = 1 := Val.nat.inj hcl.1
    subst k
    simp only [show ¬ (1 = 0) by decide, if_false]
    refine (EvalAll.mk2_last dget target).mono ?_
    intro out cost ho
    obtain ⟨tv, ct, ⟨⟨htv, hct⟩, wtv⟩, rfl, hcost⟩ := ho
    refine ⟨Or.inr ⟨g, tv, rfl, htrans, htv⟩, ?_⟩
    have wtv' : tv.wt ≤ TB := wtv.le.trans hct
    have wpair := wt_list2_le (encPerm g.val) tv
    have hcl' := hcl.2
    change _ ≤ linVectorTransportCost h W
    dsimp only [linVectorTransportCost]
    dsimp only [SB, CB, TB, chosen, a, W] at *
    simp only [List.length_cons, List.length_nil] at *
    omega

/-- The field transporter has one uniform polynomial bit bound in its actual
input, with the cited algorithm's constants fixed by its hypothesis. -/
theorem linVectorTransport_spec_poly (h : VectorStabilizer) :
    ∃ K D : ℕ, ∀ {P : Program} {b j : ℕ}, linVectorTransportAt P b j h →
      ∀ (I : VecStabInst) [NeZero I.n] (hd : 0 < I.d) (w : Fin I.d → ZMod I.p),
      FunAll P b (.list [vecStabEnc I, encVec w]) (fun out cost => linVectorTransportOut I w out ∧
        cost ≤ K * ((Val.list [vecStabEnc I, encVec w]).wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linVectorTransportCost_poly h)
  refine ⟨K, D, ?_⟩
  intro P b j hp I _ hd w
  refine FunAll.mono (linVectorTransport_spec h hp I hd w) fun out cost ho =>
    ⟨ho.1, ho.2.trans (hKD 0 _ _ (Nat.zero_le _) le_rfl)⟩

end GI.Impl
