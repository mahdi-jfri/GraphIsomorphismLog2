import Workspace.Impl.VsQA3
import Workspace.Impl.VsPStep4

/-!
# Step 4 of the analysis and the hand-off

On `[lc, vsPIn s as Lb ccs tcs]` the program `vsQA4E` runs step 4 (`vsPStep4_spec`). On a grow it
returns `[0, ⟨as'⟩]`. On a hand-off it runs the hard case (`hard`); a split is returned as it
is, and a `Q₈` tag goes to the `Q₈` continuation (`q8c`), which returns a split or a grow.

The hard case and the `Q₈` continuation are taken as hypotheses here (`VsQHardHyp`, `VsQ8CHyp`);
the `VsH*` files prove them.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- A correct split. -/
def VsQSplOK {s : VsQSt I} (Tm : ℕ) (w : Val) : Prop :=
  ∃ ts cs lows, w = vsQSplitV ts cs lows ∧ VsQSplitOK s 278 Tm ts cs lows

/-- What step 4 with the hand-off returns: a split, or a grow of `A`. -/
def VsQ4Out [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (as : List (Perm (Fin I.n))) (Tm : ℕ)
    (w : Val) : Prop :=
  VsQSplOK (s := s) Tm w ∨ ∃ as', w = .list [.nat 0, encGroup as'] ∧ VsPGrowOut hs as as'

/-- What the hard case returns: the `Q₈` tag, or a split. -/
def VsQHardOut [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (Lb : List (List (List ℕ)))
    (ccs ys : List (Perm (Fin I.n))) (r Tm : ℕ) (w : Val) : Prop :=
  (∃ (Lo : List (List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) × Perm (Fin I.n)))
      (ks : List (Perm (Fin I.n))),
      w = .list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks] ∧
      VsQOrbL (vsHAlT s) (1 :: ccs) ((vsHB s Lb r ys).map (vsHT s)) Lo ∧
      (∀ h, h ∈ gens ks ↔ h ∈ gens ccs ∧
        vsHAlT s h ((vsHB s Lb r ys).map (vsHT s)) = (vsHB s Lb r ys).map (vsHT s)) ∧
      ks.length ≤ I.n ^ 2 ∧ Lo.length ≤ 24 ∧
      (vsHK s Lb r ys).length = 0) ∨
  VsQSplOK (s := s) Tm w

/-- The hand-off facts: the input of the hard case. -/
structure VsQHand [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (as : List (Perm (Fin I.n)))
    (Lb : List (List (List ℕ))) (ccs tcs ys : List (Perm (Fin I.n))) (r : ℕ) : Prop where
  hyp : VsPHyp hs as Lb ccs
  tmem : ∀ t ∈ tcs, t ∈ gens s.hs
  cov : ∀ h ∈ gens s.hs, ∃ t ∈ tcs, t⁻¹ * h ∈ gens ccs
  tl : tcs.length ≤ vsQD s
  hys : ∀ y ∈ ys, y ∈ gens s.hs
  hysC : ∀ y ∈ ys, y ∈ gens ccs
  ysl : ys.length ≤ vsQD s ^ 2
  rp : r.Prime
  rn : r ≤ I.n
  hard : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as))
    (vsPBar hs (gens ys) ⊔ vsMScal (vsPBar hs (gens as))) r

/-- The hard case, as a hypothesis. -/
def VsQHardHyp [Fact I.p.Prime] (P : Program) (hard CH Tm : ℕ) {s : VsQSt I} (hs : VsQStOK s) : Prop :=
  ∀ (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ))) (ccs tcs ys : List (Perm (Fin I.n))) (r : ℕ),
    VsQHand hs as Lb ccs tcs ys r → ¬ s.Ab →
    FunAll P hard (.list [vsQLCV s, vsPGIn s as Lb ccs tcs ys r])
      (fun w c => VsQHardOut hs Lb ccs ys r Tm w ∧ c ≤ CH)

/-- The `Q₈` continuation, as a hypothesis. -/
def VsQ8CHyp [Fact I.p.Prime] (P : Program) (q8c CQ Tm : ℕ) {s : VsQSt I} (hs : VsQStOK s) : Prop :=
  ∀ (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ))) (ccs tcs ys : List (Perm (Fin I.n))) (r : ℕ)
    (Lo : List (List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) × Perm (Fin I.n)))
    (ks : List (Perm (Fin I.n))),
    VsQHand hs as Lb ccs tcs ys r → ¬ s.Ab →
    VsQOrbL (vsHAlT s) (1 :: ccs) ((vsHB s Lb r ys).map (vsHT s)) Lo →
    (∀ h, h ∈ gens ks ↔ h ∈ gens ccs ∧
        vsHAlT s h ((vsHB s Lb r ys).map (vsHT s)) = (vsHB s Lb r ys).map (vsHT s)) →
    ks.length ≤ I.n ^ 2 → Lo.length ≤ 24 → (vsHK s Lb r ys).length = 0 →
    FunAll P q8c (.list [vsQLCV s, vsPGIn s as Lb ccs tcs ys r,
        .list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks]])
      (fun w c => VsQ4Out hs as Tm w ∧ c ≤ CQ)

/-- Step 4 with the hand-off, on `[lc, vsPIn …]`. -/
def vsQA4E (st4 hard q8c : ℕ) : Expr :=
  .letE (.call st4 (arg 1))
  (.ite (.get (.var 1) (.nat 0))
    (.letE (.call hard (mk2 (arg 0) (.get (.var 1) (.nat 1))))
      (.ite (.arith .eq (.get (.var 2) (.nat 0)) (.nat 2))
        (.call q8c (mk3 (arg 0) (.get (.var 1) (.nat 1)) (.var 2)))
        (.var 2)))
    (.var 1))

set_option maxHeartbeats 8000000 in
/-- **Step 4 with the hand-off.** -/
theorem vsQA4_spec [Fact I.p.Prime] {P : Program} {f st4 hard q8c CH CQ : ℕ}
    (hf : P.funs[f]? = some (vsQA4E st4 hard q8c)) {hn : NormalClosure} {hd : DerivedSubgroup}
    {x : VsPStep4X}
    (hst4 : P.funs[st4]? = some (vsPStep4E x.ctxP x.der x.x2.x3.x4.ab x.x2.x3.x4.grow x.x2.x3.tl x.s2))
    (L4 : VsPStep4Lay P hn hd x) {Cφ : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.x2.x3.x4.d.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hnab : ¬ s.Ab)
    (hHard : VsQHardHyp P hard CH Tm hs) (hQ8 : VsQ8CHyp P q8c CQ Tm hs)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) (htmem : ∀ t ∈ tcs, t ∈ gens s.hs)
    (hcov : ∀ h ∈ gens s.hs, ∃ t ∈ tcs, t⁻¹ * h ∈ gens ccs) (htl : tcs.length ≤ vsQD s) :
    FunAll P f (.list [vsQLCV s, vsPIn s as Lb ccs tcs]) (fun w c => VsQ4Out hs as Tm w ∧
      c ≤ 64 * (vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * (vsPIn s as Lb ccs tcs).wt +
        CH + CQ) + 100 * ((vsQLCV s).wt + (vsPIn s as Lb ccs tcs).wt) + 10000) := by
  set lc := vsQLCV s
  set In := vsPIn s as Lb ccs tcs
  set T4 := vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * In.wt
  set B := T4 + CH + CQ
  set A := Val.list [lc, In]
  have a0 : ∀ rest, Det P (A :: rest) (arg 0) lc (2 * A.wt + 0 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, In]) (rest := rest) (j := 0) rfl
  have a1 : ∀ rest, Det P (A :: rest) (arg 1) In (2 * A.wt + 1 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, In]) (rest := rest) (j := 1) rfl
  have wA := wt_list2_le lc In
  have eA : A.wt = (Val.list [lc, In]).wt := rfl
  have eIn : (vsPIn s as Lb ccs tcs).wt = In.wt := rfl
  have elc : (vsQLCV s).wt = lc.wt := rfl
  have eT4 : vsPStep4Cost (I := I) Cφ hn hd S + 10 ^ 7 * (vsPN S + 1) * (vsPIn s as Lb ccs tcs).wt = T4 := rfl
  have eB : B = T4 + CH + CQ := rfl
  have hlcA : lc.wt < A.wt := wt_le_wt_list (by simp [A])
  refine FunAll.intro hf (EvalAll.letE (Ra := fun w c => VsPOut hs as Lb ccs tcs w ∧ c ≤ 2 * A.wt + 7 + 2 * T4 ∧
      w.wt ≤ T4) (EvalAll.call_funAll (a1 []) fun v ca hv => ?_) fun v1 c1 hv1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine (vsPStep4_spec hst4 L4 hphi hS hs hH).wt_lt.mono fun w c hw => ?_
    obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
    exact ⟨hout, by omega, by omega⟩
  obtain ⟨hout, hc1, hw1⟩ := hv1
  rcases hout with ⟨as', rfl, hgr⟩ | ⟨ys, r, rfl, hys, hysC, hysl, hrp, hrn, hhard⟩
  · -- a grow
    have d0 := Det.get' (Det.var' (P := P) (env := [A, Val.list [.nat 0, encGroup as']]) (i := 1) rfl)
      (Det.nat 0) (show [Val.nat 0, encGroup as'][0]? = some (.nat 0) from rfl)
    refine Det.post (Det.ite_zero d0 (Det.var' (P := P) (env := [A, Val.list [.nat 0, encGroup as']]) (i := 1) rfl))
      fun c hc => ⟨Or.inr ⟨as', rfl, hgr⟩, ?_⟩
    have := wt_nat_le 0
    have hw0 : (Val.nat 0).wt < (Val.list [.nat 0, encGroup as']).wt := wt_le_wt_list (by simp)
    omega
  · -- the hand-off
    set G := vsPGIn s as Lb ccs tcs ys r
    set V1 := Val.list [.nat 1, G]
    have eV1 : (Val.list [Val.nat 1, G]).wt = V1.wt := rfl
    have hHand : VsQHand hs as Lb ccs tcs ys r := ⟨hH, htmem, hcov, htl, hys, hysC, hysl, hrp, hrn, hhard⟩
    have d0 := Det.get' (Det.var' (P := P) (env := [A, V1]) (i := 1) rfl)
      (Det.nat 0) (show [Val.nat 1, G][0]? = some (.nat 1) from rfl)
    have dG := Det.get' (Det.var' (P := P) (env := [A, V1]) (i := 1) rfl)
      (Det.nat 1) (show [Val.nat 1, G][1]? = some G from rfl)
    have hGw : G.wt < V1.wt := wt_le_wt_list (by simp [V1])
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
    refine (EvalAll.vsQ_ite_pos' (R := fun w c => VsQ4Out hs as Tm w ∧ c ≤ 16 * B + 40 * A.wt + 40 * V1.wt + 1000 ∧
      w.wt ≤ B) d0 one_ne_zero ?_).mono fun w c hw => ?_
    swap
    · obtain ⟨ct, ⟨hout, hct, hwB⟩, hc⟩ := hw
      refine ⟨hout, ?_⟩
      clear_value lc In T4 B A G V1

      omega
    refine EvalAll.letE (Ra := fun w c => VsQHardOut hs Lb ccs ys r Tm w ∧ c ≤ 8 * A.wt + 8 * V1.wt + 2 * CH + 100 ∧
      w.wt ≤ CH) (EvalAll.call_funAll (Det.mk2 (a0 [V1]) dG) fun v ca hv => ?_) fun v2 c2 hv2 => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (hHard as Lb ccs tcs ys r hHand hnab).wt_lt.mono fun w c hw => ?_
      obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
      have w2 := wt_list2_le lc G
      refine ⟨hout, ?_, by omega⟩
      clear_value lc In T4 B A G V1
      omega
    obtain ⟨hout2, hc2, hw2⟩ := hv2
    rcases hout2 with ⟨Lo, ks, rfl, hLo, hks, hksl, hLol, hK0⟩ | ⟨ts, cs, lows, rfl, hok⟩
    · -- the `Q₈` tag
      set V2 := Val.list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks]
      set E2 := [A, V1, V2]
      have de := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := E2) (i := 2) rfl) (Det.nat 0)
        (show [Val.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks][0]? = some (.nat 2) from rfl))
        (Det.nat (P := P) (env := E2) 2) rfl
      have dG2 := Det.get' (Det.var' (P := P) (env := E2) (i := 1) rfl)
        (Det.nat 1) (show [Val.nat 1, G][1]? = some G from rfl)
      refine (EvalAll.vsQ_ite_pos' (R := fun w c => VsQ4Out hs as Tm w ∧
        c ≤ 8 * A.wt + 8 * V1.wt + 8 * CH + 2 * CQ + 300 ∧ w.wt ≤ CQ) de (by decide) ?_).mono fun w c hw => ?_
      · refine EvalAll.call_funAll (Det.mk3 (a0 [V1, V2]) dG2 (Det.var' (P := P) (env := E2) (i := 2) rfl))
          fun v ca hv => ?_
        obtain ⟨rfl, hca⟩ := hv
        refine (hQ8 as Lb ccs tcs ys r Lo ks hHand hnab hLo hks hksl hLol hK0).wt_lt.mono fun w c hw => ?_
        obtain ⟨⟨hout, hc⟩, hwc⟩ := hw
        have w3 := wt_list3_le lc G V2
        refine ⟨hout, ?_, by omega⟩
        clear_value lc In T4 B A G V1

        omega
      · obtain ⟨ct, ⟨hout, hct, hwq⟩, hc⟩ := hw
        refine ⟨hout, ?_, by omega⟩
        have := wt_nat_le (GI.Machine.BinOp.eval .eq 2 2)
        have hev : GI.Machine.BinOp.eval .eq 2 2 = 1 := rfl
        have hv2 : (Val.nat 2).wt < V2.wt := wt_le_wt_list (by simp [V2])
        have eV2 : (Val.list [Val.nat 2, Val.list (List.map (fun q => encPerm q.2) Lo), encGroup ks]).wt =
          V2.wt := rfl
        clear_value lc In T4 B A G V1 V2
        omega
    · -- a split
      set E2 := [A, V1, vsQSplitV ts cs lows]
      have hv1 : (Val.nat 1).wt < (vsQSplitV ts cs lows).wt := wt_le_wt_list (by simp [vsQSplitV])
      have de := Det.arith' (op := .eq) (Det.get' (Det.var' (P := P) (env := E2) (i := 2) rfl) (Det.nat 0)
        (show [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows][0]? = some (.nat 1) from rfl))
        (Det.nat (P := P) (env := E2) 2) rfl
      have hev : GI.Machine.BinOp.eval .eq 1 2 = 0 := rfl
      rw [hev] at de
      refine Det.post (Det.ite_zero de (Det.var' (P := P) (env := E2) (i := 2) rfl)) fun c hc =>
        ⟨Or.inl ⟨ts, cs, lows, rfl, hok⟩, ?_, by omega⟩
      clear_value lc In T4 B A G V1
      have eS : (Val.list [Val.nat 1, Val.list (List.map encPerm ts), encGroup cs, vsQLowsV lows]).wt =
        (vsQSplitV ts cs lows).wt := rfl
      omega

end GI.Impl
