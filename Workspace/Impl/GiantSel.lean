import Workspace.Impl.GiantNat

/-!
# The selector of `GiantStep`

The selector decides the row case `RowCase α S L` (`Cases.row`, `Cases.agg`) for the supplied
labels `L`, on the input `[sv, lv]` of `GiantStep`. The row case has three parts, and each of
them is decided exactly:

* `q > N^α` with `α = 2/5`: this holds exactly when `N² < q⁵` (`rpow_α_lt_iff`);
* a natural one-label map exists: this holds exactly when the block size is `h = 1` and the
  kernel of the labels is transitive on each block fiber (`natural_iff`, for `q ≥ 5` and a
  nonempty domain); the second part is the test `natTest_spec`, which uses the cited
  **Preimage** task once;
* no retained rows, or the row degree `m` is below `q`: read from the state value.

The selector first computes a number `bad` (`badE`), which is `0` exactly when `h = 1`,
`N² < q⁵` and the rows test passes. It returns `1` (aggregation) when `bad ≠ 0`. Otherwise it
runs the natural-map test and returns `0` (row case) when the test answers `0`, and `1`
otherwise. The power `q⁵` is computed only when `h = 1`; then `q ≤ k` (`q_le_of_h_one`), so the
cost is a polynomial in the weight of the input, in `k` and in `N`.

The main result is `giantSel_spec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens sumToFin)

variable {Ω C : Type} {k : ℕ}

/-! ### With one label per point, `q` is at most the number of points -/

/-- When the blocks are single labels and the domain is not empty, every label is the block of
some point of the domain, so there are at most `|Ω|` labels. -/
theorem q_le_of_h_one [Finite Ω] {S : State Ω C} {L : GiantLabels S} (J : JohnsonBlocks S L)
    (hh : J.h = 1) (hne : S.dom.Nonempty) : L.q ≤ Nat.card Ω := by
  classical
  obtain ⟨v0, hv0⟩ := hne
  -- every block fiber has `f ≥ 1` points, since the fiber of the block of `v0` contains `v0`
  have hf : 1 ≤ J.f := by
    rw [← J.fibers (J.p ⟨v0, hv0⟩) (J.card _)]
    exact Nat.card_pos_iff.mpr ⟨⟨⟨⟨v0, hv0⟩, rfl⟩⟩, inferInstance⟩
  have hfib : ∀ i : Fin L.q, Nonempty {v : S.dom // J.p v = {i}} := fun i =>
    (Nat.card_pos_iff.mp (by rw [J.fibers {i} (by simp [hh])]; omega)).1
  let pt : Fin L.q → Ω := fun i => ((Classical.choice (hfib i)).1 : Ω)
  have hpt : Function.Injective pt := by
    intro i j hij
    have hi := (Classical.choice (hfib i)).2
    have hj := (Classical.choice (hfib j)).2
    have : (Classical.choice (hfib i)).1 = (Classical.choice (hfib j)).1 := Subtype.ext hij
    rw [this, hj] at hi
    exact (Finset.singleton_inj.mp hi).symm
  have := Nat.card_le_card_of_injective pt hpt
  simpa using this

/-! ### The program -/

/-- The entry `i` of the state value. -/
def gsSV (i : ℕ) : Expr := .get natSV (.nat i)

/-- The rows test, `0` when it passes: `rv = []`, or `rv = [[m, rows, cols]]` with `m < q`. -/
def gsRowsE : Expr :=
  .ite (.length (gsSV 6))
    (.ite (.arith .lt (.get (.get (gsSV 6) (.nat 0)) (.nat 0)) natQ) (.nat 0) (.nat 1))
    (.nat 0)

/-- `bad`: `0` exactly when `h = 1`, `N² < q⁵` and the rows test passes. -/
def gsBadE : Expr :=
  .ite (.arith .eq (.get natLV (.nat 3)) (.nat 1))
    (.ite (.arith .lt (powE (gsSV 9) 2) (powE natQ 5)) gsRowsE (.nat 1))
    (.nat 1)

/-- The body of the selector, with the natural-map test at `nt`. -/
def giantSelBody (nt : ℕ) : Expr :=
  .letE gsBadE (.ite (.var 1) (.nat 1) (.ite (.call nt (.var 0)) (.nat 1) (.nat 0)))

/-- The selector at base `b` (73 functions), with the cited preimage primitive at `jpre`. -/
def giantSelFuns (b jpre : ℕ) : List Expr := giantSelBody (b + 1) :: natFuns (b + 1) jpre

/-! ### The value `bad` -/

section Bad

variable {P : Program} {sv lv : Val} {svs : List Val}

theorem gsSV_det (rest : List Val) (hsv : sv = .list svs) {i : ℕ} {u : Val} (hi : svs[i]? = some u) :
    Det P (.list [sv, lv] :: rest) (gsSV i) u (3 * (Val.list [sv, lv]).wt + i + 10) := by
  subst hsv
  have h := Det.get' (natSV_det rest (P := P) (lv := lv) rfl) (Det.nat i) hi
  refine h.mono ?_
  have h1 := wt_le_wt_list (vs := [Val.list svs, lv]) (v := .list svs) (by simp)
  have h2 := wt_le_wt_list (vs := svs) (v := u) (List.mem_of_getElem? hi)
  omega

/-- **The rows test.** -/
theorem gsRows_det (e : Ω ≃ Fin k) {S : State Ω C} (L : SuppliedLabels S) {rv : Val}
    (hsv : sv = .list svs) (h6 : svs[6]? = some rv) (hr : OptVal (RowValC e) rv S.rows)
    (hlv : LabValStd e S lv L) :
    ∃ rb, rb ≤ 1 ∧ (rb = 0 ↔ ∀ R, S.rows = some R → R.m < L.q) ∧
      Det P [.list [sv, lv]] gsRowsE (.nat rb) (20 * (Val.list [sv, lv]).wt + 100) := by
  obtain ⟨ps, hlvE, -, -, -⟩ := hlv
  have dQ := natLVget_det (P := P) (sv := sv) [] hlvE (i := 0) (u := .nat L.q) rfl
  have dR := gsSV_det (P := P) (lv := lv) [] hsv h6
  have hRw : rv.wt < (Val.list [sv, lv]).wt := by
    have h1 := wt_le_wt_list (vs := [sv, lv]) (v := sv) (by simp)
    have h2 : rv.wt < sv.wt := by
      rw [hsv]; exact wt_le_wt_list (vs := svs) (v := rv) (List.mem_of_getElem? h6)
    omega
  cases hR : S.rows with
  | none =>
    rw [hR] at hr
    have hr' : rv = .list [] := hr
    subst hr'
    refine ⟨0, by omega, by simp, ?_⟩
    have dl := Det.length dR
    refine (Det.ite_zero (t := .ite (.arith .lt (.get (.get (gsSV 6) (.nat 0)) (.nat 0)) natQ)
      (.nat 0) (.nat 1)) dl (Det.nat 0)).mono ?_
    have := wt_nat_le 0
    simp only [List.length_nil]
    omega
  | some R =>
    rw [hR] at hr
    obtain ⟨u, ⟨rr, cv, -, -, hu⟩, rfl⟩ := hr
    have dl := Det.length dR
    have du := Det.get' dR (Det.nat 0) (vs := [u]) (v := u) rfl
    rw [hu] at du
    have dm := Det.get' du (Det.nat 0) (vs := [.nat R.m, rr, cv]) (v := .nat R.m) rfl
    have dlt := Det.arith' (op := .lt) dm dQ rfl
    have huw : u.wt < (Val.list [u]).wt := wt_le_wt_list (by simp)
    have hmw : (Val.nat R.m).wt < u.wt := by rw [hu]; exact wt_le_wt_list (by simp)
    rw [← hu] at dlt
    have h0 := wt_nat_le 0
    have h1 := wt_nat_le 1
    by_cases hm : R.m < L.q
    · have hz : BinOp.eval .lt R.m L.q = 1 := by simp [BinOp.eval, hm]
      rw [hz] at dlt
      have d2 := Det.ite_pos (e := .nat 1) dlt one_ne_zero (Det.nat 0)
      have d3 := Det.ite_pos (e := .nat 0) dl (by simp) d2
      refine ⟨0, by omega, ?_, d3.mono ?_⟩
      · simp only [true_iff]
        intro R' hR'
        cases hR'
        exact hm
      · simp only [List.length_singleton]
        omega
    · have hz : BinOp.eval .lt R.m L.q = 0 := by simp [BinOp.eval, hm]
      rw [hz] at dlt
      have d2 := Det.ite_zero (t := .nat 0) dlt (Det.nat 1)
      have d3 := Det.ite_pos (e := .nat 0) dl (by simp) d2
      refine ⟨1, le_rfl, ?_, d3.mono ?_⟩
      · simp only [one_ne_zero, false_iff, not_forall]
        exact ⟨R, rfl, hm⟩
      · simp only [List.length_singleton]
        omega

/-- The constant of the cost of `bad`. -/
def badK : ℕ := 1000

/-- **The value `bad`.** It is `0` exactly when `h = 1`, `N² < q⁵` and the rows test passes. -/
theorem gsBad_det (e : Ω ≃ Fin k) {S : State Ω C} (L : SuppliedLabels S) {rv : Val}
    (hsv : sv = .list svs) (h6 : svs[6]? = some rv) (h9 : svs[9]? = some (.nat S.N))
    (hr : OptVal (RowValC e) rv S.rows) (hlv : LabValStd e S lv L)
    (hqk : L.con.blocks.h = 1 → L.q ≤ k) :
    ∃ bad, bad ≤ 1 ∧ (bad = 0 ↔ L.con.blocks.h = 1 ∧ S.N ^ 2 < L.q ^ 5 ∧
        ∀ R, S.rows = some R → R.m < L.q) ∧
      Det P [.list [sv, lv]] gsBadE (.nat bad)
        (badK * ((Val.list [sv, lv]).wt + k + S.N + 2) ^ 5) := by
  have hlv' := hlv
  obtain ⟨ps, hlvE, -, -, -⟩ := hlv
  set A := Val.list [sv, lv] with hA
  set T := A.wt + k + S.N + 2 with hT
  have dH := natLVget_det (P := P) (sv := sv) [] hlvE (i := 3) (u := .nat L.con.blocks.h) rfl
  have dQ := natLVget_det (P := P) (sv := sv) [] hlvE (i := 0) (u := .nat L.q) rfl
  have dN := gsSV_det (P := P) (lv := lv) [] hsv h9
  have hT2 : 2 ≤ T := by omega
  have hAw : (Val.list [sv, lv]).wt = A.wt := rfl
  have hT5 : T ≤ T ^ 5 := Nat.le_self_pow (by norm_num) _
  have hT32 : 2 ^ 5 ≤ T ^ 5 := Nat.pow_le_pow_left hT2 5
  have h0 := wt_nat_le 0
  have h1 := wt_nat_le 1
  by_cases hh : L.con.blocks.h = 1
  · have dEq := Det.arith' (op := .eq) dH (Det.nat 1) (z := 1) (by simp [BinOp.eval, hh])
    have hq := hqk hh
    have dpN := Det.powE dN 2
    have dpQ := Det.powE dQ 5
    have hN2 : (S.N + 1) ^ 2 ≤ T ^ 5 :=
      (Nat.pow_le_pow_left (show S.N + 1 ≤ T by omega) 2).trans
        (Nat.pow_le_pow_right (by omega) (by norm_num))
    have hQ5 : (L.q + 1) ^ 5 ≤ T ^ 5 := Nat.pow_le_pow_left (by omega) 5
    by_cases hlt : S.N ^ 2 < L.q ^ 5
    · have dlt := Det.arith' (op := .lt) dpN dpQ (z := 1) (by simp [BinOp.eval, hlt])
      obtain ⟨rb, hrb1, hrb, dR⟩ := gsRows_det (P := P) e L hsv h6 hr hlv'
      have d2 := Det.ite_pos (e := .nat 1) dlt one_ne_zero dR
      have d3 := Det.ite_pos (e := .nat 1) dEq one_ne_zero d2
      refine ⟨rb, hrb1, ?_, d3.mono ?_⟩
      · rw [hrb]; simp [hh, hlt]
      · have := wt_nat_le rb
        unfold badK
        omega
    · have dlt := Det.arith' (op := .lt) dpN dpQ (z := 0) (by simp [BinOp.eval, hlt])
      have d2 := Det.ite_zero (t := gsRowsE) dlt (Det.nat 1)
      have d3 := Det.ite_pos (e := .nat 1) dEq one_ne_zero d2
      refine ⟨1, le_rfl, by simp [hlt], d3.mono ?_⟩
      unfold badK
      omega
  · have dEq := Det.arith' (op := .eq) dH (Det.nat 1) (z := 0) (by simp [BinOp.eval, hh])
    have d3 := Det.ite_zero (t := .ite (.arith .lt (powE (gsSV 9) 2) (powE natQ 5)) gsRowsE
      (.nat 1)) dEq (Det.nat 1)
    refine ⟨1, le_rfl, by simp [hh], d3.mono ?_⟩
    unfold badK
    omega

end Bad

/-! ### The specification -/

/-- **The cost bound of the selector**, for an input of weight at most `W`, on `k` positions,
in a phase of size `N`: one preimage call on at most `natPB T` cells, and a polynomial in `T`,
where `T = W + 2k + N + 4`. -/
noncomputable def giantSelCost (hpre : GI.Cited.Preimage) (W k N : ℕ) : ℕ :=
  (preimagePrim hpre).boundSize (natPB (W + 2 * k + N + 4)) +
    (natCostK + badK + 10) * (W + 2 * k + N + 4) ^ 16

theorem boundSize_natPB_mono (p : Prim) {a b : ℕ} (h : a ≤ b) :
    p.boundSize (natPB a) ≤ p.boundSize (natPB b) := by
  unfold Prim.boundSize natPB
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by have := Nat.pow_le_pow_left h 6; omega) _)

/-- With more points than `N^γ`, the domain is not empty. -/
theorem dom_nonempty_of_large {S : State Ω C} (h : (S.N : ℝ) ^ P₀.γ < S.size) :
    S.dom.Nonempty := by
  have hpos : 0 < S.size := by
    have : (0 : ℝ) ≤ (S.N : ℝ) ^ P₀.γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact_mod_cast this.trans_lt h
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨x, hx⟩

/-- **The selector of `GiantStep` meets its specification**: on `[sv, lv]` it returns `0` when
the row case holds for the supplied labels, and `1` otherwise. It uses the cited **Preimage**
task (`hpre`) through the primitive at `jpre`. Its cost is at most `giantSelCost`, which the
interface must allow as the work `selW .giant` of the selector (`hW`). -/
theorem giantSel_spec (I : Iface) (Pg : Program) (hpre : GI.Cited.Preimage) {b jpre : ℕ}
    (h : Pg.HasAt b (giantSelFuns b jpre)) (hj : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hLab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
      (L : SuppliedLabels S), I.LabVal e S lv L → LabValStd e S lv L)
    (hW : ∀ {Ω C : Type} (S : State Ω C),
      (giantSelCost hpre (I.inW .giant S) (Nat.card Ω) S.N : ℝ) ≤ I.selW .giant S) :
    I.SelSpec Pg .giant I.giantCases b := by
  intro Ω C S k e c hc v hv hg
  have hv0 := hv
  obtain ⟨sv, lv, L, rfl, hcan, hlab, hq0, -⟩ := hv
  have hlv := hLab e S lv L hlab
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨-, -, -, hsize, -, -⟩ := hg
  have hne := dom_nonempty_of_large hsize
  have hq5 : 5 ≤ L.q := by
    have : P₀.q₀ = 2064 := rfl
    omega
  have hk := Iface.card_eq e
  have hqk : L.con.blocks.h = 1 → L.q ≤ k := fun hh => hk ▸ q_le_of_h_one _ hh hne
  -- the input
  have hAW : (Val.list [sv, lv]).wt ≤ I.inW .giant S := Iface.InVal.wt_le (by simp) hv0
  obtain ⟨gv, dv, xv, yv, hhv, rv, -, -, -, -, -, hr, hsvE⟩ := hcan.val
  obtain ⟨bad, hbad1, hbad, dbad⟩ := gsBad_det (P := Pg) e L hsvE rfl rfl hr hlv hqk
  have hentry : Pg.funs[b]? = some (giantSelBody (b + 1)) := by
    simpa [giantSelFuns] using h 0 (by simp [giantSelFuns])
  have hnat : NatAt Pg (b + 1) jpre := natAt_of_hasAt (by
    have := h.right (A := [giantSelBody (b + 1)]) (B := natFuns (b + 1) jpre)
    simpa [Nat.add_comm] using this)
  -- the case facts
  have hrow : RowCase P₀.α S L ↔ (L.con.blocks.h = 1 ∧ S.N ^ 2 < L.q ^ 5 ∧
      ∀ R, S.rows = some R → R.m < L.q) ∧
      ∀ v w : S.dom, L.con.blocks.p v = L.con.blocks.p w → KerRel S L.toGiantLabels v w := by
    unfold RowCase
    rw [rpow_α_lt_iff, natural_iff L.con.blocks hq5 hne]
    tauto
  set A := Val.list [sv, lv] with hA
  set W := I.inW .giant S with hWdef
  have hW' := hW S
  rw [hk, ← hWdef] at hW'
  have hsel : ∀ x : ℕ, (x : ℝ) ≤ giantSelCost hpre W k S.N → (x : ℝ) ≤ I.selB .giant S A := by
    intro x hx
    simp only [Iface.selB, reduceCtorEq, if_false]
    exact hx.trans (hW'.trans (le_max_right _ _))
  have hT : A.wt + k + S.N + 2 ≤ W + 2 * k + S.N + 4 := by omega
  have hT16 : (A.wt + k + S.N + 2) ^ 5 ≤ (W + 2 * k + S.N + 4) ^ 16 :=
    (Nat.pow_le_pow_left hT 5).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hbadc := Nat.mul_le_mul_left badK hT16
  have hT1 : W + 2 * k + S.N + 4 ≤ (W + 2 * k + S.N + 4) ^ 16 := Nat.le_self_pow (by norm_num) _
  have h0 := wt_nat_le 0
  have h1 := wt_nat_le 1
  refine FunAll.intro hentry (EvalAll.letE dbad fun w ca hw => ?_)
  obtain ⟨rfl, hca⟩ := hw
  have dV1 := Det.var' (P := Pg) (env := [A, .nat bad]) (i := 1) (v := .nat bad) rfl
  refine EvalAll.ite dV1 (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  cases hx
  by_cases hb0 : bad = 0
  · -- run the natural-map test
    subst hb0
    rw [if_pos rfl]
    obtain ⟨hh, hlt, hrows⟩ := hbad.mp rfl
    have hq := hqk hh
    have hcall := EvalAll.call_funAll (P := Pg) (env := [A, .nat 0]) (f := b + 1)
      (Q := fun w c => ∃ t, w = .nat t ∧ t ≤ 1 ∧ (t = 0 ↔ ∀ v w : S.dom,
        L.con.blocks.p v = L.con.blocks.p w → KerRel S L.toGiantLabels v w) ∧
        c ≤ A.wt + 1 + ((preimagePrim hpre).boundSize (natPB (A.wt + k + L.q + 2)) +
          natCostK * (A.wt + k + L.q + 2) ^ 16) + w.wt + 1)
      (Det.var' (i := 0) rfl) fun v' cv hv' => by
        obtain ⟨rfl, hcv⟩ := hv'
        exact (natTest_spec hpre hnat hj e L hsvE rfl hlv hh (by omega)).mono
          fun w c ⟨t, hw, ht1, ht, hc'⟩ => ⟨t, hw, ht1, ht, by
            have hc'' : c ≤ (preimagePrim hpre).boundSize (natPB (A.wt + k + L.q + 2)) +
                natCostK * (A.wt + k + L.q + 2) ^ 16 := hc'
            omega⟩
    refine EvalAll.ite hcall (fun _ _ h => by obtain ⟨t, ht, -⟩ := h; exact ⟨t, ht⟩)
      fun y cy hy => ?_
    obtain ⟨t, hty, ht1, ht, hcy⟩ := hy
    have hty' : y = t := by injection hty
    subst y
    have hT0 : A.wt + k + L.q + 2 ≤ W + 2 * k + S.N + 4 := by omega
    have hpb := boundSize_natPB_mono (preimagePrim hpre) hT0
    have hT0' := Nat.mul_le_mul_left natCostK (Nat.pow_le_pow_left hT0 16)
    have htw := wt_nat_le t
    by_cases ht0 : t = 0
    · subst ht0
      rw [if_pos rfl]
      refine (Det.nat (P := Pg) (env := [A, .nat 0]) 0).post fun c0 hc0 => ?_
      refine ⟨0, by simp [Iface.giantCases], rfl, ?_, hsel _ ?_⟩
      · exact ⟨sv, lv, L, rfl, hlab, hrow.mpr ⟨⟨hh, hlt, hrows⟩, ht.mp rfl⟩⟩
      · have hnat : ca + (cc + (cy + c0 + (Val.nat 0).wt + 1) + (Val.nat 0).wt + 1) +
            (Val.nat 0).wt + 1 ≤ giantSelCost hpre W k S.N := by
          unfold giantSelCost
          simp only [natCostK, badK] at hT0' hbadc hcy hca ⊢
          omega
        exact_mod_cast hnat
    · rw [if_neg ht0]
      refine (Det.nat (P := Pg) (env := [A, .nat 0]) 1).post fun c0 hc0 => ?_
      refine ⟨1, by simp [Iface.giantCases], rfl, ?_, hsel _ ?_⟩
      · exact ⟨sv, lv, L, rfl, hlab, fun hR => ht0 (ht.mpr (hrow.mp hR).2)⟩
      · have hnat : ca + (cc + (cy + c0 + (Val.nat 1).wt + 1) + (Val.nat 1).wt + 1) +
            (Val.nat 1).wt + 1 ≤ giantSelCost hpre W k S.N := by
          unfold giantSelCost
          simp only [natCostK, badK] at hT0' hbadc hcy hca ⊢
          omega
        exact_mod_cast hnat
  · -- one of the three tests fails: aggregation
    rw [if_neg hb0]
    refine (Det.nat (P := Pg) (env := [A, .nat bad]) 1).post fun c0 hc0 => ?_
    refine ⟨1, by simp [Iface.giantCases], rfl, ?_, hsel _ ?_⟩
    · exact ⟨sv, lv, L, rfl, hlab, fun hR => hb0 (hbad.mpr (hrow.mp hR).1)⟩
    · have hbw := wt_nat_le bad
      have hnat : ca + (cc + c0 + (Val.nat 1).wt + 1) + (Val.nat 1).wt + 1 ≤
          giantSelCost hpre W k S.N := by
        unfold giantSelCost
        simp only [natCostK, badK] at hbadc hca ⊢
        omega
      exact_mod_cast hnat

/-! ### The cost is a polynomial in `N` -/

/-- The cost bound for inputs with `W + 2k + N + 4 ≤ M`. -/
theorem giantSelCost_le_of (hpre : GI.Cited.Preimage) {W k N M : ℕ} (hM : W + 2 * k + N + 4 ≤ M) :
    giantSelCost hpre W k N ≤
      (preimagePrim hpre).c * (1000 * M ^ 6 + 2) ^ (preimagePrim hpre).k +
        (natCostK + badK + 10) * M ^ 16 := by
  unfold giantSelCost
  refine Nat.add_le_add ?_ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 16))
  unfold Prim.boundSize natPB
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by have := Nat.pow_le_pow_left hM 6; omega) _)

/-- On a node that fits its phase, `W + 2k + N + 4 ≤ 30000 (N + 2)⁶` for the input weight bound
`W = 2 (stateW + labWStd) + 6`. -/
theorem inWStd_le {S : State Ω C} (hk : Nat.card Ω ≤ S.N) (hs : Small S) :
    2 * (stateW (Nat.card Ω) S + labWStd (Nat.card Ω) S.N) + 6 + 2 * Nat.card Ω + S.N + 4 ≤
      30000 * (S.N + 2) ^ 6 := by
  have h1 := stateW_le_of_small hk hs
  have hp : (Nat.card Ω + 1) ^ 4 ≤ (S.N + 2) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 4).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hN : S.N + 2 ≤ (S.N + 2) ^ 6 := Nat.le_self_pow (by norm_num) _
  unfold labWStd
  omega

/-- **The cost of the selector is a polynomial in `N`** on a node that fits its phase (`k ≤ N`
positions, `Small` state), for an interface with the label weight `labWStd`: at most
`c (1000 M⁶ + 2)^d + (natCostK + badK + 10) M¹⁶` with `M = 3·10⁴ (N + 2)⁶`, where `c` and `d`
are the constants of the cited preimage bound. -/
theorem giantSelCost_poly (I : Iface) (hpre : GI.Cited.Preimage)
    (hlab : ∀ k N, I.labW k N = labWStd k N) {S : State Ω C} (hk : Nat.card Ω ≤ S.N)
    (hs : Small S) :
    giantSelCost hpre (I.inW .giant S) (Nat.card Ω) S.N ≤
      (preimagePrim hpre).c * (1000 * (30000 * (S.N + 2) ^ 6) ^ 6 + 2) ^ (preimagePrim hpre).k +
        (natCostK + badK + 10) * (30000 * (S.N + 2) ^ 6) ^ 16 := by
  refine giantSelCost_le_of hpre ?_
  simp only [Iface.inW, hlab]
  exact inWStd_le hk hs

/-! ### The work of the selector, as the field `Rest.giantSelW` -/

/-- **The work of the selector of `GiantStep`**, for the label weight `labWStd`: the bound
`giantSelCost` at the input weight bound `inW .giant`. This is the value to give the field
`Rest.giantSelW`. -/
noncomputable def giantSelWStd (hpre : GI.Cited.Preimage) {Ω C : Type} (S : State Ω C) : ℝ :=
  (giantSelCost hpre (2 * (stateW (Nat.card Ω) S + labWStd (Nat.card Ω) S.N) + 6)
    (Nat.card Ω) S.N : ℝ)

/-- **The selector of `GiantStep` for the concrete interface**: when `Rest.giantSelW` is at least
`giantSelWStd`, the selector at `b` meets its specification. -/
theorem Rest.giantSel (R : Rest) (hpre : GI.Cited.Preimage) {Pg : Program} {b jpre : ℕ}
    (h : Pg.HasAt b (giantSelFuns b jpre)) (hj : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hR : ∀ {Ω C : Type} (S : State Ω C), giantSelWStd hpre S ≤ R.giantSelW S) :
    R.iface.SelSpec Pg .giant R.iface.giantCases b :=
  giantSel_spec R.iface Pg hpre h hj (fun _ _ _ _ h => h) fun S => hR S

theorem poly_aux (c d K a X : ℕ) (hX1 : 1 ≤ X) :
    c * (1000 * (a * X ^ 6) ^ 6 + 2) ^ d + K * (a * X ^ 6) ^ 16 ≤
      (c * (1000 * a ^ 6 + 2) ^ d + K * a ^ 16) * X ^ (36 * d + 96) := by
  have e1 : 1000 * (a * X ^ 6) ^ 6 + 2 ≤ (1000 * a ^ 6 + 2) * X ^ 36 := by
    have h1 : 1 ≤ X ^ 36 := Nat.one_le_pow _ _ hX1
    have h2 : (a * X ^ 6) ^ 6 = a ^ 6 * X ^ 36 := by ring
    rw [h2]; nlinarith
  have e2 : c * (1000 * (a * X ^ 6) ^ 6 + 2) ^ d ≤
      c * (1000 * a ^ 6 + 2) ^ d * X ^ (36 * d + 96) := by
    calc c * (1000 * (a * X ^ 6) ^ 6 + 2) ^ d
        ≤ c * ((1000 * a ^ 6 + 2) * X ^ 36) ^ d :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e1 d)
      _ = c * (1000 * a ^ 6 + 2) ^ d * X ^ (36 * d) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ c * (1000 * a ^ 6 + 2) ^ d * X ^ (36 * d + 96) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  have e3 : K * (a * X ^ 6) ^ 16 ≤ K * a ^ 16 * X ^ (36 * d + 96) := by
    calc K * (a * X ^ 6) ^ 16 = K * a ^ 16 * X ^ 96 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  rw [add_mul]; omega

/-- **`giantSelWStd` is a polynomial in `N`** on a node that fits its phase: at most
`A (N + 2)^D` with `A = c (1000 · 30000⁶ + 2)^d + (natCostK + badK + 10) 30000¹⁶` and
`D = 36 d + 96`, where `c` and `d` are the constants of the cited preimage bound. This is the
clause of `Rest.Req` for the selector of `GiantStep`. -/
theorem giantSelWStd_le (hpre : GI.Cited.Preimage) {S : State Ω C} (hk : Nat.card Ω ≤ S.N)
    (hs : Small S) :
    giantSelWStd hpre S ≤
      (((preimagePrim hpre).c * (1000 * 30000 ^ 6 + 2) ^ (preimagePrim hpre).k +
        (natCostK + badK + 10) * 30000 ^ 16 : ℕ) : ℝ) *
        ((S.N : ℝ) + 2) ^ (36 * (preimagePrim hpre).k + 96) := by
  have h := giantSelCost_le_of hpre (inWStd_le hk hs)
  have hnat := h.trans (poly_aux (preimagePrim hpre).c (preimagePrim hpre).k
    (natCostK + badK + 10) 30000 (S.N + 2) (by omega))
  unfold giantSelWStd
  have : ((S.N : ℝ) + 2) = ((S.N + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  exact_mod_cast hnat

end GI.Impl
