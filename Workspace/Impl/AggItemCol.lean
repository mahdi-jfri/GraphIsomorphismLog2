module

public import Workspace.Impl.AggItemTs
public import Workspace.Impl.AggItemHand

@[expose] public section

/-!
# The refined tuple colorings of the round, from the items' start state

The first thing the items compute is the pair of refined tuple colorings of the two strings
(Section A.3: the comparison classes of `κ`-tuples, refined jointly by the coherent `κ`-ary
refinement). On the start state `itSt sv k q ps fx fy tt cr` the entry `itColF`:
1. reads `q` and builds the list of all `κ`-tuples (`it_ts_spec`);
2. colors every tuple of each string by its comparison class (`stCols_spec`, with the relation
   module of `stRel_spec_round`): the color of `(z, t)` is the index of the first `t₀` with
   `(x, t₀)` in the class of `(z, t)`, that is `tcol (stNum (stTs q κ) x) z t` (`stCz_tcol`);
3. calls the cited joint refinement once (`stRef_spec`, **KaryRefinement κ**).

`it_col_spec`: the output `w` satisfies `KaryOut c₀ c₁ w` for the two class colorings, at cost
`itColC M` plus the bound of the cited call.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encKColoring)

/-- On `itSt sv k q ps fx fy tt cr`: the joint refinement of the two class colorings. The
environment grows as `[st, q, [c₀, c₁]]`. -/
def itColF (ts bc fr κ : ℕ) : Expr :=
  .letE (.get (.get (.var 0) (.nat 1)) (.nat 1))
  (.letE (.call bc (mk2 (.get (.var 0) (.nat 5)) (.call ts (mk2 (.var 1) (.nat κ)))))
    (.call fr (mk2 (.var 1) (.var 2))))

/-- The cost bound of `itColF` besides the cited call, for the size parameter `M`. -/
def itColC (M : ℕ) : ℕ :=
  itTsC (M + 10) + stColsCost (stRelK * (M + 1) ^ 4) (50 * (M + 11) ^ 3) +
    30 * (M + 1) ^ 2 + stRefK * (50 * (M + 1) ^ 2 + 1) ^ 2 + 1000 * (M + 11) ^ 3

/-- A class coloring weighs at most `4 (q^κ + 1)²`. -/
theorem it_wt_cz {q κ : ℕ} (R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool) (z : ℕ) :
    (encKColoring (stCz R z)).wt ≤ 4 * (q ^ κ + 1) ^ 2 :=
  wt_encFun_le_sq (n := q ^ κ) (fun j => stCz R z (finFunctionFinEquiv.symm j))
    fun _ => stCz_le R z _

/-- **The refined tuple colorings.** On the start state of the items, `itColF` returns a joint
coherent refinement (`KaryOut`) of the class colorings `stCz (stRel …) 0` (of `x`) and
`stCz (stRel …) 1` (of `y`). -/
theorem it_col_spec (h : GI.Cited.KaryRefinement P₀.κ) {P : Program}
    {f ts pw rb mp tv dc bc brel fr brep jk : ℕ}
    (hf : P.funs[f]? = some (itColF ts bc fr P₀.κ))
    (hts : P.funs[ts]? = some (itTsF pw rb mp)) (hpw : P.HasAt pw (stDPowFuns pw))
    (hrb : P.HasAt rb (rangeFuns rb)) (hmp : P.HasAt mp (mapFuns mp tv))
    (htv : P.funs[tv]? = some (itTvF dc)) (hdc : P.HasAt dc (stDDecFuns dc))
    (hbc : P.HasAt bc (stColsFuns bc brel)) (hrel : P.HasAt brel (stRelFuns brel))
    (hfr : P.funs[fr]? = some (stRefF brep jk)) (hrep : P.HasAt brep (replicateFuns brep))
    (hjk : P.prims[jk]? = some (karyRefinementPrim h))
    {Ω C : Type} (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom] {q : ℕ}
    (πd : S.domGroup →* alternatingGroup (Fin q)) (x y : S.dom → C)
    (O : TestTupleOrder q P₀.κ) (sv : Val) (k : ℕ)
    {ps fx fy : List (Perm (Fin k) × Perm (Fin q))} (hq : 0 < q) {M : ℕ}
    (hM : (itSt sv k q ps fx fy O.tuples (stCr S πd P₀.κ x y)).wt + q ^ P₀.κ + q + P₀.κ ≤ M) :
    FunAll P f (itSt sv k q ps fx fy O.tuples (stCr S πd P₀.κ x y)) (fun w cost =>
      KaryOut (stCz (stRel S πd P₀.κ x y) 0) (stCz (stRel S πd P₀.κ x y) 1) w ∧
      cost ≤ itColC M + (karyRefinementPrim h).bound
        (karyEnc (stCz (stRel S πd P₀.κ x y) 0) (stCz (stRel S πd P₀.κ x y) 1))) := by
  set cv := stCv O.tuples (stCr S πd P₀.κ x y) with hcv
  set st := itSt sv k q ps fx fy O.tuples (stCr S πd P₀.κ x y) with hst
  set R := stRel S πd P₀.κ x y with hR
  set tsV := Val.list ((stTs q P₀.κ).map stTv) with htsV
  have hM1 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM2 : (M + 1) ^ 2 ≤ (M + 11) ^ 3 := by
    calc (M + 1) ^ 2 ≤ (M + 11) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (M + 11) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  -- the parts of the state
  have hstl : st = .list [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
      .list (fy.map pairV), cv] := rfl
  have hkq : (Val.list [.nat k, .nat q]).wt < st.wt := by
    rw [hstl]; exact wt_le_wt_list (by simp)
  have hcvw : cv.wt < st.wt := by rw [hstl]; exact wt_le_wt_list (by simp)
  have wq := wt_nat_le q
  have wk := wt_nat_le P₀.κ
  -- 1. `q`
  have d1 : Det P [st] (.get (.get (.var 0) (.nat 1)) (.nat 1)) (.nat q) _ :=
    Det.get' (Det.get' (Det.var' rfl) (Det.nat 1) rfl) (Det.nat 1) rfl
  refine FunAll.intro hf (EvalAll.letE d1 fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- 2. the class colorings
  have hts' := it_ts_spec hts hpw hrb hmp htv hdc hq (κ := P₀.κ)
  have dts := Det.call (Det.mk2 (Det.var' (P := P) (env := [st] ++ [.nat q]) (i := 1) rfl)
    (Det.nat P₀.κ)) hts'
  have hcvM : cv.wt ≤ M := by omega
  have hrel' := stRel_spec_round hrel S πd x y O (M := M) (by omega) (by omega) hcvM
  have htw : tsV.wt ≤ q ^ P₀.κ * (10 * (q ^ P₀.κ + q + P₀.κ + 11) ^ 2 + 1) + 4 :=
    it_ts_wt q P₀.κ
  have htw' : tsV.wt ≤ 11 * (M + 11) ^ 3 + 4 := by
    have e1 : q ^ P₀.κ * (10 * (q ^ P₀.κ + q + P₀.κ + 11) ^ 2 + 1) ≤ (M + 11) * (10 * (M + 11) ^ 2 + 1) :=
      Nat.mul_le_mul (by omega) (by
        have := Nat.pow_le_pow_left (show q ^ P₀.κ + q + P₀.κ + 11 ≤ M + 11 by omega) 2; omega)
    have e2 : (M + 11) * (10 * (M + 11) ^ 2 + 1) = 10 * (M + 11) ^ 3 + (M + 11) := by ring
    have : M + 11 ≤ (M + 11) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hin : (Val.list [cv, tsV]).wt ≤ 50 * (M + 11) ^ 3 := by
    have := wt_list2_le cv tsV; omega
  have hcols := stCols_spec hbc stTv_injective hrel' hin
  have dcs := Det.call (Det.mk2 (Det.get' (Det.var' (P := P) (env := [st] ++ [.nat q]) (i := 0) rfl)
    (Det.nat 5) (v := cv) rfl) dts) hcols
  refine EvalAll.letE dcs fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- 3. the refinement call
  have w0 := it_wt_cz R 0
  have w1 := it_wt_cz R 1
  have hqκ : (q ^ P₀.κ + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hcc := wt_list2_le (encKColoring (stCz R 0)) (encKColoring (stCz R 1))
  have hrin := wt_list2_le (.nat q) (.list [encKColoring (stCz R 0), encKColoring (stCz R 1)])
  have href := stRef_spec h hfr hrep hjk (stCz R 0) (stCz R 1) (fun t => stCz_le R 0 t)
    (fun t => stCz_le R 1 t) (M := 50 * (M + 1) ^ 2) (by omega) (by omega)
  refine EvalAll.call_funAll (Det.mk2 (Det.var' (P := P)
    (env := [st] ++ [.nat q] ++ [.list [encKColoring (stCz R 0), encKColoring (stCz R 1)]])
    (i := 1) rfl) (Det.var' (i := 2) rfl)) fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  refine href.mono fun w c hw => ⟨hw.1, ?_⟩
  obtain ⟨hk, hc⟩ := hw
  have hww := hk.wt_le
  have hts2 : itTsC (q ^ P₀.κ + q + P₀.κ + 10) ≤ itTsC (M + 10) := itTsC_mono (by omega)
  have hpk : 30 * (q ^ P₀.κ + 1) ^ 2 ≤ 30 * (M + 1) ^ 2 := Nat.mul_le_mul_left _ hqκ
  have wst : st.wt ≤ M := by omega
  have hqk2 := wt_list2_le (.nat q) (.nat P₀.κ)
  unfold itColC
  simp only [hst, hcv, hR, htsV] at *
  have est : (Val.list [sv, Val.list [Val.nat k, Val.nat q], Val.list (ps.map pairV),
      Val.list (fx.map pairV), Val.list (fy.map pairV), stCv O.tuples (stCr S πd P₀.κ x y)]).wt =
      (itSt sv k q ps fx fy O.tuples (stCr S πd P₀.κ x y)).wt := rfl
  omega

end GI.Impl
