module

public import Workspace.Degree.Solved
public import Workspace.Impl.RestSel
public import Workspace.Impl.SmallZ

@[expose] public section

/-!
# The first step of `Continue`

The function `contD` reads three things from a state value: its size `s`, the sum `ρ` of the tower
ranks of its hierarchy, and whether the group is transitive. If `s ≤ max(N₀, ρ)`, it calls the
general solver. Otherwise it calls the orbit chain or the reset.

* `rhoSum_spec`: the sum `ρ`, as a fold over the hierarchy.
* `contD_spec`: the three-way choice, for any postcondition of the three branches.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp len len_mono)
open GI.Cited (Val encGroup)

variable {Ω C : Type} {k : ℕ}

/-- One step of the sum on `[c, acc, I]`, for an interval value `I`, with `log₂` at `blog`. -/
def rhoStep (blog : ℕ) : Expr :=
  .letE (.get (arg 2) (.nat 1))
    (.ite (.arith .lt (.nat 1) (.var 1))
      (.arith .add (arg 1)
        (.arith .sub (.arith .mul (.nat 2) (.get (.call blog (.var 1)) (.nat 0))) (.nat 1)))
      (arg 1))

/-- The cost of one step, for a ratio at most `N` and an input of weight at most `W`. -/
def rhoStepC (N W : ℕ) : ℕ := 10 ^ 5 * (N + W + 8) ^ 2

theorem towerRank_toNat {r : ℕ} (hr : 2 ≤ r) :
    (GI.towerRank r).toNat = 2 * Nat.log 2 r - 1 := by
  unfold GI.towerRank
  rw [if_neg (by omega)]
  omega

set_option maxHeartbeats 1000000 in
theorem rhoStep_spec {P : Program} {g blog : ℕ} (hg : P.funs[g]? = some (rhoStep blog))
    (hl : P.HasAt blog (log2Funs blog)) (c pv : Val) {r a o N W : ℕ} {acc : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (haN : acc ≤ N)
    (hW : (Val.list [c, .nat acc, .list [pv, .nat r, .nat a, .nat o]]).wt ≤ W) :
    FunDet P g (.list [c, .nat acc, .list [pv, .nat r, .nat a, .nat o]])
      (.nat (acc + (GI.towerRank r).toNat)) (rhoStepC N W) := by
  set I := Val.list [pv, .nat r, .nat a, .nat o] with hI
  set x := Val.list [c, .nat acc, I] with hx
  set L := Nat.log 2 r with hL
  have dI := Det.get' (Det.arg' (P := P) (vs := [c, .nat acc, I]) (rest := []) (j := 2) rfl)
    (Det.nat 1) (show [pv, Val.nat r, .nat a, .nat o][1]? = some (.nat r) from rfl)
  have dr := Det.var' (P := P) (env := [x, Val.nat r]) (i := 1) rfl
  have dt := Det.arith (op := .lt) (Det.nat (P := P) (env := [x, Val.nat r]) 1) dr
  have hlt : BinOp.eval .lt 1 r = 1 := by
    change (if 1 < r then 1 else 0) = 1
    rw [if_pos (by omega)]
  rw [hlt] at dt
  have dacc := Det.arg' (P := P) (vs := [c, .nat acc, I]) (rest := [Val.nat r]) (j := 1) rfl
  have dlog := Det.call dr (log2_spec hl r)
  have dL := Det.get' dlog (Det.nat 0)
    (show [Val.nat L, Val.nat (2 ^ L)][0]? = some (.nat L) from rfl)
  have dm := Det.arith' (op := .mul) (z := 2 * L) (Det.nat (P := P) (env := [x, Val.nat r]) 2) dL rfl
  have ds := Det.arith' (op := .sub) (z := 2 * L - 1) dm (Det.nat 1) rfl
  have da := Det.arith' (op := .add) (z := acc + (GI.towerRank r).toNat) dacc ds (by
    rw [towerRank_toNat hr]; rfl)
  have dite : Det P [x, Val.nat r] (.ite (.arith .lt (.nat 1) (.var 1))
      (.arith .add (arg 1)
        (.arith .sub (.arith .mul (.nat 2) (.get (.call blog (.var 1)) (.nat 0))) (.nat 1)))
      (arg 1)) _ _ := Det.ite_pos dt one_ne_zero da
  refine FunDet.intro hg ((Det.letE dI dite).mono ?_)
  clear dI dr dt dacc dlog dL dm ds da dite hg hl
  have h1 := wt_nat_le r
  have h3 := wt_nat_le 1
  have hrw : (Val.nat r).wt < x.wt := by
    have h2 : (Val.nat r).wt < I.wt := wt_le_wt_list (by simp)
    have h4 : I.wt < x.wt := wt_le_wt_list (by simp)
    omega
  have hl2 : (Val.list [Val.nat L, Val.nat (2 ^ L)]).wt ≤ 4 * (Val.nat r).wt + 20 := by
    have := wt_log2Acc_le r (r + 4); rwa [log2Acc_final] at this
  have hLr : L ≤ r := Nat.log_le_self 2 r
  have hLw := wt_nat_le L
  have hrk : (GI.towerRank r).toNat ≤ 2 * r := by rw [towerRank_toNat hr]; omega
  have hwone : (Val.nat 1).wt ≤ 3 := h3
  have hlt1 : (Val.nat 1).wt ≤ 3 := hwone
  have hx' : x.wt ≤ W := hW
  unfold rhoStepC
  have hX : 8 ≤ N + W + 8 := by omega
  obtain ⟨X, hXd⟩ : ∃ X, X = N + W + 8 := ⟨_, rfl⟩
  rw [← hXd] at hX ⊢
  have hc1 : 2000 * (r + 4) + loopModK * (r + 5) * (5 * (Val.nat r).wt + r + 25) ≤ 7000 * X ^ 2 := by
    have e1 : r + 5 ≤ X := by omega
    have e2 : 5 * (Val.nat r).wt + r + 25 ≤ 6 * X := by omega
    have e3 : 2000 * (r + 4) ≤ 2000 * X := by omega
    have e4 : 2000 * X ≤ 1000 * X ^ 2 := by nlinarith
    have e5 : loopModK * (r + 5) * (5 * (Val.nat r).wt + r + 25) ≤ loopModK * X * (6 * X) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) e2
    have e6 : loopModK * X * (6 * X) = 6000 * X ^ 2 := by simp only [loopModK]; ring
    omega
  have hX2 : 10 * X ≤ X ^ 2 := by nlinarith
  generalize 2000 * (r + 4) + loopModK * (r + 5) * (5 * (Val.nat r).wt + r + 25) = Y at *
  have hLe : Nat.log 2 r = L := rfl
  rw [hLe]
  have ev : (Val.list [c, Val.nat acc, I]).wt = x.wt := rfl
  rw [ev]
  have w0 := wt_nat_le 0
  have w2 := wt_nat_le 2
  have w4 := wt_list2_le (Val.nat L) (Val.nat (2 ^ L))
  have wu := wt_nat_le (acc + (GI.towerRank r).toNat)
  have hLr' : Nat.log 2 r ≤ r := hLr
  generalize X ^ 2 = Z at *
  omega

/-- The bound on the sum, for a hierarchy value of weight at most `W`. -/
def rhoC (N W : ℕ) : ℕ :=
  (W + 2) * rhoStepC N (2 * W + 2 * N + 30) + 1000 * (W + 2) * (3 * W + 2 * N + 30)

theorem rhoNat_take_succ {Ω : Type} (l : List (Interval Ω)) (i : ℕ) (hi : i < l.length) :
    rhoNat (l.take (i + 1)) = rhoNat (l.take i) + (GI.towerRank l[i].ratio).toNat := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
  simp only [rhoNat, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

theorem rhoNat_take_le {Ω : Type} (l : List (Interval Ω)) (i : ℕ) :
    rhoNat (l.take i) ≤ rhoNat l := by
  conv_rhs => rw [← List.take_append_drop i l]
  simp only [rhoNat, List.map_append, List.sum_append]
  omega

/-- **The sum of the tower ranks.** -/
theorem rhoSum_spec {P : Program} {b g blog : ℕ} (h : P.HasAt b (foldlFuns b g))
    (hg : P.funs[g]? = some (rhoStep blog)) (hl : P.HasAt blog (log2Funs blog)) {e : Ω ≃ Fin k}
    {vs : List Val} {l : List (Interval Ω)} (hv : List.Forall₂ (IntervalValC e) vs l) {N : ℕ}
    (hok : IntervalsOK N l) (hρ : rhoNat l ≤ N) :
    FunDet P b (.list [.nat 0, .list vs, .nat 0]) (.nat (rhoNat l)) (rhoC N (Val.list vs).wt) := by
  have hlen : vs.length = l.length := hv.length_eq
  have hget := (List.forall₂_iff_get.1 hv).2
  obtain ⟨W, hW⟩ : ∃ W, W = (Val.list vs).wt := ⟨_, rfl⟩
  rw [← hW]
  have hn : vs.length ≤ W := by have := length_lt_wt_list vs; omega
  have h0 := wt_nat_le 0
  have hsp := foldl_spec h (c := .nat 0) (xs := vs) (acc0 := .nat 0) (M := N + 2)
    (Inv := fun i acc => acc = .nat (rhoNat (l.take i)))
    (B := fun _ => rhoStepC N (2 * W + 2 * N + 30)) (by simp [rhoNat])
    (fun i acc _ h => by
      subst h
      have := wt_nat_le (rhoNat (l.take i))
      have := rhoNat_take_le l i
      omega) ?_
  · refine (hsp.mono fun w cost ⟨hi, hc⟩ => ⟨?_, ?_⟩)
    · rw [hi, hlen, List.take_length]
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
      refine hc.trans ?_
      unfold rhoC
      have e1 : vs.length * rhoStepC N (2 * W + 2 * N + 30) ≤
          (W + 2) * rhoStepC N (2 * W + 2 * N + 30) := Nat.mul_le_mul_right _ (by omega)
      have e2 : loopModK * (vs.length + 1) * ((Val.list [.nat 0, .list vs, .nat 0]).wt +
          vs.length + (N + 2) + 1) ≤ 1000 * (W + 2) * (3 * W + 2 * N + 30) := by
        have w3 := wt_list3_le (.nat 0) (.list vs) (.nat 0)
        simp only [loopModK]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      omega
  · intro i acc hi hacc
    subst hacc
    have hi' : i < l.length := by omega
    have hiv := hget i (by omega) hi'
    obtain ⟨pv, -, hval⟩ := hiv
    have hval' : vs[i] = .list [pv, .nat l[i].ratio, .nat l[i].cap, .nat l[i].origin] := hval
    rw [hval']
    obtain ⟨hr2, hrN, -, -⟩ := hok _ (List.getElem_mem hi')
    have hs := rhoNat_take_le l i
    have hx : (Val.list [.nat 0, .nat (rhoNat (l.take i)),
        .list [pv, .nat l[i].ratio, .nat l[i].cap, .nat l[i].origin]]).wt ≤
        2 * W + 2 * N + 30 := by
      have w3 := wt_list3_le (.nat 0) (.nat (rhoNat (l.take i)))
        (.list [pv, .nat l[i].ratio, .nat l[i].cap, .nat l[i].origin])
      have w4 := wt_nat_le (rhoNat (l.take i))
      have w5 : (Val.list [pv, .nat l[i].ratio, .nat l[i].cap, .nat l[i].origin]).wt < W := by
        rw [hW, ← hval']; exact wt_le_wt_list (List.getElem_mem _)
      omega
    refine FunAll.mono (rhoStep_spec hg hl (.nat 0) pv hr2 hrN (hs.trans hρ) hx) fun w cost hw => ⟨?_, hw.2⟩
    rw [rhoNat_take_succ l i hi', hw.1]

/-- **The first step of `Continue`.** In the environment `[v, s, ρ]`, the call on `v` goes to the
general solver at `fs` if `s ≤ N₀` or `s ≤ ρ`. Otherwise `lo` finds a largest orbit, and the call goes
to the orbit chain at `forb` or to the reset at `frs`. -/
def contE (bs brho bl bm N₀ fs forb frs : ℕ) : Expr :=
  .letE (.call bs (.var 0))
  (.letE (.call brho (mk3 (.nat 0) (arg 5) (.nat 0)))
  (.ite (.arith .lt (.nat N₀) (.var 1))
    (.ite (.arith .lt (.var 2) (.var 1))
      (.letE (.call bl (mk2 (arg 1) (arg 2)))
        (.ite (.call bm (.get (.var 3) (.nat 1))) (.call forb (.var 0)) (.call frs (.var 0))))
      (.call fs (.var 0)))
    (.call fs (.var 0))))

/-- The cost of `contD` besides the branch. -/
def contOwn (N₀ k N W : ℕ) : ℕ :=
  sizeK * (W + 1) ^ 2 + rhoC N W + loK * (k + 1) ^ 15 + maxK * (k + 1) ^ 3 +
    1000 * (W + N + N₀ + 40) + 1000 * k

theorem rhoC_mono (N : ℕ) {W W' : ℕ} (h : W ≤ W') : rhoC N W ≤ rhoC N W' := by
  unfold rhoC rhoStepC
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`contD` chooses its branch.** -/
theorem contD_spec {P : Program} {f bs brho g blog bl bm N₀ fs forb frs : ℕ}
    (hf : P.funs[f]? = some (contE bs brho bl bm N₀ fs forb frs))
    (hbs : P.HasAt bs (sizeFuns bs)) (hbr : P.HasAt brho (foldlFuns brho g))
    (hg : P.funs[g]? = some (rhoStep blog)) (hl : P.HasAt blog (log2Funs blog))
    (hlo : P.HasAt bl (loFuns bl)) (hmax : P.HasAt bm (maxFuns bm))
    {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val} {S : State Ω C} (hcan : Canon e c v S)
    {Q : Val → ℕ → Prop}
    (hsm : S.size ≤ max N₀ (rhoNat S.hier) → FunAll P fs v Q)
    (horb : ¬ S.size ≤ max N₀ (rhoNat S.hier) → ¬ S.Transitive → FunAll P forb v Q)
    (hrs : ¬ S.size ≤ max N₀ (rhoNat S.hier) → S.Transitive → FunAll P frs v Q) :
    FunAll P f v fun u cost => ∃ c₀, Q u c₀ ∧ cost ≤ c₀ + contOwn N₀ k S.N v.wt + 8 * (u.wt + 2) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  have hsz := size_spec hbs hcan.stateVal
  have hkw := hcan.fits
  have hwv : k ≤ v.wt := StateVal.k_le_wt hcan.stateVal
  obtain ⟨gv, dv, xv, yv, hv0, rv, hgv, hdv, hxv, hyv, hhv, hrv, hvv⟩ := hcan.val
  obtain ⟨vs, rfl, hF⟩ := hhv
  obtain ⟨gs, rfl, hgens, hgl⟩ := hgv
  have hdv' : dv = indVal e S.dom := hdv
  subst hdv'
  set a := Val.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, .list vs, rv, boolVal S.floor,
    .nat S.h, .nat S.N] with ha
  subst hvv
  have hrho := rhoSum_spec hbr hg hl hF hcan.small.1 hcan.small.2.1
  have wvs : (Val.list vs).wt < a.wt := wt_le_wt_list (by simp)
  have d1 := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hsz
  have dV1 := Det.arg' (P := P) (vs := [.nat k, encGroup gs, indVal e S.dom, xv, yv, .list vs, rv,
    boolVal S.floor, .nat S.h, .nat S.N]) (rest := [.nat S.size]) (j := 5) rfl
  have d2 := Det.call (Det.mk3 (Det.nat (P := P) (env := [a, .nat S.size]) 0) dV1 (Det.nat 0)) hrho
  have ds := Det.var' (P := P) (env := [a, .nat S.size, .nat (rhoNat S.hier)]) (i := 1) rfl
  have dρ := Det.var' (P := P) (env := [a, .nat S.size, .nat (rhoNat S.hier)]) (i := 2) rfl
  have dv0 := Det.var' (P := P) (env := [a, .nat S.size, .nat (rhoNat S.hier)]) (i := 0) rfl
  have t1 := Det.arith (op := .lt) (Det.nat (P := P) (env := [a, .nat S.size, .nat (rhoNat S.hier)]) N₀) ds
  have t2 := Det.arith (op := .lt) dρ ds
  have wN := wt_nat_le N₀
  have wS := wt_nat_le S.size
  have wR := wt_nat_le (rhoNat S.hier)
  have hsk : S.size ≤ k := by
    have := Nat.card_le_card_of_injective (fun a : S.dom => e a.1)
      (fun a b h => Subtype.ext (e.injective h))
    exact this.trans (by simp)
  have hρN : rhoNat S.hier ≤ S.N := hcan.small.2.1
  have hmono := rhoC_mono S.N (Nat.le_of_lt wvs)
  have w3 := wt_list3_le (.nat 0) (.list vs) (.nat 0)
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have hcall : ∀ {env : List Val} {g' : ℕ} (i : ℕ), env[i]? = some a → FunAll P g' a Q →
      EvalAll P env (.call g' (.var i)) (fun u cost => ∃ c₀, Q u c₀ ∧
        cost ≤ a.wt + 1 + c₀ + u.wt + 1) := fun i hi h =>
    EvalAll.call_funAll (Det.var' hi) fun v' cv h0 => by
      obtain ⟨rfl, hcv⟩ := h0
      exact h.mono fun u c hq => ⟨c, hq, by omega⟩
  have hwlt : ∀ x y, (Val.nat (BinOp.eval .lt x y)).wt ≤ 3 := fun x y => by
    simp only [BinOp.eval]; split <;> decide
  refine FunAll.intro hf ?_
  have hlt1 : ∀ {x y : ℕ}, x < y → BinOp.eval .lt x y = 1 := fun h => by
    change (if _ then 1 else 0) = 1; rw [if_pos h]
  have hlt0 : ∀ {x y : ℕ}, ¬ x < y → BinOp.eval .lt x y = 0 := fun h => by
    change (if _ then 1 else 0) = 0; rw [if_neg h]
  refine EvalAll.letE d1 fun w1' c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun w2' c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  have ht1 := hwlt N₀ S.size
  have ht2 := hwlt (rhoNat S.hier) S.size
  have ea : (Val.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, .list vs, rv, boolVal S.floor,
    .nat S.h, .nat S.N]).wt = a.wt := rfl
  have cG : (encGroup gs).wt < a.wt := wt_le_wt_list (by simp [ha])
  refine EvalAll.ite t1 (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  injection hx with hx
  subst hx
  by_cases hA : N₀ < S.size
  · rw [hlt1 hA, if_neg one_ne_zero]
    refine EvalAll.ite t2 (fun _ _ h => ⟨_, h.1⟩) fun x cc' hx => ?_
    obtain ⟨hx, hcc'⟩ := hx
    injection hx with hx
    subst hx
    by_cases hB : rhoNat S.hier < S.size
    · rw [hlt1 hB, if_neg one_ne_zero]
      have hns : ¬ S.size ≤ max N₀ (rhoNat S.hier) := by
        rw [not_le, max_lt_iff]; exact ⟨hA, hB⟩
      have hne : S.dom.Nonempty := by
        obtain ⟨⟨x⟩, -⟩ := Nat.card_pos_iff.1 (show 0 < Nat.card S.dom by change 0 < S.size; omega)
        exact ⟨x.1, x.2⟩
      obtain ⟨D₁, hsub, horb', -, hloD⟩ := lo_spec hlo e S.dom_inv hne hgens hgl
      have da1 := Det.arg' (P := P) (vs := [.nat k, encGroup gs, indVal e S.dom, xv, yv, .list vs,
        rv, boolVal S.floor, .nat S.h, .nat S.N]) (rest := [.nat S.size, .nat (rhoNat S.hier)])
        (j := 1) rfl
      have da2 := Det.arg' (P := P) (vs := [.nat k, encGroup gs, indVal e S.dom, xv, yv, .list vs,
        rv, boolVal S.floor, .nat S.h, .nat S.N]) (rest := [.nat S.size, .nat (rhoNat S.hier)])
        (j := 2) rfl
      have dl := Det.call (Det.mk2 da1 da2) hloD
      refine EvalAll.letE dl fun w3' c3 h3 => ?_
      obtain ⟨rfl, hc3⟩ := h3
      have hmx := max_spec hmax (xs := (List.finRange k).map (indF e (S.dom \ D₁))) (B := k)
        (fun x hx => by
          obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
          have := indF_le_one e (S.dom \ D₁) j
          have : 1 ≤ k := by have := j.2; omega
          omega) (by simp)
      rw [foldl_max_indF] at hmx
      have hP := Det.var' (P := P) (env := [a, .nat S.size, .nat (rhoNat S.hier),
        .list [indVal e D₁, indVal e (S.dom \ D₁)]]) (i := 3)
        (v := .list [indVal e D₁, indVal e (S.dom \ D₁)]) rfl
      have hI := Det.get' hP (Det.nat 1) (v := indVal e (S.dom \ D₁)) rfl
      have heqI : indVal e (S.dom \ D₁) =
          natList ((List.finRange k).map (indF e (S.dom \ D₁))) := Lang.encFun_eq_natList _
      have d4 := Det.call hI (heqI ▸ hmx)
      have htr := transitive_iff_diff_empty hsub horb'
      have wD : ∀ D' : Set Ω, (indVal e D').wt ≤ k * 7 + 4 := fun D' =>
        DomVal.wt_le (domVal_indVal e D')
      have wD₁ := wD D₁
      have wD₂ := wD (S.dom \ D₁)
      have wDd : (indVal e S.dom).wt < a.wt := wt_le_wt_list (by simp [ha])
      have wP := wt_list2_le (indVal e D₁) (indVal e (S.dom \ D₁))
      have wL := wt_list2_le (encGroup gs) (indVal e S.dom)
      have wmx : (Val.nat (if S.dom \ D₁ = ∅ then 0 else 1)).wt ≤ 3 := by
        split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
      refine EvalAll.ite d4 (fun _ _ h => ⟨_, h.1⟩) fun x c4 hx => ?_
      obtain ⟨hx, hc4⟩ := hx
      injection hx with hx
      subst hx
      by_cases hd : S.dom \ D₁ = ∅
      · rw [if_pos hd, if_pos rfl]
        have ht : S.Transitive := htr.2 hd
        refine (hcall 0 rfl (hrs hns ht)).mono fun u cc'' ⟨c₀, hq, hle⟩ => ⟨c₀, hq, ?_⟩
        unfold contOwn
        omega
      · rw [if_neg hd, if_neg one_ne_zero]
        have ht : ¬ S.Transitive := fun h => hd (htr.1 h)
        refine (hcall 0 rfl (horb hns ht)).mono fun u cc'' ⟨c₀, hq, hle⟩ => ⟨c₀, hq, ?_⟩
        unfold contOwn
        omega
    · rw [hlt0 hB, if_pos rfl]
      have hs : S.size ≤ max N₀ (rhoNat S.hier) := le_max_of_le_right (by omega)
      refine (hcall 0 rfl (hsm hs)).mono fun u cc'' ⟨c₀, hq, hle⟩ => ⟨c₀, hq, ?_⟩
      unfold contOwn
      omega
  · rw [hlt0 hA, if_pos rfl]
    have hs : S.size ≤ max N₀ (rhoNat S.hier) := le_max_of_le_left (by omega)
    refine (hcall 0 rfl (hsm hs)).mono fun u cc'' ⟨c₀, hq, hle⟩ => ⟨c₀, hq, ?_⟩
    unfold contOwn
    omega

end GI.Degree
