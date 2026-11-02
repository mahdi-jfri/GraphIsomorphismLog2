import Workspace.Impl.LargestOrbit
import Workspace.Algorithm.OrbitKeep

/-!
# The row test of the first orbit-chain child, in `GI.Lang`

The first child of the orbit chain keeps the row record, the floor mode and `h` exactly when the
retained columns split its orbit `D₁` (`State.orbitBook`, `State.ColsSplit`; this is what
`State.inherit` gives, `State.inherit_book`). The orbit step (`Workspace/Impl/Orbit.lean`)
decides it with `splitFuns b` (18 functions at base `b`), on `[rows, ind D₁]`, where `rows` is
the row record of the state value (`[]`, or `[[m, rows, cols]]` with `cols` empty or one
partition) and `ind D₁` the indicator of `D₁`:

1. without a row record, the answer is `1` (the test is vacuous);
2. with a record and no column partition, the answer is `0`;
3. otherwise, with the column labels `lab`: the first point `p` of `D₁` (`findEqFuns`), and for
   each point `i` the number `[i ∈ D₁ and lab i ≠ lab p]` (`mapFuns` over `rangeFuns`); the
   answer is their maximum (`maxFuns`). It is `1` exactly when `D₁` meets two columns.

`split_spec`: the answer is `1` if `S.ColsSplit D₁` and `0` otherwise, at cost at most
`splitK (w + 1)^4`, where `w` is the weight of the argument.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm)

variable {Ω C : Type} {k : ℕ}

/-! ### The program -/

/-- The function of the map: on `[[ind, lab, a₀], i]`, the number `[ind i = 1 and lab i ≠ a₀]`. -/
def splitStepF : Expr :=
  .ite (.arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1)) (.nat 1))
    (.ite (.arith .eq (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 2)))
      (.nat 0) (.nat 1))
    (.nat 0)

/-- The test on `[lab, ind]`: the first point `p` with `ind p = 1`, then the maximum over the
points `i` of `[ind i = 1 and lab i ≠ lab p]`. The environment grows as `[a, p, lab p]`. -/
def splitTestE (bfind bmap brange bmax : ℕ) : Expr :=
  .letE (.call bfind (mk2 (.nat 1) (arg 1)))
  (.letE (.get (arg 0) (.var 1))
  (.call bmax (.call bmap (mk2 (mk3 (arg 1) (arg 0) (.var 2))
    (.call brange (.length (arg 1)))))))

/-- The entry on `[rows, ind]`. -/
def splitE (btest : ℕ) : Expr :=
  .ite (.length (arg 0))
    (.ite (.length (.get (.get (arg 0) (.nat 0)) (.nat 2)))
      (.call btest (mk2 (.get (.get (.get (arg 0) (.nat 0)) (.nat 2)) (.nat 0)) (arg 1)))
      (.nat 0))
    (.nat 1)

/-- The row-test module at base `b` (18 functions). -/
def splitFuns (b : ℕ) : List Expr :=
  [splitE (b + 1), splitTestE (b + 3) (b + 7) (b + 10) (b + 13), splitStepF] ++
    findEqFuns (b + 3) ++ mapFuns (b + 7) (b + 2) ++ rangeFuns (b + 10) ++ maxFuns (b + 13)

theorem length_splitFuns (b : ℕ) : (splitFuns b).length = 18 := by
  simp [splitFuns, findEqFuns, findFuns, mapFuns, rangeFuns, maxFuns, foldlFuns, loopFuns]

/-! ### The step of the map -/

/-- The value of the step on the point `i`. -/
def splitVal (ind lab : Fin k → ℕ) (a₀ : ℕ) (i : Fin k) : ℕ :=
  if ind i = 1 then (if lab i = a₀ then 0 else 1) else 0

theorem splitVal_le_one (ind lab : Fin k → ℕ) (a₀ : ℕ) (i : Fin k) : splitVal ind lab a₀ i ≤ 1 := by
  unfold splitVal; split_ifs <;> omega

theorem encFun_getElem? (f : Fin k → ℕ) (i : Fin k) :
    ((List.finRange k).map fun j => Val.nat (f j))[(i : ℕ)]? = some (.nat (f i)) := by
  rw [List.getElem?_eq_getElem (by simp)]
  simp

theorem splitStep_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some splitStepF)
    (ind lab : Fin k → ℕ) (a₀ : ℕ) (i : Fin k) (hind : ∀ j, ind j ≤ 1) (hlab : ∀ j, lab j < k)
    (ha₀ : a₀ < k) :
    FunDet P f (.list [.list [encFun ind, encFun lab, .nat a₀], .nat i])
      (.nat (splitVal ind lab a₀ i)) (1000 * (k + 1) ^ 2) := by
  set ctx : Val := .list [encFun ind, encFun lab, .nat a₀] with hctx
  have h0 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) rfl
  have hi := Det.get' (Det.get' h0 (Det.nat 0) (v := encFun ind) rfl) h1 (encFun_getElem? ind i)
  have hl := Det.get' (Det.get' h0 (Det.nat 1) (v := encFun lab) rfl) h1 (encFun_getElem? lab i)
  have ha := Det.get' h0 (Det.nat 2) (v := .nat a₀) rfl
  have e1 := Det.arith' (op := .eq) hi (Det.nat 1) (z := if ind i = 1 then 1 else 0) (by simp [BinOp.eval])
  have e2 := Det.arith' (op := .eq) hl ha (z := if lab i = a₀ then 1 else 0) (by simp [BinOp.eval])
  have hin := Det.ite' e2 (Det.nat 0 (P := P)) (Det.nat 1)
  have hout := Det.ite' e1 hin (Det.nat 0)
  refine FunDet.intro hf (hout.post fun c hc => ⟨?_, ?_⟩)
  · unfold splitVal; split_ifs <;> simp_all
  · have wI := wt_encFun_le ind (B := 1) hind
    have wL := wt_encFun_le lab (B := k) fun j => (hlab j).le
    have wC := wt_list3_le (encFun ind) (encFun lab) (.nat a₀)
    have wA := wt_list2_le ctx (.nat i)
    have := wt_nat_le a₀
    have := wt_nat_le (i : ℕ)
    have := wt_nat_le (ind i)
    have := wt_nat_le (lab i)
    have := hind i
    have := hlab i
    have := i.isLt
    have hb : ∀ p : Prop, [Decidable p] → (if p then 1 else 0 : ℕ) ≤ 1 := fun p _ => by
      split_ifs <;> omega
    have := hb (ind i = 1)
    have := hb (lab i = a₀)
    have hv : ∀ x y : ℕ, x ≤ 1 → y ≤ 1 → (Val.nat x).wt ≤ 3 ∧ (Val.nat y).wt ≤ 3 := by
      intro x y hx hy; exact ⟨by have := wt_nat_le x; omega, by have := wt_nat_le y; omega⟩
    have w01 : ∀ v : Val, v = .nat 0 ∨ v = .nat 1 → v.wt ≤ 3 := by
      rintro v (rfl | rfl) <;> simp [wt_nat, GI.Machine.len_zero]
    have wi1 : (if (if lab i = a₀ then 1 else 0) = 0 then Val.nat 1 else Val.nat 0).wt ≤ 3 :=
      w01 _ (by split_ifs <;> simp)
    have wo : (if (if ind i = 1 then 1 else 0) = 0 then Val.nat 0 else
        (if (if lab i = a₀ then 1 else 0) = 0 then Val.nat 1 else Val.nat 0)).wt ≤ 3 :=
      w01 _ (by split_ifs <;> simp)
    have hn0 : (Val.nat 0).wt ≤ 3 := w01 _ (Or.inl rfl)
    have hn1 : (Val.nat 1).wt ≤ 3 := w01 _ (Or.inr rfl)
    have hk2 : k * (2 * k + 5) + 4 ≤ 5 * (k + 1) ^ 2 := by nlinarith
    have hk1 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hco : ctx.wt = (Val.list [encFun ind, encFun lab, .nat a₀]).wt := rfl
    clear hout hin e1 e2 hi hl ha h0 h1
    omega

/-! ### What the test computes -/

theorem foldl_max_01 (l : List ℕ) (a : ℕ) (ha : a ≤ 1) (hl : ∀ x ∈ l, x ≤ 1) :
    l.foldl max a = if a = 1 ∨ 1 ∈ l then 1 else 0 := by
  induction l generalizing a with
  | nil =>
    simp only [List.foldl_nil, List.not_mem_nil, or_false]
    by_cases h : a = 1
    · simp [h]
    · rw [if_neg h]; omega
  | cons x l ih =>
    have hx := hl x (by simp)
    rw [List.foldl_cons, ih (max a x) (by omega) fun y hy => hl y (by simp [hy])]
    have : (max a x = 1 ∨ 1 ∈ l) ↔ (a = 1 ∨ 1 ∈ x :: l) := by
      simp only [List.mem_cons]
      by_cases hm : 1 ∈ l <;> simp only [hm, or_true, or_false] <;> omega
    simp only [this]

/-- The first point of a nonempty set. -/
theorem first_point (e : Ω ≃ Fin k) {D : Set Ω} (hne : D.Nonempty) :
    ∃ p : Fin k, ((List.finRange k).map (indF e D)).findIdx (fun x => decide (x = 1)) = p ∧
      e.symm p ∈ D := by
  classical
  obtain ⟨v, hv⟩ := hne
  have hex : ∃ x ∈ (List.finRange k).map (indF e D), decide (x = 1) = true := by
    refine ⟨indF e D (e v), List.mem_map_of_mem (List.mem_finRange _), ?_⟩
    simp [indF, hv]
  have hlt := List.findIdx_lt_length_of_exists hex
  rw [List.length_map, List.length_finRange] at hlt
  refine ⟨⟨_, hlt⟩, rfl, ?_⟩
  have := List.findIdx_getElem (w := by simpa using hlt) (p := fun x => decide (x = 1))
    (xs := (List.finRange k).map (indF e D))
  simp only [List.getElem_map, List.getElem_finRange, decide_eq_true_eq] at this
  by_contra hn
  simp [indF] at this
  simp only [List.findIdx_map] at hn
  exact hn this

open Classical in
/-- **The test decides whether the columns split the set.** -/
theorem test_value (e : Ω ≃ Fin k) {D : Set Ω} (c : Setoid Ω) (lab : Fin k → ℕ)
    (hlab : ∀ i j, lab i = lab j ↔ c.r (e.symm i) (e.symm j)) (p : Fin k) (hp : e.symm p ∈ D) :
    ((List.finRange k).map (splitVal (indF e D) lab (lab p))).foldl max 0 =
      if ∃ v ∈ D, ∃ w ∈ D, ¬ c.r v w then 1 else 0 := by
  classical
  rw [foldl_max_01 _ 0 (by omega) fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact splitVal_le_one _ _ _ _]
  have hiff : (0 = 1 ∨ 1 ∈ (List.finRange k).map (splitVal (indF e D) lab (lab p))) ↔
      ∃ v ∈ D, ∃ w ∈ D, ¬ c.r v w := by
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro (h | ⟨i, hi⟩)
      · omega
      · have h1 : e.symm i ∈ D := by
          by_contra h; simp [splitVal, indF, h] at hi
        have h2 : lab i ≠ lab p := by
          intro h; simp [splitVal, indF, h1, h] at hi
        exact ⟨e.symm i, h1, e.symm p, hp, fun h => h2 ((hlab i p).2 h)⟩
    · rintro ⟨v, hv, w, hw, hvw⟩
      right
      by_cases hvp : lab (e v) = lab p
      · refine ⟨e w, ?_⟩
        have hwp : lab (e w) ≠ lab p := fun h => hvw (by
          have := (hlab (e v) (e w)).1 (hvp.trans h.symm)
          simpa using this)
        simp [splitVal, indF, hw, hwp]
      · exact ⟨e v, by simp [splitVal, indF, hv, hvp]⟩
  simp only [hiff]


/-! ### The test on a column partition -/

/-- The weight of the list of `k` numbers at most `B`. -/
theorem wt_encFun_le' (f : Fin k → ℕ) {B : ℕ} (hf : ∀ i, f i ≤ B) (hB : k ≤ B) :
    (encFun f).wt ≤ 5 * (B + 1) ^ 2 := by
  have := wt_encFun_le f hf
  have : k * (2 * B + 5) ≤ B * (2 * B + 5) := Nat.mul_le_mul_right _ hB
  nlinarith

theorem splitTest_det {P : Program} {b : ℕ} (htest : P.funs[b]? = some (splitTestE (b + 2)
      (b + 6) (b + 9) (b + 12)))
    (hstep : P.funs[b + 1]? = some splitStepF) (hfind : P.HasAt (b + 2) (findEqFuns (b + 2)))
    (hmap : P.HasAt (b + 6) (mapFuns (b + 6) (b + 1))) (hrange : P.HasAt (b + 9) (rangeFuns (b + 9)))
    (hmax : P.HasAt (b + 12) (maxFuns (b + 12)))
    (ind lab : Fin k → ℕ) (hind : ∀ j, ind j ≤ 1) (hlab : ∀ j, lab j < k) (p : Fin k)
    (hp : ((List.finRange k).map ind).findIdx (fun x => decide (x = 1)) = p) :
    FunDet P b (.list [encFun lab, encFun ind])
      (.nat (((List.finRange k).map (splitVal ind lab (lab p))).foldl max 0))
      (10 ^ 7 * (k + 1) ^ 3) := by
  have hk1 : 1 ≤ k := by have := p.isLt; omega
  have pk : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (k + 1) ^ 2 ≤ (k + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have wI := wt_encFun_le' ind (B := k) (fun j => (hind j).trans hk1) le_rfl
  have wL := wt_encFun_le' lab (B := k) (fun j => (hlab j).le) le_rfl
  have hxs : ∀ x ∈ (List.finRange k).map ind, x ≤ k := by
    intro x hx; obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact (hind j).trans hk1
  -- Step 1: the first point of the orbit.
  have hF := findEq_spec hfind (xs := (List.finRange k).map ind) (j := 1) (B := k) hxs hk1
    (by simp)
  rw [hp] at hF
  have d1 := Det.call (Det.mk2 (Det.nat 1 (P := P) (env := [.list [encFun lab, encFun ind]]))
    (Det.arg' (vs := [encFun lab, encFun ind]) (rest := []) (j := 1)
      (v := natList ((List.finRange k).map ind)) (by simp [encFun_eq_natList]))) hF
  -- Step 2: the column label of that point.
  have d2 := Det.get' (Det.arg' (P := P) (vs := [encFun lab, encFun ind]) (rest := [.nat p])
    (j := 0) rfl) (Det.var' (i := 1) (v := .nat p) rfl) (encFun_getElem? lab p)
  -- Step 3: the map over the points, and the maximum.
  set env3 : List Val := [.list [encFun lab, encFun ind], .nat p, .nat (lab p)] with henv3
  have a1 := Det.arg' (P := P) (vs := [encFun lab, encFun ind]) (rest := [.nat p, .nat (lab p)])
    (j := 1) (v := encFun ind) rfl
  have a0 := Det.arg' (P := P) (vs := [encFun lab, encFun ind]) (rest := [.nat p, .nat (lab p)])
    (j := 0) (v := encFun lab) rfl
  have hctx := Det.mk3 a1 a0 (Det.var' (P := P) (env := env3) (i := 2) (v := .nat (lab p)) rfl)
  have a1' := Det.arg' (P := P) (vs := [encFun lab, encFun ind]) (rest := [.nat p, .nat (lab p)])
    (j := 1) (v := .list ((List.finRange k).map fun j => Val.nat (ind j))) rfl
  have hlen := Det.length a1'
  rw [show ((List.finRange k).map fun j => Val.nat (ind j)).length = k by simp] at hlen
  have hR : FunDet P (b + 9) (.nat k) (natList (List.range k)) (7000 * (k + 1) ^ 3) := by
    refine (range_spec hrange k).mono fun w cost hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hw.1, range_eq_encPerm_one] at hc
    have h1 := wt_encPerm_le (1 : Equiv.Perm (Fin k))
    have h2 := wt_nat_le k
    have h3 : loopModK * (k + 1) * ((Val.nat k).wt + k + (encPerm (1 : Equiv.Perm (Fin k))).wt + 1)
        ≤ loopModK * (k + 1) * (7 * (k + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    have h4 : loopModK * (k + 1) * (7 * (k + 1) ^ 2) = 7000 * (k + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega
  have drange := Det.call hlen hR
  -- The map.
  have hG : ∀ x ∈ (List.range k).map Val.nat,
      FunAll P (b + 1) (.list [.list [encFun ind, encFun lab, .nat (lab p)], x]) (fun w cost =>
        (∀ i : Fin k, x = .nat i → w = .nat (splitVal ind lab (lab p) i)) ∧
          cost ≤ 1000 * (k + 1) ^ 2) := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    refine FunAll.mono (splitStep_det hstep ind lab (lab p) ⟨j, hj⟩ hind hlab (hlab p))
      fun w cost hw => ⟨fun i hi => ?_, hw.2⟩
    simp only [Val.nat.injEq] at hi
    have : i = ⟨j, hj⟩ := Fin.ext hi.symm
    rw [this, hw.1]
  have hM := map_spec hmap hG
  have hxs' : (List.range k).map Val.nat = (List.finRange k).map fun i : Fin k => Val.nat (i : ℕ) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl
  set zs := (List.finRange k).map (splitVal ind lab (lab p)) with hzs
  have hzs_le : ∀ x ∈ zs, x ≤ k := by
    intro x hx; obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact (splitVal_le_one ind lab (lab p) j).trans hk1
  have wZ : (natList zs).wt ≤ 5 * (k + 1) ^ 2 := wt_natList_le_sq hzs_le (by simp [zs])
  have wC := wt_list3_le (encFun ind) (encFun lab) (.nat (lab p))
  have wlp := wt_nat_le (lab p)
  have hlp := hlab p
  have wRk : (natList (List.range k)).wt ≤ 4 * (k + 1) ^ 2 := by
    rw [range_eq_encPerm_one]; exact wt_encPerm_le _
  have hMd : FunDet P (b + 6) (.list [.list [encFun ind, encFun lab, .nat (lab p)],
      natList (List.range k)]) (natList zs) (10 ^ 6 * (k + 1) ^ 3) := by
    refine hM.mono fun w cost hw => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := hw
    rw [hxs'] at hws hc
    have hws' : ws = (List.finRange k).map fun i => Val.nat (splitVal ind lab (lab p) i) :=
      forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
    subst hws'
    refine ⟨by simp [natList, zs, List.map_map, Function.comp_def], ?_⟩
    simp only [List.map_map, List.length_map, List.length_finRange] at hc
    have hs : ((List.finRange k).map ((fun _ => 1000 * (k + 1) ^ 2) ∘
        fun i : Fin k => Val.nat (i : ℕ))).sum = k * (1000 * (k + 1) ^ 2) := by
      rw [show ((fun _ => 1000 * (k + 1) ^ 2) ∘ fun i : Fin k => Val.nat (i : ℕ)) =
        fun _ => 1000 * (k + 1) ^ 2 from rfl, List.map_const', List.sum_replicate,
        List.length_finRange, smul_eq_mul]
    rw [hs] at hc
    have e1 : (Val.list [.list [encFun ind, encFun lab, .nat (lab p)],
        .list ((List.finRange k).map fun i : Fin k => Val.nat (i : ℕ))]).wt =
        (Val.list [.list [encFun ind, encFun lab, .nat (lab p)], natList (List.range k)]).wt := by
      rw [← hxs']; rfl
    have e2 : (Val.list ((List.finRange k).map fun i => Val.nat (splitVal ind lab (lab p) i))).wt =
        (natList zs).wt := by simp [natList, zs, List.map_map, Function.comp_def]
    rw [e1, e2] at hc
    have wA := wt_list2_le (.list [encFun ind, encFun lab, .nat (lab p)]) (natList (List.range k))
    have h1 : k * (1000 * (k + 1) ^ 2) ≤ 1000 * (k + 1) ^ 3 := by nlinarith
    have h2 : mapK * (k + 1) * ((Val.list [.list [encFun ind, encFun lab, .nat (lab p)],
        natList (List.range k)]).wt + (natList zs).wt + 1) ≤ mapK * (k + 1) * (200 * (k + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : mapK * (k + 1) * (200 * (k + 1) ^ 2) = 200000 * (k + 1) ^ 3 := by
      simp only [mapK]; ring
    omega
  have dmap := Det.call (Det.mk2 hctx drange) hMd
  have hX := max_spec hmax hzs_le (by simp [zs])
  have dmax := Det.call dmap hX
  refine FunDet.intro htest ((Det.letE d1 (Det.letE d2 dmax)).mono ?_)
  have wA := wt_list2_le (encFun lab) (encFun ind)
  have wF := wt_list2_le (.nat 1) (natList ((List.finRange k).map ind))
  have wFi : (natList ((List.finRange k).map ind)).wt = (encFun ind).wt := by
    rw [encFun_eq_natList]
  have wp := wt_nat_le (p : ℕ)
  have hpk := p.isLt
  have w1 := wt_nat_le 1
  have wk := wt_nat_le k
  have wmx := wt_nat_le (zs.foldl max 0)
  have hmx : zs.foldl max 0 ≤ k := foldl_max_le (Nat.zero_le _) hzs_le
  have wCR := wt_list2_le (.list [encFun ind, encFun lab, .nat (lab p)]) (natList (List.range k))
  have wlen : (Val.list ((List.finRange k).map fun j => Val.nat (ind j))).wt = (encFun ind).wt := rfl
  have wlab : (Val.nat (lab p)).wt ≤ k + 2 := by omega
  have p13 : 1 ≤ (k + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  simp only [findEqK, maxK] at *
  clear d1 d2 dmax dmap drange hctx a0 a1 a1' hlen hM hMd hX hF hG hR
  omega

/-! ### The module -/

/-- The cost constant of the row-test module. -/
def splitK : ℕ := 10 ^ 9

open Classical in
/-- **The row test meets its specification**: on `[rows, ind D]`, with the row record of a state
and a nonempty set `D`, it returns `1` if the retained columns split `D` (`State.ColsSplit`) and
`0` otherwise. -/
theorem split_spec {P : Program} {b : ℕ} (h : P.HasAt b (splitFuns b)) (e : Ω ≃ Fin k)
    (S : State Ω C) {rv : Val} (hrv : OptVal (RowValC e) rv S.rows) {D : Set Ω}
    (hne : D.Nonempty) :
    FunDet P b (.list [rv, indVal e D]) (.nat (if S.ColsSplit D then 1 else 0))
      (splitK * ((Val.list [rv, indVal e D]).wt + 1) ^ 3) := by
  have hentry : P.funs[b]? = some (splitE (b + 1)) := (h.block 0 rfl : P.HasAt (b + 0) _).single
  have htest : P.funs[b + 1]? = some (splitTestE (b + 1 + 2) (b + 1 + 6) (b + 1 + 9)
      (b + 1 + 12)) := (h.block 1 rfl : P.HasAt (b + 1) _).single
  have hstep : P.funs[b + 1 + 1]? = some splitStepF := (h.block 2 rfl : P.HasAt (b + 2) _).single
  have hfind : P.HasAt (b + 1 + 2) (findEqFuns (b + 1 + 2)) := h.block 3 rfl
  have hmap : P.HasAt (b + 1 + 6) (mapFuns (b + 1 + 6) (b + 1 + 1)) := h.block 7 rfl
  have hrange : P.HasAt (b + 1 + 9) (rangeFuns (b + 1 + 9)) := h.block 10 rfl
  have hmax : P.HasAt (b + 1 + 12) (maxFuns (b + 1 + 12)) := h.block 13 rfl
  set W := (Val.list [rv, indVal e D]).wt with hW
  have wI : (indVal e D).wt < W := wt_le_wt_list (by simp)
  have wR : rv.wt < W := wt_le_wt_list (by simp)
  have hkI : k < (indVal e D).wt := by
    have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (indF e D i))
    simpa using this
  have W1 : W + 1 ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have harg0 := Det.arg' (P := P) (vs := [rv, indVal e D]) (rest := []) (j := 0) (v := rv) rfl
  have harg1 := Det.arg' (P := P) (vs := [rv, indVal e D]) (rest := []) (j := 1)
    (v := indVal e D) rfl
  cases hS : S.rows with
  | none =>
    rw [hS] at hrv
    change rv = .list [] at hrv
    subst hrv
    have hc : S.ColsSplit D := fun R hR => by rw [hS] at hR; cases hR
    rw [if_pos hc]
    have hl := Det.length harg0
    refine FunDet.intro hentry ((Det.ite_zero hl (Det.nat 1)).mono ?_)
    have := wt_nat_le 1
    simp only [List.length_nil, splitK]
    omega
  | some R =>
    rw [hS] at hrv
    obtain ⟨u, ⟨rv', cv, hrows, hcols, rfl⟩, rfl⟩ := hrv
    have hl0 := Det.length harg0
    have hu := Det.get' harg0 (Det.nat 0) (v := .list [.nat R.m, rv', cv]) rfl
    have hcv := Det.get' hu (Det.nat 2) (v := cv) rfl
    have wu : (Val.list [.nat R.m, rv', cv]).wt < W :=
      (wt_le_wt_list (by simp)).trans wR
    have wcv : cv.wt < W := (wt_le_wt_list (by simp)).trans wu
    cases hc : R.cols with
    | none =>
      rw [hc] at hcols
      change cv = .list [] at hcols
      subst hcols
      have hns : ¬ S.ColsSplit D := fun h' => by
        obtain ⟨c, hc', -⟩ := h' R hS
        rw [hc] at hc'; cases hc'
      rw [if_neg hns]
      have hl := Det.length hcv
      refine FunDet.intro hentry ((Det.ite_pos hl0 (by simp)
        (Det.ite_zero hl (Det.nat 0))).mono ?_)
      have := wt_nat_le 0
      have := wt_nat_le 1
      simp only [List.length_nil, List.length_cons, splitK]
      omega
    | some c =>
      rw [hc] at hcols
      obtain ⟨lv, ⟨lab, rfl, hlabk, hlab⟩, rfl⟩ := hcols
      obtain ⟨p, hp, hpD⟩ := first_point e hne
      have hT := splitTest_det htest hstep hfind hmap hrange hmax (indF e D) lab
        (indF_le_one e D) hlabk p hp
      rw [test_value e c lab hlab p hpD] at hT
      have hiff : S.ColsSplit D ↔ ∃ v ∈ D, ∃ w ∈ D, ¬ c.r v w := by
        constructor
        · intro h'
          obtain ⟨c', hc', h2⟩ := h' R hS
          rw [hc] at hc'; cases hc'; exact h2
        · intro h' R' hR'
          rw [hS] at hR'; cases hR'
          exact ⟨c, hc, h'⟩
      have hval : (if (∃ v ∈ D, ∃ w ∈ D, ¬ c.r v w) then 1 else 0) =
          (if S.ColsSplit D then 1 else 0 : ℕ) := by
        by_cases h' : S.ColsSplit D
        · rw [if_pos h', if_pos (hiff.1 h')]
        · rw [if_neg h', if_neg (fun h'' => h' (hiff.2 h''))]
      rw [hval] at hT
      have hl := Det.length hcv
      have hlv := Det.get' hcv (Det.nat 0) (v := encFun lab) rfl
      have hcall := Det.call (Det.mk2 hlv harg1) hT
      refine FunDet.intro hentry ((Det.ite_pos hl0 (by simp)
        (Det.ite_pos hl (by simp) hcall)).mono ?_)
      have wlv : (encFun lab).wt < W := (wt_le_wt_list (by simp)).trans wcv
      have wA := wt_list2_le (encFun lab) (indVal e D)
      have wv : (Val.nat (if S.ColsSplit D then 1 else 0)).wt ≤ 3 := by
        split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
      have hk3 : 10 ^ 7 * (k + 1) ^ 3 ≤ 10 ^ 7 * (W + 1) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      simp only [List.length_cons, List.length_nil, splitK]
      clear hT hcall hlv hl hcv hu hl0 harg0 harg1
      omega

end GI.Impl
