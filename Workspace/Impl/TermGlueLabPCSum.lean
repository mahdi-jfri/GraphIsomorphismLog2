import Workspace.Impl.TermGlueLabPSup
import Workspace.Impl.LinElementMap
import Workspace.Lang.Lib.LinIntVector

/-!
# Coordinate sums of elements of `N`

Step 5 of the label program. The label points and the offsets are products of
classes `[n]` of elements `n ∈ N` (`p_x = Π [n_i]`, `u(h) = Π [s_i] · Π [h⁻¹ k_i(h)]`). In
coordinates these products are sums of the coordinate vectors of the elements. The module
`tmGLPCSumFuns b ec add` computes such a sum: on `[gens N, [x_1, …, x_k]]` it adds the
coordinate vectors of `1, x_1, …, x_k` (`linElementCoordinates` at `ec`, which calls
ConstructiveMembership once per element; vector addition at `add`).

`tmGLPCSum_spec`: the result is `linVecVal z` with `z` the sum of one coordinate vector of each
element (`TmGLPCoordOf`), cost `tmGLPCSumC`. `tmGLPCSum_map`: under every abelian quotient map
`π` of `N`, the
point `z` maps to `Π π(x_i)` (`linElementCoordinates_map`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens MemberInst memberInput SlpReaches encInt)

variable {n : ℕ}

/-- `z` is a coordinate vector of `x` over the generators `as`, as computed by
`linElementCoordinates`. -/
def TmGLPCoordOf (as : List (Perm (Fin n))) (x : Perm (Fin n)) (z : Fin as.length → ℤ) : Prop :=
  ∃ prog : List GI.Cited.SlpInstr, SlpReaches as prog x ∧
    linExponentValue (linPrefixVectors as.length 0 as.length) prog = some z

/-! ### The mathematics -/

open Classical in
/-- An element of `⟨as⟩` read in a quotient, and `1` outside. -/
noncomputable def tmGLPπ (as : List (Perm (Fin n))) {Q : Type*} [CommGroup Q] (π : gens as →* Q)
    (x : Perm (Fin n)) : Q :=
  if h : x ∈ gens as then π ⟨x, h⟩ else 1

/-- **A sum of coordinate vectors maps to the product.** -/
theorem tmGLPCSum_map (as : List (Perm (Fin n))) {Q : Type*} [CommGroup Q] (π : gens as →* Q)
    {xs : List (Perm (Fin n))} (hx : ∀ x ∈ xs, x ∈ gens as) {zs : List (Fin as.length → ℤ)}
    (hz : List.Forall₂ (TmGLPCoordOf as) xs zs) :
    linCoordHom (fun i : Fin as.length => π (linIntoSubgroup (gens as) as[i.val]))
      (Multiplicative.ofAdd zs.sum) = (xs.map (tmGLPπ as π)).prod := by
  induction hz with
  | nil => simp
  | @cons x z xs zs hxz _ ih =>
    obtain ⟨prog, hp, he⟩ := hxz
    have hx0 : x ∈ gens as := hx x (List.mem_cons_self ..)
    rw [List.sum_cons, ofAdd_add, map_mul, ih fun y hy => hx y (List.mem_cons_of_mem _ hy),
      linElementCoordinates_map as π x hx0 prog z hp he, List.map_cons, List.prod_cons]
    simp only [tmGLPπ, dif_pos hx0]

/-! ### The program -/

/-- One step, on `[a, i, acc]` with `a = [gens N, xs, acc0]`: add the coordinates of `xs[i]`. -/
def tmGLPCStep (ec add : ℕ) : Expr :=
  .call add (mk2 (arg 2) (.call ec (mk2 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1)))))

/-- The entry, on `[gens N, xs]`: the loop from the coordinates of `1`. -/
def tmGLPCSumF (loop ec : ℕ) : Expr :=
  .call loop (mk3 (arg 0) (arg 1) (.call ec (mk2 (arg 0) (.get (.get (arg 0) (.nat 1)) (.nat 0)))))

/-- **Coordinate sums** (4 functions), with `linElementCoordinates` at `ec` and vector addition
at `add`. -/
def tmGLPCSumFuns (b ec add : ℕ) : List Expr :=
  [tmGLPCSumF (b + 1) ec] ++
    loopFuns (b + 1) (.length (.get (.var 0) (.nat 1))) (.get (.var 0) (.nat 2)) (tmGLPCStep ec add)

theorem length_tmGLPCSumFuns (b ec add : ℕ) : (tmGLPCSumFuns b ec add).length = 4 := rfl

/-! ### The specification -/

/-- The bound on one coordinate call, for an input of weight `W`, when `Ce (W + 2)^De` bounds
`linElementBudget`. -/
def tmGLPBud (Ce De W : ℕ) : ℕ := Ce * (20 * (W + 1) ^ 2 + 2) ^ De

/-- The bound on the weight of the accumulator. -/
def tmGLPMacc (Ce De W : ℕ) : ℕ := (W + 1) * (41 * (tmGLPBud Ce De W + W + 1)) + 4

/-- The bound on one vector addition. -/
def tmGLPVB (Ce De W : ℕ) : ℕ :=
  linVectorBinaryCost (2 * (tmGLPMacc Ce De W + tmGLPBud Ce De W) + 6) W
    (20 * (2 * (tmGLPMacc Ce De W + tmGLPBud Ce De W) + 8))

/-- The cost bound of the coordinate sum. -/
def tmGLPCSumC (Ce De W : ℕ) : ℕ :=
  (W + 1) * (3 * tmGLPBud Ce De W + 2 * tmGLPVB Ce De W +
      10 ^ 4 * (tmGLPMacc Ce De W + tmGLPBud Ce De W + (W + 1) ^ 2)) +
    10 ^ 5 * (W + 2) * (tmGLPMacc Ce De W + tmGLPBud Ce De W + 20 * (W + 1) ^ 2)

/-- The loop state after the elements `j < i`. -/
def TmGLPCInv (as xs : List (Perm (Fin n))) (B i : ℕ) (acc : Val) : Prop :=
  ∃ zs : List (Fin as.length → ℤ), List.Forall₂ (TmGLPCoordOf as) (1 :: xs.take i) zs ∧
    acc = linVecVal zs.sum ∧ ∀ j, (zs.sum j).natAbs < (i + 1) * 2 ^ B

theorem tmGLP_n_lt_encGroup (as : List (Perm (Fin n))) : n < (encGroup as).wt := by
  have h1 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: as).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have h2 : (Val.list ((1 :: as).map encPerm)).wt <
      (Val.list [.nat n, .list ((1 :: as).map encPerm)]).wt := wt_le_wt_list (by simp)
  have := tmGLP_n_lt_wt (1 : Perm (Fin n))
  change n < (Val.list [.nat n, .list ((1 :: as).map encPerm)]).wt
  omega

theorem tmGLP_len_lt_encGroup (as : List (Perm (Fin n))) : as.length < (encGroup as).wt := by
  have h1 := length_lt_wt_list ((1 :: as).map encPerm)
  have h2 : (Val.list ((1 :: as).map encPerm)).wt <
      (Val.list [.nat n, .list ((1 :: as).map encPerm)]).wt := wt_le_wt_list (by simp)
  simp only [List.length_map, List.length_cons] at h1
  change as.length < (Val.list [.nat n, .list ((1 :: as).map encPerm)]).wt
  omega

/-- The weight of an integer vector from bounds on its entries. -/
theorem tmGLP_vec_wt {t : ℕ} (z : Fin t → ℤ) {B : ℕ} (hz : ∀ j, (z j).natAbs < 2 ^ B) :
    (linVecVal z).wt ≤ t * (2 * (20 * (B + 1)) + 1) + 4 := by
  have h := wt_list_le_of (l := (List.finRange t).map fun i => encInt (z i)) (A := 20 * (B + 1))
    (by
      intro v hv
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
      exact linWtInt (hz j))
  simpa [linVecVal] using h

/-- The arithmetic of the final cost of the coordinate sum. -/
theorem tmGLP_csum_aux {ca cb ww c0 aw A L B W S M Bd : ℕ}
    (hca : ca ≤ 100 * S + c0 + aw + 1) (hc0 : c0 ≤ 2 * Bd + 100 * S + 1)
    (haw : aw ≤ 4 * W + 2 * M + 7) (hcb : cb ≤ A + L) (h1 : A ≤ B)
    (h2 : L ≤ 1000 * ((W + 2) * (4 * M + 20 * S))) (hww : ww ≤ M) (hS : W + 1 ≤ S) :
    ca + cb + ww + 1 ≤ B + 10 ^ 5 * (W + 2) * (M + Bd + 20 * S) := by
  have h3 : (W + 2) * (4 * M + 20 * S) ≤ 4 * ((W + 2) * (M + Bd + 20 * S)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 4 (W + 2), Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  have h5 : M + Bd + 20 * S ≤ (W + 2) * (M + Bd + 20 * S) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have e : 10 ^ 5 * (W + 2) * (M + Bd + 20 * S) = 10 ^ 5 * ((W + 2) * (M + Bd + 20 * S)) := by
    ring
  rw [e]
  generalize (W + 2) * (M + Bd + 20 * S) = X at h3 h5 ⊢
  generalize (W + 2) * (4 * M + 20 * S) = Y at h2 h3
  omega

/-- Arithmetic of one coordinate call. -/
private theorem tmGLP_ar1 {ca c w B X : ℕ} (h1 : ca ≤ X) (h2 : c ≤ B) (h3 : w < c) :
    ca + c + w + 1 ≤ 2 * B + X + 1 := by omega

/-- The entry bound after one more element. -/
private theorem tmGLP_ar2 {s a b i B : ℕ} (h : s ≤ a + b) (ha : a < (i + 1) * B) (hb : b < B) :
    s < (i + 1 + 1) * B := by
  rw [Nat.add_mul, one_mul]; omega

/-- Arithmetic of one loop step. -/
private theorem tmGLP_step_ar {ca cw cu uw L Bud Macc W VB S X : ℕ}
    (hca : ca ≤ 100 * (Macc + W + 1) + cw + 2 * L + 7)
    (hcw : cw ≤ 2 * Bud + 100 * (Macc + W + 1) + 1) (hL : L ≤ 2 * (Macc + Bud) + 6)
    (hcu : cu ≤ VB) (hu : uw ≤ Macc) (hS : W + 1 ≤ S) :
    ca + cu + uw + 1 ≤ 3 * Bud + 2 * VB + 10 ^ 3 * (Macc + Bud + S) + X := by omega

/-- **The coordinate sum.** On `[gens N, [x_1, …, x_k]]` with all `x_i ∈ N`, the result is
`linVecVal z` with `z` the sum of coordinate vectors of `1, x_1, …, x_k`. -/
theorem tmGLPCSum_spec (hm : GI.Cited.ConstructiveMembership) {P : Program} {b ec add ib jm : ℕ}
    (h : P.HasAt b (tmGLPCSumFuns b ec add)) (hec : linElementCoordinatesAt P ec jm hm)
    (hib : linIntSpec P ib) (hadd : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    {Ce De : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (σN xs : List (Perm (Fin n))) (hx : ∀ x ∈ xs, x ∈ gens σN) :
    FunAll P b (.list [encGroup σN, .list (xs.map encPerm)]) (fun u c =>
      ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: xs) zs ∧
        u = linVecVal zs.sum ∧
        c ≤ tmGLPCSumC Ce De (Val.list [encGroup σN, .list (xs.map encPerm)]).wt) := by
  set a0 : Val := .list [encGroup σN, .list (xs.map encPerm)] with ha0
  set W := a0.wt with hW
  set Bud := tmGLPBud Ce De W with hBud
  set Macc := tmGLPMacc Ce De W with hMacc
  set t := σN.length with ht
  have hentry : P.funs[b]? = some (tmGLPCSumF (b + 1) ec) :=
    by simpa using (h.block (gs := [tmGLPCSumF (b + 1) ec]) 0 rfl).single
  have hloop : P.HasAt (b + 1) (loopFuns (b + 1) (.length (.get (.var 0) (.nat 1)))
      (.get (.var 0) (.nat 2)) (tmGLPCStep ec add)) := h.block 1 rfl
  -- weights of the input
  have wN : (encGroup σN).wt < W := wt_le_wt_list (by simp)
  have wxs : (Val.list (xs.map encPerm)).wt < W := wt_le_wt_list (by simp)
  have hnW : n < W := (tmGLP_n_lt_encGroup σN).trans wN
  have htW : t < W := (tmGLP_len_lt_encGroup σN).trans wN
  have hkW : xs.length < W := by
    have := length_lt_wt_list (xs.map encPerm)
    simp only [List.length_map] at this
    omega
  have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- one coordinate call
  have hcall : ∀ x : Perm (Fin n), x ∈ gens σN →
      FunAll P ec (.list [encGroup σN, encPerm x]) (fun w c =>
        ∃ z : Fin t → ℤ, TmGLPCoordOf σN x z ∧ w = linVecVal z ∧ c ≤ Bud ∧
          (∀ j, (z j).natAbs < 2 ^ Bud) ∧ (linVecVal z).wt ≤ Bud) := by
    intro x hxN
    have hsp := linElementCoordinates_spec hm hec ⟨n, σN, x⟩ hxN
    refine (FunAll.wt_lt hsp).mono fun w c ⟨⟨⟨prog, z, hw, hp, he⟩, hc⟩, hwc⟩ => ?_
    have hmi : (memberInput ⟨n, σN, x⟩).wt ≤ 20 * (W + 1) ^ 2 := by
      have := wt_list2_le (encGroup σN) (encPerm x)
      have := wt_encPerm_le x
      have := Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2
      change (Val.list [encGroup σN, encPerm x]).wt ≤ _
      omega
    have hcB : c ≤ Bud := by
      refine hc.trans ((linElementCoordinatesCost_le hm _).trans ((hEB _).trans ?_))
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    refine ⟨z, ⟨prog, hp, he⟩, hw, hcB, fun j => ?_, by rw [← hw]; omega⟩
    have h1 := linVecEntryWt z j
    rw [← hw] at h1
    exact (linEncIntAbs (z j)).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- the accumulator bound
  have hMacc : ∀ i acc, i ≤ (xs.map encPerm).length → TmGLPCInv σN xs Bud i acc →
      acc.wt ≤ Macc := by
    rintro i acc hi ⟨zs, -, rfl, hzs⟩
    have hik : i ≤ W := by simp only [List.length_map] at hi; omega
    have h2 : ∀ j, (zs.sum j).natAbs < 2 ^ (Bud + W) := fun j => by
      have h1 : (i + 1) * 2 ^ Bud ≤ 2 ^ (Bud + W) := by
        rw [pow_add, mul_comm]
        exact Nat.mul_le_mul_left _ ((Nat.lt_two_pow_self).trans_le
          (Nat.pow_le_pow_right (by norm_num) hik))
      exact (hzs j).trans_le h1
    have := tmGLP_vec_wt _ h2
    have h3 : t * (2 * (20 * (Bud + W + 1)) + 1) ≤ (W + 1) * (41 * (Bud + W + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e1 : (W + 1) * (41 * (tmGLPBud Ce De W + W + 1)) = (W + 1) * (41 * (Bud + W + 1)) := rfl
    have e2 : σN.length * (2 * (20 * (Bud + W + 1)) + 1) = t * (2 * (20 * (Bud + W + 1)) + 1) := rfl
    change _ ≤ (W + 1) * (41 * (tmGLPBud Ce De W + W + 1)) + 4
    omega
  -- the entry
  apply FunAll.intro hentry
  have g0 := Det.arg' (P := P) (vs := [encGroup σN, .list (xs.map encPerm)]) (rest := []) (j := 0)
    rfl
  have g1 := Det.arg' (P := P) (vs := [encGroup σN, .list (xs.map encPerm)]) (rest := []) (j := 1)
    rfl
  have d1 := Det.get' (Det.get' g0 (Det.nat 1) (vs := [.nat n, .list ((1 :: σN).map encPerm)])
    (v := .list ((1 :: σN).map encPerm)) rfl) (Det.nat 0) (vs := (1 :: σN).map encPerm)
    (v := encPerm 1) rfl
  have w1 : (encPerm (1 : Perm (Fin n))).wt < (encGroup σN).wt := by
    have h1 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: σN).map encPerm)).wt :=
      wt_le_wt_list (by simp)
    have h2 : (Val.list ((1 :: σN).map encPerm)).wt <
        (Val.list [.nat n, .list ((1 :: σN).map encPerm)]).wt := wt_le_wt_list (by simp)
    exact h1.trans h2
  have hl1 : (Val.list ((1 :: σN).map encPerm)).wt < (encGroup σN).wt := by
    have h2 : (Val.list ((1 :: σN).map encPerm)).wt <
        (Val.list [.nat n, .list ((1 :: σN).map encPerm)]).wt := wt_le_wt_list (by simp)
    exact h2
  have e0 : (Val.list [encGroup σN, .list (xs.map encPerm)]).wt = W := rfl
  have wp1 := wt_encPerm_le (1 : Perm (Fin n))
  have dargs := (Det.mk2 g0 d1).mono (c' := 100 * (W + 1) ^ 2) (by
    have := wt_list2_le (encGroup σN) (encPerm (1 : Perm (Fin n)))
    omega)
  have h0call : EvalAll P [a0] (.call ec (mk2 (arg 0) (.get (.get (arg 0) (.nat 1)) (.nat 0))))
      (fun w c => ∃ z : Fin t → ℤ, TmGLPCoordOf σN 1 z ∧ w = linVecVal z ∧
        c ≤ 2 * Bud + 100 * (W + 1) ^ 2 + 1 ∧ ∀ j, (z j).natAbs < 2 ^ Bud) := by
    refine EvalAll.call_funAll dargs fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine ((hcall 1 (gens σN).one_mem).wt_lt).mono fun w c ⟨⟨z, hz, hw, hc, hzb, _⟩, hwc⟩ =>
      ⟨z, hz, hw, by omega, hzb⟩
  have dg01 := (Det.mk2 g0 g1).mono (c' := 100 * (W + 1) ^ 2) (by
    have := wt_list2_le (encGroup σN) (.list (xs.map encPerm))
    omega)
  refine EvalAll.call_funAll (EvalAll.snoc_det dg01 h0call) fun v ca hv => ?_
  obtain ⟨w0, c0, ⟨z0, hz0, rfl, hc0, hz0b⟩, rfl, hca⟩ := hv
  simp only [List.cons_append, List.nil_append] at hca ⊢
  -- the loop
  set a : Val := .list [encGroup σN, .list (xs.map encPerm), linVecVal z0] with ha
  set k := (xs.map encPerm).length with hk
  have hkx : k = xs.length := by simp [hk]
  have wz0 : (linVecVal z0).wt ≤ Macc := by
    have := tmGLP_vec_wt z0 hz0b
    have h3 : t * (2 * (20 * (Bud + 1)) + 1) ≤ (W + 1) * (41 * (Bud + W + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e1 : (W + 1) * (41 * (tmGLPBud Ce De W + W + 1)) = (W + 1) * (41 * (Bud + W + 1)) := rfl
    have e2 : σN.length * (2 * (20 * (Bud + 1)) + 1) = t * (2 * (20 * (Bud + 1)) + 1) := rfl
    change _ ≤ (W + 1) * (41 * (tmGLPBud Ce De W + W + 1)) + 4
    omega
  have wa := wt_list3_le (encGroup σN) (.list (xs.map encPerm)) (linVecVal z0)
  have ea : a.wt = (Val.list [encGroup σN, .list (xs.map encPerm), linVecVal z0]).wt := rfl
  have dk : Det P [a] (.length (.get (.var 0) (.nat 1))) (.nat k) _ :=
    Det.length (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) (Det.nat 1)
      (vs := [encGroup σN, .list (xs.map encPerm), linVecVal z0]) (v := .list (xs.map encPerm)) rfl)
  have dacc := Det.get' (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) (Det.nat 2)
    (vs := [encGroup σN, .list (xs.map encPerm), linVecVal z0]) (v := linVecVal z0) rfl
  have hInv0 : TmGLPCInv σN xs Bud 0 (linVecVal z0) :=
    ⟨[z0], by simpa using hz0, by simp, fun j => by simpa using hz0b j⟩
  have hVB : ∀ x y : Fin t → ℤ, (linVecVal x).wt ≤ Macc → (linVecVal y).wt ≤ Bud →
      linVectorBinaryCost (Val.list [linVecVal x, linVecVal y]).wt t
        (20 * ((Val.list [linVecVal x, linVecVal y]).wt + 2)) ≤ tmGLPVB Ce De W := by
    intro x y hx hy
    have := wt_list2_le (linVecVal x) (linVecVal y)
    exact linVectorBinaryCost_mono (by omega) htW.le (by omega)
  have wa1 : (Val.list (xs.map encPerm)).wt < a.wt := wt_le_wt_list (by simp)
  have wa2 : (linVecVal z0).wt < a.wt := wt_le_wt_list (by simp)
  have wa3 := a.two_le_size.trans a.size_le_wt
  have hloopS := loopBdd_spec hloop dk dacc (by omega) (M := Macc)
    (Inv := TmGLPCInv σN xs Bud) hInv0 hMacc
    (D := fun _ => 3 * Bud + 2 * tmGLPVB Ce De W + 10 ^ 3 * (Macc + Bud + (W + 1) ^ 2)) ?_
  · refine hloopS.mono fun w cb ⟨hinv, hcb⟩ => ?_
    have hwM := hMacc k w le_rfl hinv
    obtain ⟨zs, hzs, hw, -⟩ := hinv
    refine ⟨zs, ?_, hw, ?_⟩
    · rwa [hkx, List.take_of_length_le (le_refl _)] at hzs
    · have hcb' : cb ≤ k * (3 * Bud + 2 * tmGLPVB Ce De W + 10 ^ 3 * (Macc + Bud + (W + 1) ^ 2)) +
          loopModK * (k + 1) * (a.wt + k + Macc + 1) := by
        simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using hcb
      have hkW' : k ≤ W := by omega
      have h1 : k * (3 * Bud + 2 * tmGLPVB Ce De W + 10 ^ 3 * (Macc + Bud + (W + 1) ^ 2)) ≤
          (W + 1) * (3 * Bud + 2 * tmGLPVB Ce De W + 10 ^ 4 * (Macc + Bud + (W + 1) ^ 2)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : loopModK * (k + 1) * (a.wt + k + Macc + 1) ≤
          1000 * ((W + 2) * (4 * Macc + 20 * (W + 1) ^ 2)) := by
        rw [Nat.mul_assoc]; unfold loopModK
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      have haw : a.wt ≤ 4 * W + 2 * Macc + 7 := by omega
      exact tmGLP_csum_aux hca hc0 haw hcb' h1 h2 hwM hS
  · rintro i acc hi hinv
    have haccM := hMacc i acc hi.le hinv
    obtain ⟨zs, hzs, rfl, hzb⟩ := hinv
    have hi' : i < xs.length := by omega
    have hxi : (xs.map encPerm)[i]? = some (encPerm (xs[i]'hi')) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi']; rfl
    have hxN : (xs[i]'hi') ∈ gens σN := hx _ (List.getElem_mem hi')
    have g0 := Det.arg' (P := P) (vs := [a, .nat i, linVecVal zs.sum]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [a, .nat i, linVecVal zs.sum]) (rest := []) (j := 1) rfl
    have g2 := Det.arg' (P := P) (vs := [a, .nat i, linVecVal zs.sum]) (rest := []) (j := 2) rfl
    have dN := Det.get' g0 (Det.nat 0) (vs := [encGroup σN, .list (xs.map encPerm), linVecVal z0])
      (v := encGroup σN) rfl
    have dxs := Det.get' g0 (Det.nat 1) (vs := [encGroup σN, .list (xs.map encPerm), linVecVal z0])
      (v := .list (xs.map encPerm)) rfl
    have dx := Det.get' dxs g1 hxi
    have wi := wt_nat_le i
    have wx : (encPerm (xs[i]'hi')).wt < (Val.list (xs.map encPerm)).wt :=
      wt_le_wt_list (List.mem_of_getElem? hxi)
    have wm := wt_list2_le (encGroup σN) (encPerm (xs[i]'hi'))
    have wA : (Val.list [a, .nat i, linVecVal zs.sum]).wt ≤
        2 * (a.wt + (Val.nat i).wt + (linVecVal zs.sum).wt) + 7 := wt_list3_le _ _ _
    have dargs := (Det.mk2 dN dx).mono (c' := 100 * (Macc + W + 1)) (by omega)
    have dacc := g2.mono (c' := 100 * (Macc + W + 1)) (by omega)
    have hz : EvalAll P [.list [a, .nat i, linVecVal zs.sum]]
        (.call ec (mk2 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))))
        (fun w c => ∃ z : Fin t → ℤ, TmGLPCoordOf σN (xs[i]'hi') z ∧ w = linVecVal z ∧
          c ≤ 2 * Bud + 100 * (Macc + W + 1) + 1 ∧ (∀ j, (z j).natAbs < 2 ^ Bud) ∧
          (linVecVal z).wt ≤ Bud) := by
      refine EvalAll.call_funAll dargs fun v ca hv => ?_
      obtain ⟨rfl, hca⟩ := hv
      refine ((hcall (xs[i]'hi') hxN).wt_lt).mono fun w c ⟨⟨z, hz, hw, hc, hzb, hzw⟩, hwc⟩ =>
        ⟨z, hz, hw, tmGLP_ar1 hca hc hwc, hzb, hzw⟩
    refine EvalAll.call_funAll (EvalAll.mk2_last dacc hz) fun v ca hv => ?_
    obtain ⟨w, cw, ⟨z, hzc, rfl, hcw, hzzb, hwz⟩, rfl, hca⟩ := hv
    have hadd' := linVectorAdd_spec hib hadd zs.sum z
    refine FunAll.mono hadd' fun u cu ⟨hu, hcu⟩ => ?_
    have hinv' : TmGLPCInv σN xs Bud (i + 1) u := by
      refine ⟨zs ++ [z], ?_, ?_, ?_⟩
      · rw [List.take_add_one, List.getElem?_eq_getElem hi']
        exact List.rel_append hzs (List.Forall₂.cons hzc List.Forall₂.nil)
      · rw [hu, List.sum_append, List.sum_singleton]
        exact congrArg linVecVal (funext fun j => (Pi.add_apply _ _ j).symm)
      · intro j
        have e : ((zs ++ [z]).sum j) = zs.sum j + z j := by
          rw [List.sum_append, List.sum_singleton, Pi.add_apply]
        rw [e]
        exact tmGLP_ar2 (Int.natAbs_add_le (zs.sum j) (z j)) (hzb j) (hzzb j)
    have hum := hMacc (i + 1) u hi hinv'
    refine ⟨hinv', ?_⟩
    have hvb := hVB zs.sum z haccM hwz
    have hL : (Val.list [linVecVal zs.sum, linVecVal z]).wt ≤ 2 * (Macc + Bud) + 6 :=
      (wt_list2_le _ _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add haccM hwz)) 6)
    exact tmGLP_step_ar hca hcw hL (hcu.trans hvb) hum hS

end GI.Impl
