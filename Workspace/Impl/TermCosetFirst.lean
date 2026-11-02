import Workspace.Impl.TermCosetMath

/-!
# The first nonempty entry of a row or a column of the coset table

The objects of Theorem A.20 are built from the table `Iso_H(x_i, y_j)` (the list `vs`, entry
`i q + j`). The color of a row is the first `j` with a nonempty entry in its row of the table
(`tmCsStar`). `tmCsFirstF` finds it: on `[[vs, base, stride, q], j]` it returns the least
`J ≥ j`, `J < q`, with `vs[base + stride J]` a nonempty list, or `q` if there is none. Rows use
`base = i q`, `stride = 1`; columns use `base = j`, `stride = q`.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The search, by recursion on `j` (the function itself sits at `self`). -/
def tmCsFirstF (self : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.get (arg 0) (.nat 3)))
    (.ite (.length (.get (.get (arg 0) (.nat 0))
        (.arith .add (.get (arg 0) (.nat 1)) (.arith .mul (.get (arg 0) (.nat 2)) (arg 1)))))
      (arg 1)
      (.call self (mk2 (arg 0) (.arith .add (arg 1) (.nat 1)))))
    (.get (arg 0) (.nat 3))

/-- The context of the search. -/
def tmCsFirstCtx (vs : List Val) (base stride q : ℕ) : Val :=
  .list [.list vs, .nat base, .nat stride, .nat q]

/-- The cost of one step of the search, in the weight `W` of the context. -/
def tmCsFirstK (W : ℕ) : ℕ := 200 * W + 400

/-- **The search.** If every entry `base + stride j'`, `j' < q`, is a list, then from `j ≤ q`
the search returns the least `J ≥ j` with a nonempty entry (or `q`), at cost at most
`(q - j + 1) · tmCsFirstK W`. -/
theorem tmCs_first_spec {P : Program} {self : ℕ} (hf : P.funs[self]? = some (tmCsFirstF self))
    {vs : List Val} {base stride q : ℕ}
    (hl : ∀ j < q, ∃ l : List Val, vs[base + stride * j]? = some (.list l)) :
    ∀ d j, q - j = d → j ≤ q → ∃ J, FunDet P self
      (.list [tmCsFirstCtx vs base stride q, .nat j]) (.nat J)
      ((d + 1) * tmCsFirstK (tmCsFirstCtx vs base stride q).wt) ∧
      j ≤ J ∧ J ≤ q ∧ (∀ j', j ≤ j' → j' < J → vs[base + stride * j']? = some (.list [])) ∧
      (J < q → ∃ a l, vs[base + stride * J]? = some (.list (a :: l))) := by
  set c := tmCsFirstCtx vs base stride q with hc
  have hcw : (Val.list vs).wt < c.wt := wt_le_wt_list (by simp)
  have hqw : (Val.nat q).wt < c.wt := wt_le_wt_list (by simp)
  have hlenv := length_lt_wt_list vs
  have hq3 := wt_nat_le q
  have hjqw : ∀ j ≤ q, (Val.nat j).wt ≤ (Val.nat q).wt := fun j h => by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono h; omega
  intro d
  induction d with
  | zero =>
    intro j hd hj
    have hjq : j = q := by omega
    subst hjq
    refine ⟨j, FunDet.intro hf ?_, le_rfl, le_rfl, fun j' h1 h2 => by omega, fun h => by omega⟩
    have hawt : (Val.list [c, .nat j]).wt ≤ 2 * (c.wt + (Val.nat j).wt) + 6 :=
      wt_list2_le c (.nat j)
    have d1 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) (v := .nat j) rfl
    have d0 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) (v := c) rfl
    have d3 := Det.get' d0 (Det.nat 3) (vs := [.list vs, .nat base, .nat stride, .nat j])
      (v := .nat j) rfl
    have dlt := Det.arith' (op := .lt) d1 d3 (z := 0) (by simp [GI.Machine.BinOp.eval])
    refine (Det.ite_zero dlt d3).mono ?_
    unfold tmCsFirstK
    omega
  | succ d ih =>
    intro j hd hj
    have hjq : j < q := by omega
    obtain ⟨l, hlj⟩ := hl j hjq
    have hawt : (Val.list [c, .nat j]).wt ≤ 2 * (c.wt + (Val.nat j).wt) + 6 :=
      wt_list2_le c (.nat j)
    have hjw := hjqw j hjq.le
    have hidx : base + stride * j < vs.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hlj; cases hlj
    have hlw : (Val.list l).wt < (Val.list vs).wt := by
      have := wt_getElem_lt vs (base + stride * j) hidx
      obtain ⟨_, he⟩ := List.getElem_of_getElem? hlj
      rwa [he] at this
    have d1 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) (v := .nat j) rfl
    have d0 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) (v := c) rfl
    have d3 := Det.get' d0 (Det.nat 3) (vs := [.list vs, .nat base, .nat stride, .nat q])
      (v := .nat q) rfl
    have dlt := Det.arith' (op := .lt) d1 d3 (z := 1) (by simp [GI.Machine.BinOp.eval, hjq])
    have dvs := Det.get' d0 (Det.nat 0) (vs := [.list vs, .nat base, .nat stride, .nat q])
      (v := .list vs) rfl
    have dbase := Det.get' d0 (Det.nat 1) (vs := [.list vs, .nat base, .nat stride, .nat q])
      (v := .nat base) rfl
    have dstr := Det.get' d0 (Det.nat 2) (vs := [.list vs, .nat base, .nat stride, .nat q])
      (v := .nat stride) rfl
    have dmul := Det.arith' (op := .mul) dstr d1 (z := stride * j) rfl
    have dadd := Det.arith' (op := .add) dbase dmul (z := base + stride * j) rfl
    have dent := Det.get' dvs dadd hlj
    have dlen := Det.length dent
    have hbw : (Val.nat base).wt < c.wt := wt_le_wt_list (by simp)
    have hsw : (Val.nat stride).wt < c.wt := wt_le_wt_list (by simp)
    have hl0 := length_lt_wt_list l
    have hsj : stride * j < vs.length := by omega
    -- the cost of the test of the entry
    rcases l with _ | ⟨x, l⟩
    · -- empty entry: recurse
      obtain ⟨J, hJ, hJ1, hJ2, hJ3, hJ4⟩ := ih (j + 1) (by omega) (by omega)
      refine ⟨J, FunDet.intro hf ?_, by omega, hJ2, fun j' h1 h2 => ?_, hJ4⟩
      · have dj1 : Det P [Val.list [c, Val.nat j]] (.arith .add (arg 1) (.nat 1)) (.nat (j + 1))
            (2 * (Val.list [c, Val.nat j]).wt + 1 + 5 + (1 + 3) + (Val.nat (j + 1)).wt + 1) :=
          Det.arith (op := .add) d1 (Det.nat 1)
        have dcall := Det.call (Det.mk2 d0 dj1) hJ
        have dite := Det.ite_zero (t := arg 1) dlen dcall
        have hj1w := hjqw (j + 1) (by omega)
        refine (Det.ite_pos dlt (by omega) dite).mono ?_
        have hJw : (Val.nat J).wt ≤ c.wt := (hjqw J hJ2).trans hqw.le
        have h2w := wt_list2_le c (.nat (j + 1))
        simp only [List.length_nil] at *
        unfold tmCsFirstK at *
        nlinarith
      · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact hlj
        · exact hJ3 j' (by omega) h2
    · -- nonempty entry: stop at `j`
      refine ⟨j, FunDet.intro hf ?_, le_rfl, hjq.le, fun j' h1 h2 => by omega,
        fun _ => ⟨x, l, hlj⟩⟩
      have dite := Det.ite_pos
        (e := .call self (mk2 (arg 0) (.arith .add (arg 1) (.nat 1)))) dlen (by simp) d1
      refine (Det.ite_pos dlt (by omega) dite).mono ?_
      simp only [List.length_cons] at *
      unfold tmCsFirstK
      nlinarith

end GI.Impl

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-! ### The fuel of Theorem A.20: the least `ℓ` with `m⁵ ≤ 3^ℓ` -/

/-- On `[p, t, ℓ]`: while `p < t`, triple `p` and count. -/
def tmCsEllF (self : ℕ) : Expr :=
  .ite (.arith .lt (arg 0) (arg 1))
    (.call self (mk3 (.arith .mul (.nat 3) (arg 0)) (arg 1) (.arith .add (arg 2) (.nat 1))))
    (arg 2)

/-- The cost of one step, in the weight of `3 t`. -/
def tmCsEllK (W : ℕ) : ℕ := 200 * W + 200

theorem tmCs_ell_spec {P : Program} {self : ℕ} (hf : P.funs[self]? = some (tmCsEllF self))
    (t : ℕ) (ht : 1 ≤ t) :
    ∀ d ℓ, t - 3 ^ ℓ = d → (ℓ = 0 ∨ 3 ^ (ℓ - 1) < t) → ∃ L, FunDet P self
      (.list [.nat (3 ^ ℓ), .nat t, .nat ℓ]) (.nat L) ((d + 1) * tmCsEllK (Val.nat (3 * t)).wt) ∧
      t ≤ 3 ^ L ∧ (L = 0 ∨ 3 ^ (L - 1) < t) := by
  have hmono : ∀ {a b : ℕ}, a ≤ b → (Val.nat a).wt ≤ (Val.nat b).wt := fun h => by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono h; omega
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro ℓ hd hℓ
  have hlt : ℓ < 3 ^ ℓ := Nat.lt_pow_self (by norm_num)
  have e0 := Det.arg' (P := P) (vs := [.nat (3 ^ ℓ), .nat t, .nat ℓ]) (rest := []) (j := 0) rfl
  have e1 := Det.arg' (P := P) (vs := [.nat (3 ^ ℓ), .nat t, .nat ℓ]) (rest := []) (j := 1) rfl
  have e2 := Det.arg' (P := P) (vs := [.nat (3 ^ ℓ), .nat t, .nat ℓ]) (rest := []) (j := 2) rfl
  have hw3 := wt_list3_le (.nat (3 ^ ℓ)) (.nat t) (.nat ℓ)
  by_cases hp : 3 ^ ℓ < t
  · -- one more step
    have h3 : 3 ^ (ℓ + 1) = 3 * 3 ^ ℓ := by ring
    obtain ⟨L, hL, hL1, hL2⟩ := ih (t - 3 ^ (ℓ + 1)) (by rw [h3]; omega) (ℓ + 1) rfl
      (Or.inr (by simpa using hp))
    refine ⟨L, FunDet.intro hf ?_, hL1, hL2⟩
    have dlt := Det.arith' (op := .lt) e0 e1 (z := 1) (by simp [GI.Machine.BinOp.eval, hp])
    have dp : Det P [Val.list [.nat (3 ^ ℓ), .nat t, .nat ℓ]] (.arith .mul (.nat 3) (arg 0))
        (.nat (3 ^ (ℓ + 1))) (3 + 3 + (2 * (Val.list [.nat (3 ^ ℓ), .nat t, .nat ℓ]).wt + 0 + 5) +
          (Val.nat (3 ^ (ℓ + 1))).wt + 1) := by
      rw [h3]; exact Det.arith (op := .mul) (Det.nat 3) e0
    have dl : Det P [Val.list [.nat (3 ^ ℓ), .nat t, .nat ℓ]] (.arith .add (arg 2) (.nat 1))
        (.nat (ℓ + 1)) ((2 * (Val.list [.nat (3 ^ ℓ), .nat t, .nat ℓ]).wt + 2 + 5) + (1 + 3) +
          (Val.nat (ℓ + 1)).wt + 1) := Det.arith (op := .add) e2 (Det.nat 1)
    have dcall := Det.call (Det.mk3 dp e1 dl) hL
    refine (Det.ite_pos dlt (by omega) dcall).mono ?_
    have w1 := hmono (show 3 ^ ℓ ≤ 3 * t by omega)
    have w2 := hmono (show 3 ^ (ℓ + 1) ≤ 3 * t by omega)
    have w3 := hmono (show ℓ + 1 ≤ 3 * t by omega)
    have w4 := hmono (show ℓ ≤ 3 * t by omega)
    have w5 := hmono (show t ≤ 3 * t by omega)
    have w6 := hmono (show L ≤ 3 * t by
      rcases hL2 with h | h
      · omega
      · have := Nat.lt_pow_self (n := L - 1) (show 1 < 3 by norm_num); omega)
    have w7 := wt_list3_le (.nat (3 ^ (ℓ + 1))) (.nat t) (.nat (ℓ + 1))
    have h1p := Nat.one_le_pow ℓ 3 (by norm_num)
    have hdd : t - 3 ^ (ℓ + 1) + 1 + 1 ≤ d + 1 := by rw [h3]; omega
    have key := Nat.mul_le_mul_right (tmCsEllK (Val.nat (3 * t)).wt) hdd
    rw [add_mul, one_mul] at key
    unfold tmCsEllK at *
    omega
  · -- stop
    refine ⟨ℓ, FunDet.intro hf ?_, by omega, hℓ⟩
    have dlt := Det.arith' (op := .lt) e0 e1 (z := 0) (by simp [GI.Machine.BinOp.eval, hp])
    refine (Det.ite_zero (t := .call self (mk3 (.arith .mul (.nat 3) (arg 0)) (arg 1)
      (.arith .add (arg 2) (.nat 1)))) dlt e2).mono ?_
    have h3t : 3 ^ ℓ ≤ 3 * t := by
      rcases hℓ with rfl | h
      · simp; omega
      · have : 3 ^ ℓ = 3 * 3 ^ (ℓ - 1) := by
          rw [← pow_succ']; congr 1; rcases ℓ with _ | ℓ
          · simp at h; omega
          · simp
        omega
    have w1 := hmono h3t
    have w4 := hmono (show ℓ ≤ 3 * t by omega)
    have w5 := hmono (show t ≤ 3 * t by omega)
    have := Nat.le_mul_of_pos_left (tmCsEllK (Val.nat (3 * t)).wt) (show 0 < d + 1 by omega)
    unfold tmCsEllK at *
    omega

end GI.Impl
