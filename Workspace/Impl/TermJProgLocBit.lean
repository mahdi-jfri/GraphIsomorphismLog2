import Workspace.Impl.TermJProgLocMath
import Workspace.Impl.TermStep

/-!
# The local transporter of a class (program, part 1: the tests)

The input of the whole program is `[h, vs, σN, q, m]` (`tmJLInp`): the class `h`, the stored
cosets `vs` (entry `a q + j` is `Iso_H(x_a, y_j)`), the generators of `N`, and the sizes.

* `tmJLBitF`: on `[[inp, a], j]`, the local test of `(a, j)`: `0` for an empty entry, else the
  Membership test of `g⁻¹ h` in `⟨gs, σN⟩` for the entry `[g, gs]` (`tmJL_bit_spec`).
* `tmJLRowF`: on `[inp, a]`, the row `a` of tests (`tmJL_row_spec`).

Costs are stated in `Y = wt inp + 1`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {m q : ℕ}

/-! ### Weights -/

/-- A list whose entries weigh at most `B`. -/
theorem tmJL_wt_list_le {l : List Val} {B : ℕ} (h : ∀ v ∈ l, v.wt ≤ B) :
    (Val.list l).wt ≤ l.length * (2 * B + 1) + 4 := by
  have h1 := wt_list_le l
  have h2 : (l.map Val.wt).sum ≤ l.length * B := by
    have := List.sum_le_card_nsmul (l.map Val.wt) B (by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact h)
    simpa using this
  nlinarith

/-- The weight of an appended list. -/
theorem tmJL_wt_append_le (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ 3 * ((Val.list xs).wt + (Val.list ys).wt) + 4 := by
  have h1 := wt_list_le (xs ++ ys)
  have h2 := sum_wt_lt_wt_list xs
  have h3 := sum_wt_lt_wt_list ys
  have h4 := length_lt_wt_list xs
  have h5 := length_lt_wt_list ys
  simp only [List.map_append, List.sum_append, List.length_append] at h1
  omega

/-- A prim bound on an input of weight at most `W`. -/
theorem tmJL_prim_le (p : Prim) {v : Val} {W : ℕ} (h : v.wt ≤ W) :
    p.bound v ≤ p.c * (W + 2) ^ p.k :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := v.size_le_wt; omega) _)

/-! ### The input and its entries -/

/-- The input of the program. -/
def tmJLInp (h : Perm (Fin m)) (vs : List Val) (σN : List (Perm (Fin m))) (q : ℕ) : Val :=
  .list [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m]

/-- **The stored entry of `(a, j)`.** -/
theorem tmJL_entry {A : Fin q × Fin q → Set (Perm (Fin m))} {vs : List Val}
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (A ij)) vs (tmCosets q))
    (i j : Fin q) :
    ∃ v, vs[i.1 * q + j.1]? = some v ∧ AnsC (Equiv.refl (Fin m)) v (A (i, j)) := by
  have hlen : vs.length = q * q := by rw [hvs.length_eq, length_tmCosets]; ring
  have hij : i.1 * q + j.1 < q ^ 2 := by
    have : i.1 * q + j.1 < q * q := by nlinarith [i.2, j.2]
    nlinarith
  obtain ⟨h1, h2, hc⟩ := tmCosets_getElem? q (i.1 * q + j.1) hij
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0)
  have e1 : (⟨(i.1 * q + j.1) / q, h1⟩ : Fin q) = i := by
    ext; simp only; rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt j.2]; simp
  have e2 : (⟨(i.1 * q + j.1) % q, h2⟩ : Fin q) = j := by
    ext; simp only; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
  rw [e1, e2] at hc
  have hlt : i.1 * q + j.1 < vs.length := by rw [hlen]; nlinarith
  refine ⟨vs[i.1 * q + j.1], List.getElem?_eq_getElem hlt, ?_⟩
  have hR := List.forall₂_iff_get.1 hvs
  have := hR.2 (i.1 * q + j.1) hlt (by rw [← hR.1]; exact hlt)
  have hget : (tmCosets q).get ⟨i.1 * q + j.1, by rw [← hR.1]; exact hlt⟩ = (i, j) := by
    have := List.getElem?_eq_getElem (l := tmCosets q) (i := i.1 * q + j.1)
      (by rw [← hR.1]; exact hlt)
    rw [hc] at this
    exact (Option.some.inj this).symm
  rw [hget] at this
  simpa only [List.get_eq_getElem] using this

/-- The sizes are below the weight of the input. -/
theorem tmJL_inp_wt (h : Perm (Fin m)) {vs : List Val} (σN : List (Perm (Fin m))) (hq : 0 < q)
    (hlen : vs.length = q * q) :
    m < (tmJLInp h vs σN q).wt ∧ q * q < (tmJLInp h vs σN q).wt ∧ q < (tmJLInp h vs σN q).wt ∧
      (encPerm h).wt < (tmJLInp h vs σN q).wt ∧ (Val.list vs).wt < (tmJLInp h vs σN q).wt ∧
      (Val.list (σN.map encPerm)).wt < (tmJLInp h vs σN q).wt ∧
      (Val.nat q).wt < (tmJLInp h vs σN q).wt ∧ (Val.nat m).wt < (tmJLInp h vs σN q).wt := by
  have w1 : (encPerm h).wt < (tmJLInp h vs σN q).wt := wt_le_wt_list (by simp)
  have w2 : (Val.list vs).wt < (tmJLInp h vs σN q).wt := wt_le_wt_list (by simp)
  have w3 : (Val.list (σN.map encPerm)).wt < (tmJLInp h vs σN q).wt := wt_le_wt_list (by simp)
  have w4 : (Val.nat q).wt < (tmJLInp h vs σN q).wt := wt_le_wt_list (by simp)
  have w5 : (Val.nat m).wt < (tmJLInp h vs σN q).wt := wt_le_wt_list (by simp)
  have l1 := length_lt_wt_list ((List.finRange m).map fun i => Val.nat (h i))
  have l2 := length_lt_wt_list vs
  simp only [List.length_map, List.length_finRange] at l1
  have e : (encPerm h) = .list ((List.finRange m).map fun i => Val.nat (h i)) := rfl
  rw [← e] at l1
  have : q ≤ q * q := Nat.le_mul_of_pos_left q hq
  exact ⟨by omega, by omega, by omega, w1, w2, w3, w4, w5⟩

/-! ### The membership call as a deterministic piece -/

theorem tmJL_mem_det (hm : GI.Cited.Membership) {P : Program} {env : List Val} {j : ℕ} {a : Expr}
    {ca : ℕ} {gs : List (Perm (Fin m))} {x : Perm (Fin m)}
    (hj : P.prims[j]? = some (membershipPrim hm))
    (ha : Det P env a (.list [encGroup gs, encPerm x]) ca) :
    Det P env (.prim j a) (by classical exact boolVal (decide (x ∈ gens gs)))
      (ca + (membershipPrim hm).bound (.list [encGroup gs, encPerm x]) + 4) := by
  refine (membership_call hm hj ha ⟨gs, rfl, rfl⟩).mono fun w c hw => ⟨?_, by omega⟩
  classical
  rcases hw.1 with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · simp [h]
  · simp [h]

/-! ### One test -/

/-- On `[[inp, a], j]`: the local test of `(a, j)`. -/
def tmJLBitF (jm ap cp iv : ℕ) : Expr :=
  .letE (.get (.get (.get (arg 0) (.nat 0)) (.nat 1))
      (.arith .add (.arith .mul (.get (arg 0) (.nat 1)) (.get (.get (arg 0) (.nat 0)) (.nat 3)))
        (arg 1)))
    (.ite (.length (.var 1))
      (.prim jm (mk2
        (mk2 (.get (.get (.var 1) (.nat 1)) (.nat 0))
          (.call ap (mk2 (.get (.get (.var 1) (.nat 1)) (.nat 1))
            (.get (.get (arg 0) (.nat 0)) (.nat 2)))))
        (.call cp (mk2 (.call iv (.get (.var 1) (.nat 0))) (.get (.get (arg 0) (.nat 0)) (.nat 0))))))
      (.nat 0))

/-- The cost bound of one test, in `Y = wt inp + 1`. -/
def tmJLBitC (pm : Prim) (Y : ℕ) : ℕ := pm.c * (100 * Y ^ 2 + 2) ^ pm.k + 10 ^ 7 * Y ^ 4

section Setting

variable {C : Type} {H N : Subgroup (Perm (Fin m))} {σN : List (Perm (Fin m))}
  {x y : Fin q → Fin m → C} {A : Fin q × Fin q → Set (Perm (Fin m))} {vs : List Val}

/-- **One test.** -/
theorem tmJL_bit_spec (hm : GI.Cited.Membership) {P : Program} {f jm ap cp iv : ℕ}
    (hf : P.funs[f]? = some (tmJLBitF jm ap cp iv))
    (hjm : P.prims[jm]? = some (membershipPrim hm)) (hap : P.HasAt ap (appendFuns ap))
    (hcp : P.HasAt cp (composeFuns cp)) (hiv : P.HasAt iv (invFuns iv))
    (hn : GI.Multicoset.Normalizes H N) (hσN : gens σN = N)
    (hAdef : ∀ a j, A (a, j) = {u | u ∈ H ∧ x a ∘ ⇑u = y j})
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (A ij)) vs (tmCosets q))
    (h : Perm (Fin m)) (a j : Fin q) :
    FunDet P f (.list [.list [tmJLInp h vs σN q, .nat a], .nat j])
      (boolVal (tmJLMat N h A a j)) (tmJLBitC (membershipPrim hm) ((tmJLInp h vs σN q).wt + 1)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0)
  have hlen : vs.length = q * q := by rw [hvs.length_eq, length_tmCosets]; ring
  obtain ⟨wm, wqq, wq, wh, wvs, wσ, wnq, wnm⟩ := tmJL_inp_wt h σN hq hlen
  set inp := tmJLInp h vs σN q with hinp
  set av := Val.list [.list [inp, .nat a], .nat j] with hav
  set Y := inp.wt + 1 with hY
  obtain ⟨v, hv, hans⟩ := tmJL_entry hvs a j
  have wv : v.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_of_getElem? hv)
  have hinpl : inp = .list [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m] := rfl
  -- the reads before the test
  have d0 := Det.arg' (P := P) (vs := [.list [inp, .nat a], .nat j]) (rest := []) (j := 0)
    (v := .list [inp, .nat a]) rfl
  have dinp := Det.get' d0 (Det.nat 0) (vs := [inp, .nat a]) (v := inp) rfl
  have da := Det.get' d0 (Det.nat 1) (vs := [inp, .nat a]) (v := .nat a) rfl
  have dvs := Det.get' dinp (Det.nat 1) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
    .nat q, .nat m]) (v := .list vs) rfl
  have dq := Det.get' dinp (Det.nat 3) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
    .nat q, .nat m]) (v := .nat q) rfl
  have dj := Det.arg' (P := P) (vs := [.list [inp, .nat a], .nat j]) (rest := []) (j := 1)
    (v := .nat j) rfl
  have dmul := Det.arith' (op := .mul) da dq (z := a * q) rfl
  have dadd := Det.arith' (op := .add) dmul dj (z := a * q + j) rfl
  have dent := Det.get' dvs dadd hv
  have wav := wt_list2_le (.list [inp, .nat a]) (.nat j)
  have wia := wt_list2_le inp (.nat a)
  have wa := wt_nat_le a
  have wj := wt_nat_le j
  have ha := a.2
  have hj := j.2
  have haq : (a : ℕ) * q + j < q * q := by nlinarith
  have wmul := wt_nat_le (a * q)
  have wadd := wt_nat_le (a * q + j)
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rcases tmJL_ans hans with ⟨rfl, hA0⟩ | ⟨g, gs, rfl, hgl, hAg⟩
  · -- an empty entry: the test fails
    have e1 := Det.var' (P := P) (env := [av, .list []]) (i := 1) (v := .list []) rfl
    have dite := Det.ite_zero (t := .prim jm (mk2
        (mk2 (.get (.get (.var 1) (.nat 1)) (.nat 0))
          (.call ap (mk2 (.get (.get (.var 1) (.nat 1)) (.nat 1))
            (.get (.get (arg 0) (.nat 0)) (.nat 2)))))
        (.call cp (mk2 (.call iv (.get (.var 1) (.nat 0))) (.get (.get (arg 0) (.nat 0)) (.nat 0))))))
      (Det.length e1) (Det.nat 0)
    have hM : tmJLMat N h A a j = false := by
      rw [Bool.eq_false_iff]; intro hT
      obtain ⟨u, hu, -⟩ := (tmJLMat_iff h).1 hT
      rw [hA0] at hu; exact hu
    rw [hM]
    refine FunDet.intro hf ((Det.letE dent dite).mono ?_)
    have w0 : (Val.nat 0).wt ≤ 2 := by decide
    simp only [List.length_nil, wt_list_nil] at *
    unfold tmJLBitC
    omega
  · -- a coset `g ⟨gs⟩`: the Membership test
    have hsub : g • (gens gs : Set (Perm (Fin m))) ⊆ H := fun u hu => by
      rw [← hAg, hAdef] at hu; exact hu.1
    have hgs := tmJL_gs_mem hsub
    set ve := Val.list [encPerm g, encGroup gs] with hve
    have e1 := Det.var' (P := P) (env := [av, ve]) (i := 1) (v := ve) rfl
    have eG := Det.get' e1 (Det.nat 1) (vs := [encPerm g, encGroup gs]) (v := encGroup gs) rfl
    have eGn := Det.get' eG (Det.nat 0) (vs := [.nat m, .list ((1 :: gs).map encPerm)])
      (v := .nat m) rfl
    have eGl := Det.get' eG (Det.nat 1) (vs := [.nat m, .list ((1 :: gs).map encPerm)])
      (v := .list ((1 :: gs).map encPerm)) rfl
    have f0 := Det.arg' (P := P) (vs := [.list [inp, .nat a], .nat j]) (rest := [ve]) (j := 0)
      (v := .list [inp, .nat a]) rfl
    have finp := Det.get' f0 (Det.nat 0) (vs := [inp, .nat a]) (v := inp) rfl
    have fσ := Det.get' finp (Det.nat 2) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
      .nat q, .nat m]) (v := .list (σN.map encPerm)) rfl
    have fh := Det.get' finp (Det.nat 0) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
      .nat q, .nat m]) (v := encPerm h) rfl
    have hAp : FunDet P ap (.list [.list ((1 :: gs).map encPerm), .list (σN.map encPerm)])
        (.list ((1 :: gs).map encPerm ++ σN.map encPerm))
        (loopModK * ((σN.map encPerm).length + 1) *
          ((Val.list [.list ((1 :: gs).map encPerm), .list (σN.map encPerm)]).wt +
            (σN.map encPerm).length + (Val.list ((1 :: gs).map encPerm ++ σN.map encPerm)).wt +
              1)) :=
      (append_spec hap _ _).mono fun w c hw => by obtain ⟨rfl, h2⟩ := hw; exact ⟨rfl, h2⟩
    have capp := Det.call (Det.mk2 eGl fσ) hAp
    have hG' : Val.list [.nat m, .list ((1 :: gs).map encPerm ++ σN.map encPerm)] =
        encGroup (gs ++ σN) := by simp [encGroup, encPerms]
    have grp := Det.mk2 eGn capp
    rw [hG'] at grp
    have eg := Det.get' e1 (Det.nat 0) (vs := [encPerm g, encGroup gs]) (v := encPerm g) rfl
    have cinv := Det.call eg (inv_spec hiv g)
    have ccp := Det.call (Det.mk2 cinv fh) (compose_spec hcp g⁻¹ h)
    have marg := Det.mk2 grp ccp
    have dmem := tmJL_mem_det hm hjm marg
    have dite := Det.ite_pos (e := .nat 0) (Det.length e1) (by simp) dmem
    have hM : boolVal (tmJLMat N h A a j) =
        (by classical exact boolVal (decide (g⁻¹ * h ∈ gens (gs ++ σN)))) := by
      classical
      have h1 := tmJLMat_iff h (N := N) (A := A) (a := a) (j := j)
      rw [hAg] at h1
      have := h1.trans (tmJL_test_iff h hn hσN hgs)
      congr 1
      by_cases hx : g⁻¹ * h ∈ gens (gs ++ σN)
      · simp [hx, this.2 hx]
      · have : tmJLMat N h A a j = false := by
          rw [Bool.eq_false_iff]; exact fun h' => hx (this.1 h')
        simp [hx, this]
    rw [hM]
    refine FunDet.intro hf ((Det.letE dent dite).mono ?_)
    -- the cost
    have wG : (encGroup gs).wt < ve.wt := wt_le_wt_list (by simp)
    have wg : (encPerm g).wt < ve.wt := wt_le_wt_list (by simp)
    have wL1 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
      wt_le_wt_list (by simp)
    have wapp := tmJL_wt_append_le ((1 :: gs).map encPerm) (σN.map encPerm)
    have wlσ := length_lt_wt_list (σN.map encPerm)
    have wnm' := wt_nat_le m
    have wG2 := wt_list2_le (Val.nat m) (.list ((1 :: gs).map encPerm ++ σN.map encPerm))
    have wG3 : (encGroup (gs ++ σN)).wt ≤ 2 * ((Val.nat m).wt +
        (Val.list ((1 :: gs).map encPerm ++ σN.map encPerm)).wt) + 6 := by rw [← hG']; exact wG2
    have wLL := wt_list2_le (Val.list ((1 :: gs).map encPerm)) (.list (σN.map encPerm))
    have wgi := wt_encPerm_le g⁻¹
    have wgh := wt_encPerm_le (g⁻¹ * h)
    have whh := wt_encPerm_le h
    have wih := wt_list2_le (encPerm g⁻¹) (encPerm h)
    have wmarg := wt_list2_le (encGroup (gs ++ σN)) (encPerm (g⁻¹ * h))
    have hmY : m + 1 ≤ Y := by omega
    have hm2 : (m + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hmY 2
    have hm3 : (m + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hmY 3
    have hm4 : (m + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hmY 4
    have hW : (Val.list [encGroup (gs ++ σN), encPerm (g⁻¹ * h)]).wt ≤ 100 * Y ^ 2 := by omega
    have hpb := tmJL_prim_le (membershipPrim hm) hW
    have hlp : loopModK * ((σN.map encPerm).length + 1) *
        ((Val.list [.list ((1 :: gs).map encPerm), .list (σN.map encPerm)]).wt +
          (σN.map encPerm).length + (Val.list ((1 :: gs).map encPerm ++ σN.map encPerm)).wt +
            1) ≤ 1000 * Y * (100 * Y) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have hlp2 : 1000 * Y * (100 * Y) = 10 ^ 5 * Y ^ 2 := by ring
    have hb3 : (by classical exact boolVal (decide (g⁻¹ * h ∈ gens (gs ++ σN))) : Val).wt ≤ 3 :=
      wt_boolVal_le _
    have hpk : permK = 30000 := rfl
    have hik : invK = 100000 := rfl
    rw [hpk, hik] at *
    have hl2 : [encPerm g, encGroup gs].length = 2 := rfl
    unfold tmJLBitC
    omega

end Setting

end GI.Impl
