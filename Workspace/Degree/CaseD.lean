module

public import Workspace.Degree.Interface
public import Workspace.Degree.Thread
public import Workspace.Impl.GenSpecMath

@[expose] public section

/-!
# The case decision of the degree algorithm

The decision on a primitive quotient of degree `b` and order `o`, for the degree `D`. If
`o ≤ b^(E (⌊log₂ D⌋ + 1))`, the case is enumeration. Otherwise recognition is called. Its promise holds
by `PrimitiveAlternatives`, for a large enough constant `E`.

This is the only place that reads `D`. Function `caseDE D` holds `D` as a number in its text, and
`caseDT` is the same function with `D` in the environment (`rel_caseD`).
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp len len_mono)
open GI.Cited (Val encGroup encKSetTuples MarotiStructure)

/-- **The recognition primitive.** -/
noncomputable def recognitionPrim (h : JohnsonRecognition) : Prim :=
  Prim.ofHyp (fun I : RecogInst => encGroup I.gs) _ h

/-- A value with a Maróti structure in the range of recognition, as `JohnsonRecognitionTask` says. -/
def RecogOut {n : ℕ} (G : Subgroup (Perm (Fin n))) (v : Val) : Prop :=
  ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
    RecogRange m k ∧ 1 ≤ r ∧ MarotiStructure G e ∧
      v = .list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e]

theorem recognition_call (h : JohnsonRecognition) {P : Program} {env : List Val}
    {j : ℕ} {a : Expr} {ca n : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (recognitionPrim h)) (ha : Det P env a gv ca)
    (hG : GroupVal n gv G) (hn : 25 ≤ n) (hprim : MulAction.IsPreprimitive G (Fin n))
    (hpr : ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
      RecogRange m k ∧ 1 ≤ r ∧ MarotiStructure G e) :
    EvalAll P env (.prim j a) (fun w c => RecogOut G w ∧
      c ≤ ca + (recognitionPrim h).bound gv + w.wt + 1) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  refine EvalAll.prim_spec hj ha ?_
  refine (Prim.ofHyp_spec h (⟨n, hn, gs, hprim, hpr⟩ : RecogInst) ?_)
  rintro ⟨n', _, gs', _, _⟩ hy
  obtain rfl := encGroup_deg hy
  obtain rfl := encGroup_injective hy
  rfl

/-- The test on `[o, b, D]`. It returns `1` if `o ≤ b^(E (⌊log₂ D⌋ + 1))`, and `0` otherwise. -/
def degTestBody (b E : ℕ) : Expr :=
  .letE (.call (b + 1) (.get (.var 0) (.nat 2)))
    (.letE (.call (b + 4) (mk3 (.get (.var 0) (.nat 0)) (.get (.var 0) (.nat 1))
        (.arith .mul (.nat E) (.arith .add (.get (.var 1) (.nat 0)) (.nat 1)))))
      (.arith .lt (.get (.var 0) (.nat 0)) (.arith .add (.var 2) (.nat 1))))

/-- The test, at base `b` (seven functions). -/
def degTestFuns (b E : ℕ) : List Expr := [degTestBody b E] ++ log2Funs (b + 1) ++ powFuns (b + 4)

/-- The exponent of the test. -/
def degExp (E D : ℕ) : ℕ := E * (Nat.log 2 D + 1)

/-- The cost bound of the test. -/
def degTestC (E D W : ℕ) : ℕ := smallZK * (W + E * (D + 1) + D + 20) ^ 2

set_option maxHeartbeats 1000000 in
/-- **The test meets its specification.** -/
theorem degTest_spec {P : Program} {b E : ℕ} (h : P.HasAt b (degTestFuns b E)) (ord d D : ℕ) :
    FunDet P b (.list [.nat ord, .nat d, .nat D]) (boolVal (decide (ord ≤ d ^ degExp E D)))
      (degTestC E D (Val.list [.nat ord, .nat d, .nat D]).wt) := by
  simp only [degTestFuns] at h
  have hbody : P.funs[b]? = some (degTestBody b E) := h.left.left.single
  have hlog : P.HasAt (b + 1) (log2Funs (b + 1)) := h.left.right
  have hpow : P.HasAt (b + 4) (powFuns (b + 4)) := by
    have := h.right; simpa [log2Funs, loopFuns, Nat.add_assoc] using this
  set x := Val.list [.nat ord, .nat d, .nat D] with hx
  obtain ⟨L, hLd⟩ : ∃ L, Nat.log 2 D = L := ⟨_, rfl⟩
  have hexp : degExp E D = E * (L + 1) := by rw [degExp, hLd]
  rw [hexp]
  set m := min (d ^ (E * (L + 1))) (ord + 1)
  have dX := Det.var' (P := P) (env := [x]) (i := 0) rfl
  have dDd := Det.get' dX (Det.nat 2)
    (show [Val.nat ord, .nat d, .nat D][2]? = some (.nat D) from rfl)
  have dLog := Det.call dDd (log2_spec hlog D)
  rw [hLd] at dLog
  have dX2 := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)]]) (i := 0) rfl
  have dO2 := Det.get' dX2 (Det.nat 0)
    (show [Val.nat ord, .nat d, .nat D][0]? = some (.nat ord) from rfl)
  have dD2 := Det.get' dX2 (Det.nat 1)
    (show [Val.nat ord, .nat d, .nat D][1]? = some (.nat d) from rfl)
  have dLg := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)]]) (i := 1) rfl
  have dL := Det.get' dLg (Det.nat 0) (show [Val.nat L, .nat (2 ^ L)][0]? = some (.nat L) from rfl)
  have dL1 := Det.arith' (op := .add) (z := L + 1) dL (Det.nat 1) rfl
  have dE := Det.arith' (op := .mul) (z := E * (L + 1)) (Det.nat E) dL1 rfl
  have dArg := Det.mk3 dO2 dD2 dE
  have dPow := Det.call dArg (pow_spec hpow ord d (E * (L + 1)))
  have dX3 := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)], .nat m]) (i := 0) rfl
  have dO3 := Det.get' dX3 (Det.nat 0)
    (show [Val.nat ord, .nat d, .nat D][0]? = some (.nat ord) from rfl)
  have dM := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)], .nat m]) (i := 2) rfl
  have dT := Det.arith (op := .lt) dO3 (Det.arith (op := .add) dM (Det.nat 1))
  have hval : Val.nat (BinOp.eval .lt ord (BinOp.eval .add m 1)) =
      boolVal (decide (ord ≤ d ^ (E * (L + 1)))) := by
    change Val.nat (if ord < m + 1 then 1 else 0) =
      Val.nat (decide (ord ≤ d ^ (E * (L + 1)))).toNat
    by_cases hle : ord ≤ d ^ (E * (L + 1))
    · rw [if_pos ((le_iff_lt_min ord _).1 hle), decide_eq_true hle]; rfl
    · rw [if_neg (fun h' => hle ((le_iff_lt_min ord _).2 h')), decide_eq_false hle]; rfl
  rw [← hval]
  refine FunDet.intro hbody ((Det.letE dLog (Det.letE dPow dT)).mono ?_)
  clear h hbody hlog hpow dX dDd dLog dX2 dO2 dD2 dLg dL dL1 dE dArg dPow dX3 dO3 dM dT hval hexp
  have hm1 : m ≤ ord + 1 := min_le_right _ _
  clear_value m
  have hW := x.two_le_size
  have hW' := x.size_le_wt
  have hwd : (Val.nat D).wt < x.wt := wt_le_wt_list (by simp)
  have hwo : (Val.nat ord).wt < x.wt := wt_le_wt_list (by simp)
  have hwb : (Val.nat d).wt < x.wt := wt_le_wt_list (by simp)
  have hL : L ≤ D := hLd ▸ Nat.log_le_self 2 D
  have heB : E * (L + 1) ≤ E * (D + 1) := Nat.mul_le_mul_left E (by omega)
  have hlg : (Val.list [Val.nat L, Val.nat (2 ^ L)]).wt ≤ 4 * (Val.nat D).wt + 20 := by
    have := wt_log2Acc_le D (D + 4); rwa [log2Acc_final, hLd] at this
  have hwL := wt_nat_le L
  have hw3 := wt_list3_le (Val.nat ord) (Val.nat d) (Val.nat (E * (L + 1)))
  have hwe := wt_nat_le (E * (L + 1))
  have hwE := wt_nat_le E
  have hwL1 := wt_nat_le (L + 1)
  have lo1 := GI.Machine.len_add_le ord 1
  have lm := len_mono hm1
  have lm1 := len_mono (show m + 1 ≤ ord + 2 by omega)
  have lo2 := GI.Machine.len_add_le ord 2
  have hl1 : len 1 = 1 := rfl
  have hl2 : len 2 = 2 := rfl
  have wlt : ∀ y z, (Val.nat (BinOp.eval .lt y z)).wt ≤ 3 := fun y z => by
    simp only [BinOp.eval]; split <;> decide
  have w1 := wlt ord (BinOp.eval .add m 1)
  have hmax2 : max (len ord) (len 1) ≤ len ord + 1 := max_le (by omega) (by omega)
  have hmax3 : max (len ord) (len 2) ≤ len ord + 2 := max_le (by omega) (by omega)
  have lmm := len_mono (min_le_right (d ^ (E * (L + 1))) (ord + 1))
  have hE1 : E ≤ E * (D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [BinOp.eval, wt_nat] at hwd hwo hwb hwL hwe hwE hwL1 w1 hw3 hlg ⊢
  unfold degTestC
  generalize E * (L + 1) = G at *
  generalize E * (D + 1) = F at *
  set X := x.wt + F + D + 20 with hX
  clear_value X
  have hlogc : 1000 * (D + 5) * (5 * (len D + 2) + D + 25) ≤ 5000 * X ^ 2 := by
    have h1 : D + 5 ≤ X := by omega
    have h2 : 5 * (len D + 2) + D + 25 ≤ 5 * X := by omega
    calc 1000 * (D + 5) * (5 * (len D + 2) + D + 25) ≤ 1000 * X * (5 * X) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 5000 * X ^ 2 := by ring
  have hpowc : 1000 * (G + 1) * ((Val.list [Val.nat ord, Val.nat d, Val.nat G]).wt + G +
      (len (ord + 1) + 2) + 1) ≤ 6000 * X ^ 2 := by
    have h1 : G + 1 ≤ X := by omega
    have h2 : (Val.list [Val.nat ord, Val.nat d, Val.nat G]).wt + G +
        (len (ord + 1) + 2) + 1 ≤ 6 * X := by omega
    calc _ ≤ 1000 * X * (6 * X) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 6000 * X ^ 2 := by ring
  have hX10 : 10 ≤ X := by omega
  have hXX : 10 * X ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right X hX10
  simp only [loopModK, smallZK] at *
  generalize X ^ 2 = Y at *
  generalize (Val.list [Val.nat ord, Val.nat d, Val.nat G]).wt = Z at *
  obtain ⟨P1, hP1⟩ : ∃ P1, 1000 * (D + 5) * (5 * (len D + 2) + D + 25) = P1 := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2, 1000 * (G + 1) * (Z + G + (len (ord + 1) + 2) + 1) = P2 := ⟨_, rfl⟩
  rw [hP1] at hlogc ⊢
  rw [hP2] at hpowc ⊢
  clear hP1 hP2
  omega

/-- **The case decision on `[b, gv, o]`.** The number `D` is in the text. -/
def caseDE (tst jr D : ℕ) : Expr :=
  .letE (.call tst (mk3 (arg 2) (arg 0) (.nat D)))
    (.ite (.var 1) (mk1 (.nat 0)) (.prim jr (arg 1)))

variable {Ω C : Type} {S : State Ω C}

/-- **What the case decision returns.** -/
def CaseOutD (Q : PrimitiveQuotient S) (T : ℕ) (w : Val) : Prop :=
  (w = .list [.nat 0] ∧ Nat.card Q.ρ.range ≤ Q.d ^ T) ∨
    (¬ Nat.card Q.ρ.range ≤ Q.d ^ T ∧ RecogOut Q.ρ.range w)

/-- The cost bound of the case decision. -/
noncomputable def caseDCost (h : JohnsonRecognition) (E D : ℕ) (gv : Val) (b o : ℕ) : ℕ :=
  degTestC E D (2 * ((Val.nat o).wt + b + D + 10)) + (recognitionPrim h).bound gv +
    100 * (gv.wt + (Val.nat o).wt + b + D + 40)

theorem degTestC_mono (E D : ℕ) {W W' : ℕ} (h : W ≤ W') : degTestC E D W ≤ degTestC E D W' := by
  unfold degTestC
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The case decision meets its specification.** If the order fails the test, the caller must
show the promise of recognition. -/
theorem caseD_spec (h : JohnsonRecognition) {P : Program} {f tst jr E D : ℕ}
    (hf : P.funs[f]? = some (caseDE tst jr D)) (htst : P.HasAt tst (degTestFuns tst E))
    (hj : P.prims[jr]? = some (recognitionPrim h)) (Q : PrimitiveQuotient S) {gv : Val} {o : ℕ}
    (hgv : GroupVal Q.d gv Q.ρ.range) (ho : o = Nat.card Q.ρ.range)
    (hpr : ¬ o ≤ Q.d ^ degExp E D → 25 ≤ Q.d ∧
      ∃ (m k r : ℕ) (e : Fin Q.d ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
        RecogRange m k ∧ 1 ≤ r ∧ MarotiStructure Q.ρ.range e) :
    FunAll P f (.list [.nat Q.d, gv, .nat o]) (fun w c => CaseOutD Q (degExp E D) w ∧
      c ≤ caseDCost h E D gv Q.d o + 10 * w.wt) := by
  set x := Val.list [.nat Q.d, gv, .nat o] with hx
  have wx : x.wt ≤ 2 * (Q.d + 2 + gv.wt + (Val.nat o).wt) + 7 := by
    rw [hx]
    have := wt_list3_le (.nat Q.d) gv (.nat o)
    have := wt_nat_le Q.d
    omega
  have g0 : ∀ rest, Det P (x :: rest) (arg 0) (.nat Q.d) (2 * x.wt + 0 + 5) := fun rest =>
    Det.arg' (vs := [.nat Q.d, gv, .nat o]) rfl
  have g1 : ∀ rest, Det P (x :: rest) (arg 1) gv (2 * x.wt + 1 + 5) := fun rest =>
    Det.arg' (vs := [.nat Q.d, gv, .nat o]) rfl
  have g2 : ∀ rest, Det P (x :: rest) (arg 2) (.nat o) (2 * x.wt + 2 + 5) := fun rest =>
    Det.arg' (vs := [.nat Q.d, gv, .nat o]) rfl
  refine FunAll.intro hf ?_
  unfold caseDE
  have dt := Det.call (Det.mk3 (g2 []) (g0 []) (Det.nat (P := P) (env := [x]) D))
    (degTest_spec htst o Q.d D)
  have ww := wt_list3_le (.nat o) (.nat Q.d) (.nat D)
  have w1 := wt_nat_le Q.d
  have w2 := wt_nat_le D
  have w0 : (Val.list [.nat 0]).wt ≤ 9 := by
    have := wt_list1_le (.nat 0); have := wt_nat_le 0; omega
  have hC : degTestC E D (Val.list [.nat o, .nat Q.d, .nat D]).wt ≤
      degTestC E D (2 * ((Val.nat o).wt + Q.d + D + 10)) := degTestC_mono E D (by omega)
  refine EvalAll.letE dt fun vb cb hvb => ?_
  obtain ⟨rfl, hcb⟩ := hvb
  have wb := wt_boolVal_le (decide (o ≤ Q.d ^ degExp E D))
  refine EvalAll.ite (Det.var' (P := P) (env := [x, boolVal (decide (o ≤ Q.d ^ degExp E D))])
    (i := 1) rfl) (fun _ _ h => ⟨_, h.1⟩) fun t ct ht => ?_
  obtain ⟨ht, hct⟩ := ht
  injection ht with ht
  subst ht
  by_cases hz : o ≤ Q.d ^ degExp E D
  · have hb1 : (decide (o ≤ Q.d ^ degExp E D)).toNat = 1 := by simp [hz]
    rw [hb1, if_neg one_ne_zero]
    refine (Det.mk1 (Det.nat (P := P) (env := [x, boolVal (decide (o ≤ Q.d ^ degExp E D))]) 0)).post
      fun c hc => ⟨Or.inl ⟨rfl, ho ▸ hz⟩, ?_⟩
    have := wt_nat_le 0
    unfold caseDCost
    omega
  have hb0 : (decide (o ≤ Q.d ^ degExp E D)).toNat = 0 := by simp [hz]
  rw [hb0, if_pos rfl]
  obtain ⟨h25, hp⟩ := hpr hz
  refine (recognition_call h hj (g1 [boolVal (decide (o ≤ Q.d ^ degExp E D))]) hgv h25 Q.primitive
    hp).mono fun w c ⟨hw, hc⟩ => ⟨Or.inr ⟨ho ▸ hz, hw⟩, ?_⟩
  unfold caseDCost
  omega

/-- `caseDE` with `D` in the environment. -/
def caseDT (tst jr : ℕ) : Expr :=
  .letE (.call tst (.snoc (.snoc .nil (.var 1)) (mk3 (thr (arg 2)) (thr (arg 0)) (.var 1))))
    (.ite (.var 3) (thr (mk1 (.nat 0))) (.prim jr (thr (arg 1))))

/-- **The two texts agree.** -/
theorem rel_caseD (tst jr D : ℕ) : Rel D (caseDE tst jr D) (caseDT tst jr) := by
  refine .letE (.call _ ?_) (.ite (.var 1) (rel_thr D _) (.prim _ (rel_thr D _)))
  exact .snoc (.snoc (.snoc .nil (rel_thr D _)) (rel_thr D _)) .degree

end GI.Degree
