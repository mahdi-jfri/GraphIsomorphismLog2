import Workspace.Impl.AggStructCol
import Workspace.Impl.AggStructPat

/-!
# The relation module of the tuple colorings, from the comparison table

`stCols_spec` reads the relation between tuples through a module with the contract `StRelOK`.
This file gives that module. Its context is what the comparison phase hands over:
the list of the ordered test tuples in
the order of the round (`tests.tuples`), each encoded as `[b, t]` (`stTT`), and the comparison
table in the order of `compScript_evalExact` (row `a`, column `b`, both in the list order).

On `[[cv, z, tv t], tv t₀]` the module decides `tupleRel (x, t₀) (z, t)`:
* both tuples injective: one table lookup, at the positions of `(x, t₀)` and `(z, t)` in the
  list of test tuples (two searches);
* both noninjective: the first-occurrence patterns are equal (`AggStructPat.lean`);
* otherwise: no.

`stRelTab_eq`: with the table of `CompareRel`, this is `stRel` (`AggStructCol.lean`).
`stRel_spec`: the module meets `StRelOK` at cost `stRelK (M + 1)^4`, where `M` bounds `q`, `κ`
and the weight of the context.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)
open GI.Machine (BinOp)

variable {q κ : ℕ}

/-! ### Encodings -/

/-- A tuple, as the list of its entries. -/
def stTv (t : Fin κ → Fin q) : Val := natList (stL fun i => (t i : ℕ))

/-- An ordered test tuple `(b, t)`, as `[b, t]`. -/
def stTT (a : TestTuple q κ) : Val := .list [boolVal a.1, stTv a.2]

theorem stL_injective : Function.Injective (stL : (Fin κ → ℕ) → List ℕ) := by
  intro f g h
  funext i
  have := congrArg (fun l => l[(i : ℕ)]?) h
  simpa [stL] using this

theorem natList_injective : Function.Injective natList := by
  intro l l' h
  simp only [natList, Val.list.injEq] at h
  exact List.map_injective_iff.2 (fun _ _ h => by cases h; rfl) h

theorem stTv_injective : Function.Injective (stTv : (Fin κ → Fin q) → Val) := by
  intro t t' h
  have h1 := stL_injective (natList_injective h)
  funext i
  exact Fin.ext (congrFun h1 i)

theorem stTT_injective : Function.Injective (stTT : TestTuple q κ → Val) := by
  rintro ⟨b, e⟩ ⟨b', e'⟩ h
  simp only [stTT, Val.list.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  have hb : b = b' := by
    simp only [Val.nat.injEq] at h1
    cases b <;> cases b' <;> simp_all
  have he : e = e' := DFunLike.coe_injective (stTv_injective h2)
  rw [hb, he]

theorem stL_le_of_fin (t : Fin κ → Fin q) : ∀ i, ((t i : ℕ)) ≤ q := fun i => (t i).isLt.le

theorem wt_stTv_le (t : Fin κ → Fin q) {M : ℕ} (hq : q ≤ M) (hκ : κ ≤ M) :
    (stTv t).wt ≤ 5 * (M + 1) ^ 2 :=
  wt_natList_le_sq (stL_le (fun i => ((t i).isLt.le.trans hq))) (by simp [stL, hκ])

theorem wt_stTT_le (a : TestTuple q κ) {M : ℕ} (hq : q ≤ M) (hκ : κ ≤ M) :
    (stTT a).wt ≤ 25 * (M + 1) ^ 2 := by
  have h1 := wt_list2_le (boolVal a.1) (stTv a.2)
  have h2 := wt_boolVal_le a.1
  have h3 := wt_stTv_le (⇑a.2) hq hκ
  have h4 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold stTT; omega

/-! ### The relation read from a table -/

open Classical in
/-- **The relation decided from a table `cr` of the ordered test tuples**: `(x, t₀)` against
`(z, t)` (`z = 0` for `x`, `z = 1` for `y`). -/
noncomputable def stRelTab (cr : TestTuple q κ → TestTuple q κ → Bool) (z : ℕ)
    (t t₀ : Fin κ → Fin q) : Bool :=
  if h0 : Function.Injective t₀ then
    if h : Function.Injective t then cr (false, ⟨t₀, h0⟩) (decide (z = 1), ⟨t, h⟩) else false
  else if Function.Injective t then false else decide (∀ i j, t₀ i = t₀ j ↔ t i = t j)

open Classical in
/-- The table of the comparison relation. -/
noncomputable def stCr {Ω C : Type} (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom]
    (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) (x y : S.dom → C) :
    TestTuple q κ → TestTuple q κ → Bool := fun a b =>
  decide (GI.LocalCertificates.CompareRel S.domGroup πd κ (strOf S x y a.1, ⇑a.2)
    (strOf S x y b.1, ⇑b.2))

/-- **The table relation is the tuple relation `stRel`** for the table of `CompareRel`. -/
theorem stRelTab_eq {Ω C : Type} (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom]
    (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) (x y : S.dom → C) {z : ℕ} (hz : z < 2)
    (t t₀ : Fin κ → Fin q) :
    stRelTab (stCr S πd κ x y) z t t₀ = stRel S πd κ x y z t t₀ := by
  classical
  have hs : strOf S x y (decide (z = 1)) = if z = 0 then x else y := by
    unfold strOf
    rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl <;> simp
  unfold stRelTab stRel GI.LocalCertificates.tupleRel
  by_cases h0 : Function.Injective t₀ <;> by_cases h : Function.Injective t
  · simp only [h0, h, dite_true, stCr, true_and, not_true_eq_false, false_and, or_false]
    rw [hs]
    simp only [strOf, Bool.false_eq_true, if_false]
    rfl
  · simp [h0, h]
  · simp [h0, h]
  · simp [h0, h]

/-! ### Reading the table -/

theorem st_flatMap_getElem {α β : Type} (l₁ l₂ : List α) (r : α → α → β) {i j : ℕ}
    (hi : i < l₁.length) (hj : j < l₂.length) :
    (l₁.flatMap fun a => l₂.map (r a))[i * l₂.length + j]? = some (r l₁[i] l₂[j]) := by
  induction l₁ generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by simpa using hj)]
      simp [List.getElem?_eq_getElem hj]
    | succ i =>
      rw [List.getElem?_append_right (by simp [Nat.succ_mul]; omega)]
      have e : (i + 1) * l₂.length + j - (l₂.map (r a)).length = i * l₂.length + j := by
        simp [Nat.succ_mul]; omega
      rw [e, ih (by simpa using hi)]
      simp

/-- The context: the encoded test tuples and the table. -/
noncomputable def stCv (tt : List (TestTuple q κ)) (cr : TestTuple q κ → TestTuple q κ → Bool) :
    Val :=
  .list [.list (tt.map stTT), .list ((tt.flatMap fun a => tt.map (cr a)).map boolVal)]

/-! ### The key test -/

/-- On `[key, x]`, both of the form `[b, l]`: whether they are equal. -/
def stKeyF (eqn : ℕ) : Expr :=
  .ite (.arith .eq (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0)))
    (.call eqn (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1)))) (.nat 0)

/-- The cost constant of the key test. -/
def stKeyK : ℕ := 10 ^ 6

open Classical in
theorem stKey_spec {P : Program} {f eqn : ℕ} (hf : P.funs[f]? = some (stKeyF eqn))
    (heq : P.HasAt eqn (eqNatsFuns eqn)) (a a' : TestTuple q κ) {M : ℕ} (hq : q ≤ M)
    (hκ : κ ≤ M) :
    FunDet P f (.list [stTT a', stTT a]) (boolVal (decide (stTT a = stTT a')))
      (stKeyK * (M + 1) ^ 3) := by
  set l := stL fun i => ((a.2 i : Fin q) : ℕ)
  set l' := stL fun i => ((a'.2 i : Fin q) : ℕ)
  set vs : List Val := [stTT a', stTT a]
  have g0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := stTT a') rfl
  have g1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := stTT a) rfl
  have b0 := Det.get' g0 (Det.nat 0) (v := boolVal a'.1) rfl
  have b1 := Det.get' g1 (Det.nat 0) (v := boolVal a.1) rfl
  have l0 := Det.get' g0 (Det.nat 1) (v := natList l') rfl
  have l1 := Det.get' g1 (Det.nat 1) (v := natList l) rfl
  have hc := Det.arith (op := .eq) b0 b1
  have hcall := Det.call (Det.mk2 l0 l1) (eqNats_spec heq l' l)
  have hd := Det.ite' hc hcall (Det.nat 0)
  -- the value
  have hv : (if BinOp.eval .eq a'.1.toNat a.1.toNat = 0 then Val.nat 0 else
      boolVal (decide (l' = l))) = boolVal (decide (stTT a = stTT a')) := by
    have hiff : stTT a = stTT a' ↔ a.1 = a'.1 ∧ l = l' := by
      constructor
      · intro h
        have := stTT_injective h
        subst this; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        simp only [stTT, stTv]
        rw [h1]
        change Val.list [boolVal a'.1, natList l] = Val.list [boolVal a'.1, natList l']
        rw [h2]
    have key : BinOp.eval .eq a'.1.toNat a.1.toNat = if a.1 = a'.1 then 1 else 0 := by
      simp only [BinOp.eval]
      generalize a.1 = u; generalize a'.1 = u'
      cases u <;> cases u' <;> rfl
    simp only [key]
    by_cases h1 : a.1 = a'.1
    · simp only [h1, if_true, one_ne_zero, if_false]
      by_cases h2 : l = l'
      · rw [decide_eq_true h2.symm, decide_eq_true (hiff.2 ⟨h1, h2⟩)]
      · rw [decide_eq_false (fun h => h2 h.symm), decide_eq_false (fun h => h2 (hiff.1 h).2)]
    · simp only [h1, if_false, if_true]
      rw [decide_eq_false (fun h => h1 (hiff.1 h).1)]
      rfl
  rw [hv] at hd
  refine FunDet.intro hf (hd.mono ?_)
  -- the cost
  have hA := wt_stTT_le a hq hκ
  have hA' := wt_stTT_le a' hq hκ
  have hL : (natList l).wt ≤ 5 * (M + 1) ^ 2 := wt_stTv_le (⇑a.2) hq hκ
  have hL' : (natList l').wt ≤ 5 * (M + 1) ^ 2 := wt_stTv_le (⇑a'.2) hq hκ
  have hll : l'.length = κ := by simp [l', stL]
  have hvs := wt_list2_le (stTT a') (stTT a)
  have hm2 := wt_list2_le (natList l') (natList l)
  have e1 : (Val.list vs).wt = (Val.list [stTT a', stTT a]).wt := rfl
  have hb0 := wt_boolVal_le a'.1
  have hb1 := wt_boolVal_le a.1
  have hbe : (Val.nat (BinOp.eval .eq a'.1.toNat a.1.toNat)).wt ≤ 3 := by
    simp only [BinOp.eval]; split <;> simp [wt_nat, GI.Machine.len_zero]
  have hbo := wt_boolVal_le (decide (l' = l))
  have hbo' := wt_boolVal_le (decide (stTT a = stTT a'))
  have h0 := wt_nat_le 0
  have h1 := wt_nat_le 1
  have hY : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hY3 : (M + 1) ^ 3 = (M + 1) * (M + 1) ^ 2 := by ring
  have hMY : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hloop : loopModK * (l'.length + 1) * ((Val.list [natList l', natList l]).wt +
      l'.length + 4) ≤ loopModK * (M + 1) * (35 * (M + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (by omega)) (by omega)
  have hloop' : loopModK * (M + 1) * (35 * (M + 1) ^ 2) = 35 * loopModK * (M + 1) ^ 3 := by
    rw [hY3]; ring
  have hK : stKeyK * (M + 1) ^ 3 = (35 * loopModK + 965000) * (M + 1) ^ 3 := by
    norm_num [stKeyK, loopModK]
  have hY3' : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [hK]
  clear hv hd hcall hc
  generalize (M + 1) ^ 2 = Y at *
  generalize (M + 1) ^ 3 = T at *
  generalize loopModK = Lk at *
  rw [show (35 * Lk + 965000) * T = 35 * Lk * T + 965000 * T by ring]
  omega

/-! ### The search for a test tuple -/

open Classical in
/-- **The position of a test tuple** in the list: `find` with the key test. -/
theorem stFind_spec {P : Program} {bf bk eqn : ℕ} (hfind : P.HasAt bf (findFuns bf bk))
    (hk : P.funs[bk]? = some (stKeyF eqn)) (heq : P.HasAt eqn (eqNatsFuns eqn))
    {tt : List (TestTuple q κ)} {a' : TestTuple q κ} (ha : a' ∈ tt) {M : ℕ} (hq : q ≤ M)
    (hκ : κ ≤ M) (hlen : tt.length ≤ M) (hw : (Val.list (tt.map stTT)).wt ≤ M) :
    ∃ i, ∃ hi : i < tt.length, tt[i] = a' ∧
      FunDet P bf (.list [stTT a', .list (tt.map stTT)]) (.nat i) (5 * (stKeyK * (M + 1) ^ 4)) := by
  have hT : ∀ x ∈ tt.map stTT, FunDet P bk (.list [stTT a', x])
      (boolVal (decide (x = stTT a'))) (stKeyK * (M + 1) ^ 3) := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact stKey_spec hk heq a a' hq hκ
  have hfd := find_spec hfind hT
  set i := tt.findIdx fun a => decide (a = a') with hi
  have hidx : (tt.map stTT).findIdx (fun x => decide (x = stTT a')) = i := by
    rw [List.findIdx_map, hi]
    congr 1
    funext a
    simp only [Function.comp_apply]
    exact decide_eq_decide.2 ⟨fun h => stTT_injective h, fun h => by rw [h]⟩
  have hlt : i < tt.length := List.findIdx_lt_length_of_exists ⟨a', ha, by simp⟩
  have hget : tt[i] = a' := by
    have := List.findIdx_getElem (w := hlt)
    simpa using this
  refine ⟨i, hlt, hget, FunAll.mono hfd fun w cost hw' => ⟨by rw [hw'.1, hidx], ?_⟩⟩
  have hc := hw'.2
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
  have hK := wt_stTT_le a' hq hκ
  have h2 := wt_list2_le (stTT a') (.list (tt.map stTT))
  have hMY : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY4 : (M + 1) ^ 4 = (M + 1) * (M + 1) ^ 3 := by ring
  have hY3 : (M + 1) ^ 3 = (M + 1) * (M + 1) ^ 2 := by ring
  have h3 : tt.length * (stKeyK * (M + 1) ^ 3) ≤ stKeyK * (M + 1) ^ 4 := by
    rw [hY4]
    calc tt.length * (stKeyK * (M + 1) ^ 3) ≤ (M + 1) * (stKeyK * (M + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have h4 : loopModK * (tt.length + 1) * ((Val.list [stTT a', .list (tt.map stTT)]).wt +
      2 * tt.length + 3) ≤ loopModK * (M + 1) * (60 * (M + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (by omega)) (by omega)
  have h7 : 60 * loopModK ≤ stKeyK := by norm_num [loopModK, stKeyK]
  have h34 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : loopModK * (M + 1) * (60 * (M + 1) ^ 2) ≤ stKeyK * (M + 1) ^ 4 := by
    generalize loopModK = Lk at *
    generalize stKeyK = Kk at *
    calc Lk * (M + 1) * (60 * (M + 1) ^ 2) = 60 * Lk * (M + 1) ^ 3 := by rw [hY3]; ring
      _ ≤ Kk * (M + 1) ^ 4 := Nat.mul_le_mul h7 h34
  clear hw' hfd hT
  generalize stKeyK * (M + 1) ^ 4 = K at *
  omega

/-! ### The table lookup -/

/-- On `[cv, z, tv t, tv t₀]`: the table entry of `(x, t₀)` against `(z, t)`. -/
def stLookF (bf : ℕ) : Expr :=
  .letE (.call bf (mk2 (mk2 (.nat 0) (arg 3)) (.get (arg 0) (.nat 0))))
    (.letE (.call bf (mk2 (mk2 (arg 1) (arg 2)) (.get (arg 0) (.nat 0))))
      (.get (.get (arg 0) (.nat 1))
        (.arith .add (.arith .mul (.var 1) (.length (.get (arg 0) (.nat 0)))) (.var 2))))

/-- The cost constant of the lookup. -/
def stLookK : ℕ := 10 ^ 8

theorem stCv_facts {tt : List (TestTuple q κ)} {cr : TestTuple q κ → TestTuple q κ → Bool}
    {M : ℕ} (hcv : (stCv tt cr).wt ≤ M) :
    (Val.list (tt.map stTT)).wt ≤ M ∧ tt.length ≤ M ∧
      (Val.list ((tt.flatMap fun a => tt.map (cr a)).map boolVal)).wt ≤ M := by
  have h1 : (Val.list (tt.map stTT)).wt < (stCv tt cr).wt := wt_le_wt_list (by simp)
  have h2 : (Val.list ((tt.flatMap fun a => tt.map (cr a)).map boolVal)).wt <
    (stCv tt cr).wt := wt_le_wt_list (by simp)
  have h3 := length_lt_wt_list (tt.map stTT)
  simp only [List.length_map] at h3
  omega

theorem stTT_false (t₀ : Fin κ → Fin q) (h0 : Function.Injective t₀) :
    Val.list [.nat 0, stTv t₀] = stTT (false, ⟨t₀, h0⟩) := rfl

theorem stTT_z {z : ℕ} (hz : z < 2) (t : Fin κ → Fin q) (h : Function.Injective t) :
    Val.list [.nat z, stTv t] = stTT (decide (z = 1), ⟨t, h⟩) := by
  rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl <;> rfl

/-- **The table lookup.** For injective `t, t₀` the entry of `(false, t₀)` against
`(z = 1, t)`. -/
theorem stLook_spec {P : Program} {f bf bk eqn : ℕ} (hf : P.funs[f]? = some (stLookF bf))
    (hfind : P.HasAt bf (findFuns bf bk))
    (hk : P.funs[bk]? = some (stKeyF eqn)) (heq : P.HasAt eqn (eqNatsFuns eqn))
    {tt : List (TestTuple q κ)} (hmem : ∀ a, a ∈ tt) (cr : TestTuple q κ → TestTuple q κ → Bool)
    {M : ℕ} (hq : q ≤ M) (hκ : κ ≤ M) (hcv : (stCv tt cr).wt ≤ M) {z : ℕ} (hz : z < 2)
    {t t₀ : Fin κ → Fin q} (h : Function.Injective t) (h0 : Function.Injective t₀) :
    FunDet P f (.list [stCv tt cr, .nat z, stTv t, stTv t₀])
      (boolVal (cr (false, ⟨t₀, h0⟩) (decide (z = 1), ⟨t, h⟩))) (stLookK * (M + 1) ^ 4) := by
  obtain ⟨hwt, hlen, hwtab⟩ := stCv_facts hcv
  obtain ⟨i, hi, hgi, hfi⟩ := stFind_spec hfind hk heq (hmem (false, ⟨t₀, h0⟩)) hq hκ hlen hwt
  obtain ⟨j, hj, hgj, hfj⟩ := stFind_spec hfind hk heq (hmem (decide (z = 1), ⟨t, h⟩)) hq hκ
    hlen hwt
  set ttV := Val.list (tt.map stTT) with httV
  set tab := (tt.flatMap fun a => tt.map (cr a)).map boolVal with htab
  set a := Val.list [stCv tt cr, .nat z, stTv t, stTv t₀] with ha
  have hcvV : stCv tt cr = .list [ttV, .list tab] := rfl
  -- first search
  have c0 := Det.get' (Det.arg' (P := P) (vs := [stCv tt cr, .nat z, stTv t, stTv t₀]) (rest := [])
    (j := 0) rfl) (Det.nat 0) (v := ttV) rfl
  have k0 := Det.mk2 (Det.nat (P := P) (env := [a]) 0)
    (Det.arg' (vs := [stCv tt cr, .nat z, stTv t, stTv t₀]) (rest := []) (j := 3) rfl)
  rw [stTT_false t₀ h0] at k0
  have d1 := Det.call (Det.mk2 k0 c0) hfi
  -- second search
  have c0' := Det.get' (Det.arg' (P := P) (vs := [stCv tt cr, .nat z, stTv t, stTv t₀])
    (rest := [.nat i]) (j := 0) rfl) (Det.nat 0) (v := ttV) rfl
  have k1 := Det.mk2 (Det.arg' (P := P) (vs := [stCv tt cr, .nat z, stTv t, stTv t₀])
    (rest := [.nat i]) (j := 1) rfl)
    (Det.arg' (vs := [stCv tt cr, .nat z, stTv t, stTv t₀]) (rest := [.nat i]) (j := 2) rfl)
  rw [stTT_z hz t h] at k1
  have d2 := Det.call (Det.mk2 k1 c0') hfj
  -- the entry
  set env := [a, Val.nat i, Val.nat j]
  have t1 := Det.get' (Det.arg' (P := P) (vs := [stCv tt cr, .nat z, stTv t, stTv t₀])
    (rest := [.nat i, .nat j]) (j := 0) rfl) (Det.nat 1) (v := .list tab) rfl
  have c2 := Det.get' (Det.arg' (P := P) (vs := [stCv tt cr, .nat z, stTv t, stTv t₀])
    (rest := [.nat i, .nat j]) (j := 0) rfl) (Det.nat 0) (v := ttV) rfl
  have hl := Det.length c2
  have vi := Det.var' (P := P) (env := env) (i := 1) (v := .nat i) rfl
  have vj := Det.var' (P := P) (env := env) (i := 2) (v := .nat j) rfl
  have hm := Det.arith' (op := .mul) vi hl (z := i * tt.length) (by simp [BinOp.eval])
  have hs := Det.arith' (op := .add) hm vj (z := i * tt.length + j) rfl
  have hentry : tab[i * tt.length + j]? = some (boolVal (cr (false, ⟨t₀, h0⟩)
      (decide (z = 1), ⟨t, h⟩))) := by
    rw [htab, List.getElem?_map, st_flatMap_getElem tt tt cr hi hj, hgi, hgj]
    rfl
  have dg := Det.get' t1 hs hentry
  have dall := Det.letE d1 (Det.letE d2 dg)
  refine FunDet.intro hf (dall.mono ?_)
  -- the cost
  have hwa := wt_list4_le (stCv tt cr) (.nat z) (stTv t) (stTv t₀)
  have hv1 := wt_stTv_le t hq hκ
  have hv2 := wt_stTv_le t₀ hq hκ
  have hz3 := wt_nat_le z
  have hI := wt_nat_le i
  have hJ := wt_nat_le j
  have hA1 := wt_stTT_le (false, ⟨t₀, h0⟩) hq hκ
  have hA2 := wt_stTT_le (decide (z = 1), ⟨t, h⟩) hq hκ
  have hp1 := wt_list2_le (stTT (false, ⟨t₀, h0⟩)) ttV
  have hp2 := wt_list2_le (stTT (decide (z = 1), ⟨t, h⟩)) ttV
  have hb := wt_boolVal_le (cr (false, ⟨t₀, h0⟩) (decide (z = 1), ⟨t, h⟩))
  have hn0 := wt_nat_le 0
  have hn1 := wt_nat_le 1
  have hln := wt_nat_le (List.map stTT tt).length
  have hle : (List.map stTT tt).length = tt.length := List.length_map ..
  have hij : i * tt.length + j ≤ (M + 1) ^ 2 := by
    have : i * tt.length ≤ M * M := Nat.mul_le_mul (by omega) hlen
    nlinarith
  have hMY : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY4 : (M + 1) ^ 2 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hK : stLookK * (M + 1) ^ 4 = 10 * (stKeyK * (M + 1) ^ 4) + 90000000 * (M + 1) ^ 4 := by
    norm_num [stLookK, stKeyK]; ring
  rw [hK]
  clear dall dg d1 d2 hfi hfj
  generalize stKeyK * (M + 1) ^ 4 = K at *
  generalize (M + 1) ^ 4 = Z at *
  generalize (M + 1) ^ 2 = Y at *
  have e1 : (Val.list [Val.nat 0, stTv t₀]).wt = (stTT (false, ⟨t₀, h0⟩)).wt := rfl
  omega

/-! ### The relation module -/

/-- **The relation** on `[[cv, z, tv t], tv t₀]`: patterns, range, two injectivity tests, then
the table lookup or the comparison of the patterns. -/
def stRelF (b : ℕ) : Expr :=
  .letE (.call (b + 3) (.get (arg 0) (.nat 2)))
    (.letE (.call (b + 3) (arg 1))
      (.letE (.call (b + 12) (.length (arg 1)))
        (.letE (.call (b + 15) (mk2 (.var 1) (.var 3)))
          (.letE (.call (b + 15) (mk2 (.var 2) (.var 3)))
            (.ite (.var 5)
              (.ite (.var 4)
                (.call (b + 1) (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
                  (.get (arg 0) (.nat 2)) (arg 1)))
                (.nat 0))
              (.ite (.var 4) (.nat 0) (.call (b + 15) (mk2 (.var 1) (.var 2)))))))))

/-- **The relation module** at base `b` (21 functions). -/
def stRelFuns (b : ℕ) : List Expr :=
  [stRelF b, stLookF (b + 18), stKeyF (b + 15)] ++ stPatFuns (b + 3) ++ rangeFuns (b + 12) ++
    eqNatsFuns (b + 15) ++ findFuns (b + 18) (b + 2)

/-- The cost constant of the relation module. -/
def stRelK : ℕ := 10 ^ 10

/-- The values of a tuple, as numbers. -/
def stF (t : Fin κ → Fin q) : Fin κ → ℕ := fun i => (t i : ℕ)

theorem stF_injective_iff (t : Fin κ → Fin q) : Function.Injective (stF t) ↔ Function.Injective t :=
  ⟨fun h i j hij => h (by simp [stF, hij]), fun h i j hij => h (Fin.ext hij)⟩

theorem stF_pattern_iff (t t₀ : Fin κ → Fin q) :
    stPat (stF t) = stPat (stF t₀) ↔ ∀ i j, t₀ i = t₀ j ↔ t i = t j := by
  rw [stPat_eq_iff]
  simp only [stF, Fin.val_inj]
  exact ⟨fun h i j => (h i j).symm, fun h i j => (h i j).symm⟩

theorem stTv_eq (t : Fin κ → Fin q) : stTv t = natList (stL (stF t)) := rfl

/-- The weight of the numbers of a pattern or a tuple. -/
theorem st_wt_small {M : ℕ} (hκ : κ ≤ M) (t : Fin κ → Fin q) :
    (natList (stPat (stF t))).wt ≤ 5 * (M + 1) ^ 2 ∧
      (natList (List.range κ)).wt ≤ 5 * (M + 1) ^ 2 := by
  constructor
  · exact wt_natList_le_sq (fun x hx => (stPat_le _ x hx).trans hκ)
      (by rw [stPat_length]; exact hκ)
  · exact wt_natList_le_sq (fun x hx => by simp at hx; omega) (by simp [hκ])

theorem st_eqn_cost {M : ℕ} (hκ : κ ≤ M) {xs ys : List ℕ} (hx : xs.length = κ)
    (hw : (Val.list [natList xs, natList ys]).wt ≤ 30 * (M + 1) ^ 2) :
    loopModK * (xs.length + 1) * ((Val.list [natList xs, natList ys]).wt + xs.length + 4) ≤
      35000 * (M + 1) ^ 3 := by
  have hMY : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY1 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc loopModK * (xs.length + 1) * ((Val.list [natList xs, natList ys]).wt + xs.length + 4)
      ≤ loopModK * (M + 1) * (35 * (M + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (by omega)) (by omega)
    _ = 35000 * (M + 1) ^ 3 := by simp only [loopModK]; ring

/-- **The relation module meets its contract**: on `[[cv, z, tv t], tv t₀]` it returns
`stRelTab cr z t t₀`, at cost `stRelK (M + 1)^4`. -/
theorem stRel_spec {P : Program} {b : ℕ} (h : P.HasAt b (stRelFuns b))
    {tt : List (TestTuple q κ)} (hmem : ∀ a, a ∈ tt) (cr : TestTuple q κ → TestTuple q κ → Bool)
    {M : ℕ} (hq : q ≤ M) (hκ : κ ≤ M) (hcv : (stCv tt cr).wt ≤ M) :
    StRelOK P b (stCv tt cr) stTv (stRelTab cr) (stRelK * (M + 1) ^ 4) := by
  simp only [stRelFuns] at h
  have h3 := h.left.left.left.left
  have hf0 : P.funs[b]? = some (stRelF b) := by simpa using h3 0 (by simp)
  have hf1 : P.funs[b + 1]? = some (stLookF (b + 18)) := by simpa using h3 1 (by simp)
  have hf2 : P.funs[b + 2]? = some (stKeyF (b + 15)) := by simpa using h3 2 (by simp)
  have hpat : P.HasAt (b + 3) (stPatFuns (b + 3)) := by simpa using h.left.left.left.right
  have hrange : P.HasAt (b + 12) (rangeFuns (b + 12)) := by
    simpa [stPatFuns, mapFuns, findEqFuns, findFuns, loopFuns, Nat.add_assoc] using
      h.left.left.right
  have heqn : P.HasAt (b + 15) (eqNatsFuns (b + 15)) := by
    simpa [stPatFuns, mapFuns, findEqFuns, findFuns, loopFuns, rangeFuns, Nat.add_assoc] using
      h.left.right
  have hfind : P.HasAt (b + 18) (findFuns (b + 18) (b + 2)) := by
    simpa [stPatFuns, mapFuns, findEqFuns, findFuns, loopFuns, rangeFuns, eqNatsFuns,
      Nat.add_assoc] using h.right
  intro z t t₀ hz
  obtain ⟨hwt, hlen, hwtab⟩ := stCv_facts hcv
  have hFt : ∀ i, stF t i ≤ M := fun i => (t i).isLt.le.trans hq
  have hFt₀ : ∀ i, stF t₀ i ≤ M := fun i => (t₀ i).isLt.le.trans hq
  set pt := natList (stPat (stF t)) with hpt
  set p0 := natList (stPat (stF t₀)) with hp0
  set rg := natList (List.range κ) with hrg
  set it := boolVal (decide (stPat (stF t) = List.range κ)) with hit
  set i0 := boolVal (decide (stPat (stF t₀) = List.range κ)) with hi0
  set c := Val.list [stCv tt cr, .nat z, stTv t] with hc
  set a := Val.list [c, stTv t₀] with ha
  -- the patterns
  have d1 := Det.call (Det.get' (Det.arg' (P := P) (vs := [c, stTv t₀]) (rest := []) (j := 0) rfl)
    (Det.nat 2) (v := stTv t) rfl) (stPat_spec hpat (stF t) hFt hκ)
  have d2 := Det.call (Det.arg' (P := P) (vs := [c, stTv t₀]) (rest := [pt]) (j := 1) rfl)
    (stPat_spec hpat (stF t₀) hFt₀ hκ)
  -- the range
  have hl := Det.length (Det.arg' (P := P) (vs := [c, stTv t₀]) (rest := [pt, p0]) (j := 1)
    (v := .list ((stL (stF t₀)).map Val.nat)) rfl)
  have hlk : ((stL (stF t₀)).map Val.nat).length = κ := by simp [stL]
  rw [hlk] at hl
  have hwr : rg.wt ≤ 5 * (M + 1) ^ 2 := (st_wt_small hκ t).2
  have hrk : FunDet P (b + 12) (.nat κ) rg (loopModK * (M + 1) * (20 * (M + 1) ^ 2)) := by
    refine FunAll.mono (range_spec hrange κ) fun w cost hw => ⟨hw.1, ?_⟩
    have := hw.2
    rw [hw.1] at this
    have hk2 := wt_nat_le κ
    have hwr2 : (natList (List.range κ)).wt ≤ 5 * (M + 1) ^ 2 := hwr
    have hMY : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    refine this.trans (Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (by omega)) (by omega))
  have d3 := Det.call hl hrk
  -- the injectivity tests
  have d4 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, pt, p0, rg]) (i := 1) (v := pt) rfl)
    (Det.var' (i := 3) (v := rg) rfl)) (eqNats_spec heqn (stPat (stF t)) (List.range κ))
  have d5 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, pt, p0, rg, it]) (i := 2) (v := p0)
    rfl) (Det.var' (i := 3) (v := rg) rfl)) (eqNats_spec heqn (stPat (stF t₀)) (List.range κ))
  -- the weights
  have hwp : pt.wt ≤ 5 * (M + 1) ^ 2 := (st_wt_small hκ t).1
  have hwp0 : p0.wt ≤ 5 * (M + 1) ^ 2 := (st_wt_small hκ t₀).1
  have hwr' : rg.wt ≤ 5 * (M + 1) ^ 2 := hwr
  have hY1 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hv1 := wt_stTv_le t hq hκ
  have hv2 := wt_stTv_le t₀ hq hκ
  have hwc := wt_list3_le (stCv tt cr) (.nat z) (stTv t)
  have hwa := wt_list2_le c (stTv t₀)
  have hz3 := wt_nat_le z
  have hbit := wt_boolVal_le (decide (stPat (stF t) = List.range κ))
  have hbi0 := wt_boolVal_le (decide (stPat (stF t₀) = List.range κ))
  have hpl : (stPat (stF t)).length = κ := stPat_length _
  have hpl0 : (stPat (stF t₀)).length = κ := stPat_length _
  have hMY : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY34 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hY24 : (M + 1) ^ 2 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hY23 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : loopModK * ((stPat (stF t)).length + 1) * ((Val.list [natList (stPat (stF t)), natList (List.range κ)]).wt +
      (stPat (stF t)).length + 4) ≤ 35000 * (M + 1) ^ 3 :=
    st_eqn_cost (xs := stPat (stF t)) (ys := List.range κ) hκ hpl (by
      show (Val.list [pt, rg]).wt ≤ 30 * (M + 1) ^ 2
      have := wt_list2_le pt rg; omega)
  have e2 : loopModK * ((stPat (stF t₀)).length + 1) * ((Val.list [natList (stPat (stF t₀)), natList (List.range κ)]).wt +
      (stPat (stF t₀)).length + 4) ≤ 35000 * (M + 1) ^ 3 :=
    st_eqn_cost (xs := stPat (stF t₀)) (ys := List.range κ) hκ hpl0 (by
      show (Val.list [p0, rg]).wt ≤ 30 * (M + 1) ^ 2
      have := wt_list2_le p0 rg; omega)
  have e3 : loopModK * ((stPat (stF t)).length + 1) * ((Val.list [natList (stPat (stF t)), natList (stPat (stF t₀))]).wt +
      (stPat (stF t)).length + 4) ≤ 35000 * (M + 1) ^ 3 :=
    st_eqn_cost (xs := stPat (stF t)) (ys := stPat (stF t₀)) hκ hpl (by
      show (Val.list [pt, p0]).wt ≤ 30 * (M + 1) ^ 2
      have := wt_list2_le pt p0; omega)
  -- the reads of the argument in the body
  set env := [a, pt, p0, rg, it, i0] with henv
  have r0 : ∀ k (v : Val), [stCv tt cr, .nat z, stTv t][k]? = some v →
      Det P env (.get (arg 0) (.nat k)) v (2 * a.wt + 5 + (k + 3) + v.wt + 1) := fun k v hv =>
    Det.get' (Det.arg' (P := P) (vs := [c, stTv t₀]) (rest := [pt, p0, rg, it, i0]) (j := 0) rfl)
      (Det.nat k) hv
  have r1 := Det.arg' (P := P) (vs := [c, stTv t₀]) (rest := [pt, p0, rg, it, i0]) (j := 1)
    (v := stTv t₀) rfl
  have hY4 : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hiff : ∀ u : Fin κ → Fin q, stPat (stF u) = List.range κ ↔ Function.Injective u :=
    fun u => (stPat_eq_range_iff _).trans (stF_injective_iff u)
  have hbody : Det P env
      (.ite (.var 5)
        (.ite (.var 4)
          (.call (b + 1) (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
            (.get (arg 0) (.nat 2)) (arg 1)))
          (.nat 0))
        (.ite (.var 4) (.nat 0) (.call (b + 15) (mk2 (.var 1) (.var 2)))))
      (boolVal (stRelTab cr z t t₀)) (stLookK * (M + 1) ^ 4 + 10 ^ 6 * (M + 1) ^ 4) := by
    have hcw : c.wt = (Val.list [stCv tt cr, .nat z, stTv t]).wt := rfl
    have haw : a.wt = (Val.list [c, stTv t₀]).wt := rfl
    have hwa' : a.wt ≤ 70 * (M + 1) ^ 2 := by omega
    by_cases h0 : Function.Injective t₀ <;> by_cases h1 : Function.Injective t
    · have v5 : Det P env (.var 5) (.nat 1) 4 := (Det.var' (i := 5) (v := .nat 1) (by
        simp only [henv, hi0, decide_eq_true ((hiff t₀).2 h0)]; rfl)).mono (by
          have := wt_nat_le 1; omega)
      have v4 : Det P env (.var 4) (.nat 1) 4 := (Det.var' (i := 4) (v := .nat 1) (by
        simp only [henv, hit, decide_eq_true ((hiff t).2 h1)]; rfl)).mono (by
          have := wt_nat_le 1; omega)
      have dm := Det.mk4 (r0 0 (stCv tt cr) rfl) (r0 1 (.nat z) rfl) (r0 2 (stTv t) rfl) r1
      have dl := Det.call dm (stLook_spec hf1 hfind hf2 heqn hmem cr hq hκ hcv hz h1 h0)
      have hval : boolVal (cr (false, ⟨t₀, h0⟩) (decide (z = 1), ⟨t, h1⟩)) =
          boolVal (stRelTab cr z t t₀) := by simp [stRelTab, h0, h1]
      rw [hval] at dl
      refine (Det.ite_pos v5 one_ne_zero (Det.ite_pos v4 one_ne_zero dl)).mono ?_
      have := wt_list4_le (stCv tt cr) (.nat z) (stTv t) (stTv t₀)
      have := wt_boolVal_le (stRelTab cr z t t₀)
      generalize stLookK * (M + 1) ^ 4 = K at *
      generalize (M + 1) ^ 4 = Z at *
      generalize (M + 1) ^ 2 = Y at *
      norm_num
      omega
    · have v5 : Det P env (.var 5) (.nat 1) 4 := (Det.var' (i := 5) (v := .nat 1) (by
        simp only [henv, hi0, decide_eq_true ((hiff t₀).2 h0)]; rfl)).mono (by
          have := wt_nat_le 1; omega)
      have v4 : Det P env (.var 4) (.nat 0) 4 := (Det.var' (i := 4) (v := .nat 0) (by
        simp only [henv, hit, decide_eq_false (fun h => h1 ((hiff t).1 h))]; rfl)).mono (by
          have := wt_nat_le 0; omega)
      have hval : Val.nat 0 = boolVal (stRelTab cr z t t₀) := by simp [stRelTab, h0, h1]
      refine (Det.ite_pos v5 one_ne_zero (Det.ite_zero v4 (hval ▸ Det.nat 0))).mono ?_
      have := wt_boolVal_le (stRelTab cr z t t₀)
      generalize stLookK * (M + 1) ^ 4 = K at *
      generalize (M + 1) ^ 4 = Z at *
      norm_num
      omega
    · have v5 : Det P env (.var 5) (.nat 0) 4 := (Det.var' (i := 5) (v := .nat 0) (by
        simp only [henv, hi0, decide_eq_false (fun h => h0 ((hiff t₀).1 h))]; rfl)).mono (by
          have := wt_nat_le 0; omega)
      have v4 : Det P env (.var 4) (.nat 1) 4 := (Det.var' (i := 4) (v := .nat 1) (by
        simp only [henv, hit, decide_eq_true ((hiff t).2 h1)]; rfl)).mono (by
          have := wt_nat_le 1; omega)
      have hval : Val.nat 0 = boolVal (stRelTab cr z t t₀) := by simp [stRelTab, h0, h1]
      refine (Det.ite_zero v5 (Det.ite_pos v4 one_ne_zero (hval ▸ Det.nat 0))).mono ?_
      have := wt_boolVal_le (stRelTab cr z t t₀)
      generalize stLookK * (M + 1) ^ 4 = K at *
      generalize (M + 1) ^ 4 = Z at *
      norm_num
      omega
    · have v5 : Det P env (.var 5) (.nat 0) 4 := (Det.var' (i := 5) (v := .nat 0) (by
        simp only [henv, hi0, decide_eq_false (fun h => h0 ((hiff t₀).1 h))]; rfl)).mono (by
          have := wt_nat_le 0; omega)
      have v4 : Det P env (.var 4) (.nat 0) 4 := (Det.var' (i := 4) (v := .nat 0) (by
        simp only [henv, hit, decide_eq_false (fun h => h1 ((hiff t).1 h))]; rfl)).mono (by
          have := wt_nat_le 0; omega)
      have de := Det.call (Det.mk2 (Det.var' (P := P) (env := env) (i := 1) (v := pt) rfl)
        (Det.var' (i := 2) (v := p0) rfl)) (eqNats_spec heqn (stPat (stF t)) (stPat (stF t₀)))
      have hval : boolVal (decide (stPat (stF t) = stPat (stF t₀))) =
          boolVal (stRelTab cr z t t₀) := by
        have : decide (stPat (stF t) = stPat (stF t₀)) = stRelTab cr z t t₀ := by
          unfold stRelTab
          rw [dif_neg h0, if_neg h1]
          exact decide_eq_decide.2 (stF_pattern_iff t t₀)
        rw [this]
      rw [hval] at de
      refine (Det.ite_zero v5 (Det.ite_zero v4 de)).mono ?_
      have := wt_boolVal_le (stRelTab cr z t t₀)
      have := wt_list2_le pt p0
      have e3' : (Val.list [pt, p0]).wt = (Val.list [natList (stPat (stF t)), natList (stPat (stF t₀))]).wt := rfl
      generalize stLookK * (M + 1) ^ 4 = K at *
      generalize (M + 1) ^ 4 = Z at *
      generalize (M + 1) ^ 3 = T at *
      generalize (M + 1) ^ 2 = Y at *
      norm_num
      omega
  refine FunDet.intro hf0 ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4
    (Det.letE d5 hbody))))).mono ?_)
  have hcw : c.wt = (Val.list [stCv tt cr, .nat z, stTv t]).wt := rfl
  have haw : a.wt = (Val.list [c, stTv t₀]).wt := rfl
  have hwa' : a.wt ≤ 70 * (M + 1) ^ 2 := by omega
  have hb := wt_boolVal_le (stRelTab cr z t t₀)
  have hk2 := wt_nat_le κ
  have hl2 : (Val.list ((stL (stF t₀)).map Val.nat)).wt = (stTv t₀).wt := rfl
  have hm1 := wt_list2_le pt rg
  have hm2 := wt_list2_le p0 rg
  have q1 : (natList (stPat (stF t))).wt = pt.wt := rfl
  have q2 : (natList (stPat (stF t₀))).wt = p0.wt := rfl
  have q3 : (natList (List.range κ)).wt = rg.wt := rfl
  have hK : stRelK * (M + 1) ^ 4 = 10 * (stLookK * (M + 1) ^ 4) + 10 * (stPatK * (M + 1) ^ 4) +
      8900000000 * (M + 1) ^ 4 := by
    norm_num [stRelK, stLookK, stPatK]; ring
  have hloop : loopModK * (M + 1) * (20 * (M + 1) ^ 2) = 20000 * (M + 1) ^ 3 := by
    simp only [loopModK]; ring
  rw [hK, hloop]
  generalize stLookK * (M + 1) ^ 4 = K at *
  generalize stPatK * (M + 1) ^ 4 = K' at *
  generalize (M + 1) ^ 4 = Z at *
  generalize (M + 1) ^ 3 = T at *
  generalize (M + 1) ^ 2 = Y at *
  norm_num
  omega

end GI.Impl

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)

/-- **The comparison table of a round** is the table of `stCr`, in the order of `tests`. So the
context `stCv I.tests.tuples (stCr …)` is the list of encoded test tuples together with
`I.compScript.evalExact`, the value the comparison phase hands over. -/
theorem st_compTable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
    (I : Aggregation P S L) :
    haveI := I.fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq Ω := Classical.decEq _
    I.compScript.evalExact = I.tests.tuples.flatMap fun a =>
      I.tests.tuples.map (stCr S I.πd P.κ (dstr S S.x) (dstr S S.y) a) := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  obtain ⟨h1, h2⟩ := I.compScript_evalExact
  rw [h1]
  refine List.flatMap_congr fun a _ => List.map_congr_left fun b _ => ?_
  unfold stCr
  rw [Bool.eq_iff_iff, h2 a b]
  simp only [decide_eq_true_eq]

/-- **The relation module for the round**: with the context of the comparison table, the
module decides `stRel`, the relation `stCols_spec` needs (`stCz_tcol`). -/
theorem stRel_spec_round {Pg : Program} {b : ℕ} (h : Pg.HasAt b (stRelFuns b))
    {Ω C : Type} (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom] {q κ : ℕ}
    (πd : S.domGroup →* alternatingGroup (Fin q)) (x y : S.dom → C)
    (O : TestTupleOrder q κ) {M : ℕ} (hq : q ≤ M) (hκ : κ ≤ M)
    (hcv : (stCv O.tuples (stCr S πd κ x y)).wt ≤ M) :
    StRelOK Pg b (stCv O.tuples (stCr S πd κ x y)) stTv (stRel S πd κ x y)
      (stRelK * (M + 1) ^ 4) := by
  intro z t t₀ hz
  have := stRel_spec h O.mem (stCr S πd κ x y) hq hκ hcv z t t₀ hz
  rwa [stRelTab_eq S πd κ x y hz] at this

end GI.Impl
