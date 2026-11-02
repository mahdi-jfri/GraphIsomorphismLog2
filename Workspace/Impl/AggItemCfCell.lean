import Workspace.Impl.AggItemCfColM
import Workspace.Lang.Lib.Search
import Workspace.Lang.Lib.OrbitT

/-!
# One entry of the orbital coloring table

The program `col` fills the table of `orbColOut H t` entry by entry. Entry `j` belongs to the
pair `(a, b) = (j % q, j / q)`. If `a = b` is an anchor, its value is the anchor color `8 + i`,
with `i` the first position of `a` in the anchor list `A` (`find`). Otherwise it is
`4 [a ∈ C] + 2 [b ∈ C] + [(a, b) in the orbital]`, with `C = Φ \ A` (`itCfCellOldF`).

The cell function `itCfCellF` runs on `[c, j]` with the context
`c = [q, ⟨Φ⟩, ⟨A⟩, ⟨L⟩]`: the list of `Φ`, the list of the anchors `A`, and the orbit list `L` of
the pair `[u, v]` (`tupOrb_spec`, with group elements). The membership tests are `any` loops:
`itCfEqP` compares a number with an entry, `itCfPairP` compares the pair `[a, b]` with the points
of an entry of `L`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab encKColoring)

variable {q : ℕ}

/-! ### The tests -/

/-- On `[w, x]`: whether the number `x` is `w`. -/
def itCfEqP : Expr := .arith .eq (arg 1) (arg 0)

/-- On `[[a, b], x]` with `x = [[y₀, y₁], g]`: whether `y₀ = a` and `y₁ = b`. -/
def itCfPairP : Expr :=
  .arith .mul (.arith .eq (.get (.get (arg 1) (.nat 0)) (.nat 0)) (.get (arg 0) (.nat 0)))
    (.arith .eq (.get (.get (arg 1) (.nat 0)) (.nat 1)) (.get (arg 0) (.nat 1)))

theorem itCf_toNat_le (b : Bool) : b.toNat ≤ 1 := by cases b <;> simp

/-- The test of `itCfEqP` as a function of the entry. -/
def itCfIsN (w : ℕ) : Val → Bool
  | .nat x => decide (x = w)
  | _ => false

theorem itCf_eqP_spec {P : Program} {pe : ℕ} (hpe : P.funs[pe]? = some itCfEqP) (w x : ℕ) :
    FunDet P pe (.list [.nat w, .nat x]) (boolVal (itCfIsN w (.nat x)))
      (4 * (Val.list [.nat w, .nat x]).wt + 20) := by
  have hz : GI.Machine.BinOp.eval .eq x w = (itCfIsN w (.nat x)).toNat := by
    by_cases h : x = w <;> simp [h, itCfIsN, GI.Machine.BinOp.eval]
  refine FunDet.intro hpe ((Det.arith' (op := .eq)
    (Det.arg' (P := P) (vs := [.nat w, .nat x]) (rest := []) (j := 1) rfl)
    (Det.arg' (P := P) (vs := [.nat w, .nat x]) (rest := []) (j := 0) rfl) hz).mono ?_)
  have := itCf_toNat_le (itCfIsN w (.nat x))
  omega

/-- The test of `itCfPairP` as a function of the entry. -/
def itCfIsP (a b : ℕ) : Val → Bool
  | .list [.list [.nat y0, .nat y1], _] => decide (y0 = a) && decide (y1 = b)
  | _ => false

theorem itCf_pairP_spec {P : Program} {pp : ℕ} (hpp : P.funs[pp]? = some itCfPairP)
    (a b y0 y1 : ℕ) (r : Val) :
    FunDet P pp (.list [.list [.nat a, .nat b], .list [.list [.nat y0, .nat y1], r]])
      (boolVal (itCfIsP a b (.list [.list [.nat y0, .nat y1], r])))
      (40 * (Val.list [.list [.nat a, .nat b], .list [.list [.nat y0, .nat y1], r]]).wt + 200) := by
  set vs : List Val := [.list [.nat a, .nat b], .list [.list [.nat y0, .nat y1], r]] with hvs
  set W := (Val.list vs).wt with hW
  have h1 : (Val.list [.nat a, .nat b]).wt < W := wt_le_wt_list (by simp [hvs])
  have h2 : (Val.list [.list [.nat y0, .nat y1], r]).wt < W := wt_le_wt_list (by simp [hvs])
  have h3 : (Val.list [.nat y0, .nat y1]).wt < (Val.list [.list [.nat y0, .nat y1], r]).wt :=
    wt_le_wt_list (by simp)
  have ha : (Val.nat a).wt < (Val.list [.nat a, .nat b]).wt := wt_le_wt_list (by simp)
  have hb : (Val.nat b).wt < (Val.list [.nat a, .nat b]).wt := wt_le_wt_list (by simp)
  have hy0 : (Val.nat y0).wt < (Val.list [.nat y0, .nat y1]).wt := wt_le_wt_list (by simp)
  have hy1 : (Val.nat y1).wt < (Val.list [.nat y0, .nat y1]).wt := wt_le_wt_list (by simp)
  have dy : Det P [Val.list vs] (.get (arg 1) (.nat 0)) (.list [.nat y0, .nat y1]) _ :=
    Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl) (Det.nat 0) rfl
  have dab : Det P [Val.list vs] (arg 0) (.list [.nat a, .nat b]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have e0 := Det.arith' (op := .eq) (Det.get' dy (Det.nat 0) (v := .nat y0) rfl)
    (Det.get' dab (Det.nat 0) (v := .nat a) rfl) rfl
  have e1 := Det.arith' (op := .eq) (Det.get' dy (Det.nat 1) (v := .nat y1) rfl)
    (Det.get' dab (Det.nat 1) (v := .nat b) rfl) rfl
  have hz : GI.Machine.BinOp.eval .mul (GI.Machine.BinOp.eval .eq y0 a)
      (GI.Machine.BinOp.eval .eq y1 b) = (itCfIsP a b (.list [.list [.nat y0, .nat y1], r])).toNat := by
    by_cases h0 : y0 = a <;> by_cases h1 : y1 = b <;> simp [h0, h1, itCfIsP, GI.Machine.BinOp.eval]
  refine FunDet.intro hpp ((Det.arith' (op := .mul) e0 e1 hz).mono ?_)
  have := itCf_toNat_le (itCfIsP a b (.list [.list [.nat y0, .nat y1], r]))
  have h01 : GI.Machine.BinOp.eval .eq y0 a ≤ 1 := by
    simp only [GI.Machine.BinOp.eval]; split <;> omega
  have h11 : GI.Machine.BinOp.eval .eq y1 b ≤ 1 := by
    simp only [GI.Machine.BinOp.eval]; split <;> omega
  omega

theorem itCf_any_nat (w : ℕ) (ys : List ℕ) :
    (ys.map Val.nat).any (itCfIsN w) = decide (w ∈ ys) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.any_cons, ih, itCfIsN, List.mem_cons]
    by_cases h : y = w
    · subst h; simp
    · simp [h, Ne.symm h]

theorem itCf_any_pair (L : List (List (Fin q) × Perm (Fin q))) (hL : ∀ p ∈ L, p.1.length = 2)
    (a b : Fin q) :
    (L.map (GI.Lang.encPair ptsKey)).any (itCfIsP a b) = decide ([a, b] ∈ L.map Prod.fst) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have ih' := ih fun p' hp' => hL p' (List.mem_cons_of_mem _ hp')
    obtain ⟨y0, y1, hy⟩ := List.length_eq_two.1 (hL p (List.mem_cons_self ..))
    obtain ⟨y, g⟩ := p
    simp only at hy
    subst hy
    simp only [List.map_cons, List.any_cons, ih', List.mem_cons]
    have e : GI.Lang.encPair ptsKey ([y0, y1], g) = .list [.list [.nat y0, .nat y1], encPerm g] := rfl
    rw [e]
    show (decide (y0.val = a.val) && decide (y1.val = b.val) || _) = _
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.val_inj,
      List.cons.injEq, and_true]
    constructor
    · rintro (⟨rfl, rfl⟩ | h) <;> simp_all
    · rintro (⟨rfl, rfl⟩ | h) <;> simp_all

/-- The cost bound of one membership test, on an argument of weight `Z`. -/
def itCfMemC (Z : ℕ) : ℕ := 10000 * (Z + 1) ^ 2

theorem itCf_any_cost {len Z C cost : ℕ} (hlen : len < Z)
    (h : cost ≤ len * (C * Z + C) + loopModK * (len + 1) * (Z + len + 4)) (hC : C ≤ 200) :
    cost ≤ 6000 * (Z + 1) ^ 2 := by
  have h1 : len * (C * Z + C) ≤ Z * (200 * Z + 200) :=
    Nat.mul_le_mul hlen.le (by nlinarith)
  have h2 : loopModK * (len + 1) * (Z + len + 4) ≤ 1000 * (Z + 1) * (2 * Z + 4) := by
    simp only [loopModK]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  nlinarith

/-- **Membership of a number in a list of numbers**, by `any itCfEqP`. -/
theorem itCf_mem_det {P : Program} {an pe : ℕ} (han : P.HasAt an (anyFuns an pe))
    (hpe : P.funs[pe]? = some itCfEqP) {env : List Val} {x l : Expr} {w : ℕ} (ys : List ℕ)
    {cx cl : ℕ} (hx : Det P env x (.nat w) cx) (hl : Det P env l (natList ys) cl) :
    Det P env (.call an (mk2 x l)) (boolVal (decide (w ∈ ys)))
      (cx + cl + itCfMemC (Val.list [.nat w, natList ys]).wt) := by
  set Z := (Val.list [.nat w, natList ys]).wt with hZ
  have hwZ : (Val.nat w).wt < Z := wt_le_wt_list (by simp)
  have hlZ : (natList ys).wt < Z := wt_le_wt_list (by simp)
  have hA := any_spec han (c := .nat w) (xs := ys.map Val.nat) (q := itCfIsN w)
    (B := fun _ => 40 * Z + 40) (fun y hy => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
      have hxl : (Val.nat x).wt < (natList ys).wt := wt_le_wt_list hy
      have := wt_list2_le (.nat w) (.nat x)
      exact (itCf_eqP_spec hpe w x).mono (by beta_reduce; omega))
  rw [itCf_any_nat] at hA
  have hlen : (ys.map Val.nat).length < Z := by
    have := length_lt_wt_list (ys.map Val.nat)
    change _ < (natList ys).wt at this
    omega
  have dc := Det.call (Det.mk2 hx hl) (cb := 6000 * (Z + 1) ^ 2) (hA.mono fun w' c hw => by
    refine ⟨hw.1, itCf_any_cost (C := 40) hlen ?_ (by norm_num)⟩
    have h2 := hw.2
    rw [List.map_const', List.sum_replicate, smul_eq_mul] at h2
    exact h2)
  refine dc.mono ?_
  have := wt_boolVal_le (decide (w ∈ ys))
  unfold itCfMemC
  nlinarith

/-- **Membership of a pair in the orbit list**, by `any itCfPairP`. -/
theorem itCf_pmem_det {P : Program} {an pp : ℕ} (han : P.HasAt an (anyFuns an pp))
    (hpp : P.funs[pp]? = some itCfPairP) {env : List Val} {x l : Expr} (a b : Fin q)
    (L : List (List (Fin q) × Perm (Fin q))) (hL : ∀ p ∈ L, p.1.length = 2)
    {cx cl : ℕ} (hx : Det P env x (.list [.nat a, .nat b]) cx)
    (hl : Det P env l (encPairs ptsKey L) cl) :
    Det P env (.call an (mk2 x l)) (boolVal (decide ([a, b] ∈ L.map Prod.fst)))
      (cx + cl + itCfMemC (Val.list [.list [.nat a, .nat b], encPairs ptsKey L]).wt) := by
  set Z := (Val.list [.list [.nat a, .nat b], encPairs ptsKey L]).wt with hZ
  have hlZ : (encPairs ptsKey L).wt < Z := wt_le_wt_list (by simp)
  have habZ : (Val.list [.nat a.val, .nat b.val]).wt < Z := wt_le_wt_list (by simp)
  have hA := any_spec han (c := .list [.nat a, .nat b]) (xs := L.map (GI.Lang.encPair ptsKey))
    (q := itCfIsP a b) (B := fun _ => 200 * Z + 200) (fun y hy => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
      have hxl : (GI.Lang.encPair ptsKey p).wt < (encPairs ptsKey L).wt := wt_le_wt_list hy
      obtain ⟨y0, y1, hy⟩ := List.length_eq_two.1 (hL p hp)
      obtain ⟨y, g⟩ := p
      simp only at hy
      subst hy
      have e : GI.Lang.encPair ptsKey ([y0, y1], g) =
        .list [.list [.nat y0, .nat y1], encPerm g] := rfl
      rw [e] at hxl ⊢
      have := wt_list2_le (.list [.nat a, .nat b]) (.list [.list [.nat y0, .nat y1], encPerm g])
      exact (itCf_pairP_spec hpp a b y0 y1 (encPerm g)).mono (by beta_reduce; omega))
  rw [itCf_any_pair L hL] at hA
  have hlen : (L.map (GI.Lang.encPair ptsKey)).length < Z := by
    have := length_lt_wt_list (L.map (GI.Lang.encPair ptsKey))
    change _ < (encPairs ptsKey L).wt at this
    omega
  have dc := Det.call (Det.mk2 hx hl) (cb := 6000 * (Z + 1) ^ 2) (hA.mono fun w' c hw => by
    refine ⟨hw.1, itCf_any_cost (C := 200) hlen ?_ (by norm_num)⟩
    have h2 := hw.2
    rw [List.map_const', List.sum_replicate, smul_eq_mul] at h2
    exact h2)
  refine dc.mono ?_
  have := wt_boolVal_le (decide ([a, b] ∈ L.map Prod.fst))
  unfold itCfMemC
  nlinarith

theorem itCf_find_nat (w : ℕ) (ys : List ℕ) :
    (ys.map Val.nat).findIdx (itCfIsN w) = ys.idxOf w := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    rw [List.map_cons, List.findIdx_cons, ih]
    by_cases h : y = w
    · subst h; simp [itCfIsN]
    · rw [List.idxOf_cons_ne _ h]; simp [itCfIsN, h]

theorem itCf_idxOf_val (a : Fin q) (l : List (Fin q)) : (l.map Fin.val).idxOf a.val = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    by_cases h : y = a
    · subst h; rw [List.map_cons, List.idxOf_cons_eq _ rfl, List.idxOf_cons_eq _ rfl]
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun e => h (Fin.ext e)), List.idxOf_cons_ne _ h, ih]

/-- **The first position of a number in a list of numbers**, by `find itCfEqP`. -/
theorem itCf_idx_det {P : Program} {fnd pe : ℕ} (hfnd : P.HasAt fnd (findFuns fnd pe))
    (hpe : P.funs[pe]? = some itCfEqP) {env : List Val} {x l : Expr} {w : ℕ} (ys : List ℕ)
    {cx cl : ℕ} (hx : Det P env x (.nat w) cx) (hl : Det P env l (natList ys) cl) :
    Det P env (.call fnd (mk2 x l)) (.nat (ys.idxOf w))
      (cx + cl + itCfMemC (Val.list [.nat w, natList ys]).wt) := by
  set Z := (Val.list [.nat w, natList ys]).wt with hZ
  have hwZ : (Val.nat w).wt < Z := wt_le_wt_list (by simp)
  have hlZ : (natList ys).wt < Z := wt_le_wt_list (by simp)
  have hF := find_spec hfnd (c := .nat w) (xs := ys.map Val.nat) (q := itCfIsN w)
    (B := fun _ => 40 * Z + 40) (fun y hy => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
      have hxl : (Val.nat x).wt < (natList ys).wt := wt_le_wt_list hy
      have := wt_list2_le (.nat w) (.nat x)
      exact (itCf_eqP_spec hpe w x).mono (by beta_reduce; omega))
  rw [itCf_find_nat] at hF
  have hlen : (ys.map Val.nat).length < Z := by
    have := length_lt_wt_list (ys.map Val.nat)
    change _ < (natList ys).wt at this
    omega
  have dc := Det.call (Det.mk2 hx hl) (cb := 6000 * (Z + 1) ^ 2) (hF.mono fun w' c hw => by
    refine ⟨hw.1, ?_⟩
    have h2 := hw.2
    rw [List.map_const', List.sum_replicate, smul_eq_mul] at h2
    have h3 : (Val.list [Val.nat w, Val.list (ys.map Val.nat)]).wt = Z := rfl
    rw [h3] at h2
    generalize (ys.map Val.nat).length = len at h2 hlen
    have h1 : len * (40 * Z + 40) ≤ Z * (40 * Z + 40) := Nat.mul_le_mul_right _ hlen.le
    have h4 : loopModK * (len + 1) * (Z + 2 * len + 3) ≤ 1000 * (Z + 1) * (3 * Z + 3) := by
      simp only [loopModK]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    nlinarith)
  refine dc.mono ?_
  have := wt_nat_le (ys.idxOf w)
  have : ys.idxOf w ≤ ys.length := List.idxOf_le_length
  have : ys.length < Z := by simpa using hlen
  unfold itCfMemC
  nlinarith

theorem itCfMemC_mono {a b : ℕ} (h : a ≤ b) : itCfMemC a ≤ itCfMemC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-! ### The cell -/

/-- Membership of the point `x` in `C = Φ \ A`, as `0` or `1`. -/
def itCfInC (an1 : ℕ) (x : Expr) : Expr :=
  .arith .mul (.call an1 (mk2 x (.get (arg 0) (.nat 1))))
    (.arith .sub (.nat 1) (.call an1 (mk2 x (.get (arg 0) (.nat 2)))))

/-- The colors `0, …, 7` of the cell: `4 [a ∈ C] + 2 [b ∈ C] + [(a, b) ∈ 𝒪]`. -/
def itCfCellOldF (an1 an2 : ℕ) : Expr :=
  .arith .add
    (.arith .add (.arith .mul (.nat 4) (itCfInC an1 (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))))
      (.arith .mul (.nat 2) (itCfInC an1 (.arith .div (arg 1) (.get (arg 0) (.nat 0))))))
    (.call an2 (mk2 (mk2 (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))
      (.arith .div (arg 1) (.get (arg 0) (.nat 0)))) (.get (arg 0) (.nat 3))))

/-- **The cell function**, on `[[q, ⟨Φ⟩, ⟨A⟩, ⟨L⟩], j]`: for a diagonal pair `(a, a)` with `a`
in the anchor list `A`, the anchor color `8 + i` with `i` the first position of `a` in `A`
(`find`); otherwise the colors `0, …, 7` (`itCfCellOldF`). -/
def itCfCellF (an1 an2 fnd : ℕ) : Expr :=
  .ite (.arith .mul (.arith .eq (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))
      (.arith .div (arg 1) (.get (arg 0) (.nat 0))))
      (.call an1 (mk2 (.arith .mod (arg 1) (.get (arg 0) (.nat 0))) (.get (arg 0) (.nat 2)))))
    (.arith .add (.nat 8)
      (.call fnd (mk2 (.arith .mod (arg 1) (.get (arg 0) (.nat 0))) (.get (arg 0) (.nat 2)))))
    (itCfCellOldF an1 an2)

/-- The context of the cell function. -/
def itCfCtx (q : ℕ) (xs As : List (Fin q)) (L : List (List (Fin q) × Perm (Fin q))) : Val :=
  .list [.nat q, natList (xs.map Fin.val), natList (As.map Fin.val), encPairs ptsKey L]

/-- The value of the cell of the pair `(a, b)`, before the anchor colors. -/
def itCfCellON (xs As : List (Fin q)) (L : List (List (Fin q) × Perm (Fin q))) (a b : Fin q) : ℕ :=
  4 * ((decide (a ∈ xs)).toNat * (1 - (decide (a ∈ As)).toNat)) +
    2 * ((decide (b ∈ xs)).toNat * (1 - (decide (b ∈ As)).toNat)) +
    (decide ([a, b] ∈ L.map Prod.fst)).toNat

/-- The value of the cell of the pair `(a, b)`. -/
def itCfCellN (xs As : List (Fin q)) (L : List (List (Fin q) × Perm (Fin q))) (a b : Fin q) : ℕ :=
  if a = b ∧ a ∈ As then 8 + As.idxOf a else itCfCellON xs As L a b

theorem itCf_decide_val (a : Fin q) (l : List (Fin q)) :
    decide (a.val ∈ l.map Fin.val) = decide (a ∈ l) := by
  simp only [List.mem_map, Fin.val_inj, exists_eq_right]

theorem itCfCellON_le (xs As : List (Fin q)) (L : List (List (Fin q) × Perm (Fin q)))
    (a b : Fin q) : itCfCellON xs As L a b ≤ 7 := by
  unfold itCfCellON
  cases decide (a ∈ xs) <;> cases decide (a ∈ As) <;> cases decide (b ∈ xs) <;>
    cases decide (b ∈ As) <;> cases decide ([a, b] ∈ L.map Prod.fst) <;> simp

theorem itCfCellN_le (xs As : List (Fin q)) (L : List (List (Fin q) × Perm (Fin q)))
    (a b : Fin q) : itCfCellN xs As L a b ≤ 7 + As.length := by
  unfold itCfCellN
  split_ifs with h
  · have := List.idxOf_lt_length_iff.2 h.2
    omega
  · have := itCfCellON_le xs As L a b
    omega

theorem itCf_cellN_eq (P1 P2 P3 P4 P5 : Prop) [Decidable P1] [Decidable P2] [Decidable P3]
    [Decidable P4] [Decidable P5] :
    4 * ((decide P1).toNat * (1 - (decide P2).toNat)) +
      2 * ((decide P3).toNat * (1 - (decide P4).toNat)) + (decide P5).toNat =
    (if P1 ∧ ¬ P2 then 4 else 0) + (if P3 ∧ ¬ P4 then 2 else 0) + (if P5 then 1 else 0) := by
  by_cases h1 : P1 <;> by_cases h2 : P2 <;> by_cases h3 : P3 <;> by_cases h4 : P4 <;>
    by_cases h5 : P5 <;> simp [h1, h2, h3, h4, h5]

/-- The cost bound of the cell function. -/
def itCfCellC (T : ℕ) : ℕ := 10 * itCfMemC (8 * T + 40) + 300 * T + 900

theorem itCf_inC_det {P : Program} {an1 pe : ℕ} (han : P.HasAt an1 (anyFuns an1 pe))
    (hpe : P.funs[pe]? = some itCfEqP) (xs As : List (Fin q)) (L : List (List (Fin q) × Perm (Fin q)))
    (j : ℕ) {x : Expr} {w cx : ℕ} (hw : w < q)
    (hx : Det P [.list [itCfCtx q xs As L, .nat j]] x (.nat w) cx) :
    Det P [.list [itCfCtx q xs As L, .nat j]] (itCfInC an1 x)
      (.nat ((decide (w ∈ xs.map Fin.val)).toNat * (1 - (decide (w ∈ As.map Fin.val)).toNat)))
      (2 * cx + 2 * itCfMemC (2 * ((Val.list [itCfCtx q xs As L, .nat j]).wt + q) + 10) +
        8 * (Val.list [itCfCtx q xs As L, .nat j]).wt + 60) := by
  set V := (Val.list [itCfCtx q xs As L, .nat j]).wt with hV
  have hcV : (itCfCtx q xs As L).wt < V := wt_le_wt_list (by simp)
  have dX : Det P [.list [itCfCtx q xs As L, .nat j]] (.get (arg 0) (.nat 1))
      (natList (xs.map Fin.val)) _ :=
    Det.get' (Det.arg' (P := P) (vs := [itCfCtx q xs As L, .nat j]) (rest := []) (j := 0) rfl)
      (Det.nat 1) rfl
  have dA : Det P [.list [itCfCtx q xs As L, .nat j]] (.get (arg 0) (.nat 2))
      (natList (As.map Fin.val)) _ :=
    Det.get' (Det.arg' (P := P) (vs := [itCfCtx q xs As L, .nat j]) (rest := []) (j := 0) rfl)
      (Det.nat 2) rfl
  have hXc : (natList (xs.map Fin.val)).wt < (itCfCtx q xs As L).wt := wt_le_wt_list (by simp)
  have hAc : (natList (As.map Fin.val)).wt < (itCfCtx q xs As L).wt := wt_le_wt_list (by simp)
  have m1 := itCf_mem_det han hpe _ hx dX
  have m2 := itCf_mem_det han hpe _ hx dA
  have z1 : (Val.list [.nat w, natList (xs.map Fin.val)]).wt ≤ 2 * (V + q) + 10 := by
    have := wt_list2_le (.nat w) (natList (xs.map Fin.val)); have := wt_nat_le w; omega
  have z2 : (Val.list [.nat w, natList (As.map Fin.val)]).wt ≤ 2 * (V + q) + 10 := by
    have := wt_list2_le (.nat w) (natList (As.map Fin.val)); have := wt_nat_le w; omega
  have k1 := itCfMemC_mono z1
  have k2 := itCfMemC_mono z2
  have dS := Det.arith' (op := .sub) (Det.nat (P := P) (env := [.list [itCfCtx q xs As L, .nat j]]) 1) m2 rfl
  refine (Det.arith' (op := .mul) m1 dS rfl).mono ?_
  have t1 := itCf_toNat_le (decide (w ∈ xs.map Fin.val))
  have t2 := itCf_toNat_le (decide (w ∈ As.map Fin.val))
  simp only [GI.Machine.BinOp.eval]
  have : (decide (w ∈ xs.map Fin.val)).toNat * (1 - (decide (w ∈ As.map Fin.val)).toNat) ≤ 1 :=
    (Nat.mul_le_mul t1 (show 1 - (decide (w ∈ As.map Fin.val)).toNat ≤ 1 by omega)).trans (by norm_num)
  omega

theorem itCfCellC_mono {a b : ℕ} (h : a ≤ b) : itCfCellC a ≤ itCfCellC b := by
  unfold itCfCellC
  have := itCfMemC_mono (show 8 * a + 40 ≤ 8 * b + 40 by omega)
  omega

/-- The colors `0, …, 7` of one cell. -/
theorem itCf_cellOld_det {P : Program} {an1 an2 pe pp : ℕ}
    (han1 : P.HasAt an1 (anyFuns an1 pe))
    (hpe : P.funs[pe]? = some itCfEqP) (han2 : P.HasAt an2 (anyFuns an2 pp))
    (hpp : P.funs[pp]? = some itCfPairP) (xs As : List (Fin q))
    (L : List (List (Fin q) × Perm (Fin q))) (hL : ∀ p ∈ L, p.1.length = 2) (j : ℕ)
    (hj : j < q * q) :
    Det P [.list [itCfCtx q xs As L, .nat j]] (itCfCellOldF an1 an2)
      (.nat (itCfCellON xs As L ⟨j % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hj))⟩
        ⟨j / q, Nat.div_lt_of_lt_mul hj⟩))
      (6 * itCfMemC (8 * ((Val.list [itCfCtx q xs As L, .nat j]).wt + q) + 40) +
        100 * ((Val.list [itCfCtx q xs As L, .nat j]).wt + q) + 300) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  set c := itCfCtx q xs As L with hc
  set V := (Val.list [c, .nat j]).wt with hV
  have hcV : c.wt < V := wt_le_wt_list (by simp)
  have hjV : (Val.nat j).wt < V := wt_le_wt_list (by simp)
  have hVb : V ≤ 2 * c.wt + 2 * (q * q) + 20 := by
    have := wt_list2_le c (.nat j); have := wt_nat_le j; omega
  have dq : Det P [.list [c, .nat j]] (.get (arg 0) (.nat 0)) (.nat q) _ :=
    Det.get' (Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) rfl) (Det.nat 0) rfl
  have dj : Det P [.list [c, .nat j]] (arg 1) (.nat j) _ :=
    Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) rfl
  have hqc : (Val.nat q).wt < c.wt := wt_le_wt_list (by simp)
  have d0 := Det.arith' (op := .mod) dj dq rfl
  have d1 := Det.arith' (op := .div) dj dq rfl
  have hm : j % q < q := Nat.mod_lt _ hq
  have hd : j / q < q := Nat.div_lt_of_lt_mul hj
  have i0 := itCf_inC_det han1 hpe xs As L j hm d0
  have i1 := itCf_inC_det han1 hpe xs As L j hd d1
  have e0 := Det.arith' (op := .mul) (Det.nat (P := P) (env := [.list [c, .nat j]]) 4) i0 rfl
  have e1 := Det.arith' (op := .mul) (Det.nat (P := P) (env := [.list [c, .nat j]]) 2) i1 rfl
  have dl : Det P [.list [c, .nat j]] (.get (arg 0) (.nat 3)) (encPairs ptsKey L) _ :=
    Det.get' (Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) rfl) (Det.nat 3) rfl
  have hLc : (encPairs ptsKey L).wt < c.wt := wt_le_wt_list (by simp)
  have dp := itCf_pmem_det han2 hpp ⟨j % q, hm⟩ ⟨j / q, hd⟩ L hL (Det.mk2 d0 d1) dl
  refine (Det.arith' (op := .add) (Det.arith' (op := .add) e0 e1 rfl) dp ?_).mono ?_
  · simp only [GI.Machine.BinOp.eval, itCfCellON, ← itCf_decide_val]
  · have z : (Val.list [.list [.nat (j % q), .nat (j / q)], encPairs ptsKey L]).wt ≤
        8 * (V + q) + 40 := by
      have := wt_list2_le (.list [.nat (j % q), .nat (j / q)]) (encPairs ptsKey L)
      have := wt_list2_le (.nat (j % q)) (.nat (j / q))
      have := wt_nat_le (j % q); have := wt_nat_le (j / q)
      omega
    have k := itCfMemC_mono z
    have w2 := wt_list2_le (.nat (j % q)) (.nat (j / q))
    have := wt_nat_le (j % q); have := wt_nat_le (j / q); have := wt_nat_le q
    have v1 := itCf_toNat_le (decide (j % q ∈ xs.map Fin.val))
    have v2 := itCf_toNat_le (decide (j / q ∈ xs.map Fin.val))
    have v3 := itCf_toNat_le (decide ([(⟨j % q, hm⟩ : Fin q), ⟨j / q, hd⟩] ∈ L.map Prod.fst))
    have u1 : (decide (j % q ∈ xs.map Fin.val)).toNat * (1 - (decide (j % q ∈ As.map Fin.val)).toNat) ≤ 1 :=
      (Nat.mul_le_mul v1 (show 1 - (decide (j % q ∈ As.map Fin.val)).toNat ≤ 1 by omega)).trans (by norm_num)
    have u2 : (decide (j / q ∈ xs.map Fin.val)).toNat * (1 - (decide (j / q ∈ As.map Fin.val)).toNat) ≤ 1 :=
      (Nat.mul_le_mul v2 (show 1 - (decide (j / q ∈ As.map Fin.val)).toNat ≤ 1 by omega)).trans (by norm_num)
    have k2 := itCfMemC_mono (show 2 * (V + q) + 10 ≤ 8 * (V + q) + 40 by omega)
    have hd1 : (Val.list [itCfCtx q xs As L, .nat j]).wt = V := rfl
    have hN := itCfCellON_le xs As L ⟨j % q, hm⟩ ⟨j / q, hd⟩
    simp only [GI.Machine.BinOp.eval]
    generalize itCfMemC (8 * (V + q) + 40) = M at *
    generalize itCfMemC (2 * (V + q) + 10) = M2 at *
    omega

/-- A product of two numbers at most `1`, with a cost free of the product. -/
theorem itCf_mul01_det {P : Program} {env : List Val} {a b : Expr} {x y ca cb : ℕ}
    (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb) (hx : x ≤ 1) (hy : y ≤ 1) :
    Det P env (.arith .mul a b) (.nat (x * y)) (ca + cb + 4) :=
  (Det.arith' (op := .mul) ha hb rfl).mono (by
    have := Nat.mul_le_mul hx hy
    simp only [GI.Machine.BinOp.eval]
    omega)

/-- **One cell of the table.** On `[c, j]` with `j < q²` the cell function returns the value of
the pair `(j % q, j / q)`. -/
theorem itCf_cell_spec {P : Program} {fc an1 an2 fnd pe pp : ℕ}
    (hfc : P.funs[fc]? = some (itCfCellF an1 an2 fnd)) (han1 : P.HasAt an1 (anyFuns an1 pe))
    (hpe : P.funs[pe]? = some itCfEqP) (han2 : P.HasAt an2 (anyFuns an2 pp))
    (hpp : P.funs[pp]? = some itCfPairP) (hfnd : P.HasAt fnd (findFuns fnd pe))
    (xs As : List (Fin q))
    (L : List (List (Fin q) × Perm (Fin q))) (hL : ∀ p ∈ L, p.1.length = 2) (j : ℕ)
    (hj : j < q * q) :
    FunDet P fc (.list [itCfCtx q xs As L, .nat j])
      (.nat (itCfCellN xs As L ⟨j % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hj))⟩
        ⟨j / q, Nat.div_lt_of_lt_mul hj⟩))
      (itCfCellC (2 * (itCfCtx q xs As L).wt + 2 * (q * q) + q + 20)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  set c := itCfCtx q xs As L with hc
  set V := (Val.list [c, .nat j]).wt with hV
  have hcV : c.wt < V := wt_le_wt_list (by simp)
  have hjV : (Val.nat j).wt < V := wt_le_wt_list (by simp)
  have hVb : V ≤ 2 * c.wt + 2 * (q * q) + 20 := by
    have := wt_list2_le c (.nat j); have := wt_nat_le j; omega
  have dq : Det P [.list [c, .nat j]] (.get (arg 0) (.nat 0)) (.nat q) _ :=
    Det.get' (Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) rfl) (Det.nat 0) rfl
  have dj : Det P [.list [c, .nat j]] (arg 1) (.nat j) _ :=
    Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) rfl
  have hqc : (Val.nat q).wt < c.wt := wt_le_wt_list (by simp)
  have d0 := Det.arith' (op := .mod) dj dq rfl
  have d1 := Det.arith' (op := .div) dj dq rfl
  have hm : j % q < q := Nat.mod_lt _ hq
  have hd : j / q < q := Nat.div_lt_of_lt_mul hj
  have dA : Det P [.list [c, .nat j]] (.get (arg 0) (.nat 2)) (natList (As.map Fin.val)) _ :=
    Det.get' (Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) rfl) (Det.nat 2) rfl
  have hAc : (natList (As.map Fin.val)).wt < c.wt := wt_le_wt_list (by simp)
  have dE := Det.arith' (op := .eq) d0 d1 rfl
  have dM := itCf_mem_det han1 hpe (As.map Fin.val) d0 dA
  have dC := itCf_mul01_det dE dM (by simp only [GI.Machine.BinOp.eval]; split <;> omega)
    (itCf_toNat_le _)
  have dI := itCf_idx_det hfnd hpe (As.map Fin.val) d0 dA
  have dT := Det.arith' (op := .add) (Det.nat (P := P) (env := [.list [c, .nat j]]) 8) dI rfl
  have dO := itCf_cellOld_det han1 hpe han2 hpp xs As L hL j hj
  have dI' := Det.ite' dC dT dO
  -- the value
  set a : Fin q := ⟨j % q, hm⟩ with ha
  set b : Fin q := ⟨j / q, hd⟩ with hb
  have key : ∀ {e : Expr} {v w : Val} {cst : ℕ}, Det P [.list [c, .nat j]] e v cst → v = w →
      Det P [.list [c, .nat j]] e w cst := fun h e => e ▸ h
  have e1 : (As.map Fin.val).idxOf (j % q) = As.idxOf a := itCf_idxOf_val a As
  have e2 : (j % q ∈ As.map Fin.val) ↔ a ∈ As := by
    rw [ha]; simp only [List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => by rwa [show x = ⟨j % q, hm⟩ from Fin.ext e] at hx,
      fun h => ⟨_, h, rfl⟩⟩
  have e3 : (j % q = j / q) ↔ a = b := by rw [ha, hb, Fin.mk.injEq]
  replace dI' := key dI' (w := .nat (itCfCellN xs As L a b)) (by
    simp only [GI.Machine.BinOp.eval]
    rw [e1]
    unfold itCfCellN
    by_cases h : a = b ∧ a ∈ As
    · have h1 : j % q = j / q := e3.2 h.1
      have hm' : j % q ∈ As.map Fin.val := e2.2 h.2
      rw [if_pos h, if_neg (by rw [if_pos h1, one_mul]; simp [hm'])]
    · rw [if_neg h, if_pos]
      by_cases h1 : a = b
      · have : a ∉ As := fun h2 => h ⟨h1, h2⟩
        simp [e2, this]
      · have : ¬ j % q = j / q := fun e => h1 (e3.1 e)
        simp [this])
  have hVV : (Val.list [itCfCtx q xs As L, .nat j]).wt = V := rfl
  rw [hVV] at dI'
  refine FunDet.intro hfc (dI'.mono ?_)
  -- the cost
  have hlen : As.length < c.wt := by
    have := length_lt_wt_list ((As.map Fin.val).map Val.nat)
    simp only [List.length_map] at this
    change _ < (natList (As.map Fin.val)).wt at this
    omega
  have z1 : (Val.list [.nat (j % q), natList (As.map Fin.val)]).wt ≤ 8 * (V + q) + 40 := by
    have := wt_list2_le (.nat (j % q)) (natList (As.map Fin.val)); have := wt_nat_le (j % q)
    omega
  have k1 := itCfMemC_mono z1
  have hmono := itCfCellC_mono (show V + q ≤ 2 * c.wt + 2 * (q * q) + q + 20 by omega)
  refine le_trans ?_ hmono
  clear hmono
  have wI := wt_nat_le (8 + (As.map Fin.val).idxOf (j % q))
  have hmax : max (Val.nat (8 + (As.map Fin.val).idxOf (j % q))).wt
      (Val.nat (itCfCellON xs As L a b)).wt ≤ (As.map Fin.val).idxOf (j % q) + 20 := by
    have := wt_nat_le (itCfCellON xs As L a b)
    have := itCfCellON_le xs As L a b
    omega
  have hN := itCfCellN_le xs As L a b
  have hON := itCfCellON_le xs As L a b
  have hix : (As.map Fin.val).idxOf (j % q) ≤ As.length := by
    have := List.idxOf_le_length (a := j % q) (l := As.map Fin.val)
    simpa using this
  have t1 := itCf_toNat_le (decide (j % q ∈ As.map Fin.val))
  have wN := wt_nat_le (itCfCellN xs As L a b)
  have wO := wt_nat_le (itCfCellON xs As L a b)
  have wq := wt_nat_le q; have wm := wt_nat_le (j % q); have wd := wt_nat_le (j / q)
  have hjq : j % q ≤ j := Nat.mod_le _ _
  have hjq' : j / q ≤ j := Nat.div_le_self _ _
  have wj := wt_nat_le j
  simp only [GI.Machine.BinOp.eval]
  unfold itCfCellC
  generalize itCfMemC (8 * (V + q) + 40) = M at *
  generalize itCfMemC (Val.list [.nat (j % q), natList (As.map Fin.val)]).wt = M1 at *
  split_ifs <;> omega

/-! ### The table is the orbital coloring -/

theorem itCf_symm_zero' (j : Fin (q ^ 2)) (h : j.val % q < q) :
    (finFunctionFinEquiv.symm j) 0 = ⟨j.val % q, h⟩ := Fin.ext (itCf_symm_zero j)

theorem itCf_symm_one' (j : Fin (q ^ 2)) (h : j.val / q < q) :
    (finFunctionFinEquiv.symm j) 1 = ⟨j.val / q, h⟩ := Fin.ext (itCf_symm_one j)

theorem itCf_lt_sq {j : ℕ} (hj : j < q ^ 2) : j < q * q := by rw [← sq]; exact hj

/-- **The table of the cells is the orbital coloring.** Here `d` is the degree, `xs` lists
`domSet H`, `⟨gs⟩` is the pointwise stabilizer of the anchors, and `L` lists the orbit of
`[t_{d-1}, t_d]` under `⟨1 :: gs⟩`. -/
theorem itCf_table_eq {ℓ : ℕ} (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q)
    (hd : transDeg (gens hs) (domSet (gens hs)) < ℓ) (xs : List (Fin q))
    (hxs : ∀ b, b ∈ xs ↔ b ∈ domSet (gens hs)) (gs : List (Perm (Fin q)))
    (hgs : gens gs = pointwiseStab (gens hs) (itCfAnc t (transDeg (gens hs) (domSet (gens hs)))))
    (L : List (List (Fin q) × Perm (Fin q)))
    (hL : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit (fun g (xs : List (Fin q)) => xs.map g) (1 :: gs)
      [t ⟨transDeg (gens hs) (domSet (gens hs)) - 1, by omega⟩,
        t ⟨transDeg (gens hs) (domSet (gens hs)), hd⟩]) :
    Val.list ((List.finRange (q ^ 2)).map fun j =>
      .nat (itCfCellN xs (itCfAnc t (transDeg (gens hs) (domSet (gens hs)))) L
        ⟨j.val % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at j; exact j.elim0))⟩
        ⟨j.val / q, Nat.div_lt_of_lt_mul (itCf_lt_sq j.isLt)⟩)) =
      encKColoring (orbColOut (gens hs) t) := by
  classical
  unfold encKColoring orbColOut orbColAt
  rw [dif_pos hd]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact absurd j.isLt (by simp))
  have h0 := itCf_symm_zero' j (Nat.mod_lt _ hq)
  have h1 := itCf_symm_one' j (Nat.div_lt_of_lt_mul (itCf_lt_sq j.isLt))
  congr 1
  unfold orbCol itCfCellN
  rw [h0, h1]
  have eA : itCfAnc t (transDeg (gens hs) (domSet (gens hs))) =
      ancList t (transDeg (gens hs) (domSet (gens hs))) := rfl
  by_cases hc : (⟨j.val % q, Nat.mod_lt _ hq⟩ : Fin q) = ⟨j.val / q,
      Nat.div_lt_of_lt_mul (itCf_lt_sq j.isLt)⟩ ∧
      (⟨j.val % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ ancList t (transDeg (gens hs) (domSet (gens hs)))
  · rw [eA, if_pos hc, if_pos hc]
  rw [eA, if_neg hc, if_neg hc, ← eA]
  unfold itCfCellON
  have hA := itCf_mem_anc t (transDeg (gens hs) (domSet (gens hs)))
  have hO := fun a b => itCf_orb_iff (gens hs) _ _ hA gs hgs
    (t ⟨transDeg (gens hs) (domSet (gens hs)) - 1, by omega⟩)
    (t ⟨transDeg (gens hs) (domSet (gens hs)), hd⟩) a b
  rw [itCf_cellN_eq]
  simp only [Finset.mem_sdiff, ← hxs, ← hA, hO, ← hL]

end GI.Impl
