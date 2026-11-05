module

public import Workspace.Impl.AggStructDesMath
public import Workspace.Impl.AggStructDC
public import Workspace.Lang.Lib.Loop

@[expose] public section

/-!
# The Case 3 test as a program: the colors of padded tuples

The program of the Case 3 test (`stDesB`, `AggStructDesMath.lean`) works in the context
`A = [dl, tl, q, κ]` (`stDA`): the list of the refined colors, the entries of the tuple, the
number of labels and the arity. Every color it needs is `c(x, z₁, z₂, …, z₂)` with `x` the first
`m` entries of the tuple, which is `stDCol`. This file computes it.

* `stDHor_spec`: a loop module computes the index of the tuple by Horner's rule (`stDHor`).
* `stDCol_spec`: one lookup in `dl` at that index.

The facts about the context the programs use are `StDCtx`: `dl` has `q^κ` entries, the
entries of the tuple are labels, the tuple has more than `κ` entries, and the colors are below
`2 q^κ` (the bound of the refinement task's output, `KaryOut`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- The context of the test: `[dl, tl, q, κ]`. -/
def stDA (dl tl : List ℕ) (q κ : ℕ) : Val := .list [natList dl, natList tl, .nat q, .nat κ]

/-- The facts about the context that the programs use. -/
structure StDCtx (dl tl : List ℕ) (q κ : ℕ) : Prop where
  len_dl : dl.length = q ^ κ
  tl_lt : ∀ x ∈ tl, x < q
  len_tl : κ < tl.length
  q_pos : 0 < q
  κ_pos : 0 < κ
  dl_lt : ∀ x ∈ dl, x < 2 * q ^ κ

theorem stDE_lt {tl : List ℕ} {q m z₁ z₂ : ℕ} (htl : ∀ x ∈ tl, x < q) (hq : 0 < q)
    (h₁ : z₁ < q) (h₂ : z₂ < q) (i : ℕ) : stDE tl m z₁ z₂ i < q := by
  unfold stDE
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    cases h : tl[i]? with
    | none => simpa using hq
    | some x => exact htl x (List.mem_of_getElem? h)
  · exact h₁
  · exact h₂

theorem stDHor_lt {q κ : ℕ} {e : ℕ → ℕ} (he : ∀ i, e i < q) :
    ∀ i, stDHor q κ e i < q ^ i
  | 0 => by simp [stDHor]
  | i + 1 => by
    have ih := stDHor_lt (κ := κ) he i
    have h1 := he (κ - 1 - i)
    rw [stDHor, pow_succ]
    have : stDHor q κ e i * q + q ≤ q ^ i * q := by
      have := Nat.mul_le_mul_right q (show stDHor q κ e i + 1 ≤ q ^ i by omega)
      rw [Nat.add_mul, one_mul] at this
      exact this
    omega

theorem stDHor_le_pow {q κ : ℕ} {e : ℕ → ℕ} (he : ∀ i, e i < q) (hq : 0 < q) {i : ℕ}
    (hi : i ≤ κ) : stDHor q κ e i < q ^ κ :=
  (stDHor_lt he i).trans_le (Nat.pow_le_pow_right hq hi)

/-! ### The weight of the context -/

theorem wt_stDA_ge {dl tl : List ℕ} {q κ : ℕ} :
    dl.length < (stDA dl tl q κ).wt ∧ tl.length < (stDA dl tl q κ).wt ∧
      (natList dl).wt < (stDA dl tl q κ).wt ∧ (natList tl).wt < (stDA dl tl q κ).wt ∧
      (Val.nat q).wt < (stDA dl tl q κ).wt ∧ (Val.nat κ).wt < (stDA dl tl q κ).wt := by
  have h1 : (natList dl).wt < (stDA dl tl q κ).wt := wt_le_wt_list (by simp)
  have h2 : (natList tl).wt < (stDA dl tl q κ).wt := wt_le_wt_list (by simp)
  have h3 : (Val.nat q).wt < (stDA dl tl q κ).wt := wt_le_wt_list (by simp)
  have h4 : (Val.nat κ).wt < (stDA dl tl q κ).wt := wt_le_wt_list (by simp)
  have h5 : dl.length < (natList dl).wt := by
    have := length_lt_wt_list (dl.map Val.nat); simpa [natList] using this
  have h6 : tl.length < (natList tl).wt := by
    have := length_lt_wt_list (tl.map Val.nat); simpa [natList] using this
  exact ⟨by omega, by omega, h1, h2, h3, h4⟩

/-- In a context with the facts, `q` and `κ` are below the weight. -/
theorem StDCtx.le_wt {dl tl : List ℕ} {q κ : ℕ} (h : StDCtx dl tl q κ) :
    q ^ κ < (stDA dl tl q κ).wt ∧ κ < (stDA dl tl q κ).wt ∧ q < (stDA dl tl q κ).wt := by
  obtain ⟨h1, h2, -, -, -, -⟩ := wt_stDA_ge (dl := dl) (tl := tl) (q := q) (κ := κ)
  have hκ := h.len_tl
  have hq := h.q_pos
  have hqk : q ≤ q ^ κ := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ κ := Nat.pow_le_pow_right hq h.κ_pos
  rw [h.len_dl] at h1
  exact ⟨h1, by omega, by omega⟩

/-! ### Horner's rule as a loop -/

/-- Inside the step (argument `[a, i, acc]`, `a = [A, m, z₁, z₂]`): entry `j` of `A`. -/
def stDAE (j : ℕ) : Expr := .get (.get (arg 0) (.nat 0)) (.nat j)
/-- Inside the step: entry `j` of `a`. -/
def stDXE (j : ℕ) : Expr := .get (arg 0) (.nat j)
/-- The position `κ - 1 - i` of step `i`. -/
def stDIE : Expr := .arith .sub (.arith .sub (stDAE 3) (.nat 1)) (arg 1)
/-- The entry `stDE tl m z₁ z₂ (κ - 1 - i)`. -/
def stDEE : Expr :=
  .ite (.arith .lt stDIE (stDXE 1)) (.get (stDAE 1) stDIE)
    (.ite (.arith .eq stDIE (stDXE 1)) (stDXE 2) (stDXE 3))
/-- The step of Horner's rule: `acc * q + e`. -/
def stDHorStep : Expr := .arith .add (.arith .mul (arg 2) (stDAE 2)) stDEE

/-- **Horner's rule**, at base `b` (three functions): on `[A, m, z₁, z₂]`, the index of the
tuple `(x, z₁, z₂, …, z₂)`. -/
def stDHorFuns (b : ℕ) : List Expr :=
  loopFuns b (.get (.get (.var 0) (.nat 0)) (.nat 3)) (.nat 0) stDHorStep

/-- The argument `[A, m, z₁, z₂]`. -/
def stDCA (dl tl : List ℕ) (q κ m z₁ z₂ : ℕ) : Val :=
  .list [stDA dl tl q κ, .nat m, .nat z₁, .nat z₂]

theorem wt_stDCA_gt {dl tl : List ℕ} {q κ m z₁ z₂ : ℕ} :
    (stDA dl tl q κ).wt < (stDCA dl tl q κ m z₁ z₂).wt ∧
      (Val.nat m).wt < (stDCA dl tl q κ m z₁ z₂).wt ∧
      (Val.nat z₁).wt < (stDCA dl tl q κ m z₁ z₂).wt ∧
      (Val.nat z₂).wt < (stDCA dl tl q κ m z₁ z₂).wt :=
  ⟨wt_le_wt_list (by simp), wt_le_wt_list (by simp),
    wt_le_wt_list (by simp), wt_le_wt_list (by simp)⟩

/-- The cost constant of Horner's rule. -/
def stDHorK : ℕ := 10 ^ 6

theorem stDHor_spec {P : Program} {b : ℕ} (hb : P.HasAt b (stDHorFuns b)) {dl tl : List ℕ}
    {q κ : ℕ} (hc : StDCtx dl tl q κ) (m : ℕ) {z₁ z₂ : ℕ} (h₁ : z₁ < q) (h₂ : z₂ < q) :
    FunDet P b (stDCA dl tl q κ m z₁ z₂) (.nat (stDHor q κ (stDE tl m z₁ z₂) κ))
      (stDHorK * ((stDCA dl tl q κ m z₁ z₂).wt + 1) ^ 2) := by
  have he_lt : ∀ i, stDE tl m z₁ z₂ i < q := stDE_lt hc.tl_lt hc.q_pos h₁ h₂
  obtain ⟨hAa, hma, h1a, h2a⟩ := wt_stDCA_gt (dl := dl) (tl := tl) (q := q) (κ := κ) (m := m)
    (z₁ := z₁) (z₂ := z₂)
  obtain ⟨-, htlA, -, htlwA, hqA, hκA⟩ := wt_stDA_ge (dl := dl) (tl := tl) (q := q) (κ := κ)
  obtain ⟨hpowA, hκA', hqA'⟩ := hc.le_wt
  have hlen := hc.len_tl
  obtain ⟨M, hM⟩ : ∃ M, (stDCA dl tl q κ m z₁ z₂).wt = M := ⟨_, rfl⟩
  have e2 : (Val.list [stDA dl tl q κ, Val.nat m, Val.nat z₁, Val.nat z₂]).wt = M := hM
  have e3 : (Val.list [natList dl, natList tl, Val.nat q, Val.nat κ]).wt =
    (stDA dl tl q κ).wt := rfl
  rw [hM] at hAa hma h1a h2a ⊢
  -- the loop
  have hk : Det P [stDCA dl tl q κ m z₁ z₂] (.get (.get (.var 0) (.nat 0)) (.nat 3)) (.nat κ)
      (3 * M + 20) := by
    refine (Det.get' (Det.get' (Det.var' (i := 0) rfl) (Det.nat 0)
      (show [stDA dl tl q κ, .nat m, .nat z₁, .nat z₂][0]? = some (stDA dl tl q κ) from rfl))
      (Det.nat 3)
      (show [natList dl, natList tl, .nat q, .nat κ][3]? = some (.nat κ) from rfl)).mono ?_
    have : (stDA dl tl q κ).wt = (Val.list [natList dl, natList tl, Val.nat q, Val.nat κ]).wt :=
      rfl
    omega
  have hacc : Det P [stDCA dl tl q κ m z₁ z₂] (.nat 0) (.nat 0) 3 := Det.nat 0
  have hacc_wt : ∀ i acc, i ≤ κ → acc = Val.nat (stDHor q κ (stDE tl m z₁ z₂) i) →
      acc.wt ≤ M := by
    rintro i acc hi rfl
    have := stDHor_le_pow he_lt hc.q_pos hi (κ := κ)
    have := wt_nat_le (stDHor q κ (stDE tl m z₁ z₂) i)
    omega
  obtain ⟨Wd, hWd⟩ : ∃ Wd, Wd = 7 * M + 20 := ⟨_, rfl⟩
  refine (loopBdd_spec hb hk hacc (by rw [hM]; omega) (M := M)
    (Inv := fun i acc => acc = .nat (stDHor q κ (stDE tl m z₁ z₂) i)) rfl hacc_wt
    (D := fun _ => 200 * (Wd + 1)) ?_).mono ?_
  · rintro i acc hi rfl
    obtain ⟨H, hHdef⟩ : ∃ H, stDHor q κ (stDE tl m z₁ z₂) i = H := ⟨_, rfl⟩
    have hH := stDHor_le_pow he_lt hc.q_pos (κ := κ) (le_of_lt hi)
    have hH1 := stDHor_le_pow he_lt hc.q_pos (κ := κ) (show i + 1 ≤ κ by omega)
    rw [hHdef] at hH ⊢
    have hHw := wt_nat_le H
    have hiw := wt_nat_le i
    have hvs : (Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]).wt ≤ Wd := by
      have := wt_list3_le (stDCA dl tl q κ m z₁ z₂) (.nat i) (.nat H); omega
    have hW4 : 4 ≤ Wd := by omega
    have g0 : StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]] (arg 0)
        (.list [stDA dl tl q κ, .nat m, .nat z₁, .nat z₂]) 3 0 Wd :=
      StDC.arg rfl hvs (by omega) (by omega)
    have gA : StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]] (.get (arg 0) (.nat 0))
        (.list [natList dl, natList tl, .nat q, .nat κ]) 5 0 Wd :=
      StDC.get g0 (StDC.nat 0 (by omega)) rfl (by omega)
    have gtl := StDC.get (v := natList tl) gA (StDC.nat 1 (by omega)) rfl (by omega)
    have gq := StDC.get (v := .nat q) gA (StDC.nat 2 (by omega)) rfl (by omega)
    have gκ := StDC.get (v := .nat κ) gA (StDC.nat 3 (by omega)) rfl (by omega)
    have gm := StDC.get (v := .nat m) g0 (StDC.nat 1 (by omega)) rfl (by omega)
    have gz₁ := StDC.get (v := .nat z₁) g0 (StDC.nat 2 (by omega)) rfl (by omega)
    have gz₂ := StDC.get (v := .nat z₂) g0 (StDC.nat 3 (by omega)) rfl (by omega)
    have gi : StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]] (arg 1) (.nat i) 3 0
        Wd := StDC.arg rfl hvs (by omega) (by omega)
    have gacc : StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]] (arg 2) (.nat H) 3 0
        Wd := StDC.arg rfl hvs (by omega) (by omega)
    obtain ⟨i', hi'⟩ : ∃ i', κ - 1 - i = i' := ⟨_, rfl⟩
    have gI := StDC.arith' (StDC.arith' gκ (StDC.nat 1 (by omega)) (op := .sub)
      (show BinOp.eval .sub κ 1 = κ - 1 from rfl) (by omega)) gi
      (op := .sub) (show BinOp.eval .sub (κ - 1) i = i' from hi') (by omega)
    have hi'tl : i' < tl.length := by omega
    obtain ⟨E, hE⟩ : ∃ E, stDE tl m z₁ z₂ i' = E := ⟨_, rfl⟩
    have hel : E < q := hE ▸ he_lt i'
    have hEw := wt_nat_le E
    have gC : StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]]
        (.arith .lt stDIE (stDXE 1)) (.nat (BinOp.eval .lt i' m)) 19 0 Wd :=
      StDC.arith' gI gm rfl (by simp only [BinOp.eval]; split_ifs <;> omega)
    have gC2 : StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]]
        (.arith .eq stDIE (stDXE 1)) (.nat (BinOp.eval .eq i' m)) 19 0 Wd :=
      StDC.arith' gI gm rfl (by simp only [BinOp.eval]; split_ifs <;> omega)
    have gT : BinOp.eval .lt i' m ≠ 0 → StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]]
        (.get (stDAE 1) stDIE) (.nat E) 21 0 Wd := by
      intro hx
      have hlt : i' < m := by by_contra h; simp [BinOp.eval, h] at hx
      refine StDC.get gtl gI (v := .nat E) ?_ (by omega)
      rw [← hE]
      simp only [natList, List.getElem?_map, stDE, if_pos hlt,
        List.getElem?_eq_getElem hi'tl, Option.map_some, List.getD_eq_getElem _ _ hi'tl]
    have gF : BinOp.eval .lt i' m = 0 → StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]]
        (.ite (.arith .eq stDIE (stDXE 1)) (stDXE 2) (stDXE 3)) (.nat E) 30 0 Wd := by
      intro hx
      have hlt : ¬ i' < m := by intro h; simp [BinOp.eval, h] at hx
      refine StDC.ite (v := .nat E) (t := stDXE 2) (e := stDXE 3) (nt := 5) (ne := 5) (Et := 0) (Ee := 0) gC2 (fun hy => ?_) (fun hy => ?_) (by omega)
      · have heq : i' = m := by by_contra h; simp [BinOp.eval, h] at hy
        have : E = z₁ := by rw [← hE]; simp [stDE, hlt, heq]
        rw [this]; exact gz₁
      · have heq : ¬ i' = m := by intro h; simp [BinOp.eval, h] at hy
        have : E = z₂ := by rw [← hE]; simp [stDE, hlt, heq]
        rw [this]; exact gz₂
    have gE : StDC P [Val.list [stDCA dl tl q κ m z₁ z₂, .nat i, .nat H]] stDEE (.nat E) 71 0
        Wd := StDC.ite gC gT gF (by omega)
    have hval : H * q + E = stDHor q κ (stDE tl m z₁ z₂) (i + 1) := by
      rw [stDHor, hHdef, hi', hE]
    have hHq : H * q ≤ stDHor q κ (stDE tl m z₁ z₂) (i + 1) := by omega
    have gS := StDC.arith' (StDC.arith' gacc gq (op := .mul)
      (show BinOp.eval .mul H q = H * q from rfl) (by omega)) gE (op := .add)
      (show BinOp.eval .add (H * q) E = _ from hval) (by omega)
    refine gS.det.post fun c hc => ⟨rfl, ?_⟩
    beta_reduce
    omega
  · rintro w c ⟨hw, hcost⟩
    refine ⟨hw, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcost
    rw [hM] at hcost
    have h1 : κ * (200 * (Wd + 1)) ≤ (M + 1) * (4200 * (M + 1)) := by
      have : 200 * (Wd + 1) ≤ 4200 * (M + 1) := by omega
      exact Nat.mul_le_mul (by omega) this
    have h2 : loopModK * (κ + 1) * (M + κ + M + 1) ≤ 1000 * (M + 1) * (3 * (M + 1)) := by
      unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e1 : (M + 1) ^ 2 = (M + 1) * (M + 1) := by ring
    have e2 : (M + 1) * (4200 * (M + 1)) = 4200 * ((M + 1) * (M + 1)) := by ring
    have e3 : 1000 * (M + 1) * (3 * (M + 1)) = 3000 * ((M + 1) * (M + 1)) := by ring
    unfold stDHorK
    rw [e1]
    omega

/-! ### The color -/

/-- **The color of a padded tuple**: on `[A, m, z₁, z₂]`, the entry of `dl` at the index that
Horner's rule (at `h`) gives. -/
def stDColF (h : ℕ) : Expr := .get (.get (arg 0) (.nat 0)) (.call h (.var 0))

/-- The cost constant of the color. -/
def stDColK : ℕ := 2 * 10 ^ 6

theorem stDCol_spec {P : Program} {f h : ℕ} (hf : P.funs[f]? = some (stDColF h))
    (hh : P.HasAt h (stDHorFuns h)) {dl tl : List ℕ} {q κ : ℕ} (hc : StDCtx dl tl q κ) (m : ℕ)
    {z₁ z₂ : ℕ} (h₁ : z₁ < q) (h₂ : z₂ < q) :
    FunDet P f (stDCA dl tl q κ m z₁ z₂) (.nat (stDCol dl tl q κ m z₁ z₂))
      (stDColK * ((stDCA dl tl q κ m z₁ z₂).wt + 1) ^ 2) := by
  obtain ⟨hAa, -, -, -⟩ := wt_stDCA_gt (dl := dl) (tl := tl) (q := q) (κ := κ) (m := m)
    (z₁ := z₁) (z₂ := z₂)
  obtain ⟨hdA, -, hdwA, -, -, -⟩ := wt_stDA_ge (dl := dl) (tl := tl) (q := q) (κ := κ)
  obtain ⟨M, hM⟩ : ∃ M, (stDCA dl tl q κ m z₁ z₂).wt = M := ⟨_, rfl⟩
  have e2 : (Val.list [stDA dl tl q κ, Val.nat m, Val.nat z₁, Val.nat z₂]).wt = M := hM
  rw [hM] at hAa ⊢
  have he_lt : ∀ i, stDE tl m z₁ z₂ i < q := stDE_lt hc.tl_lt hc.q_pos h₁ h₂
  have hidx := stDHor_le_pow he_lt hc.q_pos (κ := κ) le_rfl
  rw [← hc.len_dl] at hidx
  obtain ⟨x, hx⟩ : ∃ x, dl[stDHor q κ (stDE tl m z₁ z₂) κ]? = some x :=
    ⟨_, List.getElem?_eq_getElem hidx⟩
  have hcol : stDCol dl tl q κ m z₁ z₂ = x := by
    unfold stDCol
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some]
  have hxw : (Val.nat x).wt < (natList dl).wt :=
    wt_le_wt_list (List.mem_map.2 ⟨x, List.mem_of_getElem? hx, rfl⟩)
  have hiw := wt_nat_le (stDHor q κ (stDE tl m z₁ z₂) κ)
  have hW : (Val.list [stDA dl tl q κ, Val.nat m, Val.nat z₁, Val.nat z₂]).wt ≤ M + 2 := by omega
  have g0 : StDC P [stDCA dl tl q κ m z₁ z₂] (arg 0) (stDA dl tl q κ) 3 0 (M + 2) :=
    StDC.arg rfl hW (by omega) (by omega)
  have gD : StDC P [stDCA dl tl q κ m z₁ z₂] (.get (arg 0) (.nat 0)) (natList dl) 5 0 (M + 2) :=
    StDC.get (vs := [natList dl, natList tl, .nat q, .nat κ]) g0 (StDC.nat 0 (by omega)) rfl
      (by omega)
  have gH := StDC.call (StDC.var' (P := P) (env := [stDCA dl tl q κ m z₁ z₂]) (i := 0) rfl
    (by omega : (stDCA dl tl q κ m z₁ z₂).wt ≤ M + 2)) (stDHor_spec hh hc m h₁ h₂)
    (by omega)
  have gC := StDC.get (v := .nat x) gD gH (by simp [natList, hx]) (by omega)
  rw [hcol]
  refine StDC.funDet hf gC ?_
  rw [hM]
  have e1 : (M + 1) ^ 2 = (M + 1) * (M + 1) := by ring
  rw [e1]
  have : 8 * (M + 2 + 1) ≤ 24 * ((M + 1) * (M + 1)) := by nlinarith
  unfold stDColK stDHorK
  omega

end GI.Impl
