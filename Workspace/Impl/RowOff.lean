module

public import Workspace.Impl.RowA18Link
public import Workspace.Lang.Lib.SmallGroup

@[expose] public section

/-!
# The positions of the domain outside row `0`, in `GI.Lang`

`N*` is the row-`0` image of the elements of `G` that fix every point of the domain outside
row `0` (`Nstar_gens`). With the row labels `rl` of the positions (`RowLabs`: the label on the
domain, `q` off it), these are the positions `i` with `0 < rl[i] < q` (`offPts`). The program is a
filter over `0, …, n - 1` (`offList_spec`); `mem_offPts` gives the form that `Nstar_gens` asks.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPts)

/-- Whether `0 < rl[i] < q`. -/
def offP (rl : List ℕ) (q i : ℕ) : Bool := decide (0 < rl.getD i 0 ∧ rl.getD i 0 < q)

/-- On `[[rl, q], i]`: `offP rl q i`. -/
def offTestF : Expr :=
  .letE (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.ite (.var 1) (.arith .lt (.var 1) (.get (arg 0) (.nat 1))) (.nat 0))

/-- The cost constant of the test. -/
def offK : ℕ := 1000

theorem offTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some offTestF) (rl : List ℕ)
    (q i : ℕ) (hi : i < rl.length) (hrl : ∀ r ∈ rl, r ≤ q) :
    FunDet P f (.list [.list [natList rl, .nat q], .nat i]) (boolVal (offP rl q i))
      (offK * ((Val.list [.list [natList rl, .nat q], .nat i]).wt + q + 1)) := by
  set c := Val.list [natList rl, .nat q]
  set inp := Val.list [c, .nat i]
  set r := rl.getD i 0 with hr
  have hrq : r ≤ q := hrl r (by rw [hr, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have g0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) rfl
  have dl := Det.get' g0 (Det.nat 0) (vs := [natList rl, .nat q]) (v := natList rl) rfl
  have dr := Det.get' dl g1 (vs := rl.map Val.nat) (v := .nat r) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi, hr, List.getD_eq_getElem _ _ hi]; rfl)
  have h0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := [.nat r]) (j := 0) rfl
  have hq := Det.get' h0 (Det.nat 1) (vs := [natList rl, .nat q]) (v := .nat q) rfl
  have hv1 := Det.var' (P := P) (env := [inp, .nat r]) (i := 1) (v := .nat r) rfl
  have w1 := wt_list2_le c (.nat i)
  have w2 := wt_nat_le r
  have w4 := wt_boolVal_le (offP rl q i)
  have w5 : c.wt < inp.wt := wt_le_wt_list (by simp)
  have w6 : (natList rl).wt < c.wt := wt_le_wt_list (by simp)
  have w7 : (Val.nat q).wt < c.wt := wt_le_wt_list (by simp)
  have e8 : (Val.list (rl.map Val.nat)).wt = (natList rl).wt := rfl
  have e9 : (Val.list [c, Val.nat i]).wt = inp.wt := rfl
  by_cases h0r : r = 0
  · have dv := Det.var' (P := P) (env := [inp, .nat r]) (i := 1) (v := .nat 0) (by simp [h0r])
    have dite := Det.ite_zero (t := .arith .lt (.var 1) (.get (arg 0) (.nat 1))) dv
      (Det.nat (P := P) (env := [inp, .nat r]) 0)
    have hval : (Val.nat 0) = boolVal (offP rl q i) := by
      unfold offP; rw [← hr, h0r]; rfl
    rw [hval] at dite
    refine FunDet.intro hf ((Det.letE dr dite).mono ?_)
    unfold offK
    omega
  · have dlt := Det.arith' (op := .lt) hv1 hq (z := if r < q then 1 else 0) rfl
    have dite := Det.ite_pos (e := .nat 0) hv1 h0r dlt
    have hval : (Val.nat (if r < q then 1 else 0)) = boolVal (offP rl q i) := by
      unfold offP; rw [← hr]
      by_cases h : r < q <;> simp [h, boolVal, Nat.pos_of_ne_zero h0r]
    rw [hval] at dite
    refine FunDet.intro hf ((Det.letE dr dite).mono ?_)
    have hb : (if r < q then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have w3 := wt_nat_le q
    unfold offK
    omega

/-- The test on values. -/
def offQ (rl : List ℕ) (q : ℕ) : Val → Bool
  | .nat i => offP rl q i
  | .list _ => false

/-- The positions `i` with `0 < rl[i] < q`. -/
def offPts (n : ℕ) (rl : List ℕ) (q : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun i => offP rl q i

theorem natList_offPts (n : ℕ) (rl : List ℕ) (q : ℕ) :
    natList ((List.range n).filter (offP rl q)) = encPts (offPts n rl q) := by
  unfold natList encPts offPts
  congr 1
  rw [← List.map_coe_finRange_eq_range, List.filter_map, List.map_map]
  simp only [Function.comp_def]
  induction (List.filter (fun x : Fin n => offP rl q ↑x) (List.finRange n)) with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons] at ih ⊢; rw [ih]; rfl

/-- The constant of the filter. -/
def offFK : ℕ := 10 ^ 4

/-- **The positions outside row `0`**, by a filter over `0, …, n - 1`. -/
theorem offList_spec {P : Program} {b f : ℕ} (hb : P.HasAt b (filterFuns b f))
    (hf : P.funs[f]? = some offTestF) {n q : ℕ} (rl : List ℕ) (hl : rl.length = n)
    (hrl : ∀ r ∈ rl, r ≤ q) :
    FunDet P b (.list [.list [natList rl, .nat q], natList (List.range n)])
      (encPts (offPts n rl q))
      (offFK * ((Val.list [.list [natList rl, .nat q], natList (List.range n)]).wt + q + 1) ^ 2) := by
  set c := Val.list [natList rl, .nat q]
  set A := (Val.list [c, natList (List.range n)]).wt
  have hxs : natList (List.range n) = .list ((List.range n).map Val.nat) := rfl
  have hcA : c.wt < A := wt_le_wt_list (by simp)
  have hnA : n < A := by
    have := length_lt_wt_list ((List.range n).map Val.nat)
    have e : (Val.list ((List.range n).map Val.nat)).wt = (natList (List.range n)).wt := rfl
    have : (natList (List.range n)).wt < A := wt_le_wt_list (by simp)
    simp only [List.length_map, List.length_range] at *
    omega
  have hF := filter_spec hb (c := c) (xs := (List.range n).map Val.nat) (q := offQ rl q)
    (B := fun _ => offK * (2 * c.wt + 2 * A + q + 20)) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hin : i < rl.length := by rw [hl]; exact List.mem_range.mp hi
      refine (offTest_spec hf rl q i hin hrl).mono ?_
      have := wt_list2_le c (.nat i)
      have := wt_nat_le i
      have : i < n := List.mem_range.mp hi
      have e : (Val.list [Val.list [natList rl, .nat q], Val.nat i]).wt =
        (Val.list [c, Val.nat i]).wt := rfl
      unfold offK; omega)
  rw [← hxs] at hF
  refine hF.mono fun w cost ⟨hw, hc⟩ => ⟨?_, ?_⟩
  · rw [hw, ← natList_offPts, natList, List.filter_map]; rfl
  · rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map, List.length_range] at hc
    have hww : w.wt ≤ A := by
      rw [hw]
      have h1 := wt_list_sublist (List.filter_sublist (p := offQ rl q)
        (l := (List.range n).map Val.nat))
      have h2 : (natList (List.range n)).wt < A := wt_le_wt_list (by simp)
      have e : (Val.list ((List.range n).map Val.nat)).wt = (natList (List.range n)).wt := rfl
      omega
    have e : (Val.list [c, natList (List.range n)]).wt = A := rfl
    rw [e] at hc
    have h1 : n * (offK * (2 * c.wt + 2 * A + q + 20)) ≤ offK * (A * (4 * A + q + 20)) := by
      have : n * (2 * c.wt + 2 * A + q + 20) ≤ A * (4 * A + q + 20) :=
        Nat.mul_le_mul (by omega) (by omega)
      calc n * (offK * (2 * c.wt + 2 * A + q + 20)) = offK * (n * (2 * c.wt + 2 * A + q + 20)) := by
            ring
        _ ≤ _ := Nat.mul_le_mul_left _ this
    have h2 : loopModK * (n + 1) * (A + n + w.wt + 1) ≤ loopModK * (A + 1) * (4 * A + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h3 : offK * (A * (4 * A + q + 20)) + loopModK * (A + 1) * (4 * A + 1) ≤
        offFK * (A + q + 1) ^ 2 := by
      simp only [offK, offFK, loopModK]
      have : 0 ≤ A * q := Nat.zero_le _
      ring_nf; nlinarith [Nat.zero_le q, Nat.zero_le A]
    omega

/-- **The positions outside row `0`** are the positions of the domain whose coordinate row is
not `0`. -/
theorem mem_offPts {Ω C : Type} {n : ℕ} {e : Ω ≃ Fin n} {S : State Ω C} {L : GiantLabels S}
    {label : Ω → Fin L.q} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom)
    (hE : ∀ b i, label (E (b, i)) = i) {rl : List ℕ} (hrl : RowLabs e S label rl) (hq : 1 ≤ L.q)
    (i : Fin n) :
    i ∈ offPts n rl L.q ↔ ∃ h : e.symm i ∈ S.dom, (E.symm ⟨e.symm i, h⟩).2 ≠ ⟨0, hq⟩ := by
  classical
  have hr := hrl.2 i
  simp only [offPts, List.mem_filter, List.mem_finRange, true_and, offP, decide_eq_true_eq]
  by_cases hi : e.symm i ∈ S.dom
  · rw [if_pos hi] at hr
    have hl : label (e.symm i) = (E.symm ⟨e.symm i, hi⟩).2 := label_of_coords E hE ⟨_, hi⟩
    rw [hr, hl]
    have := (E.symm ⟨e.symm i, hi⟩).2.2
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨hi, fun h => by rw [h] at h1; exact absurd h1 (lt_irrefl 0)⟩
    · rintro ⟨_, h⟩
      refine ⟨Nat.pos_of_ne_zero fun h0 => h (Fin.ext h0), this⟩
  · rw [if_neg hi] at hr
    rw [hr]
    simp [hi]

end GI.Impl
