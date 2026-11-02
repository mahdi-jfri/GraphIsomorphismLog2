import Workspace.Impl.AggRectSpec
import Workspace.Impl.AggCaseMath

/-!
# The certificate search: the mathematics

Lemma 5.1 asks, at a source vertex `x` of a primitive configuration with a dominant color, for a
first-entrance rectangle certificate (`RectangleCertificate`). The data of a certificate are the
left color, the right color, the edge color and two points of the two sides. The left and right
colors are the colors at the two points, and the edge color occurs on an edge from the left
side to the right point (`mixed`). So a certificate is fixed by three points: the left point
`a`, the right point `b`, and a left point `u` with an edge to `b`. The search tries all
`n³` triples and checks the conditions of the certificate on each. Every condition is a count
on the table of the colors, so the check costs a polynomial in `n`. So the search space is
polynomial, as the task asks.

This file states the test on a table of numbers `D` (the rows of the pair colors of the fiber,
as the program holds them) in list form (`rcCand`), and proves:
* `rc_cand_sound`: if the test passes at `(a, b, u)`, then there is a certificate with left
  point `a`, right point `b` and edge color `c(u, b)` (`rcMk`);
* `rc_cand_complete`: every certificate passes the test at its two points and a witness of
  `mixed`.

The coloring `c` is related to the table only through its classes: `c(i, k) = c(i', k')` exactly
when `D i k = D i' k'` (`RcTab`). For a pair configuration this is `PairCfg.coloring_eq_iff`.
-/

namespace GI.Impl

open GI.Algorithm GI.CoherentEntrance GI.PairRefinement

/-! ### The test in list form -/

/-- Entry `(i, k)` of a table. -/
def rcAt (D : List (List ℕ)) (i k : ℕ) : ℕ := (D.getD i []).getD k 0

/-- The points `k < n` with `D x k = v` (a side of the rectangle). -/
def rcSide (D : List (List ℕ)) (x n v : ℕ) : List ℕ := (List.range n).filter fun k => rcAt D x k = v

/-- The row of the rectangle matrix at `w`: `1` at `r` when `D w r = v_E`. -/
def rcBits (D : List (List ℕ)) (vE : ℕ) (Rl : List ℕ) (w : ℕ) : List ℕ :=
  Rl.map fun r => if rcAt D w r = vE then 1 else 0

/-- Column `j` of a matrix given by rows. -/
def rcCol (Bm : List (List ℕ)) (j : ℕ) : List ℕ := Bm.map fun row => row.getD j 0

/-- The column degrees of a matrix with `m` columns. -/
def rcCols (Bm : List (List ℕ)) (m : ℕ) : List ℕ := (List.range m).map fun j => (rcCol Bm j).count 1

/-- The twin test of a row `ρ`: at most half of the rows are equal to it. -/
def rcTw (Bm : List (List ℕ)) (ρ : List ℕ) : Bool :=
  decide (2 * (Bm.filter fun σ => decide (ρ = σ)).length ≤ Bm.length)

/-- **The conditions of a certificate** on the sides `Wl`, `Rl` and the matrix `Bm` (rows over
`Wl`, columns over `Rl`): the left side is dominant, the two colors differ from each other and
from the diagonal color `v0`, all row degrees are equal, all column degrees are equal, the
witness `u` is on the left side (`vU = vL`) and the first column is not full, every row has at
most `|W|/2` twins, `|W| + |R| ≤ n`, and `16 |W||R| ≤ 3 n²`. -/
def rcCond (n vL vR v0 vU : ℕ) (Wl Rl : List ℕ) (Bm : List (List ℕ)) : Bool :=
  decide (3 * n < 4 * Wl.length) && decide (vR ≠ vL) && decide (vL ≠ v0) && decide (vR ≠ v0) &&
  decide (((Bm.map fun row => row.count 1).count ((Bm.map fun row => row.count 1).getD 0 0)) =
    Wl.length) &&
  decide ((rcCols Bm Rl.length).count ((rcCols Bm Rl.length).getD 0 0) = Rl.length) &&
  decide (vU = vL) && decide ((rcCols Bm Rl.length).getD 0 0 < Wl.length) && Bm.all (rcTw Bm) &&
  decide (Wl.length + Rl.length ≤ n) && decide (16 * (Wl.length * Rl.length) ≤ 3 * (n * n))

/-- The three points of a candidate index `t < n³`. -/
def rcPa (n t : ℕ) : ℕ := t / (n * n)
def rcPb (n t : ℕ) : ℕ := t / n % n
def rcPu (n t : ℕ) : ℕ := t % n

/-- **The test of the candidate `t`** at the vertex `x`: the points `a, b, u` of `t`, the colors
`v_L = D x a`, `v_R = D x b`, `v_E = D u b`, the sides and the matrix. -/
def rcCand (D : List (List ℕ)) (x n t : ℕ) : Bool :=
  rcCond n (rcAt D x (rcPa n t)) (rcAt D x (rcPb n t)) (rcAt D x x) (rcAt D x (rcPu n t))
    (rcSide D x n (rcAt D x (rcPa n t))) (rcSide D x n (rcAt D x (rcPb n t)))
    ((rcSide D x n (rcAt D x (rcPa n t))).map
      (rcBits D (rcAt D (rcPu n t) (rcPb n t)) (rcSide D x n (rcAt D x (rcPb n t)))))

/-- The index of the candidate `(a, b, u)`. -/
def rcIdx (n a b u : ℕ) : ℕ := a * (n * n) + b * n + u

theorem rc_idx_lt {n a b u : ℕ} (ha : a < n) (hb : b < n) (hu : u < n) :
    rcIdx n a b u < n * n * n := by
  unfold rcIdx
  have h1 : b * n + u < n * n := by nlinarith
  have h2 : a * (n * n) + n * n ≤ n * n * n := by nlinarith
  omega

theorem rc_pa_idx {n a b u : ℕ} (hb : b < n) (hu : u < n) : rcPa n (rcIdx n a b u) = a := by
  unfold rcPa rcIdx
  have h1 : b * n + u < n * n := by nlinarith
  rw [Nat.add_assoc, Nat.mul_comm a, Nat.mul_add_div (by nlinarith), Nat.div_eq_of_lt h1,
    Nat.add_zero]

theorem rc_pb_idx {n a b u : ℕ} (hb : b < n) (hu : u < n) : rcPb n (rcIdx n a b u) = b := by
  unfold rcPb rcIdx
  have hn : 0 < n := by omega
  have e : a * (n * n) + b * n + u = n * (a * n + b) + u := by ring
  rw [e, Nat.mul_add_div hn, Nat.div_eq_of_lt hu, Nat.add_zero, Nat.add_mod, Nat.mul_mod_left,
    Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hb]

theorem rc_pu_idx {n a b u : ℕ} (hu : u < n) : rcPu n (rcIdx n a b u) = u := by
  unfold rcPu rcIdx
  have e : a * (n * n) + b * n + u = n * (a * n + b) + u := by ring
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]

theorem rc_idx_p {n t : ℕ} (ht : t < n * n * n) :
    rcIdx n (rcPa n t) (rcPb n t) (rcPu n t) = t := by
  unfold rcIdx rcPa rcPb rcPu
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at ht
    · exact h
  have e1 := Nat.div_add_mod t n
  have e2 := Nat.div_add_mod (t / n) n
  have e3 : t / n / n = t / (n * n) := Nat.div_div_eq_div_mul t n n
  nlinarith

theorem rc_pa_lt {n t : ℕ} (ht : t < n * n * n) : rcPa n t < n := by
  unfold rcPa
  rw [Nat.div_lt_iff_lt_mul (by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at ht
    · exact Nat.mul_pos h h)]
  rw [Nat.mul_comm]; exact ht

theorem rc_pb_lt {n t : ℕ} (ht : t < n * n * n) : rcPb n t < n := by
  unfold rcPb
  exact Nat.mod_lt _ (by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at ht
    · exact h)

theorem rc_pu_lt {n t : ℕ} (ht : t < n * n * n) : rcPu n t < n := by
  unfold rcPu
  exact Nat.mod_lt _ (by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at ht
    · exact h)

/-! ### A table of a function -/

variable {n : ℕ}

/-- The table of `Dm : Fin n → Fin n → ℕ`, by rows. -/
def rcTab (Dm : Fin n → Fin n → ℕ) : List (List ℕ) :=
  (List.finRange n).map fun i => (List.finRange n).map (Dm i)

theorem rcAt_tab (Dm : Fin n → Fin n → ℕ) (i k : Fin n) : rcAt (rcTab Dm) i k = Dm i k := by
  simp [rcAt, rcTab, List.getD_eq_getElem?_getD]

theorem rc_range_eq : List.range n = (List.finRange n).map Fin.val :=
  (List.map_coe_finRange_eq_range).symm

/-- A side as a list of points of `Fin n`. -/
theorem rcSide_tab (Dm : Fin n → Fin n → ℕ) (x : Fin n) (v : ℕ) :
    rcSide (rcTab Dm) x n v = ((List.finRange n).filter fun y => decide (Dm x y = v)).map Fin.val := by
  rw [rcSide, rc_range_eq, List.filter_map]
  congr 1
  refine List.filter_congr fun y _ => ?_
  simp [rcAt_tab]

theorem rcSide_length (Dm : Fin n → Fin n → ℕ) (x : Fin n) (v : ℕ) :
    (rcSide (rcTab Dm) x n v).length = (Finset.univ.filter fun y => Dm x y = v).card := by
  rw [rcSide_tab, List.length_map, ac_card_filter]

/-! ### The coloring of a table -/

/-- **The coloring `c` has the classes of the table `Dm`** on the side `false`. -/
def RcTab (c : Coloring n) (Dm : Fin n → Fin n → ℕ) : Prop :=
  ∀ i k i' k', c (false, i, k) = c (false, i', k') ↔ Dm i k = Dm i' k'

/-! ### Counting on a fiber of a color -/

theorem rc_card_sub (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q] :
    (Finset.univ.filter fun r : {y // p y} => q r.1).card =
      (Finset.univ.filter fun y => p y ∧ q y).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r.2, hr⟩
  · rintro ⟨hp, hq⟩; exact ⟨⟨y, hp⟩, hq, rfl⟩

/-- The length of a filtered list of points of `Fin n`, mapped to numbers. -/
theorem rc_len_filter (p : Fin n → Prop) [DecidablePred p] :
    (((List.finRange n).filter fun y => decide (p y)).map Fin.val).length =
      (Finset.univ.filter p).card := by
  rw [List.length_map, ac_card_filter]

/-- Counting the ones of a `0/1` list. -/
theorem rc_count_ite {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map fun y => if p y then 1 else 0).count 1 = (l.filter fun y => decide (p y)).length := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : p y
    · simp [h, ih, List.count_cons]
    · simp [h, ih, List.count_cons]

/-- All entries of a list equal its first entry. -/
theorem rc_count_head (l : List ℕ) :
    l.count (l.getD 0 0) = l.length ↔ ∀ x ∈ l, x = l.getD 0 0 := by
  rw [List.count_eq_length]
  exact ⟨fun h x hx => (h x hx).symm, fun h x hx => (h x hx).symm⟩

section Tab

variable {c : Coloring n} {Dm : Fin n → Fin n → ℕ} (hD : RcTab c Dm)

include hD in
theorem rc_c_iff (i k i' k' : Fin n) : c (false, i, k) = c (false, i', k') ↔ Dm i k = Dm i' k' :=
  hD i k i' k'

end Tab

/-! ### The list conditions on a table, as counts on `Fin n` -/

section Lists

variable (Dm : Fin n → Fin n → ℕ) (x : Fin n)

/-- The degree of `w` into the right side `{r | D x r = vR}`. -/
def rcRd (vR vE : ℕ) (w : Fin n) : ℕ := (Finset.univ.filter fun r => Dm x r = vR ∧ Dm w r = vE).card

/-- The degree of `r` from the left side `{w | D x w = vL}`. -/
def rcCd (vL vE : ℕ) (r : Fin n) : ℕ := (Finset.univ.filter fun w => Dm x w = vL ∧ Dm w r = vE).card

/-- The number of twins of `w` on the left side. -/
def rcTwc (vL vR vE : ℕ) (w : Fin n) : ℕ :=
  (Finset.univ.filter fun z => Dm x z = vL ∧
    ∀ r, Dm x r = vR → (Dm z r = vE ↔ Dm w r = vE)).card

/-- The points of a side, as a list of `Fin n`. -/
def rcSideF (v : ℕ) : List (Fin n) := (List.finRange n).filter fun y => decide (Dm x y = v)

theorem rc_side_eq (v : ℕ) : rcSide (rcTab Dm) x n v = (rcSideF Dm x v).map Fin.val :=
  rcSide_tab Dm x v

theorem rc_mem_sideF {v : ℕ} {y : Fin n} : y ∈ rcSideF Dm x v ↔ Dm x y = v := by
  simp [rcSideF]

theorem rc_bits_eq (vE vR : ℕ) (w : Fin n) :
    rcBits (rcTab Dm) vE (rcSide (rcTab Dm) x n vR) w =
      (rcSideF Dm x vR).map fun r => if Dm w r = vE then 1 else 0 := by
  rw [rcBits, rc_side_eq, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [rcAt_tab]

theorem rc_bits_count (vE vR : ℕ) (w : Fin n) :
    (rcBits (rcTab Dm) vE (rcSide (rcTab Dm) x n vR) w).count 1 = rcRd Dm x vR vE w := by
  rw [rc_bits_eq, rc_count_ite, rcSideF, List.filter_filter, rcRd, ac_card_filter]
  congr 1
  refine List.filter_congr fun r _ => ?_
  simp [Bool.and_comm]

/-- The matrix of the rectangle as a list of rows. -/
theorem rc_bm_eq (vL vR vE : ℕ) :
    (rcSide (rcTab Dm) x n vL).map (rcBits (rcTab Dm) vE (rcSide (rcTab Dm) x n vR)) =
      (rcSideF Dm x vL).map fun w => (rcSideF Dm x vR).map fun r => if Dm w r = vE then 1 else 0 := by
  rw [rc_side_eq Dm x vL, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  exact rc_bits_eq Dm x vE vR w

/-- Entry `j` of a mapped list. -/
theorem rc_getD_map {α : Type} (l : List α) (f : α → ℕ) {j : ℕ} (hj : j < l.length) :
    (l.map f).getD j 0 = f l[j] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-- The column degrees, read on the right side. -/
theorem rc_cols_eq (vL vR vE : ℕ) :
    rcCols ((rcSideF Dm x vL).map fun w => (rcSideF Dm x vR).map fun r => if Dm w r = vE then 1 else 0)
      (rcSideF Dm x vR).length = (rcSideF Dm x vR).map (rcCd Dm x vL vE) := by
  refine List.ext_getElem (by simp [rcCols]) fun j h1 h2 => ?_
  simp only [rcCols, List.getElem_map, List.getElem_range, rcCol, List.map_map]
  have hj : j < (rcSideF Dm x vR).length := by simpa [rcCols] using h1
  have e : ((rcSideF Dm x vL).map ((fun row => row.getD j 0) ∘ fun w =>
      (rcSideF Dm x vR).map fun r => if Dm w r = vE then 1 else 0)) =
      (rcSideF Dm x vL).map fun w => if Dm w (rcSideF Dm x vR)[j] = vE then 1 else 0 := by
    refine List.map_congr_left fun w _ => ?_
    simp only [Function.comp_apply]
    rw [rc_getD_map _ _ hj]
  rw [e, rc_count_ite]
  generalize (rcSideF Dm x vR)[j] = r
  unfold rcSideF
  rw [List.filter_filter, rcCd, ac_card_filter]
  congr 1
  refine List.filter_congr fun w _ => ?_
  simp [Bool.and_comm]

theorem rc_twins_len (vL vR vE : ℕ) (w : Fin n) :
    (((rcSideF Dm x vL).map fun w => (rcSideF Dm x vR).map fun r =>
        if Dm w r = vE then (1 : ℕ) else 0).filter fun σ =>
      decide (((rcSideF Dm x vR).map fun r => if Dm w r = vE then 1 else 0) = σ)).length =
      rcTwc Dm x vL vR vE w := by
  rw [List.filter_map, List.length_map]
  generalize hg : (fun w : Fin n => (rcSideF Dm x vR).map fun r =>
    if Dm w r = vE then (1 : ℕ) else 0) = g
  have hgz : ∀ z, g z = (rcSideF Dm x vR).map fun r => if Dm z r = vE then 1 else 0 := by
    intro z; rw [← hg]
  have e1 : ((fun σ => decide (g w = σ)) ∘ g) = fun z => decide (g w = g z) := rfl
  rw [show (fun σ => decide (((rcSideF Dm x vR).map fun r => if Dm w r = vE then 1 else 0) = σ))
    = fun σ => decide (g w = σ) by rw [hgz], e1]
  unfold rcSideF
  rw [List.filter_filter, rcTwc, ac_card_filter]
  congr 1
  refine List.filter_congr fun z _ => ?_
  rw [Bool.and_comm, ← Bool.decide_and]
  rw [decide_eq_decide]
  refine and_congr_right fun _ => ?_
  rw [hgz, hgz, eq_comm, List.map_inj_left]
  constructor
  · intro h r hr
    have := h r (by simp [rcSideF, hr])
    by_cases h1 : Dm z r = vE <;> by_cases h2 : Dm w r = vE <;> simp_all
  · intro h r hr
    have := h r (by simpa [rcSideF] using hr)
    by_cases h1 : Dm z r = vE <;> by_cases h2 : Dm w r = vE <;> simp_all

/-- All values of a function on a list are equal to its value at the head, exactly when they are
equal to its value at any member. -/
theorem rc_allEq {α : Type} (l : List α) (f : α → ℕ) {s₀ : α} (hs : s₀ ∈ l) :
    (l.map f).count ((l.map f).getD 0 0) = (l.map f).length ↔ ∀ s ∈ l, f s = f s₀ := by
  rw [rc_count_head]
  have hl : 0 < l.length := List.length_pos_of_mem hs
  rw [rc_getD_map l f hl]
  constructor
  · intro h s hs'
    rw [h _ (List.mem_map_of_mem hs'), h _ (List.mem_map_of_mem hs)]
  · intro h y hy
    obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hy
    rw [h s hs', h _ (List.getElem_mem hl)]

end Lists

/-! ### The test on a table, as counts on `Fin n` -/

section Ok

variable (Dm : Fin n → Fin n → ℕ) (x a b u : Fin n)

/-- The number of points of a side. -/
def rcSz (v : ℕ) : ℕ := (Finset.univ.filter fun y => Dm x y = v).card

theorem rc_sideF_len (v : ℕ) : (rcSideF Dm x v).length = rcSz Dm x v := by
  rw [rcSideF, rcSz, ac_card_filter]

/-- **The conditions of the test, as counts on `Fin n`** (`v_L = D x a`, `v_R = D x b`,
`v_E = D u b`). -/
structure RcOK : Prop where
  dom : 3 * n < 4 * rcSz Dm x (Dm x a)
  diff : Dm x b ≠ Dm x a
  offL : Dm x a ≠ Dm x x
  offR : Dm x b ≠ Dm x x
  rows : ∀ w, Dm x w = Dm x a → rcRd Dm x (Dm x b) (Dm u b) w = rcRd Dm x (Dm x b) (Dm u b) a
  cols : ∀ r, Dm x r = Dm x b → rcCd Dm x (Dm x a) (Dm u b) r = rcCd Dm x (Dm x a) (Dm u b) b
  uL : Dm x u = Dm x a
  mix : rcCd Dm x (Dm x a) (Dm u b) b < rcSz Dm x (Dm x a)
  tw : ∀ w, Dm x w = Dm x a → 2 * rcTwc Dm x (Dm x a) (Dm x b) (Dm u b) w ≤ rcSz Dm x (Dm x a)
  sum : rcSz Dm x (Dm x a) + rcSz Dm x (Dm x b) ≤ n
  area : 16 * (rcSz Dm x (Dm x a) * rcSz Dm x (Dm x b)) ≤ 3 * (n * n)

theorem rc_mem_sideF_self {v : ℕ} (y : Fin n) (h : Dm x y = v) : y ∈ rcSideF Dm x v :=
  (rc_mem_sideF Dm x).2 h

/-- **The test is the conditions.** -/
theorem rc_cand_iff :
    rcCand (rcTab Dm) x n (rcIdx n a b u) = true ↔ RcOK Dm x a b u := by
  have hb := b.isLt
  have hu := u.isLt
  have e1 : rcPa n (rcIdx n a b u) = a := rc_pa_idx hb hu
  have e2 : rcPb n (rcIdx n a b u) = b := rc_pb_idx hb hu
  have e3 : rcPu n (rcIdx n a b u) = u := rc_pu_idx hu
  unfold rcCand
  rw [e1, e2, e3, rcAt_tab, rcAt_tab, rcAt_tab, rcAt_tab, rcAt_tab]
  set vL := Dm x a
  set vR := Dm x b
  set vE := Dm u b
  -- the rows
  have hrows : (((rcSide (rcTab Dm) x n vL).map (rcBits (rcTab Dm) vE (rcSide (rcTab Dm) x n vR))).map
      fun row => row.count 1) = (rcSideF Dm x vL).map (rcRd Dm x vR vE) := by
    rw [List.map_map, rc_side_eq Dm x vL, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    exact rc_bits_count Dm x vE vR w
  have hbm := rc_bm_eq Dm x vL vR vE
  have hWl : (rcSide (rcTab Dm) x n vL).length = rcSz Dm x vL := by
    rw [rc_side_eq, List.length_map, rc_sideF_len]
  have hRl : (rcSide (rcTab Dm) x n vR).length = (rcSideF Dm x vR).length := by
    rw [rc_side_eq, List.length_map]
  have hcols := rc_cols_eq Dm x vL vR vE
  have haW : a ∈ rcSideF Dm x vL := rc_mem_sideF_self Dm x a rfl
  have hbR : b ∈ rcSideF Dm x vR := rc_mem_sideF_self Dm x b rfl
  have hrowsI := rc_allEq (rcSideF Dm x vL) (rcRd Dm x vR vE) haW
  have hcolsI := rc_allEq (rcSideF Dm x vR) (rcCd Dm x vL vE) hbR
  have hcol0 : ((rcSideF Dm x vR).map (rcCd Dm x vL vE)).getD 0 0 = rcCd Dm x vL vE b ∨
      ¬ (∀ s ∈ rcSideF Dm x vR, rcCd Dm x vL vE s = rcCd Dm x vL vE b) := by
    by_cases h : ∀ s ∈ rcSideF Dm x vR, rcCd Dm x vL vE s = rcCd Dm x vL vE b
    · left
      have hl : 0 < (rcSideF Dm x vR).length := List.length_pos_of_mem hbR
      rw [rc_getD_map _ _ hl]
      exact h _ (List.getElem_mem hl)
    · exact Or.inr h
  have htw : ((rcSideF Dm x vL).map fun w => (rcSideF Dm x vR).map fun r =>
      if Dm w r = vE then (1 : ℕ) else 0).all (rcTw ((rcSideF Dm x vL).map fun w =>
        (rcSideF Dm x vR).map fun r => if Dm w r = vE then (1 : ℕ) else 0)) = true ↔
      ∀ w, Dm x w = vL → 2 * rcTwc Dm x vL vR vE w ≤ rcSz Dm x vL := by
    rw [List.all_eq_true]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rcTw,
      decide_eq_true_eq, List.length_map, rc_sideF_len]
    constructor
    · intro h w hw
      have := h w ((rc_mem_sideF Dm x).2 hw)
      rwa [rc_twins_len] at this
    · intro h w hw
      rw [rc_twins_len]
      exact h w ((rc_mem_sideF Dm x).1 hw)
  rw [hbm] at hrows
  rw [hbm]
  simp only [rcCond, Bool.and_eq_true, decide_eq_true_eq]
  rw [hrows, hWl, hRl, hcols, htw]
  rw [show rcSz Dm x vL = ((rcSideF Dm x vL).map (rcRd Dm x vR vE)).length by
    rw [List.length_map, rc_sideF_len], hrowsI]
  rw [show (rcSideF Dm x vR).length = ((rcSideF Dm x vR).map (rcCd Dm x vL vE)).length by
    rw [List.length_map], hcolsI]
  simp only [List.length_map, rc_sideF_len]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
    have h8' : rcCd Dm x vL vE b < rcSz Dm x vL := by
      rcases hcol0 with h | h
      · rwa [h] at h8
      · exact absurd h6 h
    exact ⟨h1, h2, h3, h4, fun w hw => h5 w ((rc_mem_sideF Dm x).2 hw),
      fun r hr => h6 r ((rc_mem_sideF Dm x).2 hr), h7, h8', h9, h10, h11⟩
  · intro h
    have h6 : ∀ s ∈ rcSideF Dm x vR, rcCd Dm x vL vE s = rcCd Dm x vL vE b :=
      fun r hr => h.cols r ((rc_mem_sideF Dm x).1 hr)
    have h9 : ((rcSideF Dm x vR).map (rcCd Dm x vL vE)).getD 0 0 < rcSz Dm x vL := by
      rcases hcol0 with e | e
      · rw [e]; exact h.mix
      · exact absurd h6 e
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.dom, h.diff⟩, h.offL⟩, h.offR⟩,
      fun w hw => h.rows w ((rc_mem_sideF Dm x).1 hw)⟩, h6⟩, h.uL⟩, h9⟩, h.tw⟩, h.sum⟩, h.area⟩

end Ok

/-! ### The certificate from the conditions, and back -/

section Cert

variable {c : Coloring n} {Dm : Fin n → Fin n → ℕ} (hD : RcTab c Dm) (x a b u : Fin n)

include hD

theorem rc_rowValency :
    rowValency c false (c (false, x, a)) x = rcSz Dm x (Dm x a) := by
  unfold rowValency rcSz
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hD x y x a

theorem rc_rowDegree (w : ColorFiber c false x (c (false, x, a))) :
    Semiregular.rowDegree (fiberMatrix c false x (c (false, x, a)) (c (false, x, b))
      (c (false, u, b))) w = rcRd Dm x (Dm x b) (Dm u b) w.1 := by
  unfold Semiregular.rowDegree fiberMatrix
  simp only [decide_eq_true_eq]
  rw [rc_card_sub (fun y => c (false, x, y) = c (false, x, b))
    (fun y => c (false, w.1, y) = c (false, u, b)), rcRd]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hD x y x b, hD w.1 y u b]

theorem rc_columnDegree (r : ColorFiber c false x (c (false, x, b))) :
    Semiregular.columnDegree (fiberMatrix c false x (c (false, x, a)) (c (false, x, b))
      (c (false, u, b))) r = rcCd Dm x (Dm x a) (Dm u b) r.1 := by
  unfold Semiregular.columnDegree fiberMatrix
  simp only [decide_eq_true_eq]
  rw [rc_card_sub (fun y => c (false, x, y) = c (false, x, a))
    (fun y => c (false, y, r.1) = c (false, u, b)), rcCd]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hD x y x a, hD y r.1 u b]

theorem rc_twins (w : ColorFiber c false x (c (false, x, a))) :
    (Semiregular.twins (fiberMatrix c false x (c (false, x, a)) (c (false, x, b))
      (c (false, u, b))) w).card = rcTwc Dm x (Dm x a) (Dm x b) (Dm u b) w.1 := by
  unfold Semiregular.twins
  have e : (Finset.univ.filter fun z : ColorFiber c false x (c (false, x, a)) =>
      fiberMatrix c false x (c (false, x, a)) (c (false, x, b)) (c (false, u, b)) z =
        fiberMatrix c false x (c (false, x, a)) (c (false, x, b)) (c (false, u, b)) w) =
      Finset.univ.filter fun z : ColorFiber c false x (c (false, x, a)) =>
        ∀ r, Dm x r = Dm x b → (Dm z.1 r = Dm u b ↔ Dm w.1 r = Dm u b) := by
    refine Finset.filter_congr fun z _ => ⟨fun h r hr => ?_, fun h => ?_⟩
    · have := congrFun h ⟨r, (hD x r x b).2 hr⟩
      simp only [fiberMatrix, decide_eq_decide] at this
      rwa [hD z.1 r u b, hD w.1 r u b] at this
    · funext r
      simp only [fiberMatrix, decide_eq_decide]
      rw [hD z.1 r.1 u b, hD w.1 r.1 u b]
      exact h r.1 ((hD x r.1 x b).1 r.2)
  rw [e, rc_card_sub (fun y => c (false, x, y) = c (false, x, a))
    (fun y => ∀ r, Dm x r = Dm x b → (Dm y r = Dm u b ↔ Dm w.1 r = Dm u b)), rcTwc]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hD x y x a]

/-- **The certificate of a candidate that passes the test** (Lemma 5.1): left point `a`, right
point `b`, edge color `c(u, b)`. -/
noncomputable def rcMk (h : RcOK Dm x a b u) : RectangleCertificate c false x etaB where
  leftColor := c (false, x, a)
  rightColor := c (false, x, b)
  edgeColor := c (false, u, b)
  leftPoint := ⟨a, rfl⟩
  rightPoint := ⟨b, rfl⟩
  dominant := by
    rw [rc_rowValency hD]
    have := h.dom
    have h' : (3 : ℝ) * n < 4 * rcSz Dm x (Dm x a) := by exact_mod_cast this
    unfold etaB; linarith
  different := fun e => h.diff ((hD x b x a).1 e)
  leftOffDiagonal := fun e => h.offL ((hD x a x x).1 e)
  rightOffDiagonal := fun e => h.offR ((hD x b x x).1 e)
  rows w := by
    rw [rc_rowDegree hD, rc_rowDegree hD]
    exact h.rows w.1 ((hD x w.1 x a).1 w.2)
  columns r := by
    rw [rc_columnDegree hD, rc_columnDegree hD]
    exact h.cols r.1 ((hD x r.1 x b).1 r.2)
  mixed := by
    -- `u` is on the left side; some left point has no edge to `b`
    have hlt := h.mix
    unfold rcCd rcSz at hlt
    obtain ⟨w, hw, hwn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hw hwn
    refine ⟨⟨u, (hD x u x a).2 h.uL⟩, ⟨w, (hD x w x a).2 hw⟩, ?_, ?_⟩
    · simp [fiberMatrix]
    · simp only [fiberMatrix, decide_eq_false_iff_not]
      rw [hD w b u b]
      exact hwn hw
  twinBound w := by
    rw [rc_twins hD, rc_rowValency hD]
    exact h.tw w.1 ((hD x w.1 x a).1 w.2)
  sideSum := by
    have e : rowValency c false (c (false, x, b)) x = rcSz Dm x (Dm x b) := rc_rowValency hD x b
    rw [rc_rowValency hD, e]
    exact h.sum
  disjoint := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    rw [mem_colorClass] at h1 h2
    exact h.diff ((hD x b x a).1 (h2.symm.trans h1))
  area := by
    have e : rowValency c false (c (false, x, b)) x = rcSz Dm x (Dm x b) := rc_rowValency hD x b
    rw [rc_rowValency hD, e]
    have := h.area
    have h' : (16 : ℝ) * (rcSz Dm x (Dm x a) * rcSz Dm x (Dm x b)) ≤ 3 * (n * n) := by
      exact_mod_cast this
    unfold etaB; nlinarith

/-- **Every certificate passes the test** at its left point, its right point and a left point
with an edge to the right point (`mixed`). -/
theorem rc_ok_of_cert (cert : RectangleCertificate c false x etaB) (u : Fin n)
    (hu : c (false, u, cert.rightPoint.1) = cert.edgeColor)
    (hu' : c (false, x, u) = cert.leftColor) :
    RcOK Dm x cert.leftPoint.1 cert.rightPoint.1 u := by
  obtain ⟨L, R, E, ⟨a, ha⟩, ⟨b, hb⟩, hdom, hdiff, hoffL, hoffR, hrows, hcols, hmixed, htw,
    hsum, hdis, harea⟩ := cert
  simp only at hu hu' ⊢
  subst ha hb hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rc_rowValency hD] at hdom
    unfold etaB at hdom
    have : (3 : ℝ) * n < 4 * rcSz Dm x (Dm x a) := by linarith
    exact_mod_cast this
  · exact fun e => hdiff ((hD x b x a).2 e)
  · exact fun e => hoffL ((hD x a x x).2 e)
  · exact fun e => hoffR ((hD x b x x).2 e)
  · intro w hw
    have := hrows ⟨w, (hD x w x a).2 hw⟩
    rwa [rc_rowDegree hD, rc_rowDegree hD] at this
  · intro r hr
    have := hcols ⟨r, (hD x r x b).2 hr⟩
    rwa [rc_columnDegree hD, rc_columnDegree hD] at this
  · exact (hD x u x a).1 hu'
  · obtain ⟨-, ⟨w, hw⟩, -, hwf⟩ := hmixed
    have hwf' : ¬ Dm w b = Dm u b := by
      simp only [fiberMatrix, decide_eq_false_iff_not] at hwf
      exact fun e => hwf ((hD w b u b).2 e)
    unfold rcCd rcSz
    refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy.1
    · have := hsub (show w ∈ Finset.univ.filter fun y => Dm x y = Dm x a by
        simpa using (hD x w x a).1 hw)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hwf' this.2
  · intro w hw
    have := htw ⟨w, (hD x w x a).2 hw⟩
    rwa [rc_twins hD, rc_rowValency hD] at this
  · have e : rowValency c false (c (false, x, b)) x = rcSz Dm x (Dm x b) := rc_rowValency hD x b
    rw [rc_rowValency hD, e] at hsum
    exact hsum
  · have e : rowValency c false (c (false, x, b)) x = rcSz Dm x (Dm x b) := rc_rowValency hD x b
    rw [rc_rowValency hD, e] at harea
    unfold etaB at harea
    have hn : ((n : ℝ)) ^ 2 = n * n := by ring
    have : (16 : ℝ) * (rcSz Dm x (Dm x a) * rcSz Dm x (Dm x b)) ≤ 3 * (n * n) := by
      nlinarith
    exact_mod_cast this

end Cert

/-! ### The search -/

/-- The first candidate that passes the test, or `n³` if none does. -/
def rcFind (D : List (List ℕ)) (x n : ℕ) : ℕ := (List.range (n * n * n)).findIdx (rcCand D x n)

/-- **The output of the search**: `[D x a, D x b, D u b, F a, F b]` for the first candidate
`(a, b, u)` that passes the test, `[]` if none does. -/
def rcOut (D : List (List ℕ)) (F : List ℕ) (x n : ℕ) : GI.Cited.Val :=
  if rcFind D x n < n * n * n then
    .list [.nat (rcAt D x (rcPa n (rcFind D x n))), .nat (rcAt D x (rcPb n (rcFind D x n))),
      .nat (rcAt D (rcPu n (rcFind D x n)) (rcPb n (rcFind D x n))),
      .nat (F.getD (rcPa n (rcFind D x n)) 0), .nat (F.getD (rcPb n (rcFind D x n)) 0)]
  else .list []

theorem rc_find_lt_iff (D : List (List ℕ)) (x n : ℕ) :
    rcFind D x n < n * n * n ↔ ∃ t < n * n * n, rcCand D x n t = true := by
  unfold rcFind
  constructor
  · intro h
    have h' : (List.range (n * n * n)).findIdx (rcCand D x n) < (List.range (n * n * n)).length := by
      simpa using h
    refine ⟨_, h, ?_⟩
    have := List.findIdx_getElem (w := h')
    simpa using this
  · rintro ⟨t, ht, htc⟩
    have := List.findIdx_lt_length_of_exists (p := rcCand D x n) (xs := List.range (n * n * n))
      ⟨t, List.mem_range.2 ht, htc⟩
    simpa using this

theorem rc_find_cand {D : List (List ℕ)} {x n : ℕ} (h : rcFind D x n < n * n * n) :
    rcCand D x n (rcFind D x n) = true := by
  unfold rcFind at h ⊢
  have h' : (List.range (n * n * n)).findIdx (rcCand D x n) < (List.range (n * n * n)).length := by
    simpa using h
  have := List.findIdx_getElem (w := h')
  simpa using this

section Pair

variable {q : ℕ} (X : PairCfg q)

/-- The table of the pair colors of the fiber, numbered by `emb`. -/
def rcDm : Fin X.fiber.card → Fin X.fiber.card → ℕ := fun i k => X.col (X.emb rfl i) (X.emb rfl k)

theorem rc_tab_pair : RcTab X.coloring (rcDm X) := fun i k i' k' =>
  X.coloring_eq_iff false false i k i' k'

/-- The fiber, as the list of its labels in increasing order. -/
def rcFib : List ℕ := (List.finRange X.fiber.card).map fun i => (X.emb rfl i : ℕ)

theorem rc_fib_getD (i : Fin X.fiber.card) : (rcFib X).getD i 0 = X.emb rfl i := by
  simp [rcFib, List.getD_eq_getElem?_getD]

theorem rc_pos_of_cert {i₀ : Fin X.fiber.card} : 0 < X.fiber.card :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) i₀.isLt

/-- A certificate gives a candidate that passes the test. -/
theorem rc_exists_cand (i₀ : Fin X.fiber.card)
    (h : Nonempty (RectangleCertificate X.coloring false i₀ etaB)) :
    rcFind (rcTab (rcDm X)) i₀ X.fiber.card <
      X.fiber.card * X.fiber.card * X.fiber.card := by
  obtain ⟨cert⟩ := h
  obtain ⟨u, -, hu, -⟩ := cert.mixed
  have hu1 : X.coloring (false, u.1, cert.rightPoint.1) = cert.edgeColor := by
    simpa [fiberMatrix] using hu
  have hok := rc_ok_of_cert (rc_tab_pair X) i₀ cert u.1 hu1 u.2
  rw [rc_find_lt_iff]
  exact ⟨_, rc_idx_lt cert.leftPoint.1.isLt cert.rightPoint.1.isLt u.1.isLt,
    (rc_cand_iff _ _ _ _ _).2 hok⟩

/-- The three points of the candidate found. -/
def rcPts (i₀ : Fin X.fiber.card) (h : rcFind (rcTab (rcDm X)) i₀ X.fiber.card <
    X.fiber.card * X.fiber.card * X.fiber.card) :
    Fin X.fiber.card × Fin X.fiber.card × Fin X.fiber.card :=
  (⟨_, rc_pa_lt h⟩, ⟨_, rc_pb_lt h⟩, ⟨_, rc_pu_lt h⟩)

theorem rc_pts_ok (i₀ : Fin X.fiber.card) (h : rcFind (rcTab (rcDm X)) i₀ X.fiber.card <
    X.fiber.card * X.fiber.card * X.fiber.card) :
    RcOK (rcDm X) i₀ (rcPts X i₀ h).1 (rcPts X i₀ h).2.1 (rcPts X i₀ h).2.2 := by
  rw [← rc_cand_iff]
  simp only [rcPts]
  rw [rc_idx_p h]
  exact rc_find_cand h

/-- **The certificate of the search**: the certificate of the first candidate that passes the
test. -/
noncomputable def rcCertOf (i₀ : Fin X.fiber.card)
    (h : Nonempty (RectangleCertificate X.coloring false i₀ etaB)) :
    RectangleCertificate X.coloring false i₀ etaB :=
  rcMk (rc_tab_pair X) i₀ _ _ _ (rc_pts_ok X i₀ (rc_exists_cand X i₀ h))

end Pair

/-- **The certificate function of the search** (for `SojChoice.cert`). -/
noncomputable def rcCertFn : RcCertFn := fun X i₀ h => rcCertOf X i₀ h

/-- **The output of the search is the value of its certificate**, and `[]` when there is none. -/
theorem rc_out_eq {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card) :
    (∀ h : Nonempty (RectangleCertificate X.coloring false i₀ etaB),
      rcOut (rcTab (rcDm X)) (rcFib X) i₀ X.fiber.card = rcCertVal X i₀ (rcCertFn X i₀ h)) ∧
    (IsEmpty (RectangleCertificate X.coloring false i₀ etaB) →
      rcOut (rcTab (rcDm X)) (rcFib X) i₀ X.fiber.card = .list []) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hlt := rc_exists_cand X i₀ h
    unfold rcOut
    rw [if_pos hlt]
    -- the points of the candidate found
    have ha := rc_pa_lt hlt
    have hb := rc_pb_lt hlt
    have hu := rc_pu_lt hlt
    set t := rcFind (rcTab (rcDm X)) i₀ X.fiber.card
    have e1 := rcAt_tab (rcDm X) i₀ ⟨rcPa _ t, ha⟩
    have e2 := rcAt_tab (rcDm X) i₀ ⟨rcPb _ t, hb⟩
    have e3 := rcAt_tab (rcDm X) ⟨rcPu _ t, hu⟩ ⟨rcPb _ t, hb⟩
    have e4 := rc_fib_getD X ⟨rcPa _ t, ha⟩
    have e5 := rc_fib_getD X ⟨rcPb _ t, hb⟩
    simp only at e1 e2 e3 e4 e5
    rw [e1, e2, e3, e4, e5]
    unfold rcCertVal rcCertFn rcCertOf
    have hE := certVals_edge X i₀ (rcMk (rc_tab_pair X) i₀ _ _ _ (rc_pts_ok X i₀ hlt))
      (u := ⟨rcPu _ t, hu⟩) (r := ⟨rcPb _ t, hb⟩) rfl
    rw [hE]
    rfl
  · have hge : ¬ rcFind (rcTab (rcDm X)) i₀ X.fiber.card <
        X.fiber.card * X.fiber.card * X.fiber.card := by
      intro hlt
      exact h.false (rcMk (rc_tab_pair X) i₀ _ _ _ (rc_pts_ok X i₀ hlt))
    unfold rcOut
    rw [if_neg hge]

end GI.Impl
