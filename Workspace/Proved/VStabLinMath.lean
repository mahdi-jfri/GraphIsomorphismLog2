import Workspace.Impl.VStabLinInsert
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Span.Defs

/-!
# The mathematics of the echelon rows

The programs of `Impl/VStabLin*.lean` work on lists of numbers below `p`. Here a list `x` is
read as the vector `vsF p x : ℕ → ZMod p`, entry `i` being `x[i]` (and `0` past the end).

* `vsF_vsLin`, `vsF_vsAxpy`: the combination programs compute `a v + b u` and `x - c r`.
* `vsSift_mem`: if the pair and every row lie in a submodule `W` of pairs of vectors, so does
  the sifted pair. This is how tags record combinations: take `W` to be the pairs `(M t, t)`
  for a linear map `M`, or the pairs `(x, t)` with `x` a combination of the inputs given by `t`.
* `VsEch`: the rows are in echelon form: each row is `1` at its pivot, and later rows are `0` at
  earlier pivots.
* `vsSift_zero_at`: after sifting, the main part is `0` at every pivot.
* `vsSift_sub_mem`: sifting changes the main part by a vector in the span of the rows.
* `vsSift_eq_zero_iff`: the sifted main part is `0` exactly when the main part lies in the span
  of the rows.
* `vsInv_correct`: the inverse found by search is the inverse modulo a prime.
* `vsInsert_new`, `vsInsert_rel`: what the insertion (`vsInsertVal`) returns. In the first case
  the new rows are in echelon form, span the old span plus the main part, and stay in `W`. In
  the second case the main part is in the span and the pair `(0, sifted tag)` is in `W`.
-/

namespace GI.Proved

open GI.Impl

/-- The vector of a list of numbers, over `ZMod p`. -/
def vsF (p : ℕ) (x : List ℕ) : ℕ → ZMod p := fun i => (x.getD i 0 : ZMod p)

theorem vsF_apply (p : ℕ) (x : List ℕ) (i : ℕ) : vsF p x i = (x.getD i 0 : ZMod p) := rfl

theorem vsF_vsLin (p a b : ℕ) {v u : List ℕ} (h : u.length ≤ v.length) :
    vsF p (vsLin p a b v u) = (a : ZMod p) • vsF p v + (b : ZMod p) • vsF p u := by
  funext i
  simp only [vsF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i < v.length
  · rw [vsLin_getD _ _ _ _ _ hi, ZMod.natCast_mod]
    push_cast
    ring
  · have h1 : (vsLin p a b v u).getD i 0 = 0 :=
      List.getD_eq_default _ _ (by rw [vsLin_length]; omega)
    have h2 : v.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
    have h3 : u.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
    rw [h1, h2, h3]
    simp

theorem vsF_vsAxpy {p c : ℕ} (hc : c ≤ p) {x r : List ℕ} (h : r.length ≤ x.length) :
    vsF p (vsAxpy p c x r) = vsF p x - (c : ZMod p) • vsF p r := by
  rw [vsAxpy, vsF_vsLin _ _ _ h, Nat.cast_sub hc, ZMod.natCast_self]
  simp [sub_eq_add_neg]

/-! ### Sifting stays in a submodule -/

/-- The parts of each row are at most as long as those of the pair. -/
def VsShort (xt : List ℕ × List ℕ) (rows : List VsRow) : Prop :=
  ∀ r ∈ rows, r.x.length ≤ xt.1.length ∧ r.t.length ≤ xt.2.length

/-- The entries of the main part are below `p`. -/
def VsBelow (p : ℕ) (xt : List ℕ × List ℕ) : Prop := ∀ y ∈ xt.1, y < p

theorem vsSiftStep_below {p : ℕ} (hp : 0 < p) (xt : List ℕ × List ℕ) (r : VsRow) :
    VsBelow p (vsSiftStep p xt r) := vsLin_lt hp _ _

/-- The step: the main part loses `c` times the row, and so does the tag, where `c` is the
entry of the main part at the pivot. -/
theorem vsSiftStep_vsF {p : ℕ} {xt : List ℕ × List ℕ} (hb : VsBelow p xt) {r : VsRow}
    (hx : r.x.length ≤ xt.1.length) (ht : r.t.length ≤ xt.2.length) :
    vsF p (vsSiftStep p xt r).1 = vsF p xt.1 - vsF p xt.1 r.j • vsF p r.x ∧
      vsF p (vsSiftStep p xt r).2 = vsF p xt.2 - vsF p xt.1 r.j • vsF p r.t := by
  have hc : xt.1.getD r.j 0 ≤ p := by
    by_cases hj : r.j < xt.1.length
    · exact (hb _ (by simp [List.getD_eq_getElem?_getD, hj])).le
    · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _
  exact ⟨vsF_vsAxpy hc hx, vsF_vsAxpy hc ht⟩

/-- The pair of vectors of a vector pair. -/
def vsP (p : ℕ) (xt : List ℕ × List ℕ) : (ℕ → ZMod p) × (ℕ → ZMod p) :=
  (vsF p xt.1, vsF p xt.2)

/-- The pair of vectors of a row. -/
def vsR (p : ℕ) (r : VsRow) : (ℕ → ZMod p) × (ℕ → ZMod p) := (vsF p r.x, vsF p r.t)

theorem vsSiftStep_vsP {p : ℕ} {xt : List ℕ × List ℕ} (hb : VsBelow p xt) {r : VsRow}
    (hx : r.x.length ≤ xt.1.length) (ht : r.t.length ≤ xt.2.length) :
    vsP p (vsSiftStep p xt r) = vsP p xt - vsF p xt.1 r.j • vsR p r := by
  obtain ⟨h1, h2⟩ := vsSiftStep_vsF hb hx ht
  simp only [vsP, vsR, h1, h2, Prod.mk_sub_mk, Prod.smul_mk]

theorem vsSift_below {p : ℕ} (hp : 0 < p) (rows : List VsRow) {xt : List ℕ × List ℕ}
    (hb : VsBelow p xt) : VsBelow p (vsSift p rows xt) := by
  induction rows generalizing xt with
  | nil => exact hb
  | cons r rs ih => exact ih (vsSiftStep_below hp xt r)

theorem vsShort_step {p : ℕ} {xt : List ℕ × List ℕ} {r : VsRow} {rows : List VsRow}
    (h : VsShort xt rows) : VsShort (vsSiftStep p xt r) rows := by
  intro r' hr'
  obtain ⟨e1, e2⟩ := vsSiftStep_length p xt r
  rw [e1, e2]
  exact h r' hr'

/-- **Sifting stays in a submodule.** -/
theorem vsSift_mem {p : ℕ} (hp : 0 < p) (W : Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)))
    (rows : List VsRow) (hr : ∀ r ∈ rows, vsR p r ∈ W) {xt : List ℕ × List ℕ}
    (hb : VsBelow p xt) (hs : VsShort xt rows) (hxt : vsP p xt ∈ W) :
    vsP p (vsSift p rows xt) ∈ W := by
  induction rows generalizing xt with
  | nil => exact hxt
  | cons r rs ih =>
    have hr0 := hs r (by simp)
    refine ih (fun r' hr' => hr r' (by simp [hr'])) (vsSiftStep_below hp xt r)
      (vsShort_step (fun r' hr' => hs r' (by simp [hr']))) ?_
    rw [vsSiftStep_vsP hb hr0.1 hr0.2]
    exact W.sub_mem hxt (W.smul_mem _ (hr r (by simp)))

/-! ### Echelon form -/

/-- Echelon form: each row is `1` at its pivot, and later rows are `0` there. -/
def VsEch (p : ℕ) : List VsRow → Prop
  | [] => True
  | r :: rs => vsF p r.x r.j = 1 ∧ (∀ r' ∈ rs, vsF p r'.x r.j = 0) ∧ VsEch p rs

/-- The span of the main parts of the rows. -/
def vsSpan (p : ℕ) (rows : List VsRow) : Submodule (ZMod p) (ℕ → ZMod p) :=
  Submodule.span (ZMod p) {v | v ∈ rows.map fun r => vsF p r.x}

theorem vsSpan_cons (p : ℕ) (r : VsRow) (rs : List VsRow) :
    vsSpan p (r :: rs) = Submodule.span (ZMod p) (insert (vsF p r.x) {v | v ∈ rs.map fun r =>
      vsF p r.x}) := by
  unfold vsSpan
  congr 1
  ext v
  simp [eq_comm]

theorem vsSpan_nil (p : ℕ) : vsSpan p [] = ⊥ := by
  simp [vsSpan]

theorem vsF_mem_vsSpan (p : ℕ) {rows : List VsRow} {r : VsRow} (hr : r ∈ rows) :
    vsF p r.x ∈ vsSpan p rows :=
  Submodule.subset_span (by simp only [Set.mem_setOf_eq, List.mem_map]; exact ⟨r, hr, rfl⟩)

/-- A vector in the span of rows that are all `0` at `j` is `0` at `j`. -/
theorem vsSpan_apply_zero {p : ℕ} {rows : List VsRow} {j : ℕ} (h : ∀ r ∈ rows, vsF p r.x j = 0)
    {v : ℕ → ZMod p} (hv : v ∈ vsSpan p rows) : v j = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_setOf_eq, List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact h r hr
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

/-- **Triangularity.** A vector in the span of echelon rows that is `0` at every pivot is `0`. -/
theorem vsSpan_eq_zero {p : ℕ} {rows : List VsRow} (he : VsEch p rows) {v : ℕ → ZMod p}
    (hv : v ∈ vsSpan p rows) (hz : ∀ r ∈ rows, v r.j = 0) : v = 0 := by
  induction rows generalizing v with
  | nil => rw [vsSpan_nil] at hv; exact (Submodule.mem_bot _).mp hv
  | cons r rs ih =>
    obtain ⟨h1, h0, hrs⟩ := he
    rw [vsSpan_cons, Submodule.mem_span_insert] at hv
    obtain ⟨a, w, hw, rfl⟩ := hv
    have hw' : w ∈ vsSpan p rs := hw
    have hwj : w r.j = 0 := vsSpan_apply_zero h0 hw'
    have ha : a = 0 := by
      have := hz r (by simp)
      simpa [h1, hwj] using this
    subst ha
    simp only [zero_smul, zero_add] at hz ⊢
    exact ih hrs hw' fun r' hr' => hz r' (by simp [hr'])

/-! ### What sifting does to the main part -/

theorem vsSift_cons (p : ℕ) (r : VsRow) (rs : List VsRow) (xt : List ℕ × List ℕ) :
    vsSift p (r :: rs) xt = vsSift p rs (vsSiftStep p xt r) := rfl

/-- Sifting through rows that are all `0` at `j` keeps the entry at `j`. -/
theorem vsSift_apply_of_zero {p : ℕ} (hp : 0 < p) {rows : List VsRow} {j : ℕ}
    (h : ∀ r ∈ rows, vsF p r.x j = 0) {xt : List ℕ × List ℕ} (hb : VsBelow p xt)
    (hs : VsShort xt rows) : vsF p (vsSift p rows xt).1 j = vsF p xt.1 j := by
  induction rows generalizing xt with
  | nil => rfl
  | cons r rs ih =>
    have hr0 := hs r (by simp)
    rw [vsSift_cons, ih (fun r' hr' => h r' (by simp [hr'])) (vsSiftStep_below hp xt r)
      (vsShort_step (fun r' hr' => hs r' (by simp [hr']))),
      (vsSiftStep_vsF hb hr0.1 hr0.2).1]
    simp [h r (by simp)]

/-- **After sifting, the main part is `0` at every pivot.** -/
theorem vsSift_zero_at {p : ℕ} (hp : 0 < p) {rows : List VsRow} (he : VsEch p rows)
    {xt : List ℕ × List ℕ} (hb : VsBelow p xt) (hs : VsShort xt rows) :
    ∀ r ∈ rows, vsF p (vsSift p rows xt).1 r.j = 0 := by
  induction rows generalizing xt with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨h1, h0, hrs⟩ := he
    have hr0 := hs r (by simp)
    have hs' : VsShort (vsSiftStep p xt r) rs :=
      vsShort_step (fun r' hr' => hs r' (by simp [hr']))
    intro r' hr'
    rw [List.mem_cons] at hr'
    rcases hr' with hrr | hr'
    · rw [hrr, vsSift_cons, vsSift_apply_of_zero hp h0 (vsSiftStep_below hp xt r) hs',
        (vsSiftStep_vsF hb hr0.1 hr0.2).1]
      simp [h1]
    · exact ih hrs (vsSiftStep_below hp xt r) hs' r' hr'

/-- **Sifting changes the main part by a vector in the span of the rows.** -/
theorem vsSift_sub_mem {p : ℕ} (hp : 0 < p) (rows : List VsRow) {xt : List ℕ × List ℕ}
    (hb : VsBelow p xt) (hs : VsShort xt rows) :
    vsF p xt.1 - vsF p (vsSift p rows xt).1 ∈ vsSpan p rows := by
  induction rows generalizing xt with
  | nil => simp [vsSift]
  | cons r rs ih =>
    have hr0 := hs r (by simp)
    have hs' : VsShort (vsSiftStep p xt r) rs :=
      vsShort_step (fun r' hr' => hs r' (by simp [hr']))
    have h1 := ih (vsSiftStep_below hp xt r) hs'
    rw [(vsSiftStep_vsF hb hr0.1 hr0.2).1] at h1
    have hmono : vsSpan p rs ≤ vsSpan p (r :: rs) :=
      Submodule.span_mono fun v hv => by
        simp only [Set.mem_setOf_eq, List.mem_map, List.mem_cons] at hv ⊢
        obtain ⟨r', hr', rfl⟩ := hv
        exact ⟨r', Or.inr hr', rfl⟩
    have h2 : vsF p xt.1 r.j • vsF p r.x ∈ vsSpan p (r :: rs) :=
      Submodule.smul_mem _ _ (vsF_mem_vsSpan p (by simp))
    have := Submodule.add_mem _ (hmono h1) h2
    rw [vsSift_cons]
    convert this using 1
    abel

/-- **The sifted main part is `0` exactly when the main part is in the span of the rows.** -/
theorem vsSift_eq_zero_iff {p : ℕ} (hp : 0 < p) {rows : List VsRow} (he : VsEch p rows)
    {xt : List ℕ × List ℕ} (hb : VsBelow p xt) (hs : VsShort xt rows) :
    vsF p (vsSift p rows xt).1 = 0 ↔ vsF p xt.1 ∈ vsSpan p rows := by
  have hd := vsSift_sub_mem hp rows hb hs
  constructor
  · intro h0
    rw [h0, sub_zero] at hd
    exact hd
  · intro hx
    refine vsSpan_eq_zero he ?_ (vsSift_zero_at hp he hb hs)
    have := Submodule.sub_mem _ hx hd
    rwa [sub_sub_cancel] at this

/-! ### The new row -/

theorem vsEch_append {p : ℕ} {rows : List VsRow} {r : VsRow} (he : VsEch p rows)
    (hz : ∀ r' ∈ rows, vsF p r.x r'.j = 0) (h1 : vsF p r.x r.j = 1) :
    VsEch p (rows ++ [r]) := by
  induction rows with
  | nil => exact ⟨h1, by simp, trivial⟩
  | cons r0 rs ih =>
    obtain ⟨a, b, c⟩ := he
    refine ⟨a, fun r' hr' => ?_, ih c fun r' hr' => hz r' (by simp [hr'])⟩
    have hr'' : r' ∈ rs ++ [r] := hr'
    rw [List.mem_append, List.mem_singleton] at hr''
    rcases hr'' with hr' | hr'
    · exact b r' hr'
    · rw [hr']; exact hz r0 (by simp)

/-- The inverse found by search is the inverse modulo a prime. -/
theorem vsInv_correct {p c : ℕ} (hp : p.Prime) (hc0 : 0 < c) (hcp : c < p) :
    vsInv p c < p ∧ vsInv p c * c % p = 1 := by
  haveI := Fact.mk hp
  have hc : (c : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd hc0 h) (by omega)
  have hex : ∃ s ∈ List.range p, (s * c % p == 1) = true := by
    refine ⟨((c : ZMod p)⁻¹).val, List.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [beq_iff_eq, ← ZMod.val_natCast]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.inv_mul_of_unit _ (Ne.isUnit (G₀ := ZMod p) hc), ZMod.val_one]
  have hlt := List.findIdx_lt_length_of_exists hex
  have hget := List.findIdx_getElem (w := hlt)
  rw [List.getElem_range, beq_iff_eq] at hget
  rw [List.length_range] at hlt
  exact ⟨hlt, hget⟩

theorem vsNzIdx_getD {x : List ℕ} (h : vsNzIdx x < x.length) : 0 < x.getD (vsNzIdx x) 0 := by
  have hget := List.findIdx_getElem (w := h)
  simp only [decide_eq_true_eq] at hget
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact hget

/-- The main part is nonzero exactly when the search finds a nonzero entry. -/
theorem vsNzIdx_lt_iff {p : ℕ} {x : List ℕ} (hb : ∀ y ∈ x, y < p) :
    vsNzIdx x < x.length ↔ vsF p x ≠ 0 := by
  constructor
  · intro h h0
    have hpos := vsNzIdx_getD h
    have hlt : x.getD (vsNzIdx x) 0 < p := hb _ (by simp [List.getD_eq_getElem?_getD, h])
    have := congrFun h0 (vsNzIdx x)
    rw [vsF_apply, Pi.zero_apply, ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd hpos this) (by omega)
  · intro h
    by_contra hk
    have heq : vsNzIdx x = x.length := le_antisymm (vsNzIdx_le x) (by omega)
    have hall := List.findIdx_eq_length.mp heq
    refine h (funext fun i => ?_)
    rw [vsF_apply, Pi.zero_apply]
    by_cases hi : i < x.length
    · have := hall x[i] (List.getElem_mem hi)
      simp only [decide_eq_false_iff_not, not_lt, Nat.le_zero] at this
      simp [List.getD_eq_getElem?_getD, hi, this]
    · rw [List.getD_eq_default _ _ (by omega)]; simp

/-- The parts of the new row are the sifted parts scaled by the inverse. -/
theorem vsNewRow_vsF (p : ℕ) (y : List ℕ × List ℕ) (k : ℕ) :
    vsF p (vsNewRow p y k).x = (vsInv p (y.1.getD k 0) : ZMod p) • vsF p y.1 ∧
      vsF p (vsNewRow p y k).t = (vsInv p (y.1.getD k 0) : ZMod p) • vsF p y.2 := by
  simp [vsNewRow, vsF_vsLin]

theorem vsNewRow_vsR (p : ℕ) (y : List ℕ × List ℕ) (k : ℕ) :
    vsR p (vsNewRow p y k) = (vsInv p (y.1.getD k 0) : ZMod p) • vsP p y := by
  obtain ⟨h1, h2⟩ := vsNewRow_vsF p y k
  simp [vsR, vsP, h1, h2]

/-- The scale factor of the new row is the inverse of the pivot entry. -/
theorem vsNewRow_scale {p : ℕ} (hp : p.Prime) {y : List ℕ × List ℕ} (hb : VsBelow p y)
    (hk : vsNzIdx y.1 < y.1.length) :
    (vsInv p (y.1.getD (vsNzIdx y.1) 0) : ZMod p) * vsF p y.1 (vsNzIdx y.1) = 1 := by
  have hpos := vsNzIdx_getD hk
  have hlt : y.1.getD (vsNzIdx y.1) 0 < p := hb _ (by simp [List.getD_eq_getElem?_getD, hk])
  have h := (vsInv_correct hp hpos hlt).2
  rw [vsF_apply, ← Nat.cast_mul, ← ZMod.natCast_mod, h, Nat.cast_one]

theorem vsSpan_append (p : ℕ) (rows : List VsRow) (r : VsRow) :
    vsSpan p (rows ++ [r]) = vsSpan p rows ⊔ Submodule.span (ZMod p) {vsF p r.x} := by
  unfold vsSpan
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp [eq_comm, or_comm]

/-! ### The insertion -/

/-- **Insertion, new row.** If the sifted main part is nonzero, the new rows are in echelon
form, their span is the old span plus the main part, and the new row lies in every submodule
of pairs that holds the pair and the old rows. -/
theorem vsInsert_new {p : ℕ} (hp : p.Prime) {rows : List VsRow} (he : VsEch p rows)
    {xt : List ℕ × List ℕ} (hb : VsBelow p xt) (hs : VsShort xt rows)
    (hk : vsNzIdx (vsSift p rows xt).1 < (vsSift p rows xt).1.length) :
    VsEch p (rows ++ [vsNewRow p (vsSift p rows xt) (vsNzIdx (vsSift p rows xt).1)]) ∧
    vsSpan p (rows ++ [vsNewRow p (vsSift p rows xt) (vsNzIdx (vsSift p rows xt).1)]) =
      vsSpan p rows ⊔ Submodule.span (ZMod p) {vsF p xt.1} ∧
    ∀ W : Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)), (∀ r ∈ rows, vsR p r ∈ W) →
      vsP p xt ∈ W →
      vsR p (vsNewRow p (vsSift p rows xt) (vsNzIdx (vsSift p rows xt).1)) ∈ W := by
  have hp0 := hp.pos
  have hyb := vsSift_below hp0 rows hb
  have hz := vsSift_zero_at hp0 he hb hs
  have hd := vsSift_sub_mem hp0 rows hb hs
  have hscale := vsNewRow_scale hp hyb hk
  obtain ⟨hx, -⟩ := vsNewRow_vsF p (vsSift p rows xt) (vsNzIdx (vsSift p rows xt).1)
  set y := vsSift p rows xt
  set k := vsNzIdx y.1
  set s : ZMod p := (vsInv p (y.1.getD k 0) : ZMod p)
  haveI := Fact.mk hp
  have hs0 : s ≠ 0 := fun h0 => by rw [h0, zero_mul] at hscale; exact zero_ne_one hscale
  refine ⟨vsEch_append he (fun r' hr' => ?_) ?_, ?_, fun W hW hxt => ?_⟩
  · rw [hx, Pi.smul_apply, hz r' hr', smul_zero]
  · rw [hx, Pi.smul_apply, smul_eq_mul]; exact hscale
  · rw [vsSpan_append, hx]
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
      have e : s • vsF p y.1 = s • (vsF p xt.1 - (vsF p xt.1 - vsF p y.1)) := by
        rw [sub_sub_cancel]
      rw [SetLike.mem_coe, e]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.mem_sup_left hd))
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    · refine sup_le le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
      have e : vsF p xt.1 = (vsF p xt.1 - vsF p y.1) + s⁻¹ • (s • vsF p y.1) := by
        rw [smul_smul, ZMod.inv_mul_of_unit _ (Ne.isUnit (G₀ := ZMod p) hs0), one_smul, sub_add_cancel]
      rw [SetLike.mem_coe, e]
      refine Submodule.add_mem _ (Submodule.mem_sup_left hd) (Submodule.smul_mem _ _ ?_)
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  · rw [vsNewRow_vsR]
    exact W.smul_mem _ (vsSift_mem hp0 W rows hW hb hs hxt)

/-- **Insertion, relation.** If the sifted main part is zero, the main part lies in the span
of the rows, and the pair `(0, sifted tag)` lies in every submodule of pairs that holds the
pair and the rows. -/
theorem vsInsert_rel {p : ℕ} (hp : 0 < p) {rows : List VsRow} (he : VsEch p rows)
    {xt : List ℕ × List ℕ} (hb : VsBelow p xt) (hs : VsShort xt rows)
    (hk : ¬ vsNzIdx (vsSift p rows xt).1 < (vsSift p rows xt).1.length) :
    vsF p xt.1 ∈ vsSpan p rows ∧
    ∀ W : Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)), (∀ r ∈ rows, vsR p r ∈ W) →
      vsP p xt ∈ W → ((0 : ℕ → ZMod p), vsF p (vsSift p rows xt).2) ∈ W := by
  have h0 : vsF p (vsSift p rows xt).1 = 0 := by
    by_contra hne
    exact hk ((vsNzIdx_lt_iff (vsSift_below hp rows hb)).mpr hne)
  refine ⟨(vsSift_eq_zero_iff hp he hb hs).mp h0, fun W hW hxt => ?_⟩
  have := vsSift_mem hp W rows hW hb hs hxt
  rwa [vsP, h0] at this

end GI.Proved
