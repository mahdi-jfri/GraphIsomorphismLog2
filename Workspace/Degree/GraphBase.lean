module

public import Workspace.Degree.GraphLevProg
public import Workspace.Degree.GraphPairs

/-!
# The shared data of a step

* `bv D ℓ r`: the numbers and tables that all functions of a step read.
* `WB n`: a bound on the weights of all values of a step.
* `fwdV`: the table of forward neighbours as a value.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

/-- A bound on the number of positions of a query. -/
def kB (n : ℕ) : ℕ := (n * (n + 6)) ^ 2

/-- A bound on the weights of the values of a step. -/
def WB (n : ℕ) : ℕ := 1000 * (kB n + n + 10) ^ 5

theorem WB_poly : PolyB WB := by
  unfold WB kB
  poly

theorem WB_ge (n : ℕ) : 1000 * (kB n + n + 10) ≤ WB n := by
  have h : kB n + n + 10 ≤ (kB n + n + 10) ^ 5 := Nat.le_self_pow (by omega) _
  simp only [WB]
  omega

theorem le_WB (n : ℕ) : kB n + n + 1000 ≤ WB n := by
  have := WB_ge n
  omega

theorem levB_le_WB (n : ℕ) : levB n ≤ WB n := by
  have h1 : n + 1 ≤ kB n + n + 10 := by omega
  have h2 : (n + 1) ^ 2 ≤ (kB n + n + 10) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (kB n + n + 10) ^ 2 ≤ (kB n + n + 10) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  simp only [levB, WB]
  omega

/-- The sizes of a step. -/
structure Sz (n D : ℕ) : Prop where
  pos : 0 < n
  six : 6 ≤ D
  le : D ≤ n + 6

variable {n D : ℕ}

theorem Sz.m_le (h : Sz n D) : n * D ≤ n * (n + 6) := Nat.mul_le_mul_left _ h.le

theorem Sz.k_le (h : Sz n D) : n * D * (n * D) ≤ kB n := by
  have := Nat.mul_le_mul h.m_le h.m_le
  simpa [kB, sq] using this

theorem Sz.m_le_k (h : Sz n D) : n * D ≤ n * D * (n * D) :=
  Nat.le_mul_of_pos_left _ (Nat.mul_pos h.pos (by have := h.six; omega))

theorem Sz.m_pos (h : Sz n D) : 0 < n * D := Nat.mul_pos h.pos (by have := h.six; omega)

theorem nat_wt {n k : ℕ} (hk : k ≤ kB n + n + 10) : (Val.nat k).wt ≤ WB n := by
  have := wt_nat_le k
  have := WB_ge n
  omega

theorem table_wt {m : ℕ} {f : Fin m → ℕ} (hm : m ≤ kB n + n) (hf : ∀ i, f i ≤ m) :
    (encFun f).wt ≤ WB n := by
  have h1 := wt_encFun_le_sq f hf
  have h2 : (m + 1) ^ 2 ≤ (kB n + n + 10) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : (kB n + n + 10) ^ 2 ≤ (kB n + n + 10) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  simp only [WB]
  omega

/-- The numbers and tables that all functions of a step read. -/
def bv (D : ℕ) (ℓ : Fin n → ℕ) (r : ℕ) : Val :=
  .list [.nat n, .nat D, .nat (n * D), .nat (n * D * (n * D)), encFun ℓ, ids n, ids (n * D),
    ids (n * D * (n * D)), .nat r]

theorem bv_wt (h : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) :
    (bv D ℓ r).wt ≤ 40 * WB n := by
  have h0 := WB_ge n
  have hk := h.k_le
  have hm := h.m_le_k
  have hD : D ≤ n * D := Nat.le_mul_of_pos_left _ h.pos
  have w : (bv D ℓ r).wt ≤ 9 * (2 * WB n + 1) + 4 := by
    refine wt_lit _ fun v hv => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact nat_wt (by omega)
    · exact nat_wt (by omega)
    · exact nat_wt (by omega)
    · exact nat_wt (by omega)
    · exact table_wt (by omega) hℓ
    · exact table_wt (by omega) fun i => i.isLt.le
    · exact table_wt (by omega) fun i => i.isLt.le
    · exact table_wt (by omega) fun i => i.isLt.le
    · exact nat_wt (by omega)
  omega

/-- Reading a field of `bv`. -/
theorem Lv.bvGet {P : Program} {env : List Val} {T ma j : ℕ} {e : Expr} {D : ℕ} {ℓ : Fin n → ℕ}
    {r : ℕ} (he : Lv P env T e (bv D ℓ r) ma) {w : Val} (hj : j ≤ 8)
    (hw : [Val.nat n, .nat D, .nat (n * D), .nat (n * D * (n * D)), encFun ℓ, ids n, ids (n * D),
      ids (n * D * (n * D)), .nat r][j]? = some w) (hT : 11 ≤ T) :
    Lv P env T (.get e (.nat j)) w (2 * ma + 2) :=
  Lv.get he (Lv.nat j (by omega)) hw

/-- The table of forward neighbours as a value. -/
noncomputable def fwdV (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) : Val :=
  .list ((List.finRange n).map fun u => flist (fwd ℓ X u))

theorem flist_wt {m : ℕ} (l : List (Fin m)) (hl : l.length ≤ m) (hm : m ≤ kB n + n) :
    (flist l).wt ≤ WB n := by
  have h1 := wt_natList_le_sq (xs := l.map fun z : Fin m => (z : ℕ)) (B := m)
    (by simp only [List.mem_map]; rintro _ ⟨z, -, rfl⟩; exact z.isLt.le) (by simpa using hl)
  have h2 : (m + 1) ^ 2 ≤ (kB n + n + 10) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : (kB n + n + 10) ^ 2 ≤ (kB n + n + 10) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have e : flist l = natList (l.map fun z : Fin m => (z : ℕ)) := by
    simp [flist, natList]
  rw [e]
  simp only [WB]
  omega

theorem length_fwd_le (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) (u : Fin n) :
    (fwd ℓ X u).length ≤ n := by
  have := List.length_filter_le (p := fun w => (open Classical in decide (X.Adj u w ∧ ℓ w = ℓ u + 1)))
    (List.finRange n)
  simpa [fwd] using this

theorem fwdV_wt (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) : (fwdV ℓ X).wt ≤ (n + 1) * (2 * WB n + 1) + 4 := by
  have := wt_listFin_le (fun u => flist (fwd ℓ X u)) (B := WB n) fun u =>
    flist_wt _ (length_fwd_le ℓ X u) (by omega)
  exact this.trans (by nlinarith)

/-- Reading a table. -/
theorem Lv.tget {P : Program} {env : List Val} {T ma mb : ℕ} {e i : Expr} {m : ℕ}
    {f : Fin m → ℕ} (he : Lv P env T e (encFun f) ma) {z : Fin m}
    (hi : Lv P env T i (.nat z) mb) : Lv P env T (.get e i) (.nat (f z)) (2 * ma + mb + 1) :=
  Lv.get (vs := (List.finRange m).map fun i => .nat (f i)) he hi (listFin_get _ z)

/-- Reading a permutation. -/
theorem Lv.pget {P : Program} {env : List Val} {T ma mb : ℕ} {e i : Expr} {m : ℕ}
    {U : Perm (Fin m)} (he : Lv P env T e (encPerm U) ma) {z : Fin m}
    (hi : Lv P env T i (.nat z) mb) : Lv P env T (.get e i) (.nat (U z)) (2 * ma + mb + 1) := by
  rw [encPerm_eq_encFun] at he
  exact Lv.tget (f := fun i => (U i : ℕ)) he hi

open Classical in
/-- A cell of an adjacency table, as a number. -/
noncomputable def adjN (Y : SimpleGraph (Fin n)) (a b : Fin n) : ℕ := if Y.Adj a b then 1 else 0

theorem adjN_le (Y : SimpleGraph (Fin n)) (a b : Fin n) : adjN Y a b ≤ 1 := by
  unfold adjN
  split <;> omega

/-- Reading a cell of an adjacency table. -/
theorem Lv.aget {P : Program} {env : List Val} {T ma mb mc : ℕ} {a z u : Expr}
    {Y : SimpleGraph (Fin n)} (ha : Lv P env T a (adjVal Y) ma) {x y : Fin n}
    (hz : Lv P env T z (.nat x) mb) (hu : Lv P env T u (.nat y) mc) :
    Lv P env T (adjE a z u) (.nat (adjN Y x y)) (2 * (2 * ma + mb + 1) + mc + 1) := by
  classical
  have h1 := Lv.get (vs := (List.finRange n).map fun i : Fin n =>
    encFun fun j : Fin n => if Y.Adj i j then 1 else 0) ha hz (listFin_get _ x)
  exact Lv.tget (f := fun j : Fin n => adjN Y x j) h1 hu

theorem adjVal_wt (Y : SimpleGraph (Fin n)) : (adjVal Y).wt ≤ WB n :=
  (wt_adjVal_le Y).trans (levB_le_WB n)

theorem perm_wt {m : ℕ} (hm : m ≤ kB n + n) (U : Perm (Fin m)) : (encPerm U).wt ≤ WB n := by
  rw [encPerm_eq_encFun]
  exact table_wt hm fun i => (U i).isLt.le

/-- A value that is a point. -/
theorem fin_wt {m : ℕ} (hm : m ≤ kB n + n) (z : Fin m) : (Val.nat z).wt ≤ WB n :=
  nat_wt (by have := z.isLt; omega)

theorem table_wt' {m B : ℕ} {f : Fin m → ℕ} (hm : m ≤ kB n + n) (hB : B ≤ kB n + n)
    (hf : ∀ i, f i ≤ B) : (encFun f).wt ≤ WB n := by
  have h1 := wt_encFun_le f hf
  have h2 : m * (2 * B + 5) + 4 ≤ (kB n + n + 10) * (2 * (kB n + n + 10)) := by nlinarith
  have h3 : (kB n + n + 10) ^ 2 ≤ (kB n + n + 10) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  simp only [WB]
  nlinarith

/-- A bound on one entry of a context. -/
def VB (n : ℕ) : ℕ := (n + 1) * (2 * WB n + 1) + 4 + 40 * WB n

theorem VB_poly : PolyB VB := by
  have := WB_poly
  unfold VB
  poly

theorem WB_le_VB (n : ℕ) : 40 * WB n ≤ VB n := by
  simp only [VB]; omega

theorem fwdV_le_VB (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) : (fwdV ℓ X).wt ≤ VB n :=
  (fwdV_wt ℓ X).trans (by simp only [VB]; omega)

/-- The table of a list function as a value. -/
def fV (F : Fin n → List (Fin n)) : Val := .list ((List.finRange n).map fun u => flist (F u))

theorem fwdV_eq (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) : fwdV ℓ X = fV (fwd ℓ X) := rfl

theorem Lv.fget {P : Program} {env : List Val} {T ma mb : ℕ} {e i : Expr}
    {F : Fin n → List (Fin n)} (he : Lv P env T e (fV F) ma) {z : Fin n}
    (hi : Lv P env T i (.nat z) mb) : Lv P env T (.get e i) (flist (F z)) (2 * ma + mb + 1) :=
  Lv.get (vs := (List.finRange n).map fun u => flist (F u)) he hi (listFin_get _ z)

theorem Lv.flen {P : Program} {env : List Val} {T ma : ℕ} {e : Expr} {m : ℕ} {l : List (Fin m)}
    (he : Lv P env T e (flist l) ma) (hT : 3 ≤ T) :
    Lv P env T (.length e) (.nat l.length) (2 * ma + 1) := by
  have := Lv.length (vs := l.map fun z : Fin m => Val.nat (z : ℕ)) he hT
  simpa using this

theorem Lv.felem {P : Program} {env : List Val} {T ma mb : ℕ} {e i : Expr} {m : ℕ}
    {l : List (Fin m)} {x : ℕ} {w : Fin m} (he : Lv P env T e (flist l) ma)
    (hi : Lv P env T i (.nat x) mb) (hx : l[x]? = some w) :
    Lv P env T (.get e i) (.nat w) (2 * ma + mb + 1) :=
  Lv.get (vs := l.map fun z : Fin m => Val.nat (z : ℕ)) he hi (by simp [hx])

theorem slot_div (s : Fin (n * D)) : (s : ℕ) / D = ((slotE n D).symm s).1 := by
  obtain ⟨⟨u, i⟩, rfl⟩ := (slotE n D).surjective s
  simp only [Equiv.symm_apply_apply, slotE_val]
  have hi := i.isLt
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem slot_mod (s : Fin (n * D)) : (s : ℕ) % D = ((slotE n D).symm s).2 := by
  obtain ⟨⟨u, i⟩, rfl⟩ := (slotE n D).surjective s
  simp only [Equiv.symm_apply_apply, slotE_val]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

theorem pair_div {m : ℕ} (p : Fin (m * m)) : (p : ℕ) / m = ((pairE m).symm p).1 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (pairE m).surjective p
  simp only [Equiv.symm_apply_apply, pairE_val]
  have hi := b.isLt
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem pair_mod {m : ℕ} (p : Fin (m * m)) : (p : ℕ) % m = ((pairE m).symm p).2 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (pairE m).surjective p
  simp only [Equiv.symm_apply_apply, pairE_val]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]

end GI.Degree
