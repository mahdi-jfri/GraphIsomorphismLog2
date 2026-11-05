/-
**Reading the input graphs.** `decodeFuns b` is a program of twelve functions at base `b`. On the
input value `inputVal G H` it returns `[n, adjVal G, adjVal H]`, where `adjVal G` is the
adjacency matrix of `G` as a list of rows, and row `i` is `encFun` of the function
`j ↦ if G.Adj i j then 1 else 0` (`decode_inputVal`). Its cost is polynomial in `n`.

The work is done for any list of numbers `cs` (the cells): `matVal cs n off` is the `n` by `n`
matrix whose entry `(i, j)` is cell `off + n * i + j`. A row is a `map` over the points that reads
cells, and the matrix is a `map` over the points that builds rows.
-/
module

public import Workspace.Lang.Lib.Orbit
public import Workspace.Lang.Glue

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)

variable {n : ℕ}

/-- The weight of a list indexed by `Fin n`, from a bound on each entry. -/
theorem wt_listFin_le (F : Fin n → Val) {B : ℕ} (hF : ∀ i, (F i).wt ≤ B) :
    (Val.list ((List.finRange n).map F)).wt ≤ n * (2 * B + 1) + 4 := by
  have h1 := wt_list_le ((List.finRange n).map F)
  have h2 : (((List.finRange n).map F).map Val.wt).sum ≤ n * B := by
    have := List.sum_le_card_nsmul (((List.finRange n).map F).map Val.wt) B (by
      simp only [List.map_map, List.mem_map, List.mem_finRange, true_and, Function.comp_apply,
        forall_exists_index, forall_apply_eq_imp_iff]
      exact hF)
    simpa using this
  simp only [List.length_map, List.length_finRange] at h1
  nlinarith

/-- Row `i` of the matrix: the cells `base, …, base + n - 1`. -/
def rowVal (cs : List ℕ) (n base : ℕ) : Val := encFun fun j : Fin n => cs.getD (base + j) 0

/-- The `n` by `n` matrix whose entry `(i, j)` is cell `off + n * i + j`. -/
def matVal (cs : List ℕ) (n off : ℕ) : Val :=
  .list ((List.finRange n).map fun i : Fin n => rowVal cs n (off + n * i))

theorem getD_le {cs : List ℕ} {B : ℕ} (hcs : ∀ x ∈ cs, x ≤ B) (a : ℕ) : cs.getD a 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : cs[a]? with _ | x
  · simp
  · exact hcs x (List.mem_of_getElem? h)

theorem wt_rowVal_le {cs : List ℕ} (hcs : ∀ x ∈ cs, x ≤ n + 1) (base : ℕ) :
    (rowVal cs n base).wt ≤ 8 * (n + 1) ^ 2 := by
  have := wt_encFun_le (fun j : Fin n => cs.getD (base + j) 0) (B := n + 1)
    fun j => getD_le hcs _
  rw [rowVal]; nlinarith

theorem wt_matVal_le {cs : List ℕ} (hcs : ∀ x ∈ cs, x ≤ n + 1) (off : ℕ) :
    (matVal cs n off).wt ≤ 21 * (n + 1) ^ 3 := by
  have := wt_listFin_le (fun i : Fin n => rowVal cs n (off + n * i)) (B := 8 * (n + 1) ^ 2)
    fun i => wt_rowVal_le hcs _
  rw [matVal]; nlinarith

/-! ### One cell -/

/-- On `[[cells, base], j]`: cell `base + j`. -/
def cellF : Expr :=
  .get (.get (arg 0) (.nat 0)) (.arith .add (.get (arg 0) (.nat 1)) (arg 1))

theorem cellF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some cellF) (cs : List ℕ)
    (base j : ℕ) (hj : base + j < cs.length) :
    FunDet P f (.list [.list [.list (cs.map .nat), .nat base], .nat j])
      (.nat (cs.getD (base + j) 0))
      (50 * ((Val.list (cs.map .nat)).wt + base + j + 10)) := by
  set V := Val.list (cs.map .nat) with hV
  set A := Val.list [.list [V, .nat base], .nat j] with hA
  have g0 := Det.get' (P := P) (env := [A]) (Det.arg' (rest := []) (j := 0) rfl) (Det.nat 0)
    (show [V, Val.nat base][0]? = some V from rfl)
  have gb := Det.get' (P := P) (env := [A]) (Det.arg' (rest := []) (j := 0) rfl) (Det.nat 1)
    (show [V, Val.nat base][1]? = some (.nat base) from rfl)
  have ga := Det.arith' (op := .add) (z := base + j) gb (Det.arg' (rest := []) (j := 1) rfl) rfl
  have hv : (cs.map Val.nat)[base + j]? = some (.nat (cs.getD (base + j) 0)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  refine FunDet.intro hf ((Det.get' g0 ga hv).mono ?_)
  have e : (Val.list [Val.list [V, .nat base], .nat j]).wt = A.wt := rfl
  have h1 := wt_list2_le V (.nat base)
  have h2 := wt_list2_le (.list [V, .nat base]) (.nat j)
  have h3 := wt_nat_le base
  have h4 := wt_nat_le j
  have h5 := wt_nat_le (cs.getD (base + j) 0)
  have h6 : (Val.nat (cs.getD (base + j) 0)).wt < V.wt := by
    have hm : cs.getD (base + j) 0 ∈ cs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    rw [hV]; exact wt_le_wt_list (List.mem_map_of_mem hm)
  omega

/-! ### One row -/

/-- `map cellF`, at base `b` (four functions): on `[[cells, base], [0, …, n - 1]]`, the row
`rowVal cs n base`. -/
def rowMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [cellF]

theorem rowMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (rowMapFuns b)) {cs : List ℕ}
    (hcs : ∀ x ∈ cs, x ≤ n + 1) (base : ℕ) (hb : base + n ≤ cs.length) :
    FunDet P b (.list [.list [.list (cs.map .nat), .nat base], encFun fun x : Fin n => (x : ℕ)])
      (rowVal cs n base)
      (5000 * (n + 1) * ((Val.list (cs.map .nat)).wt + base + 10 * (n + 1) ^ 2)) := by
  have hf : P.funs[b + 3]? = some cellF := by
    simpa [rowMapFuns, mapFuns, loopFuns] using h.right.single
  set V := Val.list (cs.map .nat) with hV
  have hM := map_spec (c := .list [V, .nat base])
    (xs := (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)) h.left
    (R := fun x w => ∀ j : Fin n, x = .nat j → w = .nat (cs.getD (base + j) 0))
    (B := fun _ => 50 * (V.wt + base + n + 10)) (by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (cellF_spec hf cs base j (by omega)) fun w c hw => ⟨fun j' hj' => ?_, ?_⟩
      · have : j' = j := Fin.ext (by simpa using hj'.symm)
        rw [hw.1, this]
      · have := hw.2
        have := j.isLt
        have e : V.wt = (Val.list (cs.map .nat)).wt := rfl
        show c ≤ 50 * (V.wt + base + n + 10)
        omega)
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = (List.finRange n).map fun j : Fin n => Val.nat (cs.getD (base + j) 0) :=
    forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map, List.length_finRange, sum_const_finRange] at hc
  have h1 := wt_rowVal_le (n := n) hcs base
  have h4 := wt_encFun_le_sq (fun x : Fin n => (x : ℕ)) fun x => x.isLt.le
  have h5 := wt_list2_le V (.nat base)
  have h6 := wt_list2_le (.list [V, .nat base]) (encFun fun x : Fin n => (x : ℕ))
  have h7 := wt_nat_le base
  have e1 : (Val.list [.list [V, .nat base],
      .list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))]).wt =
    (Val.list [.list [V, .nat base], encFun fun x : Fin n => (x : ℕ)]).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun j : Fin n => Val.nat (cs.getD (base + j) 0))).wt
    = (rowVal cs n base).wt := rfl
  rw [e1, e2] at hc
  have hN : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN' : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h8 : n * (50 * (V.wt + base + n + 10)) ≤ (n + 1) * (50 * (V.wt + base + n + 10)) :=
    Nat.mul_le_mul_right _ (by omega)
  have h9 : mapK * (n + 1) * ((Val.list [.list [V, .nat base],
      encFun fun x : Fin n => (x : ℕ)]).wt + (rowVal cs n base).wt + 1) ≤
      (n + 1) * (1000 * (4 * V.wt + 4 * base + 16 * (n + 1) ^ 2 + 27)) := by
    rw [show mapK * (n + 1) = (n + 1) * 1000 by simp only [mapK]; ring, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  have h10 : (n + 1) * (50 * (V.wt + base + n + 10)) +
      (n + 1) * (1000 * (4 * V.wt + 4 * base + 16 * (n + 1) ^ 2 + 27)) ≤
      (n + 1) * (5000 * (V.wt + base + 10 * (n + 1) ^ 2)) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have e3 : (n + 1) * (5000 * (V.wt + base + 10 * (n + 1) ^ 2)) =
    5000 * (n + 1) * (V.wt + base + 10 * (n + 1) ^ 2) := by ring
  omega

/-! ### The matrix -/

/-- On `[[cells, n, ids, off], i]`: row `i`, which starts at cell `off + n * i`. -/
def rowF (rm : ℕ) : Expr :=
  .call rm (mk2 (mk2 (.get (arg 0) (.nat 0))
      (.arith .add (.get (arg 0) (.nat 3)) (.arith .mul (.get (arg 0) (.nat 1)) (arg 1))))
    (.get (arg 0) (.nat 2)))

theorem rowF_spec {P : Program} {f rm : ℕ} (hf : P.funs[f]? = some (rowF rm))
    (hrm : P.HasAt rm (rowMapFuns rm)) {cs : List ℕ} (hcs : ∀ x ∈ cs, x ≤ n + 1) (off : ℕ)
    (hoff : off + n * n ≤ cs.length) (i : Fin n) :
    FunDet P f (.list [.list [.list (cs.map .nat), .nat n, encFun (fun x : Fin n => (x : ℕ)),
        .nat off], .nat i]) (rowVal cs n (off + n * i))
      (6000 * (n + 1) * ((Val.list (cs.map .nat)).wt + off + 11 * (n + 1) ^ 2)) := by
  set V := Val.list (cs.map .nat) with hV
  set ids := encFun (fun x : Fin n => (x : ℕ)) with hids
  set c := Val.list [V, .nat n, ids, .nat off] with hc
  set A := Val.list [c, .nat i] with hA
  have g0 := Det.get' (P := P) (env := [A]) (Det.arg' (rest := []) (j := 0) rfl) (Det.nat 0)
    (show [V, .nat n, ids, .nat off][0]? = some V from rfl)
  have g1 := Det.get' (P := P) (env := [A]) (Det.arg' (rest := []) (j := 0) rfl) (Det.nat 1)
    (show [V, .nat n, ids, .nat off][1]? = some (.nat n) from rfl)
  have g2 := Det.get' (P := P) (env := [A]) (Det.arg' (rest := []) (j := 0) rfl) (Det.nat 2)
    (show [V, .nat n, ids, .nat off][2]? = some ids from rfl)
  have g3 := Det.get' (P := P) (env := [A]) (Det.arg' (rest := []) (j := 0) rfl) (Det.nat 3)
    (show [V, .nat n, ids, .nat off][3]? = some (.nat off) from rfl)
  have gm := Det.arith' (op := .mul) (z := n * i) g1 (Det.arg' (rest := []) (j := 1) rfl) rfl
  have ga := Det.arith' (op := .add) (z := off + n * i) g3 gm rfl
  have hi := i.isLt
  have hni : n * i + n ≤ n * n := by
    have := Nat.mul_le_mul_left n (show (i : ℕ) + 1 ≤ n by omega)
    rw [Nat.mul_succ] at this; exact this
  refine FunDet.intro hf ((Det.call (Det.mk2 (Det.mk2 g0 ga) g2)
    (rowMap_spec hrm hcs (off + n * i) (by omega))).mono ?_)
  have e1 : (Val.list [c, .nat i]).wt = A.wt := rfl
  have e2 : (Val.list [V, .nat n, ids, .nat off]).wt = c.wt := rfl
  have h1 := wt_list4_le V (.nat n) ids (.nat off)
  have h2 := wt_list2_le c (.nat i)
  have h3 := wt_list2_le V (.nat (off + n * i))
  have h4 := wt_list2_le (.list [V, .nat (off + n * i)]) ids
  have h5 := wt_encFun_le_sq (fun x : Fin n => (x : ℕ)) fun x => x.isLt.le
  have h6 := wt_rowVal_le (n := n) hcs (off + n * i)
  have h7 := wt_nat_le n
  have h8 := wt_nat_le off
  have h9 := wt_nat_le i
  have h10 := wt_nat_le (off + n * i)
  have h11 := wt_nat_le (n * i)
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hnn : n * n ≤ (n + 1) ^ 2 := by nlinarith
  have eV : (Val.list (cs.map .nat)).wt = V.wt := rfl
  have eI : (encFun (fun x : Fin n => (x : ℕ))).wt = ids.wt := rfl
  rw [eV]
  have h12 : 5000 * (n + 1) * (V.wt + (off + n * i) + 10 * (n + 1) ^ 2) ≤
      5000 * (n + 1) * (V.wt + off + 11 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have h13 : 1000 * (V.wt + off + 11 * (n + 1) ^ 2) ≤
      1000 * (n + 1) * (V.wt + off + 11 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have e3 : 6000 * (n + 1) * (V.wt + off + 11 * (n + 1) ^ 2) =
    5000 * (n + 1) * (V.wt + off + 11 * (n + 1) ^ 2) +
      1000 * (n + 1) * (V.wt + off + 11 * (n + 1) ^ 2) := by ring
  omega

/-- `map rowF`, at base `b` (eight functions): on `[[cells, n, ids, off], ids]`, the matrix
`matVal cs n off`. -/
def matFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [rowF (b + 4)] ++ rowMapFuns (b + 4)

theorem mat_spec {P : Program} {b : ℕ} (h : P.HasAt b (matFuns b)) {cs : List ℕ}
    (hcs : ∀ x ∈ cs, x ≤ n + 1) (off : ℕ) (hoff : off + n * n ≤ cs.length) :
    FunDet P b (.list [.list [.list (cs.map .nat), .nat n, encFun (fun x : Fin n => (x : ℕ)),
        .nat off], encFun (fun x : Fin n => (x : ℕ))]) (matVal cs n off)
      (14000 * (n + 1) ^ 2 * ((Val.list (cs.map .nat)).wt + off + 11 * (n + 1) ^ 2)) := by
  have hf : P.funs[b + 3]? = some (rowF (b + 4)) := by
    simpa [mapFuns, loopFuns] using h.left.right.single
  have hrm : P.HasAt (b + 4) (rowMapFuns (b + 4)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.right
  set V := Val.list (cs.map .nat) with hV
  set ids := encFun (fun x : Fin n => (x : ℕ)) with hids
  set c := Val.list [V, .nat n, ids, .nat off] with hc
  set Z := V.wt + off + 11 * (n + 1) ^ 2 with hZ
  have hM := map_spec (c := c)
    (xs := (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)) h.left.left
    (R := fun x w => ∀ i : Fin n, x = .nat i → w = rowVal cs n (off + n * i))
    (B := fun _ => 6000 * (n + 1) * Z) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (rowF_spec hf hrm hcs off hoff i) fun w c hw => ⟨fun i' hi' => ?_, hw.2⟩
      have : i' = i := Fin.ext (by simpa using hi'.symm)
      rw [hw.1, this])
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc'⟩ := hw
  have hws' : ws = (List.finRange n).map fun i : Fin n => rowVal cs n (off + n * i) :=
    forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map, List.length_finRange, sum_const_finRange] at hc'
  have e1 : (Val.list [c, .list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))]).wt =
    (Val.list [c, ids]).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun i : Fin n => rowVal cs n (off + n * i))).wt =
    (matVal cs n off).wt := rfl
  rw [e1, e2] at hc'
  have e3 : (Val.list [V, .nat n, ids, .nat off]).wt = c.wt := rfl
  have h1 := wt_list4_le V (.nat n) ids (.nat off)
  have h2 := wt_list2_le c ids
  have h3 := wt_encFun_le_sq (fun x : Fin n => (x : ℕ)) fun x => x.isLt.le
  have h4 := wt_matVal_le (n := n) hcs off
  have h5 := wt_nat_le n
  have h6 := wt_nat_le off
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have eV : (Val.list (cs.map .nat)).wt = V.wt := rfl
  have eI : (encFun (fun x : Fin n => (x : ℕ))).wt = ids.wt := rfl
  have h3' : 21 * (n + 1) ^ 3 ≤ 2 * ((n + 1) * Z) := by
    have : (n + 1) ^ 3 = (n + 1) * (n + 1) ^ 2 := by ring
    rw [this]
    have : 21 * (n + 1) ^ 2 ≤ 2 * Z := by omega
    nlinarith
  have hZ1 : Z ≤ (n + 1) * Z := Nat.le_mul_of_pos_left _ (by omega)
  have h7 : n * (6000 * (n + 1) * Z) ≤ 6000 * (n + 1) ^ 2 * Z := by
    have : n * (6000 * (n + 1) * Z) = 6000 * (n * (n + 1)) * Z := by ring
    rw [this, pow_two]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
  have h8 : mapK * (n + 1) * ((Val.list [c, ids]).wt + (matVal cs n off).wt + 1) ≤
      mapK * (n + 1) * (8 * ((n + 1) * Z)) := Nat.mul_le_mul_left _ (by omega)
  have e4 : mapK * (n + 1) * (8 * ((n + 1) * Z)) = 8000 * (n + 1) ^ 2 * Z := by
    simp only [mapK]; ring
  have e5 : 14000 * (n + 1) ^ 2 * Z = 6000 * (n + 1) ^ 2 * Z + 8000 * (n + 1) ^ 2 * Z := by ring
  omega

/-! ### The whole decoder -/

/-- The entry: on the cells, read `n`, build `ids = range n`, and build the two matrices, which
start at cells `1` and `1 + n * n`. -/
def decodeEntry (b : ℕ) : Expr :=
  .letE (.get (.var 0) (.nat 0))
    (.letE (.call (b + 1) (.var 1))
      (mk3 (.var 1)
        (.call (b + 4) (mk2 (mk4 (.var 0) (.var 1) (.var 2) (.nat 1)) (.var 2)))
        (.call (b + 4) (mk2 (mk4 (.var 0) (.var 1) (.var 2)
          (.arith .add (.nat 1) (.arith .mul (.var 1) (.var 1)))) (.var 2)))))

/-- **The decoder**, at base `b` (twelve functions). -/
def decodeFuns (b : ℕ) : List Expr := [decodeEntry b] ++ rangeFuns (b + 1) ++ matFuns (b + 4)

/-- The constant of the cost bound of the decoder. -/
def decodeK : ℕ := 400000

/-- **Decoding a list of cells.** If cell 0 is `n`, every cell is at most `n + 1`, and there are
at least `1 + 2 * (n * n)` cells, the decoder returns `n` and the two matrices that start at
cells `1` and `1 + n * n`. -/
theorem decode_spec {P : Program} {b : ℕ} (h : P.HasAt b (decodeFuns b)) {cs : List ℕ}
    (hcs : ∀ x ∈ cs, x ≤ n + 1) (h0 : cs[0]? = some n) (hlen : 1 + 2 * (n * n) ≤ cs.length) :
    FunDet P b (.list (cs.map .nat)) (.list [.nat n, matVal cs n 1, matVal cs n (1 + n * n)])
      (decodeK * (n + 1) ^ 2 * ((Val.list (cs.map .nat)).wt + (n + 1) ^ 2)) := by
  simp only [decodeFuns] at h
  have hentry : P.funs[b]? = some (decodeEntry b) := h.left.left.single
  have hrange : P.HasAt (b + 1) (rangeFuns (b + 1)) := by simpa using h.left.right
  have hmat : P.HasAt (b + 4) (matFuns (b + 4)) := by
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using h.right
  set V := Val.list (cs.map .nat) with hV
  set ids := encFun fun x : Fin n => (x : ℕ) with hids
  have hR : FunDet P (b + 1) (.nat n) ids (8000 * (n + 1) ^ 3) := by
    refine FunAll.mono (range_spec hrange n) fun w c hw => ⟨?_, ?_⟩
    · rw [hw.1, hids, encFun_id]
    · have hc := hw.2
      rw [hw.1, ← encFun_id] at hc
      have := wt_encFun_le_sq (fun x : Fin n => (x : ℕ)) fun x => x.isLt.le
      have := wt_nat_le n
      have h1 : loopModK * (n + 1) * ((Val.nat n).wt + n + (encFun fun x : Fin n => (x : ℕ)).wt
          + 1) ≤ loopModK * (n + 1) * (8 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
      have e : loopModK * (n + 1) * (8 * (n + 1) ^ 2) = 8000 * (n + 1) ^ 3 := by
        simp only [loopModK]; ring
      omega
  have h0' : (cs.map Val.nat)[0]? = some (.nat n) := by simp [h0]
  have d1 : Det P [V] (.get (.var 0) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.var' (i := 0) rfl) (Det.nat 0) h0'
  have d2 := Det.call (Det.var' (P := P) (env := [V, .nat n]) (i := 1) rfl) hR
  have hM1 := mat_spec hmat hcs 1 (by omega)
  have hM2 := mat_spec hmat hcs (1 + n * n) (by omega)
  have d3 := Det.call (Det.mk2 (Det.mk4 (Det.var' (P := P) (env := [V, .nat n, ids]) (i := 0) rfl)
    (Det.var' (i := 1) rfl) (Det.var' (i := 2) rfl) (Det.nat 1)) (Det.var' (i := 2) rfl)) hM1
  have dm := Det.arith' (op := .add) (z := 1 + n * n) (Det.nat 1)
    (Det.arith' (op := .mul) (z := n * n) (Det.var' (P := P) (env := [V, .nat n, ids]) (i := 1) rfl)
      (Det.var' (i := 1) rfl) rfl) rfl
  have d4 := Det.call (Det.mk2 (Det.mk4 (Det.var' (P := P) (env := [V, .nat n, ids]) (i := 0) rfl)
    (Det.var' (i := 1) rfl) (Det.var' (i := 2) rfl) dm) (Det.var' (i := 2) rfl)) hM2
  have d5 := Det.mk3 (Det.var' (P := P) (env := [V, .nat n, ids]) (i := 1) rfl) d3 d4
  refine FunDet.intro hentry ((Det.letE d1 (Det.letE d2 d5)).mono ?_)
  -- the cost
  have eV : (Val.list (cs.map .nat)).wt = V.wt := rfl
  have eI : (encFun (fun x : Fin n => (x : ℕ))).wt = ids.wt := rfl
  have w1 := wt_encFun_le_sq (fun x : Fin n => (x : ℕ)) fun x => x.isLt.le
  have w2 := wt_matVal_le (n := n) hcs 1
  have w3 := wt_matVal_le (n := n) hcs (1 + n * n)
  have w4 := wt_list4_le V (.nat n) ids (.nat 1)
  have w5 := wt_list4_le V (.nat n) ids (.nat (1 + n * n))
  have w6 := wt_list2_le (.list [V, .nat n, ids, .nat 1]) ids
  have w7 := wt_list2_le (.list [V, .nat n, ids, .nat (1 + n * n)]) ids
  have w8 := wt_list3_le (.nat n) (matVal cs n 1) (matVal cs n (1 + n * n))
  have w9 := wt_nat_le n
  have w10 := wt_nat_le 1
  have w11 := wt_nat_le (1 + n * n)
  have hN2 : n * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hN23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hW : V.wt ≤ (n + 1) ^ 2 * V.wt := Nat.le_mul_of_pos_left _ (by omega)
  have m1 : 14000 * (n + 1) ^ 2 * (V.wt + 1 + 11 * (n + 1) ^ 2) ≤
      14000 * ((n + 1) ^ 2 * V.wt) + 168000 * (n + 1) ^ 4 := by
    have : 14000 * (n + 1) ^ 2 * (V.wt + 1 + 11 * (n + 1) ^ 2) =
      14000 * ((n + 1) ^ 2 * V.wt) + 14000 * (n + 1) ^ 2 + 154000 * (n + 1) ^ 4 := by ring
    omega
  have m2 : 14000 * (n + 1) ^ 2 * (V.wt + (1 + n * n) + 11 * (n + 1) ^ 2) ≤
      14000 * ((n + 1) ^ 2 * V.wt) + 168000 * (n + 1) ^ 4 := by
    have : 14000 * (n + 1) ^ 2 * (V.wt + (1 + n * n) + 11 * (n + 1) ^ 2) =
      14000 * ((n + 1) ^ 2 * V.wt) + 14000 * ((n + 1) ^ 2 * (1 + n * n)) +
        154000 * (n + 1) ^ 4 := by ring
    have : (n + 1) ^ 2 * (1 + n * n) ≤ (n + 1) ^ 2 * (n + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (by omega)
    have : (n + 1) ^ 2 * (n + 1) ^ 2 = (n + 1) ^ 4 := by ring
    omega
  have e : decodeK * (n + 1) ^ 2 * (V.wt + (n + 1) ^ 2) =
    400000 * ((n + 1) ^ 2 * V.wt) + 400000 * (n + 1) ^ 4 := by simp only [decodeK]; ring
  rw [eV, e]
  omega

/-! ### The input graphs -/

open Classical in
/-- The adjacency matrix of a graph, as a list of rows. -/
noncomputable def adjVal (G : SimpleGraph (Fin n)) : Val :=
  .list ((List.finRange n).map fun i => encFun fun j => if G.Adj i j then 1 else 0)

theorem getD_inputCells (G H : SimpleGraph (Fin n)) {a : ℕ} (ha : a < 2 * n * n + 1) :
    (inputCells G H).getD a 0 = inputMem G H a := by
  simp [inputCells, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha]

theorem lt_cells (i j : Fin n) : n * i + j < n * n := by
  have := Nat.mul_le_mul_left n (show (i : ℕ) + 1 ≤ n by omega)
  rw [Nat.mul_succ] at this
  omega

theorem matVal_inputCells_left (G H : SimpleGraph (Fin n)) :
    matVal (inputCells G H) n 1 = adjVal G := by
  classical
  simp only [matVal, adjVal, rowVal]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [encFun]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  have := lt_cells i j
  rw [getD_inputCells G H (by rw [Nat.mul_assoc]; omega), (inputMem_layout G H).left i j]

theorem matVal_inputCells_right (G H : SimpleGraph (Fin n)) :
    matVal (inputCells G H) n (1 + n * n) = adjVal H := by
  classical
  simp only [matVal, adjVal, rowVal]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [encFun]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  have := lt_cells i j
  rw [getD_inputCells G H (by rw [Nat.mul_assoc]; omega), (inputMem_layout G H).right i j]

theorem wt_inputVal_le (G H : SimpleGraph (Fin n)) : (inputVal G H).wt ≤ 30 * (n + 1) ^ 3 := by
  have h1 := wt_list_le ((inputCells G H).map Val.nat)
  have hlen : (inputCells G H).length = 2 * n * n + 1 := by simp [inputCells]
  have h2 : (((inputCells G H).map Val.nat).map Val.wt).sum ≤
      (inputCells G H).length * (n + 3) := by
    have := List.sum_le_card_nsmul (((inputCells G H).map Val.nat).map Val.wt) (n + 3) (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp]
      rintro _ x hx rfl
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
      have := inputLayout_le (inputMem_layout G H) a
      have := wt_nat_le (inputMem G H a)
      omega)
    simpa using this
  simp only [List.length_map] at h1
  rw [hlen] at h1 h2
  rw [inputVal]
  have : 2 * n * n + 1 ≤ 2 * (n + 1) ^ 2 := by nlinarith
  nlinarith

/-- **Reading the input graphs.** On `inputVal G H`, the decoder returns `n` and the adjacency
matrices of `G` and `H`. Its cost is at most `decodeK * (n + 1) ^ 2 * (30 * (n + 1) ^ 3 +
(n + 1) ^ 2)`, by `wt_inputVal_le`. -/
theorem decode_inputVal {P : Program} {b : ℕ} (h : P.HasAt b (decodeFuns b))
    (G H : SimpleGraph (Fin n)) :
    FunDet P b (inputVal G H) (.list [.nat n, adjVal G, adjVal H])
      (decodeK * (n + 1) ^ 2 * ((inputVal G H).wt + (n + 1) ^ 2)) := by
  have hcs : ∀ x ∈ inputCells G H, x ≤ n + 1 := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    exact inputLayout_le (inputMem_layout G H) a
  have h0 : (inputCells G H)[0]? = some n := by
    simp [inputCells, (inputMem_layout G H).size]
  have hlen : 1 + 2 * (n * n) ≤ (inputCells G H).length := by
    simp [inputCells, Nat.mul_assoc]; omega
  have := decode_spec h hcs h0 hlen
  rwa [matVal_inputCells_left, matVal_inputCells_right] at this

end GI.Lang
