import Workspace.Impl.AggRectRepProg
import Workspace.Impl.GenProdSq
import Workspace.Impl.AggRectCertC

/-!
# Library facts for the representation program

* `rcR_getD_spec`, `Det.rcGd`: the safe lookup `rcRGetDF` computes `List.getD`.
* `rcR_mapW`, `rcR_filterW`, `rcR_findW`: the library loops with a uniform weight bound `W` and
  step costs `K (W + 1)^d`; the loop costs at most `(K + 3000) (W + 1)^(d + 2)`.
* Powers of `W + 1`.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

/-! ### Powers -/

theorem rcR_pw {W i j : ℕ} (h : i ≤ j) : (W + 1) ^ i ≤ (W + 1) ^ j :=
  Nat.pow_le_pow_right (by omega) h

theorem rcR_one_le (W d : ℕ) : 1 ≤ (W + 1) ^ d := Nat.one_le_pow _ _ (by omega)

theorem rcR_W_le {W d : ℕ} (hd : 1 ≤ d) : W + 1 ≤ (W + 1) ^ d := by
  calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
    _ ≤ (W + 1) ^ d := rcR_pw hd

theorem rcR_mul_pw {W n K d : ℕ} (hn : n ≤ W + 1) : n * (K * (W + 1) ^ d) ≤ K * (W + 1) ^ (d + 1) := by
  calc n * (K * (W + 1) ^ d) ≤ (W + 1) * (K * (W + 1) ^ d) := Nat.mul_le_mul_right _ hn
    _ = K * (W + 1) ^ (d + 1) := by ring

theorem rcR_sq_pw {W d : ℕ} (hd : 2 ≤ d) : (W + 1) * (W + 1) ≤ (W + 1) ^ d := by
  calc (W + 1) * (W + 1) = (W + 1) ^ 2 := by ring
    _ ≤ (W + 1) ^ d := rcR_pw hd

/-! ### The safe lookup -/

theorem rcR_getD_natList (xs : List ℕ) (i : ℕ) :
    (xs.map Val.nat).getD i (.nat 0) = .nat (xs.getD i 0) := by
  simp [List.getD_eq_getElem?_getD]

/-- **The safe lookup.** -/
theorem rcR_getD_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some rcRGetDF) (l : List Val)
    (i : ℕ) (d : Val) :
    FunDet P f (.list [.list l, .nat i, d]) (l.getD i d)
      (20 * (Val.list [.list l, .nat i, d]).wt + 60) := by
  have hl : (Val.list l).wt < (Val.list [.list l, .nat i, d]).wt := wt_le_wt_list (by simp)
  have hil : l.length < (Val.list l).wt := length_lt_wt_list l
  have hd : d.wt < (Val.list [.list l, .nat i, d]).wt := wt_le_wt_list (by simp)
  have g1 := Det.arg' (P := P) (vs := [.list l, .nat i, d]) (rest := []) (j := 1) (v := .nat i) rfl
  have g0 := Det.arg' (P := P) (vs := [.list l, .nat i, d]) (rest := []) (j := 0) (v := .list l) rfl
  have g2 := Det.arg' (P := P) (vs := [.list l, .nat i, d]) (rest := []) (j := 2) (v := d) rfl
  have dc := Det.arith' (op := .lt) g1 (Det.length g0) rfl
  refine FunDet.intro hf ?_
  by_cases hi : i < l.length
  · have e : BinOp.eval .lt i l.length = 1 := by simp [BinOp.eval, hi]
    rw [e] at dc
    have dg := Det.get g0 g1 hi
    have hx : l[i].wt < (Val.list l).wt := wt_getElem_lt l i hi
    have eD : l.getD i d = l[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [eD]
    refine (Det.ite_pos dc one_ne_zero dg).mono ?_
    omega
  · have e : BinOp.eval .lt i l.length = 0 := by simp [BinOp.eval, hi]
    rw [e] at dc
    have eD : l.getD i d = d := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [eD]
    refine (Det.ite_zero dc g2).mono ?_
    omega

/-- **A lookup inside an expression.** -/
theorem Det.rcGd {P : Program} {env : List Val} (I : RcRIdx) (hf : P.funs[I.gD]? = some rcRGetDF)
    {le ie de : Expr} {l : List Val} {i : ℕ} {d : Val} {cl ci cd : ℕ}
    (hl : Det P env le (.list l) cl) (hi : Det P env ie (.nat i) ci) (hd : Det P env de d cd) :
    Det P env (I.gd le ie de) (l.getD i d)
      (cl + ci + cd + 30 * (Val.list [.list l, .nat i, d]).wt + 80) := by
  have h3 := Det.mk3 hl hi hd
  refine (Det.call h3 (rcR_getD_spec hf l i d)).mono ?_
  have hx : (l.getD i d).wt < (Val.list [.list l, .nat i, d]).wt := by
    rw [List.getD_eq_getElem?_getD]
    cases h : l[i]? with
    | none => exact wt_le_wt_list (by simp)
    | some y =>
      have hy : y ∈ l := List.mem_of_getElem? h
      have h1 : y.wt < (Val.list l).wt := wt_le_wt_list hy
      have h2 : (Val.list l).wt < (Val.list [.list l, .nat i, d]).wt := wt_le_wt_list (by simp)
      simp only [Option.getD_some]
      omega
  omega

/-! ### Loops with a uniform weight bound -/

/-- **Map**, with a uniform weight bound. -/
theorem rcR_mapW {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val} {xs : List Val}
    {g : Val → Val} {K d W : ℕ} (hf : ∀ x ∈ xs, FunDet P f (.list [c, x]) (g x) (K * (W + 1) ^ d))
    (hin : (Val.list [c, .list xs]).wt ≤ W) (hout : (Val.list (xs.map g)).wt ≤ W) :
    FunDet P b (.list [c, .list xs]) (.list (xs.map g)) ((K + 3000) * (W + 1) ^ (d + 2)) := by
  refine (map_det h hf).mono ?_
  have hn : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have hx : (Val.list xs).wt < (Val.list [c, .list xs]).wt := wt_le_wt_list (by simp)
  have h1 := rcR_mul_pw (W := W) (K := K) (d := d) (show xs.length ≤ W + 1 by omega)
  have h2 : K * (W + 1) ^ (d + 1) ≤ K * (W + 1) ^ (d + 2) :=
    Nat.mul_le_mul_left _ (rcR_pw (by omega))
  have h3 : mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + (Val.list (xs.map g)).wt + 1)
      ≤ 3000 * ((W + 1) * (W + 1)) := by
    unfold mapK
    calc 1000 * (xs.length + 1) * ((Val.list [c, .list xs]).wt + (Val.list (xs.map g)).wt + 1)
        ≤ 1000 * (W + 1) * (3 * (W + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 3000 * ((W + 1) * (W + 1)) := by ring
  have h4 : 3000 * ((W + 1) * (W + 1)) ≤ 3000 * (W + 1) ^ (d + 2) :=
    Nat.mul_le_mul_left _ (rcR_sq_pw (by omega))
  rw [Nat.add_mul]
  omega

/-- **Filter**, with a uniform weight bound. -/
theorem rcR_filterW {P : Program} {b p : ℕ} (h : P.HasAt b (filterFuns b p)) {c : Val}
    {xs : List Val} {t : Val → Bool} {K d W : ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, x]) (boolVal (t x)) (K * (W + 1) ^ d))
    (hin : (Val.list [c, .list xs]).wt ≤ W) (hout : (Val.list (xs.filter t)).wt ≤ W) :
    FunDet P b (.list [c, .list xs]) (.list (xs.filter t)) ((K + 3000) * (W + 1) ^ (d + 2)) := by
  refine (filter_spec h (B := fun _ => K * (W + 1) ^ d) hp).mono fun w cost hw => ⟨hw.1, ?_⟩
  obtain ⟨rfl, hc⟩ := hw
  have hn : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have hx : (Val.list xs).wt < (Val.list [c, .list xs]).wt := wt_le_wt_list (by simp)
  have hs : (xs.map fun _ => K * (W + 1) ^ d).sum = xs.length * (K * (W + 1) ^ d) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at hc
  have h1 := rcR_mul_pw (W := W) (K := K) (d := d) (show xs.length ≤ W + 1 by omega)
  have h2 : K * (W + 1) ^ (d + 1) ≤ K * (W + 1) ^ (d + 2) :=
    Nat.mul_le_mul_left _ (rcR_pw (by omega))
  have h3 : loopModK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + xs.length +
      (Val.list (xs.filter t)).wt + 1) ≤ 3000 * ((W + 1) * (W + 1)) := by
    unfold loopModK
    calc 1000 * (xs.length + 1) * ((Val.list [c, .list xs]).wt + xs.length +
          (Val.list (xs.filter t)).wt + 1)
        ≤ 1000 * (W + 1) * (3 * (W + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 3000 * ((W + 1) * (W + 1)) := by ring
  have h4 : 3000 * ((W + 1) * (W + 1)) ≤ 3000 * (W + 1) ^ (d + 2) :=
    Nat.mul_le_mul_left _ (rcR_sq_pw (by omega))
  rw [Nat.add_mul]
  omega

/-- **Find**, with a uniform weight bound. -/
theorem rcR_findW {P : Program} {b p : ℕ} (h : P.HasAt b (findFuns b p)) {c : Val}
    {xs : List Val} {t : Val → Bool} {K d W : ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, x]) (boolVal (t x)) (K * (W + 1) ^ d))
    (hin : (Val.list [c, .list xs]).wt ≤ W) :
    FunDet P b (.list [c, .list xs]) (.nat (xs.findIdx t)) ((K + 3000) * (W + 1) ^ (d + 2)) := by
  refine (find_spec h (B := fun _ => K * (W + 1) ^ d) hp).mono fun w cost hw => ⟨hw.1, ?_⟩
  obtain ⟨rfl, hc⟩ := hw
  have hn : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have hx : (Val.list xs).wt < (Val.list [c, .list xs]).wt := wt_le_wt_list (by simp)
  have hs : (xs.map fun _ => K * (W + 1) ^ d).sum = xs.length * (K * (W + 1) ^ d) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at hc
  have h1 := rcR_mul_pw (W := W) (K := K) (d := d) (show xs.length ≤ W + 1 by omega)
  have h2 : K * (W + 1) ^ (d + 1) ≤ K * (W + 1) ^ (d + 2) :=
    Nat.mul_le_mul_left _ (rcR_pw (by omega))
  have h3 : loopModK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + 2 * xs.length + 3) ≤
      3000 * ((W + 1) * (W + 1)) := by
    unfold loopModK
    calc 1000 * (xs.length + 1) * ((Val.list [c, .list xs]).wt + 2 * xs.length + 3)
        ≤ 1000 * (W + 1) * (3 * (W + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 3000 * ((W + 1) * (W + 1)) := by ring
  have h4 : 3000 * ((W + 1) * (W + 1)) ≤ 3000 * (W + 1) ^ (d + 2) :=
    Nat.mul_le_mul_left _ (rcR_sq_pw (by omega))
  rw [Nat.add_mul]
  omega

/-! ### Loops over lists of numbers -/

/-- **Map over numbers.** -/
theorem rcR_mapN {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val} {xs : List ℕ}
    {g : ℕ → Val} {K d W : ℕ} (hf : ∀ x ∈ xs, FunDet P f (.list [c, .nat x]) (g x) (K * (W + 1) ^ d))
    (hin : (Val.list [c, natList xs]).wt ≤ W) (hout : (Val.list (xs.map g)).wt ≤ W) :
    FunDet P b (.list [c, natList xs]) (.list (xs.map g)) ((K + 3000) * (W + 1) ^ (d + 2)) := by
  have e : (xs.map Val.nat).map (fun v => g (rcNatOf v)) = xs.map g := by
    rw [List.map_map]; rfl
  have hm := rcR_mapW h (c := c) (xs := xs.map Val.nat) (g := fun v => g (rcNatOf v)) (K := K)
    (d := d) (W := W) (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact hf x hx) hin (by rw [e]; exact hout)
  rw [e] at hm
  exact hm

/-- **Filter over numbers.** -/
theorem rcR_filterN {P : Program} {b p : ℕ} (h : P.HasAt b (filterFuns b p)) {c : Val}
    {xs : List ℕ} {t : ℕ → Bool} {K d W : ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, .nat x]) (boolVal (t x)) (K * (W + 1) ^ d))
    (hin : (Val.list [c, natList xs]).wt ≤ W) (hout : (natList (xs.filter t)).wt ≤ W) :
    FunDet P b (.list [c, natList xs]) (natList (xs.filter t)) ((K + 3000) * (W + 1) ^ (d + 2)) := by
  have e : (xs.map Val.nat).filter (fun v => t (rcNatOf v)) = (xs.filter t).map Val.nat := by
    rw [List.filter_map]; rfl
  have hm := rcR_filterW h (c := c) (xs := xs.map Val.nat) (t := fun v => t (rcNatOf v)) (K := K)
    (d := d) (W := W) (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact hp x hx) hin (by rw [e]; exact hout)
  rw [e] at hm
  exact hm

/-- **Find over numbers.** -/
theorem rcR_findN {P : Program} {b p : ℕ} (h : P.HasAt b (findFuns b p)) {c : Val}
    {xs : List ℕ} {t : ℕ → Bool} {K d W : ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, .nat x]) (boolVal (t x)) (K * (W + 1) ^ d))
    (hin : (Val.list [c, natList xs]).wt ≤ W) :
    FunDet P b (.list [c, natList xs]) (.nat (xs.findIdx t)) ((K + 3000) * (W + 1) ^ (d + 2)) := by
  have e : (xs.map Val.nat).findIdx (fun v => t (rcNatOf v)) = xs.findIdx t := by
    rw [List.findIdx_map]; rfl
  have hm := rcR_findW h (c := c) (xs := xs.map Val.nat) (t := fun v => t (rcNatOf v)) (K := K)
    (d := d) (W := W) (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact hp x hx) hin
  rw [e] at hm
  exact hm

/-- **Find over a table** (a list of lists of numbers). -/
theorem rcR_findL {P : Program} {b p : ℕ} (h : P.HasAt b (findFuns b p)) {c : Val}
    {ts : List (List ℕ)} {t : List ℕ → Bool} {K d W : ℕ}
    (hp : ∀ x ∈ ts, FunDet P p (.list [c, natList x]) (boolVal (t x)) (K * (W + 1) ^ d))
    (hin : (Val.list [c, rcTV ts]).wt ≤ W) :
    FunDet P b (.list [c, rcTV ts]) (.nat (ts.findIdx t)) ((K + 3000) * (W + 1) ^ (d + 2)) := by
  have e : (ts.map natList).findIdx (fun v => t (rcNats v)) = ts.findIdx t := by
    rw [List.findIdx_map]
    congr 1
    funext x
    simp [rcNats_natList]
  have hm := rcR_findW h (c := c) (xs := ts.map natList) (t := fun v => t (rcNats v)) (K := K)
    (d := d) (W := W) (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      simp only [rcNats_natList]
      exact hp x hx) hin
  rw [e] at hm
  exact hm

/-! ### Elements of a list -/

theorem rcR_size_cellsList {x : Val} {ys : List Val} (h : x ∈ ys) :
    x.size ≤ (Val.cellsList ys).length := by
  induction ys with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    simp only [cellsList_cons, List.length_append]
    rcases h with rfl | h
    · rw [← size_eq_length]; omega
    · have := ih h; omega

/-- An entry in place of its list makes a pair lighter. -/
theorem rcR_wt_elem {c x : Val} {ys : List Val} (h : x ∈ ys) :
    (Val.list [c, x]).wt ≤ (Val.list [c, .list ys]).wt := by
  rw [wt_list_eq, wt_list_eq]
  have h1 : x.wt < (Val.list ys).wt := wt_le_wt_list h
  have h2 : x.size ≤ (Val.list ys).size := by
    have := rcR_size_cellsList h; rw [size_list]; omega
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  have := GI.Machine.len_mono (show c.size + (x.size + 0) ≤ c.size + ((Val.list ys).size + 0) by
    omega)
  omega

theorem rcR_wt_elemN {c : Val} {x : ℕ} {xs : List ℕ} (h : x ∈ xs) :
    (Val.list [c, .nat x]).wt ≤ (Val.list [c, natList xs]).wt :=
  rcR_wt_elem (List.mem_map.2 ⟨x, h, rfl⟩)

theorem rcR_lin_pw {K w W : ℕ} (h : w ≤ W) : K * (w + 10) ≤ 10 * K * (W + 1) ^ 1 := by
  rw [pow_one]
  calc K * (w + 10) ≤ K * (10 * (W + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 10 * K * (W + 1) := by ring

/-- **Map over numbers**, with steps of linear cost. -/
theorem rcR_mapN1 {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val} {xs : List ℕ}
    {g : ℕ → Val} {K W : ℕ}
    (hf : ∀ x ∈ xs, FunDet P f (.list [c, .nat x]) (g x) (K * ((Val.list [c, .nat x]).wt + 10)))
    (hin : (Val.list [c, natList xs]).wt ≤ W) (hout : (Val.list (xs.map g)).wt ≤ W) :
    FunDet P b (.list [c, natList xs]) (.list (xs.map g)) ((10 * K + 3000) * (W + 1) ^ 3) :=
  rcR_mapN h (K := 10 * K) (d := 1) (fun x hx => (hf x hx).mono
    (rcR_lin_pw ((rcR_wt_elemN hx).trans hin))) hin hout

/-- **Map over a list**, with steps of linear cost. -/
theorem rcR_mapW1 {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val} {xs : List Val}
    {g : Val → Val} {K W : ℕ}
    (hf : ∀ x ∈ xs, FunDet P f (.list [c, x]) (g x) (K * ((Val.list [c, x]).wt + 10)))
    (hin : (Val.list [c, .list xs]).wt ≤ W) (hout : (Val.list (xs.map g)).wt ≤ W) :
    FunDet P b (.list [c, .list xs]) (.list (xs.map g)) ((10 * K + 3000) * (W + 1) ^ 3) :=
  rcR_mapW h (K := 10 * K) (d := 1) (fun x hx => (hf x hx).mono
    (rcR_lin_pw ((rcR_wt_elem hx).trans hin))) hin hout

/-- **Filter over numbers**, with tests of linear cost. -/
theorem rcR_filterN1 {P : Program} {b p : ℕ} (h : P.HasAt b (filterFuns b p)) {c : Val}
    {xs : List ℕ} {t : ℕ → Bool} {K W : ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, .nat x]) (boolVal (t x))
      (K * ((Val.list [c, .nat x]).wt + 10)))
    (hin : (Val.list [c, natList xs]).wt ≤ W) (hout : (natList (xs.filter t)).wt ≤ W) :
    FunDet P b (.list [c, natList xs]) (natList (xs.filter t)) ((10 * K + 3000) * (W + 1) ^ 3) :=
  rcR_filterN h (K := 10 * K) (d := 1) (fun x hx => (hp x hx).mono
    (rcR_lin_pw ((rcR_wt_elemN hx).trans hin))) hin hout

/-- **Find over numbers**, with tests of linear cost. -/
theorem rcR_findN1 {P : Program} {b p : ℕ} (h : P.HasAt b (findFuns b p)) {c : Val}
    {xs : List ℕ} {t : ℕ → Bool} {K W : ℕ}
    (hp : ∀ x ∈ xs, FunDet P p (.list [c, .nat x]) (boolVal (t x))
      (K * ((Val.list [c, .nat x]).wt + 10)))
    (hin : (Val.list [c, natList xs]).wt ≤ W) :
    FunDet P b (.list [c, natList xs]) (.nat (xs.findIdx t)) ((10 * K + 3000) * (W + 1) ^ 3) :=
  rcR_findN h (K := 10 * K) (d := 1) (fun x hx => (hp x hx).mono
    (rcR_lin_pw ((rcR_wt_elemN hx).trans hin))) hin

/-- **Find over a table**, with tests of linear cost. -/
theorem rcR_findL1 {P : Program} {b p : ℕ} (h : P.HasAt b (findFuns b p)) {c : Val}
    {ts : List (List ℕ)} {t : List ℕ → Bool} {K W : ℕ}
    (hp : ∀ x ∈ ts, FunDet P p (.list [c, natList x]) (boolVal (t x))
      (K * ((Val.list [c, natList x]).wt + 10)))
    (hin : (Val.list [c, rcTV ts]).wt ≤ W) :
    FunDet P b (.list [c, rcTV ts]) (.nat (ts.findIdx t)) ((10 * K + 3000) * (W + 1) ^ 3) :=
  rcR_findL h (K := 10 * K) (d := 1) (fun x hx => (hp x hx).mono
    (rcR_lin_pw ((rcR_wt_elem (List.mem_map.2 ⟨x, hx, rfl⟩)).trans hin))) hin

theorem rcR_wt_nat_mono {a b : ℕ} (h : a ≤ b) : (Val.nat a).wt ≤ (Val.nat b).wt := by
  rw [wt_nat, wt_nat]; have := GI.Machine.len_mono h; omega

/-! ### Arithmetic and lookups with stated values -/

theorem Det.arithW {P : Program} {env : List Val} {op : BinOp} {a b : Expr} {x y z ca cb : ℕ}
    (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb) (hz : op.eval x y = z) :
    Det P env (.arith op a b) (.nat z) (ca + cb + (Val.nat z).wt + 1) := by
  subst hz; exact Det.arith ha hb

theorem rcR_wt_bit {b : ℕ} (h : b ≤ 1) : (Val.nat b).wt ≤ 3 := by
  have := wt_nat_le b; omega

/-- A lookup in a list of numbers, with default `0`. -/
theorem Det.rcGdN {P : Program} {env : List Val} (I : RcRIdx) (hf : P.funs[I.gD]? = some rcRGetDF)
    {le ie de : Expr} {l : List ℕ} {i : ℕ} {cl ci cd : ℕ}
    (hl : Det P env le (natList l) cl) (hi : Det P env ie (.nat i) ci)
    (hd : Det P env de (.nat 0) cd) :
    Det P env (I.gd le ie de) (.nat (l.getD i 0))
      (cl + ci + cd + 30 * (Val.list [natList l, .nat i, .nat 0]).wt + 80) := by
  have h := Det.rcGd I hf (l := l.map Val.nat) hl hi hd
  rw [rcR_getD_natList] at h
  exact h

end GI.Impl
