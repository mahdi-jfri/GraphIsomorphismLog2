module

public import Workspace.Impl.AggMT
public import Workspace.Impl.AggPairs

@[expose] public section

/-!
# The generators of `M_T`, in `GI.Lang`

`cycGensFuns` on `[q, s]`, where `s` lists for every label whether it lies in `T` (`indT`),
returns the encoded permutations `genOf T t` for `t < q³` (`cycGens_spec`). They generate
`M_T = Alt(T) × Alt(Tᶜ)` (`closure_genOf`, from `closure_cycGens`).

* `cellF` on `[[u, v, w, ok], i]` returns the image of `i` under the 3-cycle `cyc u v w` if
  `ok ≠ 0`, and `i` otherwise (`cellVal`).
* `genF` on `[[q, s], t]` decodes `t = u q² + v q + w`, computes `ok` (the three labels are
  distinct and on the same side of `T`), and maps `cellF` over the labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-! ### One entry -/

/-- The value of `cellF`, in the shape of its `if`s. -/
def cellVal (u v w ok i : ℕ) : ℕ :=
  if ok = 0 then i else
    if (if i = u then 1 else 0) = 0 then
      (if (if i = w then 1 else 0) = 0 then
        (if (if i = v then 1 else 0) = 0 then i else u) else v)
    else w

theorem cyc_apply (u v w i : Fin q) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    cyc u v w i = if i = u then w else if i = w then v else if i = v then u else i := by
  unfold cyc
  rw [Perm.mul_apply]
  split_ifs with h1 h2 h3
  · subst h1; rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm huw) hvw.symm]
  · subst h2; rw [swap_apply_right, swap_apply_left]
  · subst h3; rw [swap_apply_of_ne_of_ne (Ne.symm huv) hvw, swap_apply_right]
  · rw [swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]

/-- The side test of `cycGen`, as a number. -/
def okVal (T : Finset (Fin q)) (u v w : Fin q) : ℕ :=
  if u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ (u ∈ T ↔ v ∈ T) ∧ (v ∈ T ↔ w ∈ T) then 1 else 0

theorem cellVal_eq (T : Finset (Fin q)) (u v w i : Fin q) :
    cellVal u v w (okVal T u v w) i = (cycGen T u v w i : ℕ) := by
  unfold cellVal okVal cycGen
  by_cases h : u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ (u ∈ T ↔ v ∈ T) ∧ (v ∈ T ↔ w ∈ T)
  · rw [if_pos h, if_pos h, cyc_apply u v w i h.1 h.2.1 h.2.2.1]
    simp only [one_ne_zero, if_false, Fin.val_eq_val]
    have a1 := h.1.symm
    have a2 := h.2.1.symm
    have a3 := h.2.2.1
    by_cases h1 : i = u
    · subst h1; simp
    · by_cases h2 : i = w
      · subst h2; simp [a2]
      · by_cases h3 : i = v
        · subst h3; simp [a1, a3]
        · simp [h1, h2, h3]
  · rw [if_neg h, if_neg h]; simp

/-- On `[[u, v, w, ok], i]`. -/
def cellF : Expr :=
  let C := arg 0
  let i := arg 1
  let u := Expr.get C (.nat 0)
  let v := Expr.get C (.nat 1)
  let w := Expr.get C (.nat 2)
  let ok := Expr.get C (.nat 3)
  .ite ok (.ite (.arith .eq i u) w (.ite (.arith .eq i w) v (.ite (.arith .eq i v) u i))) i

/-- The cost constant of `cellF`. -/
def cellK : ℕ := 100000

theorem cellF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some cellF) (u v w ok i : ℕ)
    (hu : u < q) (hv : v < q) (hw : w < q) (hok : ok ≤ 1) (hi : i < q) :
    FunDet P f (.list [.list [.nat u, .nat v, .nat w, .nat ok], .nat i])
      (.nat (cellVal u v w ok i)) (cellK * (q + 1)) := by
  set C := Val.list [.nat u, .nat v, .nat w, .nat ok] with hC
  have gC := Det.arg' (P := P) (vs := [C, .nat i]) (rest := []) (j := 0) rfl
  have gi := Det.arg' (P := P) (vs := [C, .nat i]) (rest := []) (j := 1) rfl
  have gu := Det.get' gC (Det.nat 0) (v := .nat u) rfl
  have gv := Det.get' gC (Det.nat 1) (v := .nat v) rfl
  have gw := Det.get' gC (Det.nat 2) (v := .nat w) rfl
  have go := Det.get' gC (Det.nat 3) (v := .nat ok) rfl
  have e1 := Det.arith' (op := .eq) gi gu (z := if i = u then 1 else 0) rfl
  have e2 := Det.arith' (op := .eq) gi gw (z := if i = w then 1 else 0) rfl
  have e3 := Det.arith' (op := .eq) gi gv (z := if i = v then 1 else 0) rfl
  -- the weights
  have wC := wt_list_le [Val.nat u, .nat v, .nat w, .nat ok]
  have w1 := wt_list2_le C (.nat i)
  have nu := wt_nat_le u; have nv := wt_nat_le v; have nw := wt_nat_le w
  have no := wt_nat_le ok; have ni := wt_nat_le i
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wC
  have eC : C.wt = (Val.list [Val.nat u, .nat v, .nat w, .nat ok]).wt := by rw [hC]
  have hW : (Val.list [C, .nat i]).wt ≤ 60 * (q + 1) := by omega
  have hI : ∀ (c : Prop) [Decidable c] (a b : Val), a.wt ≤ q + 2 → b.wt ≤ q + 2 →
      (if c then a else b).wt ≤ q + 2 := fun c _ a b ha hb => by split_ifs <;> assumption
  have b1 : (if i = u then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have b2 : (if i = w then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have b3 : (if i = v then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have x3 := hI ((if i = v then 1 else 0) = 0) (Val.nat i) (Val.nat u) (by omega) (by omega)
  have x2 := hI ((if i = w then 1 else 0) = 0) _ (Val.nat v) x3 (by omega)
  have x1 := hI ((if i = u then 1 else 0) = 0) _ (Val.nat w) x2 (by omega)
  have x0 := hI (ok = 0) (Val.nat i) _ (by omega) x1
  have mx : ∀ a b c : ℕ, max a b ≤ a + b + c := fun a b c =>
    max_le (by omega) (by omega)
  have d3 := (Det.ite' e3 gu gi).mono (c' := 600 * (q + 1)) (by
    have := mx (2 * (Val.list [C, Val.nat i]).wt + 0 + 5 + (0 + 3) + (Val.nat u).wt + 1)
      (2 * (Val.list [C, Val.nat i]).wt + 1 + 5) 0
    have := mx (Val.nat u).wt (Val.nat i).wt 0
    omega)
  have d2 := (Det.ite' e2 gv d3).mono (c' := 1200 * (q + 1)) (by
    have := mx (2 * (Val.list [C, Val.nat i]).wt + 0 + 5 + (1 + 3) + (Val.nat v).wt + 1)
      (600 * (q + 1)) 0
    have := mx (Val.nat v).wt
      (if (if i = v then 1 else 0) = 0 then Val.nat i else Val.nat u).wt 0
    omega)
  have d1 := (Det.ite' e1 gw d2).mono (c' := 1800 * (q + 1)) (by
    have := mx (2 * (Val.list [C, Val.nat i]).wt + 0 + 5 + (2 + 3) + (Val.nat w).wt + 1)
      (1200 * (q + 1)) 0
    have := mx (Val.nat w).wt
      (if (if i = w then 1 else 0) = 0 then if (if i = v then 1 else 0) = 0 then Val.nat i
        else Val.nat u else Val.nat v).wt 0
    omega)
  have d0 := (Det.ite' go d1 gi).mono (c' := 2400 * (q + 1)) (by
    have := mx (1800 * (q + 1)) (2 * (Val.list [C, Val.nat i]).wt + 1 + 5) 0
    have := mx (if (if i = u then 1 else 0) = 0 then
      if (if i = w then 1 else 0) = 0 then if (if i = v then 1 else 0) = 0 then Val.nat i
        else Val.nat u else Val.nat v else Val.nat w).wt (Val.nat i).wt 0
    omega)
  have hval : (if ok = 0 then Val.nat i else
      (if (if i = u then 1 else 0) = 0 then
        (if (if i = w then 1 else 0) = 0 then
          (if (if i = v then 1 else 0) = 0 then Val.nat i else .nat u) else .nat v)
      else .nat w)) = .nat (cellVal u v w ok i) := by
    unfold cellVal; split_ifs <;> rfl
  rw [hval] at d0
  exact FunDet.intro hf (d0.mono (by simp only [cellK]; omega))

/-! ### One generator -/

/-- The indicator of `T`, as the value the program reads. -/
def indT (T : Finset (Fin q)) : Val := encFun fun i => if i ∈ T then 1 else 0

/-- The three labels of the number `t < q³`. -/
def decU (t : ℕ) (ht : t < q ^ 3) : Fin q :=
  ⟨t / (q * q), (Nat.div_lt_iff_lt_mul (Nat.mul_pos (Nat.pos_of_ne_zero fun h => by
    subst h; simp at ht) (Nat.pos_of_ne_zero fun h => by subst h; simp at ht))).2
    (by rw [show q ^ 3 = q * (q * q) by ring] at ht; exact ht)⟩

def decV (t : ℕ) (ht : t < q ^ 3) : Fin q :=
  ⟨t / q % q, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by subst h; simp at ht)⟩

def decW (t : ℕ) (ht : t < q ^ 3) : Fin q :=
  ⟨t % q, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by subst h; simp at ht)⟩

/-- The generator of number `t`. -/
def genOf (T : Finset (Fin q)) (t : ℕ) : Perm (Fin q) :=
  if ht : t < q ^ 3 then cycGen T (decU t ht) (decV t ht) (decW t ht) else 1

/-- Every triple has a number. -/
theorem exists_dec (u v w : Fin q) :
    ∃ t, ∃ ht : t < q ^ 3, decU t ht = u ∧ decV t ht = v ∧ decW t ht = w := by
  have hq : 0 < q := Nat.pos_of_ne_zero fun h => by subst h; exact u.elim0
  refine ⟨u * (q * q) + v * q + w, ?_, ?_, ?_, ?_⟩
  · have hu := u.isLt; have hv := v.isLt; have hw := w.isLt
    have : (u : ℕ) * (q * q) + v * q + w < (u + 1) * (q * q) := by nlinarith
    calc _ < (u + 1) * (q * q) := this
      _ ≤ q * (q * q) := Nat.mul_le_mul_right _ hu
      _ = q ^ 3 := by ring
  · apply Fin.ext
    show ((u : ℕ) * (q * q) + v * q + w) / (q * q) = u
    have hv := v.isLt; have hw := w.isLt
    have : (v : ℕ) * q + w < q * q := by nlinarith
    rw [show (u : ℕ) * (q * q) + v * q + w = (v * q + w) + (q * q) * u by ring,
      Nat.add_mul_div_left _ _ (Nat.mul_pos hq hq), Nat.div_eq_of_lt this, zero_add]
  · apply Fin.ext
    show ((u : ℕ) * (q * q) + v * q + w) / q % q = v
    rw [show (u : ℕ) * (q * q) + v * q + w = w + q * (u * q + v) by ring,
      Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt w.isLt, zero_add,
      show (u : ℕ) * q + v = v + q * u by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt v.isLt]
  · apply Fin.ext
    show ((u : ℕ) * (q * q) + v * q + w) % q = w
    rw [show (u : ℕ) * (q * q) + v * q + w = w + q * (u * q + v) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w.isLt]

/-- **The generators of `M_T`, by number.** -/
theorem closure_genOf (T : Finset (Fin q)) :
    Subgroup.closure {σ | ∃ t ∈ List.range (q ^ 3), genOf T t = σ} = MT T := by
  rw [← closure_cycGens]
  congr 1
  ext σ
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' := List.mem_range.1 ht
    exact ⟨_, _, _, by rw [genOf, dif_pos ht']⟩
  · rintro ⟨u, v, w, rfl⟩
    obtain ⟨t, ht, hu, hv, hw⟩ := exists_dec u v w
    exact ⟨t, List.mem_range.2 ht, by rw [genOf, dif_pos ht, hu, hv, hw]⟩

/-- The side test as the program computes it. -/
theorem okVal_eq (T : Finset (Fin q)) (u v w : Fin q) :
    (1 - (if (u : ℕ) = v then 1 else 0)) * (1 - (if (u : ℕ) = w then 1 else 0)) *
      (1 - (if (v : ℕ) = w then 1 else 0)) *
      ((if (if u ∈ T then 1 else 0) = (if v ∈ T then 1 else 0) then 1 else 0) *
        (if (if v ∈ T then 1 else 0) = (if w ∈ T then 1 else 0) then 1 else 0)) =
      okVal T u v w := by
  unfold okVal
  simp only [Fin.val_eq_val, ne_eq]
  by_cases h1 : u = v <;> by_cases h2 : u = w <;> by_cases h3 : v = w <;>
    by_cases hu : u ∈ T <;> by_cases hv : v ∈ T <;> by_cases hw : w ∈ T <;> simp_all

/-- On `[[q, s], t]`: the generator of number `t` (the inner map at `im`, `range` at `rg`). -/
def genF (im rg : ℕ) : Expr :=
  let C := arg 0
  let qE := Expr.get C (.nat 0)
  let sE := Expr.get C (.nat 1)
  let tE := arg 1
  let uE := Expr.arith .div tE (.arith .mul qE qE)
  let vE := Expr.arith .mod (.arith .div tE qE) qE
  let wE := Expr.arith .mod tE qE
  let neq := fun a b : Expr => Expr.arith .sub (.nat 1) (.arith .eq a b)
  let okE := Expr.arith .mul (.arith .mul (.arith .mul (neq uE vE) (neq uE wE)) (neq vE wE))
    (.arith .mul (.arith .eq (.get sE uE) (.get sE vE)) (.arith .eq (.get sE vE) (.get sE wE)))
  .call im (mk2 (mk4 uE vE wE okE) (.call rg qE))

/-- The cost constant of `genF`. -/
def genK : ℕ := 10 ^ 9

theorem wt_indT_le (T : Finset (Fin q)) : (indT T).wt ≤ 7 * q + 4 := by
  have := wt_encFun_le (fun i : Fin q => if i ∈ T then 1 else 0) (B := 1)
    (fun i => by show (if i ∈ T then 1 else 0) ≤ 1; split_ifs <;> omega)
  unfold indT; omega

theorem genF_spec {P : Program} {g im rg : ℕ} (hg : P.funs[g]? = some (genF im rg))
    (him : P.HasAt im (mapFuns im (im + 3))) (hc : P.funs[im + 3]? = some cellF)
    (hrg : P.HasAt rg (rangeFuns rg)) (T : Finset (Fin q)) (t : ℕ) (ht : t < q ^ 3) :
    FunDet P g (.list [.list [.nat q, indT T], .nat t]) (encPerm (genOf T t))
      (genK * (q + 1) ^ 3) := by
  have hq : 0 < q := Nat.pos_of_ne_zero fun h => by subst h; simp at ht
  set u := decU t ht
  set v := decV t ht
  set w := decW t ht
  set C := Val.list [.nat q, indT T] with hC
  set A := Val.list [C, .nat t] with hA
  have gC := Det.arg' (P := P) (vs := [C, .nat t]) (rest := []) (j := 0) rfl
  have gt := Det.arg' (P := P) (vs := [C, .nat t]) (rest := []) (j := 1) rfl
  have gq := Det.get' gC (Det.nat 0) (v := .nat q) rfl
  have gs := Det.get' gC (Det.nat 1) (v := indT T) rfl
  have gqq := Det.arith' (op := .mul) gq gq (z := q * q) rfl
  have gu := Det.arith' (op := .div) gt gqq (z := (u : ℕ)) rfl
  have gtq := Det.arith' (op := .div) gt gq (z := t / q) rfl
  have gv := Det.arith' (op := .mod) gtq gq (z := (v : ℕ)) rfl
  have gw := Det.arith' (op := .mod) gt gq (z := (w : ℕ)) rfl
  have hget : ∀ x : Fin q, ((List.finRange q).map fun i => Val.nat (if i ∈ T then 1 else 0))[(x : ℕ)]?
      = some (.nat (if x ∈ T then 1 else 0)) := fun x => encFun_getElem? _ x
  have su := Det.get' gs gu (hget u)
  have sv := Det.get' gs gv (hget v)
  have sw := Det.get' gs gw (hget w)
  have n1 := Det.arith' (op := .sub) (Det.nat 1) (Det.arith' (op := .eq) gu gv rfl) rfl
  have n2 := Det.arith' (op := .sub) (Det.nat 1) (Det.arith' (op := .eq) gu gw rfl) rfl
  have n3 := Det.arith' (op := .sub) (Det.nat 1) (Det.arith' (op := .eq) gv gw rfl) rfl
  have e1 := Det.arith' (op := .eq) su sv rfl
  have e2 := Det.arith' (op := .eq) sv sw rfl
  have dok := Det.arith' (op := .mul) (Det.arith' (op := .mul) (Det.arith' (op := .mul) n1 n2 rfl)
    n3 rfl) (Det.arith' (op := .mul) e1 e2 rfl) (z := okVal T u v w) (by
      simp only [BinOp.eval]; exact okVal_eq T u v w)
  have dR := Det.call gq (range_det hrg q)
  have dc := Det.mk2 (Det.mk4 gu gv gw dok) dR
  have hok : okVal T u v w ≤ 1 := by unfold okVal; split_ifs <;> omega
  have hmap := mapList_spec him (List.finRange q) (fun i : Fin q => Val.nat i.val)
    (fun i : Fin q => Val.nat (cellVal u v w (okVal T u v w) i.val))
    (c := .list [.nat u, .nat v, .nat w, .nat (okVal T u v w)]) (B := cellK * (q + 1))
    (fun a _ a' _ he => by rw [Fin.ext (Val.nat.inj he)])
    (fun i _ => cellF_spec hc u v w _ i u.isLt v.isLt w.isLt hok i.isLt)
  have e1' : Val.list ((List.finRange q).map fun i : Fin q => Val.nat i.val) =
      encPerm (1 : Perm (Fin q)) := rfl
  rw [e1'] at hmap
  have e2' : Val.list ((List.finRange q).map fun i : Fin q =>
      Val.nat (cellVal u v w (okVal T u v w) i.val)) =
      encPerm (genOf T t) := by
    unfold encPerm genOf
    rw [dif_pos ht]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [cellVal_eq]
  rw [e2'] at hmap
  have dmain := Det.call dc hmap
  refine FunDet.intro hg (dmain.mono ?_)
  -- the cost
  have be : ∀ a b : ℕ, BinOp.eq.eval a b ≤ 1 := fun a b => by
    simp only [BinOp.eval]; split_ifs <;> omega
  have bs : ∀ a : ℕ, BinOp.sub.eval 1 a ≤ 1 := fun a => Nat.sub_le 1 a
  have bm : ∀ a b : ℕ, a ≤ 1 → b ≤ 1 → BinOp.mul.eval a b ≤ 1 := fun a b ha hb => by
    show a * b ≤ 1
    calc a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb
      _ = 1 := rfl
  have i1 := be u v; have i2 := be u w; have i3 := be v w
  have i4 := be (if u ∈ T then 1 else 0) (if v ∈ T then 1 else 0)
  have i5 := be (if v ∈ T then 1 else 0) (if w ∈ T then 1 else 0)
  have j1 := bs (BinOp.eq.eval u v); have j2 := bs (BinOp.eq.eval u w)
  have j3 := bs (BinOp.eq.eval v w)
  have k1 := bm _ _ j1 j2
  have k2 := bm _ _ k1 j3
  have k3 := bm _ _ i4 i5
  have iu : (if u ∈ T then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have iv : (if v ∈ T then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have iw : (if w ∈ T then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have wiu := wt_nat_le (if u ∈ T then 1 else 0)
  have wiv := wt_nat_le (if v ∈ T then 1 else 0)
  have wiw := wt_nat_le (if w ∈ T then 1 else 0)
  have hu := u.isLt; have hv := v.isLt; have hw := w.isLt
  have htq : t / q ≤ t := Nat.div_le_self _ _
  have hq3 : q ^ 3 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hqq : q * q ≤ (q + 1) ^ 3 := by
    calc q * q ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (q + 1) ^ 2 := by ring
      _ ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq1 : q + 1 ≤ (q + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hq2 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  -- weights
  have wq := wt_nat_le q; have wt := wt_nat_le t
  have wI := wt_indT_le T
  have wC := wt_list2_le (.nat q) (indT T)
  have wA := wt_list2_le C (.nat t)
  have eC : C.wt = (Val.list [.nat q, indT T]).wt := by rw [hC]
  have wnu := wt_nat_le (u : ℕ); have wnv := wt_nat_le (v : ℕ); have wnw := wt_nat_le (w : ℕ)
  have wno := wt_nat_le (okVal T u v w)
  have w4 := wt_list_le [Val.nat u, .nat v, .nat w, .nat (okVal T u v w)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w4
  have w1 := wt_encPerm_le (1 : Perm (Fin q))
  have wg := wt_encPerm_le (genOf T t)
  have w5 := wt_list2_le (.list [Val.nat u, .nat v, .nat w, .nat (okVal T u v w)])
    (encPerm (1 : Perm (Fin q)))
  rw [List.length_finRange]
  have hq12 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hc1 : q * (cellK * (q + 1)) ≤ cellK * (q + 1) ^ 3 := by
    have : q * (cellK * (q + 1)) = cellK * (q * (q + 1)) := by ring
    rw [this]
    refine Nat.mul_le_mul_left _ ?_
    calc q * (q + 1) ≤ (q + 1) * (q + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = (q + 1) ^ 2 := by ring
      _ ≤ _ := hq2
  have hc2 : mapK * (q + 1) * ((Val.list [Val.list [Val.nat ↑u, Val.nat ↑v, Val.nat ↑w,
      Val.nat (okVal T u v w)], encPerm 1]).wt + (encPerm (genOf T t)).wt + 1) ≤
      mapK * (q + 1) * (100 * (q + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have hc3 : mapK * (q + 1) * (100 * (q + 1) ^ 2) = 100000 * (q + 1) ^ 3 := by
    simp only [mapK]; ring
  simp only [genK, cellK] at *
  omega

/-! ### All generators -/

/-- On `[q, s]`. -/
def cycEntry (b : ℕ) : Expr :=
  let qE := arg 0
  .call (b + 1) (mk2 (.var 0) (.call (b + 9) (.arith .mul (.arith .mul qE qE) qE)))

/-- The module at base `b` (twelve functions). -/
def cycGensFuns (b : ℕ) : List Expr :=
  [cycEntry b] ++ mapFuns (b + 1) (b + 4) ++ [genF (b + 5) (b + 9)] ++ mapFuns (b + 5) (b + 8) ++
    [cellF] ++ rangeFuns (b + 9)

/-- The cost bound of the module. -/
def cycGensCost (q : ℕ) : ℕ := 10 ^ 13 * (q + 1) ^ 9

/-- **The generators of `M_T`.** On `[q, indT T]` the module returns the encoded `genOf T t`
for `t < q³`. -/
theorem cycGens_spec {P : Program} {b : ℕ} (h : P.HasAt b (cycGensFuns b)) (T : Finset (Fin q)) :
    FunDet P b (.list [.nat q, indT T])
      (.list ((List.range (q ^ 3)).map fun t => encPerm (genOf T t))) (cycGensCost q) := by
  have hentry : P.funs[b]? = some (cycEntry b) := by
    simpa using (h.block 0 (gs := [cycEntry b]) (by rfl)).single
  have hom : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 (by rfl)
  have hg : P.funs[b + 4]? = some (genF (b + 5) (b + 9)) := by
    simpa using (h.block 4 (gs := [genF (b + 5) (b + 9)]) (by rfl)).single
  have him : P.HasAt (b + 5) (mapFuns (b + 5) (b + 5 + 3)) := h.block 5 (by rfl)
  have hc : P.funs[b + 5 + 3]? = some cellF := by
    simpa using (h.block 8 (gs := [cellF]) (by rfl)).single
  have hrg : P.HasAt (b + 9) (rangeFuns (b + 9)) := h.block 9 (by rfl)
  set A := Val.list [.nat q, indT T] with hA
  have gq := Det.arg' (P := P) (vs := [.nat q, indT T]) (rest := []) (j := 0) rfl
  have gn := Det.arith' (op := .mul) (Det.arith' (op := .mul) gq gq rfl) gq (z := q ^ 3)
    (by simp only [BinOp.eval]; ring)
  have hR : FunAll P (b + 9) (.nat (q ^ 3)) (fun w c => w = natList (List.range (q ^ 3)) ∧
      c ≤ loopModK * (q ^ 3 + 1) * ((Val.nat (q ^ 3)).wt + q ^ 3 +
        (natList (List.range (q ^ 3))).wt + 1)) :=
    (range_spec hrg (q ^ 3)).mono fun w c hw => ⟨hw.1, by have := hw.2; rw [hw.1] at this; exact this⟩
  have dR := Det.call gn hR
  have hmap := mapList_spec hom (List.range (q ^ 3)) Val.nat (fun t => encPerm (genOf T t))
    (c := A) (B := genK * (q + 1) ^ 3)
    (fun a _ a' _ he => by rw [Val.nat.inj he])
    (fun t ht => genF_spec hg him hc hrg T t (List.mem_range.1 ht))
  have dmain := Det.call (Det.mk2 (Det.var' (P := P) (env := [A]) (i := 0) rfl) dR) hmap
  refine FunDet.intro hentry (dmain.mono ?_)
  -- the cost
  set N := q + 1 with hN
  have p3 : q ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have r2 : (q + 1) ^ 2 = N ^ 2 := rfl
  have r3 : (q + 1) ^ 3 = N ^ 3 := rfl
  have n1 : 1 ≤ N := by omega
  have p13 : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) _
  have p23 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right n1 (by omega)
  have p36 : N ^ 3 ≤ N ^ 6 := Nat.pow_le_pow_right n1 (by omega)
  have p56 : N ^ 5 ≤ N ^ 6 := Nat.pow_le_pow_right n1 (by omega)
  have p69 : N ^ 6 ≤ N ^ 9 := Nat.pow_le_pow_right n1 (by omega)
  have hqq : BinOp.mul.eval q q ≤ N ^ 3 := by
    show q * q ≤ N ^ 3
    calc q * q ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
      _ = N ^ 2 := by ring
      _ ≤ _ := p23
  have wq := wt_nat_le q
  have wI := wt_indT_le T
  have wA := wt_list2_le (.nat q) (indT T)
  have eA : A.wt = (Val.list [.nat q, indT T]).wt := by rw [hA]
  have wn3 := wt_nat_le (q ^ 3)
  have eL : natList (List.range (q ^ 3)) = Val.list (List.map Val.nat (List.range (q ^ 3))) := rfl
  have wL : (natList (List.range (q ^ 3))).wt ≤ 7 * N ^ 6 + 4 := by
    have h1 := wt_list_map_le (List.range (q ^ 3)) Val.nat (W := q ^ 3 + 2) fun t ht => by
      have := wt_nat_le t; have := List.mem_range.1 ht; omega
    rw [List.length_range] at h1
    have h2 : q ^ 3 * (2 * (q ^ 3 + 2) + 1) ≤ N ^ 3 * (7 * N ^ 3) :=
      Nat.mul_le_mul p3 (by omega)
    have h3 : N ^ 3 * (7 * N ^ 3) = 7 * N ^ 6 := by ring
    rw [eL]; omega
  have wO : (Val.list ((List.range (q ^ 3)).map fun t => encPerm (genOf T t))).wt ≤
      9 * N ^ 5 + 4 := by
    have h1 := wt_list_map_le (List.range (q ^ 3)) (fun t => encPerm (genOf T t))
      (W := 4 * (q + 1) ^ 2) fun t _ => wt_encPerm_le _
    rw [List.length_range] at h1
    have h2 : q ^ 3 * (2 * (4 * (q + 1) ^ 2) + 1) ≤ N ^ 3 * (9 * N ^ 2) :=
      Nat.mul_le_mul p3 (by have : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
    have h3 : N ^ 3 * (9 * N ^ 2) = 9 * N ^ 5 := by ring
    omega
  have wAL := wt_list2_le A (natList (List.range (q ^ 3)))
  rw [List.length_range, ← eL]
  have c1 : q ^ 3 * (genK * (q + 1) ^ 3) ≤ genK * N ^ 6 := by
    rw [r3]
    have := Nat.mul_le_mul p3 (le_refl (genK * N ^ 3))
    have e : N ^ 3 * (genK * N ^ 3) = genK * N ^ 6 := by ring
    omega
  have c2 : mapK * (q ^ 3 + 1) * ((Val.list [A, natList (List.range (q ^ 3))]).wt +
      (Val.list ((List.range (q ^ 3)).map fun t => encPerm (genOf T t))).wt + 1) ≤
      mapK * (2 * N ^ 3) * (100 * N ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have c3 : loopModK * (q ^ 3 + 1) * ((Val.nat (q ^ 3)).wt + q ^ 3 +
      (natList (List.range (q ^ 3))).wt + 1) ≤ loopModK * (2 * N ^ 3) * (100 * N ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : mapK * (2 * N ^ 3) * (100 * N ^ 6) = 200000 * N ^ 9 := by simp only [mapK]; ring
  have e3 : loopModK * (2 * N ^ 3) * (100 * N ^ 6) = 200000 * N ^ 9 := by
    simp only [loopModK]; ring
  have r9 : (q + 1) ^ 9 = N ^ 9 := rfl
  have c1' : q ^ 3 * (genK * N ^ 3) ≤ genK * N ^ 6 := by rw [← r3]; exact c1
  simp only [cycGensCost, genK] at *
  omega

end GI.Impl
