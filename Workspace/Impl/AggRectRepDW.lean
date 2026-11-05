module

public import Workspace.Impl.AggRectRepS1

@[expose] public section

/-!
# Evaluation with a uniform weight bound

`rcRDW P env e v W c`: the expression `e` computes `v` at cost at most `c`, and `v` weighs at
most `W`. With every value of a computation below one bound `W`, each step costs a fixed multiple
of `W` plus a constant, and the cost of a whole body is a linear expression in `W` (and the costs
of its calls), which `omega` checks.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

/-- `e` computes `v` at cost at most `c`, and `v` weighs at most `W`. -/
def rcRDW (P : Program) (env : List Val) (e : Expr) (v : Val) (W c : ℕ) : Prop :=
  Det P env e v c ∧ v.wt ≤ W

namespace rcRDW

variable {P : Program} {env : List Val} {W : ℕ}

theorem mono {e : Expr} {v : Val} {c c' : ℕ} (h : rcRDW P env e v W c) (hc : c ≤ c') :
    rcRDW P env e v W c' :=
  ⟨h.1.mono hc, h.2⟩

theorem cast {e : Expr} {v v' : Val} {c : ℕ} (h : rcRDW P env e v W c) (hv : v = v') :
    rcRDW P env e v' W c := hv ▸ h

theorem fn {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body) {v w : Val} {c : ℕ}
    (h : rcRDW P [v] body w W c) : FunDet P f v w c :=
  FunDet.intro hf h.1

theorem var {i : ℕ} {v : Val} (h : env[i]? = some v) (hv : v.wt ≤ W) :
    rcRDW P env (.var i) v W (W + 1) :=
  ⟨(Det.var' h).mono (by omega), hv⟩

theorem nat (j : ℕ) (hj : j + 2 ≤ W) : rcRDW P env (.nat j) (.nat j) W (j + 3) :=
  ⟨Det.nat j, (wt_nat_le j).trans hj⟩

theorem get {l : Expr} {vs : List Val} {c j : ℕ} {v : Val} (h : rcRDW P env l (.list vs) W c)
    (hv : vs[j]? = some v) : rcRDW P env (.get l (.nat j)) v W (c + W + j + 4) := by
  have hm : v.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_of_getElem? hv)
  have := h.2
  exact ⟨(Det.get' h.1 (Det.nat j) hv).mono (by omega), by omega⟩

theorem arg {vs rest : List Val} {j : ℕ} {v : Val} (hW : (Val.list vs).wt ≤ W)
    (hv : vs[j]? = some v) : rcRDW P (.list vs :: rest) (GI.Lang.arg j) v W (2 * W + j + 5) :=
  (get (var (env := .list vs :: rest) (i := 0) rfl hW) hv).mono (by omega)

theorem arith {op : BinOp} {a b : Expr} {x y z ca cb : ℕ} (ha : rcRDW P env a (.nat x) W ca)
    (hb : rcRDW P env b (.nat y) W cb) (hz : op.eval x y = z) (hw : (Val.nat z).wt ≤ W) :
    rcRDW P env (.arith op a b) (.nat z) W (ca + cb + W + 1) := by
  subst hz
  exact ⟨(Det.arith ha.1 hb.1).mono (by omega), hw⟩

theorem length {l : Expr} {vs : List Val} {c : ℕ} (h : rcRDW P env l (.list vs) W c) :
    rcRDW P env (.length l) (.nat vs.length) W (c + W + 3) := by
  have h1 := length_lt_wt_list vs
  have h2 := wt_nat_le vs.length
  have h3 : vs.length + 4 ≤ (Val.list vs).wt := by
    rw [wt_list_eq]
    have := length_le_cellsList vs
    have : 2 * vs.length ≤ (vs.map Val.wt).sum := by
      have := sum_size_le_sum_wt vs
      rw [length_cellsList] at *
      omega
    omega
  exact ⟨(Det.length h.1).mono (by have := h.2; omega), by have := h.2; omega⟩

theorem nil (h4 : 4 ≤ W) : rcRDW P env .nil (.list []) W 5 := ⟨Det.nil, by simp; exact h4⟩

theorem mk1 {a : Expr} {va : Val} {ca : ℕ} (ha : rcRDW P env a va W ca)
    (hw : (Val.list [va]).wt ≤ W) : rcRDW P env (GI.Lang.mk1 a) (.list [va]) W (ca + W + 6) :=
  ⟨(Det.mk1 ha.1).mono (by omega), hw⟩

theorem mk2 {a b : Expr} {va vb : Val} {ca cb : ℕ} (ha : rcRDW P env a va W ca)
    (hb : rcRDW P env b vb W cb) (hw : (Val.list [va, vb]).wt ≤ W) :
    rcRDW P env (GI.Lang.mk2 a b) (.list [va, vb]) W (ca + cb + 2 * W + 7) :=
  ⟨(Det.mk2 ha.1 hb.1).mono (by omega), hw⟩

theorem mk3 {a b c : Expr} {va vb vc : Val} {ca cb cc : ℕ} (ha : rcRDW P env a va W ca)
    (hb : rcRDW P env b vb W cb) (hc : rcRDW P env c vc W cc)
    (hw : (Val.list [va, vb, vc]).wt ≤ W) :
    rcRDW P env (GI.Lang.mk3 a b c) (.list [va, vb, vc]) W (ca + cb + cc + 3 * W + 8) :=
  ⟨(Det.mk3 ha.1 hb.1 hc.1).mono (by omega), hw⟩

theorem mk4 {a b c d : Expr} {va vb vc vd : Val} {ca cb cc cd : ℕ} (ha : rcRDW P env a va W ca)
    (hb : rcRDW P env b vb W cb) (hc : rcRDW P env c vc W cc) (hd : rcRDW P env d vd W cd)
    (hw : (Val.list [va, vb, vc, vd]).wt ≤ W) :
    rcRDW P env (GI.Lang.mk4 a b c d) (.list [va, vb, vc, vd]) W
      (ca + cb + cc + cd + 4 * W + 9) :=
  ⟨(Det.mk4 ha.1 hb.1 hc.1 hd.1).mono (by omega), hw⟩

theorem mk5 {a b c d f : Expr} {va vb vc vd vf : Val} {ca cb cc cd cf : ℕ}
    (ha : rcRDW P env a va W ca) (hb : rcRDW P env b vb W cb) (hc : rcRDW P env c vc W cc)
    (hd : rcRDW P env d vd W cd) (hf : rcRDW P env f vf W cf)
    (hw : (Val.list [va, vb, vc, vd, vf]).wt ≤ W) :
    rcRDW P env (GI.Impl.mk5 a b c d f) (.list [va, vb, vc, vd, vf]) W
      (ca + cb + cc + cd + cf + 5 * W + 10) :=
  ⟨(Det.mk5 ha.1 hb.1 hc.1 hd.1 hf.1).mono (by omega), hw⟩

theorem mkList {c : ℕ} (ps : List (Expr × Val)) (h : ∀ p ∈ ps, rcRDW P env p.1 p.2 W c)
    (hw : (Val.list (ps.map Prod.snd)).wt ≤ W) :
    rcRDW P env (Expr.mkList (ps.map Prod.fst)) (.list (ps.map Prod.snd)) W
      (ps.length * (c + W + 1) + 5) :=
  ⟨(Det.mkList ps fun p hp => (h p hp).1).mono
    (by have := Nat.mul_le_mul_left ps.length (show c + (Val.list (ps.map Prod.snd)).wt + 1 ≤
      c + W + 1 by omega); omega), hw⟩

theorem letE {e body : Expr} {v w : Val} {ca cb : ℕ} (ha : rcRDW P env e v W ca)
    (hb : rcRDW P (env ++ [v]) body w W cb) :
    rcRDW P env (.letE e body) w W (ca + cb + W + 1) :=
  ⟨(Det.letE ha.1 hb.1).mono (by have := hb.2; omega), hb.2⟩

theorem call {f : ℕ} {a : Expr} {v w : Val} {ca cb : ℕ} (ha : rcRDW P env a v W ca)
    (hf : FunDet P f v w cb) (hw : w.wt ≤ W) :
    rcRDW P env (.call f a) w W (ca + cb + W + 1) :=
  ⟨(Det.call ha.1 hf).mono (by omega), hw⟩

theorem ite_pos {c t e : Expr} {x : ℕ} {v : Val} {cc ct : ℕ} (hc : rcRDW P env c (.nat x) W cc)
    (hx : x ≠ 0) (ht : rcRDW P env t v W ct) :
    rcRDW P env (.ite c t e) v W (cc + ct + W + 1) :=
  ⟨(Det.ite_pos hc.1 hx ht.1).mono (by have := ht.2; omega), ht.2⟩

theorem ite_zero {c t e : Expr} {v : Val} {cc ce : ℕ} (hc : rcRDW P env c (.nat 0) W cc)
    (he : rcRDW P env e v W ce) : rcRDW P env (.ite c t e) v W (cc + ce + W + 1) :=
  ⟨(Det.ite_zero hc.1 he.1).mono (by have := he.2; omega), he.2⟩

theorem ite {c t e : Expr} {x : ℕ} {v : Val} {cc ct ce : ℕ} (hc : rcRDW P env c (.nat x) W cc)
    (ht : x ≠ 0 → rcRDW P env t v W ct) (he : x = 0 → rcRDW P env e v W ce) :
    rcRDW P env (.ite c t e) v W (cc + ct + ce + W + 1) := by
  by_cases hx : x = 0
  · subst hx; exact (ite_zero hc (he rfl)).mono (by omega)
  · exact (ite_pos hc hx (ht hx)).mono (by omega)

/-- **The safe lookup.** -/
theorem gd (I : RcRIdx) (hf : P.funs[I.gD]? = some rcRGetDF) {le ie de : Expr} {l : List Val}
    {i : ℕ} {d : Val} {cl ci cd : ℕ} (hl : rcRDW P env le (.list l) W cl)
    (hi : rcRDW P env ie (.nat i) W ci) (hd : rcRDW P env de d W cd) :
    rcRDW P env (I.gd le ie de) (l.getD i d) W (cl + ci + cd + 200 * W + 300) := by
  have h3 := wt_list3_le (.list l) (.nat i) d
  refine ⟨(Det.rcGd I hf hl.1 hi.1 hd.1).mono (by have := hl.2; have := hi.2; have := hd.2; omega),
    ?_⟩
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hd.2
  | some y =>
    have : y.wt < (Val.list l).wt := wt_le_wt_list (List.mem_of_getElem? h)
    have := hl.2
    simp only [Option.getD_some]
    omega

/-- **The safe lookup in a list of numbers**, with default `0`. -/
theorem gdN (I : RcRIdx) (hf : P.funs[I.gD]? = some rcRGetDF) {le ie de : Expr} {l : List ℕ}
    {i : ℕ} {cl ci cd : ℕ} (hl : rcRDW P env le (natList l) W cl)
    (hi : rcRDW P env ie (.nat i) W ci) (hd : rcRDW P env de (.nat 0) W cd) :
    rcRDW P env (I.gd le ie de) (.nat (l.getD i 0)) W (cl + ci + cd + 200 * W + 300) := by
  have h := gd I hf (l := l.map Val.nat) hl hi hd
  rw [rcR_getD_natList] at h
  exact h

end rcRDW

/-! ### Small weights -/

theorem rcR_wt_bitW {b W : ℕ} (h : b ≤ 1) (hW : 3 ≤ W) : (Val.nat b).wt ≤ W :=
  (rcR_wt_bit h).trans hW

theorem rcR_eval_eq_wt (a b : ℕ) {W : ℕ} (hW : 3 ≤ W) : (Val.nat (BinOp.eval .eq a b)).wt ≤ W :=
  rcR_wt_bitW (rcR_eval_eq_le a b) hW

theorem rcR_eval_lt_wt (a b : ℕ) {W : ℕ} (hW : 3 ≤ W) : (Val.nat (BinOp.eval .lt a b)).wt ≤ W :=
  rcR_wt_bitW (rcR_eval_lt_le a b) hW

end GI.Impl
