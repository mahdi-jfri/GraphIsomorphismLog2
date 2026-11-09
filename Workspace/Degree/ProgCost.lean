module

public import Workspace.Lang.Lib.Tabulate

/-!
# Cost bounds with one budget

The recognition program and the graph program have many small functions. Their cost bounds need not
be sharp. Each proof fixes a budget `T`, polynomial in a size `X`, that exceeds the weights of the
environment and the cost of each call. Then a body of fixed shape costs a fixed multiple of `T`.

* `Lv P env T e v m`: `e` evaluates to `v` at cost at most `m * T`. The rules below compute `m`, so
  a proof needs only the side conditions on `T`.
* `pc K d X = K * (X + 1) ^ d`, with `pc_mono`.
* `tab_lv`: tabulating, in this style.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- `K * (X + 1) ^ d`. -/
def pc (K d X : ℕ) : ℕ := K * (X + 1) ^ d

theorem pc_mono {K K' d d' : ℕ} (X : ℕ) (hK : K ≤ K') (hd : d ≤ d') : pc K d X ≤ pc K' d' X :=
  Nat.mul_le_mul hK (Nat.pow_le_pow_right (by omega) hd)

theorem pc_self (K X : ℕ) : K ≤ pc K 0 X := by simp [pc]

theorem le_pc_one (X : ℕ) : X + 1 ≤ pc 1 1 X := by simp [pc]

theorem pc_add (K K' d d' X : ℕ) : pc K d X + pc K' d' X ≤ pc (K + K') (d + d') X := by
  have h1 := pc_mono X (show K ≤ K by omega) (show d ≤ d + d' by omega)
  have h2 := pc_mono X (show K' ≤ K' by omega) (show d' ≤ d + d' by omega)
  have : pc (K + K') (d + d') X = pc K (d + d') X + pc K' (d + d') X := by
    simp only [pc]; ring
  omega

theorem pc_mul (K K' d d' X : ℕ) : pc K d X * pc K' d' X = pc (K * K') (d + d') X := by
  simp only [pc, pow_add]; ring

/-- `f` is bounded by a polynomial. -/
def PolyB (f : ℕ → ℕ) : Prop := ∃ K d, ∀ n, f n ≤ pc K d n

namespace PolyB

theorem const (c : ℕ) : PolyB fun _ => c := ⟨c, 0, fun n => by simp [pc]⟩

theorem id : PolyB fun n => n := ⟨1, 1, fun n => by simp [pc]⟩

theorem add {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun n => f n + g n := by
  obtain ⟨K, d, h⟩ := hf
  obtain ⟨K', d', h'⟩ := hg
  exact ⟨K + K', d + d', fun n => (Nat.add_le_add (h n) (h' n)).trans (pc_add _ _ _ _ _)⟩

theorem mul {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun n => f n * g n := by
  obtain ⟨K, d, h⟩ := hf
  obtain ⟨K', d', h'⟩ := hg
  exact ⟨K * K', d + d', fun n => (Nat.mul_le_mul (h n) (h' n)).trans (pc_mul _ _ _ _ _).le⟩

theorem pow {f : ℕ → ℕ} (hf : PolyB f) (k : ℕ) : PolyB fun n => f n ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem mono {f g : ℕ → ℕ} (hg : PolyB g) (h : ∀ n, f n ≤ g n) : PolyB f := by
  obtain ⟨K, d, hg⟩ := hg
  exact ⟨K, d, fun n => (h n).trans (hg n)⟩

end PolyB

/-- Prove `PolyB` of an expression. -/
macro "poly" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | with_reducible apply PolyB.const
  | with_reducible apply PolyB.id
  | with_reducible apply PolyB.add
  | with_reducible apply PolyB.mul
  | with_reducible apply PolyB.pow)

/-- A multiple of a budget. -/
def Lv (P : Program) (env : List Val) (T : ℕ) (e : Expr) (v : Val) (m : ℕ) : Prop :=
  Det P env e v (m * T)

namespace Lv

variable {P : Program} {env : List Val} {T : ℕ}

theorem det {e : Expr} {v : Val} {m : ℕ} (h : Lv P env T e v m) : Det P env e v (m * T) := h

theorem wt_lt {e : Expr} {v : Val} {m : ℕ} (h : Lv P env T e v m) : v.wt < m * T := Det.wt_lt h

theorem var {i : ℕ} {v : Val} (h : env[i]? = some v) (hT : v.wt + 1 ≤ T) :
    Lv P env T (.var i) v 1 :=
  (Det.var' h).mono (by omega)

theorem arg {vs rest : List Val} {j : ℕ} {v : Val} (h : vs[j]? = some v)
    (hT : 2 * (Val.list vs).wt + j + 5 ≤ T) : Lv P (.list vs :: rest) T (GI.Lang.arg j) v 1 :=
  (Det.arg' h).mono (by omega)

theorem nat (k : ℕ) (hT : k + 3 ≤ T) : Lv P env T (.nat k) (.nat k) 1 :=
  (Det.nat k).mono (by omega)

theorem nil (hT : 5 ≤ T) : Lv P env T .nil (.list []) 1 := Det.nil.mono (by omega)

theorem arith {op : BinOp} {a b : Expr} {x y z ma mb : ℕ} (ha : Lv P env T a (.nat x) ma)
    (hb : Lv P env T b (.nat y) mb) (hz : op.eval x y = z) (hT : z + 3 ≤ T) :
    Lv P env T (.arith op a b) (.nat z) (ma + mb + 1) :=
  (Det.arith' ha hb hz).mono (by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega)

theorem get {l i : Expr} {vs : List Val} {x ma mb : ℕ} {v : Val}
    (ha : Lv P env T l (.list vs) ma) (hb : Lv P env T i (.nat x) mb) (hv : vs[x]? = some v) :
    Lv P env T (.get l i) v (2 * ma + mb + 1) := by
  have h1 := Det.get' ha hb hv
  have h2 := h1.wt_lt
  have h3 : v.wt < (Val.list vs).wt := by
    obtain ⟨hx, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    exact wt_getElem_lt vs x hx
  have h4 := ha.wt_lt
  refine h1.mono ?_
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
  have : T ≥ 0 := Nat.zero_le _
  by_cases hT : T = 0
  · subst hT; simp at h4
  · have : 1 ≤ 1 * T := by omega
    omega

theorem length {l : Expr} {vs : List Val} {ma : ℕ} (ha : Lv P env T l (.list vs) ma)
    (hT : 3 ≤ T) : Lv P env T (.length l) (.nat vs.length) (2 * ma + 1) := by
  have h1 := Det.length ha
  have h3 := length_lt_wt_list vs
  have h4 := ha.wt_lt
  refine h1.mono ?_
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

theorem snoc {l e : Expr} {vs : List Val} {v : Val} {ma mb : ℕ} (ha : Lv P env T l (.list vs) ma)
    (hb : Lv P env T e v mb) (hT : 3 ≤ T) :
    Lv P env T (.snoc l e) (.list (vs ++ [v])) (2 * ma + 3 * mb + 1) := by
  have h1 := Det.snoc ha hb
  have h3 := wt_list_snoc_le vs v
  have h4 := ha.wt_lt
  have h5 := hb.wt_lt
  refine h1.mono ?_
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  omega

theorem mk1 {a : Expr} {x : Val} {ma : ℕ} (ha : Lv P env T a x ma) (hT : 5 ≤ T) :
    Lv P env T (GI.Lang.mk1 a) (.list [x]) (2 * 1 + 3 * ma + 1) :=
  snoc (nil hT) ha (by omega)

theorem mk2 {a b : Expr} {x y : Val} {ma mb : ℕ} (ha : Lv P env T a x ma)
    (hb : Lv P env T b y mb) (hT : 5 ≤ T) :
    Lv P env T (GI.Lang.mk2 a b) (.list [x, y]) (2 * (2 * 1 + 3 * ma + 1) + 3 * mb + 1) :=
  snoc (mk1 ha hT) hb (by omega)

theorem mk3 {a b c : Expr} {x y z : Val} {ma mb mc : ℕ} (ha : Lv P env T a x ma)
    (hb : Lv P env T b y mb) (hc : Lv P env T c z mc) (hT : 5 ≤ T) :
    Lv P env T (GI.Lang.mk3 a b c) (.list [x, y, z])
      (2 * (2 * (2 * 1 + 3 * ma + 1) + 3 * mb + 1) + 3 * mc + 1) :=
  snoc (mk2 ha hb hT) hc (by omega)

theorem mk4 {a b c d : Expr} {x y z w : Val} {ma mb mc md : ℕ} (ha : Lv P env T a x ma)
    (hb : Lv P env T b y mb) (hc : Lv P env T c z mc) (hd : Lv P env T d w md) (hT : 5 ≤ T) :
    Lv P env T (GI.Lang.mk4 a b c d) (.list [x, y, z, w])
      (2 * (2 * (2 * (2 * 1 + 3 * ma + 1) + 3 * mb + 1) + 3 * mc + 1) + 3 * md + 1) :=
  snoc (mk3 ha hb hc hT) hd (by omega)

theorem letE {e body : Expr} {v w : Val} {ma mb : ℕ} (ha : Lv P env T e v ma)
    (hb : Lv P (env ++ [v]) T body w mb) : Lv P env T (.letE e body) w (ma + 2 * mb) := by
  have h1 := Det.letE ha hb
  have h5 := hb.wt_lt
  refine h1.mono ?_
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

theorem call {f : ℕ} {a : Expr} {x w : Val} {ma c : ℕ} (ha : Lv P env T a x ma)
    (hf : FunDet P f x w c) (hc : c ≤ T) : Lv P env T (.call f a) w (ma + 2) := by
  have h1 := Det.call ha hf
  have h5 := hf.wt_lt
  refine h1.mono ?_
  rw [Nat.add_mul]
  omega

/-- `if` on a known test, the true branch. -/
theorem ite_pos {c t e : Expr} {x mc mt : ℕ} {v : Val} (hc : Lv P env T c (.nat x) mc) (hx : x ≠ 0)
    (ht : Lv P env T t v mt) : Lv P env T (.ite c t e) v (mc + 2 * mt) := by
  have h1 := Det.ite_pos (e := e) hc hx ht
  have h5 := ht.wt_lt
  refine h1.mono ?_
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-- `if` on a known test, the false branch. -/
theorem ite_zero {c t e : Expr} {mc me : ℕ} {v : Val} (hc : Lv P env T c (.nat 0) mc)
    (he : Lv P env T e v me) : Lv P env T (.ite c t e) v (mc + 2 * me) := by
  have h1 := Det.ite_zero (t := t) hc he
  have h5 := he.wt_lt
  refine h1.mono ?_
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

theorem mono {e : Expr} {v : Val} {m m' : ℕ} (h : Lv P env T e v m) (hm : m ≤ m') :
    Lv P env T e v m' :=
  Det.mono h (Nat.mul_le_mul_right _ hm)

end Lv

/-- `Lv` for the body of a function. -/
theorem funDet_of_lv {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body) {v w : Val}
    {T m : ℕ} (h : Lv P [v] T body w m) : FunDet P f v w (m * T) :=
  FunDet.intro hf h

/-- Tabulating, with a budget that bounds the cost of an entry and the weights. -/
theorem tab_cost {m : ℕ} {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {F : Fin m → Val} {B W : ℕ} (hf : ∀ i : Fin m, FunDet P f (.list [c, .nat i]) (F i) B)
    (hW : (Val.list [c, encFun fun i : Fin m => (i : ℕ)]).wt + (Val.list ((List.finRange m).map F)).wt
      + 1 ≤ W) :
    FunDet P b (.list [c, encFun fun i : Fin m => (i : ℕ)]) (.list ((List.finRange m).map F))
      (m * B + mapK * (m + 1) * W) :=
  (tabulate_spec h hf).mono (by
    have := Nat.mul_le_mul_left (mapK * (m + 1)) hW
    omega)

end GI.Degree
