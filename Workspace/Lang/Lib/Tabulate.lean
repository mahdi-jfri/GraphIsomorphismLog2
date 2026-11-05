/-
Small tools for the wrapper of Algorithm 1 (`Workspace/Assembly/Build.lean`,
`Workspace/Assembly/Convert.lean`).

* `tabulate_spec`: `map f` over the points `0, …, m - 1` (the value `encFun id`) tabulates a
  function `F : Fin m → Val` when `f` computes `F i` on `[c, i]`.
* `Det.mkList`: a list of deterministic pieces is deterministic.
* `FunDet.wt_lt`, `Det.wt_lt`: the weight of a result is below its cost bound.
* `mul_pow_le`, `pow_le_pow_of_le`: arithmetic for cost bounds of the form `C * (n + 1) ^ d`.
-/
module

public import Workspace.Lang.Lib.Graph

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)

/-! ### Weights from cost bounds -/

/-- A deterministic function's result weighs less than its cost bound. -/
theorem FunDet.wt_lt {P : Program} {f : ℕ} {v w : Val} {c : ℕ} (h : FunDet P f v w c) :
    w.wt < c := by
  obtain ⟨body, -, h⟩ := h
  obtain ⟨v', c', -, ⟨⟨rfl, hc⟩, hw⟩⟩ := h.wt_lt.exists_eval
  omega

/-- A deterministic expression's value weighs less than its cost bound. -/
theorem Det.wt_lt {P : Program} {env : List Val} {e : Expr} {v : Val} {c : ℕ}
    (h : Det P env e v c) : v.wt < c := by
  obtain ⟨v', c', -, ⟨⟨rfl, hc⟩, hw⟩⟩ := (EvalAll.wt_lt h).exists_eval
  omega

/-! ### Arithmetic of polynomial bounds -/

theorem mul_pow_le {a b A B X i j : ℕ} (ha : a ≤ A * X ^ i) (hb : b ≤ B * X ^ j) :
    a * b ≤ (A * B) * X ^ (i + j) :=
  calc a * b ≤ (A * X ^ i) * (B * X ^ j) := Nat.mul_le_mul ha hb
    _ = (A * B) * X ^ (i + j) := by rw [pow_add]; ring

theorem pow_le_pow_of_le {i j : ℕ} (n : ℕ) (h : i ≤ j) : (n + 1) ^ i ≤ (n + 1) ^ j :=
  Nat.pow_le_pow_right (by omega) h

theorem one_le_pow_succ (n i : ℕ) : 1 ≤ (n + 1) ^ i := Nat.one_le_pow _ _ (by omega)

theorem loopModK_mul (a Y : ℕ) : loopModK * a * Y = 1000 * (a * Y) := by
  simp only [loopModK]; ring

theorem mapK_mul (a Y : ℕ) : mapK * a * Y = 1000 * (a * Y) := by
  simp only [mapK]; ring

theorem sq_le_pow (n : ℕ) : n * n + 2 * n + 1 = (n + 1) ^ 2 := by ring

/-! ### Lists of deterministic pieces -/

/-- **A list of deterministic pieces.** If every piece `p.1` computes `p.2` at cost at most `c`,
the list expression computes the list of the values. -/
theorem Det.mkList {P : Program} {env : List Val} {c : ℕ} (ps : List (Expr × Val))
    (h : ∀ p ∈ ps, Det P env p.1 p.2 c) :
    Det P env (Expr.mkList (ps.map Prod.fst)) (.list (ps.map Prod.snd))
      (ps.length * (c + (Val.list (ps.map Prod.snd)).wt + 1) + 5) := by
  induction ps using List.reverseRecOn with
  | nil => exact Det.nil.mono (by simp)
  | append_singleton ps p ih =>
    have ih' := ih fun q hq => h q (by simp [hq])
    have hp := h p (by simp)
    have e : Expr.mkList ((ps ++ [p]).map Prod.fst) =
        .snoc (Expr.mkList (ps.map Prod.fst)) p.1 := by
      simp [Expr.mkList, List.foldl_append]
    rw [e]
    have hm := wt_list_mono (show ps.map Prod.snd <+: (ps ++ [p]).map Prod.snd by simp)
    simp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
      List.length_cons, List.length_nil] at hm ⊢
    refine (Det.snoc ih' hp).mono ?_
    have := Nat.mul_le_mul_left ps.length
      (show c + (Val.list (ps.map Prod.snd)).wt + 1 ≤
        c + (Val.list (ps.map Prod.snd ++ [p.2])).wt + 1 by omega)
    rw [Nat.add_mul, Nat.zero_add, Nat.one_mul]
    omega

/-! ### Tabulating a function on the points -/

/-- **Tabulating.** If `f` computes `F i` on `[c, i]` at cost at most `B` for every point `i`,
then `map f` on `[c, [0, …, m - 1]]` computes the list of the `F i`. -/
theorem tabulate_spec {m : ℕ} {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {F : Fin m → Val} {B : ℕ}
    (hf : ∀ i : Fin m, FunDet P f (.list [c, .nat i]) (F i) B) :
    FunDet P b (.list [c, encFun fun i : Fin m => (i : ℕ)]) (.list ((List.finRange m).map F))
      (m * B + mapK * (m + 1) * ((Val.list [c, encFun fun i : Fin m => (i : ℕ)]).wt +
        (Val.list ((List.finRange m).map F)).wt + 1)) := by
  have hM := map_spec (c := c) (xs := (List.finRange m).map fun i : Fin m => Val.nat (i : ℕ)) h
    (R := fun x w => ∀ i : Fin m, x = .nat i → w = F i) (B := fun _ => B) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (hf i) fun w c hw => ⟨fun j hj => ?_, hw.2⟩
      have : j = i := Fin.ext (by simpa using hj.symm)
      rw [hw.1, this])
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = (List.finRange m).map F := forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map, List.length_finRange, sum_const_finRange] at hc
  exact hc

/-- The weight of the points `[0, …, m - 1]`. -/
theorem wt_ids_le (m : ℕ) : (encFun fun i : Fin m => (i : ℕ)).wt ≤ 4 * (m + 1) ^ 2 :=
  wt_encFun_le_sq _ fun i => i.isLt.le

end GI.Lang

namespace GI.Lang

open GI.Cited (Val)

/-- Adding one entry at the front of a list adds at most twice its weight plus 2. -/
theorem wt_list_cons_le (x : Val) (l : List Val) :
    (Val.list (x :: l)).wt ≤ (Val.list l).wt + 2 * x.wt + 2 := by
  have h := wt_list_snoc_le l x
  have e : (Val.list (x :: l)).wt = (Val.list (l ++ [x])).wt := by
    rw [wt_list_eq, wt_list_eq]
    simp only [List.map_cons, List.map_append, List.map_nil, List.sum_cons, List.sum_append,
      List.sum_nil, List.length_cons, List.length_append, List.length_nil]
    rw [Nat.add_comm x.size, Nat.add_comm x.wt]
    simp
  omega

end GI.Lang
