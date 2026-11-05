module

public import Workspace.Impl.GenProdGroup

@[expose] public section

/-!
# The product refinement: maps over the pairs

* `map_img_det`: `map` over a list given as the image of a list `L`, when the call on the image of
  each entry of `L` is deterministic;
* `pairUnsq_spec`: on `[c, [key, g × g]]`, the pair `[key, g]` (moves a coset representative of
  the squares back to the points);
* `ones_det`: the constant table `1` of `Fin n`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

/-- `map` over the image of a list. -/
theorem map_img_det {P : Program} {b f : ℕ} (hb : P.HasAt b (mapFuns b f)) {c : Val} {α : Type}
    (L : List α) (g h : α → Val) (hinj : ∀ p ∈ L, ∀ q ∈ L, g p = g q → h p = h q) {B : ℕ}
    (hf : ∀ p ∈ L, FunDet P f (.list [c, g p]) (h p) B) :
    FunDet P b (.list [c, .list (L.map g)]) (.list (L.map h))
      (L.length * B + mapK * (L.length + 1) * ((Val.list [c, .list (L.map g)]).wt +
        (Val.list (L.map h)).wt + 1)) := by
  classical
  let F : Val → Val := fun x => if hx : ∃ p ∈ L, g p = x then h hx.choose else x
  have hF : ∀ p ∈ L, F (g p) = h p := fun p hp => by
    have hx : ∃ q ∈ L, g q = g p := ⟨p, hp, rfl⟩
    show (if hx : ∃ q ∈ L, g q = g p then h hx.choose else g p) = h p
    rw [dif_pos hx]
    exact hinj _ hx.choose_spec.1 _ hp hx.choose_spec.2
  have hmap : (L.map g).map F = L.map h := by
    rw [List.map_map]; exact List.map_congr_left fun p hp => hF p hp
  have := map_det hb (c := c) (xs := L.map g) (F := F) (B := B) (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    rw [hF p hp]; exact hf p hp)
  rw [hmap, List.length_map] at this
  exact this

/-- On `[c, [key, g × g]]` with `c = [k, ids]`: the pair `[key, g]`. -/
def pairUnsqF (fu : ℕ) : Expr :=
  mk2 (.get (arg 1) (.nat 0)) (.call fu (mk2 (arg 0) (.get (arg 1) (.nat 1))))

theorem pairUnsq_spec {P : Program} {f fu bm fe : ℕ} (hf : P.funs[f]? = some (pairUnsqF fu))
    (hfu : P.funs[fu]? = some (tabWrapF bm)) (hbm : P.HasAt bm (mapFuns bm fe))
    (hfe : P.funs[fe]? = some unsqEntF) {k : ℕ} (a : Val) (t : Perm (Fin k)) :
    FunDet P f (.list [cK k, .list [a, encPerm (sqPerm t)]]) (.list [a, encPerm t])
      (sqConvK * (k + 1) ^ 6 + 20 * (Val.list [cK k, .list [a, encPerm (sqPerm t)]]).wt +
        20 * (k + 1) ^ 2 + 100) := by
  set x := Val.list [cK k, .list [a, encPerm (sqPerm t)]] with hx
  obtain ⟨W, hW⟩ : ∃ W, W = x.wt := ⟨_, rfl⟩
  have h0 := Det.arg' (P := P) (vs := [cK k, .list [a, encPerm (sqPerm t)]]) (rest := []) (j := 0)
    rfl
  have h1 := Det.arg' (P := P) (vs := [cK k, .list [a, encPerm (sqPerm t)]]) (rest := []) (j := 1)
    rfl
  have da := Det.get' h1 (Det.nat 0) (v := a) rfl
  have ds := Det.get' h1 (Det.nat 1) (v := encPerm (sqPerm t)) rfl
  have dc := Det.call (Det.mk2 h0 ds) (unsqPerm_spec hfu hbm hfe t)
  refine FunDet.intro hf ((Det.mk2 da dc).mono ?_)
  have hsum := sum_wt_lt_wt_list [cK k, .list [a, encPerm (sqPerm t)]]
  have hsum2 := sum_wt_lt_wt_list [a, encPerm (sqPerm t)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum hsum2
  have w2 := wt_list2_le (cK k) (encPerm (sqPerm t))
  have wt := wt_encPerm_le t
  have wo := wt_list2_le a (encPerm t)
  have ex : (Val.list [cK k, .list [a, encPerm (sqPerm t)]]).wt = x.wt := rfl
  have ec : (Val.list [Val.nat k, encFun fun j : Fin k => (j : ℕ)]).wt = (cK k).wt := rfl
  omega

/-- The constant table `1` of `Fin n`, by `map` over the identity table. -/
theorem ones_det {P : Program} {b f : ℕ} (hb : P.HasAt b (mapFuns b f))
    (hf : P.funs[f]? = some oneF) (n : ℕ) :
    FunDet P b (.list [.nat 0, encFun fun j : Fin n => (j : ℕ)]) (encFun fun _ : Fin n => 1)
      (10 ^ 5 * (n + 1) ^ 3) := by
  have h := map_det hb (c := .nat 0) (xs := (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))
    (F := fun _ => .nat 1) (B := 4) (fun x _ => one_det hf _)
  have he : (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).map fun _ => Val.nat 1) =
      (List.finRange n).map fun _ => Val.nat 1 := by
    rw [List.map_map]; rfl
  rw [he] at h
  refine h.mono ?_
  simp only [List.length_map, List.length_finRange]
  have w1 : (encFun fun _ : Fin n => 1).wt ≤ 4 * (n + 1) ^ 2 :=
    wt_encFun_le_sq _ fun x => by have := x.isLt; omega
  have w2 : (encFun fun j : Fin n => (j : ℕ)).wt ≤ 4 * (n + 1) ^ 2 := wt_ids_le n
  have w3 := wt_list2_le (.nat 0) (encFun fun j : Fin n => (j : ℕ))
  have w0 := wt_nat_le 0
  have e1 : (Val.list (List.map (fun _ => Val.nat 1) (List.finRange n))).wt =
      (encFun fun _ : Fin n => 1).wt := rfl
  have e2 : (Val.list [Val.nat 0, Val.list (List.map (fun i : Fin n => Val.nat ↑i)
      (List.finRange n))]).wt
      = (Val.list [Val.nat 0, encFun fun j : Fin n => (j : ℕ)]).wt := rfl
  have h3 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : (Val.list [Val.nat 0, encFun fun j : Fin n => (j : ℕ)]).wt +
      (encFun fun _ : Fin n => 1).wt + 1 ≤ 30 * (n + 1) ^ 2 :=
    (Nat.add_le_add_right (Nat.add_le_add w3 w1) 1).trans (by omega)
  have h5 := Nat.mul_le_mul_left (mapK * (n + 1)) h4
  have e3 : mapK * (n + 1) * (30 * (n + 1) ^ 2) = 30000 * (n + 1) ^ 3 := by
    simp only [mapK]; ring
  have h6 : n * 4 ≤ 4 * (n + 1) ^ 3 := by
    have : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  calc _ ≤ n * 4 + mapK * (n + 1) * (30 * (n + 1) ^ 2) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ h4) _
    _ ≤ _ := by omega

end GI.Impl
