/-
**The induced action on a block system, as a homomorphism.**

A block system is given by representative labels `r` (the value `encFun r`, `ReprVal`), and
`G = ⟨gs⟩` preserves it. The action of `g ∈ G` on the blocks is the permutation `hat r g` of
`Fin n` (`Workspace.Lang.Prims.BlockMath`): it sends the representative `r a` of a block to the
representative `r (g a)` of its image, and fixes the other points. `hatHom` is the
homomorphism `g ↦ hat r g` on `G`.

`blkHomFuns b` (15 functions) sends `[encGroup gs, encFun r]` to
`[encGroup gs, [encPerm (hat r g) | g ∈ gs]]` (`blkHom_det`), which is a value of `hatHom` in the
format `HomVal` of the homomorphism tasks (`blkHom_spec`). Its cost is at most
`blkHomK * ((m + 2) (n + 1))³` for `m` generators.

`tailFuns` (drop the first entry of a list) is a library function that this uses.
-/
module

public import Workspace.Lang.Prims.Graph
public import Workspace.Lang.Lib.SmallGroup

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited
open Equiv

variable {n : ℕ}

/-! ### Dropping the first entry of a list -/

/-- `tail`, at base `b` (three functions): on `x :: xs`, the list `xs`. -/
def tailFuns (b : ℕ) : List Expr :=
  loopFuns b (.arith .sub (.length (.var 0)) (.nat 1)) .nil
    (.snoc (arg 2) (.get (arg 0) (.arith .add (arg 1) (.nat 1))))

/-- **Tail.** -/
theorem tail_spec {P : Program} {b : ℕ} (h : P.HasAt b (tailFuns b)) (x : Val) (xs : List Val) :
    FunDet P b (.list (x :: xs)) (.list xs)
      (loopModK * (xs.length + 1) * (3 * (Val.list (x :: xs)).wt + 1)) := by
  set a := Val.list (x :: xs) with ha
  have hk : Det P [a] (.arith .sub (.length (.var 0)) (.nat 1)) (.nat xs.length) _ :=
    Det.arith' (Det.length (Det.var' (i := 0) rfl)) (Det.nat 1) (by simp [BinOp.eval])
  have hnx := length_lt_wt_list (x :: xs)
  have hxs : (Val.list xs).wt ≤ a.wt := wt_list_sublist (List.sublist_cons_self x xs)
  have hka := wt_nat_le xs.length
  have h2 := a.two_le_size
  have h3 := a.size_le_wt
  simp only [List.length_cons] at hnx
  have har : (Val.list (x :: xs)).wt = a.wt := rfl
  have hl : (x :: xs).length = xs.length + 1 := rfl
  refine (loopMono_spec h hk Det.nil (by omega) (by simp)
    (Inv := fun i acc => acc = .list (xs.take i)) (by simp) (D := fun _ => 0) ?_).mono ?_
  · rintro i acc hi rfl
    have hy : (x :: xs)[i + 1]? = some xs[i] := by simp [hi]
    have dA := Det.arg' (P := P) (vs := [a, .nat i, .list (xs.take i)]) (rest := []) (j := 0) rfl
    have dI := Det.arith' (op := .add) (Det.arg' (P := P) (vs := [a, .nat i, .list (xs.take i)])
      (rest := []) (j := 1) rfl) (Det.nat 1) (z := i + 1) rfl
    refine (Det.snoc (Det.arg' (P := P) (vs := [a, .nat i, .list (xs.take i)]) (rest := []) (j := 2)
      rfl) (Det.get' dA dI hy)).post fun c hc => ?_
    have hr : xs.take (i + 1) = xs.take i ++ [xs[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
    have hyi : xs[i].wt < (Val.list xs).wt := wt_getElem_lt xs i hi
    refine ⟨by beta_reduce; rw [hr], wt_list_mono (List.prefix_append _ _), ?_⟩
    have := wt_stepArg_le a i (.list (xs.take i))
    have h1 := wt_list_mono (List.prefix_append (xs.take i) [xs[i]])
    have := wt_nat_le i
    have := wt_nat_le (i + 1)
    omega
  · rintro w cost ⟨rfl, hc⟩
    simp only [Finset.sum_const_zero, Nat.zero_add, List.take_length] at hc
    rw [List.take_length]
    exact ⟨rfl, hc.trans (Nat.mul_le_mul_left _ (by omega))⟩

/-! ### The homomorphism -/

/-- The action of `G ≤ presR r` on the representatives, as a homomorphism. -/
noncomputable def hatHom (r : Fin n → Fin n) (hr : IsRepr r) (G : Subgroup (Perm (Fin n)))
    (hG : G ≤ presR r) : G →* Perm (Fin n) where
  toFun g := hat r g
  map_one' := hat_one hr
  map_mul' a b := hat_mul hr (hG a.2) (hG b.2)

theorem hatHom_apply_rep {r : Fin n → Fin n} (hr : IsRepr r) {G : Subgroup (Perm (Fin n))}
    (hG : G ≤ presR r) (g : G) (a : Fin n) : hatHom r hr G hG g (r a) = r ((g : Perm (Fin n)) a) :=
  hat_apply_rep hr (hG g.2) a

theorem gens_le_presR {r : Fin n → Fin n} {gs : List (Perm (Fin n))}
    (hgs : ∀ g ∈ gs, g ∈ presR r) : gens gs ≤ presR r :=
  (Subgroup.closure_le _).mpr fun g hg => hgs g hg

/-- The value of the action on the blocks is a homomorphism value. -/
theorem blkHom_homVal {r : Fin n → Fin n} (hr : IsRepr r) {gs : List (Perm (Fin n))}
    (hgs : ∀ g ∈ gs, g ∈ presR r) :
    HomVal n n (.list [encGroup gs, .list (gs.map fun g => encPerm (hat r g))]) (gens gs)
      (hatHom r hr (gens gs) (gens_le_presR hgs)) := by
  refine ⟨gs, gs.map (hat r), by simp [List.map_map, Function.comp_def], rfl, ?_⟩
  induction gs with
  | nil => exact List.Forall₂.nil
  | cons g gs ih =>
    refine List.Forall₂.cons ⟨Subgroup.subset_closure (by simp), rfl⟩ ?_
    refine List.Forall₂.imp (fun a b hab => ?_) (ih fun h hh => hgs h (by simp [hh]))
    obtain ⟨ha, rfl⟩ := hab
    exact ⟨Subgroup.closure_mono (fun x (hx : x ∈ gs) => List.mem_cons_of_mem g hx) ha, rfl⟩

/-! ### The program -/

/-- The entry: on `[encGroup gs, encFun r]`, `[encGroup gs, map hatF over the generators]`. -/
def blkHomEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (.get (arg 0) (.nat 0)))
    (mk2 (arg 0) (.call (b + 7) (mk2 (mk2 (arg 1) (.var 1)) (.call (b + 4) (.get (arg 0) (.nat 1))))))

/-- The program of the action on the blocks, at base `b` (15 functions). -/
def blkHomFuns (b : ℕ) : List Expr :=
  [blkHomEntry b] ++ rangeFuns (b + 1) ++ tailFuns (b + 4) ++ mapFuns (b + 7) (b + 10) ++
    [hatF (b + 11)] ++ mapFuns (b + 11) (b + 14) ++ [hatPtF]

/-- The constant of the action on the blocks. -/
def blkHomK : ℕ := 1000000

/-- **The action on a block system.** On `[encGroup gs, encFun r]`, where every generator
preserves the partition, the result is `[encGroup gs, [encPerm (hat r g) | g ∈ gs]]`. -/
theorem blkHom_det {P : Program} {b : ℕ} (h : P.HasAt b (blkHomFuns b))
    {r : Fin n → Fin n} (hr : IsRepr r) {gs : List (Perm (Fin n))}
    (hgs : ∀ g ∈ gs, g ∈ presR r) :
    FunDet P b (.list [encGroup gs, encFun fun i => (r i : ℕ)])
      (.list [encGroup gs, .list (gs.map fun g => encPerm (hat r g))])
      (blkHomK * ((gs.length + 2) * (n + 1)) ^ 3) := by
  simp only [blkHomFuns] at h
  have he : P.funs[b]? = some (blkHomEntry b) := h.left.left.left.left.left.left.single
  have hrg : P.HasAt (b + 1) (rangeFuns (b + 1)) := by
    simpa using h.left.left.left.left.left.right
  have htl : P.HasAt (b + 4) (tailFuns (b + 4)) := by
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using h.left.left.left.left.right
  have hom : P.HasAt (b + 7) (mapFuns (b + 7) (b + 10)) := by
    simpa [rangeFuns, tailFuns, loopFuns, Nat.add_assoc] using h.left.left.left.right
  have hhf : P.funs[b + 10]? = some (hatF (b + 11)) := by
    simpa [rangeFuns, tailFuns, mapFuns, loopFuns, Nat.add_assoc] using h.left.left.right.single
  have him : P.HasAt (b + 11) (mapFuns (b + 11) (b + 14)) := by
    simpa [rangeFuns, tailFuns, mapFuns, loopFuns, Nat.add_assoc] using h.left.right
  have hhp : P.funs[b + 14]? = some hatPtF := by
    simpa [rangeFuns, tailFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right.single
  generalize hL : (encFun fun i => (r i : ℕ)) = L
  have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := hL ▸ wt_encRepr_le r
  have hO := mapList_spec hom gs encPerm (fun g => encPerm (hat r g))
    (c := .list [L, idsVal n]) (B := 100000 * (n + 1) ^ 3)
    (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun g hg => hL ▸ hatF_spec hhf him hhp hr (hgs g hg))
  set vs : List Val := [encGroup gs, L] with hvs
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have dN := Det.get' (P := P) d0 (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
  have hR := Det.call dN (range_det hrg n)
  have d0' := Det.arg' (P := P) (vs := vs) (rest := [idsVal n]) (j := 0) rfl
  have d1' := Det.arg' (P := P) (vs := vs) (rest := [idsVal n]) (j := 1) rfl
  have dG' := Det.get' d0' (Det.nat 1)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][1]? =
      some (.list (encPerm 1 :: gs.map encPerm)) from rfl)
  have dT := Det.call dG' (tail_spec htl (encPerm 1) (gs.map encPerm))
  have dV := Det.var' (P := P) (env := [Val.list vs, idsVal n]) (i := 1) rfl
  have dC := Det.call (Det.mk2 (Det.mk2 d1' dV) dT) hO
  have hB := Det.letE hR (Det.mk2 d0' dC)
  refine FunDet.intro he (hB.mono ?_)
  clear hB dC dV dT dG' d1' d0' hR dN d0 hO
  have w2 := wt_encGroup_le gs
  have w3 := wt_idsVal_le n
  have w3' := wt_encPerm_le (1 : Perm (Fin n))
  have w4 := wt_list_encPerms_le (1 :: gs)
  have w4' : (Val.list (encPerm 1 :: gs.map encPerm)).wt = (Val.list ((1 :: gs).map encPerm)).wt :=
    rfl
  have w5 := wt_list_encPerms_le gs
  have w6 : (Val.list (gs.map fun g => encPerm (hat r g))).wt ≤
      13 * ((gs.length + 1) * (n + 1)) ^ 2 := by
    have := wt_list_encPerms_le (gs.map (hat r))
    simpa [List.map_map, Function.comp_def] using this
  have w7 := wt_list2_le (encGroup gs) L
  have w8 := wt_list2_le L (idsVal n)
  have w9 := wt_list2_le (.list [L, idsVal n]) (.list (gs.map encPerm))
  have w10 := wt_list2_le (encGroup gs) (.list (gs.map fun g => encPerm (hat r g)))
  have w11 := wt_nat_le n
  have wvs : (Val.list vs).wt = (Val.list [encGroup gs, L]).wt := rfl
  simp only [List.length_cons, List.length_map] at w4 ⊢
  generalize hS : (gs.length + 2) * (n + 1) = S
  obtain ⟨hmS, hnS⟩ := le_S gs.length n
  rw [hS] at hmS hnS
  have hS1 : 1 ≤ S := by omega
  have h2 : ((gs.length + 1) * (n + 1)) ^ 2 ≤ S ^ 2 :=
    Nat.pow_le_pow_left (hS ▸ Nat.mul_le_mul_right _ (by omega)) 2
  have h3 : ((gs.length + 1 + 1) * (n + 1)) ^ 2 = S ^ 2 := by rw [← hS]
  have h3' : ((gs.length + 2) * (n + 1)) ^ 2 = S ^ 2 := by rw [← hS]
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hnS 2
  have hN3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hnS 3
  have hS12 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
  have h4 : gs.length * (100000 * (n + 1) ^ 3) ≤ 100000 * S ^ 3 := by
    have : gs.length * (n + 1) ^ 3 ≤ S ^ 3 := by
      rw [← hS, mul_pow]
      exact Nat.mul_le_mul (le_trans (by omega) (Nat.le_self_pow (by norm_num) _)) le_rfl
    nlinarith
  have h5 : loopModK * (gs.length + 1) * (3 * (Val.list ((1 :: gs).map encPerm)).wt + 1) ≤
      loopModK * S * (40 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h6 : mapK * (gs.length + 1) * ((Val.list [Val.list [L, idsVal n],
      Val.list (List.map encPerm gs)]).wt + (Val.list (gs.map fun g => encPerm (hat r g))).wt + 1)
      ≤ mapK * S * (100 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e5 : loopModK * S * (40 * S ^ 2) = 40000 * S ^ 3 := by simp only [loopModK]; ring
  have e6 : mapK * S * (100 * S ^ 2) = 100000 * S ^ 3 := by simp only [mapK]; ring
  rw [← w4'] at h5
  simp only [blkHomK]
  omega

/-- **The induced action on a block system, as a homomorphism value.** For a block system with
representative labels `r` (from a `ReprVal`, by `ReprVal.elim`) that every generator preserves
(`le_presR`), the result is a `HomVal` of `hatHom`, which sends the representative `r a` to
`r (g a)` (`hatHom_apply_rep`). -/
theorem blkHom_spec {P : Program} {b : ℕ} (h : P.HasAt b (blkHomFuns b))
    {r : Fin n → Fin n} (hr : IsRepr r) {gs : List (Perm (Fin n))}
    (hgs : ∀ g ∈ gs, g ∈ presR r) :
    FunAll P b (.list [encGroup gs, encFun fun i => (r i : ℕ)]) (fun w c =>
      HomVal n n w (gens gs) (hatHom r hr (gens gs) (gens_le_presR hgs)) ∧
      c ≤ blkHomK * ((gs.length + 2) * (n + 1)) ^ 3) :=
  FunAll.mono (blkHom_det h hr hgs) fun _ _ hw => ⟨hw.1 ▸ blkHom_homVal hr hgs, hw.2⟩

end GI.Lang
