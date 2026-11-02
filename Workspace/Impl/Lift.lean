import Workspace.Impl.DomRestrict
import Workspace.Lang.Prims.Ops

/-!
# Lifting an answer from the domain back to `Ω`, in `GI.Lang`

Both steps of `Solve` find the answer of the restricted instance: `[]`, or a coset `x' ⟨gs'⟩` of
permutations of the `s` positions of the domain. The answer of `Solve` is its preimage under
the restriction (`State.liftAnswer`). Section 3: "Its caller retains the homomorphism used to
lift the returned generators and representative."

The module `liftFuns b d jpre jfac` (31 functions at base `b`; the restriction module
`domFuns d` must sit at `d`; the cited preimage and factorization primitives at `jpre`, `jfac`)
does this on `[[k, s, domCtx, gens], u']`:

1. `[]` stays `[]`.
2. The graph generators `g ⊕ g|_D` and the generators `g ⊕ 1`, on `Fin (k + s)`, for the
   generators `g` of `G` (`graphMap`, `leftMap`; a permutation `a ⊕ b` is the list of `a`
   followed by `k + b`, `shiftApp`).
3. **Preimage** (cited, [LM, Theorem 3.1(vi)(b)]): generators of the `b ∈ G` with
   `b|_D ∈ ⟨gs'⟩`, on the graph group. Its preconditions: the graph generators preserve
   `Fin k`, and `⟨gs'⟩ ≤ G|_D` because the answer lies in `G|_D` (`liftInst`).
4. **Factorization** (cited, [LM, Theorem 3.1(viii)(c)]): `1 ⊕ x' = (a ⊕ a|_D)(c ⊕ 1)` in the
   product of the graph group and `G ⊕ 1`, which it normalizes (`normalizes_graph`); then
   `a|_D = x'` (`factor_lift`), and `a` is the first `k` entries of `a ⊕ a|_D`.
5. The answer `[a, ⟨preimage⟩]` (`image_liftAnswer_coset`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encGroup gens sumToFin)
open scoped Pointwise

variable {Ω : Type} {k : ℕ}

/-! ### `a ⊕ b` as a list -/

theorem encPerm_sumToFin {n n' : ℕ} (a : Perm (Fin n)) (c : Perm (Fin n')) :
    encPerm (sumToFin (Perm.sumCongr a c)) =
      .list ((List.finRange n).map (fun i => Val.nat (a i)) ++
        (List.finRange n').map (fun j => Val.nat (n + c j))) := by
  simp only [encPerm]
  congr 1
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  congr 1
  · apply List.map_congr_left
    intro i _
    have : (Fin.castLE (Nat.le_add_right n n') i) = Fin.castAdd n' i := Fin.ext rfl
    rw [this, sumToFin_sumCongr_castAdd]
  · apply List.map_congr_left
    intro j _
    rw [sumToFin_sumCongr_natAdd]

/-- On `[k, x]`: `x + k`. -/
def addKF : Expr := .arith .add (arg 1) (arg 0)

/-- On `[a, c, k]`: the list of `a` followed by `k + c`. -/
def shiftAppF (ap am : ℕ) : Expr := .call ap (mk2 (arg 0) (.call am (mk2 (arg 2) (arg 1))))

/-- On `[[domCtx, k], g]`: `g ⊕ g|_D`. -/
def graphGenF (sa rg : ℕ) : Expr :=
  .call sa (mk3 (arg 1) (.call rg (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.get (arg 0) (.nat 1)))

/-- On `[[1_s, k], g]`: `g ⊕ 1`. -/
def leftGenF (sa : ℕ) : Expr :=
  .call sa (mk3 (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))

/-! ### `a ⊕ b` -/

/-- The cost constant of `shiftApp`. -/
def shiftK : ℕ := 10 ^ 7

theorem shiftApp_spec {P : Program} {b : ℕ} (hsa : P.funs[b + 1]? = some (shiftAppF (b + 2) (b + 5)))
    (hap : P.HasAt (b + 2) (appendFuns (b + 2))) (ham : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8)))
    (hadd : P.funs[b + 8]? = some addKF) {n n' : ℕ} (a : Perm (Fin n)) (c : Perm (Fin n')) :
    FunDet P (b + 1) (.list [encPerm a, encPerm c, .nat n]) (encPerm (sumToFin (Perm.sumCongr a c)))
      (shiftK * (n + n' + 1) ^ 3) := by
  set N := n + n' + 1 with hN
  have hn : n + 1 ≤ N := by omega
  have hn' : n' + 1 ≤ N := by omega
  have w1 : (encPerm a).wt ≤ 4 * N ^ 2 :=
    (wt_encPerm_le a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2))
  have w2 : (encPerm c).wt ≤ 4 * N ^ 2 :=
    (wt_encPerm_le c).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn' 2))
  have w3 : (encPerm (sumToFin (Perm.sumCongr a c))).wt ≤ 4 * N ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have p12 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  -- `k + c`
  have wB : (Val.list ((List.finRange n').map fun j => Val.nat (n + c j))).wt ≤ 4 * N ^ 2 := by
    have := wt_encFun_le (fun j : Fin n' => n + c j) (B := n + n') fun j => by
      show n + (c j : ℕ) ≤ n + n'; have := (c j).isLt; omega
    have e : (encFun fun j : Fin n' => n + (c j : ℕ)) =
      .list ((List.finRange n').map fun j => Val.nat (n + c j)) := rfl
    rw [e] at this
    nlinarith
  have hm := mapList_spec ham (List.finRange n') (fun j => Val.nat (c j)) (fun j => Val.nat (n + c j))
    (c := .nat n) (B := 100 * N) (fun j _ j' _ h => by simp only [Val.nat.injEq] at h ⊢; omega)
    (fun j _ => by
      have g0 := Det.arg' (P := P) (vs := [.nat n, .nat (c j)]) (rest := []) (j := 0) rfl
      have g1 := Det.arg' (P := P) (vs := [.nat n, .nat (c j)]) (rest := []) (j := 1) rfl
      refine FunDet.intro hadd ((Det.arith' (op := .add) g1 g0 (z := n + c j)
        (by simp only [BinOp.eval]; omega)).mono ?_)
      have := wt_list2_le (.nat n) (.nat (c j))
      have := wt_nat_le n
      have := wt_nat_le (c j)
      have := (c j).isLt
      omega)
  have e1 : (Val.list ((List.finRange n').map fun j => Val.nat (c j))) = encPerm c := rfl
  rw [e1] at hm
  have g0 := Det.arg' (P := P) (vs := [encPerm a, encPerm c, .nat n]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [encPerm a, encPerm c, .nat n]) (rest := []) (j := 1) rfl
  have g2 := Det.arg' (P := P) (vs := [encPerm a, encPerm c, .nat n]) (rest := []) (j := 2) rfl
  have d1 := Det.call (Det.mk2 g2 g1) hm
  have happ := append_spec hap ((List.finRange n).map fun i => Val.nat (a i))
    ((List.finRange n').map fun j => Val.nat (n + c j))
  have e2 : (Val.list ((List.finRange n).map fun i => Val.nat (a i))) = encPerm a := rfl
  rw [e2, ← encPerm_sumToFin] at happ
  have happ' : FunDet P (b + 2) (.list [encPerm a, .list ((List.finRange n').map fun j =>
      Val.nat (n + c j))]) (encPerm (sumToFin (Perm.sumCongr a c))) (30000 * N ^ 3) := by
    refine happ.mono fun w c' ⟨hw, hc⟩ => ⟨hw, ?_⟩
    subst hw
    have := wt_list2_le (encPerm a) (.list ((List.finRange n').map fun j => Val.nat (n + c j)))
    simp only [List.length_map, List.length_finRange] at hc
    have : loopModK * (n' + 1) * ((Val.list [encPerm a, .list ((List.finRange n').map fun j =>
        Val.nat (n + c j))]).wt + n' + (encPerm (sumToFin (Perm.sumCongr a c))).wt + 1) ≤
        loopModK * N * (30 * N ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hn') (by omega)
    have e3 : loopModK * N * (30 * N ^ 2) = 30000 * N ^ 3 := by simp only [loopModK]; ring
    omega
  refine FunDet.intro hsa ((Det.call (Det.mk2 g0 d1) happ').mono ?_)
  simp only [List.length_finRange] at *
  have := wt_list3_le (encPerm a) (encPerm c) (.nat n)
  have := wt_list2_le (.nat n) (encPerm c)
  have := wt_nat_le n
  have hn'B : n' * (100 * N) ≤ 100 * N ^ 2 := by
    have : n' * (100 * N) ≤ N * (100 * N) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hmk : mapK * (n' + 1) * ((Val.list [Val.nat n, encPerm c]).wt +
      (Val.list ((List.finRange n').map fun j => Val.nat (n + c j))).wt + 1) ≤
      mapK * N * (40 * N ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hn') (by omega)
  have e4 : mapK * N * (40 * N ^ 2) = 40000 * N ^ 3 := by simp only [mapK]; ring
  have := wt_list2_le (encPerm a) (.list ((List.finRange n').map fun j => Val.nat (n + c j)))
  simp only [shiftK]
  omega

/-! ### The module -/

/-- **The lifting entry** (see the module docstring). On `[[k, s, domCtx, encGroup gs], u']`.
The environment after the `let`s: `[input, graph list, left list, graph group, preimage,
preimage group, factorization]`. -/
def liftEntry (b jpre jfac : ℕ) : Expr :=
  .ite (.length (arg 1))
    (.letE (.call (b + 10) (mk2 (mk2 (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 0)))
      (.get (.get (arg 0) (.nat 3)) (.nat 1))))
    (.letE (.call (b + 14) (mk2 (mk2 (.call (b + 24) (.get (arg 0) (.nat 1)))
      (.get (arg 0) (.nat 0))) (.get (.get (arg 0) (.nat 3)) (.nat 1))))
    (.letE (mk2 (.arith .add (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (.var 1))
    (.letE (.prim jpre (mk3 (.get (arg 0) (.nat 0)) (.var 3) (.get (arg 1) (.nat 1))))
    (.letE (.call (b + 17) (mk2 (.get (arg 0) (.nat 0)) (.var 4)))
    (.letE (.prim jfac (mk3 (.var 3)
        (mk2 (.arith .add (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (.var 2))
        (.call (b + 1) (mk3 (.call (b + 24) (.get (arg 0) (.nat 0))) (.get (arg 1) (.nat 0))
          (.get (arg 0) (.nat 0))))))
    (mk2 (.call (b + 27) (mk2 (.get (.var 6) (.nat 0)) (.call (b + 24) (.get (arg 0) (.nat 0)))))
      (.var 5))))))))
    .nil

/-- **The lifting module** at base `b` (31 functions); the restriction module sits at `d`. -/
def liftFuns (b d jpre jfac : ℕ) : List Expr :=
  [liftEntry b jpre jfac] ++ [shiftAppF (b + 2) (b + 5)] ++ appendFuns (b + 2) ++
    mapFuns (b + 5) (b + 8) ++ [addKF] ++ [graphGenF (b + 1) (d + 17)] ++
    mapFuns (b + 10) (b + 9) ++ [leftGenF (b + 1)] ++ mapFuns (b + 14) (b + 13) ++
    mkGroupFuns (b + 17) ++ rangeFuns (b + 24) ++ gatherFuns (b + 27)

theorem length_liftFuns (b d jpre jfac : ℕ) : (liftFuns b d jpre jfac).length = 31 := by
  simp [liftFuns, appendFuns, mapFuns, loopFuns, mkGroupFuns, rangeFuns, gatherFuns]

/-- The blocks of the lifting module. -/
structure LiftAt (P : Program) (b d jpre jfac : ℕ) : Prop where
  entry : P.funs[b]? = some (liftEntry b jpre jfac)
  shiftApp : P.funs[b + 1]? = some (shiftAppF (b + 2) (b + 5))
  append : P.HasAt (b + 2) (appendFuns (b + 2))
  addMap : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8))
  addK : P.funs[b + 8]? = some addKF
  graphGen : P.funs[b + 9]? = some (graphGenF (b + 1) (d + 17))
  graphMap : P.HasAt (b + 10) (mapFuns (b + 10) (b + 9))
  leftGen : P.funs[b + 13]? = some (leftGenF (b + 1))
  leftMap : P.HasAt (b + 14) (mapFuns (b + 14) (b + 13))
  mkGroup : P.HasAt (b + 17) (mkGroupFuns (b + 17))
  range : P.HasAt (b + 24) (rangeFuns (b + 24))
  gather : P.HasAt (b + 27) (gatherFuns (b + 27))

theorem liftAt_of_hasAt {P : Program} {b d jpre jfac : ℕ} (h : P.HasAt b (liftFuns b d jpre jfac)) :
    LiftAt P b d jpre jfac where
  entry := by simpa using (h.block 0 (gs := [liftEntry b jpre jfac]) (by rfl)).single
  shiftApp := by simpa using (h.block 1 (gs := [shiftAppF (b + 2) (b + 5)]) (by rfl)).single
  append := h.block 2 (by rfl)
  addMap := h.block 5 (by rfl)
  addK := by simpa using (h.block 8 (gs := [addKF]) (by rfl)).single
  graphGen := by simpa using (h.block 9 (gs := [graphGenF (b + 1) (d + 17)]) (by rfl)).single
  graphMap := h.block 10 (by rfl)
  leftGen := by simpa using (h.block 13 (gs := [leftGenF (b + 1)]) (by rfl)).single
  leftMap := h.block 14 (by rfl)
  mkGroup := h.block 17 (by rfl)
  range := h.block 24 (by rfl)
  gather := h.block 27 (by rfl)

theorem LiftAt.shift_spec {P : Program} {b d jpre jfac : ℕ} (h : LiftAt P b d jpre jfac) {n n' : ℕ}
    (a : Perm (Fin n)) (c : Perm (Fin n')) :
    FunDet P (b + 1) (.list [encPerm a, encPerm c, .nat n]) (encPerm (sumToFin (Perm.sumCongr a c)))
      (shiftK * (n + n' + 1) ^ 3) :=
  shiftApp_spec h.shiftApp h.append h.addMap h.addK a c

/-! ### The graph generators and the generators `g ⊕ 1` -/

section Gens

variable (e : Ω ≃ Fin k) (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D)

/-- The cost constant of one graph generator. -/
def graphGenK : ℕ := 2 * 10 ^ 12

theorem graphGen_spec {P : Program} {b d jpre jfac : ℕ} (h : LiftAt P b d jpre jfac)
    (hd : DomAt P d) {g : Perm (Fin k)} (hg : g ∈ groupFin e G) :
    FunDet P (b + 9) (.list [.list [domCtx e D, .nat k], encPerm g])
      (encPerm (sumToFin (Perm.sumCongr g (restrP e G D hD g)))) (graphGenK * (k + 1) ^ 6) := by
  have hs : (domFin e D).length ≤ k := length_domFin_le
  have g0 := Det.arg' (P := P) (vs := [.list [domCtx e D, .nat k], encPerm g]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.list [domCtx e D, .nat k], encPerm g]) (rest := []) (j := 1) rfl
  have gc := Det.get' g0 (Det.nat 0) (v := domCtx e D) rfl
  have gk := Det.get' g0 (Det.nat 1) (v := .nat k) rfl
  have dr := Det.call (Det.mk2 gc g1) (restrGen_spec e G D hD hd hg)
  have ds := Det.call (Det.mk3 g1 dr gk) (h.shift_spec g (restrP e G D hD g))
  refine FunDet.intro h.graphGen (ds.mono ?_)
  have w1 : (Val.list [Val.list [domCtx e D, .nat k], encPerm g]).wt ≤ 200 * (k + 1) ^ 2 := by
    have := wt_list2_le (.list [domCtx e D, .nat k]) (encPerm g)
    have := wt_list2_le (domCtx e D) (.nat k)
    have := wt_domCtx_le e D
    have := wt_encPerm_le g
    have := wt_nat_le k
    have : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have w2 : (encPerm (restrP e G D hD g)).wt ≤ 4 * (k + 1) ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have w3 : (encPerm (sumToFin (Perm.sumCongr g (restrP e G D hD g)))).wt ≤ 16 * (k + 1) ^ 2 := by
    refine (wt_encPerm_le _).trans ?_
    have : (k + (domFin e D).length + 1) ^ 2 ≤ (2 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) _
    nlinarith
  have w4 := wt_list2_le (domCtx e D) (encPerm g)
  have w5 := wt_list3_le (encPerm g) (encPerm (restrP e G D hD g)) (.nat k)
  have w6 := wt_domCtx_le e D
  have w7 := wt_encPerm_le g
  have w8 := wt_nat_le k
  have p3 : (k + (domFin e D).length + 1) ^ 3 ≤ 8 * (k + 1) ^ 3 := by
    have : (k + (domFin e D).length + 1) ^ 3 ≤ (2 * (k + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) _
    nlinarith
  have p12 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : (k + 1) ^ 3 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [graphGenK, restrGenK, shiftK] at *
  omega

theorem leftGen_spec {P : Program} {b d jpre jfac : ℕ} (h : LiftAt P b d jpre jfac) {s : ℕ}
    (hs : s ≤ k) (g : Perm (Fin k)) :
    FunDet P (b + 13) (.list [.list [encPerm (1 : Perm (Fin s)), .nat k], encPerm g])
      (encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin s))))) (graphGenK * (k + 1) ^ 6) := by
  have g0 := Det.arg' (P := P) (vs := [.list [encPerm (1 : Perm (Fin s)), .nat k], encPerm g])
    (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.list [encPerm (1 : Perm (Fin s)), .nat k], encPerm g])
    (rest := []) (j := 1) rfl
  have gc := Det.get' g0 (Det.nat 0) (v := encPerm (1 : Perm (Fin s))) rfl
  have gk := Det.get' g0 (Det.nat 1) (v := .nat k) rfl
  have ds := Det.call (Det.mk3 g1 gc gk) (h.shift_spec g (1 : Perm (Fin s)))
  refine FunDet.intro h.leftGen (ds.mono ?_)
  have w1 : (encPerm (1 : Perm (Fin s))).wt ≤ 4 * (k + 1) ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have w3 : (encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin s))))).wt ≤ 16 * (k + 1) ^ 2 := by
    refine (wt_encPerm_le _).trans ?_
    have : (k + s + 1) ^ 2 ≤ (2 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) _
    nlinarith
  have w4 := wt_list2_le (encPerm (1 : Perm (Fin s))) (.nat k)
  have w4' := wt_list2_le (.list [encPerm (1 : Perm (Fin s)), .nat k]) (encPerm g)
  have w5 := wt_list3_le (encPerm g) (encPerm (1 : Perm (Fin s))) (.nat k)
  have w7 := wt_encPerm_le g
  have w8 := wt_nat_le k
  have p3 : (k + s + 1) ^ 3 ≤ 8 * (k + 1) ^ 3 := by
    have : (k + s + 1) ^ 3 ≤ (2 * (k + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) _
    nlinarith
  have p12 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : (k + 1) ^ 3 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [graphGenK, shiftK] at *
  omega

/-- A list of values, each of weight at most `W`. -/
theorem wt_list_map_le {α : Type*} (l : List α) (f : α → Val) {W : ℕ} (hf : ∀ a ∈ l, (f a).wt ≤ W) :
    (Val.list (l.map f)).wt ≤ l.length * (2 * W + 1) + 4 := by
  have h1 := wt_list_le (l.map f)
  have h2 : ((l.map f).map Val.wt).sum ≤ l.length * W := by
    have := List.sum_le_card_nsmul ((l.map f).map Val.wt) W (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact hf)
    simpa using this
  simp only [List.length_map] at h1
  nlinarith

theorem restrP_one : restrP e G D hD 1 = 1 := by
  rw [restrP_of_mem e G D hD (groupFin e G).one_mem]
  exact map_one _

theorem mem_one_cons {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) :
    ∀ g ∈ (1 :: gs), g ∈ groupFin e G := by
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact (groupFin e G).one_mem
  · rw [← hgs]; exact Subgroup.subset_closure hg

/-- The value of the graph generators, with the identity first: a group value. -/
theorem encGroup_graphGensF (gs : List (Perm (Fin k))) :
    encGroup (graphGensF e G D hD gs) = .list [.nat (k + (domFin e D).length),
      .list ((1 :: gs).map fun g => encPerm (sumToFin (Perm.sumCongr g (restrP e G D hD g))))] := by
  simp only [encGroup, encPerms, graphGensF, graphGens, List.map_cons, List.map_map]
  congr 3
  simp only [restrP_one, Perm.sumCongr_one, sumToFin_eq, map_one]
  rfl

theorem encGroup_leftGensF (gs : List (Perm (Fin k))) :
    encGroup (leftGensF e D gs) = .list [.nat (k + (domFin e D).length),
      .list ((1 :: gs).map fun g => encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin (domFin e D).length)))))] := by
  simp only [encGroup, encPerms, leftGensF, List.map_cons, List.map_map]
  simp only [Perm.sumCongr_one, sumToFin_eq, map_one]
  rfl

/-- The weight of a list of permutations of the domain or of `Fin (k + s)`. -/
theorem wt_gensList_le {n : ℕ} (hn : n ≤ 2 * k) (l : List (Perm (Fin k))) (f : Perm (Fin k) → Perm (Fin n)) :
    (Val.list (l.map fun g => encPerm (f g))).wt ≤ 40 * ((l.length + 1) * (k + 1)) ^ 2 := by
  have h := wt_list_map_le l (fun g => encPerm (f g)) (W := 16 * (k + 1) ^ 2) (fun g _ => by
    refine (wt_encPerm_le _).trans ?_
    have : (n + 1) ^ 2 ≤ (2 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) _
    nlinarith)
  have : l.length * (2 * (16 * (k + 1) ^ 2) + 1) + 4 ≤ 40 * ((l.length + 1) * (k + 1)) ^ 2 := by
    have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e1 : ((l.length + 1) * (k + 1)) ^ 2 = (l.length + 1) ^ 2 * (k + 1) ^ 2 := by ring
    have : l.length + 1 ≤ (l.length + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    nlinarith
  omega

/-- The cost constant of a list of graph generators. -/
def gensMapK : ℕ := 10 ^ 13

theorem graphList_spec {P : Program} {b d jpre jfac : ℕ} (h : LiftAt P b d jpre jfac)
    (hd : DomAt P d) {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) :
    FunDet P (b + 10) (.list [.list [domCtx e D, .nat k], .list ((1 :: gs).map encPerm)])
      (.list ((1 :: gs).map fun g => encPerm (sumToFin (Perm.sumCongr g (restrP e G D hD g)))))
      (gensMapK * ((gs.length + 2) * (k + 1)) ^ 7) := by
  have hm := mapList_spec h.graphMap (1 :: gs) encPerm
    (fun g => encPerm (sumToFin (Perm.sumCongr g (restrP e G D hD g))))
    (c := .list [domCtx e D, .nat k]) (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun a ha => graphGen_spec e G D hD h hd (mem_one_cons e G hgs a ha))
  refine hm.mono ?_
  set T := (gs.length + 2) * (k + 1) with hT
  have hT1 : k + 1 ≤ T := Nat.le_mul_of_pos_left _ (by omega)
  have hT2 : gs.length + 2 ≤ T := Nat.le_mul_of_pos_right _ (by omega)
  have hs : (domFin e D).length ≤ k := length_domFin_le
  have w1 := wt_gensList_le (n := k) (by omega) (1 :: gs) id
  have w2 := wt_gensList_le (n := k + (domFin e D).length) (by omega) (1 :: gs)
    (fun g => sumToFin (Perm.sumCongr g (restrP e G D hD g)))
  simp only [List.length_cons, id] at w1 w2
  rw [← hT] at w1 w2
  have w1' : (Val.list ((1 :: gs).map encPerm)).wt ≤ 40 * T ^ 2 := w1
  have w3 := wt_list2_le (.list [domCtx e D, .nat k]) (.list ((1 :: gs).map encPerm))
  have w4 := wt_list2_le (domCtx e D) (.nat k)
  have w5 := wt_domCtx_le e D
  have w6 := wt_nat_le k
  have p2 : (k + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT1 2
  have p6 : (k + 1) ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left hT1 6
  have p12 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
  have p37 : T ^ 3 ≤ T ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (1 :: gs).length * (graphGenK * (k + 1) ^ 6) ≤ graphGenK * T ^ 7 := by
    calc (1 :: gs).length * (graphGenK * (k + 1) ^ 6) ≤ T * (graphGenK * T ^ 6) :=
          Nat.mul_le_mul (by simp; omega) (Nat.mul_le_mul_left _ p6)
      _ = graphGenK * T ^ 7 := by ring
  have h2 : mapK * ((1 :: gs).length + 1) * ((Val.list [.list [domCtx e D, .nat k],
      .list ((1 :: gs).map encPerm)]).wt + (Val.list ((1 :: gs).map fun g =>
        encPerm (sumToFin (Perm.sumCongr g (restrP e G D hD g))))).wt + 1) ≤
      mapK * T * (400 * T ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp; omega)) (by
      have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  have h3 : mapK * T * (400 * T ^ 2) = 400000 * T ^ 3 := by simp only [mapK]; ring
  simp only [gensMapK, graphGenK] at *
  omega

theorem leftList_spec {P : Program} {b d jpre jfac : ℕ} (h : LiftAt P b d jpre jfac)
    (gs : List (Perm (Fin k))) :
    FunDet P (b + 14) (.list [.list [encPerm (1 : Perm (Fin (domFin e D).length)), .nat k],
      .list ((1 :: gs).map encPerm)])
      (.list ((1 :: gs).map fun g =>
        encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin (domFin e D).length))))))
      (gensMapK * ((gs.length + 2) * (k + 1)) ^ 7) := by
  have hs : (domFin e D).length ≤ k := length_domFin_le
  have hm := mapList_spec h.leftMap (1 :: gs) encPerm
    (fun g => encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin (domFin e D).length)))))
    (c := .list [encPerm (1 : Perm (Fin (domFin e D).length)), .nat k])
    (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun a _ => leftGen_spec h hs a)
  refine hm.mono ?_
  set T := (gs.length + 2) * (k + 1) with hT
  have hT1 : k + 1 ≤ T := Nat.le_mul_of_pos_left _ (by omega)
  have hT2 : gs.length + 2 ≤ T := Nat.le_mul_of_pos_right _ (by omega)
  have w1 := wt_gensList_le (n := k) (by omega) (1 :: gs) id
  have w2 := wt_gensList_le (n := k + (domFin e D).length) (by omega) (1 :: gs)
    (fun g => sumToFin (Perm.sumCongr g (1 : Perm (Fin (domFin e D).length))))
  simp only [List.length_cons, id] at w1 w2
  rw [← hT] at w1 w2
  have w1' : (Val.list ((1 :: gs).map encPerm)).wt ≤ 40 * T ^ 2 := w1
  have w3 := wt_list2_le (.list [encPerm (1 : Perm (Fin (domFin e D).length)), .nat k])
    (.list ((1 :: gs).map encPerm))
  have w4 := wt_list2_le (encPerm (1 : Perm (Fin (domFin e D).length))) (.nat k)
  have w5 : (encPerm (1 : Perm (Fin (domFin e D).length))).wt ≤ 4 * (k + 1) ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have w6 := wt_nat_le k
  have p2 : (k + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT1 2
  have p6 : (k + 1) ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left hT1 6
  have p12 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
  have p37 : T ^ 3 ≤ T ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (1 :: gs).length * (graphGenK * (k + 1) ^ 6) ≤ graphGenK * T ^ 7 := by
    calc (1 :: gs).length * (graphGenK * (k + 1) ^ 6) ≤ T * (graphGenK * T ^ 6) :=
          Nat.mul_le_mul (by simp; omega) (Nat.mul_le_mul_left _ p6)
      _ = graphGenK * T ^ 7 := by ring
  have h2 : mapK * ((1 :: gs).length + 1) * ((Val.list [.list [encPerm (1 : Perm (Fin (domFin e D).length)), .nat k],
      .list ((1 :: gs).map encPerm)]).wt + (Val.list ((1 :: gs).map fun g =>
        encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin (domFin e D).length)))))).wt + 1) ≤
      mapK * T * (400 * T ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp; omega)) (by
      have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  have h3 : mapK * T * (400 * T ^ 2) = 400000 * T ^ 3 := by simp only [mapK]; ring
  simp only [gensMapK, graphGenK] at *
  omega

end Gens

/-! ### The first `k` entries -/

theorem encPerm_one_eq (n : ℕ) :
    encPerm (1 : Perm (Fin n)) = natList ((List.finRange n).map Fin.val) := by
  simp only [encPerm, natList, List.map_map, Perm.one_apply]
  rfl

/-- **The first `n` entries of `a ⊕ c` are `a`.** -/
theorem gatherLeft_spec {P : Program} {b : ℕ} (h : P.HasAt b (gatherFuns b)) {n n' : ℕ}
    (a : Perm (Fin n)) (c : Perm (Fin n')) :
    FunDet P b (.list [encPerm (sumToFin (Perm.sumCongr a c)), encPerm (1 : Perm (Fin n))])
      (encPerm a) (gatherK * (40 * (n + n' + 1) ^ 2) ^ 3) := by
  set σ := sumToFin (Perm.sumCongr a c)
  have hg := gather_spec h (L := (List.finRange (n + n')).map fun i => Val.nat (σ i))
    (is := (List.finRange n).map Fin.val) (fun i hi => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
      simp only [List.length_map, List.length_finRange]
      omega)
  have e1 : (Val.list ((List.finRange (n + n')).map fun i => Val.nat (σ i))) = encPerm σ := rfl
  rw [e1, ← encPerm_one_eq] at hg
  have e2 : (Val.list (((List.finRange n).map Fin.val).map fun i =>
      ((List.finRange (n + n')).map fun i => Val.nat (σ i)).getD i (.nat 0))) = encPerm a := by
    simp only [encPerm, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [getD_finRange_map _ _ (by omega)]
    have := sumToFin_sumCongr_castAdd a c i
    simp only [σ]
    rw [← this]
    rfl
  rw [e2] at hg
  refine hg.mono ?_
  have w1 := wt_list2_le (encPerm σ) (encPerm (1 : Perm (Fin n)))
  have w2 := wt_encPerm_le σ
  have w3 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (n + n' + 1) ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have : 1 ≤ (n + n' + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

/-! ### The mathematics of the lift -/

/-- A coset inside a subgroup: its representative and its group lie in the subgroup. -/
theorem mem_of_coset_subset {n : ℕ} {H K : Subgroup (Perm (Fin n))} {x : Perm (Fin n)}
    (hsub : x • (K : Set (Perm (Fin n))) ⊆ H) : x ∈ H ∧ K ≤ H := by
  have hx : x ∈ H := hsub ⟨1, K.one_mem, mul_one x⟩
  refine ⟨hx, fun g hg => ?_⟩
  have hxg : x * g ∈ H := hsub ⟨g, hg, rfl⟩
  have := H.mul_mem (H.inv_mem hx) hxg
  rwa [inv_mul_cancel_left] at this

section Math

variable {C : Type} (e : Ω ≃ Fin k) (S : State Ω C)

/-- The answer of the restricted instance lies in the image of the restriction, so its
representative and its group do. -/
theorem lift_hyps {A' : Set (Perm S.dom)} (hA' : A' ⊆ (restrictHom S.G S.dom S.dom_inv).range)
    {x' : Perm (Fin (domFin e S.dom).length)} {gs' : List (Perm (Fin (domFin e S.dom).length))}
    (hA : toFin (domEquiv e S.dom) '' A' = x' • (gens gs' : Set _)) :
    x' ∈ (restrK e S.G S.dom S.dom_inv).range ∧ gens gs' ≤ (restrK e S.G S.dom S.dom_inv).range := by
  refine mem_of_coset_subset ?_
  rw [← hA, range_restrK]
  rintro _ ⟨σ, hσ, rfl⟩
  exact Subgroup.mem_map_of_mem _ (hA' hσ)

end Math

/-! ### Reading entries -/

theorem Det.read2 {P : Program} {vs ws : List Val} {rest : List Val} {i j : ℕ} {v : Val}
    (h1 : vs[i]? = some (.list ws)) (h2 : ws[j]? = some v) :
    Det P (.list vs :: rest) (.get (arg i) (.nat j)) v (3 * (Val.list vs).wt + i + j + 10) := by
  refine (Det.get' (Det.arg' h1) (Det.nat j) h2).mono ?_
  obtain ⟨hi, hv1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h2
  have a1 := wt_getElem_lt vs i hi
  have a2 := wt_getElem_lt ws j hj
  rw [hv1] at a1
  omega

theorem Det.read3 {P : Program} {vs ws us : List Val} {rest : List Val} {i j l : ℕ} {v : Val}
    (h1 : vs[i]? = some (.list ws)) (h2 : ws[j]? = some (.list us)) (h3 : us[l]? = some v) :
    Det P (.list vs :: rest) (.get (.get (arg i) (.nat j)) (.nat l)) v
      (4 * (Val.list vs).wt + i + j + l + 20) := by
  refine (Det.get' (Det.read2 h1 h2) (Det.nat l) h3).mono ?_
  obtain ⟨hi, hv1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hj, hv2⟩ := List.getElem?_eq_some_iff.mp h2
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp h3
  have a1 := wt_getElem_lt vs i hi
  have a2 := wt_getElem_lt ws j hj
  have a3 := wt_getElem_lt us l hl
  rw [hv1] at a1
  rw [hv2] at a2
  omega

end GI.Impl
