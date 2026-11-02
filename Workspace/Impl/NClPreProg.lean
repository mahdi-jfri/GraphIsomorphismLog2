import Workspace.Impl.NClPreMath
import Workspace.Lang.Lib.Schreier
import Workspace.Lang.Lib.LinIntTake
import Workspace.Lang.Prims.BlockHom
import Workspace.Lang.Lib.NatList

/-!
# The preimage as a program (layout, points, selection)

The program `preFuns b j` (64 functions at base `b`, the pointwise stabilizer algorithm as
primitive `j`), on `[n, encGroup (sumToFin ds), encGroup ms]`:
* `b`: the entry. It computes the kernel (pointwise stabilizer of the points `n, …, N - 1`),
  a lift of each `m ∈ 1 :: ms` (map of `b + 7`), restricts `1`, the lifts and the kernel
  generators to the first `n` points, and compresses with one more pointwise stabilizer call
  at no points.
* `b + 1 … b + 3`: the points `n, …, N - 1`. `b + 4 … b + 6`: map of the lift `b + 7`.
* `b + 8 … b + 10`: iterate the sifting step `b + 11` over the points of `Δ`.
* `b + 12 … b + 34`: Schreier transversal. `b + 35 … b + 37`: fold of the selection `b + 38`.
* `b + 39 … b + 42`: composition. `b + 43 … b + 54`: inverse. `b + 55 … b + 57`: append.
* `b + 58 … b + 60`: map of take `b + 61 … b + 63`.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv
open GI.Machine (BinOp)

/-- The points `n + i`, `i < N - n`, on `[n, N]`. -/
def prePtsFuns (b : ℕ) : List Expr :=
  loopFuns b (.arith .sub (arg 1) (arg 0)) .nil
    (.snoc (arg 2) (.arith .add (.get (arg 0) (.nat 0)) (arg 1)))

/-- The selection step, on `[β, acc, [[β'], t]]`: `t` if `β' = β`, else `acc`. -/
def preSelF : Expr :=
  .ite (.arith .eq (.get (.get (arg 2) (.nat 0)) (.nat 0)) (arg 0)) (.get (arg 2) (.nat 1)) (arg 1)

/-- The sifting step, on `[[a0, encPerm m], i, [encPerm x, pts]]`. -/
def preSiftF (b j : ℕ) : Expr :=
  let a0 := Expr.get (arg 0) (.nat 0)
  let nE := Expr.get a0 (.nat 0)
  let dv := Expr.get a0 (.nat 1)
  let bigN := Expr.get dv (.nat 0)
  let mE := Expr.get (arg 0) (.nat 1)
  .letE (.prim j (mk2 dv (.get (arg 2) (.nat 1))))
    (.letE (.call (b + 12) (.snoc (mk4 (.nat 0) (.var 1) (mk1 (.arith .add nE (arg 1))) bigN) bigN))
      (.letE (.call (b + 35) (mk3 (.get (.call (b + 43) (.get (arg 2) (.nat 0)))
          (.arith .add nE (.get mE (arg 1)))) (.var 2) (.nat 0)))
        (mk2 (.call (b + 39) (mk2 (.get (arg 2) (.nat 0)) (.var 3)))
          (.snoc (.get (arg 2) (.nat 1)) (.arith .add nE (arg 1))))))

/-- The lift of `m`, on `[a0, encPerm m]`: iterate the sifting step `n'` times from
`[encPerm 1, []]` and keep the permutation. -/
def preLiftF (b : ℕ) : Expr :=
  .get (.call (b + 8) (mk3 (.var 0) (.get (.get (arg 0) (.nat 2)) (.nat 0))
    (mk2 (.get (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.nat 0)) .nil))) (.nat 0)

/-- The entry, on `a0 = [n, Dv, Mv]`. -/
def preEntry (b j : ℕ) : Expr :=
  .letE (.prim j (mk2 (arg 1) (.call (b + 1) (mk2 (arg 0) (.get (arg 1) (.nat 0))))))
    (.letE (.call (b + 4) (mk2 (.var 0) (.get (arg 2) (.nat 1))))
      (.letE (.call (b + 55) (mk2 (.call (b + 55) (mk2 (mk1 (.get (.get (arg 1) (.nat 1)) (.nat 0)))
          (.var 2))) (.var 1)))
        (.letE (.call (b + 58) (mk2 (arg 0) (.var 3)))
          (.prim j (mk2 (mk2 (arg 0) (.var 4)) .nil)))))

/-- **The program of the preimage.** -/
def preFuns (b j : ℕ) : List Expr :=
  [preEntry b j] ++ prePtsFuns (b + 1) ++ mapFuns (b + 4) (b + 7) ++ [preLiftF b] ++
    iterFuns (b + 8) (b + 11) ++ [preSiftF b j] ++ schreierFuns (b + 12) ++
    foldlFuns (b + 35) (b + 38) ++ [preSelF] ++ composeFuns (b + 39) ++ invFuns (b + 43) ++
    appendFuns (b + 55) ++ mapFuns (b + 58) (b + 61) ++ linTakeFuns (b + 61)

structure PreAt (P : Program) (b j : ℕ) (h : PointwiseStab) : Prop where
  entry : P.funs[b]? = some (preEntry b j)
  pts : P.HasAt (b + 1) (prePtsFuns (b + 1))
  map1 : P.HasAt (b + 4) (mapFuns (b + 4) (b + 7))
  lift : P.funs[b + 7]? = some (preLiftF b)
  iter : P.HasAt (b + 8) (iterFuns (b + 8) (b + 11))
  sift : P.funs[b + 11]? = some (preSiftF b j)
  sch : P.HasAt (b + 12) (schreierFuns (b + 12))
  fold : P.HasAt (b + 35) (foldlFuns (b + 35) (b + 38))
  sel : P.funs[b + 38]? = some preSelF
  comp : P.HasAt (b + 39) (composeFuns (b + 39))
  inv : P.HasAt (b + 43) (invFuns (b + 43))
  app : P.HasAt (b + 55) (appendFuns (b + 55))
  map2 : P.HasAt (b + 58) (mapFuns (b + 58) (b + 61))
  take : P.HasAt (b + 61) (linTakeFuns (b + 61))
  prim : P.prims[j]? = some (pointwiseStabPrim h)

theorem length_schreierFuns (b : ℕ) : (schreierFuns b).length = 23 := by
  simp [schreierFuns, length_orbTFuns]

theorem preAt_of {P : Program} {b j : ℕ} {h : PointwiseStab} (hP : P.HasAt b (preFuns b j))
    (hj : P.prims[j]? = some (pointwiseStabPrim h)) : PreAt P b j h := by
  simp only [preFuns] at hP
  have L := length_schreierFuns (b + 12)
  refine ⟨hP.left.left.left.left.left.left.left.left.left.left.left.left.left.single, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hj⟩
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.left.left.left.left.left.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.left.left.left.left.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.left.left.left.left.left.right.single
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.left.left.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.left.left.left.right.single
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.left.right.single
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.left.right
  · simpa [prePtsFuns, mapFuns, iterFuns, foldlFuns, composeFuns, invFuns, rangeFuns, findFuns, appendFuns, loopFuns, L, Nat.add_assoc] using
      hP.right

/-- An operation on numbers with a bound `W` on the weight of its result. -/
theorem nclDet_arith_le {P : Program} {env : List Val} {op : BinOp} {a b : Expr} {x y z ca cb W : ℕ}
    (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb) (hz : op.eval x y = z)
    (hW : (Val.nat z).wt ≤ W) : Det P env (.arith op a b) (.nat z) (ca + cb + W + 1) := by
  subst hz; exact (Det.arith ha hb).mono (by omega)

theorem nclWt_nat_mono {x y : ℕ} (h : x ≤ y) : (Val.nat x).wt ≤ (Val.nat y).wt := by
  rw [wt_nat, wt_nat]; have := GI.Machine.len_mono h; omega

/-! ### The points `n, …, N - 1` -/

theorem nclEncPts_val {N : ℕ} (S : List (Fin N)) :
    encPts S = .list (S.map fun i => Val.nat i.val) := by
  simp only [encPts]
  congr 1
  induction S with
  | nil => rfl
  | cons a S ih => simp_all

theorem nclEncPts_eq {N : ℕ} (S : List (Fin N)) : encPts S = natList (S.map Fin.val) := by
  rw [nclEncPts_val, natList, List.map_map]; rfl

theorem nclWt_encPts_le {N : ℕ} (S : List (Fin N)) (hS : S.length ≤ N) :
    (encPts S).wt ≤ 5 * (N + 1) ^ 2 := by
  rw [nclEncPts_eq]
  exact wt_natList_le_sq (fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact i.2.le) (by simpa using hS)

theorem nclLength_deltaPts {n n' k : ℕ} : (nclDeltaPts (n' := n') n k).length ≤ n' := by
  simp [nclDeltaPts]

theorem nclEncPts_deltaPts_succ {n n' k : ℕ} (hk : k < n') :
    encPts (nclDeltaPts (n' := n') n (k + 1)) =
      .list (((nclDeltaPts (n' := n') n k).map fun i => Val.nat i.val) ++ [.nat (n + k)]) := by
  rw [nclEncPts_val, nclDeltaPts_succ hk, List.map_append]
  simp [nclInDelta_val]

/-- **The points.** On `[n, n + n']`, the value `encPts (nclDeltaPts n n')`. -/
theorem prePts_spec {P : Program} {b : ℕ} (h : P.HasAt b (prePtsFuns b)) (n n' : ℕ) :
    FunDet P b (.list [.nat n, .nat (n + n')]) (encPts (nclDeltaPts (n' := n') n n'))
      (loopModK * (n' + 1) * ((Val.list [.nat n, .nat (n + n')]).wt + n' +
        5 * (n + n' + 1) ^ 2 + 1)) := by
  set a := Val.list [.nat n, .nat (n + n')] with ha
  have hk : Det P [a] (.arith .sub (arg 1) (arg 0)) (.nat n') _ :=
    Det.arith' (Det.arg' (j := 1) (v := .nat (n + n')) rfl) (Det.arg' (j := 0) (v := .nat n) rfl)
      (by simp [BinOp.eval])
  have h0 : Det P [a] .nil (.list []) 5 := Det.nil
  have hka := wt_nat_le n
  have hkb := wt_nat_le (n + n')
  have wa := wt_list2_le (.nat n) (.nat (n + n'))
  have hna : (Val.nat (n + n')).wt < a.wt := wt_le_wt_list (by simp)
  have hn0 : (Val.nat n).wt < a.wt := wt_le_wt_list (by simp)
  have eA : a.wt = (Val.list [.nat n, .nat (n + n')]).wt := rfl
  have h2a := a.two_le_size
  have h2b := a.size_le_wt
  refine (loopBdd_spec h hk h0 (by omega)
    (M := 5 * (n + n' + 1) ^ 2) (Inv := fun i acc => acc = encPts (nclDeltaPts (n' := n') n i))
    (by beta_reduce; rw [nclDeltaPts_zero]; rfl)
    (fun i acc _ hacc => by rw [hacc]; exact nclWt_encPts_le _ (by
      have := nclLength_deltaPts (n := n) (n' := n') (k := i); omega))
    (D := fun _ => 0) fun i acc hi hacc => ?_).mono fun w c hw => ⟨?_, ?_⟩
  · subst hacc
    have e2 := nclEncPts_val (nclDeltaPts (n' := n') n i)
    rw [e2]
    set V : List Val := [a, .nat i, .list ((nclDeltaPts (n' := n') n i).map fun i => Val.nat i.val)]
    have d2 := Det.arg' (P := P) (vs := V) (rest := []) (j := 2)
      (v := .list ((nclDeltaPts (n' := n') n i).map fun i => Val.nat i.val)) rfl
    have d0 := Det.arg' (P := P) (vs := V) (rest := []) (j := 0) (v := a) rfl
    have d1 := Det.arg' (P := P) (vs := V) (rest := []) (j := 1) (v := .nat i) rfl
    have dn := Det.get' d0 (Det.nat 0) (show [Val.nat n, .nat (n + n')][0]? = some (.nat n) from rfl)
    have dS := Det.snoc d2 (nclDet_arith_le (op := BinOp.add) (z := n + i) dn d1 rfl
      (nclWt_nat_mono (show n + i ≤ n + n' by omega)))
    rw [← nclEncPts_deltaPts_succ hi] at dS
    refine dS.post fun c hc => ⟨rfl, ?_⟩
    have wV := wt_list3_le a (.nat i) (encPts (nclDeltaPts (n' := n') n i))
    rw [e2] at wV
    have eV : (Val.list V).wt = (Val.list [a, .nat i, .list ((nclDeltaPts (n' := n') n i).map
      fun i => Val.nat i.val)]).wt := rfl
    have wP := nclWt_encPts_le (nclDeltaPts (n' := n') n i) (by
      have := nclLength_deltaPts (n := n) (n' := n') (k := i); omega)
    have wP' := nclWt_encPts_le (nclDeltaPts (n' := n') n (i + 1)) (by
      have := nclLength_deltaPts (n := n) (n' := n') (k := i + 1); omega)
    have wi := wt_nat_le i
    rw [e2] at wP
    omega
  · exact hw.1
  · simpa using hw.2

/-! ### Selecting the transversal element of a point -/

theorem nclWt_encPair_le {N : ℕ} (p : Fin N × Perm (Fin N)) :
    (encPair ptKey p).wt ≤ 30 * (N + 1) ^ 2 := by
  have h1 := wt_list2_le (natList (ptKey p.1)) (encPerm p.2)
  have h2 : (natList (ptKey p.1)).wt ≤ 2 * (Val.nat p.1).wt + 5 := wt_list1_le _
  have h3 := wt_nat_le (p.1 : ℕ)
  have h4 := wt_encPerm_le p.2
  have h5 := p.1.2
  have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  simp only [encPair]
  omega

theorem nclWt_encPairs_le {N : ℕ} (L : List (Fin N × Perm (Fin N))) (hL : L.length ≤ N) :
    (Val.list (L.map (encPair ptKey))).wt ≤ 100 * (N + 1) ^ 3 := by
  have h1 := wt_list_le (L.map (encPair ptKey))
  have h2 : ((L.map (encPair ptKey)).map Val.wt).sum ≤ L.length * (30 * (N + 1) ^ 2) := by
    have := List.sum_le_card_nsmul ((L.map (encPair ptKey)).map Val.wt) (30 * (N + 1) ^ 2) (by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨p, -, rfl⟩ := hx
      exact nclWt_encPair_le p)
    simpa using this
  have h3 : L.length * (30 * (N + 1) ^ 2) ≤ (N + 1) * (30 * (N + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (N + 1) * (30 * (N + 1) ^ 2) = 30 * (N + 1) ^ 3 := by ring
  have : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  simp only [List.length_map] at h1
  omega

/-- The invariant of the selection: the transversal element of `β` among the first `i` pairs,
or `0` if there is none yet. -/
def NclSelInv {N : ℕ} (L : List (Fin N × Perm (Fin N))) (β : Fin N) (i : ℕ) (acc : Val) : Prop :=
  (∃ p ∈ L.take i, p.1 = β ∧ acc = encPerm p.2) ∨ (acc = .nat 0 ∧ ∀ p ∈ L.take i, p.1 ≠ β)

set_option maxHeartbeats 1000000 in
theorem preSel_spec {P : Program} {b j : ℕ} {h : PointwiseStab} (hP : PreAt P b j h) {N : ℕ}
    (L : List (Fin N × Perm (Fin N))) (β : Fin N) (hβ : ∃ p ∈ L, p.1 = β) (hL : L.length ≤ N) :
    FunAll P (b + 35) (.list [.nat β, .list (L.map (encPair ptKey)), .nat 0])
      (fun w c => (∃ p ∈ L, p.1 = β ∧ w = encPerm p.2) ∧ c ≤ 10 ^ 6 * (N + 1) ^ 4) := by
  set xs := L.map (encPair ptKey) with hxs
  have hlen : xs.length = L.length := by simp [hxs]
  have hf := foldl_spec hP.fold (c := .nat β) (xs := xs) (acc0 := .nat 0)
    (Inv := NclSelInv L β) (M := 4 * (N + 1) ^ 2) (B := fun _ => 2000 * (N + 1) ^ 2)
    (Or.inr ⟨rfl, by simp⟩)
    (fun i acc _ hacc => by
      rcases hacc with ⟨p, -, -, rfl⟩ | ⟨rfl, -⟩
      · exact wt_encPerm_le p.2
      · have := wt_nat_le 0
        have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega)
    (fun i acc hi hacc => by
      have hi' : i < L.length := by omega
      have hx : xs[i] = .list [.list [.nat (L[i].1 : ℕ)], encPerm L[i].2] := by
        simp only [hxs, List.getElem_map]; rfl
      rw [hx]
      set V : List Val := [.nat β, acc, .list [.list [.nat (L[i].1 : ℕ)], encPerm L[i].2]]
      have d2 := Det.arg' (P := P) (vs := V) (rest := []) (j := 2)
        (v := .list [.list [.nat (L[i].1 : ℕ)], encPerm L[i].2]) rfl
      have d0 := Det.arg' (P := P) (vs := V) (rest := []) (j := 0) (v := .nat β) rfl
      have d1 := Det.arg' (P := P) (vs := V) (rest := []) (j := 1) (v := acc) rfl
      have dk := Det.get' (Det.get' d2 (Det.nat 0) rfl) (Det.nat 0)
        (show [Val.nat (L[i].1 : ℕ)][0]? = some (.nat (L[i].1 : ℕ)) from rfl)
      have dp := Det.get' d2 (Det.nat 1) (show [Val.list [.nat (L[i].1 : ℕ)], encPerm L[i].2][1]? =
        some (encPerm L[i].2) from rfl)
      have dt := nclDet_arith_le (op := BinOp.eq) (W := 3)
        (z := if (L[i].1 : ℕ) = β then 1 else 0) dk d0 rfl
        (by split_ifs <;> simp [wt_nat, GI.Machine.len_zero])
      have dI := Det.ite' dt dp d1
      refine FunAll.mono (FunDet.intro hP.sel dI) fun w c hw => ⟨?_, ?_⟩
      · rw [hw.1]
        have ht : L.take (i + 1) = L.take i ++ [L[i]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi']; rfl
        by_cases hb : (L[i].1 : ℕ) = β
        · rw [if_pos hb, if_neg one_ne_zero]
          have hm : L[i] ∈ L.take (i + 1) := by
            rw [ht]; exact List.mem_append_right _ (List.mem_singleton_self _)
          exact Or.inl ⟨L[i], hm, Fin.ext hb, rfl⟩
        · rw [if_neg hb, if_pos rfl]
          rcases hacc with ⟨p, hp, hpb, rfl⟩ | ⟨rfl, hn⟩
          · exact Or.inl ⟨p, by rw [ht]; exact List.mem_append_left _ hp, hpb, rfl⟩
          · refine Or.inr ⟨rfl, fun p hp => ?_⟩
            rw [ht, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · exact hn p hp
            · exact fun e => hb (congrArg Fin.val e)
      · have hc := hw.2
        have wV := wt_list3_le (.nat β) acc (.list [.list [.nat (L[i].1 : ℕ)], encPerm L[i].2])
        have eV : (Val.list V).wt = (Val.list [.nat β, acc,
          .list [.list [.nat (L[i].1 : ℕ)], encPerm L[i].2]]).wt := rfl
        have wA : acc.wt ≤ 4 * (N + 1) ^ 2 := by
          rcases hacc with ⟨p, -, -, rfl⟩ | ⟨rfl, -⟩
          · exact wt_encPerm_le p.2
          · have := wt_nat_le 0
            have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
            omega
        have wP := nclWt_encPair_le L[i]
        have eP : (encPair ptKey L[i]).wt =
          (Val.list [.list [.nat (L[i].1 : ℕ)], encPerm L[i].2]).wt := rfl
        have wpp := wt_encPerm_le L[i].2
        have wb := wt_nat_le (β : ℕ)
        have hb := β.2
        have wk : (Val.list [Val.nat (L[i].1 : ℕ)]).wt ≤ (Val.list [.list [.nat (L[i].1 : ℕ)],
            encPerm L[i].2]).wt := le_of_lt (wt_le_wt_list (List.mem_cons_self ..))
        have wk2 := wt_nat_le (L[i].1 : ℕ)
        have hk2 := (L[i].1).2
        have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
        beta_reduce
        omega)
  refine FunAll.mono hf fun w c hw => ⟨?_, ?_⟩
  · rcases hw.1 with ⟨p, hp, hpb, e⟩ | ⟨-, hn⟩
    · rw [hlen, List.take_length] at hp; exact ⟨p, hp, hpb, e⟩
    · rw [hlen, List.take_length] at hn
      obtain ⟨p, hp, hpb⟩ := hβ
      exact absurd hpb (hn p hp)
  · have hc := hw.2
    have hs : (∑ i ∈ Finset.range xs.length, (fun _ => 2000 * (N + 1) ^ 2) i) =
        xs.length * (2000 * (N + 1) ^ 2) := by simp
    rw [hs] at hc
    have w3 := wt_list3_le (.nat β) (.list xs) (.nat 0)
    have wX : (Val.list xs).wt ≤ 100 * (N + 1) ^ 3 := nclWt_encPairs_le L hL
    have wb := wt_nat_le (β : ℕ)
    have w0 := wt_nat_le 0
    have hb := β.2
    have p23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have p1 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have k1 : xs.length * (2000 * (N + 1) ^ 2) ≤ (N + 1) * (2000 * (N + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : loopModK * (xs.length + 1) * ((Val.list [.nat β, .list xs, .nat 0]).wt +
        xs.length + 4 * (N + 1) ^ 2 + 1) ≤ (1000 * (N + 1)) * (400 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (by unfold loopModK; omega) (by omega)
    have e1 : (N + 1) * (2000 * (N + 1) ^ 2) = 2000 * (N + 1) ^ 3 := by ring
    have e2 : (1000 * (N + 1)) * (400 * (N + 1) ^ 3) = 400000 * (N + 1) ^ 4 := by ring
    have p34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

end GI.Impl
