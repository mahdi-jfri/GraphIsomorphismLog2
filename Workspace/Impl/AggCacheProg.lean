module

public import Workspace.Impl.AggCache

@[expose] public section

/-!
# The cache lookup, in `GI.Lang`

The cache of coset representatives (`Workspace/Impl/AggCache.lean`) is a list of entries; each
entry holds the graph forms of the lifts of `A` and `N` and the representatives chosen for them.
Before the program computes representatives for a pair `(A, N)`, it looks for an entry with the
same pair. Two pairs are the same exactly when each generating list lies in the group of the
other (`eq_iff_le_gens`), which is four subgroup tests by **Membership** (`le_spec`).

The program keeps the graph forms already encoded as group values on `k + q` points
(`ckEntV`): an entry is `[⟨A-pairs⟩, ⟨N-pairs⟩, representatives]`, the key of a pair is
`[⟨A-pairs⟩, ⟨N-pairs⟩]` (`ckKeyV`).

* `ckTest_spec`: on `[key, entry]` the test returns `1` exactly when the entry matches the key
  (`KeyMatch`), with four `le_spec` calls.
* `ckFind_spec`: on `[key, entries]` the module returns the index of the first matching entry,
  or the number of entries if none matches (`find_spec`).
* `ckFind_hit`, `ckFind_miss`: what the index says about the cache.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership)

variable {k q : ℕ}

/-! ### Values -/

/-- The value of a cache entry: the two graph forms as group values on `k + q` points, and the
representatives on positions. -/
def ckEntV (c : CacheEntry k q) : Val :=
  .list [encGroup (c.1.map encPair), encGroup (c.2.1.map encPair), .list (c.2.2.map encPerm)]

/-- The key of a pair `(A, N)` from graph forms `ps`, `ns` of their lifts. -/
def ckKeyV (ps ns : List (Perm (Fin k) × Perm (Fin q))) : Val :=
  .list [encGroup (ps.map encPair), encGroup (ns.map encPair)]

/-- The four subgroup tests of an entry against a key (the same as `KeyMatch`). -/
def ckMatch (c : CacheEntry k q) (ps ns : List (Perm (Fin k) × Perm (Fin q))) : Prop :=
  (gens (ps.map encPair) ≤ gens (c.1.map encPair) ∧ gens (c.1.map encPair) ≤ gens (ps.map encPair)) ∧
    (gens (ns.map encPair) ≤ gens (c.2.1.map encPair) ∧
      gens (c.2.1.map encPair) ≤ gens (ns.map encPair))

theorem keyMatch_iff_ckMatch {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
    (c : CacheEntry k L.q) (ps ns : List (Perm (Fin k) × Perm (Fin L.q))) :
    KeyMatch c ps ns ↔ ckMatch c ps ns := Iff.rfl

open Classical in
/-- The test as a Boolean. -/
noncomputable def ckTest (ps ns : List (Perm (Fin k) × Perm (Fin q))) (c : CacheEntry k q) :
    Bool := by
  classical exact decide (ckMatch c ps ns)

theorem ckTest_eq_true {ps ns : List (Perm (Fin k) × Perm (Fin q))} {c : CacheEntry k q} :
    ckTest ps ns c = true ↔ ckMatch c ps ns := by
  unfold ckTest; exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-! ### The test of one entry -/

/-- On `[key, entry]`: the four subgroup tests, with the subgroup test at `le`. -/
def ckTestF (le : ℕ) : Expr :=
  .ite (.call le (mk2 (.get (arg 1) (.nat 0)) (.get (arg 0) (.nat 0))))
    (.ite (.call le (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0))))
      (.ite (.call le (mk2 (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 1))))
        (.call le (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))))
        (.nat 0))
      (.nat 0))
    (.nat 0)

/-- The cost of one test on an argument of weight at most `W`. -/
noncomputable def ckTestCost (h : Membership) (W : ℕ) : ℕ :=
  4 * ((4 * W + 20) * (membershipPrim h).boundSize (4 * W + 20) + 20000 * (4 * W + 20) ^ 3) +
    200 * W + 400

open Classical in
/-- One subgroup test inside the test of an entry: on `[gv, encGroup hs]` read from the
argument, with `gv = encGroup gs`. -/
theorem ckLe_det (h : Membership) {P : Program} {le jm : ℕ} (hb : P.HasAt le (leFuns le jm))
    (hj : P.prims[jm]? = some (membershipPrim h)) {n : ℕ} {env : List Val} {ea eb : Expr}
    {gs hs : List (Perm (Fin n))} {ca cb W : ℕ} (ha : Det P env ea (encGroup gs) ca)
    (hb' : Det P env eb (encGroup hs) cb) (hga : (encGroup gs).wt ≤ W)
    (hgb : (encGroup hs).wt ≤ W) :
    Det P env (.call le (mk2 ea eb)) (boolVal (decide (gens hs ≤ gens gs)))
      (ca + cb + (4 * W + 20) * (membershipPrim h).boundSize (4 * W + 20) +
        20000 * (4 * W + 20) ^ 3 + 8 * W + 40) := by
  have hl := le_spec h hb hj (G := gens gs) ⟨gs, rfl, rfl⟩ hs
  set T := (Val.list [encGroup gs, encGroup hs]).wt with hT
  have hTW : T ≤ 2 * (W + W) + 6 := by
    have := wt_list2_le (encGroup gs) (encGroup hs); omega
  -- the membership bound
  have h1 : (encPerm (1 : Perm (Fin n))).wt < (encGroup gs).wt := by
    show (encPerm (1 : Perm (Fin n))).wt < (GI.Cited.encPerms (1 :: gs)).wt
    unfold GI.Cited.encPerms
    have : (Val.list ((1 :: gs).map encPerm)).wt < (Val.list [.nat n,
      .list ((1 :: gs).map encPerm)]).wt := wt_le_wt_list (by simp)
    have h2 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
      wt_le_wt_list (by simp)
    omega
  have hsz : (Val.list [encGroup gs, encPerm (1 : Perm (Fin n))]).size ≤ 4 * W + 20 := by
    have := (Val.list [encGroup gs, encPerm (1 : Perm (Fin n))]).size_le_wt
    have := wt_list2_le (encGroup gs) (encPerm (1 : Perm (Fin n)))
    omega
  have hmb := (membershipPrim h).bound_le hsz
  have hc1 : T * (membershipPrim h).bound (.list [encGroup gs, encPerm (1 : Perm (Fin n))]) ≤
      (4 * W + 20) * (membershipPrim h).boundSize (4 * W + 20) :=
    Nat.mul_le_mul (by omega) hmb
  have hc2 : 20000 * T ^ 3 ≤ 20000 * (4 * W + 20) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  refine (Det.call (Det.mk2 ha hb') hl).mono ?_
  have := wt_boolVal_le (decide (gens hs ≤ gens gs))
  rw [← hT]
  omega

theorem ckIte (a b : Bool) : (if a.toNat = 0 then Val.nat 0 else boolVal b) = boolVal (a && b) := by
  cases a <;> simp

open Classical in
/-- **The test of one entry.** -/
theorem ckTest_spec (h : Membership) {P : Program} {f le jm : ℕ}
    (hf : P.funs[f]? = some (ckTestF le)) (hb : P.HasAt le (leFuns le jm))
    (hj : P.prims[jm]? = some (membershipPrim h)) (ps ns : List (Perm (Fin k) × Perm (Fin q)))
    (c : CacheEntry k q) :
    FunDet P f (.list [ckKeyV ps ns, ckEntV c]) (boolVal (ckTest ps ns c))
      (ckTestCost h (Val.list [ckKeyV ps ns, ckEntV c]).wt) := by
  set W := (Val.list [ckKeyV ps ns, ckEntV c]).wt with hW
  set vs : List Val := [ckKeyV ps ns, ckEntV c]
  have gk := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := ckKeyV ps ns) rfl
  have ge := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := ckEntV c) rfl
  have hkW : (ckKeyV ps ns).wt < W := wt_le_wt_list (by simp)
  have heW : (ckEntV c).wt < W := wt_le_wt_list (by simp)
  have wK0 : (encGroup (ps.map encPair)).wt < (ckKeyV ps ns).wt := wt_le_wt_list (by simp)
  have wK1 : (encGroup (ns.map encPair)).wt < (ckKeyV ps ns).wt := wt_le_wt_list (by simp)
  have wE0 : (encGroup (c.1.map encPair)).wt < (ckEntV c).wt := wt_le_wt_list (by simp)
  have wE1 : (encGroup (c.2.1.map encPair)).wt < (ckEntV c).wt := wt_le_wt_list (by simp)
  have dK0 := Det.get' gk (Det.nat 0) (v := encGroup (ps.map encPair)) rfl
  have dK1 := Det.get' gk (Det.nat 1) (v := encGroup (ns.map encPair)) rfl
  have dE0 := Det.get' ge (Det.nat 0) (v := encGroup (c.1.map encPair)) rfl
  have dE1 := Det.get' ge (Det.nat 1) (v := encGroup (c.2.1.map encPair)) rfl
  have t1 := ckLe_det h hb hj (W := W) dE0 dK0 (by omega) (by omega)
  have t2 := ckLe_det h hb hj (W := W) dK0 dE0 (by omega) (by omega)
  have t3 := ckLe_det h hb hj (W := W) dE1 dK1 (by omega) (by omega)
  have t4 := ckLe_det h hb hj (W := W) dK1 dE1 (by omega) (by omega)
  have i3 := Det.ite' t3 t4 (Det.nat (P := P) (env := [Val.list vs]) 0)
  rw [ckIte] at i3
  have i2 := Det.ite' t2 i3 (Det.nat (P := P) (env := [Val.list vs]) 0)
  rw [ckIte] at i2
  have i1 := Det.ite' t1 i2 (Det.nat (P := P) (env := [Val.list vs]) 0)
  rw [ckIte] at i1
  have hv : (decide (gens (ps.map encPair) ≤ gens (c.1.map encPair)) &&
      (decide (gens (c.1.map encPair) ≤ gens (ps.map encPair)) &&
      (decide (gens (ns.map encPair) ≤ gens (c.2.1.map encPair)) &&
      decide (gens (c.2.1.map encPair) ≤ gens (ns.map encPair))))) = ckTest ps ns c := by
    unfold ckTest ckMatch
    by_cases a1 : gens (ps.map encPair) ≤ gens (c.1.map encPair) <;>
    by_cases a2 : gens (c.1.map encPair) ≤ gens (ps.map encPair) <;>
    by_cases a3 : gens (ns.map encPair) ≤ gens (c.2.1.map encPair) <;>
    by_cases a4 : gens (c.2.1.map encPair) ≤ gens (ns.map encPair) <;>
    simp [a1, a2, a3, a4]
  rw [hv] at i1
  refine FunDet.intro hf (i1.mono ?_)
  have b1 := wt_boolVal_le (ckTest ps ns c)
  have b2 := wt_nat_le 0
  have hvs : (Val.list vs).wt = W := rfl
  unfold ckTestCost
  clear_value W vs
  generalize (4 * W + 20) * (membershipPrim h).boundSize (4 * W + 20) = X
  generalize 20000 * (4 * W + 20) ^ 3 = Y
  have e1 := wt_boolVal_le (decide (gens (c.2.1.map encPair) ≤ gens (ns.map encPair)))
  have e2 := wt_boolVal_le (decide (gens (ns.map encPair) ≤ gens (c.2.1.map encPair)) &&
      decide (gens (c.2.1.map encPair) ≤ gens (ns.map encPair)))
  have e3 := wt_boolVal_le (decide (gens (c.1.map encPair) ≤ gens (ps.map encPair)) &&
      (decide (gens (ns.map encPair) ≤ gens (c.2.1.map encPair)) &&
      decide (gens (c.2.1.map encPair) ≤ gens (ns.map encPair))))
  omega

/-! ### The lookup -/

theorem ckTestCost_mono (h : Membership) {W W' : ℕ} (hW : W ≤ W') :
    ckTestCost h W ≤ ckTestCost h W' := by
  unfold ckTestCost
  have h1 : (membershipPrim h).boundSize (4 * W + 20) ≤ (membershipPrim h).boundSize (4 * W' + 20) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h2 := Nat.mul_le_mul (show 4 * W + 20 ≤ 4 * W' + 20 by omega) h1
  have h3 : (4 * W + 20) ^ 3 ≤ (4 * W' + 20) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  omega

/-- The lookup module at base `b` (nine functions), with membership at primitive `jm`. -/
def ckFindFuns (b jm : ℕ) : List Expr := findFuns b (b + 3) ++ [ckTestF (b + 4)] ++ leFuns (b + 4) jm

/-- The cost of the lookup on an argument of weight at most `M`. -/
noncomputable def ckFindCost (h : Membership) (M : ℕ) : ℕ :=
  M * ckTestCost h (4 * M + 6) + loopModK * (M + 1) * (3 * M + 3)

theorem ckEntV_injective : Function.Injective (ckEntV (k := k) (q := q)) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [ckEntV, Val.list.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have i1 := (List.map_injective_iff.2 encPair_injective) (encGroup_injective h1)
  have i2 := (List.map_injective_iff.2 encPair_injective) (encGroup_injective h2)
  have i3 := (List.map_injective_iff.2 encPerm_injective) h3
  simp_all

open Classical in
/-- The test on values. -/
noncomputable def ckTestV (ps ns : List (Perm (Fin k) × Perm (Fin q))) (v : Val) : Bool :=
  decide (∃ ent, ckEntV ent = v ∧ ckMatch ent ps ns)

theorem ckTestV_ent (ps ns : List (Perm (Fin k) × Perm (Fin q))) (c : CacheEntry k q) :
    ckTestV ps ns (ckEntV c) = ckTest ps ns c := by
  rw [Bool.eq_iff_iff, ckTest_eq_true]
  unfold ckTestV
  rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
  constructor
  · rintro ⟨ent, he, hm⟩
    rwa [← ckEntV_injective he]
  · intro hm; exact ⟨c, rfl, hm⟩

/-- **The cache lookup**: the index of the first entry that matches the key. -/
theorem ckFind_spec (h : Membership) {P : Program} {b jm : ℕ} (hb : P.HasAt b (ckFindFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim h)) (ps ns : List (Perm (Fin k) × Perm (Fin q)))
    (c : List (CacheEntry k q)) {M : ℕ}
    (hM : (Val.list [ckKeyV ps ns, .list (c.map ckEntV)]).wt ≤ M) :
    FunDet P b (.list [ckKeyV ps ns, .list (c.map ckEntV)]) (.nat (c.findIdx (ckTest ps ns)))
      (ckFindCost h M) := by
  have hfind : P.HasAt b (findFuns b (b + 3)) := hb.left.left
  have htest : P.funs[b + 3]? = some (ckTestF (b + 4)) := by
    simpa [findFuns, loopFuns] using hb.left.right.single
  have hle : P.HasAt (b + 4) (leFuns (b + 4) jm) := by simpa [findFuns, loopFuns] using hb.right
  have hkM : (ckKeyV ps ns).wt < M := lt_of_lt_of_le (wt_le_wt_list (by simp)) hM
  have hcM : (Val.list (c.map ckEntV)).wt < M := lt_of_lt_of_le (wt_le_wt_list (by simp)) hM
  have hT : ∀ x ∈ c.map ckEntV, FunDet P (b + 3) (.list [ckKeyV ps ns, x])
      (boolVal (ckTestV ps ns x)) (ckTestCost h (4 * M + 6)) := by
    intro x hx
    obtain ⟨ent, -, rfl⟩ := List.mem_map.1 hx
    rw [ckTestV_ent]
    refine (ckTest_spec h htest hle hj ps ns ent).mono ?_
    have h1 := wt_list2_le (ckKeyV ps ns) (ckEntV ent)
    have h2 : (ckEntV ent).wt < (Val.list (c.map ckEntV)).wt := wt_le_wt_list hx
    exact ckTestCost_mono h (by omega)
  refine (find_spec hfind hT).mono fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, List.findIdx_map]
    congr 2
    funext ent
    exact ckTestV_ent ps ns ent
  · have hc := hw.2
    rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
    have hl : c.length < M := by
      have := length_lt_wt_list (c.map ckEntV); simp only [List.length_map] at this; omega
    have a1 : c.length * ckTestCost h (4 * M + 6) ≤ M * ckTestCost h (4 * M + 6) :=
      Nat.mul_le_mul_right _ hl.le
    have a2 : loopModK * (c.length + 1) *
        ((Val.list [ckKeyV ps ns, .list (c.map ckEntV)]).wt + 2 * c.length + 3) ≤
        loopModK * (M + 1) * (3 * M + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    unfold ckFindCost
    omega

/-- **A hit**: the found entry matches. -/
theorem ckFind_hit {ps ns : List (Perm (Fin k) × Perm (Fin q))} {c : List (CacheEntry k q)}
    (hi : c.findIdx (ckTest ps ns) < c.length) :
    ckMatch (GetElem.getElem c (c.findIdx (ckTest ps ns)) hi) ps ns :=
  ckTest_eq_true.1 (List.findIdx_getElem (w := hi))

/-- **A miss**: no entry matches. -/
theorem ckFind_miss {ps ns : List (Perm (Fin k) × Perm (Fin q))} {c : List (CacheEntry k q)}
    (hi : ¬ c.findIdx (ckTest ps ns) < c.length) : ∀ ent ∈ c, ¬ ckMatch ent ps ns := by
  intro ent hent hm
  have := List.findIdx_eq_length.1 (le_antisymm List.findIdx_le_length (not_lt.1 hi)) ent hent
  rw [ckTest_eq_true.2 hm] at this
  exact Bool.noConfusion this

end GI.Impl
