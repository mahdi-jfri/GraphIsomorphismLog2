module

public import Workspace.Impl.GenNormIncProg
public import Workspace.Impl.PolyBd

@[expose] public section

/-!
# Recovering the Cameron point permutations by finite loops

For each possible image point, the inner loop tests every block. The middle loop keeps the
points passing that test. Incidence separation makes its result a singleton. The outer loop
reads that singleton for every point, giving the point permutation used by the model.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples)

/-- A common size bound for all inputs and indices of point recovery. -/
def normRecoverSize {n m k : ℕ} (e : Fin n ≃ (Fin 1 → Product.KSet m k))
    (x : Perm (Fin n)) : ℕ :=
  (encKSetTuples e).wt + (encPerm x).wt + (encPerm (1 : Perm (Fin n))).wt +
    (encPerm (1 : Perm (Fin m))).wt + m + n + 20

/-- Reading one field of the context of a map or search entry. -/
private theorem normCtxGet {P : Program} {ctxs : List Val} {entry : Val} {j : ℕ} {v : Val}
    (hj : ctxs[j]? = some v) {rest : List Val} :
    Det P (.list [.list ctxs, entry] :: rest) (.get (arg 0) (.nat j)) v
      (5 * (Val.list [.list ctxs, entry]).wt + j + 20) := by
  have hc : (Val.list ctxs).wt < (Val.list [.list ctxs, entry]).wt := wt_le_wt_list (by simp)
  have hv : v.wt < (Val.list ctxs).wt := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact wt_getElem_lt _ _ h
  exact (Det.get' (Det.arg' (j := 0) rfl) (Det.nat j) hj).mono (by omega)

/-- The test of one block, as a predicate on values for the `all` library. -/
def normIncQ {n m k : ℕ} (e : Fin n ≃ (Fin 1 → Product.KSet m k))
    (x : Perm (Fin n)) (i j : Fin m) : Val → Bool
  | .nat b => if hb : b < n then decide (i ∈ (e ⟨b, hb⟩ 0).1 ↔ j ∈ (e (x ⟨b, hb⟩) 0).1)
      else false
  | .list _ => false

/-- The candidate test. -/
def normCandidateB {n m k : ℕ} (e : Fin n ≃ (Fin 1 → Product.KSet m k))
    (x : Perm (Fin n)) (i j : Fin m) : Bool :=
  (List.finRange n).all fun b => decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1)

/-- On `[[E,x,blockIds,i],j]`, test every block for the proposed point image `j`. -/
def normCandidateF (all : ℕ) : Expr :=
  .call all (mk2 (Expr.mkList [.get (arg 0) (.nat 0), .get (arg 0) (.nat 1),
    .get (arg 0) (.nat 3), arg 1]) (.get (arg 0) (.nat 2)))

set_option maxHeartbeats 2000000 in
/-- The inner loop tests exactly the candidate predicate, at polynomial cost. -/
theorem normCandidate_spec {P : Program} {f all test mem n m k : ℕ}
    (hf : P.funs[f]? = some (normCandidateF all))
    (hall : P.HasAt all (allFuns all test))
    (htest : P.funs[test]? = some (normIncTestF mem)) (hmem : P.HasAt mem (normMemFuns mem))
    (e : Fin n ≃ (Fin 1 → Product.KSet m k)) (x : Perm (Fin n)) (i j : Fin m)
    {Z : ℕ} (hZ : normRecoverSize e x ≤ Z) :
    FunDet P f (.list [.list [encKSetTuples e, encPerm x, encPerm (1 : Perm (Fin n)), .nat i],
      .nat j]) (boolVal (normCandidateB e x i j)) (10 ^ 14 * Z ^ 4) := by
  let E := encKSetTuples e
  let xp := encPerm x
  let ids := encPerm (1 : Perm (Fin n))
  let ctx := Val.list [E, xp, ids, .nat i]
  let a := Val.list [ctx, .nat j]
  let inner := Val.list [E, xp, .nat i, .nat j]
  have hZ' : E.wt + xp.wt + ids.wt + (encPerm (1 : Perm (Fin m))).wt + m + n + 20 ≤ Z := hZ
  have hZ20 : 20 ≤ Z := by omega
  have wi := wt_nat_le (i : ℕ)
  have wj := wt_nat_le (j : ℕ)
  have hi := i.2
  have hj := j.2
  have wc := wt_list4_le E xp ids (.nat i)
  have wa := wt_list2_le ctx (.nat j)
  have winner := wt_list4_le E xp (.nat i) (.nat j)
  have wctx : ctx.wt ≤ 3 * Z := by dsimp only [ctx]; omega
  have waa : a.wt ≤ 9 * Z := by change (Val.list [ctx, .nat j]).wt ≤ 9 * Z; omega
  have win : inner.wt ≤ 5 * Z := by dsimp only [inner]; omega
  have warg := wt_list2_le inner ids
  have wall : (Val.list [inner, ids]).wt ≤ 13 * Z := by omega
  have ht : ∀ b ∈ (List.finRange n).map (fun b : Fin n => Val.nat b),
      FunDet P test (.list [inner, b]) (boolVal (normIncQ e x i j b)) (10 ^ 11 * Z ^ 3) := by
    intro b hb
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hb
    have h := normIncTest_spec htest hmem e x i j b
    change FunDet P test _ _ _ at h
    have heq : normIncQ e x i j (.nat b) =
        decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1) := by
      simp only [normIncQ, dif_pos b.2]
    rw [heq]
    refine h.mono ?_
    have wb := wt_nat_le (b : ℕ)
    have hb := b.2
    have wint := wt_list2_le inner (.nat b)
    have hh : (Val.list [inner, .nat b]).wt + m + 1 ≤ 15 * Z := by omega
    have hp := Nat.pow_le_pow_left hh 3
    have he : (15 * Z) ^ 3 = 3375 * Z ^ 3 := by ring
    change 10000000 * ((Val.list [inner, .nat b]).wt + m + 1) ^ 3 ≤ _
    rw [he] at hp
    omega
  have ha := all_spec hall ht
  have heq : ((List.finRange n).map (fun b : Fin n => Val.nat b)).all (normIncQ e x i j) =
      normCandidateB e x i j := by
    simp only [List.all_map, normCandidateB]
    congr 1
    funext b
    simp only [Function.comp_apply, normIncQ, dif_pos b.2]
  rw [heq] at ha
  have hs : (((List.finRange n).map (fun b : Fin n => Val.nat b)).map
      (fun _ => 10 ^ 11 * Z ^ 3)).sum = n * (10 ^ 11 * Z ^ 3) := by
    simp only [List.map_map, Function.comp_def]
    simp [List.map_const', List.sum_replicate, smul_eq_mul]
  have hsub : FunDet P all (.list [inner, ids]) (boolVal (normCandidateB e x i j))
      (10 ^ 12 * Z ^ 4) := by
    refine ha.mono fun w cost hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hs] at hc
    simp only [List.length_map, List.length_finRange] at hc
    have hid : Val.list ((List.finRange n).map fun b : Fin n => Val.nat b) = ids := rfl
    rw [hid] at hc
    have h1 : n * (10 ^ 11 * Z ^ 3) ≤ 10 ^ 11 * Z ^ 4 := by
      calc n * (10 ^ 11 * Z ^ 3) ≤ Z * (10 ^ 11 * Z ^ 3) := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    have h2 : loopModK * (n + 1) * ((Val.list [inner, ids]).wt + n + 4) ≤ 30000 * Z ^ 2 := by
      calc _ ≤ 1000 * (2 * Z) * (15 * Z) := by
            apply Nat.mul_le_mul
            · simp only [loopModK]; omega
            · omega
        _ = _ := by ring
    have h24 : Z ^ 2 ≤ Z ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have dE : Det P [a] (.get (arg 0) (.nat 0)) E (5 * a.wt + 20) := normCtxGet rfl
  have dx : Det P [a] (.get (arg 0) (.nat 1)) xp (5 * a.wt + 21) := normCtxGet rfl
  have di : Det P [a] (.get (arg 0) (.nat 3)) (.nat i) (5 * a.wt + 23) := normCtxGet rfl
  have dj : Det P [a] (arg 1) (.nat j) (2 * a.wt + 6) := Det.arg' (j := 1) rfl
  have dids : Det P [a] (.get (arg 0) (.nat 2)) ids (5 * a.wt + 22) := normCtxGet rfl
  have dl := Det.mkList (P := P) (env := [a]) (c := 5 * a.wt + 30)
    [(.get (arg 0) (.nat 0), E), (.get (arg 0) (.nat 1), xp),
      (.get (arg 0) (.nat 3), .nat i), (arg 1, .nat j)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact dE.mono (by omega)
      · exact dx.mono (by omega)
      · exact di.mono (by omega)
      · exact dj.mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dl
  refine FunDet.intro hf ((Det.call (Det.mk2 dl dids) hsub).mono ?_)
  have wall' : (Val.list [Val.list [E, xp, .nat i, .nat j], ids]).wt ≤ 13 * Z := wall
  have wb := wt_boolVal_le (normCandidateB e x i j)
  have h14 : Z ≤ Z ^ 4 := Nat.le_self_pow (by norm_num) _
  change _ ≤ 10 ^ 14 * Z ^ 4
  omega

/-- The candidate test as a predicate on a search entry. -/
def normCandidateQ {n m k : ℕ} (e : Fin n ≃ (Fin 1 → Product.KSet m k))
    (x : Perm (Fin n)) (i : Fin m) : Val → Bool
  | .nat j => if hj : j < m then normCandidateB e x i ⟨j, hj⟩ else false
  | .list _ => false

/-- On `[[E,x,blockIds,pointIds],i]`, read the unique candidate for point `i`. -/
def normPointF (filter : ℕ) : Expr :=
  .letE (.call filter (mk2 (Expr.mkList [.get (arg 0) (.nat 0), .get (arg 0) (.nat 1),
    .get (arg 0) (.nat 2), arg 1]) (.get (arg 0) (.nat 3))))
    (.get (.var 1) (.nat 0))

set_option maxHeartbeats 2000000 in
/-- Filtering candidate images and reading its singleton computes the model's point action. -/
theorem normPoint_spec {P : Program} {f filter cand all test mem m k : ℕ}
    (hf : P.funs[f]? = some (normPointF filter))
    (hfilter : P.HasAt filter (filterFuns filter cand))
    (hcand : P.funs[cand]? = some (normCandidateF all))
    (hall : P.HasAt all (allFuns all test))
    (htest : P.funs[test]? = some (normIncTestF mem)) (hmem : P.HasAt mem (normMemFuns mem))
    {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (x : Q.ρ.range) (i : Fin m) {Z : ℕ} (hZ : normRecoverSize e x.1 ≤ Z) :
    FunDet P f (.list [.list [encKSetTuples e, encPerm x.1,
      encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))], .nat i])
      (.nat (Q.permHom e hS x i)) (10 ^ 16 * Z ^ 5) := by
  let E := encKSetTuples e
  let xp := encPerm x.1
  let ids := encPerm (1 : Perm (Fin Q.d))
  let pts := encPerm (1 : Perm (Fin m))
  let ctx := Val.list [E, xp, ids, pts]
  let a := Val.list [ctx, .nat i]
  let inner := Val.list [E, xp, ids, .nat i]
  have hZ' : E.wt + xp.wt + ids.wt + pts.wt + m + Q.d + 20 ≤ Z := hZ
  have hZ20 : 20 ≤ Z := by omega
  have wi := wt_nat_le (i : ℕ)
  have hi := i.2
  have wc := wt_list4_le E xp ids pts
  have wa := wt_list2_le ctx (.nat i)
  have winner := wt_list4_le E xp ids (.nat i)
  have wctx : ctx.wt ≤ 3 * Z := by dsimp only [ctx]; omega
  have waa : a.wt ≤ 9 * Z := by change (Val.list [ctx, .nat i]).wt ≤ 9 * Z; omega
  have win : inner.wt ≤ 3 * Z := by dsimp only [inner]; omega
  have warg := wt_list2_le inner pts
  have wargZ : (Val.list [inner, pts]).wt ≤ 9 * Z := by omega
  have ht : ∀ j ∈ (List.finRange m).map (fun j : Fin m => Val.nat j),
      FunDet P cand (.list [inner, j]) (boolVal (normCandidateQ e x.1 i j))
        (10 ^ 14 * Z ^ 4) := by
    intro j hj
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hj
    have h := normCandidate_spec hcand hall htest hmem e x.1 i j hZ
    simpa only [normCandidateQ, dif_pos j.2] using h
  have hs := filter_spec hfilter ht
  have heq : ((List.finRange m).map (fun j : Fin m => Val.nat j)).filter
      (normCandidateQ e x.1 i) = [.nat (Q.permHom e hS x i)] := by
    have h := congrArg (List.map fun j : Fin m => Val.nat j)
      (normPointCandidates_eq Q e (Q.permOf_spec e hS x) i)
    change _ = [Val.nat (Q.permHom e hS x i)] at h
    rw [List.filter_map]
    convert h using 2
    apply List.filter_congr
    intro j _
    simp only [Function.comp_apply, normCandidateQ, dif_pos j.2,
      normCandidateB]
  rw [heq] at hs
  have hsum : (((List.finRange m).map (fun j : Fin m => Val.nat j)).map
      (fun _ => 10 ^ 14 * Z ^ 4)).sum = m * (10 ^ 14 * Z ^ 4) := by
    simp only [List.map_map, Function.comp_def]
    simp [List.map_const', List.sum_replicate, smul_eq_mul]
  have hs' : FunDet P filter (.list [inner, pts]) (.list [.nat (Q.permHom e hS x i)])
      (10 ^ 15 * Z ^ 5) := by
    refine hs.mono fun w cost hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hsum, hw.1] at hc
    simp only [List.length_map, List.length_finRange] at hc
    have hid : Val.list ((List.finRange m).map fun j : Fin m => Val.nat j) = pts := rfl
    rw [hid] at hc
    have wp := wt_nat_le (Q.permHom e hS x i : ℕ)
    have hp := (Q.permHom e hS x i).2
    have wl := wt_list1_le (.nat (Q.permHom e hS x i))
    have h1 : m * (10 ^ 14 * Z ^ 4) ≤ 10 ^ 14 * Z ^ 5 := by
      calc _ ≤ Z * (10 ^ 14 * Z ^ 4) := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    have h2 : loopModK * (m + 1) *
        ((Val.list [inner, pts]).wt + m + (Val.list [.nat (Q.permHom e hS x i)]).wt + 1) ≤
        30000 * Z ^ 2 := by
      calc _ ≤ 1000 * (2 * Z) * (15 * Z) := by
            apply Nat.mul_le_mul
            · simp only [loopModK]; omega
            · omega
        _ = _ := by ring
    have h25 : Z ^ 2 ≤ Z ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have dE : Det P [a] (.get (arg 0) (.nat 0)) E (5 * a.wt + 20) := normCtxGet rfl
  have dx : Det P [a] (.get (arg 0) (.nat 1)) xp (5 * a.wt + 21) := normCtxGet rfl
  have dids : Det P [a] (.get (arg 0) (.nat 2)) ids (5 * a.wt + 22) := normCtxGet rfl
  have di : Det P [a] (arg 1) (.nat i) (2 * a.wt + 6) := Det.arg' (j := 1) rfl
  have dpts : Det P [a] (.get (arg 0) (.nat 3)) pts (5 * a.wt + 23) := normCtxGet rfl
  have dl := Det.mkList (P := P) (env := [a]) (c := 5 * a.wt + 30)
    [(.get (arg 0) (.nat 0), E), (.get (arg 0) (.nat 1), xp),
      (.get (arg 0) (.nat 2), ids), (arg 1, .nat i)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact dE.mono (by omega)
      · exact dx.mono (by omega)
      · exact dids.mono (by omega)
      · exact di.mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dl
  have dc := Det.call (Det.mk2 dl dpts) hs'
  have dg := Det.get' (Det.var' (P := P)
    (env := [a, .list [.nat (Q.permHom e hS x i)]]) (i := 1) rfl) (Det.nat 0) rfl
  refine FunDet.intro hf ((Det.letE dc dg).mono ?_)
  have wp := wt_nat_le (Q.permHom e hS x i : ℕ)
  have hp := (Q.permHom e hS x i).2
  have wl := wt_list1_le (.nat (Q.permHom e hS x i))
  have wargZ' : (Val.list [Val.list [E, xp, ids, .nat i], pts]).wt ≤ 9 * Z := wargZ
  have h15 : Z ≤ Z ^ 5 := Nat.le_self_pow (by norm_num) _
  change _ ≤ 10 ^ 16 * Z ^ 5
  omega

set_option maxHeartbeats 2000000 in
/-- The outer loop recovers the whole point permutation, with no enumeration of `Sym(m)`. -/
theorem normRecover_spec {P : Program} {b point filter cand all test mem m k : ℕ}
    (hmap : P.HasAt b (mapFuns b point)) (hpoint : P.funs[point]? = some (normPointF filter))
    (hfilter : P.HasAt filter (filterFuns filter cand))
    (hcand : P.funs[cand]? = some (normCandidateF all))
    (hall : P.HasAt all (allFuns all test))
    (htest : P.funs[test]? = some (normIncTestF mem)) (hmem : P.HasAt mem (normMemFuns mem))
    {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (x : Q.ρ.range) {Z : ℕ} (hZ : normRecoverSize e x.1 ≤ Z) :
    FunDet P b (.list [.list [encKSetTuples e, encPerm x.1,
      encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))],
      encPerm (1 : Perm (Fin m))]) (encPerm (Q.permHom e hS x)) (10 ^ 18 * Z ^ 6) := by
  let E := encKSetTuples e
  let xp := encPerm x.1
  let ids := encPerm (1 : Perm (Fin Q.d))
  let pts := encPerm (1 : Perm (Fin m))
  let ctx := Val.list [E, xp, ids, pts]
  have h := tabulate_spec hmap (c := ctx)
    (F := fun i : Fin m => Val.nat (Q.permHom e hS x i)) (B := 10 ^ 16 * Z ^ 5)
    (fun i => normPoint_spec hpoint hfilter hcand hall htest hmem Q e hS x i hZ)
  have hout : Val.list ((List.finRange m).map fun i : Fin m => Val.nat (Q.permHom e hS x i)) =
      encPerm (Q.permHom e hS x) := rfl
  have hin : encFun (fun i : Fin m => (i : ℕ)) = pts := rfl
  rw [hout, hin] at h
  refine h.mono ?_
  have hZ' : E.wt + xp.wt + ids.wt + pts.wt + m + Q.d + 20 ≤ Z := hZ
  have hZ20 : 20 ≤ Z := by omega
  have wc := wt_list4_le E xp ids pts
  have wctx : ctx.wt ≤ 3 * Z := by dsimp only [ctx]; omega
  have wa := wt_list2_le ctx pts
  have waZ : (Val.list [ctx, pts]).wt ≤ 9 * Z := by omega
  have wo := wt_encPerm_le (Q.permHom e hS x)
  have woZ : (encPerm (Q.permHom e hS x)).wt ≤ 16 * Z ^ 2 := by
    have hp := Nat.pow_le_pow_left (show m + 1 ≤ 2 * Z by omega) 2
    nlinarith
  have h1 : m * (10 ^ 16 * Z ^ 5) ≤ 10 ^ 16 * Z ^ 6 := by
    calc _ ≤ Z * (10 ^ 16 * Z ^ 5) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have h12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have h2 : mapK * (m + 1) *
      ((Val.list [ctx, pts]).wt + (encPerm (Q.permHom e hS x)).wt + 1) ≤ 52000 * Z ^ 3 := by
    calc _ ≤ 1000 * (2 * Z) * (26 * Z ^ 2) := by
          apply Nat.mul_le_mul
          · simp only [mapK]; omega
          · omega
      _ = _ := by ring
  have h36 : Z ^ 3 ≤ Z ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The common recovery size is bounded by the weight of its actual input. -/
theorem normRecoverSize_le_input {n m k : ℕ} (e : Fin n ≃ (Fin 1 → Product.KSet m k))
    (x : Perm (Fin n)) :
    normRecoverSize e x ≤ 10 *
      ((Val.list [.list [encKSetTuples e, encPerm x, encPerm (1 : Perm (Fin n)),
        encPerm (1 : Perm (Fin m))], encPerm (1 : Perm (Fin m))]).wt + 2) := by
  let ctx := Val.list [encKSetTuples e, encPerm x, encPerm (1 : Perm (Fin n)),
    encPerm (1 : Perm (Fin m))]
  let a := Val.list [ctx, encPerm (1 : Perm (Fin m))]
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp)
  have we : (encKSetTuples e).wt < a.wt := (wt_le_wt_list (by simp)).trans wc
  have wx : (encPerm x).wt < a.wt := (wt_le_wt_list (by simp)).trans wc
  have wn : (encPerm (1 : Perm (Fin n))).wt < a.wt := (wt_le_wt_list (by simp)).trans wc
  have wm : (encPerm (1 : Perm (Fin m))).wt < a.wt := wt_le_wt_list (by simp)
  have hn : n < (encPerm (1 : Perm (Fin n))).wt := by
    have h := length_lt_wt_list ((List.finRange n).map fun i : Fin n => Val.nat i)
    rw [List.length_map, List.length_finRange] at h
    exact h
  have hm : m < (encPerm (1 : Perm (Fin m))).wt := by
    have h := length_lt_wt_list ((List.finRange m).map fun i : Fin m => Val.nat i)
    rw [List.length_map, List.length_finRange] at h
    exact h
  change normRecoverSize e x ≤ 10 * (a.wt + 2)
  unfold normRecoverSize
  omega

end GI.Impl
