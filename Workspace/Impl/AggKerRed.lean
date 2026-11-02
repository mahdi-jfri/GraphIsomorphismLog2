import Workspace.Impl.AggPre
import Workspace.Impl.Reduce

/-!
# The group of a window call, with at most `k²` generators

A window call asks `Continue` on the lift of the kernel `N = ker(φ_T|_A)` (`windowCall`). Its
canonical value needs a group value of the lift with at most `k²` generators (`GroupValC`,
`canon_window`). The program keeps `N` in graph form: pairs `ps` that generate the graph of the
lift (`pairGens_kernelIn`). The first parts generate the lift on positions (`mem_gens_fst`), but
there may be more than `k²` of them. The cited task **PointwiseStab** with no points returns the
same group with at most `k²` generators (`red_spec`).

`krFuns b j` (twenty functions at base `b`): on `[k, pairs]` it maps `fst` over the pairs, puts the
identity in front (`mkGroup`), and cuts the list (`red_spec`).

* `kr_spec`: the output is `encGroup hs` with `gens hs = gens (ps.map Prod.fst)` and at most `k²`
  generators.
* `groupValC_of_kr`: for a graph form of the lift of a subgroup `A ≤ G`, the output is a
  `GroupValC` of the lift.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens PointwiseStab)

variable {k q : ℕ}

/-- On `[c, [a, b]]`: `a`. -/
def krFstF : Expr := .get (arg 1) (.nat 0)

/-- On `[k, pairs]`: the first parts, then `mkGroup`, then the reduction. -/
def krEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 (.nat 0) (arg 1)))
    (.letE (.call (b + 5) (mk2 (arg 0) (.var 1)))
      (.call (b + 12) (mk2 (arg 0) (.var 2))))

/-- The module at base `b` (twenty functions), with the cited primitive at `j`. -/
def krFuns (b j : ℕ) : List Expr :=
  [krEntry b] ++ mapFuns (b + 1) (b + 4) ++ [krFstF] ++ mkGroupFuns (b + 5) ++ redFuns (b + 12) j

theorem krFst_step {P : Program} {f : ℕ} (hf : P.funs[f]? = some krFstF)
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P f (.list [.nat 0, pairV p]) (encPerm p.1) (300 * (k + q + 1) ^ 2) := by
  have g1 := Det.arg' (P := P) (vs := [.nat 0, pairV p]) (rest := []) (j := 1) rfl
  refine FunDet.intro hf ((Det.get' g1 (Det.nat 0) (v := encPerm p.1) rfl).mono ?_)
  have w1 := wt_pairV_le p
  have w2 := wt_list2_le (.nat 0) (pairV p)
  have w3 := wt_nat_le 0
  have w5 := wt_encPerm_le p.1
  have a2 : (k + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a3 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The cost constant of the module. -/
def krK : ℕ := 10 ^ 12

/-- **The group of the first parts, with at most `k²` generators.** -/
theorem kr_spec (hst : PointwiseStab) {P : Program} {b j : ℕ} (hb : P.HasAt b (krFuns b j))
    (hj : P.prims[j]? = some (pointwiseStabPrim hst)) (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunAll P b (.list [.nat k, .list (ps.map pairV)]) (fun w c => ∃ hs : List (Perm (Fin k)),
      w = encGroup hs ∧ gens hs = gens (ps.map Prod.fst) ∧ hs.length ≤ k ^ 2 ∧
      c ≤ (pointwiseStabPrim hst).boundSize (100 * pM k q ps ^ 4) + krK * pM k q ps ^ 9) := by
  have hentry : P.funs[b]? = some (krEntry b) := by
    simpa using (hb.block 0 (gs := [krEntry b]) (by rfl)).single
  have hmap : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := hb.block 1 (by rfl)
  have hfst : P.funs[b + 4]? = some krFstF := by
    simpa using (hb.block 4 (gs := [krFstF]) (by rfl)).single
  have hmk : P.HasAt (b + 5) (mkGroupFuns (b + 5)) := hb.block 5 (by rfl)
  have hred : P.HasAt (b + 12) (redFuns (b + 12) j) := hb.block 12 (by rfl)
  set M := pM k q ps with hM
  have hl : ps.length + 1 ≤ M := by rw [hM]; unfold pM; omega
  have hN : k + q + 1 ≤ M := by rw [hM]; unfold pM; omega
  have hM1 : 1 ≤ M := by omega
  have hl2 : ps.length + 2 ≤ M := by rw [hM]; unfold pM; omega
  have hk1 : k + 2 ≤ M := by rw [hM]; unfold pM; omega
  set vs : List Val := [.nat k, .list (ps.map pairV)]
  have g0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := .nat k) rfl
  have g1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := .list (ps.map pairV)) rfl
  -- the first parts
  have hm := mapList_spec hmap ps pairV (fun p => encPerm p.1) (c := .nat 0)
    (B := 300 * (k + q + 1) ^ 2) (fun a _ a' _ he => by rw [pairV_injective he])
    (fun p _ => krFst_step hfst p)
  have e1 : (ps.map fun p => encPerm p.1) = (ps.map Prod.fst).map encPerm := by simp
  rw [e1] at hm
  have d1 := Det.call (Det.mk2 (Det.nat (P := P) (env := [Val.list vs]) 0) g1) hm
  -- the group value
  have hmg := mkGroup_spec hmk (ps.map Prod.fst)
  have d2 := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [.list ((ps.map Prod.fst).map
    encPerm)]) (j := 0) (v := .nat k) rfl) (Det.var' (P := P)
      (env := [Val.list vs, .list ((ps.map Prod.fst).map encPerm)]) (i := 1) rfl)) hmg
  set gv := encGroup (ps.map Prod.fst) with hgv
  set fv := Val.list ((ps.map Prod.fst).map encPerm) with hfv
  -- weights
  have wP := wt_pairList_le ps
  rw [← hM] at wP
  have wF : fv.wt ≤ ps.length * (2 * (4 * (k + 1) ^ 2) + 1) + 4 := by
    rw [hfv, ← e1]
    exact wt_list_map_le ps _ fun p _ => wt_encPerm_le p.1
  have wG : gv.wt ≤ 40 * ((ps.length + 2) * (k + 1)) ^ 2 := by
    have := wt_encGroup_le (ps.map Prod.fst); simpa using this
  have m2 : (ps.length + 2) * (k + 1) ≤ M ^ 2 := by
    calc (ps.length + 2) * (k + 1) ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
      _ = M ^ 2 := by ring
  have m4 : ((ps.length + 2) * (k + 1)) ^ 2 ≤ M ^ 4 := by
    calc _ ≤ (M ^ 2) ^ 2 := Nat.pow_le_pow_left m2 2
      _ = M ^ 4 := by ring
  have m6 : ((ps.length + 2) * (k + 1)) ^ 3 ≤ M ^ 6 := by
    calc _ ≤ (M ^ 2) ^ 3 := Nat.pow_le_pow_left m2 3
      _ = M ^ 6 := by ring
  have k2 : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have k9 : (k + 1) ^ 9 ≤ M ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have kq2 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hN 2
  have p23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have p34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have p46 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right hM1 (by omega)
  have p69 : M ^ 6 ≤ M ^ 9 := Nat.pow_le_pow_right hM1 (by omega)
  have q2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ hM1
  have q3 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ hM1
  have hlF : ps.length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
  refine FunAll.intro hentry (EvalAll.letE d1 fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  have d3 := Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [fv, gv]) (j := 0) (v := .nat k) rfl)
    (Det.var' (P := P) (env := [Val.list vs, fv, gv]) (i := 2) rfl)
  refine EvalAll.call_funAll d3 fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine (red_spec hst hred hj (G := gens (ps.map Prod.fst)) ⟨_, rfl, rfl⟩).mono ?_
  rintro w cw ⟨hs, rfl, hg, hlen, hcw⟩
  refine ⟨hs, rfl, hg, hlen, ?_⟩
  -- the cost
  have wE := wt_encGroup_le_sq hlen
  have hsz : (Val.list [gv, .list []]).size ≤ 100 * M ^ 4 := by
    have := (Val.list [gv, .list []]).size_le_wt
    have := wt_list2_le gv (.list [])
    have : (Val.list []).wt ≤ 5 := by decide
    omega
  have hbd := (pointwiseStabPrim hst).bound_le hsz
  have wv := wt_list3_le (.nat 0) (.nat 0) (.nat 0)
  have wvs : (Val.list vs).wt ≤ 2 * ((Val.nat k).wt + (Val.list (ps.map pairV)).wt) + 6 :=
    wt_list2_le _ _
  have wk := wt_nat_le k
  have w0 := wt_nat_le 0
  have wa := wt_list2_le (.nat 0) (.list (ps.map pairV))
  have wb := wt_list2_le (.nat k) fv
  have wc := wt_list2_le (.nat k) gv
  have wE' : (encGroup hs).wt ≤ 320 * M ^ 6 := by
    have : (k + 1) ^ 6 ≤ M ^ 6 := Nat.pow_le_pow_left (by omega) 6
    omega
  have hmc : ps.length * (300 * (k + q + 1) ^ 2) ≤ M * (300 * M ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e4 : M * (300 * M ^ 2) = 300 * M ^ 3 := by ring
  have hmc2 : mapK * (ps.length + 1) * ((Val.list [.nat 0, .list (ps.map pairV)]).wt + fv.wt + 1) ≤
      mapK * M * (200 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hl) (by omega)
  have e5 : mapK * M * (200 * M ^ 3) = 200 * mapK * M ^ 4 := by ring
  have hmg2 : mkGroupK * ((ps.length + 2) * (k + 1)) ^ 3 ≤ mkGroupK * M ^ 6 := by
    have : ((ps.map Prod.fst).length + 2) * (k + 1) = (ps.length + 2) * (k + 1) := by simp
    exact Nat.mul_le_mul_left _ m6
  have e6 : ((ps.map Prod.fst).length + 2) * (k + 1) = (ps.length + 2) * (k + 1) := by simp
  rw [e6] at hc2
  rw [← hgv] at hcw
  have p12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have q4 : 1 ≤ M ^ 4 := Nat.one_le_pow _ _ hM1
  have q6 : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ hM1
  have q9 : 1 ≤ M ^ 9 := Nat.one_le_pow _ _ hM1
  have B1 : c1 ≤ 300000 * M ^ 4 := by simp only [mapK] at *; omega
  have B2 : c2 ≤ 200000 * M ^ 6 := by simp only [mkGroupK] at *; omega
  have B3 : ca ≤ 1000 * M ^ 4 := by omega
  have B4 : cw ≤ (pointwiseStabPrim hst).boundSize (100 * M ^ 4) + 1000 * M ^ 4 +
      10 ^ 7 * M ^ 9 := by omega
  simp only [krK]
  omega

/-- **The window group from a graph form.** If `ps` is a graph form of the lift of `A`, the output
of the module is a group value of the lift on positions, with at most `k²` generators. -/
theorem groupValC_of_kr {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
    {H : Subgroup (Perm Ω)} (hH : H ≤ S.G) {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L H ps) {hs : List (Perm (Fin k))} (hg : gens hs = gens (ps.map Prod.fst))
    (hl : hs.length ≤ k ^ 2) : GroupValC k (encGroup hs) (groupFin e H) := by
  refine ⟨hs, rfl, ?_, hl⟩
  rw [hg]
  ext a
  rw [mem_gens_fst hps]
  simp only [groupFin, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, -, hA, rfl⟩; exact ⟨g, hA, rfl⟩
  · rintro ⟨g, hA, rfl⟩; exact ⟨g, hH hA, hA, rfl⟩

end GI.Impl
