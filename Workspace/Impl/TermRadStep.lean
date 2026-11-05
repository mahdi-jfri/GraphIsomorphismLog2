module

public import Workspace.Impl.TermRadMath
public import Workspace.Impl.GMPFactorKernel
public import Workspace.Lang.Prims.Ops
public import Workspace.Lang.Prims.Blocks
public import Workspace.Lang.Lib.Fold

@[expose] public section

/-!
# T2, one factor: the step of the radical program

The program of `TermRad.lean` runs through the factors `N C_j / N C_{j+1}` of the chief series
`C₀ = H > C₁ > ⋯` of `H` multiplied by `N` (paragraph after Lemma A.21). Step `j`, on the
context `[gens H, gens N, chief series]` and the group `A` computed so far:
1. the group values of `U = N C_j` and `V = N C_{j+1}` (the generators of `N` followed by those
   of the chief term);
2. the nonabelian test `⁅C_j, C_j⁆ ≤ V` (the cited **DerivedSubgroup**, then the subgroup test
   by **Membership**, `le_spec`); `⁅C_j, C_j⁆ ≤ N C_{j+1}` holds exactly when the factor
   `U/V` is abelian (`rad_comm_le_iff`);
3. if the factor is nonabelian: the preimage `C` of `C_{H/V}(U/V)` (`GMPFactorKernel.lean`,
   conjugation on the right cosets of `V` in `U`) and `A ∩ C` (the cited
   **NormalizedIntersection**: `C` is normal in `H ≥ A`).
So after step `j` the group is `{h | radCond H N Hs (j + 1) h}` (`radStep_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### The expressions -/

/-- `gens H` in the context `[[hv, nv, cs], i, acc]`. -/
def radHvE : Expr := .get (arg 0) (.nat 0)
/-- `gens N`. -/
def radNvE : Expr := .get (arg 0) (.nat 1)
/-- The chief series. -/
def radCsE : Expr := .get (arg 0) (.nat 2)
/-- The degree, read off `gens H`. -/
def radNE : Expr := .get radHvE (.nat 0)

/-- The group value of `N ⊔ ⟨L⟩` for a generator list `L`: `[n, gens N ++ L]`. -/
def radUnionE (ap : ℕ) (lE : Expr) : Expr :=
  mk2 radNE (.call ap (mk2 (.get radNvE (.nat 1)) lE))

/-- **The step on factor `i`.** Environment `[a, U, V, D, t, C, A ∩ C]`: the group values of
`U = N C_i` and `V = N C_{i+1}`, generators of `D = ⁅C_i, C_i⁆`, the test `D ≤ V`, and, for a
nonabelian factor, generators of the quotient centralizer `C` and of `A ∩ C`. -/
def radStepBody (ap mg le jder jni fk : ℕ) : Expr :=
  .letE (radUnionE ap (.get radCsE (arg 1)))
  (.letE (radUnionE ap (.get radCsE (.arith .add (arg 1) (.nat 1))))
  (.letE (.prim jder (.call mg (mk2 radNE (.get radCsE (arg 1)))))
  (.letE (.call le (mk2 (.var 2) (.call mg (mk2 radNE (.var 3)))))
  (.ite (.var 4) (arg 2)
    (.letE (.call fk (mk3 radHvE (.var 1) (.var 2)))
    (.letE (.prim jni (mk2 (arg 2) (.call mg (mk2 radNE (.var 5)))))
      (.call mg (mk2 radNE (.var 6)))))))))

/-! ### Reading the context -/

section Read

variable {P : Program} {hv nv cs acc : Val} {i : ℕ} {rest : List Val}

/-- The weight of the step argument. -/
abbrev radW (hv nv cs acc : Val) (i : ℕ) : ℕ := (Val.list [.list [hv, nv, cs], .nat i, acc]).wt

theorem rad_wt_facts (hv nv cs acc : Val) (i : ℕ) :
    hv.wt < radW hv nv cs acc i ∧ nv.wt < radW hv nv cs acc i ∧ cs.wt < radW hv nv cs acc i ∧
      acc.wt < radW hv nv cs acc i ∧ (Val.nat i).wt < radW hv nv cs acc i := by
  have hc : (Val.list [hv, nv, cs]).wt < radW hv nv cs acc i := wt_le_wt_list (by simp)
  have h1 : hv.wt < (Val.list [hv, nv, cs]).wt := wt_le_wt_list (by simp)
  have h2 : nv.wt < (Val.list [hv, nv, cs]).wt := wt_le_wt_list (by simp)
  have h3 : cs.wt < (Val.list [hv, nv, cs]).wt := wt_le_wt_list (by simp)
  have h4 : acc.wt < radW hv nv cs acc i := wt_le_wt_list (by simp)
  have h5 : (Val.nat i).wt < radW hv nv cs acc i := wt_le_wt_list (by simp)
  omega

theorem rad_d_ctx :
    Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) (arg 0) (.list [hv, nv, cs])
      (2 * radW hv nv cs acc i + 5) := Det.arg' (j := 0) rfl

theorem rad_d_hv : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) radHvE hv
    (4 * radW hv nv cs acc i + 10) := by
  have := rad_wt_facts hv nv cs acc i
  exact (Det.get' rad_d_ctx (Det.nat 0) rfl).mono (by omega)

theorem rad_d_nv : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) radNvE nv
    (4 * radW hv nv cs acc i + 10) := by
  have := rad_wt_facts hv nv cs acc i
  exact (Det.get' rad_d_ctx (Det.nat 1) rfl).mono (by omega)

theorem rad_d_cs : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) radCsE cs
    (4 * radW hv nv cs acc i + 11) := by
  have := rad_wt_facts hv nv cs acc i
  exact (Det.get' rad_d_ctx (Det.nat 2) rfl).mono (by omega)

theorem rad_d_i : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) (arg 1) (.nat i)
    (3 * radW hv nv cs acc i + 10) := by
  have := rad_wt_facts hv nv cs acc i
  have e : (Val.list [.list [hv, nv, cs], .nat i, acc]).wt = radW hv nv cs acc i := rfl
  exact (Det.arg' (j := 1) rfl).mono (by omega)

theorem rad_d_acc : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) (arg 2) acc
    (3 * radW hv nv cs acc i + 10) := by
  have := rad_wt_facts hv nv cs acc i
  have e : (Val.list [.list [hv, nv, cs], .nat i, acc]).wt = radW hv nv cs acc i := rfl
  exact (Det.arg' (j := 2) rfl).mono (by omega)

theorem rad_d_n {gs : List (Perm (Fin n))} (hg : hv = encGroup gs) :
    Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) radNE (.nat n)
      (6 * radW hv nv cs acc i + 20) := by
  have := rad_wt_facts hv nv cs acc i
  have hn : (Val.nat n).wt < hv.wt := by
    rw [hg]; exact wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hh : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) radHvE hv
    (4 * radW hv nv cs acc i + 10) := rad_d_hv
  rw [hg] at hh hn ⊢
  exact (Det.get' hh (Det.nat 0) (v := .nat n) rfl).mono (by rw [hg] at this; omega)

/-- Entry `j` of the chief series. -/
theorem rad_d_csj {L : List (List (Perm (Fin n)))}
    (hcs : cs = .list (L.map fun hs => .list (hs.map encPerm))) {j : ℕ} (hj : j < L.length)
    {ie : Expr} {ci : ℕ} (di : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) ie (.nat j) ci) :
    Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) (.get radCsE ie)
      (.list (L[j].map encPerm)) (ci + 6 * radW hv nv cs acc i + 20) := by
  have := rad_wt_facts hv nv cs acc i
  have hlt : (Val.list (L[j].map encPerm)).wt < cs.wt := by
    rw [hcs]
    exact wt_le_wt_list (List.mem_map.mpr ⟨L[j], List.getElem_mem hj, rfl⟩)
  have hh : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) radCsE cs
    (4 * radW hv nv cs acc i + 11) := rad_d_cs
  have hget : (L.map fun hs => Val.list (hs.map encPerm))[j]? = some (.list (L[j].map encPerm)) := by
    simp [hj]
  rw [hcs] at hh hlt di ⊢
  rw [hcs] at this
  exact (Det.get' hh di hget).mono (by omega)

end Read

/-! ### The union value `N ⊔ ⟨L⟩` -/

/-- The weight of an appended list. -/
theorem rad_wt_append (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ 3 * ((Val.list xs).wt + (Val.list ys).wt) + 4 := by
  have h := wt_list_le (xs ++ ys)
  have h1 := sum_wt_lt_wt_list xs
  have h2 := sum_wt_lt_wt_list ys
  have h3 := length_lt_wt_list xs
  have h4 := length_lt_wt_list ys
  simp only [List.map_append, List.sum_append, List.length_append] at h
  omega

theorem rad_union_det {P : Program} {ap : ℕ} (hap : P.HasAt ap (appendFuns ap))
    {hv nv cs acc : Val} {i : ℕ} {rest : List Val} {gs ns hs : List (Perm (Fin n))}
    (hg : hv = encGroup gs) (hn : nv = encGroup ns) {lE : Expr} {cl : ℕ}
    (dl : Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) lE (.list (hs.map encPerm)) cl)
    (hl : (Val.list (hs.map encPerm)).wt ≤ radW hv nv cs acc i) :
    Det P (.list [.list [hv, nv, cs], .nat i, acc] :: rest) (radUnionE ap lE)
      (encGroup (ns ++ hs)) (cl + 30000 * (radW hv nv cs acc i + 1) ^ 2) ∧
      (encGroup (ns ++ hs)).wt ≤ 14 * radW hv nv cs acc i + 14 := by
  subst hg hn
  have hw := rad_wt_facts (encGroup gs) (encGroup ns) cs acc i
  have dn := rad_d_n (P := P) (cs := cs) (acc := acc) (i := i) (rest := rest)
    (nv := encGroup ns) (hv := encGroup gs) (gs := gs) rfl
  have e1 : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt :=
    wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have dnv : Det P (.list [.list [encGroup gs, encGroup ns, cs], .nat i, acc] :: rest) radNvE
      (encGroup ns) _ := rad_d_nv
  have dn1 := Det.get' dnv (Det.nat 1) (v := .list ((1 :: ns).map encPerm)) rfl
  have hap' := append_spec hap ((1 :: ns).map encPerm) (hs.map encPerm)
  have happ : ((1 :: ns).map encPerm) ++ hs.map encPerm = (1 :: (ns ++ hs)).map encPerm := by
    simp
  rw [happ] at hap'
  have hwa := rad_wt_append ((1 :: ns).map encPerm) (hs.map encPerm)
  rw [happ] at hwa
  have h2 := wt_list2_le (.list ((1 :: ns).map encPerm)) (.list (hs.map encPerm))
  have hlen := length_lt_wt_list (hs.map encPerm)
  simp only [List.length_map] at hlen
  have hapd : FunDet P ap (.list [.list ((1 :: ns).map encPerm), .list (hs.map encPerm)])
      (.list ((1 :: (ns ++ hs)).map encPerm)) (loopModK * (hs.length + 1) *
        ((Val.list [.list ((1 :: ns).map encPerm), .list (hs.map encPerm)]).wt + hs.length +
          (Val.list ((1 :: (ns ++ hs)).map encPerm)).wt + 1)) :=
    FunAll.mono hap' fun w c h => ⟨h.1, by have := h.2; rw [h.1] at this; simpa using this⟩
  have dap := Det.call (Det.mk2 dn1 dl) hapd
  have hnw : (Val.nat n).wt < (encGroup gs).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have e2 : (encGroup (ns ++ hs)).wt =
      (Val.list [.nat n, .list ((1 :: (ns ++ hs)).map encPerm)]).wt := rfl
  have h3 := wt_list2_le (.nat n) (.list ((1 :: (ns ++ hs)).map encPerm))
  have dfin := Det.mk2 dn dap
  clear dl dn dnv dn1 dap hap' hapd hap
  generalize radW (encGroup gs) (encGroup ns) cs acc i = W at *
  have hwt : (encGroup (ns ++ hs)).wt ≤ 14 * W + 14 := by omega
  refine ⟨dfin.mono ?_, hwt⟩
  -- the cost
  have hm : loopModK * (hs.length + 1) * ((Val.list [.list ((1 :: ns).map encPerm),
      .list (hs.map encPerm)]).wt + hs.length + (Val.list ((1 :: (ns ++ hs)).map encPerm)).wt + 1)
      ≤ loopModK * (W + 1) * (20 * (W + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e3 : loopModK * (W + 1) * (20 * (W + 1)) = 20000 * (W + 1) ^ 2 := by
    simp only [loopModK]; ring
  have hW1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have e4 : (Val.list [Val.nat n, Val.list ((1 :: (ns ++ hs)).map encPerm)]).wt =
    (encGroup (ns ++ hs)).wt := rfl
  omega

/-! ### Group values from generator outputs -/

/-- `mkGroup` on `[n, L]` with `L` a generator output of `G`, inside the step. -/
theorem rad_mk_det {P : Program} {mg : ℕ} (hmg : P.HasAt mg (mkGroupFuns mg))
    {env : List Val} {nE lE : Expr} {cn cl : ℕ} {L : Val} {G : Subgroup (Perm (Fin n))}
    (dn : Det P env nE (.nat n) cn) (dl : Det P env lE L cl) (hL : GensVal n L G) :
    ∃ hs : List (Perm (Fin n)), hs.length ≤ n ^ 2 ∧ gens hs = G ∧
      Det P env (.call mg (mk2 nE lE)) (encGroup hs)
        (cn + cl + 2 * (Val.list [.nat n, L]).wt + 8 * mkGroupK * (n + 1) ^ 9 + 320 * (n + 1) ^ 6
          + 8) ∧ (encGroup hs).wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨hs, rfl, hl, hf, ⟨_, he, hg⟩, hw⟩ := mkGroup_gensVal hmg hL
  obtain rfl := encGroup_injective he
  refine ⟨hs, hl, hg, (Det.call (Det.mk2 dn dl) hf).mono (by omega), hw⟩

/-! ### Facts for the step -/

theorem rad_gens_append (as bs : List (Perm (Fin n))) : gens (as ++ bs) = gens as ⊔ gens bs := by
  unfold gens
  rw [← Subgroup.closure_union]
  congr 1
  ext g
  simp

theorem rad_term_map {L : List (List (Perm (Fin n)))} {j : ℕ} (hj : j < L.length) :
    radTerm (L.map gens) j = gens L[j] := by
  simp [radTerm, hj]

theorem rad_cond_succ {H N : Subgroup (Perm (Fin n))} {Hs : List (Subgroup (Perm (Fin n)))}
    {i : ℕ} {h : Perm (Fin n)} :
    radCond H N Hs (i + 1) h ↔ radCond H N Hs i h ∧
      (¬ ⁅radTerm Hs i, radTerm Hs i⁆ ≤ N ⊔ radTerm Hs (i + 1) →
        ∀ x ∈ N ⊔ radTerm Hs i, h * x * h⁻¹ * x⁻¹ ∈ N ⊔ radTerm Hs (i + 1)) := by
  constructor
  · rintro ⟨hH, hc⟩
    exact ⟨⟨hH, fun j hj => hc j (by omega)⟩, hc i (by omega)⟩
  · rintro ⟨⟨hH, hc⟩, hi⟩
    refine ⟨hH, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hc j hj
    · exact hi

/-- The quotient centralizer is normalized by `H`. -/
theorem rad_qc_normalized {H U V C : Subgroup (Perm (Fin n))}
    (hU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U) (hV : ∀ g ∈ H, ∀ x ∈ V, g * x * g⁻¹ ∈ V)
    (hC : ∀ y, y ∈ C ↔ y ∈ H ∧ ∀ x ∈ U, y * x * y⁻¹ * x⁻¹ ∈ V) :
    ∀ g ∈ H, ∀ y ∈ C, g * y * g⁻¹ ∈ C := by
  intro g hg y hy
  rw [hC] at hy ⊢
  refine ⟨H.mul_mem (H.mul_mem hg hy.1) (H.inv_mem hg), fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ U := hU g⁻¹ (H.inv_mem hg) x hx
  have := hV g hg _ (hy.2 _ hx')
  convert this using 1
  group

/-- The invariant of the loop after the factors `j < i`: `acc` is a group value of the group
`{h | radCond H N Hs i h}`, and it weighs at most `wt (gens H) + 320 (n + 1)⁶` (it is `gens H`
itself, or a group value with at most `n²` generators). -/
def RadInv (H N : Subgroup (Perm (Fin n))) (Hs : List (Subgroup (Perm (Fin n)))) (hv : Val)
    (i : ℕ) (acc : Val) : Prop :=
  ∃ A : Subgroup (Perm (Fin n)), GroupVal n acc A ∧ (∀ h, h ∈ A ↔ radCond H N Hs i h) ∧
    acc.wt ≤ hv.wt + 320 * (n + 1) ^ 6

/-- The bound of one step, for a step argument of weight `W`. -/
def radStepCost (pd pq pi pm : Prim) (W : ℕ) : ℕ :=
  pd.boundSize (1000 * (W + 1) ^ 6) + pq.boundSize (1000 * (W + 1) ^ 6) +
    pi.boundSize (1000 * (W + 1) ^ 6) +
    1000 * (W + 1) ^ 6 * pm.boundSize (1000 * (W + 1) ^ 6) + 10 ^ 8 * (1000 * (W + 1) ^ 6) ^ 3

theorem rad_ite_zero {P : Program} {env : List Val} {c t e : Expr} {cc : ℕ}
    (hc : Det P env c (.nat 0) cc) {R : Val → ℕ → Prop} (he : EvalAll P env e R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ce, R w ce ∧ c' ≤ cc + ce + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨0, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_pos rfl]
    exact he.mono fun w ce hw => ⟨ce, hw, by omega⟩

end GI.Impl
