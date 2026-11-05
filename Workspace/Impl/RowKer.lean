module

public import Workspace.Impl.RowProg

@[expose] public section

/-!
# The label kernel in graph form, in `GI.Lang`

Theorem A.18 works with the elements of `G` that preserve every row. In the row case these are
the elements with trivial label image (`ker π`). A program carries a subgroup `A ≤ G` in graph
form, as pairs `(a, π a)` (`PairGens`). This file computes the graph form of `A ∩ ker π` with one
call of the cited task **PointwiseStab**:

1. swap each pair to `(π a, a)` (`swapMap_spec`);
2. take the pointwise stabilizer of all `q` label points in the first part (`graphStabL_spec`):
   these are the pairs with `π a = 1`;
3. swap back.

`rowKer_spec` states the result in the form of `pairGens_of_pre` with no image generators, so
`rowKer_pairGens` gives `PairGens e L (A ⊓ labPre ⊥) qs`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab PointwiseStab)

variable {k q : ℕ}

/-! ### Swapping pairs -/

/-- On `[c, [a, b]]`: `[b, a]`. -/
def swapF : Expr := mk2 (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 0))

/-- The cost constant of a swap. -/
def swapK : ℕ := 1000

theorem pairV_swap (p : Perm (Fin k) × Perm (Fin q)) :
    pairV p.swap = .list [encPerm p.2, encPerm p.1] := rfl

theorem swapF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some swapF) (c : Val)
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P f (.list [c, pairV p]) (pairV p.swap) (swapK * ((Val.list [c, pairV p]).wt + 1)) := by
  set A := Val.list [c, pairV p] with hA
  have g1 := Det.arg' (P := P) (vs := [c, pairV p]) (rest := []) (j := 1) rfl
  have da := Det.get' g1 (Det.nat 1) (v := encPerm p.2) rfl
  have db := Det.get' g1 (Det.nat 0) (v := encPerm p.1) rfl
  refine FunDet.intro hf ((Det.mk2 da db).mono ?_)
  have w1 : (pairV p).wt < A.wt := wt_le_wt_list (by simp)
  have w2 : (encPerm p.1).wt < (pairV p).wt := wt_le_wt_list (by simp)
  have w3 : (encPerm p.2).wt < (pairV p).wt := wt_le_wt_list (by simp)
  have w4 := wt_list2_le (encPerm p.2) (encPerm p.1)
  have eA : (Val.list [c, pairV p]).wt = A.wt := rfl
  simp only [swapK]
  omega

/-- `map swapF` at base `b` (four functions). -/
def swapMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [swapF]

/-- The cost constant of the swap map. -/
def swapMapK : ℕ := 10000000

theorem wt_pairV_swap (p : Perm (Fin k) × Perm (Fin q)) : (pairV p.swap).wt = (pairV p).wt := by
  show (Val.list [encPerm p.2, encPerm p.1]).wt = (Val.list [encPerm p.1, encPerm p.2]).wt
  rw [wt_list_eq, wt_list_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  rw [show (encPerm p.2).wt + ((encPerm p.1).wt + 0) = (encPerm p.1).wt + ((encPerm p.2).wt + 0)
    by omega, show (encPerm p.2).size + ((encPerm p.1).size + 0) =
      (encPerm p.1).size + ((encPerm p.2).size + 0) by omega]

theorem size_pairV_swap (p : Perm (Fin k) × Perm (Fin q)) :
    (pairV p.swap).size = (pairV p).size := by
  show (Val.list [encPerm p.2, encPerm p.1]).size = (Val.list [encPerm p.1, encPerm p.2]).size
  rw [size_list, size_list, length_cellsList, length_cellsList]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem wt_pairList_swap (ps : List (Perm (Fin k) × Perm (Fin q))) :
    (Val.list ((ps.map Prod.swap).map pairV)).wt = (Val.list (ps.map pairV)).wt := by
  rw [wt_list_eq, wt_list_eq]
  simp only [List.map_map, List.length_map]
  have h1 : (ps.map (Val.wt ∘ pairV ∘ Prod.swap)) = ps.map (Val.wt ∘ pairV) :=
    List.map_congr_left fun p _ => wt_pairV_swap p
  have h2 : (ps.map (Val.size ∘ pairV ∘ Prod.swap)) = ps.map (Val.size ∘ pairV) :=
    List.map_congr_left fun p _ => size_pairV_swap p
  rw [h1, h2]

/-- **Swap every pair**: `[c, [[a, b], …]]` ↦ `[[b, a], …]`. -/
theorem swapMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (swapMapFuns b)) (c : Val)
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P b (.list [c, .list (ps.map pairV)]) (.list ((ps.map Prod.swap).map pairV))
      (swapMapK * ((Val.list [c, .list (ps.map pairV)]).wt + 1) ^ 2) := by
  have hf : P.funs[b + 3]? = some swapF := by
    simpa [swapMapFuns, mapFuns, loopFuns] using h.right.single
  obtain ⟨A, hA⟩ : ∃ A, (Val.list [c, .list (ps.map pairV)]).wt = A := ⟨_, rfl⟩
  have h3 : (Val.list (ps.map pairV)).wt < A := hA ▸ wt_le_wt_list (by simp)
  have h4 : c.wt < A := hA ▸ wt_le_wt_list (by simp)
  have hm := mapList_spec h.left ps pairV (fun p => pairV p.swap) (c := c)
    (B := swapK * (4 * A + 7))
    (fun a _ a' _ he => by rw [pairV_injective he])
    (fun p hp => (swapF_spec hf c p).mono (by
      have h1 : (pairV p).wt < (Val.list (ps.map pairV)).wt :=
        wt_le_wt_list (List.mem_map_of_mem hp)
      have h2 := wt_list2_le c (pairV p)
      apply Nat.mul_le_mul_left
      omega))
  have e1 : (ps.map fun p => pairV p.swap) = (ps.map Prod.swap).map pairV := by simp
  rw [e1] at hm
  refine hm.mono ?_
  have hl : ps.length < A := by
    have := length_lt_wt_list (ps.map pairV)
    simp only [List.length_map] at this
    omega
  have hw : (Val.list ((ps.map Prod.swap).map pairV)).wt < A := by
    rw [wt_pairList_swap]; exact h3
  rw [hA]
  have a1 : ps.length * (swapK * (4 * A + 7)) ≤ A * (swapK * (7 * (A + 1))) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
  have a2 : mapK * (ps.length + 1) * (A + (Val.list ((ps.map Prod.swap).map pairV)).wt + 1) ≤
      mapK * (A + 1) * (2 * (A + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have a3 : A * (swapK * (7 * (A + 1))) ≤ 7 * swapK * (A + 1) ^ 2 := by
    have : A * (swapK * (7 * (A + 1))) = 7 * swapK * (A * (A + 1)) := by ring
    rw [this, sq]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  have a4 : mapK * (A + 1) * (2 * (A + 1)) = 2 * mapK * (A + 1) ^ 2 := by ring
  calc _ ≤ 7 * swapK * (A + 1) ^ 2 + 2 * mapK * (A + 1) ^ 2 :=
        Nat.add_le_add (a1.trans a3) (a2.trans a4.le)
    _ = (7 * swapK + 2 * mapK) * (A + 1) ^ 2 := by ring
    _ ≤ swapMapK * (A + 1) ^ 2 := Nat.mul_le_mul_right _ (by simp only [swapK, mapK, swapMapK]; norm_num)

/-! ### The kernel -/

/-- Swapping the factors of a subgroup of pairs. -/
theorem closure_swap (ps : List (Perm (Fin k) × Perm (Fin q))) :
    Subgroup.closure {p | p ∈ ps.map Prod.swap} =
      (Subgroup.closure {p | p ∈ ps}).map (MulEquiv.prodComm).toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image, MulEquiv.coe_toMonoidHom]
  rfl

theorem mem_closure_swap {ps : List (Perm (Fin k) × Perm (Fin q))} {x : Perm (Fin q) × Perm (Fin k)} :
    x ∈ Subgroup.closure {p | p ∈ ps.map Prod.swap} ↔ x.swap ∈ Subgroup.closure {p | p ∈ ps} := by
  rw [closure_swap, Subgroup.mem_map_equiv]
  rfl

/-- All label points. -/
theorem encPts_finRange (q : ℕ) : encPts (List.finRange q) = encPerm (1 : Perm (Fin q)) := by
  rw [encPts_eq]
  rfl

/-- **The kernel from the swapped stabilizer.** If `ks` generates the pairs `(b, a)` of the
swapped group whose first part fixes every label point, then the swapped `ks` generate the pairs
of `ps` with trivial second part. -/
theorem closure_ker_of_swap {ps ks : List (Perm (Fin k) × Perm (Fin q))}
    (h : Subgroup.closure {p | p ∈ ks.map Prod.swap} =
      Subgroup.closure {p | p ∈ (ps.map Prod.swap)} ⊓ fixFst q k (List.finRange q)) :
    Subgroup.closure {p | p ∈ ks} =
      Subgroup.closure {p | p ∈ ps} ⊓ (gens ([] : List (Perm (Fin q)))).comap (MonoidHom.snd _ _) := by
  have hg : gens ([] : List (Perm (Fin q))) = ⊥ := by
    simp [gens]
  ext x
  have hx : x ∈ Subgroup.closure {p | p ∈ ks} ↔ x.swap ∈ Subgroup.closure {p | p ∈ ks.map Prod.swap} := by
    rw [mem_closure_swap]; rfl
  rw [hx, h, Subgroup.mem_inf, Subgroup.mem_inf, mem_closure_swap, Subgroup.mem_comap, hg,
    Subgroup.mem_bot]
  simp only [Prod.swap_swap, MonoidHom.coe_snd]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hfix
    ext i
    exact congrArg Fin.val (hfix i (List.mem_finRange i))
  · intro h1 i _
    show x.2 i = i
    rw [h1]; rfl

/-- On `[[k, q], pairs]`: swap, stabilize all label points, swap back. -/
def rowKerF (b : ℕ) : Expr :=
  let kE := Expr.get (arg 0) (.nat 0)
  let qE := Expr.get (arg 0) (.nat 1)
  .letE (.call (b + 8) (mk3 (mk2 qE kE) (.call (b + 1) (mk2 (.nat 0) (arg 1))) (.call (b + 5) qE)))
    (.call (b + 1) (mk2 (.nat 0) (.var 1)))

/-- The kernel module at `b`, with the cited primitive at `jp`. -/
def rowKerFuns (b jp : ℕ) : List Expr :=
  [rowKerF b] ++ swapMapFuns (b + 1) ++ rangeFuns (b + 5) ++ graphStabFuns (b + 8) jp

/-- The cost constant of the kernel module. -/
def rowKerK : ℕ := 10 ^ 18

/-- The cost bound of the kernel module, with `M = k + q + |ps| + 2`. -/
noncomputable def rowKerCost (hst : PointwiseStab) (M : ℕ) : ℕ :=
  (pointwiseStabPrim hst).c * (100 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k + rowKerK * M ^ 12

theorem pM_swap (ps : List (Perm (Fin k) × Perm (Fin q))) :
    pM q k (ps.map Prod.swap) = pM k q ps := by
  unfold pM; simp; omega

theorem wt_pairs_le_of_len {ps : List (Perm (Fin k) × Perm (Fin q))} {M : ℕ}
    (h : pM k q ps ≤ M) : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
  have := wt_pairList_le ps
  have := Nat.pow_le_pow_left h 3
  omega

set_option maxHeartbeats 1600000 in
/-- **The label kernel in graph form.** On `[[k, q], pairs]` the module returns pairs `ks` that
generate the pairs of `⟨ps⟩` with trivial second part, at most `(k + q)²` of them. It calls
**PointwiseStab** once. -/
theorem rowKer_spec (hst : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (rowKerFuns b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim hst))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunAll P b (.list [.list [.nat k, .nat q], .list (ps.map pairV)])
      (fun w c => ∃ ks : List (Perm (Fin k) × Perm (Fin q)), w = .list (ks.map pairV) ∧
        ks.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ ks} =
          Subgroup.closure {p | p ∈ ps} ⊓ (gens ([] : List (Perm (Fin q)))).comap (MonoidHom.snd _ _) ∧
        c ≤ rowKerCost hst (pM k q ps)) := by
  have hentry : P.funs[b]? = some (rowKerF b) := by
    simpa using (hb.block 0 (gs := [rowKerF b]) (by rfl)).single
  have hsw : P.HasAt (b + 1) (swapMapFuns (b + 1)) := hb.block 1 (by rfl)
  have hrg : P.HasAt (b + 5) (rangeFuns (b + 5)) := hb.block 5 (by rfl)
  have hgs : P.HasAt (b + 8) (graphStabFuns (b + 8) jp) := hb.block 8 (by rfl)
  set A : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV)] with hA
  have gk : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 0)) (.nat k) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV)])
      (rest := rest) (j := 0) rfl) (Det.nat 0) (v := .nat k) rfl
  have gq : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 1)) (.nat q) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV)])
      (rest := rest) (j := 0) rfl) (Det.nat 1) (v := .nat q) rfl
  -- the swapped pairs and the label points
  have d1 := Det.call (Det.mk2 (Det.nat (P := P) (env := [A]) 0)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV)]) (rest := [])
      (j := 1) rfl)) (swapMap_spec hsw (.nat 0) ps)
  have d2 := Det.call (gq []) (range_det hrg q)
  rw [← encPts_finRange] at d2
  have d3 := Det.mk3 (Det.mk2 (gq []) (gk [])) d1 d2
  set sw := ps.map Prod.swap with hsw'
  have hstab := graphStabL_spec hst hgs hj sw (List.finRange q)
  set STB := (pointwiseStabPrim hst).bound
      (.list [encGroup (sw.map encPair), encPts (List.finRange q)]) +
    graphStabK * stabM q k sw (List.finRange q) ^ 8 with hSTB
  obtain ⟨C3, d3c, hC3⟩ : ∃ C3, Det P [A] _ _ C3 ∧ C3 = _ := ⟨_, d3, rfl⟩
  refine FunAll.intro hentry (EvalAll.letE (Ra := fun w c => ∃ ks' : List (Perm (Fin q) × Perm (Fin k)),
      w = .list (ks'.map pairV) ∧ ks'.length ≤ (q + k) ^ 2 ∧
      Subgroup.closure {p | p ∈ ks'} = Subgroup.closure {p | p ∈ sw} ⊓ fixFst q k (List.finRange q) ∧
      c ≤ C3 + STB + w.wt + 1)
    (EvalAll.call_funAll d3c fun v ca hv => ?_) fun w1 c1 h1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    exact hstab.mono fun w c hw => by
      obtain ⟨ks', rfl, h1, h2, h3⟩ := hw
      exact ⟨ks', rfl, h1, h2, by omega⟩
  · obtain ⟨ks', rfl, hkl, hks', hc1⟩ := h1
    -- swap back
    have d4 := Det.call (Det.mk2 (Det.nat (P := P) (env := [A, .list (ks'.map pairV)]) 0)
      (Det.var' (P := P) (env := [A, .list (ks'.map pairV)]) (i := 1) rfl))
      (swapMap_spec hsw (.nat 0) ks')
    refine d4.post fun c hc => ⟨ks'.map Prod.swap, rfl, ?_, ?_, ?_⟩
    · simp only [List.length_map]; rw [Nat.add_comm]; exact hkl
    · refine closure_ker_of_swap ?_
      rw [List.map_map, show (Prod.swap ∘ Prod.swap : Perm (Fin q) × Perm (Fin k) → _) = id from
        funext fun x => Prod.swap_swap x, List.map_id]
      exact hks'
    · -- the cost
      set M := pM k q ps with hM
      have hM2 : 2 ≤ M := by simp only [hM, pM]; omega
      have hk : k + q + 1 ≤ M := by simp only [hM, pM]; omega
      have hpl : ps.length ≤ M := by simp only [hM, pM]; omega
      have m1 : 1 ≤ M := by omega
      have pw : ∀ i j, i ≤ j → M ^ i ≤ M ^ j := fun i j hij => Nat.pow_le_pow_right m1 hij
      have bps := wt_pairs_le_of_len (ps := ps) (le_refl _)
      rw [← hM] at bps
      have bkq := wt_list2_le (.nat k) (.nat q)
      have bqk := wt_list2_le (.nat q) (.nat k)
      have wk := wt_nat_le k
      have wq := wt_nat_le q
      have bA := wt_list2_le (.list [.nat k, .nat q]) (.list (ps.map pairV))
      have eA : A.wt = (Val.list [.list [.nat k, .nat q], .list (ps.map pairV)]).wt := rfl
      have bsw : (Val.list (sw.map pairV)).wt ≤ 50 * M ^ 3 := by
        rw [hsw', wt_pairList_swap]; exact bps
      have bX := wt_encPts_le' (k := q) (X := List.finRange q) (by simp)
      have bq2 : 3 * (q + 2) ^ 2 + 4 ≤ 7 * M ^ 2 := by
        have := Nat.pow_le_pow_left (show q + 2 ≤ M by simp only [hM, pM]; omega) 2
        have := Nat.one_le_pow 2 M m1
        omega
      have b0 := wt_list2_le (.nat 0) (.list (ps.map pairV))
      have w0 := wt_nat_le 0
      -- step 1
      have c1a : swapMapK * ((Val.list [.nat 0, .list (ps.map pairV)]).wt + 1) ^ 2 ≤
          swapMapK * (200 * M ^ 3) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := Nat.one_le_pow 3 M m1; omega) 2)
      have c1b : swapMapK * (200 * M ^ 3) ^ 2 = 40000 * swapMapK * M ^ 6 := by ring
      -- step 2
      have c2a : 8000 * (q + 1) ^ 3 ≤ 8000 * M ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      -- the stabilizer call
      have bG : (encGroup (sw.map encPair)).wt ≤ 40 * M ^ 4 := by
        have := wt_encGroup_pairs_le sw
        rw [hsw', pM_swap] at this
        exact this
      have bGX := wt_list2_le (encGroup (sw.map encPair)) (encPts (List.finRange q))
      have cS1 := prim_bound_le_wt (pointwiseStabPrim hst)
        (show (Val.list [encGroup (sw.map encPair), encPts (List.finRange q)]).wt ≤ 100 * M ^ 4 by
          have := pw 2 4 (by omega); omega)
      have cS2 : graphStabK * stabM q k sw (List.finRange q) ^ 8 ≤ graphStabK * (256 * M ^ 8) := by
        apply Nat.mul_le_mul_left
        calc stabM q k sw (List.finRange q) ^ 8 ≤ (2 * M) ^ 8 :=
              Nat.pow_le_pow_left (by simp only [stabM, hsw', List.length_map,
                List.length_finRange, hM, pM]; omega) 8
          _ = 256 * M ^ 8 := by ring
      -- the result of the call
      have hkl' : ks'.length ≤ M ^ 2 := hkl.trans (Nat.pow_le_pow_left (by omega) 2)
      have bks : (Val.list (ks'.map pairV)).wt ≤ 400 * M ^ 6 := by
        have h1 := wt_pairList_le ks'
        have h2 : pM q k ks' ≤ 2 * M ^ 2 := by
          unfold pM; have := Nat.le_self_pow (by norm_num : (2:ℕ) ≠ 0) M
          have : k + q + 2 ≤ M := by simp only [hM, pM]; omega
          omega
        have h3 := Nat.pow_le_pow_left h2 3
        have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
        omega
      have b4 := wt_list2_le (.nat 0) (.list (ks'.map pairV))
      have c4a : swapMapK * ((Val.list [.nat 0, .list (ks'.map pairV)]).wt + 1) ^ 2 ≤
          swapMapK * (1000 * M ^ 6) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := Nat.one_le_pow 6 M m1; omega) 2)
      have c4b : swapMapK * (1000 * M ^ 6) ^ 2 = 1000000 * swapMapK * M ^ 12 := by ring
      have bout : (Val.list ((ks'.map Prod.swap).map pairV)).wt ≤ 400 * M ^ 6 := by
        rw [wt_pairList_swap]; exact bks
      have b3 := wt_list3_le (.list [.nat q, .nat k]) (.list (sw.map pairV)) (encPts (List.finRange q))
      have hSTB' : STB ≤ (pointwiseStabPrim hst).c * (100 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k +
          graphStabK * (256 * M ^ 8) := by rw [hSTB]; omega
      rw [hC3] at hc1
      have p3 := pw 3 12 (by omega)
      have p6 := pw 6 12 (by omega)
      have p8 := pw 8 12 (by omega)
      have p2 := pw 2 12 (by omega)
      have p4 := pw 4 12 (by omega)
      have p1 : M ≤ M ^ 12 := Nat.le_self_pow (by norm_num) M
      have bq3 : (q + 2) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by simp only [hM, pM]; omega) 2
      have b4' := wt_list2_le (.nat 0) (.list (ks'.map pairV))
      clear d4 d1 d2 d3 d3c hstab gk gq hks' hb hentry hsw hrg hgs hj
      unfold rowKerCost
      generalize (pointwiseStabPrim hst).c * (100 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k = PB at *
      have e1 : swapMapK = 10000000 := rfl
      have e2 : graphStabK = 100000000000000 := rfl
      have e3 : rowKerK = 1000000000000000000 := rfl
      rw [e1] at c1a c1b c4a c4b hc hc1
      rw [e2] at hSTB'
      rw [e3]
      linarith

end GI.Impl
