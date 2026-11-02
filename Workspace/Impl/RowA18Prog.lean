import Workspace.Impl.RowKer
import Workspace.Impl.RowParts
import Workspace.Impl.RowTrans
import Workspace.Impl.RowOff
import Workspace.Impl.RowMain

/-!
# The groups of Theorem A.18 as a program

`a18Funs` runs on `[[n, q], pairs, rows, rl]`, where `pairs` are graph-form generators of `G`,
`rows` are the coordinates returned by the coordinate program (`coordsVal`, Theorem A.17) and
`rl` the row labels of the positions. It returns `[H, N, N*, t]`:

1. the label kernel `K = G ∩ ker π` in graph form (`rowKer_spec`, one **PointwiseStab** call);
2. `K ∩ Fix(row 1)` (`graphStabL_spec`, one **PointwiseStab** call);
3. the positions of the domain outside row `0` (`offList_spec`) and `G ∩ Fix(those)`
   (`graphStabL_spec`, one **PointwiseStab** call);
4. the row-`0` parts of the three generator lists (`partsMap_spec`): generators of `H`, `N` and
   `N*` (`Hb_gens`, `Nb_gens`, `Nstar_gens`);
5. the case number `t`: `t = 0` exactly when `N` is transitive on the row (`trans_spec`,
   `transitive_iff`).

`a18_spec` states the result for `RowForm.ofPure`. The cost is polynomial in
`M = n + q + |pairs| + 2`, given the bound of the cited **PointwiseStab** task.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup encPts gens PointwiseStab)

/-- `[n, q]` from the input. -/
def a18NQ : Expr := arg 0

/-- The positions of row `0`, from the input. -/
def a18Z : Expr := .get (arg 2) (.nat 0)

/-- **The A.18 program** at `b`. -/
def a18F (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 (arg 0) (arg 1)))
  (.letE (.call (b + 42) (mk3 (arg 0) (.var 1) (.get (arg 2) (.nat 1))))
  (.letE (.call (b + 75) (mk2 (mk2 (arg 3) (.get (arg 0) (.nat 1)))
      (.call (b + 79) (.get (arg 0) (.nat 0)))))
  (.letE (.call (b + 42) (mk3 (arg 0) (arg 1) (.var 3)))
  (.letE (.call (b + 82) (mk2 a18Z (.var 2)))
  (.letE (.call (b + 97) (mk2 (.length a18Z) (.var 5)))
  (mk4 (.call (b + 82) (mk2 a18Z (.var 1))) (.var 5) (.call (b + 82) (mk2 a18Z (.var 4)))
    (.var 6)))))))

/-- The A.18 module at `b` (135 functions), with **PointwiseStab** at `jp`. -/
def a18Funs (b jp : ℕ) : List Expr :=
  [a18F b] ++ rowKerFuns (b + 1) jp ++ graphStabFuns (b + 42) jp ++
    (filterFuns (b + 75) (b + 78) ++ [offTestF]) ++ rangeFuns (b + 79) ++ partsMapFuns (b + 82) ++
    transFuns (b + 97)

/-- The cost constant of the A.18 program. -/
def a18K : ℕ := 10 ^ 22

/-- The cost bound of the A.18 program, with `M = n + q + |pairs| + 2`. -/
noncomputable def a18Cost (hst : PointwiseStab) (M : ℕ) : ℕ :=
  rowKerCost hst M + 2 * ((pointwiseStabPrim hst).c * (2000 * M ^ 8 + 2) ^ (pointwiseStabPrim hst).k)
    + a18K * M ^ 16

section Spec

variable {Ω C : Type} {n : ℕ} {e : Ω ≃ Fin n} {S : State Ω C} {L : GiantLabels S}
  {label : Ω → Fin L.q} {m : ℕ}

theorem a18_layout {P : Program} {b jp : ℕ} (h : P.HasAt b (a18Funs b jp)) :
    P.funs[b]? = some (a18F b) ∧ P.HasAt (b + 1) (rowKerFuns (b + 1) jp) ∧
      P.HasAt (b + 42) (graphStabFuns (b + 42) jp) ∧
      P.HasAt (b + 75) (filterFuns (b + 75) (b + 78)) ∧ P.funs[b + 78]? = some offTestF ∧
      P.HasAt (b + 79) (rangeFuns (b + 79)) ∧ P.HasAt (b + 82) (partsMapFuns (b + 82)) ∧
      P.HasAt (b + 97) (transFuns (b + 97)) := by
  unfold a18Funs at h
  have h6 := h.left
  have h5 := h6.left
  have h4 := h5.left
  have h3 := h4.left
  have h2 := h3.left
  have h1 := h2.left
  refine ⟨by simpa using h1.single, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h2.right
  · have := h3.right; simpa [show (rowKerFuns (b + 1) jp).length = 41 from rfl, Nat.add_assoc] using this
  · have := h4.right.left
    simpa [show (rowKerFuns (b + 1) jp).length = 41 from rfl, show (graphStabFuns (b + 42) jp).length = 33 from rfl, Nat.add_assoc] using this
  · have := h4.right.right
    simpa [show (rowKerFuns (b + 1) jp).length = 41 from rfl, show (graphStabFuns (b + 42) jp).length = 33 from rfl, show (filterFuns (b + 75) (b + 78)).length = 3 from rfl, Nat.add_assoc] using this.single
  · have := h5.right
    simpa [show (rowKerFuns (b + 1) jp).length = 41 from rfl, show (graphStabFuns (b + 42) jp).length = 33 from rfl, show (filterFuns (b + 75) (b + 78)).length = 3 from rfl, Nat.add_assoc] using this
  · have := h6.right
    simpa [show (rowKerFuns (b + 1) jp).length = 41 from rfl, show (graphStabFuns (b + 42) jp).length = 33 from rfl, show (filterFuns (b + 75) (b + 78)).length = 3 from rfl, show (rangeFuns (b + 79)).length = 3 from rfl, Nat.add_assoc] using this
  · have := h.right
    simpa [show (rowKerFuns (b + 1) jp).length = 41 from rfl, show (graphStabFuns (b + 42) jp).length = 33 from rfl, show (filterFuns (b + 75) (b + 78)).length = 3 from rfl, show (rangeFuns (b + 79)).length = 3 from rfl, show (partsMapFuns (b + 82)).length = 15 from rfl, Nat.add_assoc] using this

/-! ### The input -/

/-- The input of the A.18 program. -/
def a18In (n q : ℕ) (ps : List (Perm (Fin n) × Perm (Fin q))) (rows : Val) (rl : List ℕ) : Val :=
  .list [.list [.nat n, .nat q], .list (ps.map pairV), rows, natList rl]

theorem coordsVal_eq (E : Fin m × Fin L.q ≃ S.dom) :
    coordsVal e S E = .list ((List.finRange L.q).map fun j =>
      natList ((rowList e E j).map Fin.val)) := by
  unfold coordsVal rowList
  simp [List.map_map, Function.comp_def]

theorem coordsVal_get (E : Fin m × Fin L.q ≃ S.dom) (j : Fin L.q) :
    ((List.finRange L.q).map fun j => natList ((rowList e E j).map Fin.val))[(j : ℕ)]? =
      some (natList ((rowList e E j).map Fin.val)) := by
  simp

theorem natList_rowList (E : Fin m × Fin L.q ≃ S.dom) (j : Fin L.q) :
    natList ((rowList e E j).map Fin.val) = encPts (rowList e E j) := by
  rw [encPts_eq]; simp [natList, List.map_map, Function.comp_def]

theorem rowList_nodup (E : Fin m × Fin L.q ≃ S.dom) (j : Fin L.q) : (rowList e E j).Nodup := by
  refine (List.nodup_finRange m).map ?_
  intro a b h
  have := E.injective (Subtype.ext (e.injective h))
  exact congrArg Prod.fst this

theorem m_le_n (e : Ω ≃ Fin n) (E : Fin m × Fin L.q ≃ S.dom) (j : Fin L.q) : m ≤ n := by
  have := (rowList_nodup (e := e) E j).length_le_card
  rwa [rowList_length, Fintype.card_fin] at this

theorem zsOK_row (E : Fin m × Fin L.q ≃ S.dom) (j : Fin L.q) :
    ZsOK n ((rowList e E j).map Fin.val) :=
  ⟨fun z hz => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; exact i.2,
    by rw [List.length_map, rowList_length]; exact m_le_n e E j⟩

theorem wt_coordsVal_le (E : Fin m × Fin L.q ≃ S.dom) :
    (coordsVal e S E).wt ≤ 15 * (n + L.q + 2) ^ 3 + 4 := by
  rw [coordsVal_eq]
  have h1 : ∀ j : Fin L.q, (natList ((rowList e E j).map Fin.val)).wt ≤ 7 * (n + L.q + 2) ^ 2 := by
    intro j
    have := wt_zs_le (zsOK_row (e := e) E j)
    have := Nat.pow_le_pow_left (show n + 1 ≤ n + L.q + 2 by omega) 2
    omega
  have h2 := wt_list_map_le (List.finRange L.q) (fun j => natList ((rowList e E j).map Fin.val))
    (W := 7 * (n + L.q + 2) ^ 2) fun j _ => h1 j
  rw [List.length_finRange] at h2
  have h3 : L.q * (2 * (7 * (n + L.q + 2) ^ 2) + 1) ≤ (n + L.q + 2) * (15 * (n + L.q + 2) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (n + L.q + 2) (by omega); omega)
  have h4 : (n + L.q + 2) * (15 * (n + L.q + 2) ^ 2) = 15 * (n + L.q + 2) ^ 3 := by ring
  omega

theorem wt_a18In_le (E : Fin m × Fin L.q ≃ S.dom) (ps : List (Perm (Fin n) × Perm (Fin L.q)))
    {rl : List ℕ} (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q) :
    (a18In n L.q ps (coordsVal e S E) rl).wt ≤ 300 * pM n L.q ps ^ 3 := by
  set M := pM n L.q ps with hM
  have hM2 : n + L.q + 2 ≤ M := by rw [hM]; unfold pM; omega
  have w1 := wt_coordsVal_le (e := e) E
  have w2 := Nat.pow_le_pow_left hM2 3
  have w3 := wt_pairs_le_of_len (ps := ps) (le_refl _)
  rw [← hM] at w3
  have w4 := wt_natList_le hrl
  rw [hl] at w4
  have w5 : n * (2 * L.q + 5) ≤ M * (3 * M) := Nat.mul_le_mul (by omega) (by omega)
  have w6 := wt_list2_le (.nat n) (.nat L.q)
  have w7 := wt_nat_le n
  have w8 := wt_nat_le L.q
  have w9 := wt_list4_le (.list [.nat n, .nat L.q]) (.list (ps.map pairV)) (coordsVal e S E)
    (natList rl)
  have m1 : 1 ≤ M := by omega
  have m2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right m1 (by omega)
  have e1 : M * (3 * M) = 3 * M ^ 2 := by ring
  unfold a18In
  omega

/-! ### The steps -/

/-- The bound of a stabilizer call on at most `2 M²` pairs. -/
noncomputable def stabPB (hst : PointwiseStab) (M : ℕ) : ℕ :=
  (pointwiseStabPrim hst).c * (2000 * M ^ 8 + 2) ^ (pointwiseStabPrim hst).k

variable (hst : PointwiseStab) {P : Program} {b jp : ℕ} (E : Fin m × Fin L.q ≃ S.dom)
  {ps : List (Perm (Fin n) × Perm (Fin L.q))} {rl : List ℕ}

/-- Reading entry `i` of the input. -/
theorem a18_arg (rest : List Val) {i : ℕ} {v : Val}
    (hv : [Val.list [.nat n, .nat L.q], .list (ps.map pairV), coordsVal e S E, natList rl][i]? =
      some v) :
    Det P (a18In n L.q ps (coordsVal e S E) rl :: rest) (arg i) v
      (2 * (a18In n L.q ps (coordsVal e S E) rl).wt + 10) := by
  have hi : i < 4 := by
    by_contra h
    rw [List.getElem?_eq_none (by simp; omega)] at hv
    exact absurd hv (by simp)
  exact (Det.arg' hv).mono (by unfold a18In; omega)

theorem wt_pairs_sq_le {ks : List (Perm (Fin n) × Perm (Fin L.q))} {M : ℕ}
    (hM : n + L.q + 2 ≤ M) (hk : ks.length ≤ (n + L.q) ^ 2) :
    (Val.list (ks.map pairV)).wt ≤ 400 * M ^ 6 ∧ pM n L.q ks ≤ 2 * M ^ 2 := by
  have h1 : pM n L.q ks ≤ 2 * M ^ 2 := by
    unfold pM
    have := Nat.pow_le_pow_left (show n + L.q ≤ M by omega) 2
    have := Nat.le_self_pow (by norm_num : (2:ℕ) ≠ 0) M
    omega
  refine ⟨?_, h1⟩
  have h2 := wt_pairList_le ks
  have h3 := Nat.pow_le_pow_left h1 3
  have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
  omega

set_option maxHeartbeats 800000 in
/-- **Step 1**: the label kernel. -/
theorem a18_step1 (hb : P.HasAt (b + 1) (rowKerFuns (b + 1) jp))
    (hj : P.prims[jp]? = some (pointwiseStabPrim hst)) (hps : PairGens e L S.G ps)
    (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q) :
    EvalAll P [a18In n L.q ps (coordsVal e S E) rl] (.call (b + 1) (mk2 (arg 0) (arg 1)))
      (fun w c => ∃ ks : List (Perm (Fin n) × Perm (Fin L.q)), w = .list (ks.map pairV) ∧
        ks.length ≤ (n + L.q) ^ 2 ∧ PairGens e L (kerG S L) ks ∧
        c ≤ rowKerCost hst (pM n L.q ps) + 10000 * pM n L.q ps ^ 6) := by
  have d := Det.mk2 (a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E [] (i := 0) rfl)
    (a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E [] (i := 1) rfl)
  refine EvalAll.call_funAll d fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (rowKer_spec hst hb hj ps).mono fun w c hw => ?_
  obtain ⟨ks, rfl, hkl, hks, hc⟩ := hw
  refine ⟨ks, rfl, hkl, pairGens_of_pre hps hks, ?_⟩
  have hM2 : n + L.q + 2 ≤ pM n L.q ps := by unfold pM; omega
  have hwA := wt_a18In_le (e := e) E ps hl hrl
  obtain ⟨wk, -⟩ := wt_pairs_sq_le hM2 hkl
  have w2 := wt_list2_le (.list [.nat n, .nat L.q]) (.list (ps.map pairV))
  have w3 : (Val.list [.nat n, .nat L.q]).wt < (a18In n L.q ps (coordsVal e S E) rl).wt :=
    wt_le_wt_list (by simp)
  have w4 : (Val.list (ps.map pairV)).wt < (a18In n L.q ps (coordsVal e S E) rl).wt :=
    wt_le_wt_list (by simp)
  generalize (a18In n L.q ps (coordsVal e S E) rl).wt = A at hca hwA w3 w4
  generalize pM n L.q ps = M at hM2 hwA wk hc ⊢
  have m1 : 1 ≤ M := by omega
  have m36 : M ^ 3 ≤ M ^ 6 := Nat.pow_le_pow_right m1 (by omega)
  omega

set_option maxHeartbeats 800000 in
/-- **Step 2**: `N` before projection: the part of the kernel that fixes row `1`. -/
theorem a18_step2 (hb : P.HasAt (b + 42) (graphStabFuns (b + 42) jp))
    (hj : P.prims[jp]? = some (pointwiseStabPrim hst)) (hq : 2 ≤ L.q)
    (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q)
    {ks : List (Perm (Fin n) × Perm (Fin L.q))} (hkl : ks.length ≤ (n + L.q) ^ 2)
    (hks : PairGens e L (kerG S L) ks) :
    EvalAll P [a18In n L.q ps (coordsVal e S E) rl, .list (ks.map pairV)]
      (.call (b + 42) (mk3 (arg 0) (.var 1) (.get (arg 2) (.nat 1))))
      (fun w c => ∃ ns : List (Perm (Fin n) × Perm (Fin L.q)), w = .list (ns.map pairV) ∧
        ns.length ≤ (n + L.q) ^ 2 ∧
        PairGens e L (kerG S L ⊓ fixPos (e := e) (rowList e E ⟨1, by omega⟩)) ns ∧
        c ≤ stabPB hst (pM n L.q ps) + 10 ^ 18 * pM n L.q ps ^ 16) := by
  have d2 := a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E [.list (ks.map pairV)] (i := 2)
    (v := .list ((List.finRange L.q).map fun j => natList ((rowList e E j).map Fin.val)))
    (by rw [coordsVal_eq]; rfl)
  have dr := Det.get' d2 (Det.nat 1) (coordsVal_get E ⟨1, by omega⟩)
  rw [natList_rowList (e := e) E ⟨1, by omega⟩] at dr
  have d := Det.mk3 (a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E [.list (ks.map pairV)]
    (i := 0) rfl)
    (Det.var' (P := P) (env := [a18In n L.q ps (coordsVal e S E) rl, .list (ks.map pairV)])
      (i := 1) rfl) dr
  refine EvalAll.call_funAll d fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (graphStabL_spec hst hb hj ks (rowList e E ⟨1, by omega⟩)).mono fun w c hw => ?_
  obtain ⟨ns, rfl, hnl, hns, hc⟩ := hw
  refine ⟨ns, rfl, hnl, pairGens_of_stab hks hns, ?_⟩
  -- the cost
  have hM2 : n + L.q + 2 ≤ pM n L.q ps := by unfold pM; omega
  have hwA := wt_a18In_le (e := e) E ps hl hrl
  obtain ⟨wk, pk⟩ := wt_pairs_sq_le hM2 hkl
  obtain ⟨wn, -⟩ := wt_pairs_sq_le hM2 hnl
  have hrow := rowList_length (e := e) E ⟨1, by omega⟩
  have hmn := m_le_n e E ⟨0, by omega⟩
  have wX : (encPts (rowList e E ⟨1, by omega⟩)).wt ≤ 3 * (n + 2) ^ 2 + 4 :=
    wt_encPts_le' (by rw [hrow]; exact hmn)
  have hS : stabM n L.q ks (rowList e E ⟨1, by omega⟩) ≤ 3 * pM n L.q ps ^ 2 := by
    have := Nat.le_self_pow (by norm_num : (2:ℕ) ≠ 0) (pM n L.q ps)
    have : pM n L.q ks = n + L.q + ks.length + 2 := rfl
    unfold stabM; rw [hrow]; omega
  have wG := wt_encGroup_pairs_le ks
  have wGX := wt_list2_le (encGroup (ks.map encPair)) (encPts (rowList e E ⟨1, by omega⟩))
  have w3 := wt_list3_le (.list [.nat n, .nat L.q]) (.list (ks.map pairV))
    (encPts (rowList e E ⟨1, by omega⟩))
  have w5 : (Val.list [.nat n, .nat L.q]).wt < (a18In n L.q ps (coordsVal e S E) rl).wt :=
    wt_le_wt_list (by simp)
  have hle : (pointwiseStabPrim hst).bound
      (.list [encGroup (ks.map encPair), encPts (rowList e E ⟨1, by omega⟩)]) ≤
      stabPB hst (pM n L.q ps) := by
    refine prim_bound_le_wt (pointwiseStabPrim hst) (W := 2000 * pM n L.q ps ^ 8) ?_
    generalize pM n L.q ps = M at hM2 pk ⊢
    have m1 : 1 ≤ M := by omega
    have h2 := Nat.pow_le_pow_left pk 4
    have e : (2 * M ^ 2) ^ 4 = 16 * M ^ 8 := by ring
    have := Nat.pow_le_pow_left (show n + 2 ≤ M by omega) 2
    have := Nat.one_le_pow 2 M m1
    have m28 : M ^ 2 ≤ M ^ 8 := Nat.pow_le_pow_right m1 (by omega)
    omega
  have hS8 := Nat.pow_le_pow_left hS 8
  generalize (pointwiseStabPrim hst).bound
    (.list [encGroup (ks.map encPair), encPts (rowList e E ⟨1, by omega⟩)]) = B at hc hle
  generalize (a18In n L.q ps (coordsVal e S E) rl).wt = A at hca hwA w5
  generalize stabM n L.q ks (rowList e E ⟨1, by omega⟩) = SM at hc hS8
  generalize stabPB hst (pM n L.q ps) = PB at hle ⊢
  generalize pM n L.q ps = M at *
  have m1 : 1 ≤ M := by omega
  have e2 : (3 * M ^ 2) ^ 8 = 6561 * M ^ 16 := by ring
  have := Nat.pow_le_pow_left (show n + 2 ≤ M by omega) 2
  have m36 : M ^ 3 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
  have m616 : M ^ 6 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
  have m216 : M ^ 2 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
  have e1 : graphStabK = 100000000000000 := rfl
  rw [e1] at hc
  norm_num
  omega

set_option maxHeartbeats 800000 in
/-- **Step 3**: the positions of the domain outside row `0`. -/
theorem a18_step3 (rest : List Val) (hb : P.HasAt (b + 75) (filterFuns (b + 75) (b + 78)))
    (hf : P.funs[b + 78]? = some offTestF) (hr : P.HasAt (b + 79) (rangeFuns (b + 79)))
    (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q) :
    Det P (a18In n L.q ps (coordsVal e S E) rl :: rest)
      (.call (b + 75) (mk2 (mk2 (arg 3) (.get (arg 0) (.nat 1)))
        (.call (b + 79) (.get (arg 0) (.nat 0)))))
      (encPts (offPts n rl L.q)) (10 ^ 12 * pM n L.q ps ^ 6) := by
  have d0 := a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E rest (i := 0) rfl
  have d3 := a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E rest (i := 3) rfl
  have dq := Det.get' d0 (Det.nat 1) (vs := [.nat n, .nat L.q]) (v := .nat L.q) rfl
  have dn := Det.get' d0 (Det.nat 0) (vs := [.nat n, .nat L.q]) (v := .nat n) rfl
  have dR := Det.call dn (range_det hr n)
  rw [← range_eq_encPerm_one] at dR
  have d := Det.call (Det.mk2 (Det.mk2 d3 dq) dR) (offList_spec hb hf rl hl hrl)
  refine d.mono ?_
  -- the cost
  have hwA := wt_a18In_le (e := e) E ps hl hrl
  have hM2 : n + L.q + 2 ≤ pM n L.q ps := by unfold pM; omega
  have w1 := wt_natList_le hrl
  rw [hl] at w1
  have w2 : (natList (List.range n)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => (List.mem_range.1 hx).le) (by simp)
  have w3 := wt_list2_le (natList rl) (.nat L.q)
  have w4 := wt_list2_le (Val.list [natList rl, .nat L.q]) (natList (List.range n))
  have w5 := wt_nat_le L.q
  have w6 := wt_nat_le n
  have hX : (encPts (offPts n rl L.q)).wt ≤ 3 * (n + 2) ^ 2 + 4 := wt_encPts_le' (by
    unfold offPts
    exact (List.length_filter_le _ _).trans (by simp))
  have hrlA : (natList rl).wt < (a18In n L.q ps (coordsVal e S E) rl).wt :=
    wt_le_wt_list (by simp)
  generalize (a18In n L.q ps (coordsVal e S E) rl).wt = A at hwA hrlA ⊢
  generalize (natList rl).wt = R at w1 w3 hrlA ⊢
  generalize (Val.list [natList rl, .nat L.q]).wt = R2 at w3 w4 ⊢
  generalize (natList (List.range n)).wt = RN at w2 w4 ⊢
  generalize (Val.list [Val.list [natList rl, .nat L.q], natList (List.range n)]).wt = I at w4 ⊢
  generalize pM n L.q ps = M at hwA hM2 ⊢
  have m1 : 1 ≤ M := by omega
  have p1 := Nat.pow_le_pow_left (show n + 2 ≤ M by omega) 2
  have p2 := Nat.pow_le_pow_left (show n + 1 ≤ M by omega) 2
  have p3 := Nat.pow_le_pow_left (show n + 1 ≤ M by omega) 3
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right m1 (by omega)
  have m36 : M ^ 3 ≤ M ^ 6 := Nat.pow_le_pow_right m1 (by omega)
  have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have hI : I + L.q + 1 ≤ 2000 * M ^ 3 := by omega
  have hI2 : (I + L.q + 1) ^ 2 ≤ (2000 * M ^ 3) ^ 2 := Nat.pow_le_pow_left hI 2
  have e1 : (2000 * M ^ 3) ^ 2 = 4000000 * M ^ 6 := by ring
  have e2 : offFK = 10000 := rfl
  rw [e2]
  norm_num
  omega

set_option maxHeartbeats 800000 in
/-- **Step 4**: `N*` before projection: the elements of `G` that fix the positions `X`. -/
theorem a18_step4 (v1 v2 : Val) (hb : P.HasAt (b + 42) (graphStabFuns (b + 42) jp))
    (hj : P.prims[jp]? = some (pointwiseStabPrim hst)) (hps : PairGens e L S.G ps)
    (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q) (X : List (Fin n)) (hX : X.length ≤ n) :
    EvalAll P [a18In n L.q ps (coordsVal e S E) rl, v1, v2, encPts X]
      (.call (b + 42) (mk3 (arg 0) (arg 1) (.var 3)))
      (fun w c => ∃ ss : List (Perm (Fin n) × Perm (Fin L.q)), w = .list (ss.map pairV) ∧
        ss.length ≤ (n + L.q) ^ 2 ∧ PairGens e L (S.G ⊓ fixPos (e := e) X) ss ∧
        c ≤ stabPB hst (pM n L.q ps) + 10 ^ 18 * pM n L.q ps ^ 16) := by
  have d := Det.mk3 (a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E [v1, v2, encPts X]
      (i := 0) rfl)
    (a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E [v1, v2, encPts X] (i := 1) rfl)
    (Det.var' (P := P) (env := [a18In n L.q ps (coordsVal e S E) rl, v1, v2, encPts X])
      (i := 3) rfl)
  refine EvalAll.call_funAll d fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (graphStabL_spec hst hb hj ps X).mono fun w c hw => ?_
  obtain ⟨ss, rfl, hsl, hss, hc⟩ := hw
  refine ⟨ss, rfl, hsl, pairGens_of_stab hps hss, ?_⟩
  -- the cost
  have hM2 : n + L.q + 2 ≤ pM n L.q ps := by unfold pM; omega
  have hwA := wt_a18In_le (e := e) E ps hl hrl
  obtain ⟨ws, -⟩ := wt_pairs_sq_le hM2 hsl
  have wX : (encPts X).wt ≤ 3 * (n + 2) ^ 2 + 4 := wt_encPts_le' hX
  have hS : stabM n L.q ps X ≤ 2 * pM n L.q ps := by
    have : pM n L.q ps = n + L.q + ps.length + 2 := rfl
    unfold stabM; omega
  have wG := wt_encGroup_pairs_le ps
  have wGX := wt_list2_le (encGroup (ps.map encPair)) (encPts X)
  have w3 := wt_list3_le (.list [.nat n, .nat L.q]) (.list (ps.map pairV)) (encPts X)
  have w5 : (Val.list [.nat n, .nat L.q]).wt < (a18In n L.q ps (coordsVal e S E) rl).wt :=
    wt_le_wt_list (by simp)
  have w6 : (Val.list (ps.map pairV)).wt < (a18In n L.q ps (coordsVal e S E) rl).wt :=
    wt_le_wt_list (by simp)
  have hle : (pointwiseStabPrim hst).bound (.list [encGroup (ps.map encPair), encPts X]) ≤
      stabPB hst (pM n L.q ps) := by
    refine prim_bound_le_wt (pointwiseStabPrim hst) (W := 2000 * pM n L.q ps ^ 8) ?_
    generalize pM n L.q ps = M at hM2 wG ⊢
    have m1 : 1 ≤ M := by omega
    have := Nat.pow_le_pow_left (show n + 2 ≤ M by omega) 2
    have := Nat.one_le_pow 2 M m1
    have m28 : M ^ 2 ≤ M ^ 8 := Nat.pow_le_pow_right m1 (by omega)
    have m48 : M ^ 4 ≤ M ^ 8 := Nat.pow_le_pow_right m1 (by omega)
    omega
  have hS8 := Nat.pow_le_pow_left hS 8
  generalize (pointwiseStabPrim hst).bound (.list [encGroup (ps.map encPair), encPts X]) = B
    at hc hle
  generalize (a18In n L.q ps (coordsVal e S E) rl).wt = A at hca hwA w5 w6
  generalize stabM n L.q ps X = SM at hc hS8
  generalize stabPB hst (pM n L.q ps) = PB at hle ⊢
  generalize pM n L.q ps = M at *
  have m1 : 1 ≤ M := by omega
  have e2 : (2 * M) ^ 8 = 256 * M ^ 8 := by ring
  have := Nat.pow_le_pow_left (show n + 2 ≤ M by omega) 2
  have m36 : M ^ 3 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
  have m616 : M ^ 6 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
  have m816 : M ^ 8 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
  have m216 : M ^ 2 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
  have e1 : graphStabK = 100000000000000 := rfl
  rw [e1] at hc
  norm_num
  omega

/-- The positions of row `0`, as numbers. -/
def zs0 (e : Ω ≃ Fin n) (E : Fin m × Fin L.q ≃ S.dom) (hq : 1 ≤ L.q) : List ℕ :=
  (rowList e E ⟨0, hq⟩).map Fin.val

set_option maxHeartbeats 800000 in
/-- **Steps 5–7**: the row-`0` parts of graph-form generators. -/
theorem a18_parts (hpm : P.HasAt (b + 82) (partsMapFuns (b + 82))) (hq : 1 ≤ L.q)
    (rest : List Val) {i : ℕ} {qs : List (Perm (Fin n) × Perm (Fin L.q))}
    (hv : (a18In n L.q ps (coordsVal e S E) rl :: rest)[i]? = some (.list (qs.map pairV)))
    (hqs : qs.length ≤ (n + L.q) ^ 2) (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q) :
    Det P (a18In n L.q ps (coordsVal e S E) rl :: rest) (.call (b + 82) (mk2 a18Z (.var i)))
      (.list (qs.map fun p => natList (partNat (zs0 e E hq) p.1)))
      (10 ^ 15 * pM n L.q ps ^ 14) := by
  have d2 := a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E rest (i := 2)
    (v := .list ((List.finRange L.q).map fun j => natList ((rowList e E j).map Fin.val)))
    (by rw [coordsVal_eq]; rfl)
  have dz := Det.get' d2 (Det.nat 0) (coordsVal_get E ⟨0, hq⟩)
  have d := Det.call (Det.mk2 dz (Det.var' hv)) (partsMap_spec hpm (zsOK_row E ⟨0, hq⟩) qs)
  refine d.mono ?_
  -- the cost
  have hM2 : n + L.q + 2 ≤ pM n L.q ps := by unfold pM; omega
  have hwA := wt_a18In_le (e := e) E ps hl hrl
  obtain ⟨wq, pq⟩ := wt_pairs_sq_le hM2 hqs
  have hz := wt_zs_le (zsOK_row (e := e) E ⟨0, hq⟩)
  have hout : (Val.list (qs.map fun p => natList (partNat (zs0 e E hq) p.1))).wt ≤
      (2 * pM n L.q ps ^ 2) * (14 * (n + 1) ^ 2 + 1) + 4 := by
    have h1 := wt_list_map_le qs (fun p => natList (partNat (zs0 e E hq) p.1))
      (W := 7 * (n + 1) ^ 2) fun p _ => wt_partNat_le _ (by
        unfold zs0; rw [List.length_map, rowList_length]; exact m_le_n e E ⟨0, hq⟩) p.1
    have : pM n L.q qs = n + L.q + qs.length + 2 := rfl
    have h2 : qs.length * (2 * (7 * (n + 1) ^ 2) + 1) ≤
        (2 * pM n L.q ps ^ 2) * (14 * (n + 1) ^ 2 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have w2 := wt_list2_le (natList ((rowList e E ⟨0, hq⟩).map Fin.val)) (.list (qs.map pairV))
  have hP7 := Nat.pow_le_pow_left pq 7
  have ez : zs0 e E hq = (rowList e E ⟨0, hq⟩).map Fin.val := rfl
  rw [ez] at hout
  generalize (Val.list (qs.map fun p => natList (partNat ((rowList e E ⟨0, hq⟩).map Fin.val) p.1))).wt
    = O at hout ⊢
  generalize (a18In n L.q ps (coordsVal e S E) rl).wt = A at hwA ⊢
  generalize pM n L.q qs = Q at hP7 ⊢
  generalize pM n L.q ps = M at *
  have m1 : 1 ≤ M := by omega
  have := Nat.pow_le_pow_left (show n + 1 ≤ M by omega) 2
  have e2 : (2 * M ^ 2) ^ 7 = 128 * M ^ 14 := by ring
  have h4 : (2 * M ^ 2) * (14 * (n + 1) ^ 2 + 1) ≤ (2 * M ^ 2) * (15 * M ^ 2) :=
    Nat.mul_le_mul_left _ (by have := Nat.one_le_pow 2 M m1; omega)
  have e4 : (2 * M ^ 2) * (15 * M ^ 2) = 30 * M ^ 4 := by ring
  have m3 : M ^ 3 ≤ M ^ 14 := Nat.pow_le_pow_right m1 (by omega)
  have m4 : M ^ 4 ≤ M ^ 14 := Nat.pow_le_pow_right m1 (by omega)
  have m6 : M ^ 6 ≤ M ^ 14 := Nat.pow_le_pow_right m1 (by omega)
  have m2 : M ^ 2 ≤ M ^ 14 := Nat.pow_le_pow_right m1 (by omega)
  have m0 := Nat.one_le_pow 14 M m1
  have e1 : partsK = 1000000000000 := rfl
  rw [e1]
  norm_num
  omega

set_option maxHeartbeats 800000 in
/-- **Step 8**: the transitivity test on the generators of `N`. -/
theorem a18_trans (ht : P.HasAt (b + 97) (transFuns (b + 97))) (hq : 1 ≤ L.q)
    (rest : List Val) {σs : List (Perm (Fin m))} (hσ : σs.length ≤ (n + L.q) ^ 2)
    (hv : (a18In n L.q ps (coordsVal e S E) rl :: rest)[5]? = some (.list (σs.map encPerm)))
    (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q) :
    EvalAll P (a18In n L.q ps (coordsVal e S E) rl :: rest)
      (.call (b + 97) (mk2 (.length a18Z) (.var 5)))
      (fun w c => ∃ t : ℕ, w = .nat t ∧ (t = 0 ↔ ∀ x y : Fin m, y ∈ genOrbit σs x) ∧ t ≤ m ∧
        c ≤ 10 ^ 10 * pM n L.q ps ^ 15) := by
  have d2 := a18_arg (P := P) (e := e) (ps := ps) (rl := rl) E rest (i := 2)
    (v := .list ((List.finRange L.q).map fun j => natList ((rowList e E j).map Fin.val)))
    (by rw [coordsVal_eq]; rfl)
  have dz := Det.get' d2 (Det.nat 0) (coordsVal_get E ⟨0, hq⟩)
  have hzl : natList ((rowList e E ⟨0, hq⟩).map Fin.val) =
      .list (((rowList e E ⟨0, hq⟩).map Fin.val).map Val.nat) := rfl
  rw [hzl] at dz
  have dlen := Det.length dz
  rw [List.length_map, List.length_map, rowList_length] at dlen
  have d := Det.mk2 dlen (Det.var' hv)
  refine EvalAll.call_funAll d fun v ca hv' => ?_
  obtain ⟨rfl, hca⟩ := hv'
  refine (trans_spec ht σs).mono fun w c hw => ?_
  obtain ⟨t, rfl, ht', htm, hc⟩ := hw
  refine ⟨t, rfl, ht', htm, ?_⟩
  -- the cost
  have hM2 : n + L.q + 2 ≤ pM n L.q ps := by unfold pM; omega
  have hwA := wt_a18In_le (e := e) E ps hl hrl
  have hmn := m_le_n e E ⟨0, hq⟩
  have hz := wt_zs_le (zsOK_row (e := e) E ⟨0, hq⟩)
  have hzz : (Val.list (((rowList e E ⟨0, hq⟩).map Fin.val).map Val.nat)).wt =
      (natList ((rowList e E ⟨0, hq⟩).map Fin.val)).wt := rfl
  have hsw : (Val.list (σs.map encPerm)).wt ≤ 13 * ((σs.length + 1) * (m + 1)) ^ 2 :=
    wt_list_encPerms_le σs
  have w2 := wt_list2_le (.nat m) (.list (σs.map encPerm))
  have wt := wt_nat_le t
  have wm := wt_nat_le m
  have hX : (σs.length + 1) * (m + 1) ≤ 2 * pM n L.q ps ^ 3 := by
    have h1 : σs.length + 1 ≤ 2 * pM n L.q ps ^ 2 := by
      have := Nat.pow_le_pow_left (show n + L.q ≤ pM n L.q ps by omega) 2
      have := Nat.one_le_pow 2 (pM n L.q ps) (by omega)
      omega
    calc (σs.length + 1) * (m + 1) ≤ (2 * pM n L.q ps ^ 2) * pM n L.q ps :=
          Nat.mul_le_mul h1 (by omega)
      _ = 2 * pM n L.q ps ^ 3 := by ring
  have hX5 := Nat.pow_le_pow_left hX 5
  have hX2 := Nat.pow_le_pow_left hX 2
  generalize (a18In n L.q ps (coordsVal e S E) rl).wt = A at hca hwA
  generalize (Val.list (σs.map encPerm)).wt = W at hsw w2 hca
  generalize (σs.length + 1) * (m + 1) = X at hsw hX hX5 hX2 hc
  generalize (natList ((rowList e E ⟨0, hq⟩).map Fin.val)).wt = Z at hz hzz
  generalize pM n L.q ps = M at *
  have m1 : 1 ≤ M := by omega
  have e5 : (2 * M ^ 3) ^ 5 = 32 * M ^ 15 := by ring
  have e2 : (2 * M ^ 3) ^ 2 = 4 * M ^ 6 := by ring
  have := Nat.pow_le_pow_left (show n + 1 ≤ M by omega) 2
  have m3 : M ^ 3 ≤ M ^ 15 := Nat.pow_le_pow_right m1 (by omega)
  have m6 : M ^ 6 ≤ M ^ 15 := Nat.pow_le_pow_right m1 (by omega)
  have m2 : M ^ 2 ≤ M ^ 15 := Nat.pow_le_pow_right m1 (by omega)
  have m15 : M ≤ M ^ 15 := Nat.le_self_pow (by norm_num) M
  have e1 : transK = 10000000 := rfl
  rw [e1] at hc
  norm_num
  omega

/-! ### The whole program -/

/-- The output of the A.18 program: generators of `H`, `N`, `N*` and the case number. -/
def a18Out (σH σN σS : List (Perm (Fin m))) (t : ℕ) : Val :=
  .list [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm), .nat t]

theorem wt_a18Out_le {σH σN σS : List (Perm (Fin m))} {t M : ℕ} (hm : m + 1 ≤ M) (htm : t ≤ m)
    (h1 : σH.length + 1 ≤ 2 * M ^ 2) (h2 : σN.length + 1 ≤ 2 * M ^ 2)
    (h3 : σS.length + 1 ≤ 2 * M ^ 2) :
    (a18Out σH σN σS t).wt ≤ 400 * M ^ 6 + 20 := by
  have b : ∀ σs : List (Perm (Fin m)), σs.length + 1 ≤ 2 * M ^ 2 →
      (Val.list (σs.map encPerm)).wt ≤ 52 * M ^ 6 := by
    intro σs h
    have h1 := wt_list_encPerms_le σs
    have h2 : (σs.length + 1) * (m + 1) ≤ 2 * M ^ 3 := by
      calc (σs.length + 1) * (m + 1) ≤ (2 * M ^ 2) * M := Nat.mul_le_mul h hm
        _ = 2 * M ^ 3 := by ring
    have h3 := Nat.pow_le_pow_left h2 2
    have e : (2 * M ^ 3) ^ 2 = 4 * M ^ 6 := by ring
    omega
  have := wt_list4_le (.list (σH.map encPerm)) (.list (σN.map encPerm)) (.list (σS.map encPerm))
    (.nat t)
  have := wt_nat_le t
  have := b σH h1
  have := b σN h2
  have := b σS h3
  have : m ≤ M ^ 6 := by
    have := Nat.le_self_pow (by norm_num : (6:ℕ) ≠ 0) M
    omega
  unfold a18Out
  omega

variable (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) (hP : PureCoords S L label E) (b₀ : Fin m)

set_option maxHeartbeats 1600000 in
/-- **The A.18 program.** From graph-form generators of `G`, the coordinates of the row form
and the row labels, it returns generators of `H`, `N` and `N*` and a number `t` that is `0`
exactly when `N` is transitive on the row `B`. It uses three **PointwiseStab** calls. -/
theorem a18_spec (hA : P.HasAt b (a18Funs b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hps : PairGens e L S.G ps) (hrl : RowLabs e S label rl) :
    FunAll P b (a18In n L.q ps (coordsVal e S E) rl) (fun w c =>
      ∃ (σH σN σS : List (Perm (Fin m))) (t : ℕ), w = a18Out σH σN σS t ∧
        σH.length ≤ (n + L.q) ^ 2 ∧ σN.length ≤ (n + L.q) ^ 2 ∧ σS.length ≤ (n + L.q) ^ 2 ∧
        Subgroup.closure {σ | σ ∈ σH} = (RowForm.ofPure hnat hq E hP b₀).Hb ∧
        Subgroup.closure {σ | σ ∈ σN} = (RowForm.ofPure hnat hq E hP b₀).Nb ∧
        Subgroup.closure {σ | σ ∈ σS} = (RowForm.ofPure hnat hq E hP b₀).Nstar.map
          (RowForm.ofPure hnat hq E hP b₀).Hb.subtype ∧
        (t = 0 ↔ MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP b₀).Nl
          (RowForm.ofPure hnat hq E hP b₀).B) ∧
        c ≤ a18Cost hst (pM n L.q ps)) := by
  obtain ⟨hentry, hker, hstab, hfilt, hoff, hrange, hparts, htrans⟩ := a18_layout hA
  have hl : rl.length = n := hrl.1
  have hrq : ∀ r ∈ rl, r ≤ L.q := hrl.le
  have hq1 : 1 ≤ L.q := by omega
  set A := a18In n L.q ps (coordsVal e S E) rl with hAdef
  have hM2 : n + L.q + 2 ≤ pM n L.q ps := by unfold pM; omega
  refine FunAll.intro hentry ?_
  refine EvalAll.letE (a18_step1 (e := e) hst E (b := b) hker hj hps hl hrq) fun v1 c1 h1 => ?_
  obtain ⟨ks, rfl, hkl, hks, hc1⟩ := h1
  refine EvalAll.letE (a18_step2 (e := e) hst E (b := b) (ps := ps) hstab hj (by omega) hl hrq hkl hks)
    fun v2 c2 h2 => ?_
  obtain ⟨ns, rfl, hnl, hns, hc2⟩ := h2
  have d3 := a18_step3 (P := P) (e := e) (ps := ps) E (b := b) [.list (ks.map pairV),
    .list (ns.map pairV)] hfilt hoff hrange hl hrq
  refine EvalAll.letE d3 fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  have hXl : (offPts n rl L.q).length ≤ n := by
    unfold offPts; exact (List.length_filter_le _ _).trans (by simp)
  refine EvalAll.letE (a18_step4 (e := e) hst E (b := b) _ _ hstab hj hps hl hrq _ hXl)
    fun v4 c4 h4 => ?_
  obtain ⟨ss, rfl, hsl, hss, hc4⟩ := h4
  -- the generators
  obtain ⟨σH, eH, lH, cH⟩ := Hb_gens E hnat hq hP b₀ hks
  obtain ⟨σN, eN, lN, cN⟩ := Nb_gens E hnat hq hP b₀ hns
  obtain ⟨σS, eS, lS, cS⟩ := Nstar_gens E hnat hq hP b₀
    (X := offPts n rl L.q) (fun i => mem_offPts E hP.label_e hrl hq1 i) hss
  have d5 := a18_parts (P := P) (e := e) (ps := ps) E (b := b) hparts hq1
    [.list (ks.map pairV), .list (ns.map pairV), encPts (offPts n rl L.q), .list (ss.map pairV)]
    (i := 2) (qs := ns) rfl hnl hl hrq
  have eN' : Val.list (ns.map fun p => natList (partNat (zs0 e E hq1) p.1)) =
      .list (σN.map encPerm) := congrArg Val.list eN
  rw [eN'] at d5
  refine EvalAll.letE d5 fun v5 c5 h5 => ?_
  obtain ⟨rfl, hc5⟩ := h5
  have d6 := a18_trans (P := P) (e := e) (ps := ps) E (b := b) htrans hq1
    [.list (ks.map pairV), .list (ns.map pairV), encPts (offPts n rl L.q), .list (ss.map pairV),
      .list (σN.map encPerm)] (σs := σN) (by omega) rfl hl hrq
  refine EvalAll.letE d6 fun v6 c6 h6 => ?_
  obtain ⟨t, rfl, ht, htm, hc6⟩ := h6
  set rest : List Val := [.list (ks.map pairV), .list (ns.map pairV), encPts (offPts n rl L.q),
    .list (ss.map pairV), .list (σN.map encPerm), .nat t] with hrest
  have d7 := a18_parts (P := P) (e := e) (ps := ps) E (b := b) hparts hq1 rest
    (i := 1) (qs := ks) rfl hkl hl hrq
  have d8 := a18_parts (P := P) (e := e) (ps := ps) E (b := b) hparts hq1 rest
    (i := 4) (qs := ss) rfl hsl hl hrq
  have eH' : Val.list (ks.map fun p => natList (partNat (zs0 e E hq1) p.1)) =
      .list (σH.map encPerm) := congrArg Val.list eH
  have eS' : Val.list (ss.map fun p => natList (partNat (zs0 e E hq1) p.1)) =
      .list (σS.map encPerm) := congrArg Val.list eS
  rw [eH'] at d7
  rw [eS'] at d8
  have dv5 := Det.var' (P := P) (env := A :: rest) (i := 5) (v := .list (σN.map encPerm)) rfl
  have dv6 := Det.var' (P := P) (env := A :: rest) (i := 6) (v := .nat t) rfl
  have d := Det.mk4 d7 dv5 d8 dv6
  refine d.post fun c hc => ⟨σH, σN, σS, t, rfl, by omega, by omega, by omega, cH, cN, cS,
    ?_, ?_⟩
  · rw [ht, transitive_iff E hnat hq hP b₀ cN]
  · -- the cost
    have hmn := m_le_n e E ⟨0, hq1⟩
    have hsq : (n + L.q) ^ 2 + 1 ≤ 2 * pM n L.q ps ^ 2 := by
      have := Nat.pow_le_pow_left (show n + L.q ≤ pM n L.q ps by omega) 2
      have := Nat.one_le_pow 2 (pM n L.q ps) (by omega)
      omega
    have hw := wt_a18Out_le (σH := σH) (σN := σN) (σS := σS) (show m + 1 ≤ pM n L.q ps by omega)
      htm (by omega) (by omega) (by omega)
    have hw5 : (Val.list (σN.map encPerm)).wt ≤ (a18Out σH σN σS t).wt :=
      (wt_le_wt_list (by simp)).le
    have hw6 : (Val.nat t).wt ≤ (a18Out σH σN σS t).wt := (wt_le_wt_list (by simp)).le
    have e4 : (Val.list [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
      .nat t]).wt = (a18Out σH σN σS t).wt := rfl
    rw [e4] at hc
    have e5 : a18Cost hst (pM n L.q ps) = rowKerCost hst (pM n L.q ps) +
        2 * stabPB hst (pM n L.q ps) + a18K * pM n L.q ps ^ 16 := rfl
    rw [e5]
    generalize (a18Out σH σN σS t).wt = W at *
    generalize rowKerCost hst (pM n L.q ps) = RK at *
    generalize stabPB hst (pM n L.q ps) = PB at *
    generalize pM n L.q ps = M at *
    have m1 : 1 ≤ M := by omega
    have m6 : M ^ 6 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
    have m14 : M ^ 14 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
    have m15 : M ^ 15 ≤ M ^ 16 := Nat.pow_le_pow_right m1 (by omega)
    have m0 := Nat.one_le_pow 16 M m1
    have e1 : a18K = 10000000000000000000000 := rfl
    rw [e1]
    norm_num at hc1 hc2 hc3 hc4 hc5 hc6 hc ⊢
    omega

end Spec

end GI.Impl
