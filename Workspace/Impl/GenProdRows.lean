import Workspace.Impl.GenProdBits
import Workspace.Cited.AlgoCameron

/-!
# The product refinement: the rows of the points

The row of a point `p` of `Fin k` has `r + 1` entries. For a point of the domain, entry `i < r`
is coordinate `i` of its block (a `l`-set, as its sorted list) and entry `r` is `[1]`. For a
point off the domain, entries `i < r` are `[m]` (no `l`-set of `Fin m` has this list) and entry
`r` is `[0]`. So bit `i` of two rows is the coordinate bit `pbit i` of the two positions
(`rowBit_prodRows`), and the tables of the bit loop are the masks and the leading ones
(`pbSel_prodRows`).

The program builds the rows from the Cameron output `E` and the block numbers `num` of the
points (`labFin`, which is `d` off the domain): it appends `[1]` to each tuple of `E`, appends the
row of the points off the domain at position `d`, and gathers by `num` (`prows_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- The sorted list of an `l`-set. -/
def ksList {m l : ℕ} (A : Product.KSet m l) : List ℕ := (A.1.sort (· ≤ ·)).map Fin.val

theorem ksList_injective {m l : ℕ} : Function.Injective (ksList (m := m) (l := l)) := by
  intro A B h
  have h1 : A.1.sort (· ≤ ·) = B.1.sort (· ≤ ·) :=
    List.map_injective_iff.2 Fin.val_injective h
  exact Subtype.ext (by simpa using congrArg List.toFinset h1)

theorem ksList_ne {m l : ℕ} (A : Product.KSet m l) : ksList A ≠ [m] := by
  intro h
  have hmem : m ∈ ksList A := by rw [h]; simp
  obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
  exact absurd a.2 (by omega)

section rows

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
  (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) {k : ℕ} (e : Ω ≃ Fin k)

open Classical in
/-- **The row of a point.** -/
noncomputable def prodRows (p : Fin k) : List (List ℕ) :=
  if e.symm p ∈ S.dom then (List.finRange r).map (fun i => ksList (E (Q.blk (e.symm p)) i)) ++ [[1]]
  else List.replicate r [m] ++ [[0]]

theorem prodRows_length (p : Fin k) : (prodRows Q E e p).length = r + 1 := by
  unfold prodRows; split_ifs <;> simp

open Classical in
theorem prodRows_getD_lt (p : Fin k) {i : ℕ} (hi : i < r) :
    (prodRows Q E e p).getD i [] =
      if e.symm p ∈ S.dom then ksList (E (Q.blk (e.symm p)) ⟨i, hi⟩) else [m] := by
  unfold prodRows
  split_ifs
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp

open Classical in
theorem prodRows_getD_r (p : Fin k) :
    (prodRows Q E e p).getD r [] = if e.symm p ∈ S.dom then [1] else [0] := by
  unfold prodRows
  split_ifs
  · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
    simp
  · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
    simp

/-- **The bits of the rows are the coordinate bits.** -/
theorem rowBit_prodRows (p q : Fin k) {i : ℕ} (hi : i ≤ r) :
    rowBit (prodRows Q E e) p q i = pbit Q E i (e.symm p) (e.symm q) := by
  classical
  unfold rowBit pbit
  rcases Nat.lt_or_ge i r with hlt | hge
  · rw [dif_pos hlt, prodRows_getD_lt Q E e p hlt, prodRows_getD_lt Q E e q hlt]
    by_cases hp : e.symm p ∈ S.dom <;> by_cases hq : e.symm q ∈ S.dom
    · simp only [hp, hq, if_true, true_and, not_true_eq_false, and_false, or_false]
      simp only [ksList_injective.eq_iff]
    · simp only [hp, hq, if_true, if_false, true_and, false_and, not_true_eq_false,
        not_false_eq_true, and_true, or_false, and_false]
      rw [if_neg (ksList_ne _)]
    · simp only [hp, hq, if_true, if_false, false_and, not_true_eq_false,
        not_false_eq_true, true_and, or_false, and_false]
      rw [if_neg (fun h => ksList_ne _ h.symm)]
    · simp [hp, hq]
  · have hir : i = r := le_antisymm hi hge
    subst hir
    rw [dif_neg (lt_irrefl _), prodRows_getD_r, prodRows_getD_r]
    by_cases hp : e.symm p ∈ S.dom <;> by_cases hq : e.symm q ∈ S.dom <;> simp [hp, hq]

theorem hornerN_congr' {b b' : ℕ → ℕ} {r : ℕ} (h : ∀ i ≤ r, b i = b' i) :
    ∀ t ≤ r + 1, hornerN b r t = hornerN b' r t := hornerN_congr h

theorem leadN_congr {b b' : ℕ → ℕ} {r : ℕ} (h : ∀ i ≤ r, b i = b' i) :
    ∀ t ≤ r + 1, leadN b r t = leadN b' r t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => rw [leadN, leadN, ih (by omega), h _ (by omega)]

/-- **The tables are the masks and the leading ones.** -/
theorem pbSel_prodRows (j : Fin (k * k)) :
    pbSel (prodRows Q E e) r 0 j = maskF Q E e j ∧ pbSel (prodRows Q E e) r 1 j = leadF Q E e j := by
  have hb : ∀ i ≤ r, rowBit (prodRows Q E e) (pairFst j) (pairSnd j) i =
      pbit Q E i (e.symm (finProdFinEquiv.symm j).1) (e.symm (finProdFinEquiv.symm j).2) :=
    fun i hi => rowBit_prodRows Q E e _ _ hi
  refine ⟨?_, ?_⟩
  · simp only [pbSel, if_pos rfl, maskF, pmask]
    exact hornerN_congr hb _ le_rfl
  · simp only [pbSel, one_ne_zero, if_false, leadF, plead]
    exact leadN_congr hb _ le_rfl

end rows

/-! ### The program -/

/-- On `[c, row]`: the row with `[1]` appended. -/
def addOneF : Expr := .snoc (arg 1) (mk1 (.nat 1))

/-- The value of `addOneF` on a list. -/
def snocOne : Val → Val
  | .list ys => .list (ys ++ [natList [1]])
  | v => v

/-- The rows program, on `[E, num, m, r]`. -/
def prowsE (bm brep bga : ℕ) : Expr :=
  .call bga (mk2 (.snoc (.call bm (mk2 (.nat 0) (arg 0)))
    (.snoc (.call brep (mk2 (arg 3) (mk1 (arg 2)))) (mk1 (.nat 0)))) (arg 1))

theorem natList_ksList {m l : ℕ} (A : Product.KSet m l) :
    natList (ksList A) = .list ((A.1.sort (· ≤ ·)).map fun a => .nat a) := by
  simp only [natList, ksList, List.map_map]
  congr 1
  induction ((A.1.sort (· ≤ ·))) <;> simp_all

/-- The constant of the rows program. -/
def prowsK : ℕ := 10 ^ 14

theorem sum_wt_map_snoc_le (x : Val) : ∀ xs : List (List Val),
    ((xs.map fun ys => Val.list (ys ++ [x])).map Val.wt).sum ≤
      ((xs.map Val.list).map Val.wt).sum + xs.length * (2 * x.wt + 2)
  | [] => by simp
  | y :: ys => by
    have ih := sum_wt_map_snoc_le x ys
    have := wt_list_snoc_le y x
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e : (ys.length + 1) * (2 * x.wt + 2) = ys.length * (2 * x.wt + 2) + (2 * x.wt + 2) := by
      ring
    omega

theorem wt_map_snoc_le (xs : List (List Val)) (x : Val) :
    (Val.list (xs.map fun ys => Val.list (ys ++ [x]))).wt ≤
      2 * (Val.list (xs.map Val.list)).wt + xs.length * (4 * x.wt + 5) + 4 := by
  have h1 := wt_list_le (xs.map fun ys => Val.list (ys ++ [x]))
  have h2 := sum_wt_map_snoc_le x xs
  have h3 := sum_wt_lt_wt_list (xs.map Val.list)
  simp only [List.length_map] at h1
  have e : xs.length * (4 * x.wt + 5) = 2 * (xs.length * (2 * x.wt + 2)) + xs.length := by ring
  omega

theorem sum_map_affine : ∀ xs : List Val,
    (xs.map fun x => 6 * x.wt + 100).sum = 6 * (xs.map Val.wt).sum + 100 * xs.length
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_affine xs]; ring

set_option maxHeartbeats 2000000 in
/-- **The rows program.** On the Cameron output `E` and the block numbers of the points, it
returns the rows of the points. -/
theorem prows_spec {P : Program} {f bm fadd brep bga : ℕ}
    (hf : P.funs[f]? = some (prowsE bm brep bga)) (hbm : P.HasAt bm (mapFuns bm fadd))
    (hfadd : P.funs[fadd]? = some addOneF) (hrep : P.HasAt brep (replicateFuns brep))
    (hga : P.HasAt bga (gatherFuns bga))
    {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
    (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) {k : ℕ} (e : Ω ≃ Fin k) :
    FunDet P f (.list [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r])
      (rowsVal (prodRows Q E e))
      (prowsK * ((Val.list [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r]).wt
        + 1) ^ 6) := by
  classical
  set a := Val.list [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r] with ha
  set W := a.wt with hW
  set tup : Fin Q.d → List Val := fun x => (List.finRange r).map fun i => natList (ksList (E x i))
    with htup
  have hEv : GI.Cited.encKSetTuples E = .list ((List.finRange Q.d).map fun x => .list (tup x)) := by
    simp only [GI.Cited.encKSetTuples, htup, natList_ksList]
  set xs : List Val := (List.finRange Q.d).map fun x => .list (tup x) with hxs
  -- weights
  have wE : (Val.list xs).wt < W := by rw [← hEv]; exact wt_le_wt_list (by simp [ha])
  have wnum : (encFun (Q.labFin e)).wt < W := wt_le_wt_list (by simp [ha])
  have wm : (Val.nat m).wt < W := wt_le_wt_list (by simp [ha])
  have wr : (Val.nat r).wt < W := wt_le_wt_list (by simp [ha])
  have hd2 := Q.two_le
  have hxl : xs.length = Q.d := by simp [hxs]
  have hrW : r < W := by
    have h1 : Val.list (tup ⟨0, by omega⟩) ∈ xs := by simp [hxs]
    have h2 := wt_le_wt_list h1
    have h3 : r < (Val.list (tup ⟨0, by omega⟩)).wt := by
      have := length_lt_wt_list (tup ⟨0, by omega⟩)
      simpa [htup] using this
    omega
  have hdW : Q.d < W := by have := length_lt_wt_list xs; omega
  have hkW : k < W := by
    have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (Q.labFin e i))
    simp only [List.length_map, List.length_finRange] at this
    have e1 : (encFun (Q.labFin e)).wt =
      (Val.list ((List.finRange k).map fun i => Val.nat (Q.labFin e i))).wt := rfl
    omega
  -- the map
  have hmap := map_spec hbm (c := .nat 0) (xs := xs)
    (R := fun x w => w = snocOne x)
    (B := fun x => 6 * x.wt + 100) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      have d := Det.snoc (Det.arg' (P := P) (vs := [.nat 0, .list (tup y)]) (rest := []) (j := 1) rfl)
        (Det.mk1 (P := P) (env := [Val.list [.nat 0, .list (tup y)]]) (Det.nat 1))
      refine FunAll.mono (FunDet.intro hfadd d) fun w c hw => ⟨hw.1, ?_⟩
      have h1 := hw.2
      have h2 := wt_list2_le (.nat 0) (.list (tup y))
      have h3 := wt_list_snoc_le (tup y) (.list [.nat 1])
      have h4 := wt_list1_le (.nat 1)
      have h5 := wt_nat_le 0
      have h6 := wt_nat_le 1
      have h7 : (Val.list [Val.nat 1]).wt ≤ 11 := by omega
      simp only [snocOne] at *
      omega)
  set ext : List Val := xs.map snocOne with hext
  have wext : (Val.list ext).wt ≤ 60 * W := by
    have e1 : ext = ((List.finRange Q.d).map tup).map fun ys => Val.list (ys ++ [natList [1]]) := by
      rw [hext, hxs, List.map_map, List.map_map]; rfl
    have e2 : xs = ((List.finRange Q.d).map tup).map Val.list := by rw [hxs, List.map_map]; rfl
    have h1 := wt_map_snoc_le ((List.finRange Q.d).map tup) (natList [1])
    rw [← e1, ← e2] at h1
    have h4 := wt_list1_le (.nat 1)
    have h6 := wt_nat_le 1
    have h7 : (natList [1]).wt ≤ 11 := by
      show (Val.list [Val.nat 1]).wt ≤ 11; omega
    simp only [List.length_map, List.length_finRange] at h1
    have : Q.d * (4 * (natList [1]).wt + 5) ≤ Q.d * 49 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hBsum : (xs.map fun x => 6 * x.wt + 100).sum ≤ 106 * W := by
    have h1 : (xs.map fun x => 6 * x.wt + 100).sum = 6 * (xs.map Val.wt).sum + 100 * xs.length := by
      exact sum_map_affine xs
    have h2 := sum_wt_lt_wt_list xs
    have h3 := length_lt_wt_list xs
    omega
  have wc0 := wt_list2_le (.nat 0) (.list xs)
  have := wt_nat_le 0
  have dA0 : Det P [a] (arg 0) (.list xs) (2 * W + 5) := by
    rw [← hEv]; exact Det.arg' (vs := [_, encFun (Q.labFin e), .nat m, .nat r]) (j := 0) rfl
  have := wt_nat_le 0
  obtain ⟨CM, hCM⟩ : ∃ CM, CM = 106 * W + 100000 * (W + 1) ^ 2 := ⟨_, rfl⟩
  have hmap' : FunAll P bm (.list [.nat 0, .list xs]) (fun w c => w = .list ext ∧ c ≤ CM) := by
    refine hmap.mono fun w c hw => ?_
    obtain ⟨ws, rfl, hR, hc⟩ := hw
    rw [forall₂_eq_map hR] at hc ⊢
    refine ⟨rfl, ?_⟩
    have hx : xs.length + 1 ≤ W + 1 := by have := length_lt_wt_list xs; omega
    have wext' : (Val.list (xs.map snocOne)).wt ≤ 60 * W := wext
    have : mapK * (xs.length + 1) * ((Val.list [.nat 0, .list xs]).wt + (Val.list (xs.map snocOne)).wt + 1) ≤
        1000 * (W + 1) * (100 * (W + 1)) := by
      simp only [mapK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hx) (by omega)
    have e3 : 1000 * (W + 1) * (100 * (W + 1)) = 100000 * (W + 1) ^ 2 := by ring
    omega
  have dmap := Det.call (Det.mk2 (Det.nat (P := P) (env := [a]) 0) dA0) hmap'
  -- the row off the domain
  have dR3 : Det P [a] (arg 3) (.nat r) (2 * W + 8) :=
    Det.arg' (vs := [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r]) (j := 3) rfl
  have dR2 : Det P [a] (arg 2) (.nat m) (2 * W + 7) :=
    Det.arg' (vs := [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r]) (j := 2) rfl
  set vm : Val := .list [.nat m] with hvm
  have wvm : vm.wt ≤ 2 * W + 5 := by
    have := wt_list1_le (.nat m)
    have : vm.wt = (Val.list [.nat m]).wt := rfl
    omega
  have wrep : (Val.list (List.replicate r vm)).wt ≤ 15 * (W + 1) ^ 2 := by
    have h1 := wt_list_le_of (List.replicate r vm) (c := vm.wt) (fun v hv => by
      rw [List.eq_of_mem_replicate hv])
    rw [List.length_replicate] at h1
    have h2 : r * (2 * vm.wt + 1) ≤ W * (4 * W + 11) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  obtain ⟨CR, hCR⟩ : ∃ CR, CR = 40000 * (W + 1) ^ 3 := ⟨_, rfl⟩
  have hrep' : FunAll P brep (.list [.nat r, vm])
      (fun w c => w = .list (List.replicate r vm) ∧ c ≤ CR) := by
    refine (replicate_spec hrep r vm).mono fun w c hw => ?_
    obtain ⟨rfl, hc⟩ := hw
    refine ⟨rfl, ?_⟩
    have h1 := wt_list2_le (.nat r) vm
    have h2 : loopModK * (r + 1) * ((Val.list [.nat r, vm]).wt + r +
        (Val.list (List.replicate r vm)).wt + 1) ≤ 1000 * (W + 1) * (40 * (W + 1) ^ 2) := by
      simp only [loopModK]
      refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
      have : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    have e3 : 1000 * (W + 1) * (40 * (W + 1) ^ 2) = 40000 * (W + 1) ^ 3 := by ring
    omega
  have drep := Det.call (Det.mk2 dR3 (Det.mk1 dR2)) hrep'
  set offV : Val := .list (List.replicate r vm ++ [.list [.nat 0]]) with hoffV
  have doff := Det.snoc drep (Det.mk1 (Det.nat (P := P) (env := [a]) 0))
  have dfull := Det.snoc dmap doff
  -- the gather
  set is : List ℕ := (List.finRange k).map (Q.labFin e) with his
  have dnum : Det P [a] (arg 1) (natList is) (2 * W + 6) :=
    Det.arg' (vs := [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r]) (j := 1)
      (by show some (encFun (Q.labFin e)) = some _; rw [encFun_eq_natList])
  have hi : ∀ i ∈ is, i < (ext ++ [offV]).length := by
    intro i hi
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hi
    have := Q.labFin_le e p
    simp [hext, hxl]; omega
  have dg := Det.call (Det.mk2 dfull dnum) (gather_spec hga hi)
  have hval : Val.list (is.map fun i => (ext ++ [offV]).getD i (.nat 0)) = rowsVal (prodRows Q E e) := by
    simp only [rowsVal, his, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, PrimitiveQuotient.labFin, prodRows]
    by_cases hp : e.symm p ∈ S.dom
    · rw [if_pos hp, if_pos hp]
      have hlt : (Q.blk (e.symm p) : ℕ) < ext.length := by simp [hext, hxl]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt]
      simp [hext, hxs, snocOne, htup, List.map_append, natList]
    · rw [if_neg hp, if_neg hp]
      rw [List.getD_eq_getElem _ _ (by simp [hext, hxl]), List.getElem_append_right (by simp [hext, hxl])]
      simp [hext, hxl, hoffV, hvm, natList]
  rw [hval] at dg
  refine FunDet.intro hf (dg.mono ?_)
  have hW1 : 1 ≤ W + 1 := by omega
  have p12 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have p36 : (W + 1) ^ 3 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right hW1 (by norm_num)
  have w0 := wt_list1_le (.nat 0)
  have woff : offV.wt ≤ 16 * (W + 1) ^ 2 + 30 := by
    have := wt_list_snoc_le (List.replicate r vm) (.list [.nat 0])
    have : offV.wt = (Val.list (List.replicate r vm ++ [.list [.nat 0]])).wt := rfl
    omega
  have wfull : (Val.list (ext ++ [offV])).wt ≤ 100 * (W + 1) ^ 2 := by
    have := wt_list_snoc_le ext offV
    omega
  have wis : (natList is).wt < W := by
    have : (natList is).wt = (encFun (Q.labFin e)).wt := by rw [encFun_eq_natList]
    omega
  have wg2 := wt_list2_le (Val.list (ext ++ [offV])) (natList is)
  have hgc : gatherK * ((Val.list [Val.list (ext ++ [offV]), natList is]).wt + 1) ^ 3 ≤
      10 ^ 12 * (W + 1) ^ 6 := by
    have h1 : (Val.list [Val.list (ext ++ [offV]), natList is]).wt + 1 ≤ 210 * (W + 1) ^ 2 := by
      omega
    calc gatherK * ((Val.list [Val.list (ext ++ [offV]), natList is]).wt + 1) ^ 3
        ≤ gatherK * (210 * (W + 1) ^ 2) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
      _ = 926100000000 * (W + 1) ^ 6 := by simp only [gatherK]; ring
      _ ≤ 10 ^ 12 * (W + 1) ^ 6 := Nat.mul_le_mul_right _ (by norm_num)
  have hres := FunDet.wt_lt (gather_spec (P := P) hga hi)
  rw [hval] at hres
  have wrr := wt_list_snoc_le (List.replicate r vm) (.list [.nat 0])
  have wvr := wt_list2_le (.nat r) (.list [.nat m])
  have wv2 : (Val.list [Val.nat r, Val.list [Val.nat m]]).wt = (Val.list [.nat r, vm]).wt := rfl
  have wvr' := wt_list1_le (.nat m)
  have wvr'' : (Val.list (List.replicate r vm)).wt ≤ 15 * (W + 1) ^ 2 := wrep
  have eoff : (Val.list (List.replicate r vm ++ [Val.list [Val.nat 0]])).wt = offV.wt := rfl
  have eext : (Val.list (xs.map snocOne)).wt = (Val.list ext).wt := rfl
  have q1 : (Val.list (ext ++ [Val.list (List.replicate r vm ++ [Val.list [Val.nat 0]])])).wt =
    (Val.list (ext ++ [offV])).wt := rfl
  have q2 : (Val.list [Val.list (ext ++ [Val.list (List.replicate r vm ++ [Val.list [Val.nat 0]])]),
    natList is]).wt = (Val.list [Val.list (ext ++ [offV]), natList is]).wt := rfl
  have q3 : vm.wt = (Val.list [Val.nat m]).wt := rfl
  rw [q2]
  simp only [prowsK] at *
  omega

end GI.Impl
