import Workspace.Impl.KRefNb

/-!
# The small modules of a round

A round of the refinement is built from five small modules, each on lists of numbers:
* `look`: on `[T, is]`, the entries of `T` at the indices `is`;
* `hor`: on `[B, ds, a]`, Horner's rule in base `B` started at `a` (`krefHornerFrom`);
* `rank`: on `[L, q]`, the number of entries of `L` below `q` (`krefRank`);
* `ranks`: on `[L, qs]`, the ranks of all `q` in `qs`;
* `flat`: on `[c, Ls, []]`, the lists of `Ls` joined.

All costs are stated through one weight bound `Y` on the inputs and outputs.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp len)

theorem kref_wt_nat_mono {a b : ℕ} (h : a ≤ b) : (Val.nat a).wt ≤ (Val.nat b).wt := by
  rw [wt_nat, wt_nat]; have := len_le_of_le h; omega

theorem kref_wt_get_le {T : List ℕ} {i : ℕ} : (Val.nat (T.getD i 0)).wt ≤ (natList T).wt := by
  by_cases hi : i < T.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact (wt_le_wt_list (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)).le
  · rw [List.getD_eq_default _ _ (by omega)]
    have := wt_nat_le 0
    have h2 : (2 : ℕ) ≤ (natList T).wt := by
      unfold natList; rw [wt_list_eq]; omega
    omega

/-! ### Look-up -/

/-- On `[T, i]`: the entry `T[i]`. -/
def krefLookG : Expr := .get (arg 0) (arg 1)

/-- `look`, at base `b` (four functions). -/
def krefLookFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [krefLookG]

def krefLookK : ℕ := mapK * (3 * 100 + 11) * 2 ^ 3

theorem kref_lookG {P : Program} {g : ℕ} (hg : P.funs[g]? = some krefLookG) {T : List ℕ}
    {i Y : ℕ} (hi : i < T.length) (hT : (natList T).wt ≤ Y) (hiY : (Val.nat i).wt ≤ Y) :
    FunDet P g (.list [natList T, .nat i]) (.nat (T.getD i 0)) (100 * (Y + 1) ^ 1) := by
  have hWA : (Val.list [natList T, .nat i]).wt ≤ 4 * Y + 6 := by
    have := wt_list2_le (natList T) (.nat i); omega
  set A : List Val := [natList T, .nat i] with hA
  have d1 : Det P [.list A] (arg 0) (natList T) (2 * (Val.list A).wt + 0 + 5) := Det.arg' rfl
  have d2 : Det P [.list A] (arg 1) (.nat i) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have d3 := Det.get' d1 d2 (kref_natList_get hi)
  refine FunDet.intro hg (d3.mono ?_)
  have := kref_wt_get_le (T := T) (i := i)
  simp only [pow_one]
  omega

/-- **Look-up.** On `[T, is]`, the list of `T[i]` for `i` in `is`. -/
theorem kref_look {P : Program} {b : ℕ} (h : P.HasAt b (krefLookFuns b)) {T is : List ℕ}
    {Y : ℕ} (hi : ∀ i ∈ is, i < T.length) (hT : (natList T).wt ≤ Y) (his : (natList is).wt ≤ Y) :
    FunDet P b (.list [natList T, natList is]) (natList (is.map fun i => T.getD i 0))
      (krefLookK * (Y + 1) ^ 3) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hg : P.funs[b + 3]? = some krefLookG := by
    simpa [krefLookFuns, mapFuns, loopFuns] using h.right.single
  have hm := kref_mapL hmap (l := is) (enc := Val.nat) (F := fun i => .nat (T.getD i 0))
    (Y := Y) (A := 1) (K := 100) (d := 1) (by norm_num) (fun a _ a' _ haa => by cases haa; rfl)
    (fun i hi' => kref_lookG hg (hi i hi') hT
      ((wt_le_wt_list (List.mem_map.mpr ⟨i, hi', rfl⟩)).le.trans his)) (by omega)
    (by have : (Val.list (is.map Val.nat)).wt = (natList is).wt := rfl; omega)
  have e : Val.list (is.map fun i => Val.nat (T.getD i 0)) =
      natList (is.map fun i => T.getD i 0) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [e] at hm
  exact hm.mono (le_of_eq (by unfold krefLookK; ring))

/-! ### Horner's rule -/

/-- On `[B, acc, d]`: `acc * B + d`. -/
def krefHorG : Expr := .arith .add (.arith .mul (arg 1) (arg 0)) (arg 2)

/-- `hor`, at base `b` (four functions): on `[B, ds, a]`. -/
def krefHorFuns (b : ℕ) : List Expr := foldlFuns b (b + 3) ++ [krefHorG]

def krefHorK : ℕ := loopModK * (100 + 10)

theorem kref_horG {P : Program} {g : ℕ} (hg : P.funs[g]? = some krefHorG) {B acc d Y : ℕ}
    (hB : (Val.nat B).wt ≤ Y) (ha : (Val.nat acc).wt ≤ Y) (hd : (Val.nat d).wt ≤ Y)
    (hr : (Val.nat (acc * B + d)).wt ≤ Y) :
    FunDet P g (.list [.nat B, .nat acc, .nat d]) (.nat (acc * B + d)) (100 * (Y + 1) ^ 1) := by
  have hWA : (Val.list [.nat B, .nat acc, .nat d]).wt ≤ 6 * Y + 7 := by
    have := wt_list3_le (.nat B) (.nat acc) (.nat d); omega
  set A : List Val := [.nat B, .nat acc, .nat d] with hA
  have d0 : Det P [.list A] (arg 0) (.nat B) (2 * (Val.list A).wt + 0 + 5) := Det.arg' rfl
  have d1 : Det P [.list A] (arg 1) (.nat acc) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have d2 : Det P [.list A] (arg 2) (.nat d) (2 * (Val.list A).wt + 2 + 5) := Det.arg' rfl
  have hm := Det.arith (op := .mul) d1 d0
  have hs := Det.arith (op := .add) hm d2
  simp only [BinOp.eval] at hs
  refine FunDet.intro hg (hs.mono ?_)
  have := kref_wt_nat_mono (Nat.le_add_right (acc * B) d)
  simp only [pow_one]
  omega

theorem kref_foldl_horner (B : ℕ) (ds : List ℕ) (a : ℕ) :
    (ds.map Val.nat).foldl (fun acc x => Val.nat (krefN acc * B + krefN x)) (.nat a) =
      .nat (krefHornerFrom B a ds) := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih => simp only [List.map_cons, List.foldl_cons, krefN_nat]; exact ih _

theorem kref_hornerFrom_le_append {B : ℕ} (hB : 1 ≤ B) (a : ℕ) (l₁ l₂ : List ℕ) :
    krefHornerFrom B a l₁ ≤ krefHornerFrom B a (l₁ ++ l₂) := by
  rw [krefHornerFrom_append, krefHornerFrom_eq B _ l₂]
  have : 1 ≤ B ^ l₂.length := Nat.one_le_pow _ _ hB
  calc krefHornerFrom B a l₁ ≤ krefHornerFrom B a l₁ * B ^ l₂.length :=
        Nat.le_mul_of_pos_right _ this
    _ ≤ _ := Nat.le_add_right _ _

theorem kref_hornerFrom_take_le {B : ℕ} (hB : 1 ≤ B) (a : ℕ) (ds : List ℕ) (i : ℕ) :
    krefHornerFrom B a (ds.take i) ≤ krefHornerFrom B a ds := by
  conv_rhs => rw [← List.take_append_drop i ds]
  exact kref_hornerFrom_le_append hB a _ _

/-- **Horner's rule.** On `[B, ds, a]`, the number `krefHornerFrom B a ds`. -/
theorem kref_hor {P : Program} {b : ℕ} (h : P.HasAt b (krefHorFuns b)) {B a Y : ℕ}
    {ds : List ℕ} (hB1 : 1 ≤ B) (hB : (Val.nat B).wt ≤ Y)
    (hr : (Val.nat (krefHornerFrom B a ds)).wt ≤ Y) (hds : (natList ds).wt ≤ Y) :
    FunDet P b (.list [.nat B, natList ds, .nat a]) (.nat (krefHornerFrom B a ds))
      (krefHorK * (Y + 1) ^ 3) := by
  have hf : P.HasAt b (foldlFuns b (b + 3)) := h.left
  have hg : P.funs[b + 3]? = some krefHorG := by
    simpa [krefHorFuns, foldlFuns, loopFuns] using h.right.single
  have hpre : ∀ i, (Val.nat (krefHornerFrom B a (ds.take i))).wt ≤ Y := fun i =>
    (kref_wt_nat_mono (kref_hornerFrom_take_le hB1 a ds i)).trans hr
  have hfo := kref_foldl hf (c := .nat B) (acc0 := .nat a) (xs := ds.map Val.nat)
    (G := fun acc x => Val.nat (krefN acc * B + krefN x)) (Y := Y) (K := 100) (d := 1)
    (fun i hi => by
      rw [← List.map_take, kref_foldl_horner]
      have hi' : i < ds.length := by simpa using hi
      simp only [List.getElem_map, krefN_nat]
      have e : krefHornerFrom B a (ds.take i) * B + ds[i] = krefHornerFrom B a (ds.take (i + 1)) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
          krefHornerFrom_append]
        rfl
      refine kref_horG hg hB (hpre i) ?_ (by rw [e]; exact hpre (i + 1))
      exact (wt_le_wt_list (List.mem_map.mpr ⟨_, List.getElem_mem hi', rfl⟩)).le.trans hds)
    (fun i _ => by rw [← List.map_take, kref_foldl_horner]; exact hpre i)
    (by omega) hds
  rw [kref_foldl_horner] at hfo
  exact hfo.mono (le_of_eq (by unfold krefHorK; ring))

/-! ### Rank -/

/-- On `[q, acc, y]`: `acc + [y < q]`. -/
def krefRankG : Expr := .arith .add (arg 1) (.arith .lt (arg 2) (arg 0))

/-- On `[L, q]`: run the fold at `fo` on `[q, L, 0]`. -/
def krefRankF (fo : ℕ) : Expr := .call fo (mk3 (arg 1) (arg 0) (.nat 0))

/-- `rank`, at base `b` (five functions). -/
def krefRankFuns (b : ℕ) : List Expr := [krefRankF (b + 1)] ++ foldlFuns (b + 1) (b + 4) ++ [krefRankG]

def krefRankFoldK : ℕ := loopModK * (100 + 10)

def krefRankK : ℕ := 30 * krefRankFoldK + 100

theorem kref_rankG {P : Program} {g : ℕ} (hg : P.funs[g]? = some krefRankG) {q acc y Y : ℕ}
    (hq : (Val.nat q).wt ≤ Y) (ha : acc + 1 ≤ Y) (hy : (Val.nat y).wt ≤ Y) :
    FunDet P g (.list [.nat q, .nat acc, .nat y]) (.nat (acc + if y < q then 1 else 0))
      (100 * (Y + 1) ^ 1) := by
  have h1 := wt_nat_le acc
  have hWA : (Val.list [.nat q, .nat acc, .nat y]).wt ≤ 6 * Y + 11 := by
    have := wt_list3_le (.nat q) (.nat acc) (.nat y); omega
  set A : List Val := [.nat q, .nat acc, .nat y] with hA
  have d0 : Det P [.list A] (arg 0) (.nat q) (2 * (Val.list A).wt + 0 + 5) := Det.arg' rfl
  have d1 : Det P [.list A] (arg 1) (.nat acc) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have d2 : Det P [.list A] (arg 2) (.nat y) (2 * (Val.list A).wt + 2 + 5) := Det.arg' rfl
  have hl := Det.arith' (op := .lt) d2 d0 (z := if y < q then 1 else 0) rfl
  have hs := Det.arith' (op := .add) d1 hl (z := acc + if y < q then 1 else 0) rfl
  refine FunDet.intro hg (hs.mono ?_)
  have : (if y < q then 1 else 0) ≤ 1 := by split_ifs <;> omega
  simp only [pow_one]
  omega

theorem kref_foldl_rank (q : ℕ) (L : List ℕ) (a : ℕ) :
    (L.map Val.nat).foldl (fun acc x => Val.nat (krefN acc + if krefN x < q then 1 else 0))
      (.nat a) = .nat (a + krefRank L q) := by
  induction L generalizing a with
  | nil => simp [krefRank]
  | cons y L ih =>
    simp only [List.map_cons, List.foldl_cons, krefN_nat]
    rw [ih]
    simp only [krefRank, List.countP_cons]
    split_ifs with h1 h2 <;> simp_all <;> omega

/-- **Rank.** On `[L, q]`, the number `krefRank L q`. -/
theorem kref_rank {P : Program} {b : ℕ} (h : P.HasAt b (krefRankFuns b)) {L : List ℕ} {q Y : ℕ}
    (hL : (natList L).wt ≤ Y) (hq : (Val.nat q).wt ≤ Y) (hl : L.length + 2 ≤ Y) :
    FunDet P b (.list [natList L, .nat q]) (.nat (krefRank L q)) (krefRankK * (Y + 1) ^ 3) := by
  have hF : P.funs[b]? = some (krefRankF (b + 1)) := by
    simpa [krefRankFuns] using h 0 (by simp [krefRankFuns])
  have hf : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := by simpa using h.left.right
  have hg : P.funs[b + 4]? = some krefRankG := by
    simpa [krefRankFuns, foldlFuns, loopFuns, Nat.add_assoc] using h.right.single
  have hlen := length_natList_lt' L
  have hrk : ∀ i, krefRank (L.take i) q ≤ L.length := fun i =>
    (List.countP_le_length).trans (by simp)
  have hfo := kref_foldl hf (c := .nat q) (acc0 := .nat 0) (xs := L.map Val.nat)
    (G := fun acc x => Val.nat (krefN acc + if krefN x < q then 1 else 0)) (Y := Y) (K := 100)
    (d := 1)
    (fun i hi => by
      rw [← List.map_take, kref_foldl_rank]
      have hi' : i < L.length := by simpa using hi
      simp only [List.getElem_map, krefN_nat]
      refine kref_rankG hg hq (by have := hrk i; omega) ?_
      exact (wt_le_wt_list (List.mem_map.mpr ⟨_, List.getElem_mem hi', rfl⟩)).le.trans hL)
    (fun i _ => by
      rw [← List.map_take, kref_foldl_rank]
      have := hrk i; have := wt_nat_le (0 + krefRank (L.take i) q); omega)
    hq (by have : (Val.list (L.map Val.nat)).wt = (natList L).wt := rfl; omega)
  rw [kref_foldl_rank, Nat.zero_add] at hfo
  have hfo' : FunDet P (b + 1) (.list [.nat q, natList L, .nat 0]) (.nat (krefRank L q))
      (krefRankFoldK * (Y + 1) ^ 3) := hfo
  have hWA : (Val.list [natList L, .nat q]).wt ≤ 4 * Y + 6 := by
    have := wt_list2_le (natList L) (.nat q); omega
  set A : List Val := [natList L, .nat q] with hA
  have d0 : Det P [.list A] (arg 0) (natList L) (2 * (Val.list A).wt + 0 + 5) := Det.arg' rfl
  have d1 : Det P [.list A] (arg 1) (.nat q) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have hc := Det.call (Det.mk3 d1 d0 (Det.nat 0)) hfo'
  refine FunDet.intro hF (hc.mono ?_)
  have := wt_list3_le (.nat q) (natList L) (.nat 0)
  have := wt_nat_le 0
  have := wt_nat_le (krefRank L q)
  have : krefRank L q ≤ L.length := List.countP_le_length
  have hT : Y + 1 ≤ (Y + 1) ^ 3 := kref_le_pow (by norm_num)
  have e : krefRankK * (Y + 1) ^ 3 = 30 * (krefRankFoldK * (Y + 1) ^ 3) + 100 * (Y + 1) ^ 3 := by
    unfold krefRankK; ring
  rw [e]
  omega

/-- `ranks`, at base `b` (eight functions): on `[L, qs]`. -/
def krefRanksFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ krefRankFuns (b + 3)

def krefRanksK : ℕ := mapK * (3 * krefRankK + 11) * 2 ^ 5

/-- **Ranks.** On `[L, qs]`, the list of `krefRank L q` for `q` in `qs`. -/
theorem kref_ranks {P : Program} {b : ℕ} (h : P.HasAt b (krefRanksFuns b)) {L qs : List ℕ}
    {Y : ℕ} (hL : (natList L).wt ≤ Y) (hqs : (natList qs).wt ≤ Y) (hl : L.length + 2 ≤ Y) :
    FunDet P b (.list [natList L, natList qs]) (natList (qs.map (krefRank L)))
      (krefRanksK * (Y + 1) ^ 5) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hr : P.HasAt (b + 3) (krefRankFuns (b + 3)) := by
    simpa [krefRanksFuns, mapFuns, loopFuns] using h.right
  have hm := kref_mapL hmap (l := qs) (enc := Val.nat) (F := fun q => .nat (krefRank L q))
    (Y := Y) (A := 1) (K := krefRankK) (d := 3) (by norm_num)
    (fun a _ a' _ haa => by cases haa; rfl)
    (fun q hq => kref_rank hr hL ((wt_le_wt_list (List.mem_map.mpr ⟨q, hq, rfl⟩)).le.trans hqs) hl)
    (by omega) (by have : (Val.list (qs.map Val.nat)).wt = (natList qs).wt := rfl; omega)
  have e : Val.list (qs.map fun q => Val.nat (krefRank L q)) = natList (qs.map (krefRank L)) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [e] at hm
  exact hm.mono (le_of_eq (by unfold krefRanksK; ring))

/-! ### Append and join -/

def krefAppK : ℕ := 7 * loopModK

/-- **Append**, with a weight bound. -/
theorem kref_app {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) {xs ys : List Val} {Y : ℕ}
    (hx : (Val.list xs).wt ≤ Y) (hy : (Val.list ys).wt ≤ Y) (hxy : (Val.list (xs ++ ys)).wt ≤ Y) :
    FunDet P b (.list [.list xs, .list ys]) (.list (xs ++ ys)) (krefAppK * (Y + 1) ^ 2) := by
  refine FunAll.mono (append_spec h xs ys) fun w c hw => ⟨hw.1, ?_⟩
  obtain ⟨rfl, hc⟩ := hw
  have h1 := wt_list2_le (.list xs) (.list ys)
  have h2 := length_lt_wt_list ys
  have h3 : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (Val.list (xs ++ ys)).wt + 1) ≤ loopModK * (Y + 1) * (7 * (Y + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : loopModK * (Y + 1) * (7 * (Y + 1)) = krefAppK * (Y + 1) ^ 2 := by
    unfold krefAppK; ring
  omega

/-- The list held by a value (empty for a number). -/
def krefL : Val → List Val
  | .list l => l
  | .nat _ => []

@[simp] theorem krefL_list (l : List Val) : krefL (.list l) = l := rfl

/-- On `[c, acc, l]`: `acc ++ l`, by the append module at `ap`. -/
def krefFlatG (ap : ℕ) : Expr := .call ap (mk2 (arg 1) (arg 2))

/-- `flat`, at base `b` (eight functions): on `[c, Ls, []]`. -/
def krefFlatFuns (b : ℕ) : List Expr := foldlFuns b (b + 3) ++ [krefFlatG (b + 4)] ++ appendFuns (b + 4)

def krefFlatK : ℕ := loopModK * (100 * krefAppK + 10)

theorem kref_foldl_flat (Ls : List (List Val)) (a : List Val) :
    (Ls.map Val.list).foldl (fun acc x => Val.list (krefL acc ++ krefL x)) (.list a) =
      .list (a ++ Ls.flatten) := by
  induction Ls generalizing a with
  | nil => simp
  | cons l Ls ih => simp only [List.map_cons, List.foldl_cons, krefL_list]; rw [ih]; simp

theorem kref_wt_flatten_take (Ls : List (List Val)) (i : ℕ) :
    (Val.list (Ls.take i).flatten).wt ≤ (Val.list Ls.flatten).wt := by
  apply wt_list_mono
  conv_rhs => rw [← List.take_append_drop i Ls]
  rw [List.flatten_append]
  exact List.prefix_append _ _

/-- **Join.** On `[c, Ls, []]`, the lists of `Ls` joined. -/
theorem kref_flat {P : Program} {b : ℕ} (h : P.HasAt b (krefFlatFuns b)) {c : Val}
    {Ls : List (List Val)} {Y : ℕ} (hc : c.wt ≤ Y) (hLs : (Val.list (Ls.map Val.list)).wt ≤ Y)
    (hfl : (Val.list Ls.flatten).wt ≤ Y) :
    FunDet P b (.list [c, .list (Ls.map Val.list), .list []]) (.list Ls.flatten)
      (krefFlatK * (Y + 1) ^ 4) := by
  have hf : P.HasAt b (foldlFuns b (b + 3)) := h.left.left
  have hg : P.funs[b + 3]? = some (krefFlatG (b + 4)) := by
    simpa [krefFlatFuns, foldlFuns, loopFuns] using h.left.right.single
  have ha : P.HasAt (b + 4) (appendFuns (b + 4)) := by
    simpa [krefFlatFuns, foldlFuns, loopFuns, Nat.add_assoc] using h.right
  have hpre : ∀ i, (Val.list (Ls.take i).flatten).wt ≤ Y := fun i =>
    (kref_wt_flatten_take Ls i).trans hfl
  have hfo := kref_foldl hf (c := c) (acc0 := .list []) (xs := Ls.map Val.list)
    (G := fun acc x => Val.list (krefL acc ++ krefL x)) (Y := Y) (K := 100 * krefAppK) (d := 2)
    (fun i hi => by
      rw [← List.map_take, kref_foldl_flat]
      have hi' : i < Ls.length := by simpa using hi
      simp only [List.getElem_map, krefL_list, List.nil_append]
      have e : (Ls.take i).flatten ++ Ls[i] = (Ls.take (i + 1)).flatten := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
          List.flatten_append]
        simp
      have hli : (Val.list Ls[i]).wt ≤ Y :=
        (wt_le_wt_list (List.mem_map.mpr ⟨_, List.getElem_mem hi', rfl⟩)).le.trans hLs
      have hA := kref_app ha (hpre i) hli (by rw [e]; exact hpre (i + 1))
      have hWA : (Val.list [c, .list (Ls.take i).flatten, .list Ls[i]]).wt ≤ 6 * Y + 7 := by
        have := wt_list3_le c (.list (Ls.take i).flatten) (.list Ls[i]); have := hpre i; omega
      set A : List Val := [c, .list (Ls.take i).flatten, .list Ls[i]] with hA'
      have d1 : Det P [.list A] (arg 1) (.list (Ls.take i).flatten) (2 * (Val.list A).wt + 1 + 5) :=
        Det.arg' rfl
      have d2 : Det P [.list A] (arg 2) (.list Ls[i]) (2 * (Val.list A).wt + 2 + 5) := Det.arg' rfl
      have hcall := Det.call (Det.mk2 d1 d2) hA
      refine FunDet.intro hg (hcall.mono ?_)
      have := wt_list2_le (.list (Ls.take i).flatten) (.list Ls[i])
      have := hpre i
      have := hpre (i + 1)
      rw [← e] at this
      have hT : Y + 1 ≤ (Y + 1) ^ 2 := kref_le_pow (by norm_num)
      have e2 : 100 * krefAppK * (Y + 1) ^ 2 = 100 * (krefAppK * (Y + 1) ^ 2) := by ring
      rw [e2]
      have : 1 ≤ krefAppK := by unfold krefAppK loopModK; norm_num
      have : (Y + 1) ^ 2 ≤ krefAppK * (Y + 1) ^ 2 := Nat.le_mul_of_pos_left _ this
      omega)
    (fun i _ => by rw [← List.map_take, kref_foldl_flat]; simpa using hpre i)
    hc hLs
  rw [kref_foldl_flat, List.nil_append] at hfo
  exact hfo.mono (le_of_eq (by unfold krefFlatK; ring))

end GI.Impl
