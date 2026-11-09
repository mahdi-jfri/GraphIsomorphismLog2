module

public import Workspace.Degree.ProgCost
public import Workspace.Lang.Lib.Graph
public import Workspace.Lang.Lib.Search
public import Workspace.Lang.Lib.NatList

/-!
# Tables

Most functions of the graph program compute a table: a value for each `i < m`. A table module holds
an expression `e` for one entry, over the argument `[c, i]`.

* `tabFuns b e`: on `[c, [0, …, m - 1]]`, the list of the values of `e`. Its spec is `tab_spec`.
* `ids m`: the list `[0, …, m - 1]`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- The table of `e`, at base `b`. Four functions. -/
def tabFuns (b : ℕ) (e : Expr) : List Expr := mapFuns b (b + 3) ++ [e]

theorem length_tabFuns (b : ℕ) (e : Expr) : (tabFuns b e).length = 4 := by
  simp [tabFuns, mapFuns, loopFuns]

/-- The list `[0, …, m - 1]`. -/
abbrev ids (m : ℕ) : Val := encFun fun i : Fin m => (i : ℕ)

theorem listFin_get {m : ℕ} (F : Fin m → Val) (i : Fin m) :
    ((List.finRange m).map F)[(i : ℕ)]? = some (F i) := by
  simp

theorem listFin_get' {m : ℕ} (F : Fin m → Val) {i : ℕ} (hi : i < m) :
    ((List.finRange m).map F)[i]? = some (F ⟨i, hi⟩) := by
  simp [hi]

theorem encFun_val {m : ℕ} (f : Fin m → ℕ) :
    encFun f = .list ((List.finRange m).map fun i => .nat (f i)) := rfl

/-- The weight of a list whose entries weigh at most `c`. -/
theorem wt_lit (vs : List Val) {c : ℕ} (h : ∀ v ∈ vs, v.wt ≤ c) :
    (Val.list vs).wt ≤ vs.length * (2 * c + 1) + 4 := by
  have h1 := wt_list_le vs
  have h2 := List.sum_le_card_nsmul (vs.map Val.wt) c (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ v hv rfl; exact h v hv)
  simp only [List.length_map, smul_eq_mul] at h2
  have : vs.length * (2 * c + 1) = 2 * (vs.length * c) + vs.length := by ring
  omega

/-- A list of five. -/
def mk5 (a b c d e : Expr) : Expr := .snoc (mk4 a b c d) e

theorem Lv.mk5 {P : Program} {env : List Val} {T : ℕ} {a b c d e : Expr} {x y z w v : Val}
    {ma mb mc md me : ℕ} (ha : Lv P env T a x ma) (hb : Lv P env T b y mb) (hc : Lv P env T c z mc)
    (hd : Lv P env T d w md) (he : Lv P env T e v me) (hT : 5 ≤ T) :
    Lv P env T (GI.Degree.mk5 a b c d e) (.list [x, y, z, w, v])
      (2 * (2 * (2 * (2 * (2 * 1 + 3 * ma + 1) + 3 * mb + 1) + 3 * mc + 1) + 3 * md + 1) +
        3 * me + 1) :=
  Lv.snoc (Lv.mk4 ha hb hc hd hT) he (by omega)

/-- **A table.** -/
theorem tab_spec {P : Program} {b : ℕ} {e : Expr} (h : P.HasAt b (tabFuns b e)) {m T K W : ℕ}
    {c : Val} {F : Fin m → Val} (hf : ∀ i : Fin m, Lv P [.list [c, .nat i]] T e (F i) K)
    (hW : (Val.list [c, ids m]).wt + (Val.list ((List.finRange m).map F)).wt + 1 ≤ W) :
    FunDet P b (.list [c, ids m]) (.list ((List.finRange m).map F))
      (m * (K * T) + mapK * (m + 1) * W) := by
  have hb : P.funs[b + 3]? = some e := by
    simpa [mapFuns, loopFuns] using h.right.single
  exact tab_cost h.left (fun i => funDet_of_lv hb (hf i)) hW

/-- **A table of numbers.** -/
theorem tabN_spec {P : Program} {b : ℕ} {e : Expr} (h : P.HasAt b (tabFuns b e)) {m T K W : ℕ}
    {c : Val} {f : Fin m → ℕ} (hf : ∀ i : Fin m, Lv P [.list [c, .nat i]] T e (.nat (f i)) K)
    (hW : (Val.list [c, ids m]).wt + (encFun f).wt + 1 ≤ W) :
    FunDet P b (.list [c, ids m]) (encFun f) (m * (K * T) + mapK * (m + 1) * W) :=
  tab_spec h hf hW

/-- The Boolean test on a number. -/
noncomputable def finTest {m : ℕ} (q : Fin m → Prop) (x : Val) : Bool :=
  open Classical in decide (∃ z : Fin m, x = .nat z ∧ q z)

open Classical in
theorem finTest_nat {m : ℕ} (q : Fin m → Prop) (z : Fin m) :
    finTest q (.nat z) = decide (q z) := by
  simp only [finTest, decide_eq_decide]
  constructor
  · rintro ⟨y, hy, h⟩
    have : y = z := Fin.ext (by simpa using hy.symm)
    exact this ▸ h
  · exact fun h => ⟨z, rfl, h⟩

open Classical in
theorem any_finTest {m : ℕ} (q : Fin m → Prop) :
    ((List.finRange m).map fun i : Fin m => Val.nat (i : ℕ)).any (finTest q) =
      decide (∃ z, q z) := by
  simp only [List.any_map, decide_eq_true_eq]
  rw [Bool.eq_iff_iff]
  simp [finTest_nat]

open Classical in
/-- **Is there a point that passes the test?** -/
theorem anyFin_spec {P : Program} {b p : ℕ} (h : P.HasAt b (anyFuns b p)) {m B : ℕ} {c : Val}
    (q : Fin m → Prop) (hp : ∀ z : Fin m, FunDet P p (.list [c, .nat z]) (boolVal (decide (q z))) B) :
    FunDet P b (.list [c, ids m]) (.nat (if ∃ z, q z then 1 else 0))
      (m * B + loopModK * (m + 1) * ((Val.list [c, ids m]).wt + m + 4)) := by
  have hs := any_spec (c := c) (xs := (List.finRange m).map fun i : Fin m => Val.nat (i : ℕ)) h
    (q := finTest q) (B := fun _ => B) (by
      intro x hx
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
      rw [finTest_nat]
      exact hp z)
  refine hs.mono fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, any_finTest]
    by_cases h : ∃ z, q z <;> simp [h]
  · have h2 := hw.2
    simp only [List.map_map, List.length_map, List.length_finRange, sum_const_finRange] at h2
    exact h2

/-- A list of points as a value. -/
def flist {m : ℕ} (l : List (Fin m)) : Val := .list (l.map fun z : Fin m => .nat (z : ℕ))

open Classical in
theorem filter_finTest {m : ℕ} (q : Fin m → Prop) :
    ((List.finRange m).map fun i : Fin m => Val.nat (i : ℕ)).filter (finTest q) =
      ((List.finRange m).filter fun z : Fin m => decide (q z)).map fun z : Fin m => Val.nat (z : ℕ) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro z _
  simp [finTest_nat]

open Classical in
/-- **The points that pass the test.** -/
theorem filterFin_spec {P : Program} {b p : ℕ} (h : P.HasAt b (filterFuns b p)) {m B W : ℕ}
    {c : Val} (q : Fin m → Prop)
    (hp : ∀ z : Fin m, FunDet P p (.list [c, .nat z]) (boolVal (decide (q z))) B)
    (hW : (Val.list [c, ids m]).wt + m +
      (flist ((List.finRange m).filter fun z : Fin m => decide (q z))).wt + 1 ≤ W) :
    FunDet P b (.list [c, ids m]) (flist ((List.finRange m).filter fun z : Fin m => decide (q z)))
      (m * B + loopModK * (m + 1) * W) := by
  have hs := filter_spec (c := c) (xs := (List.finRange m).map fun i : Fin m => Val.nat (i : ℕ)) h
    (q := finTest q) (B := fun _ => B) (by
      intro x hx
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
      rw [finTest_nat]
      exact hp z)
  refine hs.mono fun w cost hw => ?_
  obtain ⟨rfl, h2⟩ := hw
  rw [filter_finTest] at h2 ⊢
  simp only [List.map_map, List.length_map, List.length_finRange, sum_const_finRange] at h2
  refine ⟨rfl, h2.trans ?_⟩
  have := Nat.mul_le_mul_left (loopModK * (m + 1)) hW
  have e : (Val.list [c, .list ((List.finRange m).map fun i : Fin m => Val.nat (i : ℕ))]).wt =
    (Val.list [c, ids m]).wt := rfl
  rw [e]
  exact Nat.add_le_add_left this _

open Classical in
theorem findIdx_finTest {m : ℕ} (q : Fin m → Prop) :
    ((List.finRange m).map fun i : Fin m => Val.nat (i : ℕ)).findIdx (finTest q) =
      (List.finRange m).findIdx fun z : Fin m => decide (q z) := by
  rw [List.findIdx_map]
  congr 1
  funext z
  simp [finTest_nat]

open Classical in
/-- **The first point that passes the test.** -/
theorem findFin_spec {P : Program} {b p : ℕ} (h : P.HasAt b (findFuns b p)) {m B : ℕ} {c : Val}
    (q : Fin m → Prop) (hp : ∀ z : Fin m, FunDet P p (.list [c, .nat z]) (boolVal (decide (q z))) B) :
    FunDet P b (.list [c, ids m]) (.nat ((List.finRange m).findIdx fun z : Fin m => decide (q z)))
      (m * B + loopModK * (m + 1) * ((Val.list [c, ids m]).wt + 2 * m + 3)) := by
  have hs := find_spec (c := c) (xs := (List.finRange m).map fun i : Fin m => Val.nat (i : ℕ)) h
    (q := finTest q) (B := fun _ => B) (by
      intro x hx
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
      rw [finTest_nat]
      exact hp z)
  refine hs.mono fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, findIdx_finTest]
  · have h2 := hw.2
    simp only [List.map_map, List.length_map, List.length_finRange, sum_const_finRange] at h2
    exact h2

open Classical in
/-- The first point that passes the test is below `m` and passes it, if there is one. -/
theorem findIdx_finRange {m : ℕ} (q : Fin m → Prop) (h : ∃ z, q z) :
    ∃ hi : (List.finRange m).findIdx (fun z : Fin m => decide (q z)) < m,
      q ⟨_, hi⟩ := by
  have h1 : (List.finRange m).findIdx (fun z : Fin m => decide (q z)) < (List.finRange m).length := by
    obtain ⟨z, hz⟩ := h
    exact List.findIdx_lt_length_of_exists ⟨z, List.mem_finRange z, by simpa using hz⟩
  have h2 := List.findIdx_getElem (w := h1)
  simp only [List.getElem_finRange, decide_eq_true_eq] at h2
  simp only [List.length_finRange] at h1
  refine ⟨h1, ?_⟩
  simpa using h2

theorem findIdx_finRange_le {m : ℕ} (q : Fin m → Bool) :
    (List.finRange m).findIdx q ≤ m := by
  simpa using List.findIdx_le_length (xs := List.finRange m) (p := q)

/-- **A map over a list, for an injective code.** -/
theorem mapInj_spec {α : Type} {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    (L : List α) (enc res : α → Val) (henc : Function.Injective enc) {B W : ℕ}
    (hf : ∀ a ∈ L, FunDet P f (.list [c, enc a]) (res a) B)
    (hW : (Val.list [c, .list (L.map enc)]).wt + (Val.list (L.map res)).wt + 1 ≤ W) :
    FunDet P b (.list [c, .list (L.map enc)]) (.list (L.map res))
      (L.length * B + mapK * (L.length + 1) * W) := by
  have hM := map_spec (c := c) (xs := L.map enc) h
    (R := fun x w => ∀ a, x = enc a → w = res a) (B := fun _ => B) (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      refine FunAll.mono (hf a ha) fun w c hw => ⟨fun a' ha' => ?_, hw.2⟩
      rw [hw.1, henc ha'])
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = L.map res := forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
  subst hws'
  refine ⟨rfl, hc.trans ?_⟩
  have h1 : ((L.map enc).map fun _ => B).sum = L.length * B := by
    simp [Function.comp_def]
  rw [h1]
  have h2 := Nat.mul_le_mul_left (mapK * ((L.map enc).length + 1)) hW
  simp only [List.length_map] at h2 ⊢
  omega

end GI.Degree
