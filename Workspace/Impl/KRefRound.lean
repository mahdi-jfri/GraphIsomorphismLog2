import Workspace.Impl.KRefRoundV

/-!
# The modules of one round

* `cnts`: on `[rl, range M]`, how often each `u < M` occurs in `rl`;
* `vcs`: on `[[A, B], upd]`, for each list of indices in `upd`, the Horner code of the colors
  at these indices (the vector codes of one tuple);
* `vtab`: on `[[A, B], nbs]`, the vector codes of all tuples;
* `sig`: on `[[A, B, VAll, range M], nb]`, the signature code of one tuple;
* `stab`: on `[[A, B, VAll, range M], nbs]`, the signature codes of all tuples.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (len)

variable {n k : ℕ}

/-! ### Counts -/

/-- On `[rl, u]`: the number of entries of `rl` equal to `u`, by the count module at `cnt`. -/
def krefCntE (cnt : ℕ) : Expr := .call cnt (mk2 (arg 1) (arg 0))

/-- `cnts`, at base `b` (nine functions). -/
def krefCntsFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [krefCntE (b + 4)] ++ countFuns (b + 4)

def krefCntK : ℕ := countK + 100

def krefCntsK : ℕ := mapK * (3 * krefCntK + 11) * 2 ^ 5

/-- **Counts.** -/
theorem kref_cnts {P : Program} {b : ℕ} (h : P.HasAt b (krefCntsFuns b)) {rl : List ℕ} {M Y : ℕ}
    (hrl : ∀ a ∈ rl, a ≤ Y) (hl : rl.length ≤ Y) (hM : M ≤ Y) (hw : (natList rl).wt ≤ Y)
    (hwM : (natList (List.range M)).wt ≤ Y) :
    FunDet P b (.list [natList rl, natList (List.range M)])
      (natList ((List.range M).map rl.count)) (krefCntsK * (Y + 1) ^ 5) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left.left
  have hE : P.funs[b + 3]? = some (krefCntE (b + 4)) := by
    simpa [krefCntsFuns, mapFuns, loopFuns] using h.left.right.single
  have hc : P.HasAt (b + 4) (countFuns (b + 4)) := by
    simpa [krefCntsFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right
  have hbody : ∀ u ∈ List.range M, FunDet P (b + 3) (.list [natList rl, .nat u])
      (.nat (rl.count u)) (krefCntK * (Y + 1) ^ 3) := by
    intro u hu
    have hu' := List.mem_range.mp hu
    have hcnt := count_spec hc (xs := rl) (j := u) (B := Y) hrl (by omega) hl
    have hWA : (Val.list [natList rl, .nat u]).wt ≤ 4 * Y + 8 := by
      have := wt_list2_le (natList rl) (.nat u); have := wt_nat_le u; omega
    set A : List Val := [natList rl, .nat u] with hA
    have d0 : Det P [.list A] (arg 0) (natList rl) (2 * (Val.list A).wt + 0 + 5) := Det.arg' rfl
    have d1 : Det P [.list A] (arg 1) (.nat u) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
    have hcall := Det.call (Det.mk2 d1 d0) hcnt
    refine FunDet.intro hE (hcall.mono ?_)
    have := wt_list2_le (.nat u) (natList rl)
    have := wt_nat_le u
    have := wt_nat_le (rl.count u)
    have : rl.count u ≤ rl.length := List.count_le_length
    have hT : Y + 1 ≤ (Y + 1) ^ 3 := kref_le_pow (by norm_num)
    have e : krefCntK * (Y + 1) ^ 3 = countK * (Y + 1) ^ 3 + 100 * (Y + 1) ^ 3 := by
      unfold krefCntK; ring
    rw [e]
    omega
  have hm := kref_mapL hmap (l := List.range M) (enc := Val.nat) (F := fun u => .nat (rl.count u))
    (Y := Y) (A := 1) (K := krefCntK) (d := 3) (by norm_num)
    (fun a _ a' _ haa => by cases haa; rfl) hbody (by omega)
    (by have : (Val.list ((List.range M).map Val.nat)).wt = (natList (List.range M)).wt := rfl
        omega)
  have e : Val.list ((List.range M).map fun u => Val.nat (rl.count u)) =
      natList ((List.range M).map rl.count) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [e] at hm
  exact hm.mono (le_of_eq (by unfold krefCntsK; ring))

/-! ### Vector codes -/

/-- On `[[A, B], is]`: the Horner code in base `B` of the entries of `A` at `is`. -/
def krefVcF (look hor : ℕ) : Expr :=
  .call hor (mk3 (.get (arg 0) (.nat 1)) (.call look (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.nat 0))

def krefVcK : ℕ := krefHorK + krefLookK + 200

/-- Bounds for one list of indices. -/
structure KrefVcOK (Y : ℕ) (A : List ℕ) (B : ℕ) (is : List ℕ) : Prop where
  lt : ∀ i ∈ is, i < A.length
  wis : (natList is).wt ≤ Y
  wlook : (natList (is.map fun i => A.getD i 0)).wt ≤ Y
  whor : (Val.nat (krefHorner B (is.map fun i => A.getD i 0))).wt ≤ Y

theorem kref_vcF {P : Program} {g look hor : ℕ} (hg : P.funs[g]? = some (krefVcF look hor))
    (hl : P.HasAt look (krefLookFuns look)) (hh : P.HasAt hor (krefHorFuns hor))
    {A is : List ℕ} {B Y : ℕ} (hB : 1 ≤ B) (hc : (Val.list [natList A, .nat B]).wt ≤ Y)
    (hok : KrefVcOK Y A B is) :
    FunDet P g (.list [.list [natList A, .nat B], natList is])
      (.nat (krefHorner B (is.map fun i => A.getD i 0))) (krefVcK * (Y + 1) ^ 3) := by
  have hwA : (natList A).wt ≤ Y := (wt_le_wt_list (by simp)).le.trans hc
  have hwB : (Val.nat B).wt ≤ Y := (wt_le_wt_list (by simp)).le.trans hc
  have hlk := kref_look hl hok.lt hwA hok.wis
  have hhr := kref_hor hh (a := 0) (ds := is.map fun i => A.getD i 0) hB hwB hok.whor hok.wlook
  have hWA : (Val.list [.list [natList A, .nat B], natList is]).wt ≤ 4 * Y + 6 := by
    have := wt_list2_le (.list [natList A, .nat B]) (natList is); have := hok.wis; omega
  set V : List Val := [.list [natList A, .nat B], natList is] with hV
  have dA : Det P [.list V] (.get (arg 0) (.nat 0)) (natList A) (3 * (Val.list V).wt + 0 + 0 + 9) :=
    Det.arg2 rfl rfl
  have dB : Det P [.list V] (.get (arg 0) (.nat 1)) (.nat B) (3 * (Val.list V).wt + 0 + 1 + 9) :=
    Det.arg2 rfl rfl
  have di : Det P [.list V] (arg 1) (natList is) (2 * (Val.list V).wt + 1 + 5) := Det.arg' rfl
  have d1 := Det.call (Det.mk2 dA di) hlk
  have d2 := Det.call (Det.mk3 dB d1 (Det.nat 0)) hhr
  refine FunDet.intro hg (d2.mono ?_)
  have := wt_list2_le (natList A) (natList is)
  have := wt_list3_le (.nat B) (natList (is.map fun i => A.getD i 0)) (.nat 0)
  have := wt_nat_le 0
  have := hok.wlook
  have hwh := hok.whor
  rw [krefHorner] at hwh
  have := hok.wis
  have hT : Y + 1 ≤ (Y + 1) ^ 3 := kref_le_pow (by norm_num)
  have e : krefVcK * (Y + 1) ^ 3 =
      krefHorK * (Y + 1) ^ 3 + krefLookK * (Y + 1) ^ 3 + 200 * (Y + 1) ^ 3 := by
    unfold krefVcK; ring
  rw [e]
  omega

/-- `vcs`, at base `b` (four functions). -/
def krefVcsFuns (b look hor : ℕ) : List Expr := mapFuns b (b + 3) ++ [krefVcF look hor]

def krefVcsK : ℕ := mapK * (3 * krefVcK + 11) * 2 ^ 5

/-- **Vector codes of one tuple.** -/
theorem kref_vcs {P : Program} {b look hor : ℕ} (h : P.HasAt b (krefVcsFuns b look hor))
    (hl : P.HasAt look (krefLookFuns look)) (hh : P.HasAt hor (krefHorFuns hor))
    {A : List ℕ} {Us : List (List ℕ)} {B Y : ℕ} (hB : 1 ≤ B)
    (hc : (Val.list [natList A, .nat B]).wt ≤ Y) (hok : ∀ is ∈ Us, KrefVcOK Y A B is)
    (hUs : (Val.list (Us.map natList)).wt ≤ Y) :
    FunDet P b (.list [.list [natList A, .nat B], .list (Us.map natList)])
      (natList (Us.map fun is => krefHorner B (is.map fun i => A.getD i 0)))
      (krefVcsK * (Y + 1) ^ 5) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hg : P.funs[b + 3]? = some (krefVcF look hor) := by
    simpa [krefVcsFuns, mapFuns, loopFuns] using h.right.single
  have hm := kref_mapL hmap (l := Us) (enc := natList)
    (F := fun is => .nat (krefHorner B (is.map fun i => A.getD i 0)))
    (Y := Y) (A := 1) (K := krefVcK) (d := 3) (by norm_num)
    (fun a _ a' _ haa => by rw [natList_inj haa]) (fun is his => kref_vcF hg hl hh hB hc (hok is his))
    (by omega) (by omega)
  have e : Val.list (Us.map fun is => Val.nat (krefHorner B (is.map fun i => A.getD i 0))) =
      natList (Us.map fun is => krefHorner B (is.map fun i => A.getD i 0)) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [e] at hm
  exact hm.mono (le_of_eq (by unfold krefVcsK; ring))

/-! ### Weights of the table -/

theorem kref_wt_updIs (x : Fin k → Fin n) (z : Fin n) :
    (natList ((List.finRange k).map fun i => krefIdx (Function.update x i z))).wt ≤
      7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by simp [k_le_krefX]) (fun a ha => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact (krefIdx_lt _).le.trans N_le_krefX)

theorem kref_wt_upd (x : Fin k → Fin n) :
    (Val.list ((krefUpd x).map natList)).wt ≤ 20 * krefX n k ^ 3 := by
  have h := kref_wt_listMap (l := krefUpd x) (f := natList) (C := 7 * krefX n k ^ 2) (fun is his => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp his; exact kref_wt_updIs x z)
  have hl : (krefUpd x).length = n := by simp [krefUpd]
  rw [hl] at h
  obtain ⟨hX2, hX12, hX23, -, -⟩ := kref_X4 (n := n) (k := k)
  have := @n_le_krefX n k
  have : n * (7 * krefX n k ^ 2) ≤ 7 * krefX n k ^ 3 := by
    rw [show krefX n k ^ 3 = krefX n k * krefX n k ^ 2 by ring]; nlinarith
  omega

theorem kref_wt_pat (x : Fin k → Fin n) : (natList (krefPat x)).wt ≤ 7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by simp [krefPat, krefDig, k_le_krefX]) (fun a ha => by
    unfold krefPat at ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    have := List.findIdx_le_length (p := fun y => decide (y = b)) (xs := krefDig x)
    rw [length_krefDig] at this
    exact this.trans k_le_krefX)

theorem kref_wt_tidx (x : Fin k → Fin n) : (natList (krefTidx x)).wt ≤ 7 * krefX n k ^ 2 :=
  kref_wt_natList_X (by simp [krefTidx, length_krefTups, kk_le_krefX]) (fun a ha => by
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp ha
    exact (krefIdx_lt _).le.trans N_le_krefX)

theorem kref_wt_nbVal (x : Fin k → Fin n) : (krefNbVal x).wt ≤ 60 * krefX n k ^ 3 := by
  have h := wt_list4_le (.nat (krefIdx x)) (natList (krefPat x)) (natList (krefTidx x))
    (.list ((krefUpd x).map natList))
  have := wt_nat_le (krefIdx x); have := (krefIdx_lt x).le.trans N_le_krefX
  have := kref_wt_pat x; have := kref_wt_tidx x; have := kref_wt_upd x
  obtain ⟨hX2, hX12, hX23, -, -⟩ := kref_X4 (n := n) (k := k)
  have : krefX n k ^ 2 ≤ krefX n k ^ 3 := hX23
  have : 2 * krefX n k ^ 2 ≤ krefX n k ^ 3 := by
    rw [show krefX n k ^ 3 = krefX n k * krefX n k ^ 2 by ring]; nlinarith
  unfold krefNbVal
  omega

theorem kref_wt_nbs : (krefNbs n k).wt ≤ 130 * krefX n k ^ 4 := by
  have h := kref_wt_listMap (l := krefTups n k) (f := krefNbVal) (C := 60 * krefX n k ^ 3)
    (fun x _ => kref_wt_nbVal x)
  rw [length_krefTups] at h
  obtain ⟨hX2, hX12, hX23, hX34, -⟩ := kref_X4 (n := n) (k := k)
  have := @N_le_krefX n k
  have : n ^ k * (60 * krefX n k ^ 3) ≤ 60 * krefX n k ^ 4 := by
    rw [show krefX n k ^ 4 = krefX n k * krefX n k ^ 3 by ring]; nlinarith
  unfold krefNbs
  omega

/-! ### The vector codes of all tuples -/

/-- On `[[A, B], nb]`: the vector codes of the tuple of `nb`. -/
def krefVtabE (vcs : ℕ) : Expr := .call vcs (mk2 (arg 0) (.get (arg 1) (.nat 3)))

/-- `vtab`, at base `b` (four functions). -/
def krefVtabFuns (b vcs : ℕ) : List Expr := mapFuns b (b + 3) ++ [krefVtabE vcs]

def krefVtabEK : ℕ := 4 * krefVcsK + 100

def krefVtabK : ℕ := mapK * (3 * krefVtabEK + 11) * 2 ^ 7

theorem krefNbVal_inj {x y : Fin k → Fin n} (h : krefNbVal x = krefNbVal y) : x = y := by
  unfold krefNbVal at h
  simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq] at h
  exact finFunctionFinEquiv.injective (Fin.ext h.1)

section Tab

variable {col : KCol n k} (hs : KrefSmall col)

include hs

theorem kref_wt_ctxAB (β : Bool) :
    (Val.list [natList (krefAv col β), .nat (krefB n k)]).wt ≤ 30 * krefX n k ^ 2 := by
  have := wt_list2_le (natList (krefAv col β)) (.nat (krefB n k))
  have := kref_wt_Av hs β; have := kref_wt_B hs
  obtain ⟨hX2, hX12, -, -, -⟩ := kref_X4 (n := n) (k := k)
  omega

theorem kref_vcOK (β : Bool) (x : Fin k → Fin n) :
    ∀ is ∈ krefUpd x, KrefVcOK (krefZ n k) (krefAv col β) (krefB n k) is := by
  intro is his
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp his
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    rw [length_krefAv]; exact krefIdx_lt _
  · have := kref_wt_updIs x z; omega
  · rw [kref_look_upd]
    have h := kref_wt_natList_C (xs := krefVec col β x z) (C := 3 * krefX n k) (fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha; exact kref_wt_col hs β _)
    have hl : (krefVec col β x z).length = k := by simp [krefVec]
    rw [hl] at h
    have := @k_le_krefX n k
    have : k * (3 * krefX n k) ≤ 3 * krefX n k ^ 2 := by rw [sq]; nlinarith
    omega
  · rw [kref_look_upd]; have := kref_wt_vcode hs β x z; omega

omit hs in
theorem kref_vcs_eq (β : Bool) (x : Fin k → Fin n) :
    (krefUpd x).map (fun is => krefHorner (krefB n k) (is.map fun i => (krefAv col β).getD i 0)) =
      krefVcs col β x := by
  simp only [krefUpd, List.map_map, krefVcs, List.ofFn_eq_map]
  apply List.map_congr_left
  intro z _
  simp only [Function.comp_apply]
  rw [← kref_look_upd col β x z, List.map_map]

/-- **Vector codes of all tuples.** -/
theorem kref_vtab {P : Program} {b vcs look hor : ℕ} (h : P.HasAt b (krefVtabFuns b vcs))
    (hv : P.HasAt vcs (krefVcsFuns vcs look hor))
    (hl : P.HasAt look (krefLookFuns look)) (hh : P.HasAt hor (krefHorFuns hor)) (β : Bool) :
    FunDet P b (.list [.list [natList (krefAv col β), .nat (krefB n k)], krefNbs n k])
      (.list ((krefTups n k).map fun x => natList (krefVcs col β x)))
      (krefVtabK * (krefZ n k + 1) ^ 7) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hg : P.funs[b + 3]? = some (krefVtabE vcs) := by
    simpa [krefVtabFuns, mapFuns, loopFuns] using h.right.single
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  have hc := kref_wt_ctxAB hs β
  have hB1 : 1 ≤ krefB n k := by unfold krefB; omega
  have hbody : ∀ x ∈ krefTups n k, FunDet P (b + 3)
      (.list [.list [natList (krefAv col β), .nat (krefB n k)], krefNbVal x])
      (natList (krefVcs col β x)) (krefVtabEK * (krefZ n k + 1) ^ 5) := by
    intro x _
    have hvc := kref_vcs hv hl hh (Us := krefUpd x) (Y := krefZ n k) hB1 (by omega)
      (kref_vcOK hs β x) (by have := kref_wt_upd x; omega)
    rw [kref_vcs_eq] at hvc
    have hwx := kref_wt_nbVal x
    have hWA : (Val.list [.list [natList (krefAv col β), .nat (krefB n k)], krefNbVal x]).wt ≤
        krefZ n k := by
      have := wt_list2_le (.list [natList (krefAv col β), .nat (krefB n k)]) (krefNbVal x)
      omega
    set V : List Val := [.list [natList (krefAv col β), .nat (krefB n k)], krefNbVal x] with hV
    have d0 : Det P [.list V] (arg 0) (.list [natList (krefAv col β), .nat (krefB n k)])
        (2 * (Val.list V).wt + 0 + 5) := Det.arg' rfl
    have d1 : Det P [.list V] (.get (arg 1) (.nat 3)) (.list ((krefUpd x).map natList))
        (3 * (Val.list V).wt + 1 + 3 + 9) := Det.arg2 rfl rfl
    have hcall := Det.call (Det.mk2 d0 d1) hvc
    refine FunDet.intro hg (hcall.mono ?_)
    have := wt_list2_le (.list [natList (krefAv col β), .nat (krefB n k)])
      (.list ((krefUpd x).map natList))
    have := kref_wt_upd x
    have := kref_wt_vcs hs β x
    have hT : krefZ n k + 1 ≤ (krefZ n k + 1) ^ 5 := kref_le_pow (by norm_num)
    have e : krefVtabEK * (krefZ n k + 1) ^ 5 =
        4 * (krefVcsK * (krefZ n k + 1) ^ 5) + 100 * (krefZ n k + 1) ^ 5 := by
      unfold krefVtabEK; ring
    rw [e]
    omega
  have hm := kref_mapL hmap (l := krefTups n k) (enc := krefNbVal)
    (F := fun x => natList (krefVcs col β x)) (Y := krefZ n k) (A := 1) (K := krefVtabEK) (d := 5)
    (by norm_num) (fun a _ a' _ haa => by rw [krefNbVal_inj haa]) hbody (by omega)
    (by have := kref_wt_nbs (n := n) (k := k); unfold krefNbs at this; omega)
  exact hm.mono (le_of_eq (by unfold krefVtabK; ring))

end Tab

end GI.Impl
