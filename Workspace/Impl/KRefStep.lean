import Workspace.Impl.KRefSig

/-!
# One round of the refinement

The state of a round is `[A0, A1]`, the two colorings as lists (`krefSt col`). The round body
`krefRoundG`, on `[[nbs, B, range M], i, [A0, A1]]`, computes
1. the vector codes of both inputs (`vtab`) and all of them joined (`flat`, `append`): `VAll`;
2. the signature codes of both inputs (`stab`) and all of them joined: `SAll`;
3. the ranks of the signature codes of each input among `SAll` (`ranks`).
The result is the state of `krefStep col` (`kref_roundG`).
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (len)

variable {n k : ℕ}

/-! ### The signature codes of all tuples -/

/-- `stab`, at base `b` (four functions). -/
def krefStabFuns (b look hor ranks cnts vcs : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [krefSigF look hor ranks cnts vcs]

def krefStabK : ℕ := mapK * (3 * krefSigK + 11) * 2 ^ 7

section Stab

variable {col : KCol n k} (hs : KrefSmall col)

include hs

/-- **The signature codes of all tuples.** -/
theorem kref_stab {P : Program} {b look hor ranks cnts vcs : ℕ}
    (h : P.HasAt b (krefStabFuns b look hor ranks cnts vcs))
    (hat : KrefSigAt P look hor ranks cnts vcs) (β : Bool) :
    FunDet P b (.list [krefSigCtx col β, krefNbs n k]) (natList (krefSCodes col β))
      (krefStabK * (krefZ n k + 1) ^ 7) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hg : P.funs[b + 3]? = some (krefSigF look hor ranks cnts vcs) := by
    simpa [krefStabFuns, mapFuns, loopFuns] using h.right.single
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  have hm := kref_mapL hmap (l := krefTups n k) (enc := krefNbVal)
    (F := fun x => .nat (krefHorner (krefB n k) (krefSig col β x))) (Y := krefZ n k) (A := 1)
    (K := krefSigK) (d := 5) (by norm_num) (fun a _ a' _ haa => by rw [krefNbVal_inj haa])
    (fun x _ => kref_sigF hs hg hat β x) (by have := kref_wt_sigCtx hs β; omega)
    (by have := kref_wt_nbs (n := n) (k := k); unfold krefNbs at this; omega)
  have e : Val.list ((krefTups n k).map fun x => Val.nat (krefHorner (krefB n k) (krefSig col β x)))
      = natList (krefSCodes col β) := by
    simp [natList, krefSCodes, List.map_map, Function.comp_def]
  rw [e] at hm
  exact hm.mono (le_of_eq (by unfold krefStabK; ring))

end Stab

/-! ### The round -/

/-- The round body. -/
def krefRoundG (vtab flat app stab ranks : ℕ) : Expr :=
  .letE (.call vtab (mk2 (mk2 (.get (arg 2) (.nat 0)) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 0))))
   (.letE (.call vtab (mk2 (mk2 (.get (arg 2) (.nat 1)) (.get (arg 0) (.nat 1)))
      (.get (arg 0) (.nat 0))))
    (.letE (.call app (mk2 (.call flat (mk3 (.nat 0) (.var 1) .nil))
        (.call flat (mk3 (.nat 0) (.var 2) .nil))))
     (.letE (.call stab (mk2 (mk4 (.get (arg 2) (.nat 0)) (.get (arg 0) (.nat 1)) (.var 3)
          (.get (arg 0) (.nat 2))) (.get (arg 0) (.nat 0))))
      (.letE (.call stab (mk2 (mk4 (.get (arg 2) (.nat 1)) (.get (arg 0) (.nat 1)) (.var 3)
          (.get (arg 0) (.nat 2))) (.get (arg 0) (.nat 0))))
       (.letE (.call app (mk2 (.var 4) (.var 5)))
        (mk2 (.call ranks (mk2 (.var 6) (.var 4))) (.call ranks (mk2 (.var 6) (.var 5)))))))))

/-- Where the modules used by the round sit. -/
structure KrefRoundAt (P : Program) (look hor ranks cnts vcs vtab flat app stab : ℕ) : Prop where
  hsig : KrefSigAt P look hor ranks cnts vcs
  hvtab : P.HasAt vtab (krefVtabFuns vtab vcs)
  hflat : P.HasAt flat (krefFlatFuns flat)
  happ : P.HasAt app (appendFuns app)
  hstab : P.HasAt stab (krefStabFuns stab look hor ranks cnts vcs)

def krefRoundK : ℕ :=
  30 * (krefVtabK + krefFlatK + krefAppK + krefStabK + krefRanksK) + 100000

/-- The fixed part of the round's input. -/
def krefRCtx (n k : ℕ) : Val :=
  .list [krefNbs n k, .nat (krefB n k), natList (List.range (krefM n k))]

/-- The state of a round. -/
def krefSt (col : KCol n k) : Val :=
  .list [natList (krefAv col false), natList (krefAv col true)]

theorem kref_wt_RCtx : (krefRCtx n k).wt ≤ 340 * krefX n k ^ 4 := by
  have h := wt_list3_le (krefNbs n k) (.nat (krefB n k)) (natList (List.range (krefM n k)))
  have h1 := kref_wt_nbs (n := n) (k := k)
  have h2 : (Val.nat (krefB n k)).wt ≤ 3 * krefX n k := by
    have := wt_nat_le (krefB n k); have : krefB n k ≤ 2 * krefX n k := by unfold krefB krefX; omega
    have := @krefX_two n k; omega
  have hM : krefM n k ≤ 2 * krefX n k ^ 2 := by
    unfold krefM
    have h1 := @N_le_krefX n k; have h2 := @n_le_krefX n k
    have : n ^ k * n ≤ krefX n k ^ 2 := by rw [sq]; exact Nat.mul_le_mul h1 h2
    rw [Nat.mul_assoc]; omega
  have h3 := kref_wt_range (n := n) (k := k) hM
  obtain ⟨hX2, hX12, hX23, hX34, -⟩ := kref_X4 (n := n) (k := k)
  unfold krefRCtx
  omega

theorem kref_natList_flatten (Ls : List (List ℕ)) :
    Val.list (Ls.map natList) = Val.list ((Ls.map fun l => l.map Val.nat).map Val.list) := by
  simp [natList, List.map_map, Function.comp_def]

theorem kref_flatten_natList (Ls : List (List ℕ)) :
    Val.list (Ls.map fun l => l.map Val.nat).flatten = natList Ls.flatten := by
  simp [natList, List.map_flatten]

theorem kref_natList_append (a b : List ℕ) :
    Val.list ((a.map Val.nat) ++ (b.map Val.nat)) = natList (a ++ b) := by
  simp [natList]

section Round

variable {col : KCol n k} (hs : KrefSmall col)

include hs

theorem kref_wt_St : (krefSt col).wt ≤ 50 * krefX n k ^ 2 := by
  have := wt_list2_le (natList (krefAv col false)) (natList (krefAv col true))
  obtain ⟨hX2, hX12, -, -, -⟩ := kref_X4 (n := n) (k := k)
  have := kref_wt_Av hs false; have := kref_wt_Av hs true
  unfold krefSt; omega

omit hs in
theorem kref_VCodes_sub (β : Bool) : List.Sublist (krefVCodes col β).flatten (krefVAll col) := by
  cases β
  · exact List.sublist_append_left _ _
  · exact List.sublist_append_right _ _

end Round

theorem kref_vt_eq (col : KCol n k) (β : Bool) :
    Val.list ((krefTups n k).map fun x => natList (krefVcs col β x)) =
      Val.list ((((krefTups n k).map (krefVcs col β)).map fun l => l.map Val.nat).map Val.list) := by
  simp [natList, List.map_map, Function.comp_def]

theorem kref_small_step {col : KCol n k} : KrefSmall (krefStep col) := fun β x =>
  (krefStep_lt (col := col) β x).le

/-- **One round.** -/
theorem kref_roundG {P : Program} {g look hor ranks cnts vcs vtab flat app stab : ℕ}
    (hg : P.funs[g]? = some (krefRoundG vtab flat app stab ranks))
    (hat : KrefRoundAt P look hor ranks cnts vcs vtab flat app stab)
    {col : KCol n k} (hs : KrefSmall col) {i : ℕ} (hi : i ≤ 2 * n ^ k) :
    FunDet P g (.list [krefRCtx n k, .nat i, krefSt col]) (krefSt (krefStep col))
      (krefRoundK * (krefZ n k + 1) ^ 7) := by
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  have hN := @N_le_krefX n k
  -- weights
  have wR := kref_wt_RCtx (n := n) (k := k)
  have wSt := kref_wt_St hs
  have wi := wt_nat_le i
  have wvt0 := kref_wt_vtab hs false
  have wvt1 := kref_wt_vtab hs true
  have wfl0 := kref_wt_VAll_sub hs (kref_VCodes_sub (col := col) false)
  have wfl1 := kref_wt_VAll_sub hs (kref_VCodes_sub (col := col) true)
  have wVA := kref_wt_VAll hs
  have wsc0 := kref_wt_SCodes hs false
  have wsc1 := kref_wt_SCodes hs true
  have wSA := kref_wt_SAll hs
  have wn0 := kref_wt_Av (kref_small_step (col := col)) false
  have wn1 := kref_wt_Av (kref_small_step (col := col)) true
  have wA0 := kref_wt_Av hs false
  have wA1 := kref_wt_Av hs true
  have wB := kref_wt_B hs
  have wsx0 := kref_wt_sigCtx hs false
  have wsx1 := kref_wt_sigCtx hs true
  have wnbs := kref_wt_nbs (n := n) (k := k)
  have wrg := kref_wt_range (n := n) (k := k) (kref_M_le hs)
  have hSAl : (krefSAll col).length + 2 ≤ krefZ n k := by rw [length_krefSAll]; omega
  -- the module calls
  have cvt : ∀ β, FunDet P vtab (.list [.list [natList (krefAv col β), .nat (krefB n k)],
      krefNbs n k]) (.list ((((krefTups n k).map (krefVcs col β)).map fun l =>
        l.map Val.nat).map Val.list)) (krefVtabK * (krefZ n k + 1) ^ 7) := fun β => by
    rw [← kref_vt_eq]
    exact kref_vtab hs hat.hvtab hat.hsig.hvcs hat.hsig.hlook hat.hsig.hhor β
  have cfl : ∀ β, FunDet P flat (.list [.nat 0, .list ((((krefTups n k).map (krefVcs col β)).map
      fun l => l.map Val.nat).map Val.list), .list []]) (natList (krefVCodes col β).flatten)
      (krefFlatK * (krefZ n k + 1) ^ 4) := fun β => by
    have := kref_flat hat.hflat (c := .nat 0)
      (Ls := ((krefTups n k).map (krefVcs col β)).map fun l => l.map Val.nat) (Y := krefZ n k)
      (by have := wt_nat_le 0; omega)
      (by rw [← kref_vt_eq]; cases β <;> omega)
      (by rw [kref_flatten_natList, ← kref_vcodes_eq]; cases β <;> omega)
    rw [kref_flatten_natList, ← kref_vcodes_eq] at this
    exact this
  have cap1 : FunDet P app (.list [natList (krefVCodes col false).flatten,
      natList (krefVCodes col true).flatten]) (natList (krefVAll col))
      (krefAppK * (krefZ n k + 1) ^ 2) := by
    have := kref_app hat.happ (xs := (krefVCodes col false).flatten.map Val.nat)
      (ys := (krefVCodes col true).flatten.map Val.nat) (Y := krefZ n k)
      (by change (natList _).wt ≤ _; omega) (by change (natList _).wt ≤ _; omega)
      (by rw [kref_natList_append]; unfold krefVAll at wVA; omega)
    rw [kref_natList_append] at this
    exact this
  have cst : ∀ β, FunDet P stab (.list [krefSigCtx col β, krefNbs n k])
      (natList (krefSCodes col β)) (krefStabK * (krefZ n k + 1) ^ 7) := fun β =>
    kref_stab hs hat.hstab hat.hsig β
  have cap2 : FunDet P app (.list [natList (krefSCodes col false), natList (krefSCodes col true)])
      (natList (krefSAll col)) (krefAppK * (krefZ n k + 1) ^ 2) := by
    have := kref_app hat.happ (xs := (krefSCodes col false).map Val.nat)
      (ys := (krefSCodes col true).map Val.nat) (Y := krefZ n k)
      (by change (natList _).wt ≤ _; omega) (by change (natList _).wt ≤ _; omega)
      (by rw [kref_natList_append]; unfold krefSAll at wSA; omega)
    rw [kref_natList_append] at this
    exact this
  have crk : ∀ β, FunDet P ranks (.list [natList (krefSAll col), natList (krefSCodes col β)])
      (natList (krefAv (krefStep col) β)) (krefRanksK * (krefZ n k + 1) ^ 5) := fun β => by
    have := kref_ranks hat.hsig.hranks (L := krefSAll col) (qs := krefSCodes col β)
      (Y := krefZ n k) (by omega) (by cases β <;> omega) hSAl
    rw [kref_scodes_rank] at this
    exact this
  -- the environment
  have hWV : (Val.list [krefRCtx n k, .nat i, krefSt col]).wt ≤ krefZ n k := by
    have := wt_list3_le (krefRCtx n k) (.nat i) (krefSt col); omega
  set V : List Val := [krefRCtx n k, .nat i, krefSt col] with hV
  have gA0 : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 2) (.nat 0))
      (natList (krefAv col false)) (3 * (Val.list V).wt + 2 + 0 + 9) := fun _ => Det.arg2 rfl rfl
  have gA1 : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 2) (.nat 1))
      (natList (krefAv col true)) (3 * (Val.list V).wt + 2 + 1 + 9) := fun _ => Det.arg2 rfl rfl
  have gN : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 0) (.nat 0)) (krefNbs n k)
      (3 * (Val.list V).wt + 0 + 0 + 9) := fun _ => Det.arg2 rfl rfl
  have gB : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 0) (.nat 1))
      (.nat (krefB n k)) (3 * (Val.list V).wt + 0 + 1 + 9) := fun _ => Det.arg2 rfl rfl
  have gR : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 0) (.nat 2))
      (natList (List.range (krefM n k))) (3 * (Val.list V).wt + 0 + 2 + 9) :=
    fun _ => Det.arg2 rfl rfl
  -- the values
  set vt0 : Val := .list ((((krefTups n k).map (krefVcs col false)).map fun l =>
    l.map Val.nat).map Val.list) with hvt0
  set vt1 : Val := .list ((((krefTups n k).map (krefVcs col true)).map fun l =>
    l.map Val.nat).map Val.list) with hvt1
  have wv0 : vt0.wt ≤ 30 * krefX n k ^ 4 := by rw [hvt0, ← kref_vt_eq]; exact wvt0
  have wv1 : vt1.wt ≤ 30 * krefX n k ^ 4 := by rw [hvt1, ← kref_vt_eq]; exact wvt1
  -- the steps
  have s1 := Det.call (Det.mk2 (Det.mk2 (gA0 []) (gB [])) (gN [])) (cvt false)
  set E2 : List Val := [.list V, vt0] with hE2
  have s2 := Det.call (Det.mk2 (Det.mk2 (gA1 [vt0]) (gB [vt0])) (gN [vt0])) (cvt true)
  set E3 : List Val := E2 ++ [vt1] with hE3
  have v1 : Det P E3 (.var 1) vt0 (vt0.wt + 1) := Det.var' rfl
  have v2 : Det P E3 (.var 2) vt1 (vt1.wt + 1) := Det.var' rfl
  have f0 := Det.call (Det.mk3 (Det.nat 0) v1 Det.nil) (cfl false)
  have f1 := Det.call (Det.mk3 (Det.nat 0) v2 Det.nil) (cfl true)
  have s3 := Det.call (Det.mk2 f0 f1) cap1
  set E4 : List Val := E3 ++ [natList (krefVAll col)] with hE4
  have v3 : Det P E4 (.var 3) (natList (krefVAll col)) ((natList (krefVAll col)).wt + 1) :=
    Det.var' rfl
  have s4 := Det.call (Det.mk2 (Det.mk4 (gA0 [vt0, vt1, natList (krefVAll col)])
    (gB [vt0, vt1, natList (krefVAll col)]) v3 (gR [vt0, vt1, natList (krefVAll col)]))
    (gN [vt0, vt1, natList (krefVAll col)])) (cst false)
  set E5 : List Val := E4 ++ [natList (krefSCodes col false)] with hE5
  have v3' : Det P E5 (.var 3) (natList (krefVAll col)) ((natList (krefVAll col)).wt + 1) :=
    Det.var' rfl
  have s5 := Det.call (Det.mk2 (Det.mk4 (gA1 [vt0, vt1, natList (krefVAll col),
      natList (krefSCodes col false)])
    (gB [vt0, vt1, natList (krefVAll col), natList (krefSCodes col false)]) v3'
    (gR [vt0, vt1, natList (krefVAll col), natList (krefSCodes col false)]))
    (gN [vt0, vt1, natList (krefVAll col), natList (krefSCodes col false)])) (cst true)
  set E6 : List Val := E5 ++ [natList (krefSCodes col true)] with hE6
  have v4 : Det P E6 (.var 4) (natList (krefSCodes col false))
      ((natList (krefSCodes col false)).wt + 1) := Det.var' rfl
  have v5 : Det P E6 (.var 5) (natList (krefSCodes col true))
      ((natList (krefSCodes col true)).wt + 1) := Det.var' rfl
  have s6 := Det.call (Det.mk2 v4 v5) cap2
  set E7 : List Val := E6 ++ [natList (krefSAll col)] with hE7
  have u4 : Det P E7 (.var 4) (natList (krefSCodes col false))
      ((natList (krefSCodes col false)).wt + 1) := Det.var' rfl
  have u5 : Det P E7 (.var 5) (natList (krefSCodes col true))
      ((natList (krefSCodes col true)).wt + 1) := Det.var' rfl
  have u6 : Det P E7 (.var 6) (natList (krefSAll col)) ((natList (krefSAll col)).wt + 1) :=
    Det.var' rfl
  have r0 := Det.call (Det.mk2 u6 u4) (crk false)
  have r1 := Det.call (Det.mk2 u6 u5) (crk true)
  have s7 := Det.mk2 r0 r1
  have hall := Det.letE s1 (Det.letE s2 (Det.letE s3 (Det.letE s4 (Det.letE s5 (Det.letE s6 s7)))))
  refine FunDet.intro hg (hall.mono ?_)
  -- the cost
  have ec0 : (Val.list [natList (krefAv col false), .nat (krefB n k), natList (krefVAll col),
      natList (List.range (krefM n k))]).wt = (krefSigCtx col false).wt := rfl
  have ec1 : (Val.list [natList (krefAv col true), .nat (krefB n k), natList (krefVAll col),
      natList (List.range (krefM n k))]).wt = (krefSigCtx col true).wt := rfl
  have es : (krefSt (krefStep col)).wt = (Val.list [natList (krefAv (krefStep col) false),
      natList (krefAv (krefStep col) true)]).wt := rfl
  have := wt_list2_le (natList (krefAv (krefStep col) false)) (natList (krefAv (krefStep col) true))
  have := wt_list2_le (.list [natList (krefAv col false), .nat (krefB n k)]) (krefNbs n k)
  have := wt_list2_le (.list [natList (krefAv col true), .nat (krefB n k)]) (krefNbs n k)
  have := wt_list2_le (natList (krefAv col false)) (.nat (krefB n k))
  have := wt_list2_le (natList (krefAv col true)) (.nat (krefB n k))
  have := wt_list3_le (.nat 0) vt0 (.list [])
  have := wt_list3_le (.nat 0) vt1 (.list [])
  have := wt_list2_le (natList (krefVCodes col false).flatten) (natList (krefVCodes col true).flatten)
  have := wt_list2_le (krefSigCtx col false) (krefNbs n k)
  have := wt_list2_le (krefSigCtx col true) (krefNbs n k)
  have := wt_list2_le (natList (krefSCodes col false)) (natList (krefSCodes col true))
  have := wt_list2_le (natList (krefSAll col)) (natList (krefSCodes col false))
  have := wt_list2_le (natList (krefSAll col)) (natList (krefSCodes col true))
  have ev0 : (Val.list (List.map Val.list (List.map (fun l => List.map Val.nat l)
      (List.map (krefVcs col false) (krefTups n k))))).wt = vt0.wt := rfl
  have ev1 : (Val.list (List.map Val.list (List.map (fun l => List.map Val.nat l)
      (List.map (krefVcs col true) (krefTups n k))))).wt = vt1.wt := rfl
  have ex0 : (Val.list [Val.list [natList (krefAv col false), Val.nat (krefB n k),
      natList (krefVAll col), natList (List.range (krefM n k))], krefNbs n k]).wt =
      (Val.list [krefSigCtx col false, krefNbs n k]).wt := rfl
  have ex1 : (Val.list [Val.list [natList (krefAv col true), Val.nat (krefB n k),
      natList (krefVAll col), natList (List.range (krefM n k))], krefNbs n k]).wt =
      (Val.list [krefSigCtx col true, krefNbs n k]).wt := rfl
  have := wt_nat_le 0
  have h0 := wt_list_le ([] : List Val)
  simp only [List.map_nil, List.sum_nil, List.length_nil] at h0
  have hT : krefZ n k + 1 ≤ (krefZ n k + 1) ^ 7 := kref_le_pow (by norm_num)
  have q2 : krefAppK * (krefZ n k + 1) ^ 2 ≤ krefAppK * (krefZ n k + 1) ^ 7 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have q4 : krefFlatK * (krefZ n k + 1) ^ 4 ≤ krefFlatK * (krefZ n k + 1) ^ 7 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have q5 : krefRanksK * (krefZ n k + 1) ^ 5 ≤ krefRanksK * (krefZ n k + 1) ^ 7 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have e : krefRoundK * (krefZ n k + 1) ^ 7 = 30 * (krefVtabK * (krefZ n k + 1) ^ 7) +
      30 * (krefFlatK * (krefZ n k + 1) ^ 7) + 30 * (krefAppK * (krefZ n k + 1) ^ 7) +
      30 * (krefStabK * (krefZ n k + 1) ^ 7) + 30 * (krefRanksK * (krefZ n k + 1) ^ 7) +
      100000 * (krefZ n k + 1) ^ 7 := by
    unfold krefRoundK; ring
  rw [e]
  omega

end GI.Impl
