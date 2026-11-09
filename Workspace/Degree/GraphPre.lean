module

public import Workspace.Degree.GraphPost
public import Workspace.Degree.Interface

/-!
# Before a string query

`preE`: on `[c, r, [U, G]]`, the data of a step and the input of the string query.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The fields of `bv` without the radius. -/
def baseV (n D : ℕ) (ℓ : Fin n → ℕ) : List Val :=
  [.nat n, .nat D, .nat (n * D), .nat (n * D * (n * D)), encFun ℓ, ids n, ids (n * D),
    ids (n * D * (n * D))]

/-- The context of a step. -/
noncomputable def stepCtx (D : ℕ) (ℓ : Fin n → ℕ) (X Y : SimpleGraph (Fin n)) : Val :=
  .list [.list (baseV n D ℓ), adjVal X, adjVal Y]

/-- The body. -/
def preE (fw cl gn on : ℕ) : Expr :=
  let c := arg 0
  let i5 := Expr.get (.var 1) (.nat 5)
  let i7 := Expr.get (.var 1) (.nat 7)
  .letE (.snoc (.get c (.nat 0)) (arg 1))
  (.letE (.call fw (mk2 (mk3 (.var 1) (.get c (.nat 1)) i5) i5))
  (.letE (.call fw (mk2 (mk3 (.var 1) (.get c (.nat 2)) (.get (arg 2) (.nat 0))) i5))
  (.letE (.call cl (mk2 (mk4 (.var 1) (.get c (.nat 1)) i5 (.var 2)) i7))
  (.letE (.call cl (mk2 (mk4 (.var 1) (.get c (.nat 2)) (.get (arg 2) (.nat 0)) (.var 3)) i7))
  (.letE (.call gn (mk2 (.var 1) (.get (.get (arg 2) (.nat 1)) (.nat 1))))
  (.letE (.call on (mk2 .nil i7))
    (mk4 (.var 1) (.var 2) (.var 3) (mk2 (.get (.var 1) (.nat 1))
      (.snoc (.snoc (.snoc (.snoc (.snoc
        (mk5 (.get (.var 1) (.nat 3)) (mk2 (.get (.var 1) (.nat 3)) (.var 6)) (.var 7) (.var 4)
          (.var 5)) .nil) .nil) (.nat 0)) (.nat 2)) (.get (.var 1) (.nat 3)))))))))))

/-- The result. -/
noncomputable def preV (hD : 0 < D) (ℓ : Fin n → ℕ) (r : ℕ) (X Y : SimpleGraph (Fin n))
    (U : Perm (Fin n)) (gs : List (Perm (Fin n))) : Val :=
  .list [bv D ℓ r, fwdV ℓ X, fwdV ℓ (pull U Y), .list [.nat D,
    stringVal (n * D * (n * D)) (slotGens hD gs) (colorX D ℓ r X (fwd ℓ X))
      (colorX D ℓ r (pull U Y) (fwd ℓ (pull U Y)))]]

/-- A bound on the weights. -/
def preW (n : ℕ) : ℕ := 1000 * LB n + 10000 * VB n

/-- The cost of the table of ones. -/
def oneC (n : ℕ) : ℕ := kB n * 10 + mapK * (kB n + 1) * preW n

/-- The budget. -/
def preT (n : ℕ) : ℕ := fwdC n + colC n + gensC n + oneC n + preW n

/-- The bound. -/
def preC (n : ℕ) : ℕ := 100000000 * preT n

theorem preC_poly : PolyB preC := by
  have := VB_poly
  have := WB_poly
  have := fwdC_poly
  have := colC_poly
  have := gensC_poly
  unfold preC preT oneC preW LB kB
  poly

theorem pull_one (X : SimpleGraph (Fin n)) : pull 1 X = X := by
  ext a b
  rfl

theorem ids_eq : ids n = encPerm (1 : Perm (Fin n)) := by
  rw [encPerm_eq_encFun]
  rfl

/-- A list of at most `kB n ^ 2 + 1` permutations. -/
theorem permList_wt {m : ℕ} (hm : m ≤ kB n + n) {L : List (Perm (Fin m))}
    (hL : L.length ≤ kB n ^ 2 + 1) : (Val.list (L.map encPerm)).wt ≤ LB n := by
  have := wt_lit (L.map encPerm) (c := WB n) (by
    intro x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
    exact perm_wt hm g)
  simp only [List.length_map] at this
  refine this.trans ?_
  simp only [LB]
  have := Nat.mul_le_mul_right (2 * WB n + 1) (show L.length ≤ kB n ^ 2 + 2 by omega)
  omega

theorem length_slotGens_le (hS : Sz n D) (hD : 0 < D) {gs : List (Perm (Fin n))}
    (hgs : gs.length ≤ n ^ 2) : (slotGens hD gs).length ≤ (n * D * (n * D)) ^ 2 := by
  rw [length_slotGens]
  have h1 := hS.m_pos
  have h2 := hS.six
  have h3 : n ^ 2 ≤ n * D * (n * D) := by
    have : n ≤ n * D := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have h4 : n * D * (n * D) * 2 ≤ n * D * (n * D) * (n * D * (n * D)) := by
    refine Nat.mul_le_mul_left _ ?_
    have : D ≤ n * D := Nat.le_mul_of_pos_left _ hS.pos
    nlinarith
  have h5 := hS.m_le_k
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The data of a step.** -/
theorem pre_spec {P : Program} {a fw cl gn on : ℕ} (hf : P.funs[a]? = some (preE fw cl gn on))
    (hF : P.HasAt fw (fwdFuns fw)) (hC : P.HasAt cl (tabFuns cl colE))
    (hG : P.HasAt gn (gensFuns gn)) (hO : P.HasAt on (tabFuns on (.nat 1))) (hS : Sz n D)
    (hD : 0 < D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n)
    (X Y : SimpleGraph (Fin n)) (U : Perm (Fin n)) {gs : List (Perm (Fin n))}
    (hgs : gs.length ≤ n ^ 2) :
    FunDet P a (.list [stepCtx D ℓ X Y, .nat r, .list [encPerm U, encGroup gs]])
      (preV hD ℓ r X Y U gs) (preC n) := by
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have hmm := hS.m_pos
  have wb := bv_wt hS hℓ hr
  have wX := adjVal_wt X
  have wY := adjVal_wt Y
  have wU : (encPerm U).wt ≤ WB n := perm_wt (by omega) U
  have wn : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  have wDn : (Val.nat D).wt ≤ WB n := nat_wt (by have := hS.le; omega)
  have wm : (Val.nat (n * D)).wt ≤ WB n := nat_wt (by omega)
  have wk : (Val.nat (n * D * (n * D))).wt ≤ WB n := nat_wt (by omega)
  have wr : (Val.nat r).wt ≤ WB n := nat_wt (by omega)
  have wℓ : (encFun ℓ).wt ≤ WB n := table_wt (by omega) hℓ
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wj : (ids (n * D)).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wK : (ids (n * D * (n * D))).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have hg1 : ((1 : Perm (Fin n)) :: gs).length ≤ kB n ^ 2 + 1 := by
    have : n ^ 2 ≤ kB n ^ 2 := Nat.pow_le_pow_left (by have := Nat.le_mul_of_pos_right n (show 0 < 1 by omega); nlinarith) 2
    simp only [List.length_cons]
    omega
  have wL : (Val.list (((1 : Perm (Fin n)) :: gs).map encPerm)).wt ≤ LB n :=
    permList_wt (by omega) hg1
  have hslot : ((1 : Perm (Fin (n * D * (n * D)))) :: slotGens hD gs).length ≤ kB n ^ 2 + 1 := by
    have h1 := length_slotGens_le hS hD hgs
    have h2 := Nat.pow_le_pow_left hk 2
    simp only [List.length_cons]
    omega
  have wS : (Val.list (((1 : Perm (Fin (n * D * (n * D)))) :: slotGens hD gs).map encPerm)).wt ≤
      LB n := permList_wt (by omega) hslot
  have hb0 : (Val.list (baseV n D ℓ)).wt ≤ 8 * (2 * WB n + 1) + 4 := wt_lit _ (by
    intro v hv
    simp only [baseV, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  have hc0 : (stepCtx D ℓ X Y).wt ≤ 3 * (2 * (8 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 :=
    wt_lit _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl | rfl | rfl) <;> omega)
  have ha0 : (Val.list [encPerm U, .list [.nat n, .list (((1 : Perm (Fin n)) :: gs).map encPerm)]]).wt ≤
      2 * (2 * (2 * (2 * (LB n + WB n) + 1) + 4 + WB n) + 1) + 4 := by
    have : (Val.list [.nat n, .list (((1 : Perm (Fin n)) :: gs).map encPerm)]).wt ≤
        2 * (2 * (LB n + WB n) + 1) + 4 := wt_lit _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl) <;> omega)
    exact wt_lit _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl) <;> omega)
  have hG0 : encGroup gs = .list [.nat n, .list (((1 : Perm (Fin n)) :: gs).map encPerm)] := rfl
  rw [hG0]
  set ctx := stepCtx D ℓ X Y with hctx
  set acc : Val := .list [encPerm U, .list [.nat n, .list (((1 : Perm (Fin n)) :: gs).map encPerm)]]
    with hacc
  have ha1 : (Val.list [ctx, .nat r, acc]).wt ≤ 3 * (2 * (ctx.wt + acc.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl | rfl | rfl) <;> omega)
  have hW : 2 * (Val.list [ctx, .nat r, acc]).wt + 100 + 2 * WB n + 40 * VB n ≤ preW n := by
    simp only [preW]
    omega
  have hW2 : VB n + LB n + 100 ≤ preW n := by simp only [preW]; omega
  have hTW : preW n ≤ preT n := by simp only [preT]; omega
  set T := preT n with hT
  set A := Val.list [ctx, .nat r, acc] with hA
  have hT1 : fwdC n ≤ T := by simp only [hT, preT]; omega
  have hT2 : colC n ≤ T := by simp only [hT, preT]; omega
  have hT3 : gensC n ≤ T := by simp only [hT, preT]; omega
  have hT4 : oneC n ≤ T := by simp only [hT, preT]; omega
  have n0 : ∀ (env : List Val) (k : ℕ), k ≤ 8 → Lv P env T (.nat k) (.nat k) 1 :=
    fun env k hk => Lv.nat k (by omega)
  have g0 : ∀ rest, Lv P (A :: rest) T (arg 0) ctx 1 := fun rest => Lv.arg (vs := [ctx, .nat r, acc]) rfl
    (by change 2 * A.wt + 0 + 5 ≤ T; omega)
  have g1 : ∀ rest, Lv P (A :: rest) T (arg 1) (.nat r) 1 := fun rest =>
    Lv.arg (vs := [ctx, .nat r, acc]) rfl (by change 2 * A.wt + 1 + 5 ≤ T; omega)
  have g2 : ∀ rest, Lv P (A :: rest) T (arg 2) acc 1 := fun rest =>
    Lv.arg (vs := [ctx, .nat r, acc]) rfl (by change 2 * A.wt + 2 + 5 ≤ T; omega)
  have gb := fun rest => Lv.get (vs := [.list (baseV n D ℓ), adjVal X, adjVal Y]) (g0 rest)
    (n0 _ 0 (by omega)) rfl
  have gx := fun rest => Lv.get (vs := [.list (baseV n D ℓ), adjVal X, adjVal Y]) (g0 rest)
    (n0 _ 1 (by omega)) rfl
  have gy := fun rest => Lv.get (vs := [.list (baseV n D ℓ), adjVal X, adjVal Y]) (g0 rest)
    (n0 _ 2 (by omega)) rfl
  have gu := fun rest => Lv.get (vs := [encPerm U, .list [.nat n, .list (((1 : Perm (Fin n)) :: gs).map encPerm)]])
    (g2 rest) (n0 _ 0 (by omega)) rfl
  have gg := fun rest => Lv.get (vs := [encPerm U, .list [.nat n, .list (((1 : Perm (Fin n)) :: gs).map encPerm)]])
    (g2 rest) (n0 _ 1 (by omega)) rfl
  have gl := fun rest => Lv.get (vs := [.nat n, .list (((1 : Perm (Fin n)) :: gs).map encPerm)])
    (gg rest) (n0 _ 1 (by omega)) rfl
  set B := bv D ℓ r with hB
  have mkB : Lv P [A] T (.snoc (.get (arg 0) (.nat 0)) (arg 1)) B _ :=
    Lv.snoc (vs := baseV n D ℓ) (gb []) (g1 []) (by omega)
  have v1 : ∀ tl, Lv P (A :: B :: tl) T (.var 1) B 1 := fun tl => Lv.var rfl (by omega)
  have i5 := fun tl => Lv.bvGet (v1 tl) (j := 5) (w := ids n) (by omega) rfl (by omega)
  have i7 := fun tl => Lv.bvGet (v1 tl) (j := 7) (w := ids (n * D * (n * D))) (by omega) rfl
    (by omega)
  have i3 := fun tl => Lv.bvGet (v1 tl) (j := 3) (w := .nat (n * D * (n * D))) (by omega) rfl
    (by omega)
  have i1 := fun tl => Lv.bvGet (v1 tl) (j := 1) (w := .nat D) (by omega) rfl (by omega)
  have hP1 := pull_one X
  have sFX : FunDet P fw (.list [.list [B, adjVal X, ids n], ids n]) (fwdV ℓ X) (fwdC n) := by
    have := fwd_spec hF hS hℓ hr X 1
    rwa [hP1, ← ids_eq] at this
  have sFY := fwd_spec hF hS hℓ hr Y U
  set FX := fwdV ℓ X with hFX
  set FY := fwdV ℓ (pull U Y) with hFY
  have wFX : FX.wt ≤ VB n := fwdV_le_VB ℓ X
  have wFY : FY.wt ≤ VB n := fwdV_le_VB ℓ _
  have sCX : FunDet P cl (.list [.list [B, adjVal X, ids n, FX], ids (n * D * (n * D))])
      (encFun (colorX D ℓ r X (fwd ℓ X))) (colC n) := by
    have := col_spec hC hS hℓ hr X 1 (fwd ℓ X) (length_fwd_le ℓ X)
    rwa [hP1, ← ids_eq] at this
  have sCY : FunDet P cl (.list [.list [B, adjVal Y, encPerm U, FY], ids (n * D * (n * D))])
      (encFun (colorX D ℓ r (pull U Y) (fwd ℓ (pull U Y)))) (colC n) :=
    col_spec hC hS hℓ hr Y U (fwd ℓ (pull U Y)) (length_fwd_le ℓ _)
  have sG := gens_spec hG hS hD hℓ hr hgs
  have h5w : 5 ≤ kB n + n := by have := hS.six; have : D ≤ n * D := Nat.le_mul_of_pos_left _ hS.pos; omega
  have colB : ∀ (Z : SimpleGraph (Fin n)), (encFun (colorX D ℓ r Z (fwd ℓ Z))).wt ≤ WB n := fun Z =>
    table_wt' (B := 5) (by omega) (by omega) fun p => by
      obtain ⟨s, s', rfl⟩ := exists_pair p
      rw [colorX_pair]
      exact slotColor_le _ _
  set CX := encFun (colorX D ℓ r X (fwd ℓ X)) with hCX
  set CY := encFun (colorX D ℓ r (pull U Y) (fwd ℓ (pull U Y))) with hCY
  have wCX : CX.wt ≤ WB n := colB X
  have wCY : CY.wt ≤ WB n := colB _
  set GS := Val.list (((1 : Perm (Fin (n * D * (n * D)))) :: slotGens hD gs).map encPerm) with hGS
  set ON : Val := encFun fun _ : Fin (n * D * (n * D)) => 1 with hON
  have wON : ON.wt ≤ WB n := table_wt' (B := 1) (by omega) (by omega) fun _ => le_rfl
  have cFX := Lv.call (Lv.mk2 (Lv.mk3 (v1 []) (gx [B]) (i5 []) (by omega)) (i5 []) (by omega)) sFX hT1
  have cFY := Lv.call (Lv.mk2 (Lv.mk3 (v1 [FX]) (gy [B, FX]) (gu [B, FX]) (by omega)) (i5 [FX])
    (by omega)) sFY hT1
  have v2 : ∀ tl, Lv P (A :: B :: FX :: tl) T (.var 2) FX 1 := fun tl => Lv.var rfl (by omega)
  have v3 : ∀ tl, Lv P (A :: B :: FX :: FY :: tl) T (.var 3) FY 1 := fun tl => Lv.var rfl (by omega)
  have cCX := Lv.call (Lv.mk2 (Lv.mk4 (v1 [FX, FY]) (gx [B, FX, FY]) (i5 [FX, FY]) (v2 [FY])
    (by omega)) (i7 [FX, FY]) (by omega)) sCX hT2
  have cCY := Lv.call (Lv.mk2 (Lv.mk4 (v1 [FX, FY, CX]) (gy [B, FX, FY, CX]) (gu [B, FX, FY, CX])
    (v3 [CX]) (by omega)) (i7 [FX, FY, CX]) (by omega)) sCY hT2
  have cGS := Lv.call (Lv.mk2 (v1 [FX, FY, CX, CY]) (gl [B, FX, FY, CX, CY]) (by omega)) sG hT3
  have sO : FunDet P on (.list [.list [], ids (n * D * (n * D))]) ON (oneC n) := by
    refine (tabN_spec (T := 10) (K := 1) (W := preW n) hO
      (fun i => Lv.nat 1 (by norm_num)) ?_).mono ?_
    · have : (Val.list [.list [], ids (n * D * (n * D))]).wt ≤
          2 * (2 * (WB n + WB n) + 1) + 4 := wt_lit _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro v (rfl | rfl)
        · have := wt_lit [] (c := 0) (by simp)
          simp only [List.length_nil] at this
          omega
        · omega)
      change _ + ON.wt + 1 ≤ preW n
      simp only [preW]
      omega
    · simp only [oneC]
      have e1 := Nat.mul_le_mul_right 10 hk
      have e2 : mapK * (n * D * (n * D) + 1) * preW n ≤ mapK * (kB n + 1) * preW n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      omega
  have cON := Lv.call (Lv.mk2 (Lv.nil (by omega)) (i7 [FX, FY, CX, CY, GS]) (by omega)) sO hT4
  have wGS : GS.wt ≤ LB n := wS
  set E8 : List Val := [FX, FY, CX, CY, GS, ON] with hE8
  have vv : ∀ {i : ℕ} {v : Val}, (A :: B :: E8)[i]? = some v → v.wt ≤ VB n + LB n →
      Lv P (A :: B :: E8) T (.var i) v 1 := fun h hv => Lv.var h (by omega)
  have sv := Lv.mk5 (i3 E8) (Lv.mk2 (i3 E8) (vv (i := 6) rfl (by omega)) (by omega)) (vv (i := 7) rfl (by omega)) (vv (i := 4) rfl (by omega)) (vv (i := 5) rfl (by omega)) (by omega)
  have sv2 := Lv.snoc (Lv.snoc (Lv.snoc (Lv.snoc (Lv.snoc sv (Lv.nil (by omega)) (by omega))
    (Lv.nil (by omega)) (by omega)) (n0 _ 0 (by omega)) (by omega)) (n0 _ 2 (by omega)) (by omega))
    (i3 E8) (by omega)
  have o1 := Lv.mk4 (v1 E8) (vv (i := 2) rfl (by omega)) (vv (i := 3) rfl (by omega))
    (Lv.mk2 (i1 E8) sv2 (by omega)) (by omega)
  have l7 := Lv.letE cON o1
  have l6 := Lv.letE cGS l7
  have l5 := Lv.letE cCY l6
  have l4 := Lv.letE cCX l5
  have l3 := Lv.letE cFY l4
  have l2 := Lv.letE cFX l3
  have l1 := Lv.letE mkB l2
  have hC' : preC n = 100000000 * T := rfl
  rw [hC']
  exact funDet_of_lv hf (T := T) (m := 100000000) (Lv.mono (e := preE fw cl gn on) l1 (by norm_num))

end GI.Degree
