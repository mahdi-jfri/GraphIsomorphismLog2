import Workspace.Impl.AggStructDesHit

/-!
# The Case 3 test as a program

`stDes_spec`: on `A = [dl, tl, q, κ]`, the program finds the first prefix length `m_h` where
the hit test succeeds, computes the vertex colors `V` of that prefix, and decides `stDesB`:
either the classes of `V` are balanced, or the next coordinate of the tuple lies in the
dominant class. By `stDesB_iff` this is the Case 3 test `StDes`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- Inside an environment that starts with `A`: `q`, `κ` and the coordinate `t κ`. -/
def stDTq : Expr := .get (.var 0) (.nat 2)
def stDTκ : Expr := .get (.var 0) (.nat 3)
def stDTt : Expr := .get (.get (.var 0) (.nat 1)) stDTκ

/-- **The Case 3 test** on `A`: modules `fh` (find of the hit test), `rb` (range), `vm` (vertex
colors), `ad` (any of the class test), `dvv` (the class test of a color) and `cf` (color). -/
def stDesF (fh rb vm ad dvv cf : ℕ) : Expr :=
  .letE (.call fh (mk2 (.var 0) (.call rb stDTκ)))
    (.ite (.arith .lt (.var 1) stDTκ)
      (.letE (.call vm (mk2 (.var 0) (.var 1)))
        (.ite (.call ad (mk2 (mk2 (.var 2) stDTq) (.call rb stDTq)))
          (.call dvv (mk2 (mk2 (.var 2) stDTq) (.call cf (mk4 (.var 0) (.var 1) stDTt stDTt))))
          (.nat 1)))
      (.nat 0))

theorem stDT_parts {P : Program} {dl tl : List ℕ} {q κ : ℕ} (hc : StDCtx dl tl q κ)
    (rest : List Val) {W : ℕ} (hW : (stDA dl tl q κ).wt ≤ W) (h5 : 5 ≤ W) :
    StDC P (stDA dl tl q κ :: rest) (.var 0) (stDA dl tl q κ) 1 0 W ∧
    StDC P (stDA dl tl q κ :: rest) stDTq (.nat q) 3 0 W ∧
    StDC P (stDA dl tl q κ :: rest) stDTκ (.nat κ) 3 0 W ∧
    StDC P (stDA dl tl q κ :: rest) stDTt (.nat (tl.getD κ 0)) 7 0 W := by
  obtain ⟨-, -, -, htw, hqw, hκw⟩ := wt_stDA_ge (dl := dl) (tl := tl) (q := q) (κ := κ)
  have g0 : StDC P (stDA dl tl q κ :: rest) (.var 0) (stDA dl tl q κ) 1 0 W :=
    StDC.var' rfl hW
  have gκ : StDC P (stDA dl tl q κ :: rest) stDTκ (.nat κ) 3 0 W :=
    StDC.get (vs := [natList dl, natList tl, .nat q, .nat κ]) g0 (StDC.nat 3 (by omega)) rfl
      (by omega)
  have hκ := hc.len_tl
  have htl : (tl.map Val.nat)[κ]? = some (.nat (tl.getD κ 0)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hκ, List.getD_eq_getElem _ _ hκ]; rfl
  have hle : (Val.nat (tl.getD κ 0)).wt ≤ (natList tl).wt :=
    st_wt_mem (List.mem_of_getElem? htl)
  refine ⟨g0, StDC.get (vs := [natList dl, natList tl, .nat q, .nat κ]) g0
    (StDC.nat 2 (by omega)) rfl (by omega), gκ, ?_⟩
  exact StDC.get (StDC.get (vs := [natList dl, natList tl, .nat q, .nat κ]) g0
    (StDC.nat 1 (by omega)) rfl (by show (natList tl).wt ≤ W; omega)) gκ htl
    (hle.trans (by omega))

/-- The cost constant of the Case 3 test. -/
def stDesK : ℕ := 10 ^ 52

theorem stDes_spec {P : Program} {f fh ht rb vm mb vf cf h ad dv dv' cb : ℕ}
    (hf : P.funs[f]? = some (stDesF fh rb vm ad dv' cf))
    (hfh : P.HasAt fh (findFuns fh ht)) (hht : StDHitOK P ht) (hrb : P.HasAt rb (rangeFuns rb))
    (hvm : P.funs[vm]? = some (stDVMapF mb rb))
    (hmb : P.HasAt mb (mapFuns mb vf)) (hvf : P.funs[vf]? = some (stDVF cf))
    (hcf : P.funs[cf]? = some (stDColF h)) (hh : P.HasAt h (stDHorFuns h))
    (had : P.HasAt ad (anyFuns ad dv)) (hdv : P.funs[dv]? = some (stDDomF dv'))
    (hdv' : P.funs[dv']? = some (stDDomVF cb)) (hcb : P.HasAt cb (countFuns cb))
    {dl tl : List ℕ} {q κ : ℕ} (hc : StDCtx dl tl q κ) {N : ℕ} (hN : (stDA dl tl q κ).wt ≤ N) :
    FunDet P f (stDA dl tl q κ) (boolVal (stDesB dl tl q κ)) (stDesK * (N + 1) ^ 17) := by
  obtain ⟨hql, hκN, hqN⟩ := hc.le_wt
  have hκl := hc.len_tl
  have hq0 := hc.q_pos
  have hY1 : 1 ≤ N + 1 := by omega
  have hY2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨W, hW⟩ : ∃ W, W = 1000 * (N + 1) ^ 2 + 1000 := ⟨_, rfl⟩
  -- the first hit
  obtain ⟨mh, hmh⟩ : ∃ mh, (List.range κ).findIdx (stDHit dl tl q κ) = mh := ⟨_, rfl⟩
  have hmhκ : mh ≤ κ := by rw [← hmh]; exact (List.findIdx_le_length).trans (by simp)
  have hAi : ∀ i, i ≤ κ → (Val.list [stDA dl tl q κ, .nat i]).wt ≤ 4 * N + 10 := by
    intro i hi
    have := wt_list2_le (stDA dl tl q κ) (.nat i)
    have := wt_nat_le i
    omega
  have hrκ : (natList (List.range κ)).wt ≤ 5 * (N + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range κ) (B := κ) (fun x hx => (List.mem_range.1 hx).le)
      (by simp)
    have : (κ + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hrq : (natList (List.range q)).wt ≤ 5 * (N + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range q) (B := q) (fun x hx => (List.mem_range.1 hx).le)
      (by simp)
    have : (q + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨E1, hE1⟩ : ∃ E1, κ * (stDHitK * (4 * N + 10 + 1) ^ 16) +
      loopModK * (20 * (N + 1) ^ 2 + 1) * (3 * (20 * (N + 1) ^ 2) + 3) = E1 := ⟨_, rfl⟩
  have hfind := st_find_det hfh (c := stDA dl tl q κ) (n := κ) (t := stDHit dl tl q κ)
    (B := stDHitK * (4 * N + 10 + 1) ^ 16) (X := 20 * (N + 1) ^ 2)
    (fun i hi => hht hc hi.le (hAi i hi.le))
    (by have := wt_list2_le (stDA dl tl q κ) (natList (List.range κ)); omega) (by omega)
  rw [hmh, hE1] at hfind
  obtain ⟨E2, hE2⟩ : ∃ E2, 10000 * (κ + 1) ^ 3 = E2 := ⟨_, rfl⟩
  have hrk := st_range_det hrb κ
  rw [hE2] at hrk
  obtain ⟨g0, -, gκ, -⟩ := stDT_parts (P := P) hc [] (W := W) (by omega) (by omega)
  have g1 := StDC.call (StDC.mk2 g0 (StDC.call gκ hrk (by omega))
    (by have := wt_list2_le (stDA dl tl q κ) (natList (List.range κ)); omega) (by omega)) hfind
    (by have := wt_nat_le mh; omega)
  obtain ⟨g0', gq', gκ', gt'⟩ := stDT_parts (P := P) hc [.nat mh] (W := W) (by omega) (by omega)
  have gmh : StDC P [stDA dl tl q κ, .nat mh] (.var 1) (.nat mh) 1 0 W :=
    StDC.var' rfl (by have := wt_nat_le mh; omega)
  have gc := StDC.arith' gmh gκ' (op := .lt) (z := BinOp.eval .lt mh κ) rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  have hW0 : (boolVal false).wt ≤ W := by have := wt_boolVal_le false; omega
  have hW1 : (boolVal true).wt ≤ W := by have := wt_boolVal_le true; omega
  obtain ⟨E3, hE3⟩ : ∃ E3, stDVMK * (4 * N + 10 + 1) ^ 3 = E3 := ⟨_, rfl⟩
  obtain ⟨E4, hE4⟩ : ∃ E4, 10000 * (q + 1) ^ 3 = E4 := ⟨_, rfl⟩
  obtain ⟨E5, hE5⟩ : ∃ E5, q * (2 * stDDomK * (2 * N + 1) ^ 3) +
      loopModK * (200 * (N + 1) ^ 2 + 1) * (3 * (200 * (N + 1) ^ 2) + 3) = E5 := ⟨_, rfl⟩
  obtain ⟨E6, hE6⟩ : ∃ E6, stDColK * (8 * N + 9) ^ 2 = E6 := ⟨_, rfl⟩
  obtain ⟨E7, hE7⟩ : ∃ E7, stDDomK * (2 * N + 1) ^ 3 = E7 := ⟨_, rfl⟩
  have hcost : 100 * (W + 1) + (E1 + E2 + E3 + E4 + E5 + E6 + E7) ≤ stDesK * (N + 1) ^ 17 := by
    have hP := fun i j (h : i ≤ j) => Nat.pow_le_pow_right hY1 h
    have u1 : κ * (stDHitK * (4 * N + 10 + 1) ^ 16) ≤ stDHitK * 11 ^ 16 * (N + 1) ^ 17 := by
      calc κ * (stDHitK * (4 * N + 10 + 1) ^ 16) ≤ (N + 1) * (stDHitK * (11 * (N + 1)) ^ 16) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 16))
        _ = _ := by ring
    have u2 : loopModK * (20 * (N + 1) ^ 2 + 1) * (3 * (20 * (N + 1) ^ 2) + 3) ≤
        loopModK * 21 * 63 * (N + 1) ^ 4 := by
      have h1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ loopModK * (21 * (N + 1) ^ 2) * (63 * (N + 1) ^ 2) :=
            st_mul3 le_rfl (by omega) (by omega)
        _ = _ := by ring
    have u3 : 10000 * (κ + 1) ^ 3 ≤ 80000 * (N + 1) ^ 3 := by
      calc _ ≤ 10000 * (2 * (N + 1)) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
        _ = _ := by ring
    have u4 : stDVMK * (4 * N + 10 + 1) ^ 3 ≤ stDVMK * 1331 * (N + 1) ^ 3 := by
      calc _ ≤ stDVMK * (11 * (N + 1)) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
        _ = _ := by ring
    have u5 : 10000 * (q + 1) ^ 3 ≤ 80000 * (N + 1) ^ 3 := by
      calc _ ≤ 10000 * (2 * (N + 1)) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
        _ = _ := by ring
    have u6 : q * (2 * stDDomK * (2 * N + 1) ^ 3) ≤ 16 * stDDomK * (N + 1) ^ 4 := by
      calc q * (2 * stDDomK * (2 * N + 1) ^ 3) ≤ (N + 1) * (2 * stDDomK * (2 * (N + 1)) ^ 3) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
        _ = _ := by ring
    have u7 : loopModK * (200 * (N + 1) ^ 2 + 1) * (3 * (200 * (N + 1) ^ 2) + 3) ≤
        loopModK * 201 * 603 * (N + 1) ^ 4 := by
      have h1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ loopModK * (201 * (N + 1) ^ 2) * (603 * (N + 1) ^ 2) :=
            st_mul3 le_rfl (by omega) (by omega)
        _ = _ := by ring
    have u8 : stDColK * (8 * N + 9) ^ 2 ≤ stDColK * 81 * (N + 1) ^ 2 := by
      calc _ ≤ stDColK * (9 * (N + 1)) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
        _ = _ := by ring
    have u9 : stDDomK * (2 * N + 1) ^ 3 ≤ stDDomK * 8 * (N + 1) ^ 3 := by
      calc _ ≤ stDDomK * (2 * (N + 1)) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
        _ = _ := by ring
    have hp2 := hP 2 17 (by norm_num)
    have hp3 := hP 3 17 (by norm_num)
    have hp4 := hP 4 17 (by norm_num)
    rw [← hE1, ← hE2, ← hE3, ← hE4, ← hE5, ← hE6, ← hE7, hW]
    clear g1 gc g0 gκ g0' gq' gκ' gt' gmh hfind hrk
    simp only [stDesK, stDHitK, stDVMK, stDDomK, stDColK, loopModK] at u1 u2 u4 u6 u7 u8 u9 ⊢
    norm_num at u1 u2 u4 u6 u7 u8 u9 ⊢
    linarith
  unfold stDesB
  rw [hmh]
  by_cases hlt : mh < κ
  · have hx : BinOp.eval .lt mh κ ≠ 0 := by simp [BinOp.eval, hlt]
    have hV := stDV_spec hvm hmb hrb hvf hcf hh hc mh (hAi mh hmhκ)
    rw [hE3] at hV
    have hVle := hc.stDV_le mh
    have hVl := stDV_length dl tl q κ mh
    have hVw := hc.wt_stDV mh
    obtain ⟨V, hVd⟩ : ∃ V, stDV dl tl q κ mh = V := ⟨_, rfl⟩
    rw [hVd] at hV hVle hVl hVw
    rw [hVd]
    have hM2 : (2 * (stDA dl tl q κ).wt + 1) ^ 2 ≤ 4 * (N + 1) ^ 2 := by
      calc _ ≤ (2 * (N + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = _ := by ring
    have gV := StDC.call (StDC.mk2 g0' gmh (by have := hAi mh hmhκ; omega) (by omega)) hV
      (by omega)
    obtain ⟨g0'', gq'', -, gt''⟩ := stDT_parts (P := P) hc [.nat mh, natList V] (W := W)
      (by omega) (by omega)
    have gmh'' : StDC P [stDA dl tl q κ, .nat mh, natList V] (.var 1) (.nat mh) 1 0 W :=
      StDC.var' rfl (by have := wt_nat_le mh; omega)
    have gV'' : StDC P [stDA dl tl q κ, .nat mh, natList V] (.var 2) (natList V) 1 0 W :=
      StDC.var' rfl (by omega)
    have hVB : ∀ x ∈ V, x ≤ 2 * N := fun x hx => by have := hVle x hx; omega
    have hcV : (Val.list [natList V, .nat q]).wt ≤ 20 * (2 * N + 1) ^ 2 :=
      st_wt_ctxV hVB hVl (by omega)
    have hN2 : (2 * N + 1) ^ 2 ≤ 4 * (N + 1) ^ 2 := by
      calc _ ≤ (2 * (N + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = _ := by ring
    have hr := st_range_det hrb q
    rw [hE4] at hr
    have hdom := st_any_det had (c := .list [natList V, .nat q]) (n := q) (t := stDDom V q)
      (B := 2 * stDDomK * (2 * N + 1) ^ 3) (X := 200 * (N + 1) ^ 2)
      (fun i hi => stDDom_spec hdv hdv' hcb hVB hVl (by omega) hi)
      (by have := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q)); omega)
      (by omega)
    rw [hE5] at hdom
    have gany := StDC.call (StDC.mk2 (StDC.mk2 gV'' gq'' (by omega) (by omega))
      (StDC.call gq'' hr (by omega))
      (by have := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q)); omega)
      (by omega)) hdom (by have := wt_boolVal_le ((List.range q).any (stDDom V q)); omega)
    by_cases h2 : (List.range q).any (stDDom V q) = true
    · have hb : stDBal V q = false := by simp [stDBal, h2]
      have hx2 : ((List.range q).any (stDDom V q)).toNat ≠ 0 := by simp [h2]
      obtain ⟨z, hz⟩ : ∃ z, tl.getD κ 0 = z := ⟨_, rfl⟩
      have hzq : z < q := by
        rw [← hz, List.getD_eq_getElem _ _ hκl]; exact hc.tl_lt _ (List.getElem_mem hκl)
      rw [hz] at gt''
      have hcol := stDCol_spec hcf hh hc mh hzq hzq
      have hCA : (stDCA dl tl q κ mh z z).wt ≤ 8 * N + 8 := by
        have := wt_list4_le (stDA dl tl q κ) (.nat mh) (.nat z) (.nat z)
        have := wt_nat_le mh; have := wt_nat_le z
        unfold stDCA; omega
      have hcolE : stDColK * ((stDCA dl tl q κ mh z z).wt + 1) ^ 2 ≤ E6 := by
        rw [← hE6]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      obtain ⟨Ec, hEc⟩ : ∃ Ec, stDColK * ((stDCA dl tl q κ mh z z).wt + 1) ^ 2 = Ec := ⟨_, rfl⟩
      rw [hEc] at hcol hcolE
      obtain ⟨col, hcold⟩ : ∃ col, stDCol dl tl q κ mh z z = col := ⟨_, rfl⟩
      have hcolN : col ≤ 2 * N := by
        have : col ≤ 2 * (stDA dl tl q κ).wt := by
          rw [← hcold]; unfold stDCol; rw [List.getD_eq_getElem?_getD]
          cases h' : dl[stDHor q κ (stDE tl mh z z) κ]? with
          | none => simp
          | some y => exact hc.dl_le y (List.mem_of_getElem? h')
        omega
      rw [hcold] at hcol
      have gcol := StDC.call (StDC.mk4 g0'' gmh'' gt'' gt'' (by
        have := wt_list4_le (stDA dl tl q κ) (.nat mh) (.nat z) (.nat z)
        have := wt_nat_le mh; have := wt_nat_le z; omega) (by omega)) hcol
        (by have := wt_nat_le col; omega)
      have hdv2 := stDDomV_spec hdv' hcb hVB hVl (by omega) hcolN
      rw [hE7] at hdv2
      have gdv := StDC.call (StDC.mk2 (StDC.mk2 gV'' gq'' (by omega) (by omega)) gcol
        (by have := wt_list2_le (.list [natList V, .nat q]) (.nat col); have := wt_nat_le col
            omega) (by omega)) hdv2 (by have := wt_boolVal_le (stDDomV V q col); omega)
      have hwv : (boolVal (stDDomV V q col)).wt ≤ W := by
        have := wt_boolVal_le (stDDomV V q col); omega
      have g := StDC.letE g1 (st_iteT (e := .nat 0) gc hx (StDC.letE gV
        (st_iteT (e := .nat 1) gany hx2 gdv hwv) hwv) hwv) hwv
      simp only [decide_eq_true hlt, hb, Bool.true_and, Bool.false_or, hz, hcold]
      exact StDC.funDet hf (g.mono (n' := 100) (E' := E1 + E2 + E3 + E4 + E5 + E6 + E7)
        (by omega) (by omega)) hcost
    · have hx2 : ((List.range q).any (stDDom V q)).toNat = 0 := by simp at h2 ⊢; simpa using h2
      have hb : stDBal V q = true := by simp only [stDBal]; simpa using h2
      have g := StDC.letE g1 (st_iteT (e := .nat 0) gc hx (StDC.letE gV
        (st_iteF (t := .call dv' (mk2 (mk2 (.var 2) stDTq)
          (.call cf (mk4 (.var 0) (.var 1) stDTt stDTt)))) gany hx2 (StDC.nat 1 (by omega)) hW1)
          hW1) hW1) hW1
      simp only [decide_eq_true hlt, hb, Bool.true_and, Bool.true_or]
      exact StDC.funDet hf (g.mono (n' := 100) (E' := E1 + E2 + E3 + E4 + E5 + E6 + E7)
        (by omega) (by omega)) hcost
  · have hx : BinOp.eval .lt mh κ = 0 := by simp [BinOp.eval, hlt]
    have g := StDC.letE g1 (st_iteF (t := .letE (.call vm (mk2 (.var 0) (.var 1)))
        (.ite (.call ad (mk2 (mk2 (.var 2) stDTq) (.call rb stDTq)))
          (.call dv' (mk2 (mk2 (.var 2) stDTq) (.call cf (mk4 (.var 0) (.var 1) stDTt stDTt))))
          (.nat 1))) gc hx (StDC.nat 0 (by omega)) hW0) hW0
    simp only [decide_eq_false hlt, Bool.false_and]
    exact StDC.funDet hf (g.mono (n' := 100) (E' := E1 + E2 + E3 + E4 + E5 + E6 + E7)
      (by omega) (by omega)) hcost

end GI.Impl