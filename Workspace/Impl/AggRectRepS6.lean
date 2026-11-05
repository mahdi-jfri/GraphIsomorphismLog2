module

public import Workspace.Impl.AggRectRepS5

@[expose] public section

/-!
# The cell step of the representation program

`cellFF` computes the cell code `rcRCellN` of one position (`rcR_cell_spec`).
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

theorem rcR_bit2 (c d : ℕ) :
    BinOp.eval .mul (BinOp.eval .eq c 1) (BinOp.eval .eq d 1) ≠ 0 ↔ c = 1 ∧ d = 1 := by
  simp only [BinOp.eval]; split_ifs <;> simp_all

theorem rcR_bit3 (a b c d : ℕ) :
    BinOp.eval .mul (BinOp.eval .lt a b) (BinOp.eval .mul (BinOp.eval .eq c 1)
      (BinOp.eval .eq d 1)) ≠ 0 ↔ a < b ∧ c = 1 ∧ d = 1 := by
  simp only [BinOp.eval]; split_ifs <;> simp_all

theorem rcR_bitU (u : Bool) (c d : ℕ) :
    BinOp.eval .mul u.toNat (BinOp.eval .mul (BinOp.eval .eq c 1) (BinOp.eval .eq d 1)) ≠ 0 ↔
      u = true ∧ c = 1 ∧ d = 1 := by
  cases u <;> simp only [BinOp.eval] <;> split_ifs <;> simp_all

theorem rcR_wt_code (r q c : ℕ) :
    (Val.nat (1 + r * q + c)).wt ≤ (Val.nat r).wt + (Val.nat q).wt + (Val.nat c).wt + 3 := by
  have h1 := rcR_wt_add (1 + r * q) c
  have h2 := rcR_wt_add 1 (r * q)
  have h3 := rcR_wt_mul r q
  have h4 := wt_nat_le 1
  omega

section Cell

variable {P : Program} {I : RcRIdx}

set_option maxHeartbeats 4000000 in
/-- **The cell code of one position.** -/
theorem rcR_cell_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.cellF]? = some I.cellFF)
    (hl0 : P.funs[I.look]? = some I.lookF)
    (hf0 : P.HasAt I.fLk0 (findFuns I.fLk0 I.lk0P)) (hp0 : P.funs[I.lk0P]? = some I.lk0PF)
    (dl : List ℕ) (Lk : List (List ℕ)) (k q : ℕ) (wl rl : List ℕ) (car uno : Bool)
    (rowT : List ℕ) (i : ℕ) :
    FunDet P I.cellF (.list [.list [natList dl, rcTV Lk, .nat k, .nat q, natList wl, natList rl,
      .nat car.toNat, .nat uno.toNat, natList rowT], .nat i])
      (.nat (rcRCellN dl Lk k q wl rl car uno rowT i))
      (10 ^ 20 * ((Val.list [.list [natList dl, rcTV Lk, .nat k, .nat q, natList wl, natList rl,
        .nat car.toNat, .nat uno.toNat, natList rowT], .nat i]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [natList dl, rcTV Lk, .nat k, .nat q, natList wl,
    natList rl, .nat car.toNat, .nat uno.toNat, natList rowT], .nat i]).wt := ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs : List Val, Cs = [natList dl, rcTV Lk, .nat k, .nat q, natList wl,
    natList rl, .nat car.toNat, .nat uno.toNat, natList rowT] := ⟨_, rfl⟩
  have hC : (Val.list Cs).wt < V := by rw [hV, hCs]; exact wt_le_wt_list (by simp)
  have hi : (Val.nat i).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have mC : ∀ v ∈ Cs, v.wt < V := fun v hv => (wt_le_wt_list hv).trans hC
  have hdl := mC (natList dl) (by simp [hCs])
  have hT := mC (rcTV Lk) (by simp [hCs])
  have hk := mC (.nat k) (by simp [hCs])
  have hq := mC (.nat q) (by simp [hCs])
  have hwl := mC (natList wl) (by simp [hCs])
  have hrl := mC (natList rl) (by simp [hCs])
  have hrow := mC (natList rowT) (by simp [hCs])
  have hX : (Val.list [Val.list Cs, .nat i]).wt = V := by rw [hV, hCs]
  -- reading the context, in any environment that starts with the input
  have rd : ∀ (rest : List Val) (j : ℕ) (v : Val), Cs[j]? = some v →
      rcRDW P (.list [.list Cs, .nat i] :: rest) (.get (arg 0) (.nat j)) v W (3 * W + j + 9) :=
    fun rest j v h => (rcRDW.get (rcRDW.arg (rest := rest) (by omega) rfl) h).mono (by omega)
  have ai : ∀ rest : List Val, rcRDW P (.list [.list Cs, .nat i] :: rest) (arg 1) (.nat i) W
      (2 * W + 6) := fun rest => rcRDW.arg (rest := rest) (by omega) rfl
  have nn : ∀ (env : List Val) (j : ℕ), j ≤ 2 → rcRDW P env (.nat j) (.nat j) W (j + 3) :=
    fun _ j hj => rcRDW.nat j (by omega)
  -- the test of the domain
  have ddl := rcRDW.gdN I hgD (rd [] 0 (natList dl) (by simp [hCs])) (ai []) (nn _ 0 (by omega))
  have d0 := rcRDW.arith (op := .eq) ddl (nn _ 0 (by omega)) rfl (rcR_eval_eq_wt _ _ (by omega))
  -- the lookup
  obtain ⟨y, hy⟩ : ∃ y, y = rcRLook Lk i := ⟨_, rfl⟩
  have wy : (natList y).wt ≤ (rcTV Lk).wt := hy ▸ rcR_wt_look Lk i
  have w2 := wt_list2_le (rcTV Lk) (.nat i)
  have dlk := rcRDW.call (rcRDW.mk2 (rd [] 1 (rcTV Lk) (by simp [hCs])) (ai []) (by omega))
    (rcR_look_spec hgD hl0 hf0 hp0 Lk i) (by rw [hy] at wy; omega)
  rw [← hy] at dlk
  -- the first label `c`
  have vy : ∀ rest : List Val, rcRDW P (.list [.list Cs, .nat i] :: natList y :: rest) (.var 1)
      (natList y) W (W + 1) := fun rest => rcRDW.var rfl (by omega)
  have dy1 := rcRDW.gdN I hgD (vy []) (nn _ 1 (by omega)) (nn _ 0 (by omega))
  have wc1 := rcR_wt_getD_le y 1
  have dc := rcRDW.arith (op := .sub) (z := y.getD 1 0 - k) dy1
    (rd [natList y] 2 (.nat k) (by simp [hCs])) rfl
    (by have := rcR_wt_sub (y.getD 1 0) k; omega)
  obtain ⟨c, hc⟩ : ∃ c, c = y.getD 1 0 - k := ⟨_, rfl⟩
  rw [← hc] at dc
  have wc : (Val.nat c).wt ≤ (rcTV Lk).wt := by
    rw [hc]; have := rcR_wt_sub (y.getD 1 0) k; omega
  -- the environment after `c`
  have vc : ∀ rest : List Val, rcRDW P (.list [.list Cs, .nat i] :: natList y :: .nat c :: rest)
      (.var 2) (.nat c) W (W + 1) := fun rest => rcRDW.var rfl (by omega)
  have dcar := rd [natList y, .nat c] 6 (.nat car.toNat) (by simp [hCs])
  -- the value
  obtain ⟨R, hR⟩ : ∃ R, R = rcRCellN dl Lk k q wl rl car uno rowT i := ⟨_, rfl⟩
  have hRv : R = if dl.getD i 0 = 0 then 0 else if car then
      rcRCarCodeN wl rl q (rowT.getD i 0) c else rcRCodeN wl rl q uno c
        ((rcRLook Lk i).getD 2 0 - k) := by
    rw [hR, hc, hy]; rfl
  -- the carrier branch
  have carB : car = true → rcRDW P [.list [.list Cs, .nat i], natList y, .nat c]
      (.letE (I.gd (.get (arg 0) (.nat 8)) (arg 1) (.nat 0))
        (.ite (rcRAnd (.arith .lt (.var 3) (.get (arg 0) (.nat 3)))
            (rcRAnd (rcREq (I.gd (.get (arg 0) (.nat 4)) (.var 3) (.nat 0)) (.nat 1))
              (rcREq (I.gd (.get (arg 0) (.nat 5)) (.var 2) (.nat 0)) (.nat 1))))
          (.arith .add (.arith .add (.nat 1) (.arith .mul (.var 3) (.get (arg 0) (.nat 3))))
            (.var 2)) (.nat 0))) (.nat (rcRCarCodeN wl rl q (rowT.getD i 0) c)) W
      (1000 * W + 3000) := by
    intro _
    obtain ⟨r, hr⟩ : ∃ r, r = rowT.getD i 0 := ⟨_, rfl⟩
    have dr := rcRDW.gdN I hgD (rd [natList y, .nat c] 8 (natList rowT) (by simp [hCs]))
      (ai [natList y, .nat c]) (nn _ 0 (by omega))
    rw [← hr] at dr
    have wr : (Val.nat r).wt ≤ (natList rowT).wt := hr ▸ rcR_wt_getD_le rowT i
    have vr := rcRDW.var (P := P) (W := W) (env := [.list [.list Cs, .nat i], natList y, .nat c,
      .nat r]) (i := 3) (v := .nat r) rfl (by omega)
    have gq := rd [natList y, .nat c, .nat r] 3 (.nat q) (by simp [hCs])
    have t1 := rcRDW.arith (op := .lt) vr gq rfl (rcR_eval_lt_wt _ _ (by omega))
    have t2 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD (rd [natList y, .nat c, .nat r] 4
      (natList wl) (by simp [hCs])) vr (nn _ 0 (by omega))) (nn _ 1 (by omega)) rfl
      (rcR_eval_eq_wt _ _ (by omega))
    have t3 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD (rd [natList y, .nat c, .nat r] 5
      (natList rl) (by simp [hCs])) (vc [.nat r]) (nn _ 0 (by omega))) (nn _ 1 (by omega)) rfl
      (rcR_eval_eq_wt _ _ (by omega))
    have t4 := rcRDW.arith (op := .mul) t2 t3 rfl (rcR_wt_bitW (rcR_eval_mul_le
      (rcR_eval_eq_le _ _) (rcR_eval_eq_le _ _)) (by omega))
    have t5 := rcRDW.arith (op := .mul) t1 t4 rfl (rcR_wt_bitW (rcR_eval_mul_le
      (rcR_eval_lt_le _ _) (rcR_eval_mul_le (rcR_eval_eq_le _ _) (rcR_eval_eq_le _ _))) (by omega))
    have wcode := rcR_wt_code r q c
    have a1 := rcRDW.arith (op := .mul) (z := r * q) vr gq rfl
      (by have := rcR_wt_mul r q; omega)
    have a2 := rcRDW.arith (op := .add) (z := 1 + r * q) (nn _ 1 (by omega)) a1 rfl
      (by have := rcR_wt_add 1 (r * q); have := rcR_wt_mul r q; have := wt_nat_le 1; omega)
    have a3 := rcRDW.arith (op := .add) (z := 1 + r * q + c) a2 (vc [.nat r]) rfl (by omega)
    have dite := rcRDW.ite (v := .nat (rcRCarCodeN wl rl q r c)) t5
      (fun hx => by
        have h := (rcR_bit3 _ _ _ _).1 hx
        rw [show rcRCarCodeN wl rl q r c = 1 + r * q + c by
          unfold rcRCarCodeN; rw [if_pos h]]
        exact a3)
      (fun hx => by
        have h : ¬ (r < q ∧ wl.getD r 0 = 1 ∧ rl.getD c 0 = 1) := fun h =>
          ((rcR_bit3 _ _ _ _).2 h) hx
        rw [show rcRCarCodeN wl rl q r c = 0 by unfold rcRCarCodeN; rw [if_neg h]]
        exact nn _ 0 (by omega))
    have := rcRDW.letE dr dite
    rw [hr] at this
    exact this.mono (by omega)
  -- the pair branch
  obtain ⟨d, hd⟩ : ∃ d, d = y.getD 2 0 - k := ⟨_, rfl⟩
  have wd : (Val.nat d).wt ≤ (rcTV Lk).wt := by
    rw [hd]; have := rcR_wt_sub (y.getD 2 0) k; have := rcR_wt_getD_le y 2; omega
  have parB : car = false → rcRDW P [.list [.list Cs, .nat i], natList y, .nat c]
      (.letE (.arith .sub (I.gd (.var 1) (.nat 2) (.nat 0)) (.get (arg 0) (.nat 2)))
        (.ite (rcRAnd (rcREq (I.gd (.get (arg 0) (.nat 4)) (.var 2) (.nat 0)) (.nat 1))
            (rcREq (I.gd (.get (arg 0) (.nat 5)) (.var 3) (.nat 0)) (.nat 1)))
          (.arith .add (.arith .add (.nat 1) (.arith .mul (.var 2) (.get (arg 0) (.nat 3))))
            (.var 3))
          (.ite (rcRAnd (.get (arg 0) (.nat 7)) (rcRAnd (rcREq (I.gd (.get (arg 0) (.nat 4))
              (.var 3) (.nat 0)) (.nat 1)) (rcREq (I.gd (.get (arg 0) (.nat 5)) (.var 2) (.nat 0))
              (.nat 1))))
            (.arith .add (.arith .add (.nat 1) (.arith .mul (.var 3) (.get (arg 0) (.nat 3))))
              (.var 2)) (.nat 0))))
      (.nat (rcRCodeN wl rl q uno c d)) W (3000 * W + 9000) := by
    intro _
    have dy2 := rcRDW.gdN I hgD (vy [.nat c]) (nn _ 2 (by omega)) (nn _ 0 (by omega))
    have dd := rcRDW.arith (op := .sub) (z := d) dy2
      (rd [natList y, .nat c] 2 (.nat k) (by simp [hCs])) hd.symm (by omega)
    have vd := rcRDW.var (P := P) (W := W) (env := [.list [.list Cs, .nat i], natList y, .nat c,
      .nat d]) (i := 3) (v := .nat d) rfl (by omega)
    have gq := rd [natList y, .nat c, .nat d] 3 (.nat q) (by simp [hCs])
    have t2 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD (rd [natList y, .nat c, .nat d] 4
      (natList wl) (by simp [hCs])) (vc [.nat d]) (nn _ 0 (by omega))) (nn _ 1 (by omega)) rfl
      (rcR_eval_eq_wt _ _ (by omega))
    have t3 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD (rd [natList y, .nat c, .nat d] 5
      (natList rl) (by simp [hCs])) vd (nn _ 0 (by omega))) (nn _ 1 (by omega)) rfl
      (rcR_eval_eq_wt _ _ (by omega))
    have t4 := rcRDW.arith (op := .mul) t2 t3 rfl (rcR_wt_bitW (rcR_eval_mul_le
      (rcR_eval_eq_le _ _) (rcR_eval_eq_le _ _)) (by omega))
    have s2 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD (rd [natList y, .nat c, .nat d] 4
      (natList wl) (by simp [hCs])) vd (nn _ 0 (by omega))) (nn _ 1 (by omega)) rfl
      (rcR_eval_eq_wt _ _ (by omega))
    have s3 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD (rd [natList y, .nat c, .nat d] 5
      (natList rl) (by simp [hCs])) (vc [.nat d]) (nn _ 0 (by omega))) (nn _ 1 (by omega)) rfl
      (rcR_eval_eq_wt _ _ (by omega))
    have s4 := rcRDW.arith (op := .mul) s2 s3 rfl (rcR_wt_bitW (rcR_eval_mul_le
      (rcR_eval_eq_le _ _) (rcR_eval_eq_le _ _)) (by omega))
    have gu := rd [natList y, .nat c, .nat d] 7 (.nat uno.toNat) (by simp [hCs])
    have s5 := rcRDW.arith (op := .mul) gu s4 rfl (rcR_wt_bitW (rcR_eval_mul_le
      (by cases uno <;> simp) (rcR_eval_mul_le (rcR_eval_eq_le _ _) (rcR_eval_eq_le _ _)))
      (by omega))
    have wc1 := rcR_wt_code c q d
    have wc2 := rcR_wt_code d q c
    have b1 := rcRDW.arith (op := .add) (z := 1 + c * q + d)
      (rcRDW.arith (op := .add) (z := 1 + c * q) (nn _ 1 (by omega))
        (rcRDW.arith (op := .mul) (z := c * q) (vc [.nat d]) gq rfl
          (by have := rcR_wt_mul c q; omega)) rfl
        (by have := rcR_wt_add 1 (c * q); have := rcR_wt_mul c q; have := wt_nat_le 1; omega))
      vd rfl (by omega)
    have b2 := rcRDW.arith (op := .add) (z := 1 + d * q + c)
      (rcRDW.arith (op := .add) (z := 1 + d * q) (nn _ 1 (by omega))
        (rcRDW.arith (op := .mul) (z := d * q) vd gq rfl
          (by have := rcR_wt_mul d q; omega)) rfl
        (by have := rcR_wt_add 1 (d * q); have := rcR_wt_mul d q; have := wt_nat_le 1; omega))
      (vc [.nat d]) rfl (by omega)
    have dite := rcRDW.ite (v := .nat (rcRCodeN wl rl q uno c d)) t4
      (fun hx => by
        have h := (rcR_bit2 _ _).1 hx
        rw [show rcRCodeN wl rl q uno c d = 1 + c * q + d by unfold rcRCodeN; rw [if_pos h]]
        exact b1)
      (fun hx => by
        have h : ¬ (wl.getD c 0 = 1 ∧ rl.getD d 0 = 1) := fun h => ((rcR_bit2 _ _).2 h) hx
        exact rcRDW.ite (v := .nat (rcRCodeN wl rl q uno c d)) s5
          (fun hx' => by
            have h' := (rcR_bitU _ _ _).1 hx'
            rw [show rcRCodeN wl rl q uno c d = 1 + d * q + c by
              unfold rcRCodeN; rw [if_neg h, if_pos h']]
            exact b2)
          (fun hx' => by
            have h' : ¬ (uno = true ∧ wl.getD d 0 = 1 ∧ rl.getD c 0 = 1) := fun h' =>
              ((rcR_bitU _ _ _).2 h') hx'
            rw [show rcRCodeN wl rl q uno c d = 0 by unfold rcRCodeN; rw [if_neg h, if_neg h']]
            exact nn _ 0 (by omega)))
    exact (rcRDW.letE dd dite).mono (by omega)
  -- the whole body
  have dmain := rcRDW.ite (v := .nat R) d0
    (fun hx => by
      have h0 : dl.getD i 0 = 0 := by by_contra h; exact hx (by simp only [BinOp.eval, if_neg h])
      rw [show R = 0 by rw [hRv, if_pos h0]]
      exact nn _ 0 (by omega))
    (fun hx => by
      have h0 : dl.getD i 0 ≠ 0 := by
        intro h; simp only [BinOp.eval, if_pos h] at hx; exact one_ne_zero hx
      exact rcRDW.letE dlk (rcRDW.letE dc (rcRDW.ite (v := .nat R) dcar
        (fun hc' => by
          have hct : car = true := by cases car <;> simp_all
          rw [show R = rcRCarCodeN wl rl q (rowT.getD i 0) c by
            rw [hRv, if_neg h0, if_pos hct]]
          exact carB hct)
        (fun hc' => by
          have hcf : car = false := by cases car <;> simp_all
          rw [show R = rcRCodeN wl rl q uno c d by
            rw [hRv, if_neg h0, if_neg (by simp [hcf]), hd, hy]]
          exact parB hcf))))
  rw [hR] at dmain
  subst hCs
  refine (rcRDW.fn hf dmain).mono ?_
  have p2 := rcR_V10 V
  have c1 := rcR_look_cost hW (x := (Val.list [rcTV Lk, .nat i]).wt) (by omega)
  norm_num at c1 ⊢
  omega

end Cell

end GI.Impl
