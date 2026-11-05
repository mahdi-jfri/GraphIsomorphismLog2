module

public import Workspace.Impl.AggRectRepS3

@[expose] public section

/-!
# The label action read from the table

`piFF` computes `rcRPiN Lk k h j` (`rcR_pi_spec`), by three lookups in the orbit table.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

/-! ### Weights of numbers -/

theorem rcR_wt_add (a b : ℕ) : (Val.nat (a + b)).wt ≤ (Val.nat a).wt + (Val.nat b).wt := by
  rw [wt_nat, wt_nat, wt_nat]; have := GI.Machine.len_add_le_add a b; omega

theorem rcR_wt_mul (a b : ℕ) : (Val.nat (a * b)).wt ≤ (Val.nat a).wt + (Val.nat b).wt := by
  rw [wt_nat, wt_nat, wt_nat]; have := GI.Machine.len_mul_le a b; omega

theorem rcR_wt_sub (a b : ℕ) : (Val.nat (a - b)).wt ≤ (Val.nat a).wt :=
  rcR_wt_nat_mono (Nat.sub_le a b)

theorem rcR_wt_tv_getD (Lk : List (List ℕ)) (i : ℕ) :
    (natList (Lk.getD i [])).wt ≤ (rcTV Lk).wt := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : Lk[i]? with
  | none =>
    show (Val.list []).wt ≤ (Val.list (Lk.map natList)).wt
    rw [wt_list_nil, wt_list_eq]; omega
  | some y =>
    simp only [Option.getD_some]
    exact (wt_le_wt_list (List.mem_map.2 ⟨y, List.mem_of_getElem? hx, rfl⟩)).le

theorem rcR_wt_look (Lk : List (List ℕ)) (i : ℕ) : (natList (rcRLook Lk i)).wt ≤ (rcTV Lk).wt :=
  rcR_wt_tv_getD Lk _

theorem rcR_wt_look1 (Lk : List (List ℕ)) (t : ℕ) :
    (natList (rcRLook1 Lk t)).wt ≤ (rcTV Lk).wt :=
  rcR_wt_tv_getD Lk _

theorem rcR_wt_look2 (Lk : List (List ℕ)) (t a : ℕ) :
    (natList (rcRLook2 Lk t a)).wt ≤ (rcTV Lk).wt :=
  rcR_wt_tv_getD Lk _

theorem rcR_look_cost {V W : ℕ} (hW : W = 100 * (V + 10)) {x : ℕ} (hx : x ≤ W) :
    10 ^ 11 * (x + 10) ^ 3 ≤ 10 ^ 11 * 101 ^ 3 * (V + 10) ^ 3 := by
  have h1 : (x + 10) ^ 3 ≤ (100 * (V + 10) + 1 + 9) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : (100 * (V + 10) + 1 + 9) ^ 3 ≤ (101 * (V + 10)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  rw [mul_pow] at h2
  calc 10 ^ 11 * (x + 10) ^ 3 ≤ 10 ^ 11 * (101 ^ 3 * (V + 10) ^ 3) :=
        Nat.mul_le_mul_left _ (h1.trans h2)
    _ = 10 ^ 11 * 101 ^ 3 * (V + 10) ^ 3 := by ring

section Pi

variable {P : Program} {I : RcRIdx}

set_option maxHeartbeats 2000000 in
/-- **The label action read from the table** at label `j`. -/
theorem rcR_pi_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.piF]? = some I.piFF)
    (hl0 : P.funs[I.look]? = some I.lookF) (hl1 : P.funs[I.look1]? = some I.look1F)
    (hl2 : P.funs[I.look2]? = some I.look2F)
    (hf0 : P.HasAt I.fLk0 (findFuns I.fLk0 I.lk0P)) (hp0 : P.funs[I.lk0P]? = some I.lk0PF)
    (hf1 : P.HasAt I.fLk1 (findFuns I.fLk1 I.lk1P)) (hp1 : P.funs[I.lk1P]? = some I.lk1PF)
    (hf2 : P.HasAt I.fLk2 (findFuns I.fLk2 I.lk2P)) (hp2 : P.funs[I.lk2P]? = some I.lk2PF)
    (Lk : List (List ℕ)) (k : ℕ) (hl : List ℕ) (j : ℕ) :
    FunDet P I.piF (.list [.list [rcTV Lk, .nat k, natList hl], .nat j])
      (.nat (rcRPiN Lk k (fun v => hl.getD v 0) j))
      (10 ^ 20 * ((Val.list [.list [rcTV Lk, .nat k, natList hl], .nat j]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [rcTV Lk, .nat k, natList hl], .nat j]).wt :=
    ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hC : (Val.list [rcTV Lk, .nat k, natList hl]).wt < V := by
    rw [hV]; exact wt_le_wt_list (by simp)
  have hT : (rcTV Lk).wt < (Val.list [rcTV Lk, .nat k, natList hl]).wt := wt_le_wt_list (by simp)
  have hk : (Val.nat k).wt < (Val.list [rcTV Lk, .nat k, natList hl]).wt :=
    wt_le_wt_list (by simp)
  have hh : (natList hl).wt < (Val.list [rcTV Lk, .nat k, natList hl]).wt :=
    wt_le_wt_list (by simp)
  have hj : (Val.nat j).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  -- the names of the values
  obtain ⟨y1, hy1⟩ : ∃ y1, y1 = rcRLook1 Lk (k + j) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = rcRLook Lk (hl.getD (y1.getD 0 0) 0) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = z.getD 1 0 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = z.getD 2 0 := ⟨_, rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ z2, z2 = rcRLook Lk (hl.getD ((rcRLook2 Lk (k + j)
    (y1.getD 2 0)).getD 0 0) 0) := ⟨_, rfl⟩
  have wy1 : (natList y1).wt ≤ (rcTV Lk).wt := hy1 ▸ rcR_wt_look1 Lk (k + j)
  have wz : (natList z).wt ≤ (rcTV Lk).wt := hz ▸ rcR_wt_look Lk _
  have wz2 : (natList z2).wt ≤ (rcTV Lk).wt := hz2 ▸ rcR_wt_look Lk _
  have wA : (Val.nat A).wt ≤ (natList z).wt := hA ▸ rcR_wt_getD_le z 1
  have wB : (Val.nat B).wt ≤ (natList z).wt := hB ▸ rcR_wt_getD_le z 2
  have wkj := rcR_wt_add k j
  -- the environments
  have e0 : ∀ (rest : List Val) (i : ℕ) (v : Val),
      [rcTV Lk, .nat k, natList hl][i]? = some v →
      rcRDW P (.list [.list [rcTV Lk, .nat k, natList hl], .nat j] :: rest)
        (.get (arg 0) (.nat i)) v W (3 * W + i + 9) := fun rest i v h =>
    (rcRDW.get (rcRDW.arg (rest := rest) (by omega) rfl) h).mono (by omega)
  have e1 : ∀ rest : List Val, rcRDW P (.list [.list [rcTV Lk, .nat k, natList hl], .nat j] ::
      rest) (arg 1) (.nat j) W (2 * W + 6) := fun rest =>
    rcRDW.arg (rest := rest) (by omega) rfl
  -- y1
  have dkj := rcRDW.arith (op := .add) (z := k + j) (e0 [] 1 (.nat k) rfl) (e1 []) rfl (by omega)
  have dl1 := rcRDW.call (rcRDW.mk2 (e0 [] 0 (rcTV Lk) rfl) dkj
      (by have := wt_list2_le (rcTV Lk) (.nat (k + j)); omega))
    (rcR_look1_spec hgD hl1 hf1 hp1 Lk (k + j)) (by rw [hy1] at wy1; omega)
  rw [← hy1] at dl1
  -- z
  have r1 : ∀ (rest : List Val), rcRDW P (.list [.list [rcTV Lk, .nat k, natList hl], .nat j] ::
      natList y1 :: rest) (.var 1) (natList y1) W (W + 1) := fun rest =>
    rcRDW.var rfl (by omega)
  have n0 : ∀ env : List Val, rcRDW P env (.nat 0) (.nat 0) W 3 := fun _ =>
    rcRDW.nat 0 (by omega)
  have n1 : ∀ env : List Val, rcRDW P env (.nat 1) (.nat 1) W 4 := fun _ =>
    rcRDW.nat 1 (by omega)
  have n2 : ∀ env : List Val, rcRDW P env (.nat 2) (.nat 2) W 5 := fun _ =>
    rcRDW.nat 2 (by omega)
  have dh := rcRDW.gdN I hgD (e0 [natList y1] 2 (natList hl) rfl)
    (rcRDW.gdN I hgD (r1 []) (n0 _) (n0 _)) (n0 _)
  have wh := rcR_wt_getD_le hl (y1.getD 0 0)
  have dl0 := rcRDW.call (rcRDW.mk2 (e0 [natList y1] 0 (rcTV Lk) rfl) dh
      (by have := wt_list2_le (rcTV Lk) (.nat (hl.getD (y1.getD 0 0) 0)); omega))
    (rcR_look_spec hgD hl0 hf0 hp0 Lk (hl.getD (y1.getD 0 0) 0)) (by rw [hz] at wz; omega)
  rw [← hz] at dl0
  -- A and B
  have r2 : ∀ (rest : List Val), rcRDW P (.list [.list [rcTV Lk, .nat k, natList hl], .nat j] ::
      natList y1 :: natList z :: rest) (.var 2) (natList z) W (W + 1) := fun rest =>
    rcRDW.var rfl (by omega)
  have dA := rcRDW.gdN I hgD (r2 []) (n1 _) (n0 _)
  rw [← hA] at dA
  have dB := rcRDW.gdN I hgD (r2 [.nat A]) (n2 _) (n0 _)
  rw [← hB] at dB
  -- the environment of the body
  have v3 : ∀ rest : List Val, rcRDW P (.list [.list [rcTV Lk, .nat k, natList hl], .nat j] ::
      natList y1 :: natList z :: .nat A :: .nat B :: rest) (.var 3) (.nat A) W (W + 1) :=
    fun rest => rcRDW.var rfl (by omega)
  have v4 : ∀ rest : List Val, rcRDW P (.list [.list [rcTV Lk, .nat k, natList hl], .nat j] ::
      natList y1 :: natList z :: .nat A :: .nat B :: rest) (.var 4) (.nat B) W (W + 1) :=
    fun rest => rcRDW.var rfl (by omega)
  have dAB := rcRDW.arith (op := .eq) (v3 []) (v4 []) rfl (rcR_eval_eq_wt _ _ (by omega))
  -- the second lookup, in the case `A ≠ B`
  have r1' := rcRDW.var (P := P) (W := W) (env := [.list [.list [rcTV Lk, .nat k, natList hl],
    .nat j], natList y1, natList z, .nat A, .nat B]) (i := 1) (v := natList y1) rfl (by omega)
  have dkj' := rcRDW.arith (op := .add) (z := k + j) (e0 [natList y1, natList z, .nat A, .nat B] 1 (.nat k) rfl)
    (e1 [natList y1, natList z, .nat A, .nat B]) rfl (by omega)
  have dy2 := rcRDW.gdN I hgD r1' (n2 _) (n0 _)
  have wy2 := rcR_wt_getD_le y1 2
  have wl2 := rcR_wt_look2 Lk (k + j) (y1.getD 2 0)
  have dl2 := rcRDW.call (rcRDW.mk3 (e0 [natList y1, natList z, .nat A, .nat B] 0 (rcTV Lk) rfl)
      dkj' dy2 (by have := wt_list3_le (rcTV Lk) (.nat (k + j)) (.nat (y1.getD 2 0)); omega))
    (rcR_look2_spec hgD hl2 hf2 hp2 Lk (k + j) (y1.getD 2 0)) (by omega)
  have dh2 := rcRDW.gdN I hgD (e0 [natList y1, natList z, .nat A, .nat B] 2 (natList hl) rfl)
    (rcRDW.gdN I hgD dl2 (n0 _) (n0 _)) (n0 _)
  have wh2 := rcR_wt_getD_le hl ((rcRLook2 Lk (k + j) (y1.getD 2 0)).getD 0 0)
  have w32 := wt_list2_le (rcTV Lk)
    (.nat (hl.getD ((rcRLook2 Lk (k + j) (y1.getD 2 0)).getD 0 0) 0))
  have dl3 := rcRDW.call (rcRDW.mk2 (e0 [natList y1, natList z, .nat A, .nat B] 0 (rcTV Lk) rfl)
      dh2 (by omega))
    (rcR_look_spec hgD hl0 hf0 hp0 Lk _) (by rw [hz2] at wz2; omega)
  rw [← hz2] at dl3
  have v5 := rcRDW.var (P := P) (W := W) (env := [.list [.list [rcTV Lk, .nat k, natList hl],
    .nat j], natList y1, natList z, .nat A, .nat B, natList z2]) (i := 5) (v := natList z2) rfl
    (by omega)
  have dc1 := rcRDW.arith (op := .eq) (v3 [natList z2]) (rcRDW.gdN I hgD v5 (n1 _) (n0 _)) rfl
    (rcR_eval_eq_wt _ _ (by omega))
  have dc2 := rcRDW.arith (op := .eq) (v3 [natList z2]) (rcRDW.gdN I hgD v5 (n2 _) (n0 _)) rfl
    (rcR_eval_eq_wt _ _ (by omega))
  have dsum := rcRDW.arith (op := .add) (z := BinOp.eval .eq A (z2.getD 1 0) + BinOp.eval .eq A (z2.getD 2 0)) dc1 dc2 rfl (by
    have := rcR_wt_add (BinOp.eval .eq A (z2.getD 1 0)) (BinOp.eval .eq A (z2.getD 2 0))
    have := rcR_eval_eq_wt A (z2.getD 1 0) (W := 3) le_rfl
    have := rcR_eval_eq_wt A (z2.getD 2 0) (W := 3) le_rfl
    omega)
  have dlt := rcRDW.arith (op := .lt) (n0 _) dsum rfl (rcR_eval_lt_wt _ _ (by omega))
  -- the value
  obtain ⟨R, hR⟩ : ∃ R, R = (if A = B then A else if A = z2.getD 1 0 ∨ A = z2.getD 2 0 then A
    else B) := ⟨_, rfl⟩
  have wR : (Val.nat R).wt ≤ W := by
    rw [hR]; split_ifs <;> omega
  have dite := rcRDW.ite (v := .nat R) dAB
    (fun hx => by
      have h1 : A = B := by by_contra h; exact hx (by simp [BinOp.eval, h])
      have eR : R = A := by rw [hR, if_pos h1]
      rw [eR]; exact v3 [])
    (fun hx => by
      have h1 : A ≠ B := by intro h; simp [BinOp.eval, h] at hx
      exact rcRDW.letE dl3 (rcRDW.ite (v := .nat R) dlt
        (fun hx' => by
          have h2 : A = z2.getD 1 0 ∨ A = z2.getD 2 0 := by
            by_contra h
            rw [not_or] at h
            exact hx' (by simp only [BinOp.eval, if_neg h.1, if_neg h.2]; rfl)
          have eR : R = A := by rw [hR, if_neg h1, if_pos h2]
          rw [eR]; exact v3 [natList z2])
        (fun hx' => by
          have h2 : ¬ (A = z2.getD 1 0 ∨ A = z2.getD 2 0) := by
            rintro (h | h) <;> simp [BinOp.eval, h] at hx'
          have eR : R = B := by rw [hR, if_neg h1, if_neg h2]
          rw [eR]; exact v4 [natList z2])))
  have dsub := rcRDW.arith (op := .sub) (z := R - k) dite
    (e0 [natList y1, natList z, .nat A, .nat B] 1 (.nat k) rfl) rfl
    (by have := rcR_wt_sub R k; omega)
  have dall := rcRDW.letE dl1 (rcRDW.letE dl0 (rcRDW.letE dA (rcRDW.letE dB dsub)))
  have eV : R - k = rcRPiN Lk k (fun v => hl.getD v 0) j := by
    simp only [hR, hA, hB, hz, hz2, hy1, rcRPiN]
  rw [eV] at dall
  refine (rcRDW.fn hf dall).mono ?_
  have c1 := rcR_look_cost hW (x := (Val.list [rcTV Lk, .nat (k + j)]).wt)
    (by have := wt_list2_le (rcTV Lk) (.nat (k + j)); omega)
  have c2 := rcR_look_cost hW (x := (Val.list [rcTV Lk, .nat (hl.getD (y1.getD 0 0) 0)]).wt)
    (by have := wt_list2_le (rcTV Lk) (.nat (hl.getD (y1.getD 0 0) 0)); omega)
  have c3 := rcR_look_cost hW (x := (Val.list [rcTV Lk, .nat (k + j), .nat (y1.getD 2 0)]).wt)
    (by have := wt_list3_le (rcTV Lk) (.nat (k + j)) (.nat (y1.getD 2 0)); omega)
  have c4 := rcR_look_cost hW (x := (Val.list [rcTV Lk,
    .nat (hl.getD ((rcRLook2 Lk (k + j) (y1.getD 2 0)).getD 0 0) 0)]).wt)
    (by omega)
  have p2 := rcR_V10 V
  norm_num at c1 c2 c3 c4 ⊢
  omega

end Pi

end GI.Impl
