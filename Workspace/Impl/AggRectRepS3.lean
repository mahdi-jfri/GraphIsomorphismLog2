import Workspace.Impl.AggRectRepS2

/-!
# Keys, row numbers, small labels and table lookups

The steps that call a library loop: the small-label test (`count`), the key of a position
(`rcRKeyN`, by `find`), the key test of `rcRKeysN`, the row number `rcRRowN'` (`findEq`), and the
three lookups `rcRLook`, `rcRLook1`, `rcRLook2` in the orbit table (`find`). Each costs at most
a constant times `(V + 10)³` for the input weight `V`.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

/-! ### Powers of the input weight -/

theorem rcR_pw_scale (V d : ℕ) : (100 * (V + 10) + 1) ^ d ≤ 101 ^ d * (V + 10) ^ d := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by omega) d

theorem rcR_pw_le {a b : ℕ} (h : a ≤ b) (c d : ℕ) : (a + c) ^ d ≤ (b + c) ^ d :=
  Nat.pow_le_pow_left (by omega) d

theorem rcR_pw10 (W d : ℕ) : (W + 10) ^ d ≤ 10 ^ d * (W + 1) ^ d := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by omega) d

theorem rcR_V10 (V : ℕ) : V + 10 ≤ (V + 10) ^ 3 := by
  have : 1 ≤ (V + 10) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc V + 10 = (V + 10) * 1 := by ring
    _ ≤ (V + 10) * (V + 10) ^ 2 := Nat.mul_le_mul_left _ this
    _ = (V + 10) ^ 3 := by ring

theorem rcR_pw_1_10 (V : ℕ) : (V + 1) ^ 3 ≤ (V + 10) ^ 3 := Nat.pow_le_pow_left (by omega) 3

theorem rcR_findIdx_le {α : Type} (l : List α) (p : α → Bool) : l.findIdx p ≤ l.length :=
  List.findIdx_le_length

theorem rcR_natList_len (l : List ℕ) : l.length < (natList l).wt := by
  have := length_lt_wt_list (l.map Val.nat); simpa [natList] using this

theorem rcR_tv_getD (ts : List (List ℕ)) (i : ℕ) :
    (ts.map natList).getD i (.list []) = natList (ts.getD i []) := by
  rw [show (Val.list [] : Val) = natList [] from rfl, List.getD_map]

section Steps

variable {P : Program} {I : RcRIdx}

/-- **The small-label test**: at most two labels equal the label of `c`. -/
theorem rcR_smP_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.smP]? = some I.smPF)
    (hc : P.HasAt I.cnt (countFuns I.cnt)) (labs : List ℕ) (c : ℕ)
    (hB : ∀ x ∈ labs, x ≤ (Val.list [natList labs, .nat c]).wt) :
    FunDet P I.smP (.list [natList labs, .nat c])
      (boolVal (decide (labs.count (labs.getD c 0) ≤ 2)))
      (10 ^ 7 * ((Val.list [natList labs, .nat c]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [natList labs, .nat c]).wt := ⟨_, rfl⟩
  rw [← hV] at hB ⊢
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hl : (natList labs).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have hlen := rcR_natList_len labs
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [natList labs, .nat c]) (W := W) (j := 0)
    (v := natList labs) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [natList labs, .nat c]) (W := W) (j := 1)
    (v := .nat c) (by omega) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [natList labs, .nat c]]) 0 (by omega)
  have n3 := rcRDW.nat (P := P) (W := W) (env := [.list [natList labs, .nat c]]) 3 (by omega)
  have g := rcRDW.gdN I hgD a0 a1 n0
  have hj := rcR_getD_le hB c
  have w1 := wt_nat_le (labs.getD c 0)
  have w2 := wt_list2_le (.nat (labs.getD c 0)) (natList labs)
  have m := rcRDW.mk2 g a0 (by omega)
  have hcnt := count_spec hc (xs := labs) (j := labs.getD c 0) (B := V) hB hj (by omega)
  have hcl : labs.count (labs.getD c 0) ≤ labs.length := List.count_le_length
  have w3 := wt_nat_le (labs.count (labs.getD c 0))
  have cl := rcRDW.call m hcnt (by omega)
  have hz : BinOp.eval .lt (labs.count (labs.getD c 0)) 3 =
      (decide (labs.count (labs.getD c 0) ≤ 2)).toNat := by
    rw [rcR_ltT, show decide (labs.count (labs.getD c 0) < 3) =
      decide (labs.count (labs.getD c 0) ≤ 2) from decide_eq_decide.2 (by omega)]
  have r := rcRDW.arith (op := .lt) cl n3 hz (rcR_wt_toNat _ (by omega))
  refine (rcRDW.fn hf r).mono ?_
  have p1 := rcR_pw_1_10 V
  have p2 := rcR_V10 V
  have hK : countK = 100000 := rfl
  rw [hK]
  nlinarith

/-- **The key of a position**: `rcRKeyN dl rl k i`, on `[C, i]` for a context `C` that starts
with `dl`, `rl`, `range k`. -/
theorem rcR_keyN_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.keyN]? = some I.keyNF)
    (hfk : P.HasAt I.fKey (findFuns I.fKey I.keyP)) (hkp : P.funs[I.keyP]? = some I.keyPF)
    (dl rl : List ℕ) (k : ℕ) (rest : List Val) (i : ℕ) :
    FunDet P I.keyN
      (.list [.list (natList dl :: natList rl :: natList (List.range k) :: rest), .nat i])
      (.nat (rcRKeyN dl rl k i))
      (10 ^ 11 * ((Val.list [.list (natList dl :: natList rl :: natList (List.range k) :: rest),
        .nat i]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list (natList dl :: natList rl ::
    natList (List.range k) :: rest), .nat i]).wt := ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hC : (Val.list (natList dl :: natList rl :: natList (List.range k) :: rest)).wt < V := by
    rw [hV]; exact wt_le_wt_list (by simp)
  have hdl : (natList dl).wt < (Val.list (natList dl :: natList rl ::
    natList (List.range k) :: rest)).wt := wt_le_wt_list (by simp)
  have hrl : (natList rl).wt < (Val.list (natList dl :: natList rl ::
    natList (List.range k) :: rest)).wt := wt_le_wt_list (by simp)
  have hrk : (natList (List.range k)).wt < (Val.list (natList dl :: natList rl ::
    natList (List.range k) :: rest)).wt := wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list (natList dl :: natList rl ::
    natList (List.range k) :: rest), .nat i]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list (natList dl :: natList rl ::
    natList (List.range k) :: rest), .nat i]) (W := W) (j := 1) (v := .nat i) (by omega) rfl
  have gdl := rcRDW.get a0 (j := 0) (v := natList dl) rfl
  have grl := rcRDW.get a0 (j := 1) (v := natList rl) rfl
  have grk := rcRDW.get a0 (j := 2) (v := natList (List.range k)) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.list (natList dl :: natList rl ::
    natList (List.range k) :: rest), .nat i]]) 0 (by omega)
  have g := rcRDW.gdN I hgD grl a1 n0
  have wli := rcR_wt_getD_le rl i
  have w3 := wt_list3_le (natList dl) (natList rl) (.nat (rl.getD i 0))
  have m3 := rcRDW.mk3 gdl grl g (by omega)
  have w2 := wt_list2_le (.list [natList dl, natList rl, .nat (rl.getD i 0)])
    (natList (List.range k))
  have m2 := rcRDW.mk2 m3 grk (by omega)
  have hfind := rcR_findN1 hfk (c := .list [natList dl, natList rl, .nat (rl.getD i 0)])
    (xs := List.range k) (t := fun j => dl.getD j 0 == 1 && rl.getD j 0 == rl.getD i 0)
    (K := 5000) (W := W) (fun j _ => rcR_keyP_spec hgD hkp dl rl (rl.getD i 0) j) (by omega)
  have hk1 := rcR_findIdx_le (List.range k) (fun j => dl.getD j 0 == 1 && rl.getD j 0 ==
    rl.getD i 0)
  have hk2 := rcR_natList_len (List.range k)
  rw [List.length_range] at hk1 hk2
  have w4 := wt_nat_le ((List.range k).findIdx fun j => dl.getD j 0 == 1 && rl.getD j 0 ==
    rl.getD i 0)
  have cl := rcRDW.call m2 hfind (by omega)
  refine (rcRDW.fn hf cl).mono ?_
  have p1 := rcR_pw_scale V 3
  have p2 := rcR_V10 V
  rw [← hW] at p1
  have : (10 * 5000 + 3000) * (W + 1) ^ 3 ≤ 53000 * (101 ^ 3 * (V + 10) ^ 3) :=
    Nat.mul_le_mul_left _ p1
  norm_num at this ⊢
  omega

/-- **The key test** of `rcRKeysN`: `j` in the domain and its own key. -/
theorem rcR_keysP_spec (hgD : P.funs[I.gD]? = some rcRGetDF)
    (hf : P.funs[I.keysP]? = some I.keysPF) (hkn : P.funs[I.keyN]? = some I.keyNF)
    (hfk : P.HasAt I.fKey (findFuns I.fKey I.keyP)) (hkp : P.funs[I.keyP]? = some I.keyPF)
    (dl rl : List ℕ) (k j : ℕ) :
    FunDet P I.keysP (.list [.list [natList dl, natList rl, natList (List.range k)], .nat j])
      (boolVal (dl.getD j 0 == 1 && rcRKeyN dl rl k j == j))
      (10 ^ 12 * ((Val.list [.list [natList dl, natList rl, natList (List.range k)],
        .nat j]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [natList dl, natList rl, natList (List.range k)],
    .nat j]).wt := ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hC : (Val.list [natList dl, natList rl, natList (List.range k)]).wt < V := by
    rw [hV]; exact wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList dl, natList rl,
    natList (List.range k)], .nat j]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList dl, natList rl,
    natList (List.range k)], .nat j]) (W := W) (j := 1) (v := .nat j) (by omega) rfl
  have v0 := rcRDW.var (P := P) (W := W) (env := [.list [.list [natList dl, natList rl,
    natList (List.range k)], .nat j]]) (i := 0) rfl (by omega)
  have gdl := rcRDW.get a0 (j := 0) (v := natList dl) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [natList dl, natList rl,
    natList (List.range k)], .nat j]]) 0 (by omega)
  have n1 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [natList dl, natList rl,
    natList (List.range k)], .nat j]]) 1 (by omega)
  have e1 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD gdl a1 n0) n1 rfl
    (rcR_eval_eq_wt _ _ (by omega))
  have hkey := rcR_keyN_spec hgD hkn hfk hkp dl rl k [] j
  rw [← hV] at hkey
  have hk1 : rcRKeyN dl rl k j ≤ k := by
    have := rcR_findIdx_le (List.range k) (fun t => dl.getD t 0 == 1 && rl.getD t 0 ==
      rl.getD j 0)
    rw [List.length_range] at this; exact this
  have hk2 := rcR_natList_len (List.range k)
  rw [List.length_range] at hk2
  have hrk : (natList (List.range k)).wt < (Val.list [natList dl, natList rl,
    natList (List.range k)]).wt := wt_le_wt_list (by simp)
  have w4 := wt_nat_le (rcRKeyN dl rl k j)
  have ck := rcRDW.call v0 hkey (by omega)
  have e2 := rcRDW.arith (op := .eq) ck a1 rfl (rcR_eval_eq_wt _ _ (by omega))
  rw [rcR_eqT] at e1 e2
  have e4 := rcRDW.arith (op := .mul) e1 e2 (rcR_andT _ _) (rcR_wt_toNat _ (by omega))
  refine (rcRDW.fn hf e4).mono ?_
  have p2 := rcR_V10 V
  omega

/-- **The row number** of a position: `rcRRowN' dl rl k i`. -/
theorem rcR_rowF_spec (hgD : P.funs[I.gD]? = some rcRGetDF)
    (hf : P.funs[I.rowF]? = some I.rowFF) (hkn : P.funs[I.keyN]? = some I.keyNF)
    (hfk : P.HasAt I.fKey (findFuns I.fKey I.keyP)) (hkp : P.funs[I.keyP]? = some I.keyPF)
    (hfe : P.HasAt I.fEq (findEqFuns I.fEq))
    (dl rl : List ℕ) (k : ℕ) (keys : List ℕ) (hkeys : ∀ x ∈ keys, x < k) (i : ℕ) :
    FunDet P I.rowF
      (.list [.list [natList dl, natList rl, natList (List.range k), natList keys], .nat i])
      (.nat (keys.findIdx fun t => t == rcRKeyN dl rl k i))
      (10 ^ 12 * ((Val.list [.list [natList dl, natList rl, natList (List.range k),
        natList keys], .nat i]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [natList dl, natList rl, natList (List.range k),
    natList keys], .nat i]).wt := ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hC : (Val.list [natList dl, natList rl, natList (List.range k), natList keys]).wt < V := by
    rw [hV]; exact wt_le_wt_list (by simp)
  have hks : (natList keys).wt < (Val.list [natList dl, natList rl, natList (List.range k),
    natList keys]).wt := wt_le_wt_list (by simp)
  have hrk : (natList (List.range k)).wt < (Val.list [natList dl, natList rl,
    natList (List.range k), natList keys]).wt := wt_le_wt_list (by simp)
  have hk2 := rcR_natList_len (List.range k)
  rw [List.length_range] at hk2
  have hkl := rcR_natList_len keys
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList dl, natList rl,
    natList (List.range k), natList keys], .nat i]) (W := W) (j := 0) (by omega) rfl
  have v0 := rcRDW.var (P := P) (W := W) (env := [.list [.list [natList dl, natList rl,
    natList (List.range k), natList keys], .nat i]]) (i := 0) rfl (by omega)
  have gks := rcRDW.get a0 (j := 3) (v := natList keys) rfl
  have hkey := rcR_keyN_spec hgD hkn hfk hkp dl rl k [natList keys] i
  rw [← hV] at hkey
  have hk1 : rcRKeyN dl rl k i ≤ k := by
    have := rcR_findIdx_le (List.range k) (fun t => dl.getD t 0 == 1 && rl.getD t 0 ==
      rl.getD i 0)
    rw [List.length_range] at this; exact this
  have w4 := wt_nat_le (rcRKeyN dl rl k i)
  have ck := rcRDW.call v0 hkey (by omega)
  have w2 := wt_list2_le (.nat (rcRKeyN dl rl k i)) (natList keys)
  have m := rcRDW.mk2 ck gks (by omega)
  have hfe' := findEq_spec hfe (xs := keys) (j := rcRKeyN dl rl k i) (B := V)
    (fun x hx => by have := hkeys x hx; omega) (by omega) (by omega)
  have hfi := rcR_findIdx_le keys (fun x => decide (x = rcRKeyN dl rl k i))
  have w5 := wt_nat_le (keys.findIdx fun x => decide (x = rcRKeyN dl rl k i))
  have cl := rcRDW.call m hfe' (by omega)
  have e : (keys.findIdx fun x => decide (x = rcRKeyN dl rl k i)) =
      keys.findIdx fun t => t == rcRKeyN dl rl k i := by
    congr 1
  rw [e] at cl
  refine (rcRDW.fn hf cl).mono ?_
  have p1 := rcR_pw_1_10 V
  have p2 := rcR_V10 V
  have hK : findEqK = 100000 := rfl
  rw [hK]
  omega

/-! ### The lookups in the orbit table -/

/-- **`rcRLook`.** -/
theorem rcR_look_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.look]? = some I.lookF)
    (hfl : P.HasAt I.fLk0 (findFuns I.fLk0 I.lk0P)) (hp : P.funs[I.lk0P]? = some I.lk0PF)
    (Lk : List (List ℕ)) (i : ℕ) :
    FunDet P I.look (.list [rcTV Lk, .nat i]) (natList (rcRLook Lk i))
      (10 ^ 11 * ((Val.list [rcTV Lk, .nat i]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [rcTV Lk, .nat i]).wt := ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hT : (rcTV Lk).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have hT' : (Val.list (Lk.map natList)).wt < V := hT
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [rcTV Lk, .nat i]) (W := W) (j := 0)
    (v := .list (Lk.map natList)) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [rcTV Lk, .nat i]) (W := W) (j := 1)
    (v := .nat i) (by omega) rfl
  have w2 := wt_list2_le (.nat i) (rcTV Lk)
  have hi : (Val.nat i).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have m := rcRDW.mk2 a1 a0 (by unfold rcTV at w2; omega)
  have hfind := rcR_findL1 hfl (c := .nat i) (ts := Lk) (t := fun y => y.getD 0 0 == i)
    (K := 5000) (W := W) (fun y _ => rcR_lk0P_spec hgD hp i y) (by omega)
  have hn := rcR_findIdx_le Lk (fun y => y.getD 0 0 == i)
  have hl := length_lt_wt_list (Lk.map natList)
  rw [List.length_map] at hl
  have w5 := wt_nat_le (Lk.findIdx fun y => y.getD 0 0 == i)
  have cl := rcRDW.call m hfind (by omega)
  have nl := rcRDW.nil (P := P) (env := [.list [rcTV Lk, .nat i]]) (W := W) (by omega)
  have g := rcRDW.gd I hgD a0 cl nl
  rw [rcR_tv_getD] at g
  refine (rcRDW.fn hf g).mono ?_
  have p1 := rcR_pw_scale V 3
  rw [← hW] at p1
  have : (10 * 5000 + 3000) * (W + 1) ^ 3 ≤ 53000 * (101 ^ 3 * (V + 10) ^ 3) :=
    Nat.mul_le_mul_left _ p1
  have p2 := rcR_V10 V
  norm_num at this ⊢
  omega

/-- **`rcRLook1`.** -/
theorem rcR_look1_spec (hgD : P.funs[I.gD]? = some rcRGetDF)
    (hf : P.funs[I.look1]? = some I.look1F)
    (hfl : P.HasAt I.fLk1 (findFuns I.fLk1 I.lk1P)) (hp : P.funs[I.lk1P]? = some I.lk1PF)
    (Lk : List (List ℕ)) (t : ℕ) :
    FunDet P I.look1 (.list [rcTV Lk, .nat t]) (natList (rcRLook1 Lk t))
      (10 ^ 11 * ((Val.list [rcTV Lk, .nat t]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [rcTV Lk, .nat t]).wt := ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hT : (rcTV Lk).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have hT' : (Val.list (Lk.map natList)).wt < V := hT
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [rcTV Lk, .nat t]) (W := W) (j := 0)
    (v := .list (Lk.map natList)) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [rcTV Lk, .nat t]) (W := W) (j := 1)
    (v := .nat t) (by omega) rfl
  have w2 := wt_list2_le (.nat t) (rcTV Lk)
  have hi : (Val.nat t).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have m := rcRDW.mk2 a1 a0 (by unfold rcTV at w2; omega)
  have hfind := rcR_findL1 hfl (c := .nat t) (ts := Lk) (t := fun y => y.getD 1 0 == t)
    (K := 5000) (W := W) (fun y _ => rcR_lk1P_spec hgD hp t y) (by omega)
  have hn := rcR_findIdx_le Lk (fun y => y.getD 1 0 == t)
  have hl := length_lt_wt_list (Lk.map natList)
  rw [List.length_map] at hl
  have w5 := wt_nat_le (Lk.findIdx fun y => y.getD 1 0 == t)
  have cl := rcRDW.call m hfind (by omega)
  have nl := rcRDW.nil (P := P) (env := [.list [rcTV Lk, .nat t]]) (W := W) (by omega)
  have g := rcRDW.gd I hgD a0 cl nl
  rw [rcR_tv_getD] at g
  refine (rcRDW.fn hf g).mono ?_
  have p1 := rcR_pw_scale V 3
  rw [← hW] at p1
  have : (10 * 5000 + 3000) * (W + 1) ^ 3 ≤ 53000 * (101 ^ 3 * (V + 10) ^ 3) :=
    Nat.mul_le_mul_left _ p1
  have p2 := rcR_V10 V
  norm_num at this ⊢
  omega

/-- **`rcRLook2`.** -/
theorem rcR_look2_spec (hgD : P.funs[I.gD]? = some rcRGetDF)
    (hf : P.funs[I.look2]? = some I.look2F)
    (hfl : P.HasAt I.fLk2 (findFuns I.fLk2 I.lk2P)) (hp : P.funs[I.lk2P]? = some I.lk2PF)
    (Lk : List (List ℕ)) (t a : ℕ) :
    FunDet P I.look2 (.list [rcTV Lk, .nat t, .nat a]) (natList (rcRLook2 Lk t a))
      (10 ^ 11 * ((Val.list [rcTV Lk, .nat t, .nat a]).wt + 10) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [rcTV Lk, .nat t, .nat a]).wt := ⟨_, rfl⟩
  rw [← hV]
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + 10) := ⟨_, rfl⟩
  have hT : (rcTV Lk).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have hT' : (Val.list (Lk.map natList)).wt < V := hT
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [rcTV Lk, .nat t, .nat a]) (W := W) (j := 0)
    (v := .list (Lk.map natList)) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [rcTV Lk, .nat t, .nat a]) (W := W) (j := 1)
    (v := .nat t) (by omega) rfl
  have a2 := rcRDW.arg (P := P) (rest := []) (vs := [rcTV Lk, .nat t, .nat a]) (W := W) (j := 2)
    (v := .nat a) (by omega) rfl
  have ht : (Val.nat t).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have ha : (Val.nat a).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have w1 := wt_list2_le (.nat t) (.nat a)
  have m1 := rcRDW.mk2 a1 a2 (by omega)
  have w2 := wt_list2_le (.list [.nat t, .nat a]) (rcTV Lk)
  have m := rcRDW.mk2 m1 a0 (by unfold rcTV at w2; omega)
  have hfind := rcR_findL1 hfl (c := .list [.nat t, .nat a]) (ts := Lk)
    (t := fun y => y.getD 1 0 == t && !(y.getD 2 0 == a))
    (K := 5000) (W := W) (fun y _ => rcR_lk2P_spec hgD hp t a y) (by omega)
  have hn := rcR_findIdx_le Lk (fun y => y.getD 1 0 == t && !(y.getD 2 0 == a))
  have hl := length_lt_wt_list (Lk.map natList)
  rw [List.length_map] at hl
  have w5 := wt_nat_le (Lk.findIdx fun y => y.getD 1 0 == t && !(y.getD 2 0 == a))
  have cl := rcRDW.call m hfind (by omega)
  have nl := rcRDW.nil (P := P) (env := [.list [rcTV Lk, .nat t, .nat a]]) (W := W) (by omega)
  have g := rcRDW.gd I hgD a0 cl nl
  rw [rcR_tv_getD] at g
  refine (rcRDW.fn hf g).mono ?_
  have p1 := rcR_pw_scale V 3
  rw [← hW] at p1
  have : (10 * 5000 + 3000) * (W + 1) ^ 3 ≤ 53000 * (101 ^ 3 * (V + 10) ^ 3) :=
    Nat.mul_le_mul_left _ p1
  have p2 := rcR_V10 V
  norm_num at this ⊢
  omega

end Steps

end GI.Impl
