module

public import Workspace.Impl.AggItemC1Chk

@[expose] public section

/-!
# Case 1 as a program: the item

`itC1F` computes the Case 1 item from orbit labels `labX`, `labY` of the certificate groups:

1. the data of both labelings (`itDatF`);
2. whether the numbers of points in blocks of each size agree (`itChkF`); if not, no overcoset;
3. otherwise a point `a` with `labX a ≠ a`, the transposition `t = (labX a, a)`, the generators
   `itcGp labX` of the stabilizer, and the Schreier list `itcMs labX a` of its even part;
4. the aligning permutation `posY⁻¹ posX`, times `t` if it is odd.

`it_c1_spec`: the program returns the overcosets `itcOsM … (itcMs labX a)` as `lcOv` values.
`it_c1_itemM`: these stand for the overcosets of the model's `caseOneItem X Y` (`asOvAt`), and
their lists generate their groups. The callees are given by their specs.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {q : ℕ}

/-! ### The overcosets with the program's generators -/

/-- The program's generators of the even stabilizer. -/
noncomputable def itcMs (labX : Fin q → ℕ) (a : Fin q) : List (Perm (Fin q)) :=
  (List.range (2 * (itcGp labX).length)).map (itSchE (itcT labX a) (itcGp labX))

/-- The overcosets of `itcOs` with the generators `ms`. -/
noncomputable def itcOsM {gx : List (Perm (Fin q))} {labX : Fin q → ℕ}
    (h : ItcLab gx labX) (labY : Fin q → ℕ) {a : Fin q} (ha : labX a ≠ a)
    (E₀ : Subgroup (alternatingGroup (Fin q))) (ms : List (Perm (Fin q))) : List (LcOver q) :=
  (itcOs h labY ha E₀).map fun o => (o.1, o.2.1, ms)

theorem itcMs_gens (labX : Fin q → ℕ) (a : Fin q) :
    gens (itcMs labX a) = gens (itpSch (itcT labX a) (itcGens labX)) := by
  rw [itcMs, itSchE_gens]
  unfold gens
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, itp_mem_sch, itcGp_mem]

theorem itcOs_snd {gx : List (Perm (Fin q))} {labX : Fin q → ℕ} {h : ItcLab gx labX}
    {labY : Fin q → ℕ} {a : Fin q} {ha : labX a ≠ a} {E₀ : Subgroup (alternatingGroup (Fin q))}
    {o : LcOver q} (ho : o ∈ itcOs h labY ha E₀) :
    o.2.2 = itpSch (itcT labX a) (itcGens labX) := by
  classical
  unfold itcOs at ho
  split_ifs at ho
  · rw [List.mem_singleton] at ho; subst ho; rfl
  · simp at ho

variable {Ω C : Type} {P : Params} {S : State Ω C}

/-- **The Case 1 item with the program's generators.** -/
theorem it_c1_itemM (L : GiantLabels S) {ℓ : ℕ} (X Y : GI.Algorithm.Canon L.q P.κ ℓ)
    {gx gy : List (Perm (Fin L.q))} {labX labY : Fin L.q → ℕ}
    (hX : gens gx = X.grp) (hY : gens gy = Y.grp) (hlX : ItcLab gx labX) (hlY : ItcLab gy labY)
    {a : Fin L.q} (ha : labX a ≠ a) :
    ∃ ovs, (caseOneItem (P := P) (S := S) X Y).script = Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L)
        (itcOsM hlX labY ha (evenStab (q := L.q) (labelOrbitPart X.grp)) (itcMs labX a)) ovs ∧
      ∀ o ∈ itcOsM hlX labY ha (evenStab (q := L.q) (labelOrbitPart X.grp)) (itcMs labX a),
        gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
  obtain ⟨ovs, h1, h2, h3⟩ := it_c1_item (P := P) L X Y hX hY hlX hlY ha
  refine ⟨ovs, h1, ?_, ?_⟩
  · rw [itcOsM, List.forall₂_map_left_iff]
    exact h2.imp fun _ _ h => h
  · intro o ho
    rw [itcOsM, List.mem_map] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    show gens (itcMs labX a) = _
    rw [itcMs_gens, ← itcOs_snd ho', h3 o' ho']

/-! ### The program -/

/-- On `[encFun labX, encFun labY]`: the Case 1 item. -/
def itC1F (dat chk fnd swt gen sch cmp par : ℕ) : Expr :=
  .letE (.call dat (.get (.var 0) (.nat 0)))
  (.letE (.call dat (.get (.var 0) (.nat 1)))
  (.letE (.call chk (mk2 (.get (.var 1) (.nat 1)) (.get (.var 2) (.nat 1))))
  (.ite (.var 3)
    (.letE (.call fnd (mk2 (.get (.var 0) (.nat 0)) (.get (.var 1) (.nat 4))))
    (.letE (.call swt (mk2 (mk2 (.get (.get (.var 0) (.nat 0)) (.var 4)) (.var 4))
      (.get (.var 1) (.nat 4))))
    (.letE (.call gen (.var 1))
    (.letE (.call sch (mk2 (.var 5) (.var 6)))
    (.letE (.call cmp (mk2 (.get (.var 2) (.nat 3)) (.get (.var 1) (.nat 2))))
    (.letE (.call par (.var 8))
    (.letE (.ite (.var 9) (.call cmp (mk2 (.var 8) (.var 5))) (.var 8))
      (.snoc .nil (mk2 (.var 10) (.var 7))))))))))
    .nil)))

/-- The cost bound of `itC1F`. -/
def itC1C (q : ℕ) : ℕ := 10 ^ 10 * (q + 1) ^ 6

theorem itpAlign_eq (labX labY : Fin q → ℕ) :
    itpAlign labX labY = (itpPosE labY)⁻¹ * itpPosE labX := rfl

theorem itcGp_length (lab : Fin q → ℕ) : (itcGp lab).length ≤ (q + 1) ^ 2 := by
  simp only [itcGp, List.length_append, List.length_map, List.length_range]; nlinarith

theorem itcMs_length (lab : Fin q → ℕ) (a : Fin q) : (itcMs lab a).length ≤ 2 * (q + 1) ^ 2 := by
  have := itcGp_length lab
  simp only [itcMs, List.length_map, List.length_range]; omega

open Classical in
set_option maxHeartbeats 8000000 in
/-- **The Case 1 item as a program.** -/
theorem it_c1_spec {P : Program} {f dat chk fnd ft swt gen sch cmp par : ℕ}
    (hf : P.funs[f]? = some (itC1F dat chk fnd swt gen sch cmp par))
    (hdat : ∀ lab : Fin q → ℕ, (∀ x, lab x < q) → FunDet P dat (encFun lab) (itDatV lab) (itDatC q))
    (hchk : ∀ labX labY : Fin q → ℕ, FunDet P chk (.list [encFun (itpSz labX), encFun (itpSz labY)])
      (boolVal (decide (∀ s, itpCnt labX s = itpCnt labY s))) (itChkC q))
    (hfd : P.HasAt fnd (findFuns fnd ft)) (hft : P.funs[ft]? = some itFixT)
    (hswt : ∀ u v : Fin q, FunDet P swt (.list [.list [.nat u, .nat v], natList (List.range q)])
      (encPerm (Equiv.swap u v)) (10 ^ 5 * (q + 1) ^ 3))
    (hgen : ∀ {gs : List (Perm (Fin q))} {lab : Fin q → ℕ}, ItcLab gs lab →
      FunDet P gen (itDatV lab) (.list ((itcGp lab).map encPerm)) (itGensC q))
    (hsch : ∀ (t : Perm (Fin q)) (S : List (Perm (Fin q))), S.length ≤ (q + 1) ^ 2 →
      FunDet P sch (.list [encPerm t, .list (S.map encPerm)])
        (.list (((List.range (2 * S.length)).map (itSchE t S)).map encPerm)) (itSchC q))
    (hcmp : P.HasAt cmp (composeFuns cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    {gx gy : List (Perm (Fin q))} {labX labY : Fin q → ℕ} (hlX : ItcLab gx labX)
    (hlY : ItcLab gy labY) (hex : ∃ a : Fin q, labX a ≠ a)
    (E₀ : Subgroup (alternatingGroup (Fin q))) :
    ∃ (a : Fin q) (ha : labX a ≠ a), FunDet P f (.list [encFun labX, encFun labY])
      (.list ((itcOsM hlX labY ha E₀ (itcMs labX a)).map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2))
      (itC1C q) := by
  have hltX : ∀ x, labX x < q := fun x => (hlX.min x).1
  have hltY : ∀ x, labY x < q := fun x => (hlY.min x).1
  obtain ⟨a, ha, hfa⟩ := it_fnd_spec hfd hft hltX hex
  refine ⟨a, ha, ?_⟩
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq5 : (q + 1) ^ 4 ≤ (q + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq6 : (q + 1) ^ 5 ≤ (q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := 200 * (q + 1) ^ 4
  -- weights
  have hLX := it_encFun_wt labX fun x => (hltX x).le
  have hLY := it_encFun_wt labY fun x => (hltY x).le
  have hDX := it_datV_wt labX hltX
  have hDY := it_datV_wt labY hltY
  have hSX := it_encFun_wt (itpSz labX) (itpSz_le labX)
  have hSY := it_encFun_wt (itpSz labY) (itpSz_le labY)
  have hR := it_range_wt (q := q)
  have hPX := wt_encPerm_le (itpPosE labX)
  have hIY := wt_encPerm_le (itpPosE labY)⁻¹
  have hT := wt_encPerm_le (itcT labX a)
  have hAl := wt_encPerm_le (itpAlign labX labY)
  have hSg := wt_encPerm_le (itcSig labX labY a)
  have hGw : (Val.list ((itcGp labX).map encPerm)).wt ≤ (q + 1) ^ 2 * (9 * (q + 1) ^ 2) + 4 :=
    it_perms_wt (itcGp_length labX)
  have hMw : (Val.list ((itcMs labX a).map encPerm)).wt ≤ 2 * (q + 1) ^ 2 * (9 * (q + 1) ^ 2) + 4 :=
    it_perms_wt (itcMs_length labX a)
  have e4 : (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 9 * (q + 1) ^ 4 := by ring
  have e4' : 2 * (q + 1) ^ 2 * (9 * (q + 1) ^ 2) = 18 * (q + 1) ^ 4 := by ring
  have hin := wt_list2_le (encFun labX) (encFun labY)
  have haw := wt_nat_le (a : ℕ)
  have haq := a.isLt
  have hlaw := wt_nat_le (labX a)
  have hlaq := hltX a
  have hbool : ∀ b : Bool, (boolVal b).wt ≤ 3 := fun b => by
    unfold boolVal; have := wt_nat_le b.toNat; have := Bool.toNat_le b; omega
  -- the first three steps
  have v0 : StDC P [(Val.list [encFun labX, encFun labY])] (.var 0) (Val.list [encFun labX, encFun labY]) 1 0 W := StDC.var' rfl (by omega)
  have d1 := StDC.call (StDC.get v0 (StDC.nat 0 (by omega)) (v := encFun labX) rfl (by omega))
    (hdat labX hltX) (by omega)
  set E1 : List Val := [(Val.list [encFun labX, encFun labY]), itDatV labX]
  have d2 := StDC.call (StDC.get (StDC.var' (W := W) (env := E1) (i := 0) rfl (by omega))
    (StDC.nat 1 (by omega)) (v := encFun labY) rfl (by omega)) (hdat labY hltY) (by omega)
  set E2 : List Val := [(Val.list [encFun labX, encFun labY]), itDatV labX, itDatV labY]
  have u1 : StDC P E2 (.var 1) (.list [encFun labX, encFun (itpSz labX), encPerm (itpPosE labX),
      encPerm (itpPosE labX)⁻¹, natList (List.range q)]) 1 0 W := StDC.var' rfl (by
    show (itDatV labX).wt ≤ W; omega)
  have u2 : StDC P E2 (.var 2) (.list [encFun labY, encFun (itpSz labY), encPerm (itpPosE labY),
      encPerm (itpPosE labY)⁻¹, natList (List.range q)]) 1 0 W := StDC.var' rfl (by
    show (itDatV labY).wt ≤ W; omega)
  have hss := wt_list2_le (encFun (itpSz labX)) (encFun (itpSz labY))
  have d3 := StDC.call (StDC.mk2 (StDC.get u1 (StDC.nat 1 (by omega)) (v := encFun (itpSz labX)) rfl
      (by omega)) (StDC.get u2 (StDC.nat 1 (by omega)) (v := encFun (itpSz labY)) rfl (by omega))
      (by omega) (by omega)) (hchk labX labY) (by have := hbool (decide (∀ s, itpCnt labX s = itpCnt labY s)); omega)
  set C := decide (∀ s, itpCnt labX s = itpCnt labY s)
  set E3 : List Val := [(Val.list [encFun labX, encFun labY]), itDatV labX, itDatV labY, boolVal C]
  -- the output
  have hout : (itcOsM hlX labY ha E₀ (itcMs labX a)).map (fun o => lcOv (o.1 : Perm (Fin q)) o.2.2) =
      if C = true then [lcOv (itcSig labX labY a) (itcMs labX a)] else [] := by
    simp only [itcOsM, itcOs, C, decide_eq_true_eq]
    split_ifs <;> rfl
  have hlc := wt_list2_le (encPerm (itcSig labX labY a)) (.list ((itcMs labX a).map encPerm))
  have hlcw : (Val.list [lcOv (itcSig labX labY a) (itcMs labX a)]).wt ≤ W := by
    have := wt_list_le_of [lcOv (itcSig labX labY a) (itcMs labX a)] (c := 50 * (q + 1) ^ 4) (by
      intro v hv; rw [List.mem_singleton] at hv; subst hv; unfold lcOv; omega)
    simp only [List.length_singleton] at this; omega
  have hnil : (Val.list []).wt ≤ W := by
    rw [wt_list_nil]; omega
  have hW4 : 4 ≤ W := by omega
  -- the branch with an overcoset
  have hthen : StDC P E3 (.letE (.call fnd (mk2 (.get (.var 0) (.nat 0)) (.get (.var 1) (.nat 4))))
    (.letE (.call swt (mk2 (mk2 (.get (.get (.var 0) (.nat 0)) (.var 4)) (.var 4))
      (.get (.var 1) (.nat 4))))
    (.letE (.call gen (.var 1))
    (.letE (.call sch (mk2 (.var 5) (.var 6)))
    (.letE (.call cmp (mk2 (.get (.var 2) (.nat 3)) (.get (.var 1) (.nat 2))))
    (.letE (.call par (.var 8))
    (.letE (.ite (.var 9) (.call cmp (mk2 (.var 8) (.var 5))) (.var 8))
      (.snoc .nil (mk2 (.var 10) (.var 7)))))))))) (.list [lcOv (itcSig labX labY a) (itcMs labX a)]) 300
      (10 ^ 5 * (q + 1) ^ 3 + 10 ^ 5 * (q + 1) ^ 3 + itGensC q + itSchC q +
        permK * (q + 1) ^ 3 + itParC q + permK * (q + 1) ^ 3) W := by
    have w0 : StDC P E3 (.var 0) (.list [encFun labX, encFun labY]) 1 0 W := StDC.var' rfl (by omega)
    have w1 : StDC P E3 (.var 1) (.list [encFun labX, encFun (itpSz labX), encPerm (itpPosE labX),
        encPerm (itpPosE labX)⁻¹, natList (List.range q)]) 1 0 W := StDC.var' rfl (by
      show (itDatV labX).wt ≤ W; omega)
    have hlr := wt_list2_le (encFun labX) (natList (List.range q))
    have f1 := StDC.call (StDC.mk2 (StDC.get w0 (StDC.nat 0 (by omega)) (v := encFun labX) rfl
      (by omega)) (StDC.get w1 (StDC.nat 4 (by omega)) (v := natList (List.range q)) rfl (by omega))
      (by omega) hW4) hfa (by omega)
    set E4 := E3 ++ [Val.nat a]
    have x0 : StDC P E4 (.var 0) (.list [encFun labX, encFun labY]) 1 0 W := StDC.var' rfl (by omega)
    have x1 : StDC P E4 (.var 1) (.list [encFun labX, encFun (itpSz labX), encPerm (itpPosE labX),
        encPerm (itpPosE labX)⁻¹, natList (List.range q)]) 1 0 W := StDC.var' rfl (by
      show (itDatV labX).wt ≤ W; omega)
    have x4 : StDC P E4 (.var 4) (.nat a) 1 0 W := StDC.var' rfl (by omega)
    have xl := StDC.get (vs := (List.finRange q).map fun i => Val.nat (labX i))
      (StDC.get x0 (StDC.nat 0 (by omega)) (v := encFun labX) rfl (by omega)) x4
      (encFun_getElem? labX a) (by omega)
    have hp2 := wt_list2_le (.nat (labX a)) (.nat a)
    have hp3 := wt_list2_le (.list [.nat (labX a), .nat a]) (natList (List.range q))
    have hsw := hswt (itcC labX a) a
    rw [itcC_val' hltX] at hsw
    have hT' : (encPerm (Equiv.swap (itcC labX a) a)).wt ≤ 4 * (q + 1) ^ 2 := wt_encPerm_le _
    have f2 := StDC.call (StDC.mk2 (StDC.mk2 xl x4 (by omega) hW4)
      (StDC.get x1 (StDC.nat 4 (by omega)) (v := natList (List.range q)) rfl (by omega))
      (by omega) hW4) hsw (by omega)
    set E5 := E4 ++ [encPerm (itcT labX a)]
    have f3 := StDC.call (StDC.var' (W := W) (env := E5) (i := 1) rfl (by omega)) (hgen hlX) (by omega)
    set E6 := E5 ++ [Val.list ((itcGp labX).map encPerm)]
    have y5 : StDC P E6 (.var 5) (encPerm (itcT labX a)) 1 0 W := StDC.var' rfl (by omega)
    have y6 : StDC P E6 (.var 6) (.list ((itcGp labX).map encPerm)) 1 0 W := StDC.var' rfl (by omega)
    have htg := wt_list2_le (encPerm (itcT labX a)) (.list ((itcGp labX).map encPerm))
    have f4 := StDC.call (StDC.mk2 y5 y6 (by omega) hW4) (hsch (itcT labX a) (itcGp labX) (itcGp_length labX)) (by
      show (Val.list ((itcMs labX a).map encPerm)).wt ≤ W; omega)
    set E7 := E6 ++ [Val.list ((itcMs labX a).map encPerm)]
    have z1 : StDC P E7 (.var 1) (.list [encFun labX, encFun (itpSz labX), encPerm (itpPosE labX),
        encPerm (itpPosE labX)⁻¹, natList (List.range q)]) 1 0 W := StDC.var' rfl (by
      show (itDatV labX).wt ≤ W; omega)
    have z2 : StDC P E7 (.var 2) (.list [encFun labY, encFun (itpSz labY), encPerm (itpPosE labY),
        encPerm (itpPosE labY)⁻¹, natList (List.range q)]) 1 0 W := StDC.var' rfl (by
      show (itDatV labY).wt ≤ W; omega)
    have hip := wt_list2_le (encPerm (itpPosE labY)⁻¹) (encPerm (itpPosE labX))
    have hip' := wt_encPerm_le ((itpPosE labY)⁻¹ * itpPosE labX)
    have f5 := StDC.call (StDC.mk2 (StDC.get z2 (StDC.nat 3 (by omega))
      (v := encPerm (itpPosE labY)⁻¹) rfl (by omega)) (StDC.get z1 (StDC.nat 2 (by omega))
      (v := encPerm (itpPosE labX)) rfl (by omega)) (by omega) hW4)
      (compose_spec hcmp (itpPosE labY)⁻¹ (itpPosE labX)) (by omega)
    rw [← itpAlign_eq] at f5
    have hat' := wt_encPerm_le (itpAlign labX labY * itcT labX a)
    set E8 := E7 ++ [encPerm (itpAlign labX labY)]
    have hpw : (Val.nat (itpNInv (itpAlign labX labY) % 2)).wt ≤ W := by
      have := wt_nat_le (itpNInv (itpAlign labX labY) % 2); have := Nat.mod_lt (itpNInv (itpAlign labX labY)) (show 2 > 0 by omega)
      omega
    have f6 := StDC.call (StDC.var' (W := W) (env := E8) (i := 8) rfl (by omega)) (hpar (itpAlign labX labY)) hpw
    set E9 := E8 ++ [Val.nat (itpNInv (itpAlign labX labY) % 2)]
    have p8 : StDC P E9 (.var 8) (encPerm (itpAlign labX labY)) 1 0 W := StDC.var' rfl (by omega)
    have p5 : StDC P E9 (.var 5) (encPerm (itcT labX a)) 1 0 W := StDC.var' rfl (by omega)
    have hat := wt_list2_le (encPerm (itpAlign labX labY)) (encPerm (itcT labX a))
    have f7 := StDC.ite (v := encPerm (itcSig labX labY a))
      (StDC.var' (W := W) (env := E9) (i := 9) rfl hpw)
      (fun hp => by
        have hs : sign (itpAlign labX labY) ≠ 1 := it_parity_ne.1 hp
        have hv : itcSig labX labY a = (itpAlign labX labY) * (itcT labX a) := by rw [itcSig, if_neg hs]
        rw [hv]
        exact StDC.call (StDC.mk2 p8 p5 (by omega) hW4) (compose_spec hcmp (itpAlign labX labY) (itcT labX a)) (by omega))
      (fun hp => by
        have hs : sign (itpAlign labX labY) = 1 := by by_contra h; exact it_parity_ne.2 h hp
        have hv : itcSig labX labY a = (itpAlign labX labY) := by rw [itcSig, if_pos hs]
        rw [hv]; exact p8) (by omega)
    set E10 := E9 ++ [encPerm (itcSig labX labY a)]
    have r10 : StDC P E10 (.var 10) (encPerm (itcSig labX labY a)) 1 0 W := StDC.var' rfl (by omega)
    have r7 : StDC P E10 (.var 7) (.list ((itcMs labX a).map encPerm)) 1 0 W := StDC.var' rfl (by omega)
    have f8 := StDC.snoc (StDC.nil (W := W) (env := E10) hW4) (StDC.mk2 r10 r7 (by omega) hW4)
      (by simp only [List.nil_append]; exact hlcw)
    simp only [List.nil_append] at f8
    have all := StDC.letE f1 (StDC.letE f2 (StDC.letE f3 (StDC.letE f4 (StDC.letE f5
      (StDC.letE f6 (StDC.letE f7 f8 hlcw) hlcw) hlcw) hlcw) hlcw) hlcw) hlcw
    refine all.mono ?_ ?_
    · omega
    · omega
  have hite := StDC.ite (v := .list ((itcOsM hlX labY ha E₀ (itcMs labX a)).map
      fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)) (x := C.toNat)
    (StDC.var' (W := W) (env := E3) (i := 3) rfl (by have := hbool C; unfold boolVal at this; omega))
    (fun hC => by
      have hC' : C = true := by
        by_contra h; rw [Bool.not_eq_true] at h; rw [h] at hC; exact hC rfl
      rw [hout, if_pos hC']; exact hthen)
    (fun hC => by
      have hC' : ¬ C = true := by
        intro h; rw [h] at hC; exact absurd hC (by decide)
      rw [hout, if_neg hC']; exact StDC.nil hW4)
    (by rw [hout]; split_ifs; exacts [hlcw, hnil])
  have hw' : (Val.list ((itcOsM hlX labY ha E₀ (itcMs labX a)).map
      fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)).wt ≤ W := by
    rw [hout]; split_ifs; exacts [hlcw, hnil]
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 hite hw') hw') hw'
  refine StDC.funDet hf dall ?_
  unfold itC1C itGensC itSchC itParC itChkC itDatC
  simp only [permK]
  have c1 : 1000 * (W + 1) ≤ 10 ^ 6 * (q + 1) ^ 6 := by omega
  have c2 : 10 ^ 7 * (q + 1) ^ 4 ≤ 10 ^ 7 * (q + 1) ^ 6 := by omega
  have c3 : 10 ^ 5 * (q + 1) ^ 3 ≤ 10 ^ 5 * (q + 1) ^ 6 := by omega
  have c4 : 30000 * (q + 1) ^ 3 ≤ 30000 * (q + 1) ^ 6 := by omega
  omega

end GI.Impl
