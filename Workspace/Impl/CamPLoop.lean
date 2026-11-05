module

public import Workspace.Impl.CamPLoopMath
public import Workspace.Impl.CamPCol
public import Workspace.Impl.CamDirectSocle

@[expose] public section

/-!
# Step 3 of `camProg`: the factor loop as a program

`camLoopBody` is one round on `[⟨⟩, i, [Cur, [T₀, …]]]` (`⟨⟩` is the trivial group):
1. `o ← GroupOrder Cur`. If `o = 1`, return the accumulator unchanged.
2. Otherwise `w_T ← camFactorFuns Cur`, and `T ← ⟨w_T⟩`, a single simple factor of `Cur`.
3. `C ← GMPNormalCentralizer (G = Cur, K = 1, H = Cur, N = T)`, the centralizer of `T` in `Cur`.
4. Return `[⟨C⟩, [T₀, …, T]]`.
The preconditions of the cited calls hold by `CamInv` (`camLoop_step`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp len len_le_self)

variable {n m k r : ℕ}

/-- `n`, read from the current group. -/
def camNE : Expr := .get (.get (arg 2) (.nat 0)) (.nat 0)

/-- One round of the factor loop. The group-building calls go to `b + 1`. -/
def camLoopBody (b fc jo jq : ℕ) : Expr :=
  .letE (.prim jo (.get (arg 2) (.nat 0)))
    (.ite (.arith .eq (.var 1) (.nat 1)) (arg 2)
      (.letE (.call fc (.get (arg 2) (.nat 0)))
        (.letE (.call (b + 1) (mk2 camNE (.var 2)))
          (.letE (.prim jq (mk2 (.get (arg 2) (.nat 0)) (.var 3)))
            (.letE (.call (b + 1) (mk2 camNE (.var 4)))
              (mk2 (.var 5) (.snoc (.get (arg 2) (.nat 1)) (.var 3))))))))

/-- Where the parts of the round sit. -/
structure CamLoopAt (P : Program) (b fc jo jp jn jq : ℕ) (ho : GroupOrder)
    (hp : PointwiseStab) (hncl : NormalClosure) (hqc : GMPNormalCentralizer) : Prop where
  body : P.funs[b]? = some (camLoopBody b fc jo jq)
  mg : P.HasAt (b + 1) (mkGroupFuns (b + 1))
  fac : CamFactorAt P fc jo jp jn ho hp hncl
  po : P.prims[jo]? = some (groupOrderPrim ho)
  pq : P.prims[jq]? = some (gmpNormalCentralizerPrim hqc)

def camLoopK : ℕ := 10 ^ 9

/-- The cost bound of one round. -/
noncomputable def camLoopCost (ho : GroupOrder) (hp : PointwiseStab) (hncl : NormalClosure)
    (hd : DerivedSubgroup) (hqc : GMPNormalCentralizer) (n : ℕ) : ℕ :=
  (groupOrderPrim ho).boundSize (camLoopB n) +
    (camDirectPrim ho hp hncl hd).boundSize (camLoopB n) +
    (gmpNormalCentralizerPrim hqc).boundSize (camLoopB n) + camLoopK * (n + 1) ^ 12

theorem cam_le_bot (H : Subgroup (Perm (Fin n))) : gens ([] : List (Perm (Fin n))) ≤ H := by
  rw [cam_gens_nil]; exact bot_le

theorem cam_bot_normal (H : Subgroup (Perm (Fin n))) :
    ∀ g ∈ H, ∀ k ∈ gens ([] : List (Perm (Fin n))), g * k * g⁻¹ ∈ gens ([] : List (Perm (Fin n))) := by
  intro g _ k hk; rw [cam_gens_nil] at hk ⊢; rw [Subgroup.mem_bot] at hk ⊢; rw [hk]; group

/-- The weight of the list of factors found. -/
theorem cam_wt_factors_le (ps : List (Fin r × List (Perm (Fin n))))
    (hps : ∀ p ∈ ps, p.2.length ≤ n ^ 2) (hl : ps.length ≤ n + 1) :
    (Val.list (ps.map fun p => encGroup p.2)).wt ≤ 700 * (n + 1) ^ 7 := by
  have h1 := cam_wt_list_le_of (vs := ps.map fun p => encGroup p.2) (B := 320 * (n + 1) ^ 6)
    (fun v hv => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact wt_encGroup_le_sq (hps p hp))
  rw [List.length_map] at h1
  have h2 : ps.length * (2 * (320 * (n + 1) ^ 6) + 1) ≤ (n + 1) * (641 * (n + 1) ^ 6) :=
    Nat.mul_le_mul hl (by have := Nat.one_le_pow 6 (n + 1) (by omega); omega)
  have e : (n + 1) * (641 * (n + 1) ^ 6) = 641 * (n + 1) ^ 7 := by ring
  have : 1 ≤ (n + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The weights in one round. -/
theorem cam_wt_round_le (cur : List (Perm (Fin n))) (ps : List (Fin r × List (Perm (Fin n))))
    (hcl : cur.length ≤ n ^ 2) (hps : ∀ p ∈ ps, p.2.length ≤ n ^ 2) (hl : ps.length ≤ n + 1)
    (i : ℕ) (hi : i ≤ n) :
    (Val.list [encGroup ([] : List (Perm (Fin n))), .nat i,
      .list [encGroup cur, .list (ps.map fun p => encGroup p.2)]]).wt ≤ 7000 * (n + 1) ^ 7 := by
  have h1 := cam_wt_factors_le ps hps hl
  have h2 := wt_encGroup_le_sq hcl
  have h3 := wt_encGroup_le_sq (hs := ([] : List (Perm (Fin n)))) (by simp)
  have h4 := wt_list2_le (encGroup cur) (.list (ps.map fun p => encGroup p.2))
  have h5 := wt_list3_le (encGroup ([] : List (Perm (Fin n)))) (.nat i)
    (.list [encGroup cur, .list (ps.map fun p => encGroup p.2)])
  have h6 := wt_nat_le i
  have h67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h17 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
  omega

/-- **One round of the factor loop.** -/
theorem camLoop_step {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    (hd : DerivedSubgroup) {hqc : GMPNormalCentralizer}
    {P : Program} {b fc jo jp jn jq : ℕ} (hP : CamLoopAt P b fc jo jp jn jq ho hp hncl hqc)
    (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (hn0 : 0 < n) (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) (_hrn : r ≤ n)
    (i : ℕ) (hin : i ≤ n) (acc : Val) (hinv : CamInv e i acc) :
    FunAll P b (.list [encGroup ([] : List (Perm (Fin n))), .nat i, acc])
      (fun w cost => CamInv e (i + 1) w ∧ cost ≤ camLoopCost ho hp hncl hd hqc n) := by
  have hkm : k < m := by omega
  obtain ⟨cur, ps, rfl, hcl, hps, hnd, hcur, hlen⟩ := hinv
  set c0 := encGroup ([] : List (Perm (Fin n))) with hc0
  set Tv := Val.list (ps.map fun p => encGroup p.2) with hTv
  set acc := Val.list [encGroup cur, Tv] with hacc
  have hacc' : camAcc cur ps = acc := rfl
  rw [hacc']
  set a := Val.list [c0, .nat i, acc] with ha
  set S := Finset.univ \ (camFsts ps).toFinset with hS
  have dCur := fun (rest : List Val) => Det.get' (Det.arg' (P := P) (vs := [c0, .nat i, acc])
    (rest := rest) (j := 2) rfl) (Det.nat 0)
    (show [encGroup cur, Tv][0]? = some (encGroup cur) from rfl)
  refine FunAll.intro hP.body (EvalAll.letE (groupOrder_call ho hP.po (dCur []) ⟨cur, rfl, rfl⟩)
    fun vo co ho' => ?_)
  obtain ⟨rfl, hco⟩ := ho'
  have dT := Det.arith (op := .eq) (Det.var' (P := P) (env := [a, .nat (Nat.card (gens cur))])
    (i := 1) rfl) (Det.nat (P := P) (env := [a, .nat (Nat.card (gens cur))]) 1)
  refine EvalAll.ite dT (fun _ _ h => ⟨_, h.1⟩) fun x ct hx => ?_
  obtain ⟨hx1, hct⟩ := hx
  cases hx1
  by_cases hS0 : S = ∅
  · -- nothing is left: the accumulator is returned unchanged
    have h1 : Nat.card (gens cur) = 1 := by
      rw [hcur]; exact (cam_card_cur_eq_one e hm hk1 hkm S).mpr hS0
    have hev : BinOp.eval .eq (Nat.card (gens cur)) 1 = 1 := by
      simp [BinOp.eval, h1]
    rw [hev, if_neg one_ne_zero]
    have hfull := cam_fsts_full hnd hS0
    refine (Det.arg' (P := P) (vs := [c0, .nat i, acc]) (rest := [.nat (Nat.card (gens cur))])
      (j := 2) rfl).post fun cc hcc => ⟨⟨cur, ps, rfl, hcl, hps, hnd, hcur, by omega⟩, ?_⟩
    have hW : a.wt ≤ 7000 * (n + 1) ^ 7 :=
      cam_wt_round_le cur ps hcl (fun p hp => (hps p hp).2) (by omega) i hin
    have hcw6 := wt_encGroup_le_sq hcl
    have haw : (Val.list [c0, .nat i, acc]).wt = a.wt := rfl
    have hacw : acc.wt < a.wt := wt_le_wt_list (by simp)
    have hcw : (encGroup cur).wt < acc.wt := wt_le_wt_list (by simp)
    have hb1 := (groupOrderPrim ho).bound_le (v := encGroup cur) (B := camLoopB n)
      ((Val.size_le_wt _).trans (by unfold camLoopB; omega))
    have hct' : ct ≤ (Val.nat (Nat.card (gens cur))).wt + 1 + 4 + (Val.nat 1).wt + 1 := by
      simpa [hev] using hct
    have hcard := wt_card_le (gens cur)
    have hn2 : n ^ 2 ≤ (n + 1) ^ 12 := (Nat.pow_le_pow_left (by omega) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
    have h7 : (n + 1) ^ 7 ≤ (n + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    have h67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have hw1 : (Val.nat 1).wt = 3 := rfl
    unfold camLoopCost
    simp only [camLoopK] at *
    clear_value a acc c0 Tv S
    generalize (n + 1) ^ 12 = Q at *
    generalize (n + 1) ^ 7 = Q7 at *
    generalize (n + 1) ^ 6 = Q6 at *
    omega
  · -- a factor is left
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
    have h1 : Nat.card (gens cur) ≠ 1 := by
      rw [hcur]; exact fun h => hS0 ((cam_card_cur_eq_one e hm hk1 hkm S).mp h)
    have hev : BinOp.eval .eq (Nat.card (gens cur)) 1 = 0 := by
      simp [BinOp.eval, h1]
    rw [hev, if_pos rfl]
    have hlt := cam_fsts_lt hnd hne.choose_spec
    -- the direct factor search
    have dFac : EvalAll P [a, .nat (Nat.card (gens cur))] (.call fc (.get (arg 2) (.nat 0)))
        (fun vs cs => (∃ i0 ∈ S, GensVal n vs (camProd e {i0})) ∧
          cs ≤ (camDirectPrim ho hp hncl hd).boundSize (camLoopB n) +
            (encGroup cur).wt + 2 * a.wt + 27 * (n + 1) ^ 6 + 20) := by
      refine EvalAll.call_funAll (dCur [.nat (Nat.card (gens cur))]) fun v1 ca1 hv1 => ?_
      obtain ⟨rfl, hca1⟩ := hv1
      refine (camFactor_spec hP.fac e hm hk1 hk hn0 hne cur hcl hcur).mono fun w cb ⟨hw, hcb⟩ =>
        ⟨hw, ?_⟩
      obtain ⟨i0, -, hgv⟩ := hw
      have hgw := GensVal.wt_le hgv
      have hb := camFactorCost_le_boundSize ho hp hncl hd n
      have h0w : (Val.nat 0).wt = 2 := rfl
      have h2w : (Val.nat 2).wt = 4 := rfl
      have haw : (Val.list [c0, .nat i, acc]).wt = a.wt := rfl
      omega
    refine EvalAll.letE dFac fun vs cs hcs => ?_
    obtain ⟨⟨i0, hi0S, hsT, rfl, hsTl, hgT⟩, hcs⟩ := hcs
    -- the factor `T`
    set E1 := [a, Val.nat (Nat.card (gens cur)), Val.list (hsT.map encPerm)] with hE1
    have dN := fun (rest : List Val) => Det.encPerms_size (gs := 1 :: cur) (dCur rest)
    have dLi := Det.var' (P := P) (env := E1) (i := 2) rfl
    obtain ⟨tsT, htsT, htsTl, fT, ⟨tsT', hTe, hTg⟩, hTw⟩ :=
      mkGroup_gensVal hP.mg (G := camProd e {i0}) ⟨hsT, rfl, hsTl, hgT⟩
    have dTc := Det.call (Det.mk2 (dN [.nat (Nat.card (gens cur)),
      Val.list (hsT.map encPerm)]) dLi) fT
    refine EvalAll.letE dTc fun vT cT hT => ?_
    obtain ⟨rfl, hcT⟩ := hT
    obtain rfl := encGroup_injective hTe
    -- the centralizer
    set E2 := E1 ++ [encGroup tsT] with hE2
    have hTn : ∀ y ∈ gens cur, ∀ x ∈ gens tsT, y * x * y⁻¹ ∈ gens tsT := by
      rw [hTg, hcur]; exact camX_prod_normal S {i0}
    have dQa := Det.mk2 (dCur (E2.drop 1)) (Det.var' (P := P) (env := E2) (i := 3) rfl)
    refine EvalAll.letE (gmpNormalCentralizer_call hqc hP.pq dQa ⟨cur, rfl, rfl⟩ ⟨tsT, rfl, rfl⟩ hTn)
      fun vQ cQ hQ => ?_
    obtain ⟨⟨C, hCg, hCm⟩, hcQ⟩ := hQ
    have hCe : C = camProd e (S.erase i0) := by
      refine cam_cent_erase e hm hk1 hkm hi0S fun y => ?_
      rw [hCm y, hcur, hTg]
    obtain ⟨cks, rfl, hckl, fC, ⟨cks', hce, hcg⟩, hCw⟩ := mkGroup_gensVal hP.mg hCg
    obtain rfl := encGroup_injective hce
    set E3 := E2 ++ [Val.list (cks.map encPerm)] with hE3
    have dCc := Det.call (Det.mk2 (dN (E3.drop 1)) (Det.var' (P := P) (env := E3) (i := 4) rfl)) fC
    have dTs := Det.get' (Det.arg' (P := P) (vs := [c0, .nat i, acc]) (rest := (E3 ++ [encGroup cks]).drop 1)
      (j := 2) rfl) (Det.nat 1) (show [encGroup cur, Tv][1]? = some Tv from rfl)
    have dR := Det.mk2 (Det.var' (P := P) (env := E3 ++ [encGroup cks]) (i := 5) rfl)
      (Det.snoc dTs (Det.var' (P := P) (env := E3 ++ [encGroup cks]) (i := 3) rfl))
    refine EvalAll.letE dCc fun vC cC hC => ?_
    obtain ⟨rfl, hcC⟩ := hC
    refine dR.post fun cc hcc => ⟨⟨cks, ps ++ [(i0, tsT)], ?_, hckl, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [camAcc]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hps p hp
      · rw [List.mem_singleton] at hp; subst hp; exact ⟨hTg, htsTl⟩
    · have hi0n : i0 ∉ camFsts ps := by
        have := (Finset.mem_sdiff.mp hi0S).2; simpa using this
      have e1 : camFsts (ps ++ [(i0, tsT)]) = camFsts ps ++ [i0] := by simp [camFsts]
      rw [e1, List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      rintro rfl
      exact hi0n (hy ▸ hx)
    · rw [hcg, hCe, cam_sdiff_snoc]
    · simp only [List.length_append, List.length_singleton]; omega
    clear dR dCc dTs fC fT dQa dTc dLi dN dCur dT dFac
    have hW : a.wt ≤ 7000 * (n + 1) ^ 7 :=
      cam_wt_round_le cur ps hcl (fun p hp => (hps p hp).2) (by omega) i hin
    have hps' : ∀ p ∈ ps ++ [(i0, tsT)], p.2.length ≤ n ^ 2 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (hps p hp).2
      · rw [List.mem_singleton] at hp; subst hp; exact htsTl
    have hW' := cam_wt_factors_le (ps ++ [(i0, tsT)]) hps' (by simp; omega)
    rw [List.map_append, List.map_singleton] at hW'
    have hR := wt_list2_le (encGroup cks) (.list ((ps.map fun p => encGroup p.2) ++ [encGroup tsT]))
    have hcw6 := wt_encGroup_le_sq hcl
    have hTw6 := hTw
    have haw : (Val.list [c0, .nat i, acc]).wt = a.wt := rfl
    have hacw : acc.wt < a.wt := wt_le_wt_list (by simp)
    have hcw : (encGroup cur).wt < acc.wt := wt_le_wt_list (by simp)
    have hTvw : Tv.wt < acc.wt := wt_le_wt_list (by simp)
    have hc0w : c0.wt < a.wt := wt_le_wt_list (by simp)
    have hc06 : c0.wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq (by simp)
    have hTL : (Val.list (hsT.map encPerm)).wt ≤ 13 * (n + 1) ^ 6 :=
      GensVal.wt_le ⟨hsT, rfl, hsTl, hgT⟩
    have hQ4 := wt_list2_le (encGroup cur) (encGroup tsT)
    have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hQ4' : (Val.list [encGroup cur, encGroup tsT]).wt ≤ camLoopB n := by
      unfold camLoopB; omega
    have hb1 := (groupOrderPrim ho).bound_le (v := encGroup cur) (B := camLoopB n)
      ((Val.size_le_wt _).trans (by unfold camLoopB; omega))
    have hb3 := (gmpNormalCentralizerPrim hqc).bound_le
      (v := Val.list [encGroup cur, encGroup tsT]) (B := camLoopB n)
      ((Val.size_le_wt _).trans hQ4')
    have hct' : ct ≤ (Val.nat (Nat.card (gens cur))).wt + 1 + 4 + (Val.nat 0).wt + 1 := by
      simpa [hev] using hct
    have hw0 : (Val.nat 0).wt = 2 := rfl
    have hcard := wt_card_le (gens cur)
    have hnw := wt_nat_le n
    have hmk1 := wt_list2_le (.nat n) (.list (cks.map encPerm))
    have hmk2 : (Val.list (cks.map encPerm)).wt ≤ 13 * (n + 1) ^ 6 := GensVal.wt_le hCg
    have hmk3 := wt_list2_le (.nat n) (.list (hsT.map encPerm))
    have hn2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have h78 : (n + 1) ^ 7 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have h89 : (n + 1) ^ 8 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have h912 : (n + 1) ^ 9 ≤ (n + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1n : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    unfold camLoopCost
    simp only [camLoopK, mkGroupK] at *
    clear_value a acc c0 Tv S E1 E2 E3
    generalize (n + 1) ^ 12 = Q12 at *
    generalize (n + 1) ^ 9 = Q9 at *
    generalize (n + 1) ^ 8 = Q8 at *
    generalize (n + 1) ^ 7 = Q7 at *
    generalize (n + 1) ^ 6 = Q6 at *
    generalize (n + 1) ^ 2 = Q2 at *
    omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n m k r : ℕ}

/-- The factor loop, at base `b`: the round, the group builder, and the iteration (at `b + 8`). -/
def camLoopFuns (b fc jo jq : ℕ) : List Expr :=
  [camLoopBody b fc jo jq] ++ mkGroupFuns (b + 1) ++ iterFuns (b + 8) b

theorem camLoopAt_of {P : Program} {b fc jo jp jn jq : ℕ} {ho : GroupOrder}
    {hp : PointwiseStab} {hncl : NormalClosure} {hqc : GMPNormalCentralizer}
    (h : P.HasAt b (camLoopFuns b fc jo jq))
    (hfac : CamFactorAt P fc jo jp jn ho hp hncl)
    (po : P.prims[jo]? = some (groupOrderPrim ho))
    (pq : P.prims[jq]? = some (gmpNormalCentralizerPrim hqc)) :
    CamLoopAt P b fc jo jp jn jq ho hp hncl hqc ∧ P.HasAt (b + 8) (iterFuns (b + 8) b) := by
  simp only [camLoopFuns] at h
  exact ⟨{ body := h.left.left.single
           mg := by simpa using h.left.right
           fac := hfac, po := po, pq := pq },
    by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, Nat.add_assoc] using h.right⟩

theorem cam_wt_inv_le (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (hrn : r ≤ n)
    {i : ℕ} {acc : Val} (h : CamInv e i acc) : acc.wt ≤ 3000 * (n + 1) ^ 7 := by
  obtain ⟨cur, ps, rfl, hcl, hps, -, -, hlen⟩ := h
  have h1 := cam_wt_factors_le ps (fun p hp => (hps p hp).2) (by omega)
  have h2 := wt_encGroup_le_sq hcl
  have h3 := wt_list2_le (encGroup cur) (.list (ps.map fun p => encGroup p.2))
  have h67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have : 1 ≤ (n + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  exact h3.trans (by omega)

/-- **The factor loop.** Started on the socle `camProd e univ`, after `n` rounds it has found all
`r` factors. -/
theorem camLoop_spec {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    (hd : DerivedSubgroup) {hqc : GMPNormalCentralizer}
    {P : Program} {b fc jo jp jn jq : ℕ} (hP : CamLoopAt P b fc jo jp jn jq ho hp hncl hqc)
    (hI : P.HasAt (b + 8) (iterFuns (b + 8) b))
    (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (hn0 : 0 < n) (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) (hrn : r ≤ n)
    (cur : List (Perm (Fin n))) (hcl : cur.length ≤ n ^ 2)
    (hcur : gens cur = camProd e Finset.univ) :
    FunAll P (b + 8) (.list [encGroup ([] : List (Perm (Fin n))), .nat n,
        camAcc cur ([] : List (Fin r × List (Perm (Fin n))))])
      (fun w cost => CamInv e n w ∧
        cost ≤ n * camLoopCost ho hp hncl hd hqc n + loopModK * (n + 1) * (15000 * (n + 1) ^ 7)) := by
  have h0 : CamInv e 0 (camAcc cur ([] : List (Fin r × List (Perm (Fin n))))) :=
    ⟨cur, [], rfl, hcl, by simp, List.nodup_nil, by simpa using hcur, by simp⟩
  refine (iter_spec hI h0 (fun i acc _ h => cam_wt_inv_le e hrn h)
    fun i acc hi h => camLoop_step hd hP e hn0 hm hk1 hk hrn i hi.le acc h).mono fun w cost hw => ⟨hw.1, ?_⟩
  obtain ⟨-, hc'⟩ := hw
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc'
  have h1 := cam_wt_inv_le e hrn h0
  have h2 := wt_encGroup_le_sq (hs := ([] : List (Perm (Fin n)))) (by simp)
  have h3 := wt_list3_le (encGroup ([] : List (Perm (Fin n)))) (.nat n)
    (camAcc cur ([] : List (Fin r × List (Perm (Fin n)))))
  have h4 := wt_nat_le n
  have h67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h17 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
  have h5 : (Val.list [encGroup ([] : List (Perm (Fin n))), .nat n,
      camAcc cur ([] : List (Fin r × List (Perm (Fin n))))]).wt + n + 3000 * (n + 1) ^ 7 + 1 ≤
      15000 * (n + 1) ^ 7 := by omega
  have h6 := Nat.mul_le_mul_left (loopModK * (n + 1)) h5
  omega

end GI.Impl
