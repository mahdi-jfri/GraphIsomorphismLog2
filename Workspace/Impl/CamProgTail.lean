module

public import Workspace.Impl.CamProg
public import Workspace.Impl.CamXSocle

@[expose] public section

/-!
# Correctness and cost of steps 2–7 of `camProg`

`camTail_spec`: on `encGroup gs`, when `⟨gs⟩` has a Maróti identification `e` with `m ≥ 5`,
`1 ≤ k` and `2k < m`, the tail answers `[2]` or `[1, m, k, r, E]` as `CameronOut` requires. Every
cited call is made with its precondition, as recorded at the call.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp len len_le_self)

variable {n m k r : ℕ}

/-- The bound on the arguments of all cited calls of the tail. -/
def camPB (X : ℕ) : ℕ := 10 ^ 12 * X ^ 12

/-- The four cited bounds. -/
noncomputable def camS4 (ho : GroupOrder) (hp : PointwiseStab) (hncl : NormalClosure)
    (hd : DerivedSubgroup) (hqc : GMPNormalCentralizer)
    (hj : JohnsonIdentification) (X : ℕ) : ℕ :=
  (groupOrderPrim ho).boundSize (camPB X) +
    (camDirectPrim ho hp hncl hd).boundSize (camPB X) +
    (gmpNormalCentralizerPrim hqc).boundSize (camPB X) + (johnsonPrim hj).boundSize (camPB X)

theorem cam_ge_one_six (n : ℕ) : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)

theorem cam_wt_col_le {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} {i : Fin r}
    {x₀ : Fin n} {v : Val} (h : CamFacOut e i x₀ v) (hmn : m ≤ n) (hn : 0 < n) :
    v.wt ≤ 12 * (n + 1) ^ 3 := by
  obtain ⟨-, -, -, -, -, -, -, F, -, rfl⟩ := h
  have h1 := cam_wt_list_le_of (vs := (List.finRange n).map fun x => kVal (F x))
    (B := 5 * (m + 1) ^ 2)
    (fun v hv => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv; exact wt_kVal_le _)
  simp only [List.length_map, List.length_finRange] at h1
  have h2 : n * (2 * (5 * (m + 1) ^ 2) + 1) ≤ (n + 1) * (11 * (n + 1) ^ 2) := by
    refine Nat.mul_le_mul (by omega) ?_
    have := Nat.pow_le_pow_left (show m + 1 ≤ n + 1 by omega) 2
    have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have e : (n + 1) * (11 * (n + 1) ^ 2) = 11 * (n + 1) ^ 3 := by ring
  have : 2 ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  exact h1.trans (by omega)

theorem cam_ctx_wt_le (ns : List (Perm (Fin n))) (hnsl : ns.length ≤ n ^ 2) (hm : m ≤ n)
    (hk : k ≤ n) :
    (Val.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m, .nat k]).wt ≤
      1300 * (n + 1) ^ 6 := by
  have w1 := wt_encGroup_le_sq (hs := ([] : List (Perm (Fin n)))) (by simp)
  have w2 := wt_encGroup_le_sq hnsl
  have w3 := wt_nat_le m
  have w4 := wt_nat_le k
  have w5 := wt_list4_le (encGroup ns) (encGroup ([] : List (Perm (Fin n)))) (.nat m) (.nat k)
  have := cam_ge_one_six n
  have : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  omega

theorem cam_fac_bound {hj : JohnsonIdentification} {hqc : GMPNormalCentralizer} {ctx y : Val}
    {X : ℕ} (hctx : ctx.wt ≤ 1300 * (n + 1) ^ 6) (hy : y.wt ≤ 320 * (n + 1) ^ 6)
    (hnX : n + 1 ≤ X) {c : ℕ}
    (hc : c ≤ (johnsonPrim hj).boundSize (camFacB ((Val.list [ctx, y]).wt + 1)) +
      (gmpNormalCentralizerPrim hqc).boundSize (camFacB ((Val.list [ctx, y]).wt + 1)) +
      camFacK * ((Val.list [ctx, y]).wt + 1) ^ 30) :
    c ≤ (johnsonPrim hj).boundSize (camPB X) + (gmpNormalCentralizerPrim hqc).boundSize (camPB X) +
      camFacK * 4000 ^ 30 * X ^ 180 := by
  have w2 := wt_list2_le ctx y
  have h6 := Nat.pow_le_pow_left hnX 6
  have hZ : (Val.list [ctx, y]).wt + 1 ≤ 4000 * X ^ 6 := by
    have := cam_ge_one_six n; omega
  have hB : camFacB ((Val.list [ctx, y]).wt + 1) ≤ camPB X := by
    unfold camFacB camPB
    have h1 := Nat.pow_le_pow_left hZ 2
    have e : (4000 * X ^ 6) ^ 2 = 16000000 * X ^ 12 := by ring
    omega
  have h1 := cam_boundSize_mono (johnsonPrim hj) hB
  have h2 := cam_boundSize_mono (gmpNormalCentralizerPrim hqc) hB
  have h3 : ((Val.list [ctx, y]).wt + 1) ^ 30 ≤ 4000 ^ 30 * X ^ 180 := by
    calc _ ≤ (4000 * X ^ 6) ^ 30 := Nat.pow_le_pow_left hZ 30
      _ = 4000 ^ 30 * X ^ 180 := by ring
  have h4 := Nat.mul_le_mul_left camFacK h3
  have e5 : camFacK * (4000 ^ 30 * X ^ 180) = camFacK * 4000 ^ 30 * X ^ 180 := by ring
  exact hc.trans (Nat.add_le_add (Nat.add_le_add h1 h2) (h4.trans e5.le))

theorem cam_arith_cx {D A B a c : ℕ} (h1 : D ≤ 2 * (A + B) + 6) (h2 : A ≤ 1300 * a)
    (h3 : B ≤ 700 * c) (h4 : a ≤ c) : D ≤ 5000 * c + 6 := by omega

theorem cam_map_cost {n r X ca cb BF Wcx Ww : ℕ} (hn : 1 ≤ n) (hnX : n + 1 ≤ X) (hrn : r ≤ n)
    (hcb : cb ≤ r * BF + mapK * (r + 1) * (Wcx + Ww + 1)) (hWcx : Wcx ≤ 5000 * (n + 1) ^ 7 + 6)
    (hWw : Ww ≤ r * (2 * (12 * (n + 1) ^ 3) + 1) + 4) (hca : ca ≤ 30000 * (n + 1) ^ 7) :
    ca + cb + Ww + 1 ≤ X * BF + 10 ^ 9 * X ^ 10 := by
  have q3 := Nat.pow_le_pow_left hnX 3
  have q7 := Nat.pow_le_pow_left hnX 7
  have r37 : X ^ 3 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have r710 : X ^ 7 ≤ X ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have r810 : X ^ 8 ≤ X ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have r1 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have r7 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ (by omega)
  have k3 : r * (2 * (12 * (n + 1) ^ 3) + 1) ≤ X * (25 * X ^ 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e3 : X * (25 * X ^ 3) = 25 * X ^ 4 := by ring
  have r47 : X ^ 4 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hin : Wcx + Ww + 1 ≤ 6000 * X ^ 7 := by
    have : 2 ^ 7 ≤ X ^ 7 := Nat.pow_le_pow_left (by omega) 7
    omega
  have k1 : r * BF ≤ X * BF := Nat.mul_le_mul_right _ (by omega)
  have k2 : mapK * (r + 1) * (Wcx + Ww + 1) ≤ mapK * X * (6000 * X ^ 7) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hin
  have e2 : mapK * X * (6000 * X ^ 7) = 6000 * mapK * X ^ 8 := by ring
  simp only [mapK] at k2 e2 hcb
  omega

theorem cam_tail_sum {X S GO CS QC J K0 P T : ℕ} (hX : 1 ≤ X) (hS : S = GO + CS + QC + J)
    (hP : P ≤ 10 ^ 39 * X ^ 182) (hK : 10 ^ 40 ≤ K0)
    (hT : T ≤ CS + GO + X * S + (X * (J + QC) + K0 * X ^ 181) + P) :
    T ≤ 2 * X * S + 2 * K0 * X ^ 182 := by
  have e1 : X * S = X * GO + X * CS + X * QC + X * J := by rw [hS]; ring
  have e2 : X * (J + QC) = X * J + X * QC := by ring
  have e3 : 2 * X * S = 2 * (X * S) := by ring
  have e4 : 2 * K0 * X ^ 182 = 2 * (K0 * X ^ 182) := by ring
  have h1 : GO ≤ X * GO := Nat.le_mul_of_pos_left _ hX
  have h2 : CS ≤ X * CS := Nat.le_mul_of_pos_left _ hX
  have h3 : K0 * X ^ 181 ≤ K0 * X ^ 182 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by norm_num))
  have h4 : 10 ^ 40 * X ^ 182 ≤ K0 * X ^ 182 := Nat.mul_le_mul_right _ hK
  omega

theorem cam_K0 : 10 ^ 40 ≤ camFacK * 4000 ^ 30 := by unfold camFacK; norm_num

/-- The cost bound of the tail. -/
noncomputable def camTailCost (ho : GroupOrder) (hp : PointwiseStab) (hncl : NormalClosure)
    (hd : DerivedSubgroup) (hqc : GMPNormalCentralizer)
    (hj : JohnsonIdentification) (X : ℕ) : ℕ :=
  2 * X * camS4 ho hp hncl hd hqc hj X + 2 * camFacK * 4000 ^ 30 * X ^ 182

set_option maxHeartbeats 2000000 in
/-- **The tail.** -/
theorem camTail_spec {ho : GroupOrder} {hp : PointwiseStab} {hncl : NormalClosure}
    {hd : DerivedSubgroup} {hqc : GMPNormalCentralizer}
    {hj : JohnsonIdentification} {P : Program} {b jo jp jn jd jq jj : ℕ}
    (hP : CamAt P b jo jp jn jd jq jj ho hp hncl hd hqc hj) (gs : List (Perm (Fin n)))
    (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (hM : MarotiStructure (gens gs) e)
    (hprim : MulAction.IsPreprimitive (gens gs) (Fin n)) (hn : 25 ≤ n) (h5 : 5 ≤ m)
    (hk1 : 1 ≤ k) (hk : 2 * k < m) :
    FunAll P (b + 1) (encGroup gs) (fun v c => CameronOut (gens gs) v ∧
      c ≤ camTailCost ho hp hncl hd hqc hj ((encGroup gs).wt + 1)) := by
  obtain ⟨hr1, hrn, hmn⟩ := cam_sizes e hn hk1 hk
  have hn0 : 0 < n := by omega
  set x₀ : Fin n := ⟨0, hn0⟩ with hx₀
  set x := encGroup gs with hx
  set X := x.wt + 1 with hX
  have hxS : (gs.length + 2) * (n + 1) ≤ x.wt := S_le_wt_encGroup gs
  have hnX : n + 1 ≤ X := by
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hXp : ∀ i j, i ≤ j → X ^ i ≤ X ^ j := fun i j h => Nat.pow_le_pow_right (by omega) h
  have hnXp : ∀ i, (n + 1) ^ i ≤ X ^ i := fun i => Nat.pow_le_pow_left hnX i
  have hPB : ∀ B, B ≤ 10 ^ 12 * X ^ 12 → ∀ p : Prim, p.boundSize B ≤ p.boundSize (camPB X) :=
    fun B hB p => cam_boundSize_mono p hB
  have dx : Det P [x] (.var 0) x (x.wt + 1) := Det.var' rfl
  have dn := fun (rest : List Val) => Det.encPerms_size (gs := 1 :: gs)
    (Det.var' (P := P) (env := x :: rest) (i := 0) rfl)
  -- the direct socle search
  have hxe : (encPerms (1 :: gs)).wt = x.wt := rfl
  have h6 := hnXp 6
  have h8 := hnXp 8
  have hX8 := hXp 1 8 (by norm_num)
  have hX12 := hXp 1 12 (by norm_num)
  have h68 := hXp 6 8 (by norm_num)
  have h612 := hXp 6 12 (by norm_num)
  refine FunAll.intro hP.tail (EvalAll.letE
    (Ra := fun vs cs => GensVal n vs (camProd e Finset.univ) ∧
      cs ≤ (camDirectPrim ho hp hncl hd).boundSize (camPB X) + 200 * X ^ 8)
    (EvalAll.call_funAll dx fun v ca hv => ?_) fun vs cs hcs => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine (camSocle_spec hP.soc gs hM hprim hn h5 hk1 hk).mono fun w cb ⟨hw, hcb⟩ => ⟨hw, ?_⟩
    have hww := GensVal.wt_le hw
    have hb := camSocleCost_le_boundSize ho hp hncl hd (encGroup gs) n (B := camPB X)
      (by unfold camPB; omega)
      (by unfold camSocleB camPB; rw [← hx]; simp only [pow_one] at hX12; omega)
    clear * - hca hcb hww hb h6 h8 hX8 h68 hX
    simp only [pow_one] at hX8
    omega
  obtain ⟨hvs, hcs1⟩ := hcs
  set E1 := [x, vs] with hE1
  have dLi := Det.var' (P := P) (env := E1) (i := 1) rfl
  obtain ⟨ns, -, hnsl, fN, ⟨ns', hNe, hns⟩, hNw⟩ :=
    mkGroup_gensVal hP.mg (G := camProd e Finset.univ) hvs
  obtain rfl := encGroup_injective hNe
  refine EvalAll.letE (Det.call (Det.mk2 (dn E1.tail) dLi) fN) fun vN cN hN => ?_
  obtain ⟨rfl, hcN⟩ := hN
  have hcN1 : cN ≤ 10 ^ 7 * X ^ 9 := by
    have hsNw := GensVal.wt_le hvs
    have w1 := wt_list2_le (.nat n) vs
    have w2 := wt_nat_le n
    have h9 := hnXp 9
    have h69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have hX9 := hXp 1 9 (by norm_num)
    clear * - hcN hsNw w1 w2 h9 h69 hX9 hNw hxe hX hnX
    simp only [pow_one, mkGroupK] at *
    omega
  -- the trivial group
  set E2 := E1 ++ [encGroup ns] with hE2
  have fE := mkGroup_spec hP.mg ([] : List (Perm (Fin n)))
  refine EvalAll.letE (Det.call (Det.mk2 (dn E2.tail) (Det.nil (P := P) (env := E2))) fE)
    fun vE cE hE => ?_
  obtain ⟨rfl, hcE⟩ := hE
  have hcE1 : cE ≤ 10 ^ 7 * X ^ 9 := by
    have w0 := wt_encGroup_le_sq (hs := ([] : List (Perm (Fin n)))) (by simp)
    have w1 := wt_list2_le (.nat n) (.list [])
    have w2 := wt_nat_le n
    have hnil : (Val.list []).wt ≤ 10 := by decide
    have h9 := hnXp 9
    have h3 := hnXp 3
    have h39 := hXp 3 9 (by norm_num)
    have h69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have hX9 := hXp 1 9 (by norm_num)
    have e : (([] : List (Perm (Fin n))).length + 2) * (n + 1) = 2 * (n + 1) := by simp
    rw [e] at hcE
    have e2 : (2 * (n + 1)) ^ 3 = 8 * (n + 1) ^ 3 := by ring
    rw [e2] at hcE
    clear * - hcE w0 w1 w2 hnil h9 h3 h39 h69 hX9 hxe hX hnX
    simp only [pow_one, mkGroupK] at *
    omega
  -- the factor loop
  set E3 := E2 ++ [encGroup ([] : List (Perm (Fin n)))] with hE3
  have dLa := Det.mk3 (Det.var' (P := P) (env := E3) (i := 3) rfl) (dn E3.tail)
    (Det.mk2 (Det.var' (P := P) (env := E3) (i := 2) rfl) (Det.nil (P := P) (env := E3)))
  have fL := camLoop_spec hd hP.loop hP.iter e hn0 h5 hk1 hk hrn ns hnsl hns
  refine EvalAll.letE (Ra := fun w c => CamInv e n w ∧
      c ≤ X * camS4 ho hp hncl hd hqc hj X + 10 ^ 14 * X ^ 13)
    (EvalAll.call_funAll dLa fun v ca hv => ?_) fun vL cL hL => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine fL.mono fun w cb hw => ⟨hw.1, ?_⟩
    obtain ⟨hw1, hcb⟩ := hw
    have hww := cam_wt_inv_le e hrn hw1
    have hLc : camLoopCost ho hp hncl hd hqc n ≤ camS4 ho hp hncl hd hqc hj X + 10 ^ 9 * X ^ 12 := by
      have hB : camLoopB n ≤ 10 ^ 12 * X ^ 12 := by
        unfold camLoopB
        have := hnXp 6; have := hXp 6 12 (by norm_num); omega
      have h1 := hPB _ hB (groupOrderPrim ho)
      have h2 := hPB _ hB (camDirectPrim ho hp hncl hd)
      have h3 := hPB _ hB (gmpNormalCentralizerPrim hqc)
      have h4 := Nat.mul_le_mul_left camLoopK (hnXp 12)
      unfold camLoopCost camS4
      simp only [camLoopK] at h4 ⊢
      omega
    have k1 := Nat.mul_le_mul (show n ≤ X by omega) hLc
    have e1 : X * (camS4 ho hp hncl hd hqc hj X + 10 ^ 9 * X ^ 12) =
        X * camS4 ho hp hncl hd hqc hj X + 10 ^ 9 * X ^ 13 := by ring
    have k2 : loopModK * (n + 1) * (15000 * (n + 1) ^ 7) ≤ loopModK * X * (15000 * X ^ 7) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hnX) (Nat.mul_le_mul_left _ (hnXp 7))
    have e2 : loopModK * X * (15000 * X ^ 7) = 15000 * loopModK * X ^ 8 := by ring
    have w1 := wt_encGroup_le_sq (hs := ([] : List (Perm (Fin n)))) (by simp)
    have w2 := wt_encGroup_le_sq hnsl
    have w3 := wt_nat_le n
    have w4 := wt_list2_le (encGroup ns) (.list [])
    have w5 := wt_list3_le (encGroup ([] : List (Perm (Fin n)))) (.nat n)
      (.list [encGroup ns, .list []])
    have hnil : (Val.list []).wt ≤ 10 := by decide
    have hxe : (encPerms (1 :: gs)).wt = x.wt := rfl
    have p1 := hnXp 6; have p2 := hnXp 7
    have p3 := hXp 6 7 (by norm_num); have p4 := hXp 7 8 (by norm_num); have p5 := hXp 8 13 (by norm_num)
    have p6 := hXp 1 6 (by norm_num)
    simp only [loopModK, pow_one] at *
    clear_value X x
    generalize X ^ 13 = Q13 at *
    generalize X ^ 8 = Q8 at *
    generalize X ^ 7 = Q7 at *
    generalize X ^ 6 = Q6 at *
    omega
  obtain ⟨⟨cur, ps, rfl, hcl, hps, hnd, hcur, hlen⟩, hcL⟩ := hL
  have hpsl : ps.length = r := by omega
  have hps0 : 0 < ps.length := by omega
  set p0 := ps[0] with hp0
  have hp0m : p0 ∈ ps := List.getElem_mem _
  set Tv := Val.list (ps.map fun p => encGroup p.2) with hTv
  set E4 := E3 ++ [camAcc cur ps] with hE4
  have dTs := fun (rest : List Val) => Det.get' (Det.var' (P := P) (env := E4 ++ rest) (i := 4)
    (by simp [hE4, hE3, hE2, hE1]; rfl)) (Det.nat 1)
    (show [encGroup cur, Tv][1]? = some Tv from rfl)
  have dT0 := fun (rest : List Val) => Det.get' (dTs rest) (Det.nat 0)
    (show (ps.map fun p => encGroup p.2)[0]? = some (encGroup p0.2) by
      rw [List.getElem?_map, List.getElem?_eq_getElem hps0]; rfl)
  -- the order of the first factor
  have hgp0 := (hps p0 hp0m).1
  have hcard : Nat.card (gens p0.2) = m.factorial / 2 := by
    rw [hgp0, camX_card_prod (by omega) hk1 (by omega), Finset.card_singleton, pow_one]
  refine EvalAll.letE (groupOrder_call ho hP.po (dT0 []) ⟨p0.2, rfl, rfl⟩) fun vo co hO => ?_
  obtain ⟨rfl, hco⟩ := hO
  have hco1 : co ≤ (groupOrderPrim ho).boundSize (camPB X) + 10000 * X ^ 7 := by
    have w1 := wt_encGroup_le_sq hcl
    have w2 := wt_encGroup_le_sq (hps p0 hp0m).2
    have w3 := wt_list2_le (encGroup cur) Tv
    have hxsw := cam_wt_factors_le ps (fun p hp => (hps p hp).2) (by omega)
    have hTve : (Val.list (ps.map fun p => encGroup p.2)).wt = Tv.wt := rfl
    have hb := (groupOrderPrim ho).bound_le (v := encGroup p0.2) (B := camPB X)
      ((Val.size_le_wt _).trans (by
        unfold camPB; have := hnXp 6; have := hXp 6 12 (by norm_num); omega))
    have h6 := hnXp 6
    have h7 := hnXp 7
    have h67 := hXp 6 7 (by norm_num)
    have hn2 : n ^ 2 ≤ (n + 1) ^ 7 := (Nat.pow_le_pow_left (by omega) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
    rw [hTve] at hxsw
    have h71 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ (by omega)
    clear * - hco w1 w2 w3 hxsw hb h6 h7 h67 hn2 h71
    omega
  rw [hcard]
  -- reading `m`
  set E5 := E4 ++ [Val.nat (m.factorial / 2)] with hE5
  have fM := camM_spec hP.cm (m := m) (n := n) (by omega) (by omega)
  refine EvalAll.letE (Det.call (Det.mk2 (Det.var' (P := P) (env := E5) (i := 5) rfl)
    (dn E5.tail)) fM) fun vm cm hm => ?_
  obtain ⟨rfl, hcm⟩ := hm
  have hcm1 : cm ≤ 10 ^ 10 * X ^ 4 := by
    have hwc : (Val.nat (m.factorial / 2)).wt ≤ n ^ 2 + 3 := hcard ▸ wt_card_le (gens p0.2)
    have w1 := wt_list2_le (.nat (m.factorial / 2)) (.nat n)
    have w2 := wt_nat_le n
    have w3 := wt_nat_le m
    have hn2 : n ^ 2 ≤ X ^ 2 := (Nat.pow_le_pow_left (by omega) 2).trans (hnXp 2)
    have hX2 := hXp 1 2 (by norm_num)
    have hin : (Val.list [.nat (m.factorial / 2), .nat n]).wt + n + 10 ≤ 100 * X ^ 2 := by
      clear * - hwc w1 w2 hn2 hX2 hnX
      simp only [pow_one] at *
      omega
    have hsq := Nat.pow_le_pow_left hin 2
    have e : (100 * X ^ 2) ^ 2 = 10000 * X ^ 4 := by ring
    rw [e] at hsq
    have kk := Nat.mul_le_mul_left camSearchK hsq
    have h24 := hXp 2 4 (by norm_num)
    have hmX : m + 1 ≤ X := by omega
    clear * - hcm hwc w1 w2 w3 hn2 hX2 kk h24 hmX hnX hxe hX
    simp only [pow_one, camSearchK] at *
    omega
  -- an orbit of the first factor, and reading `k`
  set E6 := E5 ++ [Val.nat m] with hE6
  obtain ⟨O0, hO0, ts0', hO0m, -, hts0l, fR0⟩ := camRestr_spec hP.restr (.list []) p0.2 hn0
  refine EvalAll.letE (Det.call (Det.mk2 (Det.nil (P := P) (env := E6))
    (dT0 [Val.nat (m.factorial / 2), Val.nat m] : Det P E6 _ _ _)) fR0) fun vA cA hA => ?_
  obtain ⟨rfl, hcA⟩ := hA
  have hcA1 : cA ≤ 10 ^ 36 * X ^ 42 := by
    have w1 := wt_encGroup_le_sq hcl
    have w2 := wt_encGroup_le_sq (hps p0 hp0m).2
    have w3 := wt_list2_le (encGroup cur) Tv
    have hxsw := cam_wt_factors_le ps (fun p hp => (hps p hp).2) (by omega)
    have hTve : (Val.list (ps.map fun p => encGroup p.2)).wt = Tv.wt := rfl
    rw [hTve] at hxsw
    have w4 := wt_list2_le (.list []) (encGroup p0.2)
    have hnil : (Val.list []).wt ≤ 10 := by decide
    have hOl : O0.length ≤ n := by simpa using hO0.length_le_card
    have w5 := wt_list3_le (natList (O0.map Fin.val)) (encGroup ts0') (encGroup p0.2)
    have w6 : (natList (O0.map Fin.val)).wt ≤ 5 * (n + 1) ^ 2 :=
      wt_natList_le_sq (B := n) (fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega) (by simpa using hOl)
    have w7 : (encGroup ts0').wt ≤ 360 * (n + 1) ^ 6 := by
      have h1 := wt_encGroup_le ts0'
      have hl := (hps p0 hp0m).2
      have h2 : (ts0'.length + 2) * (O0.length + 1) ≤ 3 * (n + 1) ^ 3 := by
        rw [hts0l]
        have : (p0.2.length + 1 + 2) * (O0.length + 1) ≤ (3 * (n + 1) ^ 2) * (n + 1) := by
          refine Nat.mul_le_mul ?_ (by omega)
          have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
          omega
        have e : (3 * (n + 1) ^ 2) * (n + 1) = 3 * (n + 1) ^ 3 := by ring
        omega
      have h3 := Nat.pow_le_pow_left h2 2
      have e : (3 * (n + 1) ^ 3) ^ 2 = 9 * (n + 1) ^ 6 := by ring
      omega
    have hR7 : ((Val.list [.list [], encGroup p0.2]).wt + 1) ^ 7 ≤ 700 ^ 7 * X ^ 42 := by
      have h1 : (Val.list [.list [], encGroup p0.2]).wt + 1 ≤ 700 * X ^ 6 := by
        have := hnXp 6; have := cam_ge_one_six n; omega
      calc _ ≤ (700 * X ^ 6) ^ 7 := Nat.pow_le_pow_left h1 7
        _ = 700 ^ 7 * X ^ 42 := by ring
    have kk := Nat.mul_le_mul_left camRestrK hR7
    have h2 := cam_ge_one_six n
    have h67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have h7 := hnXp 7
    have h742 := hXp 7 42 (by norm_num)
    have h2' : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    clear * - hcA w1 w2 w3 hxsw w4 hnil w5 w6 w7 kk h2 h67 h7 h742 h2'
    simp only [camRestrK] at kk hcA
    omega
  have hO0len : O0.length = m.choose k := by
    refine cam_orbit_length e p0.1 x₀ O0 hO0 fun y => ?_
    rw [hO0m y, hgp0]
    exact camX_orbit_factor (by omega) (by omega) p0.1 x₀ y
  set E7 := E6 ++ [Val.list [natList (O0.map Fin.val), encGroup ts0', encGroup p0.2]] with hE7
  have dS := Det.length (Det.get' (Det.var' (P := P) (env := E7) (i := 7) rfl) (Det.nat 0)
    (show [natList (O0.map Fin.val), encGroup ts0', encGroup p0.2][0]? =
      some (natList (O0.map Fin.val)) from rfl))
  have hSl : ((O0.map Fin.val).map Val.nat).length = m.choose k := by simp [hO0len]
  rw [hSl] at dS
  have fK := camK_spec hP.ck hk
  refine EvalAll.letE (Det.call (Det.mk2 (Det.var' (P := P) (env := E7) (i := 6) rfl) dS) fK)
    fun vk ck hK => ?_
  obtain ⟨rfl, hck⟩ := hK
  have hOl0 : O0.length ≤ n := by simpa using hO0.length_le_card
  have hck1 : ck ≤ 10 ^ 9 * X ^ 6 := by
    have w1 := wt_encGroup_le_sq (hps p0 hp0m).2
    have w5 := wt_list3_le (natList (O0.map Fin.val)) (encGroup ts0') (encGroup p0.2)
    have w6 : (natList (O0.map Fin.val)).wt ≤ 5 * (n + 1) ^ 2 :=
      wt_natList_le_sq (B := n) (fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; omega) (by simpa using hOl0)
    have w7 : (encGroup ts0').wt ≤ 40 * ((ts0'.length + 2) * (O0.length + 1)) ^ 2 :=
      wt_encGroup_le ts0'
    have hl := (hps p0 hp0m).2
    have h2 : (ts0'.length + 2) * (O0.length + 1) ≤ 3 * (n + 1) ^ 3 := by
      rw [hts0l]
      have : (p0.2.length + 1 + 2) * (O0.length + 1) ≤ (3 * (n + 1) ^ 2) * (n + 1) := by
        refine Nat.mul_le_mul ?_ (by omega)
        have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
        omega
      have e : (3 * (n + 1) ^ 2) * (n + 1) = 3 * (n + 1) ^ 3 := by ring
      omega
    have h3 := Nat.pow_le_pow_left h2 2
    have e : (3 * (n + 1) ^ 3) ^ 2 = 9 * (n + 1) ^ 6 := by ring
    have hne : (Val.list (List.map Val.nat (List.map Fin.val O0))).wt =
      (natList (O0.map Fin.val)).wt := rfl
    have hch : m.choose k ≤ n := by omega
    have wm := wt_nat_le m
    have wk := wt_nat_le k
    have wc := wt_nat_le (m.choose k)
    have w8 := wt_list2_le (.nat m) (.nat (m.choose k))
    have hin : (Val.list [.nat m, .nat (m.choose k)]).wt + m + 10 ≤ 20 * X := by omega
    have hsq := Nat.pow_le_pow_left hin 2
    have e2 : (20 * X) ^ 2 = 400 * X ^ 2 := by ring
    rw [e2] at hsq
    have kk := Nat.mul_le_mul_left camSearchK hsq
    have h6 := hnXp 6
    have h2' : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h26 := hXp 2 6 (by norm_num)
    have h16 := hXp 1 6 (by norm_num)
    clear * - hck w1 w5 w6 w7 h3 e hne hch wm wk wc w8 kk h6 h2' h26 h16 hmn hnX hk
    simp only [camSearchK, pow_one] at *
    omega
  -- the test `m + 2 ≤ (k + 1)²`
  set E8 := E7 ++ [Val.nat k] with hE8
  have dT := Det.arith (op := .lt) (Det.arith (op := .add) (Det.var' (P := P) (env := E8) (i := 6) rfl)
    (Det.nat (P := P) (env := E8) 1)) (Det.arith (op := .mul)
      (Det.arith (op := .add) (Det.var' (P := P) (env := E8) (i := 8) rfl) (Det.nat (P := P) (env := E8) 1))
      (Det.arith (op := .add) (Det.var' (P := P) (env := E8) (i := 8) rfl) (Det.nat (P := P) (env := E8) 1)))
  refine EvalAll.ite dT (fun _ _ h => ⟨_, h.1⟩) fun xt ct hxt => ?_
  obtain ⟨hxt1, hct⟩ := hxt
  cases hxt1
  have hct1 : ct ≤ 100 * X ^ 2 := by
    have w1 := wt_nat_le m
    have w2 := wt_nat_le k
    have w3 := wt_nat_le (BinOp.eval .add m 1)
    have w4 := wt_nat_le (BinOp.eval .add k 1)
    have w5 := wt_nat_le (BinOp.eval .mul (BinOp.eval .add k 1) (BinOp.eval .add k 1))
    have w6 := wt_nat_le (BinOp.eval .lt (BinOp.eval .add m 1)
      (BinOp.eval .mul (BinOp.eval .add k 1) (BinOp.eval .add k 1)))
    have hlt1 : BinOp.eval .lt (BinOp.eval .add m 1)
        (BinOp.eval .mul (BinOp.eval .add k 1) (BinOp.eval .add k 1)) ≤ 1 := by
      by_cases h : m + 1 < (k + 1) * (k + 1) <;> simp [BinOp.eval, h]
    have ea : BinOp.eval .add m 1 = m + 1 := rfl
    have eb : BinOp.eval .add k 1 = k + 1 := rfl
    have ec : BinOp.eval .mul (BinOp.eval .add k 1) (BinOp.eval .add k 1) = (k + 1) * (k + 1) := rfl
    have hkX : k + 1 ≤ X := by clear * - hk hmn hnX; omega
    have hkk : (k + 1) * (k + 1) ≤ X ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul hkX hkX
    have hX2 := hXp 1 2 (by norm_num)
    clear * - hct w1 w2 w3 w4 w5 w6 hlt1 ea eb ec hkk hX2 hmn hnX hk
    simp only [pow_one] at *
    omega
  have hsq : (k + 1) ^ 2 = (k + 1) * (k + 1) := by ring
  by_cases hlt : m + 1 < (k + 1) * (k + 1)
  · -- the answer `[2]`
    have hev : BinOp.eval .lt (BinOp.eval .add m 1)
        (BinOp.eval .mul (BinOp.eval .add k 1) (BinOp.eval .add k 1)) = 1 := by
      simp [BinOp.eval, hlt]
    rw [hev, if_neg one_ne_zero]
    refine (Det.snoc (Det.nil (P := P) (env := E8)) (Det.nat 2)).post fun cc hcc =>
      ⟨cam_out_two hM hk (by omega), ?_⟩
    have hW2 : (Val.list ([] ++ [Val.nat 2])).wt ≤ 30 := by decide
    have q2 := hXp 2 182 (by norm_num); have q4 := hXp 4 182 (by norm_num)
    have q6 := hXp 6 182 (by norm_num); have q7 := hXp 7 182 (by norm_num)
    have q8 := hXp 8 182 (by norm_num); have q9 := hXp 9 182 (by norm_num)
    have q13 := hXp 13 182 (by norm_num); have q42 := hXp 42 182 (by norm_num)
    have q0 : 1 ≤ X ^ 182 := Nat.one_le_pow _ _ (by omega)
    have h1X : 1 ≤ X := by omega
    have e : 2 * camFacK * 4000 ^ 30 * X ^ 182 = 2 * (camFacK * 4000 ^ 30) * X ^ 182 := by ring
    unfold camTailCost
    rw [e]
    refine cam_tail_sum h1X rfl (P := 200 * X ^ 8 + 2 * 10 ^ 7 * X ^ 9 + 10 ^ 14 * X ^ 13 +
      10 ^ 4 * X ^ 7 + 10 ^ 10 * X ^ 4 + 10 ^ 36 * X ^ 42 + 10 ^ 9 * X ^ 6 + 100 * X ^ 2 + 1000)
      (by clear * - q2 q4 q6 q7 q8 q9 q13 q42 q0; omega) cam_K0 ?_
    clear * - hcs1 hcN1 hcE1 hcL hco1 hcm1 hcA1 hck1 hct1 hcc hW2
    omega
  · have hev : BinOp.eval .lt (BinOp.eval .add m 1)
        (BinOp.eval .mul (BinOp.eval .add k 1) (BinOp.eval .add k 1)) = 0 := by
      simp [BinOp.eval, hlt]
    rw [hev, if_pos rfl]
    have hb : (k + 1) ^ 2 < m + 2 := by omega
    -- the columns, one factor at a time
    set ctx := Val.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m, .nat k] with hctx
    set xs := ps.map fun p => encGroup p.2 with hxs
    have hch2 : 2 ≤ m.choose k := (show 2 ≤ m by omega).trans (cam_m_le_choose hk1 hk)
    set R : Val → Val → Prop := fun y w => ∀ (i : Fin r) (ts : List (Perm (Fin n))),
      y = encGroup ts → gens ts = camProd e {i} → CamFacOut e i x₀ w with hR
    have hctxw : ctx.wt ≤ 1300 * (n + 1) ^ 6 := cam_ctx_wt_le ns hnsl (by omega) (by omega)
    set BF := (johnsonPrim hj).boundSize (camPB X) + (gmpNormalCentralizerPrim hqc).boundSize (camPB X) +
      camFacK * 4000 ^ 30 * X ^ 180 with hBF
    have hf : ∀ y ∈ xs, FunAll P (b + 103) (.list [ctx, y]) (fun w c => R y w ∧ c ≤ BF) := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      refine (camFac_spec hP.fac e hn0 h5 hk1 hk hb hmn ns p.2 hns p.1 (hps p hp).1).mono
        fun w c hw => ⟨fun i ts hts hgi => ?_, ?_⟩
      · obtain rfl := encGroup_injective hts
        have : p.1 = i := cam_prod_single_inj e (by omega) (by omega) hch2 x₀
          ((hps p hp).1.symm.trans hgi)
        exact this ▸ hw.1
      · exact cam_fac_bound hctxw (wt_encGroup_le_sq (hps p hp).2) hnX hw.2
    have dCtx := Det.mk4 (Det.var' (P := P) (env := E8) (i := 2) rfl)
      (Det.var' (P := P) (env := E8) (i := 3) rfl) (Det.var' (P := P) (env := E8) (i := 6) rfl)
      (Det.var' (P := P) (env := E8) (i := 8) rfl)
    have dXs := (dTs [Val.nat (m.factorial / 2), Val.nat m,
        Val.list [natList (O0.map Fin.val), encGroup ts0', encGroup p0.2], Val.nat k] :
      Det P E8 _ _ _)
    have hwsw : ∀ ws, List.Forall₂ R xs ws → ∀ w ∈ ws, w.wt ≤ 12 * (n + 1) ^ 3 := by
      intro ws hws w hw
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      have hjx : j < xs.length := hws.length_eq ▸ hj
      have hjp : j < ps.length := by simpa [hxs] using hjx
      have := hws.get hjx hj
      have hxj : xs.get ⟨j, hjx⟩ = encGroup (ps[j]'hjp).2 := by
        simp only [hxs, List.get_eq_getElem, List.getElem_map]
      exact cam_wt_col_le (this _ _ hxj (hps _ (List.getElem_mem _)).1) hmn hn0
    have hxsw := cam_wt_factors_le ps (fun p hp => (hps p hp).2) (by omega)
    refine EvalAll.letE (Ra := fun w c => (∃ ws, w = .list ws ∧ List.Forall₂ R xs ws) ∧
        c ≤ X * BF + 10 ^ 9 * X ^ 10)
      (EvalAll.call_funAll (Det.mk2 dCtx dXs) fun v ca hv => ?_) fun vC cC hC => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (map_spec hP.mp hf).mono fun w cb hw => ?_
      obtain ⟨ws, rfl, hws, hcb⟩ := hw
      refine ⟨⟨ws, rfl, hws⟩, ?_⟩
      have hW := cam_wt_list_le_of (hwsw ws hws)
      have hlw : ws.length = r := by rw [← hws.length_eq, hxs, List.length_map, hpsl]
      have hsum : (xs.map fun _ => BF).sum = xs.length * BF := by
        simp [List.map_const', List.sum_replicate]
      have hxl : xs.length = r := by rw [hxs, List.length_map, hpsl]
      rw [hsum, hxl] at hcb
      rw [hlw] at hW
      have hce : (Val.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m, .nat k]).wt =
        ctx.wt := rfl
      have hxe : (Val.list xs).wt = Tv.wt := rfl
      have w1 := wt_encGroup_le_sq (hs := ([] : List (Perm (Fin n)))) (by simp)
      have w2 := wt_encGroup_le_sq hnsl
      have w3 := wt_encGroup_le_sq hcl
      have w4 := wt_nat_le m
      have w5 := wt_nat_le k
      have w6 := wt_list2_le (encGroup cur) Tv
      have w7 := wt_list2_le ctx Tv
      have r67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      have r17 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
      have hce2 : (Val.list [Val.list [encGroup ns, encGroup ([] : List (Perm (Fin n))), .nat m,
        .nat k], Tv]).wt = (Val.list [ctx, Tv]).wt := rfl
      have hTve : (Val.list (ps.map fun p => encGroup p.2)).wt = Tv.wt := rfl
      have hca' : ca ≤ 30000 * (n + 1) ^ 7 := by
        clear * - hca hce hce2 hTve w1 w2 w3 w4 w5 w6 w7 hctxw hxsw r67 r17 hmn hk
        rw [hce, hce2] at hca
        rw [hTve] at hxsw
        omega
      have hcx : (Val.list [ctx, Val.list xs]).wt ≤ 5000 * (n + 1) ^ 7 + 6 := by
        have hx2 : (Val.list [ctx, Val.list xs]).wt = (Val.list [ctx, Tv]).wt := rfl
        have hTve : (Val.list (ps.map fun p => encGroup p.2)).wt = Tv.wt := rfl
        rw [hx2]
        exact cam_arith_cx w7 hctxw (hTve ▸ hxsw) r67
      exact cam_map_cost hn0 hnX hrn hcb hcx hW hca'
    obtain ⟨⟨ws, rfl, hws⟩, hcC⟩ := hC
    have hS : List.Forall₂ (fun i v => CamFacOut e i x₀ v) (camFsts ps) ws := by
      have hl := hws.length_eq
      refine List.forall₂_of_length_eq_of_get (by simpa [hxs] using hl) fun j h1 h2 => ?_
      have hjp : j < ps.length := by simpa [camFsts] using h1
      have hj : j < xs.length := by rw [hxs, List.length_map]; exact hjp
      have := hws.get hj h2
      have hpj : ps[j]'hjp ∈ ps := List.getElem_mem _
      have hxj : xs.get ⟨j, hj⟩ = encGroup (ps[j]'hjp).2 := by
        simp only [hxs, List.get_eq_getElem, List.getElem_map]
      have h3 := this (ps[j]'hjp).1 (ps[j]'hjp).2 hxj (hps _ hpj).1
      have h4 : (camFsts ps).get ⟨j, h1⟩ = (ps[j]'hjp).1 := by
        simp only [camFsts, List.get_eq_getElem, List.getElem_map]
      rw [h4]
      exact h3
    obtain ⟨e', hM', colsF, rfl, hEnc⟩ := cam_assemble hM h5 hk1 hk hb x₀ (camFsts ps) hnd
      (by simp [hpsl]) ws hS
    set E9 := E8 ++ [Val.list (colsF.map camColV)] with hE9
    have fT := camTr_spec hP.tr colsF
    refine EvalAll.letE (Det.call (Det.mk2 (dn E9.tail) (Det.var' (P := P) (env := E9) (i := 9) rfl))
      fT) fun vT cT hT => ?_
    obtain ⟨rfl, hcT⟩ := hT
    rw [hEnc]
    set E10 := E9 ++ [encKSetTuples e'] with hE10
    have dXs' := (dTs [Val.nat (m.factorial / 2), Val.nat m,
        Val.list [natList (O0.map Fin.val), encGroup ts0', encGroup p0.2], Val.nat k,
        Val.list (colsF.map camColV), encKSetTuples e'] : Det P E10 _ _ _)
    have hxl : xs.length = r := by simp [hxs, hpsl]
    have dOut := Det.snoc (Det.mk4 (Det.nat (P := P) (env := E10) 1)
      (Det.var' (P := P) (env := E10) (i := 6) rfl) (Det.var' (P := P) (env := E10) (i := 8) rfl)
      (Det.length dXs')) (Det.var' (P := P) (env := E10) (i := 10) rfl)
    rw [hxl] at dOut
    refine dOut.post fun cc hcc => ⟨cam_out_one hM' hk hb, ?_⟩
    -- the weights of the columns and of the answer
    have hcolw : (Val.list (colsF.map camColV)).wt ≤ 30 * (n + 1) ^ 4 := by
      have h1 := cam_wt_list_le_of (hwsw _ hws)
      have hl : (colsF.map camColV).length = r := by
        rw [← hws.length_eq, hxs, List.length_map, hpsl]
      rw [hl] at h1
      have h2 : r * (2 * (12 * (n + 1) ^ 3) + 1) ≤ (n + 1) * (25 * (n + 1) ^ 3) :=
        Nat.mul_le_mul (by clear * - hrn; omega)
          (by have := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos n); clear * - this; omega)
      have e : (n + 1) * (25 * (n + 1) ^ 3) = 25 * (n + 1) ^ 4 := by ring
      have : 2 ^ 4 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_left (by clear * - hn0; omega) 4
      clear * - h1 h2 e this
      omega
    have hencw : (encKSetTuples e').wt ≤ 200 * (n + 1) ^ 5 := by
      rw [← hEnc]
      have h1 := cam_wt_list_le_of
        (vs := (List.finRange n).map fun x => Val.list (colsF.map fun f => f x))
        (B := 3 * ((Val.list (colsF.map camColV)).wt + 1))
        (fun v hv => by
          obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
          have := cam_wt_row_le colsF x; clear * - this; omega)
      simp only [List.length_map, List.length_finRange] at h1
      have h2 : n * (2 * (3 * ((Val.list (colsF.map camColV)).wt + 1)) + 1) ≤
          (n + 1) * (190 * (n + 1) ^ 4) :=
        Nat.mul_le_mul (by clear * -; omega) (by
          have := Nat.one_le_pow 4 (n + 1) (Nat.succ_pos n); clear * - this hcolw; omega)
      have e : (n + 1) * (190 * (n + 1) ^ 4) = 190 * (n + 1) ^ 5 := by ring
      have : 2 ^ 5 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_left (by clear * - hn0; omega) 5
      clear * - h1 h2 e this
      omega
    have hcT1 : cT ≤ 10 ^ 17 * X ^ 16 := by
      have w1 := wt_list2_le (.nat n) (.list (colsF.map camColV))
      have w2 := wt_nat_le n
      have h4 := hnXp 4
      have h5 := hnXp 5
      have h45 := hXp 4 5 (by norm_num)
      have h416 := hXp 5 16 (by norm_num)
      have h14 := hXp 1 4 (by norm_num)
      have hin : (Val.list [.nat n, .list (colsF.map camColV)]).wt + n + 1 ≤ 80 * X ^ 4 := by
        clear * - w1 w2 hcolw h4 h14 hnX
        simp only [pow_one] at *
        omega
      have hp := Nat.pow_le_pow_left hin 4
      have e : (80 * X ^ 4) ^ 4 = 40960000 * X ^ 16 := by ring
      rw [e] at hp
      have kk := Nat.mul_le_mul_left camTrK hp
      have hencX : (Val.list ((List.finRange n).map fun x =>
          Val.list (colsF.map fun f => f x))).wt ≤ 200 * X ^ 5 := by
        rw [hEnc]; exact hencw.trans (Nat.mul_le_mul_left _ h5)
      have h1 := hXp 1 16 (by norm_num)
      clear * - hcT w1 w2 hcolw h4 h45 h416 h14 hnX kk hencX hxe hX h1
      simp only [camTrK, pow_one] at *
      omega
    have hcc1 : cc ≤ 10 ^ 6 * X ^ 7 := by
      have w1 := wt_encGroup_le_sq hcl
      have w3 := wt_list2_le (encGroup cur) Tv
      have hxsw := cam_wt_factors_le ps (fun p hp => (hps p hp).2) (by clear * - hpsl hrn; omega)
      have hTve : (Val.list (ps.map fun p => encGroup p.2)).wt = Tv.wt := rfl
      rw [hTve] at hxsw
      have w4 := wt_list4_le (.nat 1) (.nat m) (.nat k) (.nat r)
      have w5 := wt_list_le ([Val.nat 1, Val.nat m, Val.nat k, Val.nat r] ++ [encKSetTuples e'])
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, List.length_append, List.length_cons, List.length_nil] at w5
      have wm := wt_nat_le m; have wk := wt_nat_le k; have wr := wt_nat_le r
      have w1' : (Val.nat 1).wt = 3 := rfl
      have h5 := hnXp 5; have h6 := hnXp 6; have h7 := hnXp 7
      have h57 := hXp 5 7 (by norm_num); have h17 := hXp 1 7 (by norm_num)
      have h67 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num)
      clear * - hcc w1 w3 hxsw w4 w5 wm wk wr w1' hencw h5 h6 h7 h57 h17 h67 hmn hk hrn hnX
      simp only [pow_one] at *
      omega
    have hfw : (Val.list ([Val.nat 1, Val.nat m, Val.nat k, Val.nat r] ++ [encKSetTuples e'])).wt ≤
        10 ^ 4 * X ^ 7 := by
      have w5 := wt_list_le ([Val.nat 1, Val.nat m, Val.nat k, Val.nat r] ++ [encKSetTuples e'])
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, List.length_append, List.length_cons, List.length_nil] at w5
      have wm := wt_nat_le m; have wk := wt_nat_le k; have wr := wt_nat_le r
      have w1' : (Val.nat 1).wt = 3 := rfl
      have h5 := hnXp 5; have h57 := hXp 5 7 (by norm_num); have h17 := hXp 1 7 (by norm_num)
      clear * - w5 wm wk wr w1' hencw h5 h57 h17 hmn hk hrn hnX
      simp only [pow_one] at *
      omega
    have eBF : X * BF = X * ((johnsonPrim hj).boundSize (camPB X) +
        (gmpNormalCentralizerPrim hqc).boundSize (camPB X)) + camFacK * 4000 ^ 30 * X ^ 181 := by
      rw [hBF]; ring
    rw [eBF] at hcC
    have q2 := hXp 2 182 (by norm_num); have q4 := hXp 4 182 (by norm_num)
    have q6 := hXp 6 182 (by norm_num); have q7 := hXp 7 182 (by norm_num)
    have q8 := hXp 8 182 (by norm_num); have q9 := hXp 9 182 (by norm_num)
    have q10 := hXp 10 182 (by norm_num); have q16 := hXp 16 182 (by norm_num)
    have q13 := hXp 13 182 (by norm_num); have q42 := hXp 42 182 (by norm_num)
    have h1X : 1 ≤ X := le_trans (Nat.succ_pos n) hnX
    have q0 : 1 ≤ X ^ 182 := Nat.one_le_pow _ _ h1X
    have e : 2 * camFacK * 4000 ^ 30 * X ^ 182 = 2 * (camFacK * 4000 ^ 30) * X ^ 182 := by ring
    have e2 : camFacK * 4000 ^ 30 * X ^ 181 = (camFacK * 4000 ^ 30) * X ^ 181 := by ring
    rw [e2] at hcC
    unfold camTailCost
    rw [e]
    refine cam_tail_sum h1X rfl (P := 200 * X ^ 8 + 2 * 10 ^ 7 * X ^ 9 + 10 ^ 14 * X ^ 13 +
      10 ^ 4 * X ^ 7 + 10 ^ 10 * X ^ 4 + 10 ^ 36 * X ^ 42 + 10 ^ 9 * X ^ 6 + 100 * X ^ 2 +
      10 ^ 9 * X ^ 10 + 10 ^ 17 * X ^ 16 + 10 ^ 7 * X ^ 7 + 1000)
      (by clear * - q2 q4 q6 q7 q8 q9 q10 q16 q13 q42 q0; omega) cam_K0 ?_
    clear * - hcs1 hcN1 hcE1 hcL hco1 hcm1 hcA1 hck1 hct1 hcC hcT1 hcc1 hfw
    omega

end GI.Impl
