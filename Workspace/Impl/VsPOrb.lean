import Workspace.Impl.VsPWord

/-!
# The orbit of `ȳ` under conjugation

The orbit is kept as a list of pairs `(z, key z)`, deduplicated by keys, of length at most `cap`.

* `vsPOIns`: insert the conjugate `h z h⁻¹` if its key is new (`vsPOIns_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The value of a pair `(z, κ)`. -/
def vsPPV {n : ℕ} (p : Perm (Fin n) × List ℕ) : Val := .list [encPerm p.1, natList p.2]

/-- Insert `c` (with key `kf c`) unless the list is full or the key is present. -/
def vsPOIns {n : ℕ} (kf : Perm (Fin n) → List ℕ) (cap : ℕ) (O : List (Perm (Fin n) × List ℕ))
    (c : Perm (Fin n)) : List (Perm (Fin n) × List ℕ) :=
  if O.length < cap ∧ (O.map Prod.snd).findIdx (fun κ => decide (κ = kf c)) = O.length then
    O ++ [(c, kf c)] else O

/-- On `[κ, (z, κ')]`: `1` if `κ = κ'`. -/
def vsPPkE (eq : ℕ) : Expr := .call eq (mk2 (arg 0) (.get (arg 1) (.nat 1)))

theorem vsPPk_spec {P : Program} {f eq : ℕ} (hf : P.funs[f]? = some (vsPPkE eq))
    (heq : P.HasAt eq (eqNatsFuns eq)) {n : ℕ} (κ : List ℕ) (p : Perm (Fin n) × List ℕ) {N : ℕ}
    (hκ : κ.length ≤ N) (hκw : (natList κ).wt ≤ 5 * (N + 1) ^ 2)
    (hpw : (natList p.2).wt ≤ 5 * (N + 1) ^ 2) (hp1 : (encPerm p.1).wt ≤ 4 * (N + 1) ^ 2) :
    FunDet P f (.list [natList κ, vsPPV p]) (boolVal (decide (κ = p.2))) (10 ^ 5 * (N + 1) ^ 3) := by
  have a0 := Det.arg' (P := P) (vs := [natList κ, vsPPV p]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [natList κ, vsPPV p]) (rest := []) (j := 1) rfl
  have a1' : Det P [.list [natList κ, vsPPV p]] (arg 1) (.list [encPerm p.1, natList p.2]) _ := a1
  have d := Det.get' a1' (Det.nat 1)
    (show [encPerm p.1, natList p.2][1]? = some (natList p.2) from rfl)
  refine FunDet.intro hf ((Det.call (Det.mk2 a0 d) (eqNats_spec heq κ p.2)).mono ?_)
  have w1 := wt_list2_le (natList κ) (vsPPV p)
  have w2 := wt_list2_le (encPerm p.1) (natList p.2)
  have ep : (vsPPV p).wt = (Val.list [encPerm p.1, natList p.2]).wt := rfl
  have w3 := wt_list2_le (natList κ) (natList p.2)
  have wb := wt_boolVal_le (decide (κ = p.2))
  have hK : loopModK = 1000 := rfl
  have q0 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hm : loopModK * (κ.length + 1) * ((Val.list [natList κ, natList p.2]).wt + κ.length + 4) ≤
      1000 * (N + 1) * (30 * (N + 1) ^ 2) := by
    rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : 1000 * (N + 1) * (30 * (N + 1) ^ 2) = 30000 * (N + 1) ^ 3 := by ring
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- On `[h, z]`: `h z h⁻¹`. -/
def vsPConjE (comp inv : ℕ) : Expr :=
  .call comp (mk2 (.call comp (mk2 (arg 0) (arg 1))) (.call inv (arg 0)))

theorem vsPConj_spec {P : Program} {f comp inv n : ℕ} (hf : P.funs[f]? = some (vsPConjE comp inv))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    (h z : Perm (Fin n)) :
    FunDet P f (.list [encPerm h, encPerm z]) (encPerm (h * z * h⁻¹)) (vsPCommCost n) := by
  have a0 := Det.arg' (P := P) (vs := [encPerm h, encPerm z]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [encPerm h, encPerm z]) (rest := []) (j := 1) rfl
  have d1 := Det.call (Det.mk2 a0 a1) (compose_spec hcomp h z)
  have i0 := Det.call a0 (inv_spec hinv h)
  have d2 := Det.call (Det.mk2 d1 i0) (compose_spec hcomp (h * z) h⁻¹)
  refine FunDet.intro hf (d2.mono ?_)
  have w1 := wt_encPerm_le h
  have w2 := wt_encPerm_le z
  have w3 := wt_encPerm_le (h * z)
  have w4 := wt_encPerm_le h⁻¹
  have w5 := wt_encPerm_le (h * z * h⁻¹)
  have w8 := wt_list2_le (encPerm h) (encPerm z)
  have w10 := wt_list2_le (encPerm (h * z)) (encPerm h⁻¹)
  have q1 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q2 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q0 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [vsPCommCost, permK, invK]
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

theorem vsPPV_inj {n : ℕ} {p q : Perm (Fin n) × List ℕ} (h : vsPPV p = vsPPV q) : p = q := by
  simp only [vsPPV, Val.list.injEq, List.cons.injEq, and_true] at h
  exact Prod.ext (encPerm_injective h.1) (vsFMat_natList_inj h.2)

/-- The search test "pair with key `κ`". -/
noncomputable def vsPQK {n : ℕ} (κ : List ℕ) (v : Val) : Bool := by
  classical exact decide (∃ p : Perm (Fin n) × List ℕ, v = vsPPV p ∧ κ = p.2)

open Classical in
theorem vsPQK_enc {n : ℕ} (κ : List ℕ) (p : Perm (Fin n) × List ℕ) :
    vsPQK (n := n) κ (vsPPV p) = decide (p.2 = κ) := by
  unfold vsPQK
  refine Bool.decide_congr ⟨fun ⟨q, e, h⟩ => ?_, fun h => ⟨p, rfl, h.symm⟩⟩
  rw [vsPPV_inj e]; exact h.symm

/-- The insert step, on `[[pc, z, cap], O, h]`. -/
def vsPOInsE (conj key fd : ℕ) : Expr :=
  .letE (.call conj (mk2 (arg 2) (.get (arg 0) (.nat 1))))
  (.letE (.call key (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
    (.ite (.arith .lt (.length (arg 1)) (.get (arg 0) (.nat 2)))
      (.ite (.arith .lt (.call fd (mk2 (.var 2) (arg 1))) (.length (arg 1))) (arg 1)
        (.snoc (arg 1) (mk2 (.var 1) (.var 2))))
      (arg 1)))

/-- A list of pairs whose entries are keys of their elements. -/
def VsPOK (I : VecStabInst) (ws' cs : List (List ℕ)) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (O : List (Perm (Fin I.n) × List ℕ)) : Prop :=
  ∀ p ∈ O, p.2 = vsPKey I ws' cs Zp gs p.1 ∧ p.1 ∈ gens I.gs

/-- The cost of an insert step. -/
def vsPOInsCost (Cφ N W : ℕ) : ℕ :=
  vsPCommCost N + vsPKeyCost Cφ N W + (N + 1) * (10 ^ 5 * (N + 1) ^ 3) +
    10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 4) + 1000 * W + 10 ^ 4 * (N + 1) ^ 4

set_option maxHeartbeats 8000000 in
theorem vsPOIns_spec {P : Program} {f conj comp inv key mp it comm loc fd fd' pk eq eqb phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPOInsE conj key fd)) (hconj : P.funs[conj]? = some (vsPConjE comp inv))
    (hfd : P.HasAt fd (findFuns fd pk)) (hpk : P.funs[pk]? = some (vsPPkE eq))
    (heqn : P.HasAt eq (eqNatsFuns eq))
    (hkey : P.funs[key]? = some (vsPKeyE mp)) (hmp : P.HasAt mp (mapFuns mp it))
    (hit : P.funs[it]? = some (vsPKeyItemE comm loc fd'))
    (hcomm : P.funs[comm]? = some (vsPCommE comp inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfd' : P.HasAt fd' (findFuns fd' eqb)) (heq : P.HasAt eqb (vsPEqFuns eqb))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} (H : VsPCtxOK I N W ws' cs rows hs)
    (hZ : ∀ A ∈ Zp, VsWSq I.p cs.length A) (hZl : Zp.length ≤ N)
    (hpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W) (hgs : ∀ g ∈ gs, g ∈ gens I.gs)
    (hgl : gs.length ≤ N) {z h : Perm (Fin I.n)} (hz : z ∈ gens I.gs) (hh : h ∈ gens I.gs)
    {cap : ℕ} (hcap : cap ≤ N) {O : List (Perm (Fin I.n) × List ℕ)}
    (hO : VsPOK I ws' cs Zp gs O) (hOl : O.length ≤ cap) :
    FunDet P f (.list [.list [vsPPc I ws' cs rows hs gs Zp, encPerm z, .nat cap],
        .list (O.map vsPPV), encPerm h])
      (.list ((vsPOIns (vsPKey I ws' cs Zp gs) cap O (h * z * h⁻¹)).map vsPPV))
      (vsPOInsCost Cφ N W) := by
  set pc := vsPPc I ws' cs rows hs gs Zp
  set kf := vsPKey I ws' cs Zp gs
  set c := h * z * h⁻¹
  set κ := kf c
  set A := Val.list [.list [pc, encPerm z, .nat cap], .list (O.map vsPPV), encPerm h]
  set vs := [Val.list [pc, encPerm z, .nat cap], .list (O.map vsPPV), encPerm h]
  have hc : c ∈ gens I.gs := mul_mem (mul_mem hh hz) (inv_mem hh)
  -- the conjugate and its key
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dz := Det.get' a0 (Det.nat 1) (show [pc, encPerm z, Val.nat cap][1]? = some (encPerm z) from rfl)
  have dc := Det.call (Det.mk2 a2 dz) (vsPConj_spec hconj hcomp hinv h z)
  set E1 := [A, encPerm c]
  have b0 := Det.arg' (P := P) (vs := vs) (rest := [encPerm c]) (j := 0) rfl
  have bpc := Det.get' b0 (Det.nat 0) (show [pc, encPerm z, Val.nat cap][0]? = some pc from rfl)
  have v1 := Det.var' (P := P) (env := E1) (i := 1) rfl
  have dk := Det.call (Det.mk2 bpc v1) (vsPKey_spec hkey hmp hit hcomm hcomp hinv hloc hwl hfd' heq
    hphi H hZ hZl hpc hgs hgl hc)
  set E2 := [A, encPerm c, natList κ]
  have e0 := Det.arg' (P := P) (vs := vs) (rest := [encPerm c, natList κ]) (j := 0) rfl
  have e1 := Det.arg' (P := P) (vs := vs) (rest := [encPerm c, natList κ]) (j := 1) rfl
  have ecap := Det.get' e0 (Det.nat 2) (show [pc, encPerm z, Val.nat cap][2]? = some (.nat cap) from rfl)
  have dlen := Det.length e1
  have dcond := Det.arith' (op := .lt) dlen ecap rfl
  have w1 := Det.var' (P := P) (env := E2) (i := 1) rfl
  have w2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  -- the search for the key
  have hkeyl : ∀ p ∈ O, p.2.length ≤ N ∧ (∀ x ∈ p.2, x ≤ N) := by
    intro p hp
    rw [(hO p hp).1]
    refine ⟨by simp [vsPKey]; omega, fun x hx => ?_⟩
    simp only [vsPKey, List.mem_map] at hx
    obtain ⟨g, -, rfl⟩ := hx
    have : vsPKeyIdx I ws' cs Zp p.1 g ≤ Zp.length := List.findIdx_le_length
    omega
  have hκl : κ.length ≤ N ∧ ∀ x ∈ κ, x ≤ N := by
    refine ⟨by simp [κ, kf, vsPKey]; omega, fun x hx => ?_⟩
    simp only [κ, kf, vsPKey, List.mem_map] at hx
    obtain ⟨g, -, rfl⟩ := hx
    have : vsPKeyIdx I ws' cs Zp c g ≤ Zp.length := List.findIdx_le_length
    omega
  have hn := H.n
  have hp2 : ∀ g : Perm (Fin I.n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hq : ∀ v ∈ O.map vsPPV, FunDet P pk (.list [natList κ, v]) (boolVal (vsPQK (n := I.n) κ v))
      (10 ^ 5 * (N + 1) ^ 3) := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    rw [vsPQK_enc]
    have := vsPPk_spec hpk heqn κ p (N := N) hκl.1 (wt_natList_le_sq hκl.2 hκl.1)
      (wt_natList_le_sq (hkeyl p hp).2 (hkeyl p hp).1) (hp2 p.1)
    have e : decide (κ = p.2) = decide (p.2 = κ) := Bool.decide_congr ⟨Eq.symm, Eq.symm⟩
    rwa [e] at this
  have dF := Det.call (Det.mk2 w2 e1) ((find_spec hfd hq).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have eF : (O.map vsPPV).findIdx (vsPQK (n := I.n) κ) =
      (O.map Prod.snd).findIdx (fun κ' => decide (κ' = κ)) := by
    rw [List.findIdx_map, List.findIdx_map]
    congr 1
    funext p
    exact vsPQK_enc κ p
  rw [eF] at dF
  have dfc := Det.arith' (op := .lt) dF (Det.length e1) rfl
  have dsn := Det.snoc e1 (Det.mk2 w1 w2)
  have hOm : (O.map vsPPV).length = O.length := List.length_map _
  -- weights and costs
  have hOl' : O.length ≤ N := by omega
  have wpcW : pc.wt ≤ W := hpc
  have wκ : (natList κ).wt ≤ 5 * (N + 1) ^ 2 := wt_natList_le_sq hκl.2 hκl.1
  have wpair : ∀ p ∈ O, (vsPPV p).wt ≤ 30 * (N + 1) ^ 2 := by
    intro p hp
    have := wt_list2_le (encPerm p.1) (natList p.2)
    have := hp2 p.1
    have := wt_natList_le_sq (hkeyl p hp).2 (hkeyl p hp).1
    have e : (vsPPV p).wt = (Val.list [encPerm p.1, natList p.2]).wt := rfl
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have wO : (Val.list (O.map vsPPV)).wt ≤ 70 * (N + 1) ^ 3 := by
    have h1 := vs_wt_list_le_of (O.map vsPPV) (c := 30 * (N + 1) ^ 2) (by
      intro v hv; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact wpair p hp)
    rw [List.length_map] at h1
    have : O.length * (2 * (30 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (61 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
    have e : (N + 1) * (61 * (N + 1) ^ 2) = 61 * (N + 1) ^ 3 := by ring
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have wz := hp2 z
  have wh := hp2 h
  have wcc := hp2 c
  have wcap := wt_nat_le cap
  have w3 := wt_list3_le pc (encPerm z) (.nat cap)
  have wA := wt_list3_le (.list [pc, encPerm z, .nat cap]) (.list (O.map vsPPV)) (encPerm h)
  have eA : A.wt = (Val.list vs).wt := rfl
  have evs : (Val.list vs).wt = (Val.list [Val.list [pc, encPerm z, Val.nat cap],
      Val.list (List.map vsPPV O), encPerm h]).wt := rfl
  have w2 := wt_list2_le (encPerm h) (encPerm z)
  have w2' := wt_list2_le pc (encPerm c)
  have w2'' := wt_list2_le (natList κ) (.list (O.map vsPPV))
  have wp2 := wt_list2_le (encPerm c) (natList κ)
  have wsn : (Val.list (O.map vsPPV ++ [Val.list [encPerm c, natList κ]])).wt ≤
      (Val.list (O.map vsPPV)).wt + 2 * (Val.list [encPerm c, natList κ]).wt + 10 := by
    have := vsW_wt_append_le (O.map vsPPV) [Val.list [encPerm c, natList κ]]
    have := wt_list1_le (Val.list [encPerm c, natList κ])
    omega
  have hsum : ((O.map vsPPV).map fun _ => 10 ^ 5 * (N + 1) ^ 3).sum ≤
      (N + 1) * (10 ^ 5 * (N + 1) ^ 3) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
    exact Nat.mul_le_mul_right _ (by omega)
  have hloop : loopModK * ((O.map vsPPV).length + 1) * ((Val.list [natList κ,
      .list (O.map vsPPV)]).wt + 2 * (O.map vsPPV).length + 3) ≤
      10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 4) := by
    have h1 : (O.map vsPPV).length + 1 ≤ 10 * (N + 1) := by rw [List.length_map]; omega
    have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q24 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q14 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
    have h2 : (Val.list [natList κ, .list (O.map vsPPV)]).wt + 2 * (O.map vsPPV).length + 3 ≤
        W + 1000 * (N + 1) ^ 4 := by rw [List.length_map]; omega
    calc loopModK * ((O.map vsPPV).length + 1) * _ ≤ 1000 * (10 * (N + 1)) *
          (W + 1000 * (N + 1) ^ 4) := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 4) := by ring
  have hF := List.findIdx_le_length (p := fun κ' => decide (κ' = κ)) (xs := O.map Prod.snd)
  rw [List.length_map] at hF
  have wF := wt_nat_le ((O.map Prod.snd).findIdx (fun κ' => decide (κ' = κ)))
  have wlen := wt_nat_le (O.map vsPPV).length
  have hcomm4 : vsPCommCost I.n ≤ vsPCommCost N := by
    unfold vsPCommCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have q0 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q4 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have heval1 : ∀ a b : ℕ, GI.Machine.BinOp.eval .lt a b ≤ 1 := by
    intro a b; simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  have ev1 := heval1 (O.map vsPPV).length cap
  have ev2 := heval1 ((O.map Prod.snd).findIdx (fun κ' => decide (κ' = κ))) (O.map vsPPV).length
  have ecw : (encPerm (h * z * h⁻¹)).wt = (encPerm c).wt := rfl
  have eκ : (natList (vsPKey I ws' cs Zp gs c)).wt = (natList κ).wt := rfl
  apply FunDet.intro hf
  by_cases h1 : O.length < cap
  · have dc1 := dcond
    rw [show GI.Machine.BinOp.eval .lt (O.map vsPPV).length cap = 1 by
      simp [GI.Machine.BinOp.eval, hOm, h1]] at dc1
    by_cases h2 : (O.map Prod.snd).findIdx (fun κ' => decide (κ' = κ)) = O.length
    · -- new key: append
      have hv : vsPOIns kf cap O c = O ++ [(c, κ)] := by simp [vsPOIns, h1, h2, κ]
      have dc2 := dfc
      rw [show GI.Machine.BinOp.eval .lt ((O.map Prod.snd).findIdx
          (fun κ' => decide (κ' = κ))) (O.map vsPPV).length = 0 by
          simp [GI.Machine.BinOp.eval, hOm, h2]] at dc2
      rw [hv, List.map_append]
      have ev : Val.list (O.map vsPPV ++ [Val.list [encPerm c, natList κ]]) =
          .list (O.map vsPPV ++ [(c, κ)].map vsPPV) := rfl
      rw [← ev]
      refine (Det.letE dc (Det.letE dk (Det.ite_pos dc1 one_ne_zero (Det.ite_zero dc2 dsn)))).mono ?_
      unfold vsPOInsCost
      omega
    · -- key present: keep
      have hv : vsPOIns kf cap O c = O := by
        unfold vsPOIns; rw [if_neg]; rintro ⟨-, h2'⟩; exact h2 h2'
      have hlt : (O.map Prod.snd).findIdx (fun κ' => decide (κ' = κ)) < O.length := by
        have := List.findIdx_le_length (p := fun κ' => decide (κ' = κ)) (xs := O.map Prod.snd)
        rw [List.length_map] at this; omega
      have dc2 := dfc
      rw [show GI.Machine.BinOp.eval .lt ((O.map Prod.snd).findIdx
          (fun κ' => decide (κ' = κ))) (O.map vsPPV).length = 1 by
          simp only [GI.Machine.BinOp.eval, hOm, if_pos hlt]] at dc2
      rw [hv]
      refine (Det.letE dc (Det.letE dk (Det.ite_pos dc1 one_ne_zero
        (Det.ite_pos dc2 one_ne_zero e1)))).mono ?_
      unfold vsPOInsCost
      omega
  · have hv : vsPOIns kf cap O c = O := by simp [vsPOIns, h1]
    have dc0 := dcond
    rw [show GI.Machine.BinOp.eval .lt (O.map vsPPV).length cap = 0 by
      simp [GI.Machine.BinOp.eval, hOm, h1]] at dc0
    rw [hv]
    refine (Det.letE dc (Det.letE dk (Det.ite_zero dc0 e1))).mono ?_
    unfold vsPOInsCost

    omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- Insert the conjugates `h z h⁻¹`, `h ∈ hs1`. -/
def vsPOInner {n : ℕ} (kf : Perm (Fin n) → List ℕ) (cap : ℕ) (hs1 : List (Perm (Fin n)))
    (z : Perm (Fin n)) (O : List (Perm (Fin n) × List ℕ)) : List (Perm (Fin n) × List ℕ) :=
  hs1.foldl (fun O h => vsPOIns kf cap O (h * z * h⁻¹)) O

theorem vsPOIns_ok {ws' cs : List (List ℕ)} {Zp : List (List (List ℕ))} {gs : List (Perm (Fin I.n))}
    {cap : ℕ} {O : List (Perm (Fin I.n) × List ℕ)} (hO : VsPOK I ws' cs Zp gs O) (hOl : O.length ≤ cap)
    {c : Perm (Fin I.n)} (hc : c ∈ gens I.gs) :
    VsPOK I ws' cs Zp gs (vsPOIns (vsPKey I ws' cs Zp gs) cap O c) ∧
      (vsPOIns (vsPKey I ws' cs Zp gs) cap O c).length ≤ cap := by
  unfold vsPOIns
  split_ifs with h
  · refine ⟨fun p hp => ?_, by simp; omega⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hO p hp
    · simp at hp; subst hp; exact ⟨rfl, hc⟩
  · exact ⟨hO, hOl⟩

theorem vsPOInner_ok {ws' cs : List (List ℕ)} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))}
    (hh : ∀ h ∈ hs1, h ∈ gens I.gs) {z : Perm (Fin I.n)} (hz : z ∈ gens I.gs) :
    ∀ (i : ℕ) (O : List (Perm (Fin I.n) × List ℕ)), VsPOK I ws' cs Zp gs O → O.length ≤ cap →
      VsPOK I ws' cs Zp gs ((hs1.take i).foldl (fun O h =>
          vsPOIns (vsPKey I ws' cs Zp gs) cap O (h * z * h⁻¹)) O) ∧
        ((hs1.take i).foldl (fun O h => vsPOIns (vsPKey I ws' cs Zp gs) cap O (h * z * h⁻¹)) O).length
          ≤ cap := by
  intro i
  induction i with
  | zero => intro O hO hOl; simpa using ⟨hO, hOl⟩
  | succ i ih =>
    intro O hO hOl
    rcases Nat.lt_or_ge i hs1.length with hi | hi
    · rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
      obtain ⟨h1, h2⟩ := ih O hO hOl
      simp only [List.foldl_cons, List.foldl_nil]
      have hhi := hh _ (List.getElem_mem hi)
      exact vsPOIns_ok h1 h2 (mul_mem (mul_mem hhi hz) (inv_mem hhi))
    · rw [List.take_of_length_le (by omega)]
      have := ih O hO hOl
      rwa [List.take_of_length_le (by omega)] at this

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The weight of a list of pairs whose keys have entries `≤ N` and length `≤ N`. -/
theorem vsP_wt_pairs {N n : ℕ} (hn : n ≤ N) {O : List (Perm (Fin n) × List ℕ)} (hOl : O.length ≤ N)
    (hk : ∀ p ∈ O, p.2.length ≤ N ∧ ∀ x ∈ p.2, x ≤ N) :
    (Val.list (O.map vsPPV)).wt ≤ 70 * (N + 1) ^ 3 := by
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wpair : ∀ p ∈ O, (vsPPV p).wt ≤ 30 * (N + 1) ^ 2 := by
    intro p hp
    have := wt_list2_le (encPerm p.1) (natList p.2)
    have := hp2 p.1
    have := wt_natList_le_sq (hk p hp).2 (hk p hp).1
    have e : (vsPPV p).wt = (Val.list [encPerm p.1, natList p.2]).wt := rfl
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h1 := vs_wt_list_le_of (O.map vsPPV) (c := 30 * (N + 1) ^ 2) (by
    intro v hv; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact wpair p hp)
  rw [List.length_map] at h1
  have : O.length * (2 * (30 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (61 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
  have e : (N + 1) * (61 * (N + 1) ^ 2) = 61 * (N + 1) ^ 3 := by ring
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

theorem vsPOK_keys {ws' cs : List (List ℕ)} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {N : ℕ} (hZl : Zp.length ≤ N) (hgl : gs.length ≤ N)
    {O : List (Perm (Fin I.n) × List ℕ)} (hO : VsPOK I ws' cs Zp gs O) :
    ∀ p ∈ O, p.2.length ≤ N ∧ ∀ x ∈ p.2, x ≤ N := by
  intro p hp
  rw [(hO p hp).1]
  refine ⟨by simp [vsPKey]; omega, fun x hx => ?_⟩
  simp only [vsPKey, List.mem_map] at hx
  obtain ⟨g, -, rfl⟩ := hx
  have : vsPKeyIdx I ws' cs Zp p.1 g ≤ Zp.length := List.findIdx_le_length
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The cost of the inner fold. -/
def vsPOInnerCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) ^ 2 * vsPOInsCost Cφ N W + 2 * 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 4)

set_option maxHeartbeats 8000000 in
theorem vsPOInner_spec {P : Program} {fi ins conj comp inv key mp it comm loc fd fd' pk eq eqb phi Cφ N W : ℕ}
    (hfi : P.HasAt fi (foldlFuns fi ins)) (hins : P.funs[ins]? = some (vsPOInsE conj key fd))
    (hconj : P.funs[conj]? = some (vsPConjE comp inv))
    (hfd : P.HasAt fd (findFuns fd pk)) (hpk : P.funs[pk]? = some (vsPPkE eq))
    (heqn : P.HasAt eq (eqNatsFuns eq))
    (hkey : P.funs[key]? = some (vsPKeyE mp)) (hmp : P.HasAt mp (mapFuns mp it))
    (hit : P.funs[it]? = some (vsPKeyItemE comm loc fd'))
    (hcomm : P.funs[comm]? = some (vsPCommE comp inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfd' : P.HasAt fd' (findFuns fd' eqb)) (heq : P.HasAt eqb (vsPEqFuns eqb))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} (H : VsPCtxOK I N W ws' cs rows hs)
    (hZ : ∀ A ∈ Zp, VsWSq I.p cs.length A) (hZl : Zp.length ≤ N)
    (hpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W) (hgs : ∀ g ∈ gs, g ∈ gens I.gs)
    (hgl : gs.length ≤ N) {hs1 : List (Perm (Fin I.n))} (hh : ∀ h ∈ hs1, h ∈ gens I.gs)
    (hhl : hs1.length ≤ (N + 1) ^ 2) (hhw : (Val.list (hs1.map encPerm)).wt ≤ W)
    {z : Perm (Fin I.n)} (hz : z ∈ gens I.gs) {cap : ℕ} (hcap : cap ≤ N)
    {O : List (Perm (Fin I.n) × List ℕ)} (hO : VsPOK I ws' cs Zp gs O) (hOl : O.length ≤ cap) :
    FunDet P fi (.list [.list [vsPPc I ws' cs rows hs gs Zp, encPerm z, .nat cap],
        .list (hs1.map encPerm), .list (O.map vsPPV)])
      (.list ((vsPOInner (vsPKey I ws' cs Zp gs) cap hs1 z O).map vsPPV))
      (vsPOInnerCost Cφ N W) := by
  set c := Val.list [vsPPc I ws' cs rows hs gs Zp, encPerm z, .nat cap]
  have hn := H.n
  have hok := vsPOInner_ok (ws' := ws') (cs := cs) (Zp := Zp) (gs := gs) (cap := cap) hh hz
  have hM : ∀ i acc, i ≤ (hs1.map encPerm).length →
      acc = Val.list (((hs1.take i).foldl (fun O h => vsPOIns (vsPKey I ws' cs Zp gs) cap O (h * z * h⁻¹)) O).map vsPPV) →
      acc.wt ≤ 70 * (N + 1) ^ 3 := by
    rintro i acc - rfl
    obtain ⟨h1, h2⟩ := hok i O hO hOl
    exact vsP_wt_pairs hn (by omega) (vsPOK_keys hZl hgl h1)
  have hstep : ∀ i acc (hi : i < (hs1.map encPerm).length),
      acc = Val.list (((hs1.take i).foldl (fun O h => vsPOIns (vsPKey I ws' cs Zp gs) cap O (h * z * h⁻¹)) O).map vsPPV) →
      FunAll P ins (.list [c, acc, (hs1.map encPerm)[i]]) (fun w cost =>
        w = Val.list (((hs1.take (i + 1)).foldl (fun O h => vsPOIns (vsPKey I ws' cs Zp gs) cap O (h * z * h⁻¹)) O).map
          vsPPV) ∧ cost ≤ vsPOInsCost Cφ N W) := by
    rintro i acc hi rfl
    have hi' : i < hs1.length := by simpa using hi
    obtain ⟨h1, h2⟩ := hok i O hO hOl
    have e : (hs1.map encPerm)[i] = encPerm hs1[i] := by simp
    rw [e]
    refine FunAll.mono (vsPOIns_spec hins hconj hfd hpk heqn hkey hmp hit hcomm hcomp hinv hloc hwl
      hfd' heq hphi H hZ hZl hpc hgs hgl hz (hh _ (List.getElem_mem hi')) hcap h1 h2) ?_
    intro w cost hw
    refine ⟨?_, hw.2⟩
    rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
      List.foldl_append]
    rfl
  have hf := foldl_spec hfi (c := c) (xs := hs1.map encPerm) (acc0 := .list (O.map vsPPV))
    (Inv := fun i acc => acc = Val.list (((hs1.take i).foldl
      (fun O h => vsPOIns (vsPKey I ws' cs Zp gs) cap O (h * z * h⁻¹)) O).map vsPPV)) (M := 70 * (N + 1) ^ 3)
    (B := fun _ => vsPOInsCost Cφ N W) (by simp) hM hstep
  refine FunAll.mono hf fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]; rfl
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have h1 : hs1.length * vsPOInsCost Cφ N W ≤ (N + 1) ^ 2 * vsPOInsCost Cφ N W :=
      Nat.mul_le_mul_right _ hhl
    have wO := vsP_wt_pairs hn (by omega) (vsPOK_keys hZl hgl hO)
    have wz := (wt_encPerm_le z).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
    have wcap := wt_nat_le cap
    have w3 := wt_list3_le (vsPPc I ws' cs rows hs gs Zp) (encPerm z) (.nat cap)
    have ec : c.wt = (Val.list [vsPPc I ws' cs rows hs gs Zp, encPerm z, .nat cap]).wt := rfl
    have w4 := wt_list3_le c (.list (hs1.map encPerm)) (.list (O.map vsPPV))
    have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have hl2 : loopModK * (hs1.length + 1) * ((Val.list [c, .list (hs1.map encPerm),
        .list (O.map vsPPV)]).wt + hs1.length + 70 * (N + 1) ^ 3 + 1) ≤
        2 * 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 4) := by
      have h1 : hs1.length + 1 ≤ 2 * (N + 1) ^ 2 := by omega
      have h2 : (Val.list [c, .list (hs1.map encPerm), .list (O.map vsPPV)]).wt + hs1.length +
          70 * (N + 1) ^ 3 + 1 ≤ 10 * (W + 1000 * (N + 1) ^ 4) := by omega
      calc loopModK * (hs1.length + 1) * _ ≤ 1000 * (2 * (N + 1) ^ 2) *
            (10 * (W + 1000 * (N + 1) ^ 4)) := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
        _ = 2 * 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 4) := by ring
    unfold vsPOInnerCost
    omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- One pass: for every pair `(z, κ)` of the list (as it was), insert the conjugates of `z`. -/
def vsPOPass {n : ℕ} (kf : Perm (Fin n) → List ℕ) (cap : ℕ) (hs1 : List (Perm (Fin n)))
    (O : List (Perm (Fin n) × List ℕ)) : List (Perm (Fin n) × List ℕ) :=
  O.foldl (fun O' p => vsPOInner kf cap hs1 p.1 O') O

/-- The outer step, on `[[pc, cap, hs1], O', (z, κ)]`. -/
def vsPOOutE (fi : ℕ) : Expr :=
  .call fi (mk3 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 2) (.nat 0)) (.get (arg 0) (.nat 1)))
    (.get (arg 0) (.nat 2)) (arg 1))

theorem vsPOInner_ok' {ws' cs : List (List ℕ)} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))}
    (hh : ∀ h ∈ hs1, h ∈ gens I.gs) {z : Perm (Fin I.n)} (hz : z ∈ gens I.gs)
    {O : List (Perm (Fin I.n) × List ℕ)} (hO : VsPOK I ws' cs Zp gs O) (hOl : O.length ≤ cap) :
    VsPOK I ws' cs Zp gs (vsPOInner (vsPKey I ws' cs Zp gs) cap hs1 z O) ∧
      (vsPOInner (vsPKey I ws' cs Zp gs) cap hs1 z O).length ≤ cap := by
  have := vsPOInner_ok (ws' := ws') (cs := cs) (Zp := Zp) (gs := gs) (cap := cap) hh hz
    hs1.length O hO hOl
  rwa [List.take_length] at this

theorem vsPOPass_ok {ws' cs : List (List ℕ)} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))}
    (hh : ∀ h ∈ hs1, h ∈ gens I.gs) {O : List (Perm (Fin I.n) × List ℕ)}
    (hO : VsPOK I ws' cs Zp gs O) (hOl : O.length ≤ cap) :
    ∀ i, VsPOK I ws' cs Zp gs ((O.take i).foldl
        (fun O' p => vsPOInner (vsPKey I ws' cs Zp gs) cap hs1 p.1 O') O) ∧
      ((O.take i).foldl (fun O' p => vsPOInner (vsPKey I ws' cs Zp gs) cap hs1 p.1 O') O).length ≤ cap := by
  intro i
  induction i with
  | zero => simpa using ⟨hO, hOl⟩
  | succ i ih =>
    rcases Nat.lt_or_ge i O.length with hi | hi
    · rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact vsPOInner_ok' hh (hO _ (List.getElem_mem hi)).2 ih.1 ih.2
    · rw [List.take_of_length_le (by omega)]
      have := ih; rwa [List.take_of_length_le (by omega)] at this

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The cost of a pass. -/
def vsPOPassCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) * (vsPOInnerCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) +
    10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 3)

set_option maxHeartbeats 8000000 in
theorem vsPOPass_spec {P : Program} {fo out fi ins conj comp inv key mp it comm loc fd fd' pk eq eqb phi Cφ N W : ℕ}
    (hfo : P.HasAt fo (foldlFuns fo out)) (hout : P.funs[out]? = some (vsPOOutE fi))
    (hfi : P.HasAt fi (foldlFuns fi ins)) (hins : P.funs[ins]? = some (vsPOInsE conj key fd))
    (hconj : P.funs[conj]? = some (vsPConjE comp inv))
    (hfd : P.HasAt fd (findFuns fd pk)) (hpk : P.funs[pk]? = some (vsPPkE eq))
    (heqn : P.HasAt eq (eqNatsFuns eq))
    (hkey : P.funs[key]? = some (vsPKeyE mp)) (hmp : P.HasAt mp (mapFuns mp it))
    (hit : P.funs[it]? = some (vsPKeyItemE comm loc fd'))
    (hcomm : P.funs[comm]? = some (vsPCommE comp inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfd' : P.HasAt fd' (findFuns fd' eqb)) (heq : P.HasAt eqb (vsPEqFuns eqb))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} (H : VsPCtxOK I N W ws' cs rows hs)
    (hZ : ∀ A ∈ Zp, VsWSq I.p cs.length A) (hZl : Zp.length ≤ N)
    (hpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W) (hgs : ∀ g ∈ gs, g ∈ gens I.gs)
    (hgl : gs.length ≤ N) {hs1 : List (Perm (Fin I.n))} (hh : ∀ h ∈ hs1, h ∈ gens I.gs)
    (hhl : hs1.length ≤ (N + 1) ^ 2) (hhw : (Val.list (hs1.map encPerm)).wt ≤ W)
    {cap : ℕ} (hcap : cap ≤ N)
    {O : List (Perm (Fin I.n) × List ℕ)} (hO : VsPOK I ws' cs Zp gs O) (hOl : O.length ≤ cap) :
    FunDet P fo (.list [.list [vsPPc I ws' cs rows hs gs Zp, .nat cap, .list (hs1.map encPerm)],
        .list (O.map vsPPV), .list (O.map vsPPV)])
      (.list ((vsPOPass (vsPKey I ws' cs Zp gs) cap hs1 O).map vsPPV))
      (vsPOPassCost Cφ N W) := by
  set c := Val.list [vsPPc I ws' cs rows hs gs Zp, .nat cap, .list (hs1.map encPerm)]
  have hn := H.n
  have hok := vsPOPass_ok (ws' := ws') (cs := cs) (Zp := Zp) (gs := gs) (cap := cap) hh hO hOl
  set F := fun (O' : List (Perm (Fin I.n) × List ℕ)) (p : Perm (Fin I.n) × List ℕ) =>
    vsPOInner (vsPKey I ws' cs Zp gs) cap hs1 p.1 O'
  have hM : ∀ i acc, i ≤ (O.map vsPPV).length →
      acc = Val.list (((O.take i).foldl F O).map vsPPV) → acc.wt ≤ 70 * (N + 1) ^ 3 := by
    rintro i acc - rfl
    obtain ⟨h1, h2⟩ := hok i
    exact vsP_wt_pairs hn (by omega) (vsPOK_keys hZl hgl h1)
  have hstep : ∀ i acc (hi : i < (O.map vsPPV).length),
      acc = Val.list (((O.take i).foldl F O).map vsPPV) →
      FunAll P out (.list [c, acc, (O.map vsPPV)[i]]) (fun w cost =>
        w = Val.list (((O.take (i + 1)).foldl F O).map vsPPV) ∧
        cost ≤ vsPOInnerCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) := by
    rintro i acc hi rfl
    have hi' : i < O.length := by simpa using hi
    obtain ⟨h1, h2⟩ := hok i
    set O' := (O.take i).foldl F O
    set p := O[i]
    have e : (O.map vsPPV)[i] = vsPPV p := by simp [p]
    rw [e]
    set vs := [c, Val.list (O'.map vsPPV), vsPPV p]
    have a0 : Det P [.list vs] (arg 0) (.list [vsPPc I ws' cs rows hs gs Zp, .nat cap,
        .list (hs1.map encPerm)]) _ := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
    have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
    have a2 : Det P [.list vs] (arg 2) (.list [encPerm p.1, natList p.2]) _ :=
      Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
    have dpc := Det.get' a0 (Det.nat 0) (show [vsPPc I ws' cs rows hs gs Zp, Val.nat cap,
      Val.list (hs1.map encPerm)][0]? = some (vsPPc I ws' cs rows hs gs Zp) from rfl)
    have dcap := Det.get' a0 (Det.nat 1) (show [vsPPc I ws' cs rows hs gs Zp, Val.nat cap,
      Val.list (hs1.map encPerm)][1]? = some (.nat cap) from rfl)
    have dhs := Det.get' a0 (Det.nat 2) (show [vsPPc I ws' cs rows hs gs Zp, Val.nat cap,
      Val.list (hs1.map encPerm)][2]? = some (.list (hs1.map encPerm)) from rfl)
    have dz := Det.get' a2 (Det.nat 0) (show [encPerm p.1, natList p.2][0]? = some (encPerm p.1)
      from rfl)
    have hpz : p.1 ∈ gens I.gs := (hO p (List.getElem_mem hi')).2
    have dI := Det.call (Det.mk3 (Det.mk3 dpc dz dcap) dhs a1)
      (vsPOInner_spec hfi hins hconj hfd hpk heqn hkey hmp hit hcomm hcomp hinv hloc hwl hfd' heq
        hphi H hZ hZl hpc hgs hgl hh hhl hhw hpz hcap h1 h2)
    refine FunAll.intro hout (dI.post fun cst hcst => ⟨?_, ?_⟩)
    · rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some, List.foldl_append]
      rfl
    · have wpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W := hpc
      have wO' := vsP_wt_pairs hn (by omega) (vsPOK_keys hZl hgl h1)
      have hkp := vsPOK_keys hZl hgl hO p (List.getElem_mem hi')
      have wp1 := (wt_encPerm_le p.1).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
      have wp2 := wt_natList_le_sq hkp.2 hkp.1
      have wpp := wt_list2_le (encPerm p.1) (natList p.2)
      have ep : (vsPPV p).wt = (Val.list [encPerm p.1, natList p.2]).wt := rfl
      have wcap := wt_nat_le cap
      have wc := wt_list3_le (vsPPc I ws' cs rows hs gs Zp) (.nat cap) (.list (hs1.map encPerm))
      have ec : c.wt = (Val.list [vsPPc I ws' cs rows hs gs Zp, .nat cap,
        .list (hs1.map encPerm)]).wt := rfl
      have wvs := wt_list3_le c (Val.list (O'.map vsPPV)) (vsPPV p)
      have evs : (Val.list vs).wt = (Val.list [c, Val.list (O'.map vsPPV), vsPPV p]).wt := rfl
      have w3 := wt_list3_le (vsPPc I ws' cs rows hs gs Zp) (encPerm p.1) (.nat cap)
      have w3' := wt_list3_le (.list [vsPPc I ws' cs rows hs gs Zp, encPerm p.1, .nat cap])
        (.list (hs1.map encPerm)) (Val.list (O'.map vsPPV))
      have wres := vsP_wt_pairs hn (by have := (vsPOInner_ok' hh hpz h1 h2).2; omega)
        (vsPOK_keys hZl hgl (vsPOInner_ok' hh hpz h1 h2).1) (O := vsPOInner (vsPKey I ws' cs Zp gs)
          cap hs1 p.1 O')
      have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
      have ea2 : (Val.list [encPerm p.1, natList p.2]).wt = (Val.list [encPerm p.1, natList p.2]).wt :=
        rfl
      omega
  have hf := foldl_spec hfo (c := c) (xs := O.map vsPPV) (acc0 := .list (O.map vsPPV))
    (Inv := fun i acc => acc = Val.list (((O.take i).foldl F O).map vsPPV)) (M := 70 * (N + 1) ^ 3)
    (B := fun _ => vsPOInnerCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) (by simp) hM hstep
  refine FunAll.mono hf fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]; rfl
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have h1 : O.length * (vsPOInnerCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) ≤
        (N + 1) * (vsPOInnerCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have wO := vsP_wt_pairs hn (by omega) (vsPOK_keys hZl hgl hO)
    have wcap := wt_nat_le cap
    have wpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W := hpc
    have wc := wt_list3_le (vsPPc I ws' cs rows hs gs Zp) (.nat cap) (.list (hs1.map encPerm))
    have ec : c.wt = (Val.list [vsPPc I ws' cs rows hs gs Zp, .nat cap,
      .list (hs1.map encPerm)]).wt := rfl
    have w4 := wt_list3_le c (.list (O.map vsPPV)) (.list (O.map vsPPV))
    have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have hl2 : loopModK * (O.length + 1) * ((Val.list [c, .list (O.map vsPPV),
        .list (O.map vsPPV)]).wt + O.length + 70 * (N + 1) ^ 3 + 1) ≤
        10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 3) := by
      have h1 : O.length + 1 ≤ N + 1 := by omega
      have h2 : (Val.list [c, .list (O.map vsPPV), .list (O.map vsPPV)]).wt + O.length +
          70 * (N + 1) ^ 3 + 1 ≤ 10 * (W + 1000 * (N + 1) ^ 3) := by omega
      calc loopModK * (O.length + 1) * _ ≤ 1000 * (N + 1) * (10 * (W + 1000 * (N + 1) ^ 3)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
        _ = 10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 3) := by ring
    unfold vsPOPassCost
    omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- `F` passes from `[(y, key y)]`. -/
def vsPOrbit {n : ℕ} (kf : Perm (Fin n) → List ℕ) (cap : ℕ) (hs1 : List (Perm (Fin n))) (F : ℕ)
    (y : Perm (Fin n)) : List (Perm (Fin n) × List ℕ) :=
  (vsPOPass kf cap hs1)^[F] [(y, kf y)]

/-- The iteration step, on `[c', i, O]`. -/
def vsPOItE (fo : ℕ) : Expr := .call fo (mk3 (arg 0) (arg 2) (arg 2))

/-- The orbit program, on `[pc, y, cap, hs1, F]`. -/
def vsPOrbE (key it : ℕ) : Expr :=
  .letE (.call key (mk2 (arg 0) (arg 1)))
    (.call it (mk3 (mk3 (arg 0) (arg 2) (arg 3)) (arg 4) (mk1 (mk2 (arg 1) (.var 1)))))

theorem vsPOPass_ok' {ws' cs : List (List ℕ)} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))}
    (hh : ∀ h ∈ hs1, h ∈ gens I.gs) {O : List (Perm (Fin I.n) × List ℕ)}
    (hO : VsPOK I ws' cs Zp gs O) (hOl : O.length ≤ cap) :
    VsPOK I ws' cs Zp gs (vsPOPass (vsPKey I ws' cs Zp gs) cap hs1 O) ∧
      (vsPOPass (vsPKey I ws' cs Zp gs) cap hs1 O).length ≤ cap := by
  have := vsPOPass_ok (ws' := ws') (cs := cs) (Zp := Zp) (gs := gs) (cap := cap) hh hO hOl O.length
  rwa [List.take_length] at this

theorem vsPOrbit_ok {ws' cs : List (List ℕ)} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {cap : ℕ} (hcap : 1 ≤ cap) {hs1 : List (Perm (Fin I.n))}
    (hh : ∀ h ∈ hs1, h ∈ gens I.gs) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    ∀ F, VsPOK I ws' cs Zp gs (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y) ∧
      (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y).length ≤ cap := by
  intro F
  induction F with
  | zero =>
    refine ⟨fun p hp => ?_, by simp [vsPOrbit]; omega⟩
    simp [vsPOrbit] at hp; subst hp; exact ⟨rfl, hy⟩
  | succ F ih =>
    simp only [vsPOrbit, Function.iterate_succ_apply']
    exact vsPOPass_ok' hh ih.1 ih.2

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The cost of the orbit program. -/
def vsPOrbCost (Cφ N W : ℕ) : ℕ :=
  vsPKeyCost Cφ N W + (N + 1) * (vsPOPassCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) +
    10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 3) + 1000 * W + 10 ^ 4 * (N + 1) ^ 3

set_option maxHeartbeats 8000000 in
/-- **The orbit program.** -/
theorem vsPOrb_spec {P : Program} {f itb st fo out fi ins conj comp inv key mp it comm loc fd fd' pk eq eqb phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPOrbE key itb)) (hitb : P.HasAt itb (iterFuns itb st))
    (hst : P.funs[st]? = some (vsPOItE fo))
    (hfo : P.HasAt fo (foldlFuns fo out)) (hout : P.funs[out]? = some (vsPOOutE fi))
    (hfi : P.HasAt fi (foldlFuns fi ins)) (hins : P.funs[ins]? = some (vsPOInsE conj key fd))
    (hconj : P.funs[conj]? = some (vsPConjE comp inv))
    (hfd : P.HasAt fd (findFuns fd pk)) (hpk : P.funs[pk]? = some (vsPPkE eq))
    (heqn : P.HasAt eq (eqNatsFuns eq))
    (hkey : P.funs[key]? = some (vsPKeyE mp)) (hmp : P.HasAt mp (mapFuns mp it))
    (hit : P.funs[it]? = some (vsPKeyItemE comm loc fd'))
    (hcomm : P.funs[comm]? = some (vsPCommE comp inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfd' : P.HasAt fd' (findFuns fd' eqb)) (heq : P.HasAt eqb (vsPEqFuns eqb))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} (H : VsPCtxOK I N W ws' cs rows hs)
    (hZ : ∀ A ∈ Zp, VsWSq I.p cs.length A) (hZl : Zp.length ≤ N)
    (hpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W) (hgs : ∀ g ∈ gs, g ∈ gens I.gs)
    (hgl : gs.length ≤ N) {hs1 : List (Perm (Fin I.n))} (hh : ∀ h ∈ hs1, h ∈ gens I.gs)
    (hhl : hs1.length ≤ (N + 1) ^ 2) (hhw : (Val.list (hs1.map encPerm)).wt ≤ W)
    {cap : ℕ} (hcap1 : 1 ≤ cap) (hcap : cap ≤ N) {F : ℕ} (hF : F ≤ N)
    {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    FunDet P f (.list [vsPPc I ws' cs rows hs gs Zp, encPerm y, .nat cap, .list (hs1.map encPerm),
        .nat F])
      (.list ((vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y).map vsPPV)) (vsPOrbCost Cφ N W) := by
  have hn := H.n
  set pc := vsPPc I ws' cs rows hs gs Zp
  set c' := Val.list [pc, .nat cap, .list (hs1.map encPerm)]
  set vs := [pc, encPerm y, .nat cap, .list (hs1.map encPerm), .nat F]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dk := Det.call (Det.mk2 a0 a1) (vsPKey_spec hkey hmp hit hcomm hcomp hinv hloc hwl hfd' heq
    hphi H hZ hZl hpc hgs hgl hy)
  set E := [Val.list vs, natList (vsPKey I ws' cs Zp gs y)]
  have b k {v : Val} (hv : vs[k]? = some v) := Det.arg' (P := P) (vs := vs)
    (rest := [natList (vsPKey I ws' cs Zp gs y)]) (j := k) hv
  have v1 := Det.var' (P := P) (env := E) (i := 1) rfl
  have dc := Det.mk3 (b 0 rfl) (b 2 rfl) (b 3 rfl)
  have dacc := Det.mk1 (Det.mk2 (b 1 rfl) v1)
  have hok := vsPOrbit_ok (ws' := ws') (cs := cs) (Zp := Zp) (gs := gs) hcap1 hh hy
  have hM : ∀ i acc, i ≤ F →
      acc = Val.list ((vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 i y).map vsPPV) →
      acc.wt ≤ 70 * (N + 1) ^ 3 := by
    rintro i acc - rfl
    exact vsP_wt_pairs hn ((hok i).2.trans hcap) (vsPOK_keys hZl hgl (hok i).1)
  have hstep : ∀ i acc, i < F →
      acc = Val.list ((vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 i y).map vsPPV) →
      FunAll P st (.list [c', .nat i, acc]) (fun w cost =>
        w = Val.list ((vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 (i + 1) y).map vsPPV) ∧
        cost ≤ vsPOPassCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) := by
    rintro i acc hi rfl
    set O := vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 i y
    set ws := [c', .nat i, Val.list (O.map vsPPV)]
    have e0 := Det.arg' (P := P) (vs := ws) (rest := []) (j := 0) rfl
    have e2 := Det.arg' (P := P) (vs := ws) (rest := []) (j := 2) rfl
    have dp := Det.call (Det.mk3 e0 e2 e2) (vsPOPass_spec hfo hout hfi hins hconj hfd hpk heqn hkey
      hmp hit hcomm hcomp hinv hloc hwl hfd' heq hphi H hZ hZl hpc hgs hgl hh hhl hhw hcap
      (hok i).1 (hok i).2)
    refine FunAll.intro hst (dp.post fun cst hcst => ⟨?_, ?_⟩)
    · simp only [O, vsPOrbit, Function.iterate_succ_apply']
    · have wO := vsP_wt_pairs hn ((hok i).2.trans hcap) (vsPOK_keys hZl hgl (hok i).1)
        (O := O)
      have wcap := wt_nat_le cap
      have wc := wt_list3_le pc (.nat cap) (.list (hs1.map encPerm))
      have ec : c'.wt = (Val.list [pc, .nat cap, .list (hs1.map encPerm)]).wt := rfl
      have ww := wt_list3_le c' (.nat i) (Val.list (O.map vsPPV))
      have eww : (Val.list ws).wt = (Val.list [c', .nat i, Val.list (O.map vsPPV)]).wt := rfl
      have wi := wt_nat_le i
      have w3 := wt_list3_le c' (Val.list (O.map vsPPV)) (Val.list (O.map vsPPV))
      have wnew := vsP_wt_pairs hn ((hok (i + 1)).2.trans hcap)
        (vsPOK_keys hZl hgl (hok (i + 1)).1) (O := vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 (i + 1) y)
      have enew : vsPOPass (vsPKey I ws' cs Zp gs) cap hs1 O =
          vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 (i + 1) y := by
        simp only [O, vsPOrbit, Function.iterate_succ_apply']
      rw [enew] at hcst
      have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
      omega
  have hiter := iter_spec hitb (c := c') (k := F)
    (acc0 := Val.list [Val.list [encPerm y, natList (vsPKey I ws' cs Zp gs y)]])
    (Inv := fun i acc => acc = Val.list ((vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 i y).map vsPPV))
    (M := 70 * (N + 1) ^ 3) (B := fun _ => vsPOPassCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3)
    rfl hM hstep
  have dI := Det.call (Det.mk3 dc (b 4 rfl) dacc) ((hiter).mono fun w c hw => ⟨hw.1, hw.2⟩)
  refine FunDet.intro hf ((Det.letE dk dI).mono ?_)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1 : F * (vsPOPassCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) ≤
      (N + 1) * (vsPOPassCost Cφ N W + 1000 * W + 10 ^ 5 * (N + 1) ^ 3) :=
    Nat.mul_le_mul_right _ (by omega)
  have wpc : pc.wt ≤ W := hpc
  have hky := vsPOK_keys hZl hgl (hok 0).1 (y, vsPKey I ws' cs Zp gs y) (by simp [vsPOrbit])
  have hky' : (vsPKey I ws' cs Zp gs y).length ≤ N ∧ ∀ x ∈ vsPKey I ws' cs Zp gs y, x ≤ N := hky
  have wky := wt_natList_le_sq hky'.2 hky'.1
  have wy := (wt_encPerm_le y).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have wcap := wt_nat_le cap
  have wF := wt_nat_le F
  have wvs := wt_list_le vs
  have evs : (Val.list vs).wt = (Val.list [pc, encPerm y, .nat cap, .list (hs1.map encPerm),
    .nat F]).wt := rfl
  have wvs' := wt_list_le [pc, encPerm y, .nat cap, .list (hs1.map encPerm), .nat F]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wvs'
  have wc := wt_list3_le pc (.nat cap) (.list (hs1.map encPerm))
  have ec : c'.wt = (Val.list [pc, .nat cap, .list (hs1.map encPerm)]).wt := rfl
  have w2 := wt_list2_le pc (encPerm y)
  have wp := wt_list2_le (encPerm y) (natList (vsPKey I ws' cs Zp gs y))
  have wp1 := wt_list1_le (Val.list [encPerm y, natList (vsPKey I ws' cs Zp gs y)])
  have w3 := wt_list3_le c' (.nat F) (Val.list [Val.list [encPerm y, natList (vsPKey I ws' cs Zp gs y)]])
  have wres := vsP_wt_pairs hn ((hok F).2.trans hcap) (vsPOK_keys hZl hgl (hok F).1)
    (O := vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y)
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hl2 : loopModK * (F + 1) * ((Val.list [c', .nat F, Val.list [Val.list [encPerm y,
      natList (vsPKey I ws' cs Zp gs y)]]]).wt + F + 70 * (N + 1) ^ 3 + 1) ≤
      10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 3) := by
    have h1 : F + 1 ≤ N + 1 := by omega
    have h2 : (Val.list [c', .nat F, Val.list [Val.list [encPerm y,
        natList (vsPKey I ws' cs Zp gs y)]]]).wt + F + 70 * (N + 1) ^ 3 + 1 ≤
        10 * (W + 1000 * (N + 1) ^ 3) := by omega
    calc loopModK * (F + 1) * _ ≤ 1000 * (N + 1) * (10 * (W + 1000 * (N + 1) ^ 3)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) * (W + 1000 * (N + 1) ^ 3) := by ring
  have b1 : (Val.list vs).wt ≤ 4 * W + 20 * (N + 1) ^ 2 := by omega
  have b2 : c'.wt ≤ 4 * W + 20 * (N + 1) ^ 2 := by omega
  have b3 : (Val.list [Val.list [encPerm y, natList (vsPKey I ws' cs Zp gs y)]]).wt ≤
      100 * (N + 1) ^ 2 := by omega
  have b4 : (Val.list [c', Val.nat F, Val.list [Val.list [encPerm y,
      natList (vsPKey I ws' cs Zp gs y)]]]).wt ≤ 10 * W + 400 * (N + 1) ^ 2 := by omega
  unfold vsPOrbCost
  linarith

end GI.Impl
