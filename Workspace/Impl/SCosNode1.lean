import Workspace.Impl.SCosNodeMath

/-!
# Functions 0–3, the pieces

The cost scale `scosNodeS n = 100000 (n + 1)^7` bounds every weight that functions 0–3 see
(`N = n + n`, group values of weight at most `scosW n`, permutations and indicators of
`Fin N`). Its powers `scosNodeS3`, `scosNodeS5` are definitions, so that `omega` treats them as
atoms. Then the deterministic pieces: the count of 1s of an indicator, the index of the first 1,
the orbit labels, the indicator of an orbit, and the indicator of `Φ \ O`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

/-! ### Cost scales -/

/-- The weight scale of functions 0–3. -/
def scosNodeS (n : ℕ) : ℕ := 100000 * (n + 1) ^ 7

/-- Its cube. -/
def scosNodeS3 (n : ℕ) : ℕ := scosNodeS n ^ 3

/-- Its fifth power. -/
def scosNodeS5 (n : ℕ) : ℕ := scosNodeS n ^ 5

theorem scosNodeS_big (n : ℕ) : 100000 ≤ scosNodeS n := by
  unfold scosNodeS
  have := Nat.one_le_pow 7 (n + 1) (by omega)
  omega

theorem scosNodeS_le3 (n : ℕ) : scosNodeS n ≤ scosNodeS3 n := by
  unfold scosNodeS3
  exact Nat.le_self_pow (by norm_num) _

theorem scosNodeS3_le5 (n : ℕ) : scosNodeS3 n ≤ scosNodeS5 n := by
  unfold scosNodeS3 scosNodeS5
  exact Nat.pow_le_pow_right (by have := scosNodeS_big n; omega) (by norm_num)

theorem scosNodeS_sq (n : ℕ) : scosNodeS n * scosNodeS n ≤ scosNodeS3 n := by
  unfold scosNodeS3
  calc scosNodeS n * scosNodeS n = scosNodeS n ^ 2 := by ring
    _ ≤ scosNodeS n ^ 3 := Nat.pow_le_pow_right (by have := scosNodeS_big n; omega) (by norm_num)

theorem scosNode_le_pow7 (n : ℕ) : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by norm_num) _

theorem scosNode_N (n : ℕ) : n + n + 2 ≤ scosNodeS n := by
  have := scosNode_le_pow7 n
  unfold scosNodeS
  omega

theorem scosNode_N3 (n : ℕ) : (n + n + 1 + 1) ^ 3 ≤ scosNodeS3 n := by
  unfold scosNodeS3
  exact Nat.pow_le_pow_left (scosNode_N n) 3

theorem scosNode_W (n : ℕ) : scosW n ≤ scosNodeS n := by
  unfold scosW scosNodeS
  have h1 : (n + n + 1) ^ 6 ≤ (2 * (n + 1)) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h2 : (2 * (n + 1)) ^ 6 = 64 * (n + 1) ^ 6 := by ring
  have h3 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem scosNode_orbPow {m : ℕ} (hm : m + 1 ≤ scosW n) :
    ((m + 1) * (n + n + 1)) ^ 5 ≤ scosNodeS5 n := by
  unfold scosNodeS5
  apply Nat.pow_le_pow_left
  unfold scosW scosNodeS at *
  have h1 : (m + 1) * (n + n + 1) ≤ 320 * (n + n + 1) ^ 6 * (n + n + 1) :=
    Nat.mul_le_mul_right _ hm
  have h2 : 320 * (n + n + 1) ^ 6 * (n + n + 1) = 320 * (n + n + 1) ^ 7 := by ring
  have h3 : (n + n + 1) ^ 7 ≤ (2 * (n + 1)) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have h4 : (2 * (n + 1)) ^ 7 = 128 * (n + 1) ^ 7 := by ring
  omega

theorem scosNode_wtPerm (σ : Perm (Fin (n + n))) : (encPerm σ).wt ≤ scosNodeS n := by
  have h := wt_encPerm_le σ
  have h1 : (n + n + 1) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (2 * (n + 1)) ^ 2 = 4 * (n + 1) ^ 2 := by ring
  have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold scosNodeS
  omega

theorem scosNode_wtInd (Φ : Finset (Fin n)) : (scosInd Φ).wt ≤ scosNodeS n := by
  have h := wt_encFun_le (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) (B := 1)
    (indF_le_one _ _)
  have e : scosInd Φ = encFun (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) := rfl
  rw [e]
  have hpow := scosNode_le_pow7 n
  unfold scosNodeS
  omega

theorem scosNode_wtLab (lab : Fin (n + n) → ℕ) (h : ∀ x, lab x ≤ n + n) :
    (encFun lab).wt ≤ scosNodeS n := by
  have h0 := wt_encFun_le_sq lab h
  have h1 : (n + n + 1) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (2 * (n + 1)) ^ 2 = 4 * (n + 1) ^ 2 := by ring
  have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold scosNodeS
  omega

theorem scosNode_wtAns {w : Val} {x : ScosPair n} {𝒢 : Subgroup (ScosPair n)}
    {Φ : Finset (Fin n)} (h : ScosAns n w x 𝒢 Φ) : w.wt ≤ 5 * scosNodeS n := by
  have := scosNodeS_big n
  rcases h with ⟨rfl, -⟩ | ⟨z, -, lv, rfl, -, hw⟩
  · simp; omega
  · have := wt_list2_le (encPerm (nintSum z)) lv
    have := scosNode_wtPerm (nintSum z)
    have := scosNode_W n
    omega

/-- The problem value, unpacked. -/
theorem scosNode_prob {v : Val} {𝒢 : Subgroup (ScosPair n)} {x : ScosPair n}
    {Φ : Finset (Fin n)} (hv : ScosProb n v 𝒢 x Φ) :
    ∃ gs : List (Perm (Fin (n + n))), v = .list [encGroup gs, encPerm (nintSum x), scosInd Φ] ∧
      gens gs = 𝒢.map nintSum ∧ (encGroup gs).wt ≤ scosW n := by
  obtain ⟨gv, rfl, ⟨gs, rfl, hgs⟩, hw⟩ := hv.val
  exact ⟨gs, rfl, hgs, hw⟩

theorem scosNode_wtProb (gv xv iv : Val) (h1 : gv.wt ≤ scosNodeS n) (h2 : xv.wt ≤ scosNodeS n)
    (h3 : iv.wt ≤ scosNodeS n) : (Val.list [gv, xv, iv]).wt ≤ 7 * scosNodeS n := by
  have := wt_list3_le gv xv iv
  have := scosNodeS_big n
  omega

theorem scosNode_wt4 (gv xv iv ov : Val) (h1 : gv.wt ≤ scosNodeS n) (h2 : xv.wt ≤ scosNodeS n)
    (h3 : iv.wt ≤ scosNodeS n) (h4 : ov.wt ≤ scosNodeS n) :
    (Val.list [gv, xv, iv, ov]).wt ≤ 9 * scosNodeS n := by
  have := wt_list4_le gv xv iv ov
  have := scosNodeS_big n
  omega

/-! ### Control helpers -/

/-- A `let` whose bound value is computed deterministically. -/
theorem scosNode_let {P : Program} {env : List Val} {e body : Expr} {v : Val} {ca : ℕ}
    {Q : Val → ℕ → Prop} (ha : Det P env e v ca)
    (hb : ∀ ca' ≤ ca, EvalAll P (env ++ [v]) body (fun w cb => Q w (ca' + cb + w.wt + 1))) :
    EvalAll P env (.letE e body) Q :=
  EvalAll.letE ha fun _ ca' h => by
    obtain ⟨rfl, h⟩ := h
    exact hb ca' h

/-- An `if` on a test computed deterministically. -/
theorem scosNode_ite {P : Program} {env : List Val} {c t e : Expr} {x cc : ℕ}
    {Q : Val → ℕ → Prop} (hc : Det P env c (.nat x) cc)
    (hb : ∀ cc' ≤ cc, EvalAll P env (if x = 0 then e else t)
      (fun w cb => Q w (cc' + cb + w.wt + 1))) :
    EvalAll P env (.ite c t e) Q :=
  EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    exact hb cc' h2

/-- A call on an argument computed deterministically. -/
theorem scosNode_call {P : Program} {env : List Val} {f : ℕ} {a : Expr} {v : Val} {ca : ℕ}
    {Q : Val → ℕ → Prop} (ha : Det P env a v ca)
    (hb : ∀ ca' ≤ ca, FunAll P f v (fun w cb => Q w (ca' + cb + w.wt + 1))) :
    EvalAll P env (.call f a) Q :=
  EvalAll.call_funAll ha fun _ ca' h => by
    obtain ⟨rfl, h⟩ := h
    exact hb ca' h

/-! ### The pieces -/

section Pieces

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

theorem scosNode_card_le (Φ : Finset (Fin n)) : Φ.card ≤ n := by
  simpa using Finset.card_le_univ Φ

/-- The number of 1s of an indicator. -/
theorem scosNode_countDet {env : List Val} {e : Expr} {Φ : Finset (Fin n)} {ce : ℕ}
    (he : Det 𝒫 env e (scosInd Φ) ce) :
    Det 𝒫 env (.call 24 (mk2 (.nat 1) e)) (.nat Φ.card) (ce + 200000 * scosNodeS3 n) := by
  have hw := scosNode_wtInd Φ
  rw [scosInd_eq_natList] at he hw
  have hc := count_spec (scos_count (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (xs := scosNodeL Φ) (j := 1) (B := n + n + 1)
    (fun x hx => (scosNodeL_le Φ x hx).trans (by omega)) (by omega)
    (by rw [length_scosNodeL]; omega)
  rw [scosNode_count] at hc
  refine (Det.call (Det.mk2 (Det.nat 1) he) hc).mono ?_
  have h1 := wt_list2_le (.nat 1) (natList (scosNodeL Φ))
  have h2 := wt_nat_le 1
  have h3 := wt_nat_le Φ.card
  have h4 := scosNode_card_le Φ
  have h5 := scosNode_N3 n
  have h6 := scosNodeS_le3 n
  have h7 := scosNode_N n
  unfold countK
  omega

/-- The index of the first 1 of the indicator of a nonempty `Φ`. -/
theorem scosNode_findDet {env : List Val} {e : Expr} {Φ : Finset (Fin n)} {ce : ℕ}
    (hne : Φ.Nonempty) (he : Det 𝒫 env e (scosInd Φ) ce) :
    ∃ a₀ ∈ Φ, Det 𝒫 env (.call 29 (mk2 (.nat 1) e)) (.nat (Fin.castAdd n a₀ : ℕ))
      (ce + 200000 * scosNodeS3 n) := by
  obtain ⟨a₀, ha₀, hidx⟩ := scosNode_findIdx hne
  refine ⟨a₀, ha₀, ?_⟩
  have hw := scosNode_wtInd Φ
  rw [scosInd_eq_natList] at he hw
  have hc := findEq_spec (scos_findEq (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (xs := scosNodeL Φ) (j := 1) (B := n + n + 1)
    (fun x hx => (scosNodeL_le Φ x hx).trans (by omega)) (by omega)
    (by rw [length_scosNodeL]; omega)
  rw [hidx] at hc
  refine (Det.call (Det.mk2 (Det.nat 1) he) hc).mono ?_
  have h1 := wt_list2_le (.nat 1) (natList (scosNodeL Φ))
  have h2 := wt_nat_le 1
  have h3 := wt_nat_le (Fin.castAdd n a₀ : ℕ)
  have h4 := (Fin.castAdd n a₀).isLt
  have h5 := scosNode_N3 n
  have h6 := scosNodeS_le3 n
  have h7 := scosNode_N n
  unfold findEqK
  omega

/-- The orbit labels of the group of pairs. -/
theorem scosNode_orbDet {gs : List (Perm (Fin (n + n)))} (hw : (encGroup gs).wt ≤ scosW n)
    {env : List Val} {e : Expr} {ce : ℕ} (he : Det 𝒫 env e (encGroup gs) ce) :
    ∃ lab : Fin (n + n) → ℕ, (∀ x y, lab x = lab y ↔ y ∈ genOrbit (1 :: gs) x) ∧
      (∀ x, lab x < n + n) ∧
      Det 𝒫 env (.call 37 e) (encFun lab) (ce + 2000000 * scosNodeS5 n) := by
  obtain ⟨lab, hdet, hiff, hlt⟩ :=
    orbits_spec (scos_orbit (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) (1 :: gs)
  have hlt' : ∀ x, lab x < n + n := fun x => (hlt x).1
  refine ⟨lab, hiff, hlt', (Det.call he hdet).mono ?_⟩
  have hlen : (1 :: gs).length + 1 ≤ scosW n := by
    have h1 := length_lt_wt_list ((1 :: gs).map encPerm)
    have h2 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
      wt_le_wt_list (by simp)
    rw [List.length_map] at h1
    omega
  have h1 := scosNode_orbPow hlen
  have h2 := scosNode_wtLab lab (fun x => (hlt' x).le)
  have h3 := scosNodeS_le3 n
  have h4 := scosNodeS3_le5 n
  have h5 := scosNodeS_big n
  unfold orbitK
  omega

/-- The indicator of the orbit of `a₀`. -/
theorem scosNode_eqIndDet {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)}
    (hinv : ScosInv 𝒢 Φ) {a₀ : Fin n} (ha : a₀ ∈ Φ) {gs : List (Perm (Fin (n + n)))}
    (hgs : gens gs = 𝒢.map nintSum) {lab : Fin (n + n) → ℕ}
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit (1 :: gs) x) (hlt : ∀ x, lab x < n + n)
    {env : List Val} {e1 e2 : Expr} {c1 c2 : ℕ}
    (h1 : Det 𝒫 env e1 (.nat (lab (Fin.castAdd n a₀))) c1) (h2 : Det 𝒫 env e2 (encFun lab) c2) :
    Det 𝒫 env (.call 33 (mk2 e1 e2)) (scosInd (scosNodeO 𝒢 Φ a₀))
      (c1 + c2 + 200000 * scosNodeS3 n) := by
  have hwl := scosNode_wtLab lab (fun x => (hlt x).le)
  have e : encFun lab = natList ((List.finRange (n + n)).map lab) := by
    simp [encFun, natList, List.map_map]
  rw [e] at h2 hwl
  have hc := eqInd_spec (scos_eqInd (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (xs := (List.finRange (n + n)).map lab) (j := lab (Fin.castAdd n a₀)) (B := n + n + 1)
    (fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      have := hlt i; omega)
    (by have := hlt (Fin.castAdd n a₀); omega) (by simp) (by omega)
  rw [scosNode_orbitInd hinv ha hgs hlab] at hc
  refine (Det.call (Det.mk2 h1 h2) hc).mono ?_
  have h3 := wt_list2_le (.nat (lab (Fin.castAdd n a₀))) (natList ((List.finRange (n + n)).map lab))
  have h4 := wt_nat_le (lab (Fin.castAdd n a₀))
  have h5 := hlt (Fin.castAdd n a₀)
  have h6 := scosNode_wtInd (scosNodeO 𝒢 Φ a₀)
  have h7 := scosNode_N3 n
  have h8 := scosNodeS_le3 n
  have h9 := scosNode_N n
  unfold eqIndK
  omega

/-- The value form of an indicator. -/
theorem scosNode_ind_list (Φ : Finset (Fin n)) :
    scosInd Φ = .list ((List.finRange (n + n)).map
      fun i => .nat (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) i)) := rfl

/-- One step of the sub-map: `ind[i] - oind[i]`. -/
theorem scosNode_stepDet {Φ O : Finset (Fin n)} (hO : O ⊆ Φ) (a : Fin (n + n)) :
    FunDet 𝒫 10 (.list [.list [scosInd Φ, scosInd O], .nat a])
      (.nat (indF (Equiv.refl (Fin (n + n))) (scosPhiF (Φ \ O)) a)) (1000 * scosNodeS n) := by
  refine FunDet.intro (scos_subStep (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) ?_
  set C : Val := .list [scosInd Φ, scosInd O] with hC
  have a0 : Det 𝒫 [.list [C, .nat a]] (arg 0) C _ :=
    Det.arg' (rest := []) (vs := [C, .nat a]) (j := 0) rfl
  have a1 : Det 𝒫 [.list [C, .nat a]] (arg 1) (.nat a) _ :=
    Det.arg' (rest := []) (vs := [C, .nat a]) (j := 1) rfl
  have g0 := Det.get' a0 (Det.nat 0) (rfl : [scosInd Φ, scosInd O][0]? = some (scosInd Φ))
  have g1 := Det.get' a0 (Det.nat 1) (rfl : [scosInd Φ, scosInd O][1]? = some (scosInd O))
  rw [scosNode_ind_list] at g0 g1
  have p0 := Det.get' g0 a1 (encFun_getElem? (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) a)
  have p1 := Det.get' g1 a1 (encFun_getElem? (indF (Equiv.refl (Fin (n + n))) (scosPhiF O)) a)
  have d := Det.arith' (op := .sub) p0 p1 (scosNode_sub hO a)
  unfold scosSubStepF
  refine d.mono ?_
  rw [← scosNode_ind_list, ← scosNode_ind_list]
  have hC2 := wt_list2_le (scosInd Φ) (scosInd O)
  have hA := wt_list2_le C (.nat a)
  have w1 := scosNode_wtInd Φ
  have w2 := scosNode_wtInd O
  have w3 := wt_nat_le (a : ℕ)
  have w4 := a.isLt
  have w5 := wt_nat_le (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) a)
  have w6 := wt_nat_le (indF (Equiv.refl (Fin (n + n))) (scosPhiF O) a)
  have w7 := indF_le_one (Equiv.refl (Fin (n + n))) (scosPhiF Φ) a
  have w8 := indF_le_one (Equiv.refl (Fin (n + n))) (scosPhiF O) a
  have w9 := indF_le_one (Equiv.refl (Fin (n + n))) (scosPhiF (Φ \ O)) a
  have w10 := scosNode_N n
  have w11 := scosNodeS_big n
  rw [← hC] at *
  omega

/-- The sub-map: the indicator of `Φ \ O` from those of `Φ` and `O`. -/
theorem scosNode_mapDet {Φ O : Finset (Fin n)} (hO : O ⊆ Φ) :
    FunDet 𝒫 69 (.list [.list [scosInd Φ, scosInd O], encPerm (1 : Perm (Fin (n + n)))])
      (scosInd (Φ \ O)) (100000 * scosNodeS3 n) := by
  set C : Val := .list [scosInd Φ, scosInd O] with hC
  set xs : List Val := (List.finRange (n + n)).map fun i => .nat ((1 : Perm (Fin (n + n))) i)
    with hxs
  have hm := map_spec (scos_subMap (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) (c := C)
    (xs := xs) (R := fun x w => ∃ i : Fin (n + n), x = .nat i ∧
      w = .nat (indF (Equiv.refl (Fin (n + n))) (scosPhiF (Φ \ O)) i))
    (B := fun _ => 1000 * scosNodeS n) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (scosNode_stepDet hO i) fun w cost hw => ⟨⟨i, rfl, hw.1⟩, hw.2⟩)
  have he : encPerm (1 : Perm (Fin (n + n))) = .list xs := rfl
  rw [he]
  refine FunAll.mono hm fun w cost ⟨ws, hw, hR, hcost⟩ => ⟨?_, ?_⟩
  · have := forall₂_map_eq (g := fun i => Val.nat (indF (Equiv.refl (Fin (n + n)))
      (scosPhiF (Φ \ O)) i)) (fun a _ w ⟨i, hi, hw⟩ => by
        have : (a : ℕ) = i := by simpa using hi
        rw [hw, ← Fin.ext this]) hR
    rw [hw, this]
    rfl
  · have hlen : xs.length = n + n := by simp [hxs]
    have hsum : (xs.map fun _ => 1000 * scosNodeS n).sum = (n + n) * (1000 * scosNodeS n) := by
      simp [hlen]
    rw [hsum, hlen] at hcost
    have hw1 : w.wt ≤ scosNodeS n := by
      have := scosNode_wtInd (Φ \ O)
      have hw' : w = scosInd (Φ \ O) := by
        have := forall₂_map_eq (g := fun i => Val.nat (indF (Equiv.refl (Fin (n + n)))
          (scosPhiF (Φ \ O)) i)) (fun a _ w ⟨i, hi, hw⟩ => by
            have : (a : ℕ) = i := by simpa using hi
            rw [hw, ← Fin.ext this]) hR
        rw [hw, this]; rfl
      rw [hw']; exact this
    have hw2 : (Val.list [C, .list xs]).wt ≤ 12 * scosNodeS n := by
      have := wt_list2_le C (.list xs)
      have : C.wt ≤ 2 * ((scosInd Φ).wt + (scosInd O).wt) + 6 := by
        rw [hC]; exact wt_list2_le (scosInd Φ) (scosInd O)
      have := scosNode_wtInd Φ
      have := scosNode_wtInd O
      have := scosNode_wtPerm (1 : Perm (Fin (n + n)))
      rw [he] at this
      have := scosNodeS_big n
      omega
    have hN := scosNode_N n
    have hS := scosNodeS_big n
    have hsq := scosNodeS_sq n
    generalize (Val.list [C, .list xs]).wt = A at *
    generalize w.wt = B at *
    generalize scosNodeS n = S at *
    have k1 : (n + n) * (1000 * S) ≤ 1000 * (S * S) := by
      have : (n + n) * (1000 * S) ≤ S * (1000 * S) := Nat.mul_le_mul_right _ (by omega)
      linarith
    have k2 : mapK * (n + n + 1) * (A + B + 1) ≤ 1000 * (S * (14 * S)) := by
      unfold mapK
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    nlinarith

/-- The sub-map with its argument built from the argument `[gv, xv, ind, oind]`. -/
theorem scosNode_subDet {Φ O : Finset (Fin n)} (hO : O ⊆ Φ) {gv xv : Val} {rest : List Val}
    (hw : (Val.list [gv, xv, scosInd Φ, scosInd O]).wt ≤ 9 * scosNodeS n) :
    Det 𝒫 (.list [gv, xv, scosInd Φ, scosInd O] :: rest)
      (.call 69 (mk2 (mk2 (arg 2) (arg 3)) (.call 72 (.length (arg 2)))))
      (scosInd (Φ \ O)) (200000 * scosNodeS3 n) := by
  have a2 : Det 𝒫 (.list [gv, xv, scosInd Φ, scosInd O] :: rest) (arg 2) (scosInd Φ) _ :=
    Det.arg' (j := 2) rfl
  have a3 : Det 𝒫 (.list [gv, xv, scosInd Φ, scosInd O] :: rest) (arg 3) (scosInd O) _ :=
    Det.arg' (j := 3) rfl
  have a2' : Det 𝒫 (.list [gv, xv, scosInd Φ, scosInd O] :: rest) (arg 2)
      (.list ((List.finRange (n + n)).map
        fun i => .nat (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) i)))
      (2 * (Val.list [gv, xv, scosInd Φ, scosInd O]).wt + 2 + 5) := a2
  have hl := Det.length a2'
  rw [List.length_map, List.length_finRange] at hl
  have hr := Det.call hl (GI.Lang.range_det (scos_range (c := c) (hps := hps) (hpre := hpre)
    (hmb := hmb)) (n + n))
  have hd := Det.call (Det.mk2 (Det.mk2 a2 a3) hr) (scosNode_mapDet hO)
  refine hd.mono ?_
  have := wt_list2_le (scosInd Φ) (scosInd O)
  have := wt_list2_le (.list [scosInd Φ, scosInd O]) (encPerm (1 : Perm (Fin (n + n))))
  have := scosNode_wtInd Φ
  have := scosNode_wtInd O
  have := scosNode_wtInd (Φ \ O)
  have := scosNode_wtPerm (1 : Perm (Fin (n + n)))
  have := scosNode_N n
  have := scosNodeS_big n
  have := scosNodeS_le3 n
  have h3 : (n + n + 1) ^ 3 ≤ scosNodeS3 n :=
    (Nat.pow_le_pow_left (by omega) 3).trans (scosNode_N3 n)
  omega

end Pieces

end GI.Impl
