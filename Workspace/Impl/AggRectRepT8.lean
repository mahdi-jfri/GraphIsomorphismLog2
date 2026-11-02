import Workspace.Impl.AggRectRepT7

/-!
# Glue for the top-level proof of the representation program

Small facts that connect the stage specs:

* encodings: `encFun f = natList (rcRL f)` (`rcR_encFun_eq`), the sets `W`, `R` as lists;
* the orbit labels of stage 1 are below `q`, and two labels agree exactly when the points share
  an orbit (`rcR_uno_eq`);
* weight bounds for the results of the stages (`rcR_wt_R1`, `rcR_wt_R2`, `rcR_wt_R3p`,
  `rcR_wt_R3c`);
* `k` and `q` are below the input weight (`rcR_In_k`, `rcR_In_q`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Lang GI.Rectangle
open GI.Cited (Val gens encPerm encGroup encPts)

/-! ### Encodings -/

theorem rcR_encFun_eq {n : ℕ} (f : Fin n → ℕ) : encFun f = natList (rcRL f) := by
  simp only [encFun, natList, rcRL, List.map_map]
  rfl

theorem rcR_setVal_eq {q : ℕ} (W : Finset (Fin q)) : rcSetVal W = natList (rcRInd W) :=
  rcR_encFun_eq _

theorem rcR_range_finRange {n : ℕ} (f : ℕ → ℕ) :
    (List.range n).map f = (List.finRange n).map fun i : Fin n => f (i : ℕ) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-! ### Orbit labels -/

theorem rcR_labs_lt {q : ℕ} (gs : List (Perm (Fin q))) :
    ∀ y ∈ (List.finRange q).map (orbitLabels gs), y < q := by
  intro y hy
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
  exact ((orbitLabels_spec gs).2 c).1

theorem rcR_labs_getD {q : ℕ} (gs : List (Perm (Fin q))) (c : Fin q) :
    ((List.finRange q).map (orbitLabels gs)).getD c 0 = orbitLabels gs c := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Two orbit labels agree exactly when the points lie in one orbit. -/
theorem rcR_uno_eq {q : ℕ} (gs : List (Perm (Fin q))) (d₁ d₂ : Fin q) :
    (((List.finRange q).map (orbitLabels gs)).getD d₁ 0 ==
      ((List.finRange q).map (orbitLabels gs)).getD d₂ 0) = decide (d₂ ∈ rcROrb (gens gs) d₁) := by
  rw [rcR_labs_getD, rcR_labs_getD]
  have h : orbitLabels gs d₁ = orbitLabels gs d₂ ↔ d₂ ∈ rcROrb (gens gs) d₁ := by
    rw [(orbitLabels_spec gs).1, mem_genOrbit, rcR_mem_orb]
    rfl
  by_cases h' : orbitLabels gs d₁ = orbitLabels gs d₂
  · rw [h', beq_self_eq_true]
    exact (decide_eq_true (h.1 h')).symm
  · rw [beq_eq_false_iff_ne.2 h']
    exact (decide_eq_false fun hh => h' (h.2 hh)).symm

/-! ### Weights of the stage results -/

theorem rcR_one_le_sq (M : ℕ) : M + 1 ≤ (M + 1) ^ 2 := by
  calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
    _ ≤ (M + 1) ^ 2 := rcR_pow_le_pow (by omega) (by norm_num)

theorem rcR_wt_R1' {q M x : ℕ} (hq : q ≤ M) (hx : x ≤ M) (labs : List ℕ)
    (hlab : ∀ y ∈ labs, y < q) (hlabl : labs.length = q) (t : ℕ → Bool) :
    (Val.list [.nat x, natList labs, natList (List.range q),
      natList ((List.range q).filter t)]).wt ≤ 50 * (M + 1) ^ 2 := by
  have h1 : (natList labs).wt ≤ 5 * (M + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by have := hlab y hy; omega) (by omega)
  have h2 := rcR_wt_range q M hq
  have h3 : (natList ((List.range q).filter t)).wt ≤ 5 * (M + 1) ^ 2 :=
    (rcR_wt_filter _ _).trans h2
  have h4 := wt_nat_le x
  have h5 := wt_list4_le (.nat x) (natList labs) (natList (List.range q))
    (natList ((List.range q).filter t))
  have h6 := rcR_one_le_sq M
  omega

/-- The result of stage 1. -/
theorem rcR_wt_R1 {k q M x : ℕ} (hq : q ≤ M) (hx : x ≤ M) (qs : List (Perm (Fin k) × Perm (Fin q))) :
    (rcRSt1Val x qs).wt ≤ 50 * (M + 1) ^ 2 :=
  rcR_wt_R1' hq hx _ (rcR_labs_lt _) (by simp) _

/-- The result of stage 2. -/
theorem rcR_wt_R2 {d₁ d₂ k M : ℕ} {ts gl : List (List ℕ)} (car uno : Bool) (h1 : d₁ ≤ M)
    (h2 : d₂ ≤ M) (hk : k ≤ M) (hts : (rcTV ts).wt ≤ 300 * (M + 1) ^ 5)
    (hgl : (rcTV gl).wt ≤ 300 * (M + 1) ^ 5) :
    (rcRSt2Val d₁ d₂ ts gl car uno k).wt ≤ 5000 * (M + 1) ^ 5 := by
  have hp : (M + 1) ^ 2 ≤ (M + 1) ^ 5 := rcR_pow_le_pow (by omega) (by norm_num)
  have h6 := rcR_one_le_sq M
  have hr := rcR_wt_range k M hk
  have hc : (Val.nat car.toNat).wt ≤ 3 := by
    have := wt_nat_le car.toNat; cases car <;> simp at this ⊢ <;> omega
  have hu : (Val.nat uno.toNat).wt ≤ 3 := by
    have := wt_nat_le uno.toNat; cases uno <;> simp at this ⊢ <;> omega
  have hd1 := wt_nat_le d₁
  have hd2 := wt_nat_le d₂
  have := wt_list_le_of [.nat d₁, .nat d₂, rcTV ts, rcTV gl, .nat car.toNat, .nat uno.toNat,
    natList (List.range k)] (c := 300 * (M + 1) ^ 5) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  unfold rcRSt2Val
  simp only [List.length_cons, List.length_nil] at this
  omega

/-- The result of stage 3 for pairs. -/
theorem rcR_wt_R3p {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M) (qs : List (Perm (Fin k) × Perm (Fin q)))
    (hl : qs.length ≤ (k + q) ^ 2) :
    (Val.list [.list (qs.map pairV), .list []]).wt ≤ 7000 * (M + 1) ^ 6 := by
  have h1 := rcR_wt_qs hk hq qs hl
  have h2 := wt_list_le ([] : List Val)
  have h3 := wt_list2_le (.list (qs.map pairV)) (.list [])
  have : 1 ≤ (M + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  simp only [List.map_nil, List.sum_nil, List.length_nil] at h2
  omega

/-- The result of stage 3 for single labels. -/
theorem rcR_wt_R3c {k q m M : ℕ} (hk : k ≤ M) (hq : q ≤ M) (hm : m ≤ k)
    (qs : List (Perm (Fin k) × Perm (Fin (m + q)))) (hl : qs.length ≤ (k + (m + q)) ^ 2)
    (rowT : List ℕ) (hr : ∀ y ∈ rowT, y ≤ M) (hrl : rowT.length ≤ M) :
    (Val.list [.list (qs.map pairV), natList rowT]).wt ≤ 500000 * (M + 1) ^ 6 := by
  have h1 := rcR_wt_qs (M := 2 * M) (by omega) (by omega) qs hl
  have h2 : (2 * M + 1) ^ 6 ≤ 64 * (M + 1) ^ 6 := by
    calc (2 * M + 1) ^ 6 ≤ (2 * (M + 1)) ^ 6 := rcR_pow_mono (by omega) 6
      _ = 64 * (M + 1) ^ 6 := by rw [mul_pow]; norm_num
  have h3 : (natList rowT).wt ≤ 5 * (M + 1) ^ 2 := wt_natList_le_sq hr hrl
  have h4 := wt_list2_le (.list (qs.map pairV)) (natList rowT)
  have h5 : (M + 1) ^ 2 ≤ (M + 1) ^ 6 := rcR_pow_le_pow (by omega) (by norm_num)
  have : 1 ≤ (M + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ### The input -/

theorem rcR_In_k {svs : List Val} {dl : List ℕ} {k q : ℕ} (hsv2 : svs[2]? = some (natList dl))
    (hdl : dl.length = k) (ps : List (Perm (Fin k) × Perm (Fin q))) (wl rl : List ℕ) :
    k ≤ (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]).wt := by
  have h1 := rcR_natList_len dl
  have h2 := wt_le_wt_list (List.mem_of_getElem? hsv2)
  have h3 : (Val.list svs).wt < (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl,
    natList rl]).wt := wt_le_wt_list (by simp)
  omega

theorem rcR_In_q {k q : ℕ} (svs : List Val) (ps : List (Perm (Fin k) × Perm (Fin q)))
    {wl : List ℕ} (hwl : wl.length = q) (rl : List ℕ) :
    q ≤ (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]).wt := by
  have h1 := rcR_natList_len wl
  have h3 : (natList wl).wt < (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl,
    natList rl]).wt := wt_le_wt_list (by simp)
  omega

theorem rcR_In_ps {k q : ℕ} (svs : List Val) (ps : List (Perm (Fin k) × Perm (Fin q)))
    (wl rl : List ℕ) :
    ps.length ≤ (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]).wt := by
  have h1 := length_lt_wt_list (ps.map pairV)
  have h3 : (Val.list (ps.map pairV)).wt < (Val.list [.list svs, .nat q, .list (ps.map pairV),
    natList wl, natList rl]).wt := wt_le_wt_list (by simp)
  rw [List.length_map] at h1
  omega

/-- The input of the first PointwiseStab call is small. -/
theorem rcR_wt_stabIn {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M)
    (ps : List (Perm (Fin k) × Perm (Fin q))) (hps : ps.length ≤ M) (pt : Fin (k + q)) :
    (Val.list [encGroup (ps.map encPair), encPts [pt]]).wt ≤ 1000 * (M + 1) ^ 4 := by
  have h1 := wt_list_encPerms_le ((1 : Perm (Fin (k + q))) :: ps.map encPair)
  simp only [List.length_cons, List.length_map] at h1
  have h2 : ((ps.length + 1 + 1) * (k + q + 1)) ^ 2 ≤ 16 * (M + 1) ^ 4 := by
    calc ((ps.length + 1 + 1) * (k + q + 1)) ^ 2 ≤ ((2 * (M + 1)) * (2 * (M + 1))) ^ 2 :=
          rcR_pow_mono (Nat.mul_le_mul (by omega) (by omega)) 2
      _ = 16 * (M + 1) ^ 4 := by ring
  have h3 := wt_nat_le (k + q)
  have h4 := wt_list2_le (.nat (k + q)) (.list ((1 :: ps.map encPair).map encPerm))
  have h5 := wt_encPts_le [pt]
  simp only [List.length_cons, List.length_nil] at h5
  have h6 := wt_list2_le (encGroup (ps.map encPair)) (encPts [pt])
  have h7 : (encGroup (ps.map encPair)).wt = (Val.list [.nat (k + q),
    .list ((1 :: ps.map encPair).map encPerm)]).wt := rfl
  have h8 : 1 * (k + q + 2) ≤ 3 * (M + 1) := by omega
  have h9 : M + 1 ≤ (M + 1) ^ 4 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 4 := rcR_pow_le_pow (by omega) (by norm_num)
  omega

end GI.Impl
