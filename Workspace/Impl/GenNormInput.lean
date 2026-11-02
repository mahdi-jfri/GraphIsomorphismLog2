import Workspace.Impl.GenNormStepCost

/-! # Polynomial weight of the normalization input produced by exposure and recognition -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples)

/-- Sorted subset encodings contain at most `m` entries, each below `m`. -/
theorem normSetVal_wt {m : ℕ} (A : Finset (Fin m)) :
    (normSetVal A).wt ≤ 5 * (m + 1) ^ 2 := by
  have h := wt_natList_le_sq (xs := (A.sort (· ≤ ·)).map fun a : Fin m => (a : ℕ))
    (B := m) (by intro a ha; obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha; exact j.isLt.le)
    (by simpa only [List.length_map, Finset.length_sort, Fintype.card_fin] using Finset.card_le_univ A)
  simpa [normSetVal, natList, List.map_map, Function.comp_def] using h

/-- The single-factor Cameron table has polynomial weight in the phase size. -/
theorem normTable_wt {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (hfit : n ≤ S.N) :
    (encKSetTuples e).wt ≤ 1000 * (S.N + 2) ^ 3 := by
  obtain ⟨_, heq, -, -⟩ := normTable_get e ⟨0, by have := Q.two_le; omega⟩
  rw [heq]
  have hrow : ∀ x ∈ (List.finRange Q.d).map (fun x => Val.list [normSetVal (e x 0).1]),
      x.wt ≤ 10 * (m + 1) ^ 2 + 5 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    have h := wt_list_le [normSetVal (e i 0).1]
    have hs := normSetVal_wt (e i 0).1
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at h
    omega
  have ht := wt_list_le_of _ hrow
  simp only [List.length_map, List.length_finRange] at ht
  have hd : Q.d ≤ S.N := (Q.d_le_card en).trans hfit
  have hm : m + 1 ≤ 2 * (S.N + 2) := by have := normDegree_le en Q e hS; omega
  have hp : (m + 1) ^ 2 ≤ 4 * (S.N + 2) ^ 2 := by
    calc _ ≤ (2 * (S.N + 2)) ^ 2 := Nat.pow_le_pow_left hm 2
      _ = _ := by ring
  have hmul := Nat.mul_le_mul hd (show 2 * (10 * (m + 1) ^ 2 + 5) + 1 ≤
    80 * (S.N + 2) ^ 2 + 11 by omega)
  nlinarith [Nat.le_self_pow (by norm_num : 3 ≠ 0) (S.N + 2)]

/-- Every component of the branch input has polynomial weight. Exposure retains exactly
its quotient numbering, so no extra size assumption on the representative value is needed. -/
theorem normInput_wt {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (cc : C → ℕ) {sv rep hv : Val} (hcan : Canon en cc sv S)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (hr : normNumbered en Q rep)
    (hh : HierValC en hv (Q.pre ++ Q.top :: Q.post)) :
    (Val.list [sv, rep, hv, .nat m, .nat k, encKSetTuples e]).wt ≤
      10 ^ 6 * (S.N + 2) ^ 6 := by
  obtain ⟨lab, rfl, hl, -, -⟩ := hr
  have wr := wt_encFun_le_sq lab (fun i => (hl i).le)
  have ws := hcan.wt_le_poly
  have hn := hcan.fits
  have he := normTable_wt en Q e hS hcan.fits
  have hI := Q.intervalsOK hcan.small.1
  have hρ : rhoNat (Q.pre ++ Q.top :: Q.post) ≤ rhoNat S.hier := by
    have h : (rhoNat (Q.pre ++ Q.top :: Q.post) : ℝ) ≤ rhoNat S.hier := by
      rw [rhoNat_cast, rhoNat_cast]
      exact Q.rho_le
    exact_mod_cast h
  have hlen : (Q.pre ++ Q.top :: Q.post).length ≤ S.N :=
    (length_le_rhoNat (fun I h => (hI I h).1)).trans (hρ.trans hcan.small.2.1)
  have wh := hh.wt_le.trans (hierW_le (by omega : n + 1 ≤ S.N + 2) le_rfl hlen
    (fun I h => ⟨(hI I h).2.1, (hI I h).2.2.1, (hI I h).2.2.2⟩))
  have hm := normDegree_le en Q e hS
  have hk := (Q.k_bounds e).2.le
  have wm := wt_nat_le m
  have wk := wt_nat_le k
  have win := wt_list_le [sv, encFun lab, hv, .nat m, .nat k, encKSetTuples e]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at win
  have hp2 : (n + 1) ^ 2 ≤ (S.N + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hp26 : (S.N + 2) ^ 2 ≤ (S.N + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp36 : (S.N + 2) ^ 3 ≤ (S.N + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp16 : S.N + 2 ≤ (S.N + 2) ^ 6 := Nat.le_self_pow (by norm_num) _
  omega

end GI.Impl
