import Workspace.Impl.AggCmpRep
import Workspace.Impl.AggCertWt

/-!
# The weight of the program states of the comparison phase

`CmRep` asks that every program state weighs at most a bound `Bw`. This file gives `Bw` as a
polynomial (`cmBw`): a program state `[σ.val par, u]` weighs at most
`cmBw par.wt k q M₀ L`, when the cache has at most `M₀` values, each lifted group at most
`(k + q)²` generators, at most `L` results are stored, the stage is at most `k`, and `u` is a
canonical answer or small (`cm_wt_state`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

variable {k : ℕ}

/-- **The weight bound of the program states.** -/
def cmBw (P k q M₀ L : ℕ) : ℕ := 10 * (P + ansW k + 10 ^ 4 * (M₀ + L + 1) * (k + q + 1) ^ 6)

theorem cm_wt_entV {q : ℕ} {p : List (Perm (Fin k)) × Perm (Fin k)} (h : p.1.length ≤ (k + q) ^ 2) :
    (cmEntV p).wt ≤ 1000 * (k + q + 1) ^ 6 := by
  have h1 := wt_encGroup_le p.1
  have h2 := wt_encPerm_le p.2
  have h3 := wt_list2_le (encGroup p.1) (encPerm p.2)
  obtain ⟨f1, f2, f3, f4, f5, e4, e6, -, -, -⟩ := cp_pow_facts k q
  have a : (p.1.length + 2) * (k + 1) ≤ 3 * (k + q + 1) ^ 2 * (k + q + 1) := by
    have : p.1.length + 2 ≤ 3 * (k + q + 1) ^ 2 := by omega
    exact Nat.mul_le_mul this (by omega)
  have b : ((p.1.length + 2) * (k + 1)) ^ 2 ≤ 9 * (k + q + 1) ^ 6 := by
    have := Nat.pow_le_pow_left a 2
    have e : (3 * (k + q + 1) ^ 2 * (k + q + 1)) ^ 2 = 9 * (k + q + 1) ^ 6 := by ring
    omega
  have c : (k + 1) ^ 2 ≤ (k + q + 1) ^ 6 := by
    have : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  unfold cmEntV
  omega

theorem cm_wt_oV (o : Option (Perm (Fin k))) : (cmOV o).wt ≤ 8 * (k + 1) ^ 2 + 6 := by
  rcases o with _ | a
  · simp only [cmOV]
    have := wt_list_le ([] : List Val)
    simp only [List.map_nil, List.sum_nil, List.length_nil] at this
    omega
  · simp only [cmOV]
    have h1 := wt_list_le [encPerm a]
    have h2 := wt_encPerm_le a
    simp at h1
    omega

/-- **The weight of a program state.** -/
theorem cm_wt_state {q M₀ L : ℕ} {par u : Val} {σ : CmSt k} (hj : σ.j ≤ k) (hfl : σ.fl ≤ 2)
    (hc : σ.cache.length ≤ M₀) (hcl : ∀ p ∈ σ.cache, p.1.length ≤ (k + q) ^ 2)
    (ha : σ.acc.length ≤ L) (hu : u.wt ≤ ansW k) :
    (Val.list [σ.val par, u]).wt ≤ cmBw par.wt k q M₀ L := by
  obtain ⟨f1, -, f3, f4, f5, -, -, -, f9, f10⟩ := cp_pow_facts k q
  have hC := cp_wt_list (vs := σ.cache.map cmEntV) (n := M₀) (c := 1000 * (k + q + 1) ^ 6)
    (by simpa using hc) (by
      simp only [List.mem_map]; rintro _ ⟨p, hp, rfl⟩; exact cm_wt_entV (hcl p hp))
  have hA := cp_wt_list (vs := σ.acc.map boolVal) (n := L) (c := 3) (by simpa using ha) (by
      simp only [List.mem_map]; rintro _ ⟨b, -, rfl⟩; exact wt_boolVal_le b)
  have hO := cm_wt_oV σ.o
  have hJ := wt_nat_le σ.j
  have hF := wt_nat_le σ.fl
  have hK := wt_list_le [par, .nat σ.j, cmOV σ.o, .list (σ.cache.map cmEntV),
    .list (σ.acc.map boolVal), .nat σ.fl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at hK
  have hS := wt_list2_le (σ.val par) u
  have e : (σ.val par).wt = (Val.list [par, .nat σ.j, cmOV σ.o, .list (σ.cache.map cmEntV),
    .list (σ.acc.map boolVal), .nat σ.fl]).wt := rfl
  have g6 : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have g2 : (k + 1) ^ 2 ≤ (k + q + 1) ^ 6 := le_trans f3 (le_trans f4 f5)
  have gk : k ≤ (k + q + 1) ^ 6 := by
    have : k + q + 1 ≤ (k + q + 1) ^ 6 := Nat.le_self_pow (by omega) _
    omega
  have m1 : M₀ * (2 * (1000 * (k + q + 1) ^ 6) + 1) ≤ 3000 * M₀ * (k + q + 1) ^ 6 := by
    have : 2 * (1000 * (k + q + 1) ^ 6) + 1 ≤ 3000 * (k + q + 1) ^ 6 := by omega
    calc M₀ * (2 * (1000 * (k + q + 1) ^ 6) + 1) ≤ M₀ * (3000 * (k + q + 1) ^ 6) :=
          Nat.mul_le_mul_left _ this
      _ = 3000 * M₀ * (k + q + 1) ^ 6 := by ring
  have m2 : L * 7 ≤ 7 * L * (k + q + 1) ^ 6 := by
    have := Nat.mul_le_mul_left (7 * L) g6
    omega
  have m3 : 10 ^ 4 * (M₀ + L + 1) * (k + q + 1) ^ 6 =
      10 ^ 4 * M₀ * (k + q + 1) ^ 6 + 10 ^ 4 * L * (k + q + 1) ^ 6 + 10 ^ 4 * (k + q + 1) ^ 6 := by
    ring
  have m4 : 3000 * M₀ * (k + q + 1) ^ 6 ≤ 10 ^ 4 * M₀ * (k + q + 1) ^ 6 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
  have m5 : 7 * L * (k + q + 1) ^ 6 ≤ 10 ^ 4 * L * (k + q + 1) ^ 6 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
  unfold cmBw
  omega

end GI.Impl
