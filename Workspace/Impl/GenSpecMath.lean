import Workspace.Impl.GenCase
import Workspace.Impl.GenCosetsMath
import Workspace.Impl.PolyBd
import Workspace.Lang.Lib.OrbitT

/-!
# Bounds for the general dispatcher that depend only on the number of points

The work of a dispatcher node may depend only on the node (`Rest.Wgeneral`), and the node knows
the number `k` of points but not the primitive quotient that the program exposes. So the bounds
on the data that the cost of the general step depends on are stated in terms of `k`.

* `gsBk k = (k + 2)^(72000 ⌊log₂ (k + 2)⌋)`: it bounds the order `|ρ(G)|` of a small quotient
  (`gs_card_le_Bk`: `|ρ(G)| ≤ exp(a log² d)` with `a = 36000` and `d ≤ k`), and `r!` for a product
  structure with `r` coordinates (`gs_fact_le_Bk`: `2^r ≤ d`, so `r ≤ log₂ d`).
* `gsWc k = 40 (k + 2)^4` bounds the weight of the output of the case decision
  (`gs_caseOut_wt_le`): a Maróti structure `Fin d ≃ (Fin r → KSet m l)` has `m, r ≤ d`.
* `gs_pbu_compW`: a uniformly polynomial function of a uniformly polynomial weight is uniformly
  polynomial.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encKSetTuples)

variable {Ω C : Type} {S : State Ω C}

/-- The bound on `|ρ(G)|` of a small quotient and on `r!` of a product structure, for a state on
`k` points. -/
def gsBk (k : ℕ) : ℕ := (k + 2) ^ (72000 * Nat.log 2 (k + 2))

theorem gsBk_mono {k k' : ℕ} (h : k ≤ k') : gsBk k ≤ gsBk k' :=
  (Nat.pow_le_pow_left (by omega) _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))))

theorem gs_one_le_log (k : ℕ) : 1 ≤ Nat.log 2 (k + 2) :=
  Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- **The order of a small quotient is at most `gsBk k`.** With `L = ⌊log₂ (k + 2)⌋ ≥ 1` we have
`log d ≤ log (k + 2) < (L + 1) log 2 ≤ 2 L`, so `a log² d ≤ 72000 L log (k + 2)`. -/
theorem gs_card_le_Bk (Q : PrimitiveQuotient S) {k : ℕ} (hd : Q.d ≤ k) (hs : Q.Small P₀.a) :
    Nat.card Q.ρ.range ≤ gsBk k := by
  have ha : P₀.a = 36000 := rfl
  unfold PrimitiveQuotient.Small at hs
  rw [ha] at hs
  set L := Nat.log 2 (k + 2) with hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast gs_one_le_log k
  have hlt : k + 2 < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hK : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hd2 : (2 : ℝ) ≤ Q.d := by exact_mod_cast Q.two_le
  have hdK : (Q.d : ℝ) ≤ (k : ℝ) + 2 := by
    have : (Q.d : ℝ) ≤ k := by exact_mod_cast hd
    linarith
  have hld0 : 0 ≤ Real.log Q.d := Real.log_nonneg (by linarith)
  have hld : Real.log Q.d ≤ Real.log ((k : ℝ) + 2) := Real.log_le_log (by linarith) hdK
  have hlk : Real.log ((k : ℝ) + 2) < (L + 1) * Real.log 2 := by
    have h1 : ((k : ℝ) + 2) < (2 : ℝ) ^ (L + 1) := by exact_mod_cast hlt
    have h2 := Real.log_lt_log hK h1
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h2
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hle2L : Real.log Q.d ≤ 2 * L := by nlinarith
  have hexp : Real.exp (36000 * Real.log Q.d ^ 2) ≤ Real.exp ((72000 * L : ℕ) *
      Real.log ((k : ℝ) + 2)) := by
    rw [Real.exp_le_exp]
    push_cast
    nlinarith
  rw [Real.exp_nat_mul, Real.exp_log hK] at hexp
  have := hs.trans hexp
  unfold gsBk
  exact_mod_cast this

/-- `m ≤ binom(m, l)` for `1 ≤ l < m`. -/
theorem gs_le_choose : ∀ {m l : ℕ}, 1 ≤ l → l < m → m ≤ m.choose l
  | 0, _, _, h => absurd h (by omega)
  | m + 1, l, h1, h2 => by
    rcases Nat.lt_or_ge l 2 with hl | hl
    · obtain rfl : l = 1 := by omega
      simp
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      show m + 1 ≤ m.choose l' + m.choose (l' + 1)
      have := gs_le_choose (m := m) (l := l') (by omega) (by omega)
      have := Nat.choose_pos (show l' + 1 ≤ m by omega)
      omega

/-- The numbers of a product structure: `l < m ≤ d`, `1 ≤ l` and `2^r ≤ d`. -/
theorem gs_kset_bounds (Q : PrimitiveQuotient S) {m l r : ℕ}
    (e : Fin Q.d ≃ (Fin r → Product.KSet m l)) :
    1 ≤ l ∧ l < m ∧ m ≤ Q.d ∧ 2 ^ r ≤ Q.d := by
  have hd := Q.card_kset_pow e
  have h2 := Q.two_le_choose e
  have hr := Q.one_le_r e
  have hlm : l ≤ m := by
    by_contra h
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h2
    omega
  have hl0 : l ≠ 0 := by rintro rfl; simp at h2
  have hlm' : l ≠ m := by rintro rfl; simp at h2
  have hcd : m.choose l ≤ Q.d := by rw [hd]; exact Nat.le_self_pow (by omega) _
  refine ⟨by omega, by omega, (gs_le_choose (by omega) (by omega)).trans hcd, ?_⟩
  rw [hd]
  exact Nat.pow_le_pow_left h2 r

/-- **`r! ≤ gsBk k`** for a product structure with `r` coordinates: `2^r ≤ d ≤ k`, so
`r ≤ ⌊log₂ (k + 2)⌋` and `r! ≤ r^r ≤ (k + 2)^r`. -/
theorem gs_fact_le_Bk (Q : PrimitiveQuotient S) {m l r k : ℕ}
    (e : Fin Q.d ≃ (Fin r → Product.KSet m l)) (hd : Q.d ≤ k) : r.factorial ≤ gsBk k := by
  obtain ⟨-, -, -, h2r⟩ := gs_kset_bounds Q e
  have hrL : r ≤ Nat.log 2 (k + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hrk : r ≤ k + 2 := (Nat.lt_two_pow_self).le.trans (by omega)
  calc r.factorial ≤ r ^ r := Nat.factorial_le_pow r
    _ ≤ (k + 2) ^ r := Nat.pow_le_pow_left hrk r
    _ ≤ gsBk k := Nat.pow_le_pow_right (by omega) (by omega)

/-- The weight bound of the output of the case decision on `k` points. -/
def gsWc (k : ℕ) : ℕ := 40 * (k + 2) ^ 4

/-- **The weight of a Maróti structure value** is at most `15 (k + 2)^4` when `d ≤ k`. -/
theorem gs_encKSet_wt_le (Q : PrimitiveQuotient S) {m l r k : ℕ}
    (e : Fin Q.d ≃ (Fin r → Product.KSet m l)) (hd : Q.d ≤ k) :
    (encKSetTuples e).wt ≤ 15 * (k + 2) ^ 4 := by
  obtain ⟨-, hlm, hmd, h2r⟩ := gs_kset_bounds Q e
  have hrk : r ≤ k := (Nat.lt_two_pow_self).le.trans (h2r.trans hd)
  have hmk : m ≤ k := hmd.trans hd
  set K := k + 2 with hK
  have hin : ∀ (x : Fin Q.d) (i : Fin r),
      (Val.list (((e x i).1.sort (· ≤ ·)).map fun a => Val.nat a)).wt ≤ 3 * K ^ 2 := by
    intro x i
    have h := wt_list_le_of (((e x i).1.sort (· ≤ ·)).map fun a => Val.nat a) (c := k + 1)
      (by
        intro v hv
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
        have := wt_nat_le a
        have ha' : a < m := by
          simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap,
            List.mem_singleton] at ha
          obtain ⟨b, -, rfl⟩ := ha
          exact b.2
        omega)
    have hlen : (((e x i).1.sort (· ≤ ·)).map fun a => Val.nat a).length = l := by
      rw [List.length_map]
      simp [List.bind_eq_flatMap, (e x i).2]
    rw [hlen] at h
    have : l * (2 * (k + 1) + 1) ≤ k * (2 * k + 3) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hmid : ∀ x : Fin Q.d, (Val.list ((List.finRange r).map fun i =>
      Val.list (((e x i).1.sort (· ≤ ·)).map fun a => Val.nat a))).wt ≤ 7 * K ^ 3 := by
    intro x
    have h := wt_list_le_of ((List.finRange r).map fun i =>
      Val.list (((e x i).1.sort (· ≤ ·)).map fun a => Val.nat a)) (c := 3 * K ^ 2) (by
        intro v hv
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
        exact hin x i)
    rw [List.length_map, List.length_finRange] at h
    have : r * (2 * (3 * K ^ 2) + 1) ≤ k * (2 * (3 * K ^ 2) + 1) := Nat.mul_le_mul_right _ hrk
    nlinarith
  have h := wt_list_le_of ((List.finRange Q.d).map fun x => Val.list ((List.finRange r).map
      fun i => Val.list (((e x i).1.sort (· ≤ ·)).map fun a => Val.nat a))) (c := 7 * K ^ 3) (by
    intro v hv
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hv
    exact hmid x)
  rw [List.length_map, List.length_finRange] at h
  have h0 : Q.d * (2 * (7 * K ^ 3) + 1) ≤ k * (2 * (7 * K ^ 3) + 1) := Nat.mul_le_mul_right _ hd
  unfold encKSetTuples
  refine h.trans ?_
  have hdK : Q.d + 2 ≤ K := by omega
  have h1 := Nat.mul_le_mul_right (2 * (7 * K ^ 3) + 1) hdK
  rw [Nat.add_mul] at h1
  have h2 : K ≤ K ^ 4 := Nat.le_self_pow (by norm_num) _
  have h3 : K * (2 * (7 * K ^ 3) + 1) = 14 * K ^ 4 + K := by ring
  have h4 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **The output of the case decision weighs at most `gsWc k`** when `d ≤ k`. -/
theorem gs_caseOut_wt_le (Q : PrimitiveQuotient S) {k : ℕ} (hd : Q.d ≤ k) {w : Val}
    (hw : CaseOut Q w) : w.wt ≤ gsWc k := by
  have hK : 1 ≤ (k + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  rcases hw with ⟨rfl, -⟩ | ⟨m, l, r, e, rfl, -, -, -⟩
  · have := wt_list1_le (.nat 0); have := wt_nat_le 0; unfold gsWc; omega
  · obtain ⟨-, hlm, hmd, h2r⟩ := gs_kset_bounds Q e
    have hrk : r ≤ k := (Nat.lt_two_pow_self).le.trans (h2r.trans hd)
    have hE := gs_encKSet_wt_le Q e hd
    have h := wt_list_le [.nat 1, .nat m, .nat l, .nat r, encKSetTuples e]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h
    have := wt_nat_le 1; have := wt_nat_le m; have := wt_nat_le l; have := wt_nat_le r
    have : k + 2 ≤ (k + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
    have : 2 ^ 4 ≤ (k + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    unfold gsWc
    omega

/-- **Substituting a uniformly polynomial weight** into a uniformly polynomial function gives a
uniformly polynomial function. -/
theorem gs_pbu_compW {f g : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (hg : PBU g) :
    PBU fun k W B => f k (g k W B) B := by
  obtain ⟨C, D, h⟩ := hf
  obtain ⟨C', D', h'⟩ := hg
  refine ⟨C * (C' + 1) ^ D, (D' + 1) * D, fun k W B => ?_⟩
  set X := W + B + k + 2 with hX
  have hX1 : 1 ≤ X := by omega
  have hg' : g k W B ≤ C' * X ^ D' := h' k W B
  have hXp : X ≤ X ^ (D' + 1) := Nat.le_self_pow (by omega) _
  have hXp' : X ^ D' ≤ X ^ (D' + 1) := Nat.pow_le_pow_right hX1 (by omega)
  have hY : g k W B + B + k + 2 ≤ (C' + 1) * X ^ (D' + 1) := by
    have := Nat.mul_le_mul_left C' hXp'
    rw [Nat.add_mul, one_mul]
    omega
  unfold PB
  calc f k (g k W B) B ≤ C * (g k W B + B + k + 2) ^ D := h k _ B
    _ ≤ C * ((C' + 1) * X ^ (D' + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY D)
    _ = C * (C' + 1) ^ D * X ^ ((D' + 1) * D) := by rw [mul_pow, ← pow_mul]; ring

/-- Substituting a function of `k` for `B`. -/
theorem gs_pbu_compB {f g : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (hg : PBU g) :
    PBU fun k W B => f k W (g k W B) := by
  obtain ⟨C, D, h⟩ := hf
  obtain ⟨C', D', h'⟩ := hg
  refine ⟨C * (C' + 1) ^ D, (D' + 1) * D, fun k W B => ?_⟩
  set X := W + B + k + 2 with hX
  have hX1 : 1 ≤ X := by omega
  have hg' : g k W B ≤ C' * X ^ D' := h' k W B
  have hXp : X ≤ X ^ (D' + 1) := Nat.le_self_pow (by omega) _
  have hXp' : X ^ D' ≤ X ^ (D' + 1) := Nat.pow_le_pow_right hX1 (by omega)
  have hY : W + g k W B + k + 2 ≤ (C' + 1) * X ^ (D' + 1) := by
    have := Nat.mul_le_mul_left C' hXp'
    rw [Nat.add_mul, one_mul]
    omega
  unfold PB
  calc f k W (g k W B) ≤ C * (W + g k W B + k + 2) ^ D := h k W _
    _ ≤ C * ((C' + 1) * X ^ (D' + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY D)
    _ = C * (C' + 1) ^ D * X ^ ((D' + 1) * D) := by rw [mul_pow, ← pow_mul]; ring

end GI.Impl
