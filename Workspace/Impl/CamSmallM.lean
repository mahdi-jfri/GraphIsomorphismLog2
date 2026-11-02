import Workspace.Impl.CamTransport

/-!
# `m ≥ 5` above the order threshold

Step 3 of the reduction of `camProg` (`CamProg.lean`). A group with a Maróti structure has order at
most `r! · (m!)^r`, since each element is fixed by its coordinate permutation and its `r`
permutations of `Fin m` (`cam_card_le`). For `m ≤ 4` this is below `n^{1 + ⌊log₂ n⌋}`, where
`n = binom(m, k)^r ≥ 25` (`cam_five_le`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ}

/-- The number of points is `binom(m, k)^r`. -/
theorem cam_n_eq (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) :
    n = (m.choose k) ^ r := by
  have := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_finset_len,
    Fintype.card_fin] at this
  exact this

/-- A group with a Maróti structure has at most `r! · (m!)^r` elements. -/
theorem cam_card_le {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hM : MarotiStructure G e) :
    Nat.card G ≤ r.factorial * m.factorial ^ r := by
  choose σ h hgh using fun g : G => hM.1 g.1 g.2
  have hinj : Function.Injective fun g : G => (σ g, h g) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    apply Subtype.ext
    ext x
    have ha := hgh a x
    have hb := hgh b x
    rw [hab.1, hab.2, ← hb] at ha
    exact congrArg Fin.val (e.injective ha)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_perm, Nat.card_fun, Nat.card_perm, Nat.card_fin,
    Nat.card_fin] at this

/-- The counting core: for `b ≥ 2`, `r ≥ 2` and `L + 2 ≥ r + c`,
`b^{c r} · r! < b^{r (1 + L)}`. Indeed `r! < r^r ≤ (b^{r-1})^r`, and
`c r + (r - 1) r ≤ r (1 + L)`. -/
theorem cam_count_core {b r c L : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (hL : r + c ≤ L + 2) :
    b ^ (c * r) * r.factorial < b ^ (r * (1 + L)) := by
  have h1 : r.factorial < r ^ r := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.factorial_succ, pow_succ', ]
    refine Nat.mul_lt_mul_of_pos_left ?_ (by omega)
    exact (Nat.factorial_le_pow s).trans_lt (Nat.pow_lt_pow_left (by omega) (by omega))
  have h2 : r ≤ b ^ (r - 1) := by
    have : r - 1 < 2 ^ (r - 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ (r - 1) ≤ b ^ (r - 1) := Nat.pow_le_pow_left hb _
    omega
  have h4 : r ^ r ≤ b ^ ((r - 1) * r) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h2 _
  have h5 : c * r + (r - 1) * r ≤ r * (1 + L) := by
    rw [← add_mul, mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  calc b ^ (c * r) * r.factorial < b ^ (c * r) * b ^ ((r - 1) * r) :=
        Nat.mul_lt_mul_of_pos_left (h1.trans_le h4) (Nat.pow_pos (by omega))
    _ = b ^ (c * r + (r - 1) * r) := (pow_add _ _ _).symm
    _ ≤ b ^ (r * (1 + L)) := Nat.pow_le_pow_right (by omega) h5

/-- `⌊log₂ (b^r)⌋ ≥ r ⌊log₂ b⌋`. -/
theorem cam_log_pow_ge (b r : ℕ) (hb : 1 ≤ b) : r * Nat.log 2 b ≤ Nat.log 2 (b ^ r) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  rw [pow_mul']
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) r

/-- The binomials `binom(m, k) ≥ 2` with `m ≤ 4`. -/
theorem cam_small_choose (hm : m ≤ 4) (hb : 2 ≤ m.choose k) :
    (m = 2 ∧ m.choose k = 2) ∨ (m = 3 ∧ m.choose k = 3) ∨ (m = 4 ∧ m.choose k = 4) ∨
      (m = 4 ∧ m.choose k = 6) := by
  have hk : k ≤ m := by
    by_contra hk
    rw [Nat.choose_eq_zero_of_lt (by omega)] at hb
    omega
  interval_cases m <;> interval_cases k <;> revert hb <;> decide

/-- **`m ≥ 5` above the order threshold.** -/
theorem cam_five_le {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hM : MarotiStructure G e)
    (hn : 25 ≤ n) (hbig : n ^ (1 + Nat.log 2 n) ≤ Nat.card G) : 5 ≤ m := by
  by_contra hm
  have hcard := (hbig.trans (cam_card_le hM))
  have hne := cam_n_eq e
  set b := m.choose k with hbdef
  -- the per-case constants: `m! ≤ b^c` and `⌊log₂ b⌋ ≥ d`, with `d r + 2 ≥ r + c`
  have hb2 : 2 ≤ b := by
    by_contra hb
    have : b ^ r ≤ 1 := pow_le_one₀ (Nat.zero_le _) (by omega)
    omega
  have key := cam_small_choose (by omega) hb2
  -- the per-case constants: `m! ≤ b^c` and `⌊log₂ b⌋ ≥ d`, with `r + c ≤ d r + 2`
  obtain ⟨c, d, hfac, hlogb, hcd⟩ : ∃ c d : ℕ, m.factorial ≤ b ^ c ∧ d ≤ Nat.log 2 b ∧
      (∀ r, 1 ≤ r → r + c ≤ d * r + 2) := by
    rcases key with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;> rw [hbdef, hb]
    · exact ⟨1, 1, by decide, by decide, fun r _ => by omega⟩
    · exact ⟨2, 1, by decide, by decide, fun r _ => by omega⟩
    · exact ⟨3, 2, by decide, by decide, fun r _ => by omega⟩
    · exact ⟨2, 2, by decide, by decide, fun r _ => by omega⟩
  have hr2 : 2 ≤ r := by
    by_contra hr
    have hb6 : b ≤ 6 := by rcases key with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega
    interval_cases r
    · simp at hne; omega
    · simp at hne; omega
  have hL : r + c ≤ Nat.log 2 n + 2 := by
    have := cam_log_pow_ge b r (by omega)
    rw [← hne] at this
    have := hcd r (by omega)
    have : d * r ≤ r * Nat.log 2 b := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hlogb
    omega
  have hlt := cam_count_core hb2 hr2 hL
  have hfr : m.factorial ^ r ≤ b ^ (c * r) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hfac r
  have : r.factorial * m.factorial ^ r < n ^ (1 + Nat.log 2 n) :=
    calc r.factorial * m.factorial ^ r ≤ b ^ (c * r) * r.factorial := by
          rw [mul_comm]; exact Nat.mul_le_mul_right _ hfr
      _ < b ^ (r * (1 + Nat.log 2 n)) := hlt
      _ = n ^ (1 + Nat.log 2 n) := by rw [pow_mul, ← hne]
  omega

end GI.Impl
