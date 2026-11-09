module

public import Workspace.Degree.AlmostSimpleBound
public import Workspace.Degree.RadicalFreeCount

/-!
# The numbers in the hard case

Let `Q` be radical-free and in `Γ̂_D`, with simple factors `T_1, …, T_b` of its socle. Let `f_i` be
the least index of a proper subgroup of `T_i`. Assume `∏ f_i ≤ W²`, and that some prime `r ∈ {2, 3}`
has `r`-part at most `W^23` in a number divisible by `|Q|`. Then `D³ |Q|³ ≤ W^(807 (⌊log₂ D⌋ + 1))`
(`GI.Degree.cube_card_le`).

Each factor has `log |T_i| ≤ (8 + log₂ D) log f_i + 5 log D · v_r(|T_i|)`
(`GI.Degree.log_factor_le`). If `T_i` is not alternating, this is `GI.Degree.log_card_simple_le`
for the action on the cosets of a subgroup of index `f_i`. If `T_i = Alt(m)`, then `m ≤ D` and
`m ≤ 5 v_r(m!/2)`.
-/

@[expose] public section

namespace GI.Degree

open GI.RadicalSocle GI.SocleOuter GI.RadicalFreeOrder

theorem le_factorization_factorial (m r : ℕ) (hr : r.Prime) :
    m / r ≤ m.factorial.factorization r := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [Nat.factorization_def _ hr, padicValNat_factorial (b := Nat.log r m + 2) (by omega)]
  have hmem : 1 ∈ Finset.Ico 1 (Nat.log r m + 2) := by
    rw [Finset.mem_Ico]
    omega
  have := Finset.single_le_sum (f := fun i => m / r ^ i) (fun _ _ => Nat.zero_le _) hmem
  simpa using this

/-- `m ≤ 5 v_r(m!/2)` for `r ∈ {2, 3}`. -/
theorem le_five_mul_factorization {m t r : ℕ} (hm : 5 ≤ m) (ht : 2 * t = m.factorial)
    (hr : r = 2 ∨ r = 3) : m ≤ 5 * t.factorization r := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact Nat.factorial_ne_zero m ht.symm
  have hmul : m.factorial.factorization r = (2).factorization r + t.factorization r := by
    rw [← ht, Nat.factorization_mul (by norm_num) ht0]
    rfl
  rcases hr with rfl | rfl
  · have h1 := le_factorization_factorial m 2 Nat.prime_two
    have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
    omega
  · have h1 := le_factorization_factorial m 3 Nat.prime_three
    have h2 : (2 : ℕ).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    omega

variable {T : Type} [Group T] [Finite T] [IsSimpleGroup T]

/-- A simple group acts faithfully on the cosets of a proper subgroup. -/
theorem injective_toPermHom {M : Subgroup T} (hM : M ≠ ⊤) :
    Function.Injective (MulAction.toPermHom T (T ⧸ M)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hN : (MulAction.toPermHom T (T ⧸ M)).ker.Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := (MulAction.toPermHom T (T ⧸ M)).ker) with
    h | h
  · exact h
  · exfalso
    apply hM
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (MulAction.toPermHom T (T ⧸ M)).ker := h ▸ Subgroup.mem_top x
    have h1 := congrArg (fun σ : Equiv.Perm (T ⧸ M) => σ ((1 : T) : T ⧸ M)) (MonoidHom.mem_ker.1 hx)
    have h2 : ((x * 1 : T) : T ⧸ M) = ((1 : T) : T ⧸ M) := h1
    have h3 := QuotientGroup.eq.1 h2
    simpa using M.inv_mem h3

/-- The bound for one simple factor. -/
theorem log_factor_le {D r : ℕ} (hD : 6 ≤ D) (hr : r = 2 ∨ r = 3) (hT : GammaHat D T)
    {M : Subgroup T} (hM : M ≠ ⊤) :
    Real.log (Nat.card T) ≤ (8 + Real.log D / Real.log 2) * Real.log M.index +
      5 * Real.log D * (Nat.card T).factorization r := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hi0 : 0 ≤ Real.log M.index := Real.log_natCast_nonneg _
  have hc : 0 ≤ 8 + Real.log D / Real.log 2 := by positivity
  by_cases hnot : ∀ m, 5 ≤ m → IsEmpty (T ≃* alternatingGroup (Fin m))
  · have h := log_card_simple_le hnot (gammaHat_simple_iff.1 hT) _ (injective_toPermHom hM)
    have h2 : (0 : ℝ) ≤ 5 * Real.log D * (Nat.card T).factorization r := by positivity
    have h3 : Nat.card (T ⧸ M) = M.index := rfl
    rw [h3] at h
    linarith
  · push Not at hnot
    obtain ⟨m, hm, ⟨e⟩⟩ := hnot
    have hmD : m ≤ D := hT.le_of_alternating_section hm ⊤
      (e.toMonoidHom.comp (⊤ : Subgroup T).subtype) (fun y => ⟨⟨e.symm y, trivial⟩, by simp⟩)
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hcard : 2 * Nat.card T = m.factorial := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, two_mul_card_alternatingGroup,
        Fintype.card_perm, Fintype.card_fin]
    have h5 := le_five_mul_factorization hm hcard hr
    have hle : (Nat.card T : ℝ) ≤ m.factorial := by
      rw [← hcard]
      push_cast
      have : (0 : ℝ) ≤ Nat.card T := by positivity
      linarith
    have h1 : Real.log (Nat.card T) ≤ Real.log m.factorial :=
      Real.log_le_log (by exact_mod_cast Nat.card_pos) hle
    have h2 := log_factorial_le m
    have hlogm : Real.log m ≤ Real.log D :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hmD)
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have h3 : (m : ℝ) * Real.log m ≤ m * Real.log D := mul_le_mul_of_nonneg_left hlogm hm0
    have h4 : (m : ℝ) ≤ 5 * (Nat.card T).factorization r := by exact_mod_cast h5
    have h6 : (m : ℝ) * Real.log D ≤ 5 * (Nat.card T).factorization r * Real.log D :=
      mul_le_mul_of_nonneg_right h4 hL0
    have h7 : 0 ≤ (8 + Real.log D / Real.log 2) * Real.log M.index := by positivity
    linarith

section Count

variable {Q : Type} [Group Q] [Finite Q] [Fintype (Factors Q)]

theorem gammaHat_factor {D : ℕ} (hQ : GammaHat D Q) (N : Factors Q) : GammaHat D N.val :=
  hQ.of_injective ((socle Q).subtype.comp N.val.subtype)
    ((socle Q).subtype_injective.comp N.val.subtype_injective)

/-- Pure arithmetic for the end of the hard case. -/
theorem final_arith {x l lam y I V b S LQ L : ℝ} (hl : 0 < l) (hy1 : 1 ≤ y) (hlam : lam = y * l)
    (hx : l ≤ x) (hS : S ≤ (8 + y) * I + 5 * lam * V) (hI : I ≤ 2 * x) (hV0 : 0 ≤ V)
    (hV : V * l ≤ 23 * x) (hb : b * l ≤ 2 * x) (hLQ : LQ ≤ b * lam + 2 * S) (hyL : y ≤ L) :
    3 * lam + 3 * LQ ≤ 807 * L * x := by
  have hx0 : 0 < x := by linarith
  have h1 : (8 + y) * I ≤ (8 + y) * (2 * x) := mul_le_mul_of_nonneg_left hI (by linarith)
  have h2 : 5 * lam * V = 5 * y * (V * l) := by rw [hlam]; ring
  have hy0 : 0 ≤ 5 * y := by linarith
  have h3 : 5 * y * (V * l) ≤ 5 * y * (23 * x) := mul_le_mul_of_nonneg_left hV hy0
  have h4 : b * lam = y * (b * l) := by rw [hlam]; ring
  have h5 : y * (b * l) ≤ y * (2 * x) := mul_le_mul_of_nonneg_left hb (by linarith)
  have h6 : lam ≤ y * x := by rw [hlam]; exact mul_le_mul_of_nonneg_left hx (by linarith)
  have h7 : 8 * x ≤ 8 * (y * x) := by nlinarith
  have h8 : y * x ≤ L * x := mul_le_mul_of_nonneg_right hyL hx0.le
  nlinarith

/-- **The bound for `Q`.** -/
theorem cube_card_le (rf : ∀ N : Subgroup Q, N.Normal → IsSolvable N → N = ⊥) {D : ℕ} (hD : 6 ≤ D)
    (hQ : GammaHat D Q) {W n r : ℕ} (hW : 2 ≤ W) (hr : r = 2 ∨ r = 3)
    (M : ∀ N : Factors Q, Subgroup N.val) (hM : ∀ N, M N ≠ ⊤)
    (hprod : ∏ N, (M N).index ≤ W ^ 2) (hdvd : Nat.card Q ∣ n) (hn : n ≠ 0)
    (hS : (r ^ n.factorization r) ^ 3 ≤ W ^ 69) :
    D ^ 3 * Nat.card Q ^ 3 ≤ W ^ (807 * (Nat.log 2 D + 1)) := by
  classical
  have rfE := normal_subgroup_radicalFree rf (socle Q)
  have hsimple : ∀ N : Factors Q, IsSimpleGroup N.val := socle_intrinsic_factor_simple
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrp : r.Prime := by
    rcases hr with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  set x := Real.log W with hxdef
  set lam := Real.log D with hlamdef
  set y := lam / Real.log 2 with hydef
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hx : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (by exact_mod_cast hW)
  have hlam2 : Real.log 2 ≤ lam := Real.log_le_log (by norm_num) (by
    have : (6 : ℝ) ≤ D := by exact_mod_cast hD
    linarith)
  have hy1 : 1 ≤ y := by
    rw [hydef, le_div_iff₀ hl]
    linarith
  have hlamy : lam = y * Real.log 2 := by
    rw [hydef]
    field_simp
  have hyL : y ≤ ((Nat.log 2 D + 1 : ℕ) : ℝ) := by
    rw [hydef, div_le_iff₀ hl]
    have h1 : D < 2 ^ (Nat.log 2 D + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
    have h2 : (D : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 D + 1) := by exact_mod_cast h1.le
    calc lam ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 D + 1)) := Real.log_le_log hDpos h2
      _ = _ := by rw [Real.log_pow]
  -- the factors
  set t : Factors Q → ℕ := fun N => Nat.card N.val with ht
  set idx : Factors Q → ℕ := fun N => (M N).index with hidx
  set v : Factors Q → ℕ := fun N => (t N).factorization r with hv
  have htpos : ∀ N, t N ≠ 0 := fun N => Nat.card_pos.ne'
  have hidx2 : ∀ N, 2 ≤ idx N := by
    intro N
    have h0 : idx N ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : idx N ≠ 1 := fun h => hM N (Subgroup.index_eq_one.1 h)
    omega
  have hfac : ∀ N, Real.log (t N) ≤ (8 + y) * Real.log (idx N) + 5 * lam * (v N) := by
    intro N
    haveI := hsimple N
    exact log_factor_le hD hr (gammaHat_factor hQ N) (hM N)
  have hsum : ∑ N, Real.log (t N) ≤
      (8 + y) * ∑ N, Real.log (idx N) + 5 * lam * ((∑ N, v N : ℕ) : ℝ) := by
    calc _ ≤ ∑ N, ((8 + y) * Real.log (idx N) + 5 * lam * (v N)) :=
          Finset.sum_le_sum fun N _ => hfac N
      _ = _ := by
          push_cast
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hI : ∑ N, Real.log (idx N) ≤ 2 * x := by
    rw [← Real.log_prod (fun N _ => by
      have := hidx2 N
      positivity)]
    have h1 : ((∏ N, idx N : ℕ) : ℝ) ≤ (W : ℝ) ^ 2 := by exact_mod_cast hprod
    have h2 := Real.log_le_log (by
      have : 0 < ∏ N, idx N := Finset.prod_pos fun N _ => by
        have := hidx2 N
        omega
      exact_mod_cast this) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    simpa using h2
  have hb : (Nat.card (Factors Q) : ℝ) * Real.log 2 ≤ 2 * x := by
    refine le_trans ?_ hI
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun N _ => ?_
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hidx2 N)
  -- the valuation
  have hcardsoc : Nat.card (socle Q) = ∏ N, t N := by
    rw [← Nat.card_congr (intrinsicProductEquiv rfE socle_idempotent).toEquiv, Nat.card_pi]
  have hdvd' : ∏ N, t N ∣ n := by
    rw [← hcardsoc]
    exact (Subgroup.card_subgroup_dvd_card _).trans hdvd
  have hprodt : ∏ N, t N ≠ 0 := Finset.prod_ne_zero_iff.2 fun N _ => htpos N
  have hsumv : ∑ N, v N = (∏ N, t N).factorization r := by
    rw [Nat.factorization_prod fun N _ => htpos N]
    simp [Finsupp.finset_sum_apply, hv]
  have hVle : ∑ N, v N ≤ n.factorization r := by
    rw [hsumv]
    exact (Nat.factorization_le_iff_dvd hprodt hn).2 hdvd' r
  have hV : ((∑ N, v N : ℕ) : ℝ) * Real.log 2 ≤ 23 * x := by
    have h1 : (((r : ℝ) ^ n.factorization r) ^ 3) ≤ (W : ℝ) ^ 69 := by exact_mod_cast hS
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hrp.pos
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    have hlogr : Real.log 2 ≤ Real.log r :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hrp.two_le)
    have h3 : ((∑ N, v N : ℕ) : ℝ) ≤ n.factorization r := by exact_mod_cast hVle
    have h4 : ((∑ N, v N : ℕ) : ℝ) * Real.log 2 ≤ n.factorization r * Real.log r :=
      mul_le_mul h3 hlogr hl.le (by positivity)
    linarith
  -- the order of `Q`
  have hcardQ : Nat.card Q ≤ D ^ Nat.card (Factors Q) * ∏ N, t N ^ 2 := by
    refine (card_le_of_radicalFree rf hD hQ).trans (Nat.mul_le_mul_left _ ?_)
    refine Finset.prod_le_prod fun N _ => ?_
    haveI := hsimple N
    exact autBound (socle_intrinsic_factor_nonabelian rf N)
  have hLQ : Real.log (Nat.card Q) ≤
      (Nat.card (Factors Q) : ℝ) * lam + 2 * ∑ N, Real.log (t N) := by
    have h1 : (Nat.card Q : ℝ) ≤ (D : ℝ) ^ Nat.card (Factors Q) * ∏ N, (t N : ℝ) ^ 2 := by
      exact_mod_cast hcardQ
    have htR : ∀ N ∈ (Finset.univ : Finset (Factors Q)), ((t N : ℝ)) ^ 2 ≠ 0 := fun N _ => by
      have : (t N : ℝ) ≠ 0 := by exact_mod_cast htpos N
      positivity
    have h2 := Real.log_le_log (by exact_mod_cast Nat.card_pos) h1
    rw [Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.2 htR), Real.log_pow,
      Real.log_prod htR] at h2
    simp only [Real.log_pow] at h2
    rw [← Finset.mul_sum] at h2
    exact_mod_cast h2
  have hfinal := final_arith hl hy1 hlamy hx hsum hI (by positivity) hV hb hLQ hyL
  have hgoal : ((D ^ 3 * Nat.card Q ^ 3 : ℕ) : ℝ) ≤ ((W ^ (807 * (Nat.log 2 D + 1)) : ℕ) : ℝ) := by
    have hQpos : (0 : ℝ) < Nat.card Q := by exact_mod_cast Nat.card_pos
    push_cast
    refine (Real.log_le_log_iff (by positivity) (by positivity)).1 ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast at hfinal ⊢
    linarith
  exact_mod_cast hgoal

end Count

end GI.Degree
