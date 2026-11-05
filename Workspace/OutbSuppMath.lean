module

public import Workspace.RadicalFreeOrder
public import Workspace.Impl.TermRepsMath
public import Workspace.CitedChecks.AlgoTotality

@[expose] public section

/-!
# Brute-force Frattini descent modulo `R` (the mathematics)

Given permutation groups `R ≤ E_H ≤ K ≤ Sym(n)` with `R, E_H ⊴ K` and `K / E_H` solvable, together
with a list `reps` of right coset representatives of `R` in `E_H` (`∀ x ∈ E_H, TmRpCov R reps x`),
we construct a subgroup `R'` with `R ≤ R' ≤ K`, `R' / R` solvable, and `R' ⊔ E_H = K` by Frattini
descent modulo `R`:

1. Maintain `S` with `R ≤ S ≤ K` and `S ⊔ E_H = K`, and let `M = S ⊓ E_H` (so `R ≤ M ≤ E_H`).
2. Test nilpotency of `M / R` by checking each prime `p ≤ n` dividing `[M : R] = |M| / |R|`:
   - Build a Sylow `p`-subgroup `P / R` of `M / R` (`OutbSylowMod p R M P`) by brute force over
     `reps`: starting from `P = R`, repeatedly scan `reps` and adjoin `e ∈ reps` whenever
     `e ∈ M`, `e ∉ P`, and `|⟨P, e⟩|` divides `p^(v_p([M : R])) |R|` (`outbSylStep`,
     `outbSylPass`). By Sylow's theorem in `M / R`, as long as `P / R` is not yet a Sylow
     `p`-subgroup of `M / R`, such a representative `e ∈ reps` exists (`outb_exists_rep_grow`), so
     at most `n² + 1` passes over `reps` produce `OutbSylowMod p R M P` (`outb_syl_done`).
   - Test whether `M` normalizes `P` (`OutbNormIn M P`, equivalent to normality of `P / R` in
     `M / R` by `outb_sylow_normal_iff`).
3. If a nonnormal Sylow subgroup `P / R` of `M / R` is found, correct each generator `s` of `S` by
   scanning `reps` for `e ∈ reps` with `e ∈ M` and `(e s) P (e s)⁻¹ ≤ P` (`outbFixStep`,
   `outbFixFold`). Such a representative `e ∈ reps` exists by Sylow's conjugacy theorem in `M / R`
   (`outb_exists_rep_conj`). Replacing `S` by `R ⊔ ⟨t_s⟩` preserves `R ≤ S₁ ≤ S` and
   `S₁ ⊔ E_H = K` while halving `|S ⊓ E_H|` (`outb_corr_step`).
4. When every Sylow subgroup of `M / R` is normal, `M / R` is nilpotent (`outb_sieve_end`), and
   since `K / E_H` is solvable, `S / R` is solvable (`outb_solvable_quotient`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n : ℕ}

/-! ### Quotients modulo `R` and Sylow subgroups of `M / R` -/

/-- `K` normalizes `P`. -/
def OutbNormIn (K P : Subgroup (Perm (Fin n))) : Prop :=
  ∀ g ∈ K, ∀ x ∈ P, g * x * g⁻¹ ∈ P

/-- `P` is the full preimage in `M` of a Sylow `p`-subgroup of `M / R`: `R ≤ P ≤ M` and
`|P| = p^(v_p(|M| / |R|)) |R|`. -/
def OutbSylowMod (p : ℕ) (R M P : Subgroup (Perm (Fin n))) : Prop :=
  R ≤ P ∧ P ≤ M ∧ Nat.card P = p ^ (Nat.card M / Nat.card R).factorization p * Nat.card R

/-- The image of `P` in `M / R`. -/
def outbQuotSub (R M P : Subgroup (Perm (Fin n))) [(R.subgroupOf M).Normal] :
    Subgroup (M ⧸ R.subgroupOf M) :=
  (P.subgroupOf M).map (QuotientGroup.mk' (R.subgroupOf M))

theorem outb_card_subgroupOf {K P : Subgroup (Perm (Fin n))} (h : P ≤ K) :
    Nat.card (P.subgroupOf K) = Nat.card P :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem outb_card_quotient_mul {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M) :
    Nat.card (M ⧸ R.subgroupOf M) * Nat.card R = Nat.card M := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf M)
  rw [outb_card_subgroupOf hRM] at h1
  exact h1.symm

theorem outb_card_quotient {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M) :
    Nat.card (M ⧸ R.subgroupOf M) = Nat.card M / Nat.card R := by
  rw [← outb_card_quotient_mul hRM, Nat.mul_div_cancel _ Nat.card_pos]

theorem outb_mem_quotSub_iff {R M P : Subgroup (Perm (Fin n))} [(R.subgroupOf M).Normal]
    (hRP : R ≤ P) (_hPM : P ≤ M) (x : M) :
    QuotientGroup.mk' (R.subgroupOf M) x ∈ outbQuotSub R M P ↔ (x : Perm (Fin n)) ∈ P := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h1 : y⁻¹ * x ∈ R.subgroupOf M := by
      rwa [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply]
    have h2 : (y : Perm (Fin n))⁻¹ * (x : Perm (Fin n)) ∈ P := hRP h1
    simpa using P.mul_mem hy h2
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem outb_card_quotSub_mul {R M P : Subgroup (Perm (Fin n))} [(R.subgroupOf M).Normal]
    (hRP : R ≤ P) (hPM : P ≤ M) :
    Nat.card (outbQuotSub R M P) * Nat.card R = Nat.card P := by
  let f : P →* M ⧸ R.subgroupOf M :=
    (QuotientGroup.mk' (R.subgroupOf M)).comp (Subgroup.inclusion hPM)
  have hrange : f.range = outbQuotSub R M P := by
    ext z
    simp only [MonoidHom.mem_range, outbQuotSub, Subgroup.mem_map, Subgroup.mem_subgroupOf, f,
      MonoidHom.comp_apply]
    exact ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨⟨x, hPM hx⟩, hx, h⟩,
      fun ⟨⟨x, _⟩, hxP, h⟩ => ⟨⟨x, hxP⟩, h⟩⟩
  have hker : f.ker = R.subgroupOf P := by
    ext ⟨x, hx⟩
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (P ⧸ f.ker) = Nat.card (outbQuotSub R M P) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [h2, hker, outb_card_subgroupOf hRP] at h1
  exact h1.symm

theorem outb_card_quotSub {R M P : Subgroup (Perm (Fin n))} [(R.subgroupOf M).Normal]
    (hRP : R ≤ P) (hPM : P ≤ M) :
    Nat.card (outbQuotSub R M P) = Nat.card P / Nat.card R := by
  rw [← outb_card_quotSub_mul hRP hPM, Nat.mul_div_cancel _ Nat.card_pos]

theorem outbSylowMod_iff_card_quotSub {p : ℕ} {R M P : Subgroup (Perm (Fin n))}
    [(R.subgroupOf M).Normal] (hRP : R ≤ P) (hPM : P ≤ M) :
    OutbSylowMod p R M P ↔
      Nat.card (outbQuotSub R M P) = p ^ (Nat.card (M ⧸ R.subgroupOf M)).factorization p := by
  have hRM : R ≤ M := hRP.trans hPM
  unfold OutbSylowMod
  rw [← outb_card_quotSub_mul hRP hPM, outb_card_quotient hRM]
  exact ⟨fun h => Nat.mul_right_cancel Nat.card_pos h.2.2,
    fun h => ⟨hRP, hPM, by rw [h]⟩⟩

/-- The Sylow `p`-subgroup of `M / R` associated to `OutbSylowMod p R M P`. -/
noncomputable def outbSylow {p : ℕ} [Fact p.Prime] {R M P : Subgroup (Perm (Fin n))}
    [(R.subgroupOf M).Normal] (h : OutbSylowMod p R M P) : Sylow p (M ⧸ R.subgroupOf M) :=
  Sylow.ofCard (outbQuotSub R M P) ((outbSylowMod_iff_card_quotSub h.1 h.2.1).mp h)

/-- `outbSylow h` is normal in `M / R` if and only if `M` normalizes `P`. -/
theorem outb_sylow_normal_iff {p : ℕ} [Fact p.Prime] {R M P : Subgroup (Perm (Fin n))}
    [(R.subgroupOf M).Normal] (h : OutbSylowMod p R M P) :
    ((outbSylow h : Sylow p (M ⧸ R.subgroupOf M)) : Subgroup (M ⧸ R.subgroupOf M)).Normal ↔
      OutbNormIn M P := by
  have hRP := h.1
  have hPM := h.2.1
  change (outbQuotSub R M P).Normal ↔ OutbNormIn M P
  constructor
  · intro hN g hg x hx
    have hx' : QuotientGroup.mk' (R.subgroupOf M) ⟨x, hPM hx⟩ ∈ outbQuotSub R M P :=
      (outb_mem_quotSub_iff hRP hPM ⟨x, hPM hx⟩).mpr hx
    have hconj := hN.conj_mem _ hx' (QuotientGroup.mk' (R.subgroupOf M) ⟨g, hg⟩)
    rw [← map_inv, ← map_mul, ← map_mul, outb_mem_quotSub_iff hRP hPM] at hconj
    exact hconj
  · intro hN
    refine ⟨fun z hz q => ?_⟩
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) q
    obtain ⟨⟨x, hxM⟩, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) z
    rw [← map_inv, ← map_mul, ← map_mul, outb_mem_quotSub_iff hRP hPM]
    exact hN g hg x ((outb_mem_quotSub_iff hRP hPM ⟨x, hxM⟩).mp hz)

/-! ### The prime-part helper `outbPPart` -/

/-- Bounds `v_p(c) ≤ n²` for `c = |M| / |R|`. -/
theorem outb_factorization_le_sq {R M : Subgroup (Perm (Fin n))} (p : ℕ) :
    (Nat.card M / Nat.card R).factorization p ≤ n ^ 2 := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp
  · set c := Nat.card M / Nat.card R
    set v := c.factorization p
    have hcM : c ≤ Nat.card M := Nat.div_le_self _ _
    have hM2 : Nat.card M < 2 ^ (n ^ 2 + 1) := GI.CitedChecks.card_lt_two_pow M
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · simp [v, hc0]
    · have hdvd : p ^ v ∣ c := Nat.ordProj_dvd c p
      have hpv : p ^ v ≤ c := Nat.le_of_dvd hc0 hdvd
      have h2v : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp v
      have hlt : 2 ^ v < 2 ^ (n ^ 2 + 1) := lt_of_le_of_lt (h2v.trans hpv) (lt_of_le_of_lt hcM hM2)
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
      omega

/-- Arithmetic step for `outbPPartF`: for `a ≤ v = (|M| / |R|).factorization p` and
`B = p ^ a * |R|`, we have `p ∣ (|M| / B)` iff `a < v`. -/
theorem outb_ppart_div_Step {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M)
    {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : a ≤ (Nat.card M / Nat.card R).factorization p) :
    let v := (Nat.card M / Nat.card R).factorization p
    let B := p ^ a * Nat.card R
    B ≤ Nat.card M ∧
      (p ∣ (Nat.card M / B) ↔ a < v) := by
  intro v B
  have hmul := outb_card_quotient_mul hRM
  have hquot := outb_card_quotient hRM
  have hcM : (Nat.card M / Nat.card R) * Nat.card R = Nat.card M := by
    rw [← hquot, hmul]
  have hc0 : Nat.card M / Nat.card R ≠ 0 := by
    rw [← hquot]
    exact Nat.card_pos.ne'
  have hdvd_v : p ^ v ∣ Nat.card M / Nat.card R := Nat.ordProj_dvd _ p
  have hdvd_a : p ^ a ∣ Nat.card M / Nat.card R := (Nat.pow_dvd_pow p ha).trans hdvd_v
  obtain ⟨q, hq⟩ := hdvd_a
  have hMB : Nat.card M = q * B := by
    dsimp [B]
    rw [← hcM, hq]
    ring
  have hB0 : 0 < B := Nat.mul_pos (pow_pos hp.pos a) Nat.card_pos
  have hdiv : Nat.card M / B = q := by rw [hMB, Nat.mul_div_cancel _ hB0]
  have hq0 : 0 < q := by
    by_contra h
    have h0 : q = 0 := by omega
    rw [h0, mul_zero] at hq
    exact hc0 hq
  refine ⟨by rw [hMB]; exact Nat.le_mul_of_pos_left _ hq0, ?_⟩
  rw [hdiv]
  constructor
  · rintro ⟨k, rfl⟩
    by_contra hge
    have hav : a ≤ v := ha
    have heq : a = v := by omega
    rw [heq] at hq
    have hcv : (Nat.card M / Nat.card R) / p ^ v = p * k := by
      rw [hq, Nat.mul_comm, Nat.mul_div_cancel _ (pow_pos hp.pos v)]
    exact Nat.not_dvd_ordCompl hp hc0 ⟨k, hcv⟩
  · intro hlt
    have ha1 : a + 1 ≤ v := by omega
    have hdvd1 : p ^ (a + 1) ∣ Nat.card M / Nat.card R := (Nat.pow_dvd_pow p ha1).trans hdvd_v
    obtain ⟨k, hk⟩ := hdvd1
    refine ⟨k, ?_⟩
    have : p ^ a * q = p ^ a * (p * k) := by
      calc p ^ a * q = Nat.card M / Nat.card R := hq.symm
        _ = p ^ (a + 1) * k := hk
        _ = p ^ a * (p * k) := by rw [pow_succ]; ring
    exact Nat.mul_left_cancel (pow_pos hp.pos a) this

/-! ### Brute-force Sylow construction in `M / R` -/

theorem outb_gens_append (as bs : List (Perm (Fin n))) :
    gens (as ++ bs) = gens as ⊔ gens bs := by
  unfold gens
  rw [← Subgroup.closure_union]
  congr 1
  ext g
  simp

theorem outb_gens_singleton (e : Perm (Fin n)) :
    gens [e] = Subgroup.closure {e} := by
  unfold gens
  simp

/-- If `P / R` is a `p`-subgroup of `M / R` of order `p^b` with `b < v_p(|M| / |R|)`, then some
representative `e ∈ reps` lies in `M \ P` and keeps `⟨P, e⟩ / R` inside a Sylow `p`-subgroup of
`M / R` (so `|⟨P, e⟩|` divides `p^(v_p(|M| / |R|)) |R|`). -/
theorem outb_exists_rep_grow {p : ℕ} (hp : p.Prime) {R M E_H P : Subgroup (Perm (Fin n))}
    [(R.subgroupOf M).Normal] (hME : M ≤ E_H) {reps : List (Perm (Fin n))}
    (hcov : ∀ x ∈ E_H, TmRpCov R reps x) (hRP : R ≤ P) (hPM : P ≤ M) {b : ℕ}
    (hc : Nat.card P = p ^ b * Nat.card R)
    (hb : b < (Nat.card M / Nat.card R).factorization p) :
    ∃ e ∈ reps, e ∈ M ∧ e ∉ P ∧
      Nat.card (P ⊔ Subgroup.closure {e} : Subgroup (Perm (Fin n))) ∣
        p ^ (Nat.card M / Nat.card R).factorization p * Nat.card R := by
  have : Fact p.Prime := ⟨hp⟩
  have hRM : R ≤ M := hRP.trans hPM
  set Pbar := outbQuotSub R M P
  have hcPbar : Nat.card Pbar = p ^ b := by
    rw [outb_card_quotSub hRP hPM, hc, Nat.mul_div_cancel _ Nat.card_pos]
  have hpg : IsPGroup p Pbar := IsPGroup.of_card hcPbar
  obtain ⟨Q, hPQ⟩ := hpg.exists_le_sylow
  have hcQ : Nat.card Q = p ^ (Nat.card M / Nat.card R).factorization p := by
    rw [Q.card_eq_multiplicity, outb_card_quotient hRM]
  have hlt_card : Nat.card Pbar < Nat.card Q := by
    rw [hcPbar, hcQ]
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mpr hb
  have hlt : Pbar < (Q : Subgroup (M ⧸ R.subgroupOf M)) :=
    lt_of_le_of_ne hPQ fun heq => Nat.ne_of_lt hlt_card (by rw [heq])
  obtain ⟨xbar, hxQ, hxPbar⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨⟨x, hxM⟩, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) xbar
  obtain ⟨e, he_reps, hxe⟩ := hcov x (hME hxM)
  have heM : e ∈ M := by
    have h1 : (x * e⁻¹)⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (hRM hxe)) hxM
    simpa using h1
  have heP : e ∉ P := by
    intro heP
    apply hxPbar
    rw [outb_mem_quotSub_iff hRP hPM]
    have h1 : (x * e⁻¹) * e ∈ P := P.mul_mem (hRP hxe) heP
    simpa using h1
  set P' : Subgroup (Perm (Fin n)) := P ⊔ Subgroup.closure {e}
  have hRP' : R ≤ P' := hRP.trans le_sup_left
  have hP'M : P' ≤ M := sup_le hPM ((Subgroup.closure_le _).mpr (by simp [heM]))
  have hsubQ : outbQuotSub R M P' ≤ (Q : Subgroup (M ⧸ R.subgroupOf M)) := by
    rintro _ ⟨⟨y, hyM⟩, hyP', rfl⟩
    have hle : P' ≤ ((Q : Subgroup _).comap
        (QuotientGroup.mk' (R.subgroupOf M))).map M.subtype := by
      refine sup_le ?_ ((Subgroup.closure_le _).mpr ?_)
      · intro z hz
        exact ⟨⟨z, hPM hz⟩, hPQ ((outb_mem_quotSub_iff hRP hPM ⟨z, hPM hz⟩).mpr hz), rfl⟩
      · simp only [Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_map,
          Subgroup.mem_comap]
        refine ⟨⟨e, heM⟩, ?_, rfl⟩
        have hsplit : (⟨x, hxM⟩ : M) = ⟨x * e⁻¹, hRM hxe⟩ * ⟨e, heM⟩ :=
          Subtype.ext (by simp)
        have hmk1 : QuotientGroup.mk' (R.subgroupOf M) ⟨x * e⁻¹, hRM hxe⟩ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hxe
        have heq_mk : QuotientGroup.mk' (R.subgroupOf M) ⟨e, heM⟩ =
            QuotientGroup.mk' (R.subgroupOf M) ⟨x, hxM⟩ := by
          rw [hsplit, map_mul, hmk1, one_mul]
        rw [heq_mk]
        exact hxQ
    obtain ⟨⟨z, hzM⟩, hzQ, hzy⟩ := hle hyP'
    cases hzy
    exact hzQ
  have hdvd : Nat.card (outbQuotSub R M P') ∣ Nat.card Q :=
    Subgroup.card_dvd_of_le hsubQ
  rw [hcQ] at hdvd
  refine ⟨e, he_reps, heM, heP, ?_⟩
  rw [← outb_card_quotSub_mul hRP' hP'M]
  exact Nat.mul_dvd_mul_right hdvd (Nat.card R)

/-- One step of the brute-force Sylow pass over `reps`. -/
noncomputable def outbSylStep (M : Subgroup (Perm (Fin n))) (B : ℕ)
    (ps : List (Perm (Fin n))) (e : Perm (Fin n)) : List (Perm (Fin n)) := by
  classical
  exact if e ∈ M ∧ e ∉ gens ps ∧ Nat.card (gens (ps ++ [e])) ∣ B then ps ++ [e] else ps

/-- One full pass of `outbSylStep` over `reps`. -/
noncomputable def outbSylPass (M : Subgroup (Perm (Fin n))) (B : ℕ)
    (reps ps : List (Perm (Fin n))) : List (Perm (Fin n)) :=
  reps.foldl (outbSylStep M B) ps

/-- The invariant of the brute-force Sylow construction: `R ≤ ⟨ps⟩ ≤ M` has order `p^b |R|` with
`a ≤ b ≤ v` and `ps.length ≤ n² + b`. -/
def OutbSylInv (p : ℕ) (R M : Subgroup (Perm (Fin n))) (v a : ℕ)
    (ps : List (Perm (Fin n))) : Prop :=
  R ≤ gens ps ∧ gens ps ≤ M ∧ a ≤ v ∧
    ∃ b : ℕ, a ≤ b ∧ b ≤ v ∧ Nat.card (gens ps) = p ^ b * Nat.card R ∧ ps.length ≤ n ^ 2 + b

theorem outbSylInv_zero {p : ℕ} {M : Subgroup (Perm (Fin n))} {rs : List (Perm (Fin n))}
    (hrl : rs.length ≤ n ^ 2) (hRM : gens rs ≤ M) (v : ℕ) :
    OutbSylInv p (gens rs) M v 0 rs :=
  ⟨le_rfl, hRM, Nat.zero_le v, 0, le_rfl, Nat.zero_le v, by simp, by omega⟩

theorem outbSylInv_length_le {p : ℕ} {R M : Subgroup (Perm (Fin n))} {v a : ℕ}
    {ps : List (Perm (Fin n))} (hv : v ≤ n ^ 2) (h : OutbSylInv p R M v a ps) :
    ps.length ≤ 2 * n ^ 2 := by
  obtain ⟨-, -, -, b, -, hbv, -, hl⟩ := h
  omega

theorem outbSylInv_mono {p : ℕ} {R M : Subgroup (Perm (Fin n))} {v a a' : ℕ}
    {ps : List (Perm (Fin n))} (ha : a' ≤ a) (h : OutbSylInv p R M v a ps) :
    OutbSylInv p R M v a' ps := by
  obtain ⟨h1, h2, h3, b, hba, hbv, hc, hl⟩ := h
  exact ⟨h1, h2, ha.trans h3, b, ha.trans hba, hbv, hc, hl⟩

/-- When `outbSylStep` appends `e`, the exponent `b` increases by at least `1`. -/
theorem outbSylStep_taken {p : ℕ} (hp : p.Prime) {R M : Subgroup (Perm (Fin n))} {v a : ℕ}
    {ps : List (Perm (Fin n))} (h : OutbSylInv p R M v a ps) {e : Perm (Fin n)}
    (heM : e ∈ M) (heP : e ∉ gens ps)
    (hdvd : Nat.card (gens (ps ++ [e])) ∣ p ^ v * Nat.card R) :
    OutbSylInv p R M v (min (a + 1) v) (ps ++ [e]) := by
  obtain ⟨hRP, hPM, hav, b, hba, hbv, hc, hl⟩ := h
  have hge : gens (ps ++ [e]) = gens ps ⊔ Subgroup.closure {e} := by
    rw [outb_gens_append, outb_gens_singleton]
  have hRP' : R ≤ gens (ps ++ [e]) := by rw [hge]; exact hRP.trans le_sup_left
  have hP'M : gens (ps ++ [e]) ≤ M := by
    rw [hge]; exact sup_le hPM ((Subgroup.closure_le _).mpr (by simp [heM]))
  have hdvdR : Nat.card R ∣ Nat.card (gens (ps ++ [e])) := Subgroup.card_dvd_of_le hRP'
  obtain ⟨k, hk⟩ := hdvdR
  have hk_mul : k * Nat.card R = Nat.card (gens (ps ++ [e])) := by rw [hk, mul_comm]
  have hk_dvd : k ∣ p ^ v := by
    rw [← hk_mul] at hdvd
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨q, Nat.mul_right_cancel (Nat.card_pos (α := R)) ?_⟩
    rw [hq]
    ring
  obtain ⟨b', hb'v, rfl⟩ := (Nat.dvd_prime_pow hp).mp hk_dvd
  have hlt_sub : gens ps < gens (ps ++ [e]) := by
    rw [hge]
    refine lt_of_le_of_ne le_sup_left fun heq => heP ?_
    have : e ∈ gens ps ⊔ Subgroup.closure {e} :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton e))
    rwa [← heq] at this
  have hlt_card : Nat.card (gens ps) < Nat.card (gens (ps ++ [e])) := by
    have h2 := GI.CitedChecks.two_mul_card_le_of_lt hlt_sub
    have hpos : 0 < Nat.card (gens ps) := Nat.card_pos
    omega
  rw [hc, ← hk_mul] at hlt_card
  have hlt_pow : p ^ b < p ^ b' := Nat.lt_of_mul_lt_mul_right hlt_card
  have hbb' : b < b' := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt_pow
  refine ⟨hRP', hP'M, min_le_right _ _, b', ?_, hb'v, hk_mul.symm, ?_⟩
  · exact (min_le_left _ _).trans (by omega)
  · rw [List.length_append, List.length_singleton]; omega

theorem outbSylStep_inv {p : ℕ} (hp : p.Prime) {R M : Subgroup (Perm (Fin n))} {v a : ℕ}
    {ps : List (Perm (Fin n))} (h : OutbSylInv p R M v a ps) (e : Perm (Fin n)) :
    OutbSylInv p R M v a (outbSylStep M (p ^ v * Nat.card R) ps e) := by
  classical
  unfold outbSylStep
  have hav := h.2.2.1
  split_ifs with hc
  · exact outbSylInv_mono (by omega) (outbSylStep_taken hp h hc.1 hc.2.1 hc.2.2)
  · exact h

/-- Folding `outbSylStep` over a list `l` either leaves `ps` unchanged (with every element of `l`
failing the test on `ps`) or advances the exponent bound to `min (a + 1) v`. -/
theorem outbSyl_foldl_dichotomy {p : ℕ} (hp : p.Prime) {R M : Subgroup (Perm (Fin n))} {v a : ℕ}
    (l : List (Perm (Fin n))) {ps : List (Perm (Fin n))} (h : OutbSylInv p R M v a ps) :
    let B := p ^ v * Nat.card R
    (l.foldl (outbSylStep M B) ps = ps ∧
      ∀ e ∈ l, ¬ (e ∈ M ∧ e ∉ gens ps ∧ Nat.card (gens (ps ++ [e])) ∣ B)) ∨
    OutbSylInv p R M v (min (a + 1) v) (l.foldl (outbSylStep M B) ps) := by
  classical
  intro B
  induction l generalizing ps with
  | nil =>
    exact Or.inl ⟨rfl, fun _ hmem => absurd hmem List.not_mem_nil⟩
  | cons e l ih =>
    simp only [List.foldl_cons]
    unfold outbSylStep
    split_ifs with hc
    · right
      have h1 : OutbSylInv p R M v (min (a + 1) v) (ps ++ [e]) :=
        outbSylStep_taken hp h hc.1 hc.2.1 hc.2.2
      clear ih
      have hinv : ∀ (l' : List (Perm (Fin n))) (qs : List (Perm (Fin n))),
          OutbSylInv p R M v (min (a + 1) v) qs →
          OutbSylInv p R M v (min (a + 1) v) (l'.foldl (outbSylStep M B) qs) := by
        intro l'
        induction l' with
        | nil => intro qs hq; exact hq
        | cons e' l' ih' =>
          intro qs hq
          exact ih' _ (outbSylStep_inv hp hq e')
      exact hinv l (ps ++ [e]) h1
    · rcases ih h with ⟨heq, hnone⟩ | hadv
      · refine Or.inl ⟨heq, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · exact hnone x hx
      · exact Or.inr hadv

/-- One pass over `reps` advances `OutbSylInv` from `a` to `min (a + 1) v`. -/
theorem outbSylPass_inv {p : ℕ} (hp : p.Prime) {R M E_H : Subgroup (Perm (Fin n))}
    [(R.subgroupOf M).Normal] (hME : M ≤ E_H) {reps : List (Perm (Fin n))}
    (hcov : ∀ x ∈ E_H, TmRpCov R reps x) {a : ℕ} {ps : List (Perm (Fin n))}
    (h : OutbSylInv p R M ((Nat.card M / Nat.card R).factorization p) a ps) :
    let v := (Nat.card M / Nat.card R).factorization p
    OutbSylInv p R M v (min (a + 1) v)
      (outbSylPass M (p ^ v * Nat.card R) reps ps) := by
  intro v
  unfold outbSylPass
  rcases outbSyl_foldl_dichotomy hp reps h with ⟨heq, hnone⟩ | hadv
  · obtain ⟨hRP, hPM, hav, b, hba, hbv, hc, hl⟩ := h
    rcases Nat.eq_or_lt_of_le hbv with rfl | hlt
    · rw [heq]
      exact ⟨hRP, hPM, min_le_right _ _, v, min_le_right _ _, le_rfl, hc, hl⟩
    · obtain ⟨e, he_reps, heM, heP, hdvd⟩ :=
        outb_exists_rep_grow hp hME hcov hRP hPM hc hlt
      rw [← outb_gens_singleton, ← outb_gens_append] at hdvd
      exact absurd ⟨heM, heP, hdvd⟩ (hnone e he_reps)
  · exact hadv

/-- After `n² + 1` passes over `reps`, `gens ps` satisfies `OutbSylowMod p R M (gens ps)`. -/
theorem outb_syl_done {p : ℕ} {R M : Subgroup (Perm (Fin n))} {ps : List (Perm (Fin n))}
    (h : OutbSylInv p R M ((Nat.card M / Nat.card R).factorization p)
      (min (n ^ 2 + 1) ((Nat.card M / Nat.card R).factorization p)) ps) :
    OutbSylowMod p R M (gens ps) := by
  have hv : (Nat.card M / Nat.card R).factorization p ≤ n ^ 2 := outb_factorization_le_sq p
  have hmin : min (n ^ 2 + 1) ((Nat.card M / Nat.card R).factorization p) =
      (Nat.card M / Nat.card R).factorization p := Nat.min_eq_right (by omega)
  rw [hmin] at h
  obtain ⟨hRP, hPM, -, b, hvb, hbv, hc, -⟩ := h
  have hbe : b = (Nat.card M / Nat.card R).factorization p := le_antisymm hbv hvb
  subst hbe
  exact ⟨hRP, hPM, hc⟩

/-! ### Nilpotency of `M / R` and the prime sieve -/

/-- The prime divisors of `[M : R] = |M| / |R|` (for `R ≤ M`) are at most `n`. -/
theorem outb_prime_le_of_le {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ Nat.card M / Nat.card R) : q ≤ n := by
  have h1 : Nat.card M / Nat.card R ∣ Nat.card M := by
    rw [← outb_card_quotient hRM]
    exact ⟨Nat.card R, (outb_card_quotient_mul hRM).symm⟩
  have h2 : Nat.card M ∣ Nat.card (Perm (Fin n)) := Subgroup.card_subgroup_dvd_card M
  rw [Nat.card_eq_fintype_card (α := Perm (Fin n)), Fintype.card_perm, Fintype.card_fin] at h2
  exact (Nat.Prime.dvd_factorial hq).mp ((hd.trans h1).trans h2)

/-- If every prime `q ≤ n` dividing `|M| / |R|` has a Sylow subgroup `P / R` normalized by `M`,
then `M / R` is nilpotent. -/
theorem outb_nilpotent_of_normal {R M : Subgroup (Perm (Fin n))} [(R.subgroupOf M).Normal]
    (hRM : R ≤ M)
    (h : ∀ q, q.Prime → q ≤ n → q ∣ Nat.card M / Nat.card R →
      ∃ P, OutbSylowMod q R M P ∧ OutbNormIn M P) :
    Group.IsNilpotent (M ⧸ R.subgroupOf M) := by
  have htfae := (Group.isNilpotent_of_finite_tfae (G := M ⧸ R.subgroupOf M)).out 1 4
  refine htfae.mpr fun q hq Q => ?_
  by_cases hd : q ∣ Nat.card M / Nat.card R
  · obtain ⟨P, hP, hn⟩ := h q hq.out (outb_prime_le_of_le hRM hq.out hd) hd
    have hN := (outb_sylow_normal_iff hP).mpr hn
    have huniq := Sylow.unique_of_normal (outbSylow hP) hN
    rwa [huniq.eq_default Q, ← huniq.eq_default (outbSylow hP)]
  · have hc : Nat.card Q = 1 := by
      rw [Q.card_eq_multiplicity, outb_card_quotient hRM,
        Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
    rw [Subgroup.card_eq_one.mp hc]
    exact Subgroup.normal_bot

/-- `d` is prime when `d ≥ 2` divides `r` and no smaller prime divides `r`. -/
theorem outb_prime_of_sieve {d r : ℕ} (h2 : 2 ≤ d) (hd : d ∣ r)
    (hlow : ∀ q, q.Prime → q < d → ¬ q ∣ r) : d.Prime := by
  have hm := Nat.minFac_prime (show d ≠ 1 by omega)
  have hle := Nat.minFac_le (show 0 < d by omega)
  rcases Nat.lt_or_ge (Nat.minFac d) d with hlt | hge
  · exact absurd ((Nat.minFac_dvd d).trans hd) (hlow _ hm hlt)
  · have : Nat.minFac d = d := le_antisymm hle hge
    rw [← this]; exact hm

/-- One sieve step on `c = |M| / |R|`. -/
theorem outb_sieve_step_arith {c r m d : ℕ} (hc : c = r * m) (hc0 : c ≠ 0)
    (hm : ∀ q, q.Prime → q ∣ m → q < d) (hd : d.Prime) :
    d ^ c.factorization d ∣ r ∧ c = r / d ^ c.factorization d * (m * d ^ c.factorization d) ∧
      (∀ q, q.Prime → q ∣ m * d ^ c.factorization d → q < d + 1) ∧
      ¬ d ∣ r / d ^ c.factorization d := by
  set a := d ^ c.factorization d with ha
  have hcop : Nat.Coprime a m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hd).mpr fun h => by
      have := hm d hd h; omega)
  have har : a ∣ r := hcop.dvd_of_dvd_mul_right (hc ▸ Nat.ordProj_dvd c d)
  obtain ⟨r', hr'⟩ := har
  have ha0 : 0 < a := pow_pos hd.pos _
  have hrdiv : r / a = r' := by rw [hr']; exact Nat.mul_div_cancel_left _ ha0
  refine ⟨⟨r', hr'⟩, ?_, ?_, ?_⟩
  · rw [hrdiv, hc, hr']; ring
  · intro q hq hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · have := hm q hq h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hq hd).mp (hq.dvd_of_dvd_pow h); omega
  · rw [hrdiv]
    intro hdr
    have hcompl : c / a = r' * m := by
      rw [hc, hr', mul_assoc]; exact Nat.mul_div_cancel_left _ ha0
    exact Nat.not_dvd_ordCompl hd hc0 (by rw [← ha, hcompl]; exact Dvd.dvd.mul_right hdr m)

/-- The sieve invariant on `[M : R] = |M| / |R|`. -/
def OutbSieve (R M : Subgroup (Perm (Fin n))) (i r : ℕ) : Prop :=
  ∃ m, Nat.card M / Nat.card R = r * m ∧
    (∀ q, q.Prime → q ∣ m → q < i) ∧
    (∀ q, q.Prime → q < i → ¬ q ∣ r) ∧
    (∀ q, q.Prime → q < i → q ∣ Nat.card M / Nat.card R → ∃ P, OutbSylowMod q R M P ∧ OutbNormIn M P)

theorem outb_sieve_zero (R M : Subgroup (Perm (Fin n))) :
    OutbSieve R M 0 (Nat.card M / Nat.card R) :=
  ⟨1, by ring, fun q hq h => absurd (Nat.le_of_dvd one_pos h) (by have := hq.two_le; omega),
    fun _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega)⟩

theorem outb_sieve_le {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M) {i r : ℕ}
    (h : OutbSieve R M i r) : r ≤ Nat.card M := by
  obtain ⟨m, hc, -⟩ := h
  have hcpos : 0 < Nat.card M / Nat.card R := by
    rw [← outb_card_quotient hRM]; exact Nat.card_pos
  have hr : r ≤ Nat.card M / Nat.card R := Nat.le_of_dvd hcpos ⟨m, hc⟩
  exact hr.trans (Nat.div_le_self _ _)

theorem outb_sieve_small {R M : Subgroup (Perm (Fin n))} {i r : ℕ} (hi : i < 2)
    (h : OutbSieve R M i r) : OutbSieve R M (i + 1) r := by
  obtain ⟨m, hc, h1, _, _⟩ := h
  refine ⟨m, hc, fun q hq hd => by have := h1 q hq hd; omega, fun q hq hlt => ?_,
    fun q hq hlt => ?_⟩
  · have := hq.two_le; omega
  · have := hq.two_le; omega

theorem outb_sieve_skip {R M : Subgroup (Perm (Fin n))} {i r : ℕ} (hd : ¬ i ∣ r)
    (h : OutbSieve R M i r) : OutbSieve R M (i + 1) r := by
  obtain ⟨m, hc, h1, h2, h3⟩ := h
  refine ⟨m, hc, fun q hq hqd => by have := h1 q hq hqd; omega, fun q hq hlt => ?_,
    fun q hq hlt hqK => ?_⟩
  · rcases Nat.lt_or_ge q i with h' | h'
    · exact h2 q hq h'
    · have : q = i := by omega
      rw [this]; exact hd
  · rcases Nat.lt_or_ge q i with h' | h'
    · exact h3 q hq h' hqK
    · have hqi : q = i := by omega
      rw [hc] at hqK
      rcases (Nat.Prime.dvd_mul hq).mp hqK with h'' | h''
      · exact absurd (hqi ▸ h'') hd
      · have := h1 q hq h''; omega

theorem outb_sieve_prime {R M : Subgroup (Perm (Fin n))} {i r : ℕ} (hi : 2 ≤ i) (hd : i ∣ r)
    (h : OutbSieve R M i r) : i.Prime := by
  obtain ⟨_, -, -, h2, -⟩ := h
  exact outb_prime_of_sieve hi hd h2

theorem outb_sieve_dvd {R M : Subgroup (Perm (Fin n))} {i r : ℕ} (hd : i ∣ r)
    (h : OutbSieve R M i r) : i ∣ Nat.card M / Nat.card R := by
  obtain ⟨m, hc, -⟩ := h
  rw [hc]; exact hd.mul_right m

theorem outb_sieve_next {R M P : Subgroup (Perm (Fin n))} (hRM : R ≤ M) {i r : ℕ}
    (hp : i.Prime) (hd : i ∣ r) (h : OutbSieve R M i r)
    (hP : OutbSylowMod i R M P) (hn : OutbNormIn M P) :
    OutbSieve R M (i + 1) (r / (Nat.card P / Nat.card R)) := by
  obtain ⟨m, hc, h1, h2, h3⟩ := h
  have hc0 : Nat.card M / Nat.card R ≠ 0 := by
    rw [← outb_card_quotient hRM]; exact Nat.card_pos.ne'
  have hcP : Nat.card P / Nat.card R = i ^ (Nat.card M / Nat.card R).factorization i := by
    rw [hP.2.2, Nat.mul_div_cancel _ Nat.card_pos]
  obtain ⟨har, hc', hm', hnd⟩ := outb_sieve_step_arith hc hc0 h1 hp
  rw [← hcP] at har hc' hm' hnd
  refine ⟨m * (Nat.card P / Nat.card R), hc', hm', fun q hq hlt hqr => ?_,
    fun q hq hlt hqK => ?_⟩
  · rcases Nat.lt_or_ge q i with h' | h'
    · exact h2 q hq h' (hqr.trans (Nat.div_dvd_of_dvd har))
    · have : q = i := by omega
      rw [this] at hqr; exact hnd hqr
  · rcases Nat.lt_or_ge q i with h' | h'
    · exact h3 q hq h' hqK
    · have : q = i := by omega
      subst this
      exact ⟨P, hP, hn⟩

theorem outb_sieve_end {R M : Subgroup (Perm (Fin n))} [(R.subgroupOf M).Normal]
    (hRM : R ≤ M) {r : ℕ} (h : OutbSieve R M (n + 1) r) :
    Group.IsNilpotent (M ⧸ R.subgroupOf M) := by
  obtain ⟨_, -, -, -, h3⟩ := h
  exact outb_nilpotent_of_normal hRM fun q hq hqn hqK => h3 q hq (by omega) hqK

/-! ### Brute-force Sylow conjugation in `M / R` -/

/-- A subgroup of `Sym(n)` mapped into itself by conjugation is normalized by the conjugating
element. -/
theorem outb_mem_normalizer_of_map_le {P : Subgroup (Perm (Fin n))} {u : Perm (Fin n)}
    (hle : P.map (MulAut.conj u).toMonoidHom ≤ P) :
    u ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) := by
  have hcard : Nat.card (P.map (MulAut.conj u).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj u).injective
  have heq : P.map (MulAut.conj u).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hle ⟨x, hx, rfl⟩
  · intro hux
    rw [← heq] at hux
    obtain ⟨y, hy, hyx⟩ := hux
    have : y = x := (MulAut.conj u).injective hyx
    rwa [← this]

theorem outb_map_le_of_mem_normalizer {P : Subgroup (Perm (Fin n))} {u : Perm (Fin n)}
    (hu : u ∈ Subgroup.normalizer (P : Set (Perm (Fin n)))) :
    P.map (MulAut.conj u).toMonoidHom ≤ P := by
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hu x).mp hx

/-- Conjugation by `s` preserves `OutbSylowMod` when `s` and `s⁻¹` normalize `R` and `M`. -/
theorem outbSylowMod_conj {p : ℕ} {R M P : Subgroup (Perm (Fin n))}
    (h : OutbSylowMod p R M P) {s : Perm (Fin n)}
    (hsR_inv : ∀ r ∈ R, s⁻¹ * r * s ∈ R) (hsM : ∀ m ∈ M, s * m * s⁻¹ ∈ M) :
    OutbSylowMod p R M (P.map (MulAut.conj s).toMonoidHom) := by
  obtain ⟨hRP, hPM, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact ⟨s⁻¹ * r * s, hRP (hsR_inv r hr), by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hsM x (hPM hx)
  · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hc]

/-- By Sylow's conjugacy theorem in `M / R`, if `OutbSylowMod p R M P` holds and `s` normalizes `R`
and `M`, there is a coset representative `e ∈ reps` with `e ∈ M` and `(e * s) P (e * s)⁻¹ ≤ P`. -/
theorem outb_exists_rep_conj {p : ℕ} (hp : p.Prime) {R M E_H P : Subgroup (Perm (Fin n))}
    [(R.subgroupOf M).Normal] (hME : M ≤ E_H) {reps : List (Perm (Fin n))}
    (hcov : ∀ x ∈ E_H, TmRpCov R reps x) (hsyl : OutbSylowMod p R M P) {s : Perm (Fin n)}
    (hsR_inv : ∀ r ∈ R, s⁻¹ * r * s ∈ R) (hsM : ∀ m ∈ M, s * m * s⁻¹ ∈ M) :
    ∃ e ∈ reps, e ∈ M ∧ P.map (MulAut.conj (e * s)).toMonoidHom ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hRP := hsyl.1
  have hPM := hsyl.2.1
  have hRM : R ≤ M := hRP.trans hPM
  set Q := P.map (MulAut.conj s).toMonoidHom
  have hsylQ : OutbSylowMod p R M Q := outbSylowMod_conj hsyl hsR_inv hsM
  obtain ⟨hbar, hsmul⟩ :=
    MulAction.exists_smul_eq (M ⧸ R.subgroupOf M) (outbSylow hsyl) (outbSylow hsylQ)
  obtain ⟨⟨g, hgM⟩, hg_eq⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) hbar⁻¹
  have hbar_eq : hbar = (QuotientGroup.mk' (R.subgroupOf M) ⟨g, hgM⟩)⁻¹ := by
    rw [hg_eq, inv_inv]
  obtain ⟨e, he_reps, hge⟩ := hcov g (hME hgM)
  have heM : e ∈ M := by
    have h1 : (g * e⁻¹)⁻¹ * g ∈ M := M.mul_mem (M.inv_mem (hRM hge)) hgM
    simpa using h1
  refine ⟨e, he_reps, heM, ?_⟩
  rintro _ ⟨x, hxP, rfl⟩
  have hxQ : s * x * s⁻¹ ∈ Q := ⟨x, hxP, rfl⟩
  have hsxM : s * x * s⁻¹ ∈ M := hsM x (hPM hxP)
  have hxQbar : QuotientGroup.mk' (R.subgroupOf M) ⟨s * x * s⁻¹, hsxM⟩ ∈
      (outbSylow hsylQ : Subgroup (M ⧸ R.subgroupOf M)) :=
    (outb_mem_quotSub_iff hsylQ.1 hsylQ.2.1 ⟨s * x * s⁻¹, hsxM⟩).mpr hxQ
  rw [← hsmul, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply, ← hg_eq, hbar_eq,
    ← map_inv, ← map_mul, ← map_mul] at hxQbar
  have hgxP : g * (s * x * s⁻¹) * g⁻¹ ∈ P :=
    (outb_mem_quotSub_iff hRP hPM _).mp hxQbar
  have hrP : (g * e⁻¹)⁻¹ ∈ P := hRP (R.inv_mem hge)
  have hprod : (g * e⁻¹)⁻¹ * (g * (s * x * s⁻¹) * g⁻¹) * ((g * e⁻¹)⁻¹)⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem hrP hgxP) (P.inv_mem hrP)
  have heq : (g * e⁻¹)⁻¹ * (g * (s * x * s⁻¹) * g⁻¹) * ((g * e⁻¹)⁻¹)⁻¹ =
      (e * s) * x * (e * s)⁻¹ := by group
  rw [heq] at hprod
  exact hprod

/-- One step of the brute-force Sylow-conjugation fold over `reps`. -/
noncomputable def outbFixStep (M P : Subgroup (Perm (Fin n))) (s : Perm (Fin n))
    (t e : Perm (Fin n)) : Perm (Fin n) := by
  classical
  exact if e ∈ M ∧ P.map (MulAut.conj (e * s)).toMonoidHom ≤ P then e * s else t

/-- The fold of `outbFixStep` over `reps`. -/
noncomputable def outbFixFold (M P : Subgroup (Perm (Fin n))) (reps : List (Perm (Fin n)))
    (s : Perm (Fin n)) : Perm (Fin n) :=
  reps.foldl (outbFixStep M P s) s

theorem outbFix_foldl_good {M P : Subgroup (Perm (Fin n))} {s : Perm (Fin n)}
    (l : List (Perm (Fin n))) {t : Perm (Fin n)}
    (ht : ∃ g ∈ M, t = g * s ∧ t ∈ Subgroup.normalizer (P : Set (Perm (Fin n)))) :
    ∃ g ∈ M, l.foldl (outbFixStep M P s) t = g * s ∧
      l.foldl (outbFixStep M P s) t ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) := by
  classical
  induction l generalizing t with
  | nil => exact ht
  | cons e l ih =>
    simp only [List.foldl_cons]
    unfold outbFixStep
    split_ifs with hc
    · exact ih ⟨e, hc.1, rfl, outb_mem_normalizer_of_map_le hc.2⟩
    · exact ih ht

theorem outbFix_foldl_of_mem {M P : Subgroup (Perm (Fin n))} {s : Perm (Fin n)}
    (l : List (Perm (Fin n))) (t : Perm (Fin n))
    (hex : ∃ e ∈ l, e ∈ M ∧ P.map (MulAut.conj (e * s)).toMonoidHom ≤ P) :
    ∃ g ∈ M, l.foldl (outbFixStep M P s) t = g * s ∧
      l.foldl (outbFixStep M P s) t ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) := by
  classical
  induction l generalizing t with
  | nil =>
    obtain ⟨_, hmem, -⟩ := hex
    exact absurd hmem List.not_mem_nil
  | cons e l ih =>
    simp only [List.foldl_cons]
    unfold outbFixStep
    split_ifs with hc
    · exact outbFix_foldl_good l ⟨e, hc.1, rfl, outb_mem_normalizer_of_map_le hc.2⟩
    · obtain ⟨e', he', hc'⟩ := hex
      rcases List.mem_cons.mp he' with rfl | he'
      · exact absurd hc' hc
      · exact ih _ ⟨e', he', hc'⟩

/-- `outbFixFold M P reps s` produces `g * s` with `g ∈ M` normalizing `P`. -/
theorem outbFixFold_spec {p : ℕ} (hp : p.Prime) {R M E_H P : Subgroup (Perm (Fin n))}
    [(R.subgroupOf M).Normal] (hME : M ≤ E_H) {reps : List (Perm (Fin n))}
    (hcov : ∀ x ∈ E_H, TmRpCov R reps x) (hsyl : OutbSylowMod p R M P) {s : Perm (Fin n)}
    (hsR_inv : ∀ r ∈ R, s⁻¹ * r * s ∈ R) (hsM : ∀ m ∈ M, s * m * s⁻¹ ∈ M) :
    ∃ g ∈ M, outbFixFold M P reps s = g * s ∧
      outbFixFold M P reps s ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) :=
  outbFix_foldl_of_mem reps s (outb_exists_rep_conj hp hME hcov hsyl hsR_inv hsM)

/-! ### The Frattini step modulo `R` and the end of the descent -/

/-- **One Frattini step modulo `R`.** Let `S = ⟨ss⟩` with `R ≤ S ≤ K` and `S ⊔ E_H = K`,
`M = S ⊓ E_H`, and `R ≤ P ≤ M` not normalized by `M`. If `ts` corrects every generator of `ss` into
`M s ∩ N_K(P)`, then `S₁ = R ⊔ ⟨ts⟩ = ⟨rs ++ ts⟩` satisfies `R ≤ S₁ ≤ S`, `S₁ ⊔ E_H = K`, and
`2 |S₁ ⊓ E_H| ≤ |S ⊓ E_H|`. -/
theorem outb_corr_step {K E_H R P : Subgroup (Perm (Fin n))} {rs ss ts : List (Perm (Fin n))}
    (_hRE : R ≤ E_H) (hRS : R ≤ gens ss) (hRP : R ≤ P) (hR : gens rs = R)
    (hSE : gens ss ⊔ E_H = K)
    (hts : ∀ t ∈ ts, t ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) ∧
      ∃ g ∈ gens ss ⊓ E_H, ∃ s ∈ ss, t = g * s)
    (hcov : ∀ s ∈ ss, ∃ t ∈ ts, ∃ g ∈ gens ss ⊓ E_H, t = g * s)
    (hnot : ¬ OutbNormIn (gens ss ⊓ E_H) P) :
    R ≤ gens (rs ++ ts) ∧ gens (rs ++ ts) ≤ gens ss ∧ gens (rs ++ ts) ⊔ E_H = K ∧
      2 * Nat.card (gens (rs ++ ts) ⊓ E_H : Subgroup _) ≤
        Nat.card (gens ss ⊓ E_H : Subgroup _) := by
  rw [outb_gens_append, hR]
  have hts_le : gens ts ≤ gens ss := by
    refine (Subgroup.closure_le _).mpr fun t ht => ?_
    obtain ⟨-, g, hg, s, hs, rfl⟩ := hts t ht
    exact (gens ss).mul_mem hg.1 (Subgroup.subset_closure hs)
  have hS1_le : R ⊔ gens ts ≤ gens ss := sup_le hRS hts_le
  have hSS1 : gens ss ≤ (R ⊔ gens ts) ⊔ E_H := by
    refine (Subgroup.closure_le _).mpr fun s hs => ?_
    obtain ⟨t, ht, g, hg, rfl⟩ := hcov s hs
    have : s = g⁻¹ * (g * s) := by group
    rw [SetLike.mem_coe, this]
    have ht1 : g * s ∈ R ⊔ gens ts := Subgroup.mem_sup_right (Subgroup.subset_closure ht)
    have hg1 : g⁻¹ ∈ E_H := E_H.inv_mem hg.2
    have hmul := Subgroup.mul_mem_sup hg1 ht1
    rwa [sup_comm] at hmul
  have hsup : (R ⊔ gens ts) ⊔ E_H = K :=
    le_antisymm (hSE ▸ sup_le_sup_right hS1_le _)
      (hSE ▸ sup_le hSS1 le_sup_right)
  have hnorm : R ⊔ gens ts ≤ Subgroup.normalizer (P : Set (Perm (Fin n))) := by
    refine sup_le (hRP.trans Subgroup.le_normalizer) ?_
    exact (Subgroup.closure_le _).mpr fun t ht => (hts t ht).1
  refine ⟨le_sup_left, hS1_le, hsup, GI.CitedChecks.two_mul_card_le_of_lt
    (lt_of_le_of_ne (inf_le_inf_right _ hS1_le) fun heq => hnot ?_)⟩
  intro g hg x hx
  have hg1 : g ∈ (R ⊔ gens ts) ⊓ E_H := heq ▸ hg
  exact (Subgroup.mem_normalizer_iff.mp (hnorm hg1.1) x).mp hx

/-- **Solvability of `S / R` at the end of the descent**: when `R ≤ S ≤ K`, `R ≤ E_H ≤ K`,
`K / E_H` is solvable, and `(S ⊓ E_H) / R` is nilpotent, the quotient `S / R` is solvable. -/
theorem outb_solvable_quotient {K E_H R S : Subgroup (Perm (Fin n))}
    (hRE : R ≤ E_H) (hEK : E_H ≤ K) (hRS : R ≤ S) (hSK : S ≤ K)
    [(E_H.subgroupOf K).Normal] [(R.subgroupOf (S ⊓ E_H : Subgroup _)).Normal]
    [(R.subgroupOf S).Normal]
    (hK : Group.IsSolvable (K ⧸ E_H.subgroupOf K))
    (hM : Group.IsNilpotent ((S ⊓ E_H : Subgroup _) ⧸ R.subgroupOf (S ⊓ E_H : Subgroup _))) :
    Group.IsSolvable (S ⧸ R.subgroupOf S) := by
  have : Group.IsSolvable (K ⧸ E_H.subgroupOf K) := hK
  have : Group.IsNilpotent ((S ⊓ E_H : Subgroup _) ⧸ R.subgroupOf (S ⊓ E_H : Subgroup _)) := hM
  have : Group.IsSolvable ((S ⊓ E_H : Subgroup _) ⧸ R.subgroupOf (S ⊓ E_H : Subgroup _)) :=
    inferInstance
  have hRM : R ≤ S ⊓ E_H := le_inf hRS hRE
  obtain ⟨a, ha⟩ := GI.Multicoset.exists_relDerived_of_isSolvable hEK
  obtain ⟨b, hb⟩ := GI.Multicoset.exists_relDerived_of_isSolvable hRM
  have haS : GI.Multicoset.relDerived S (S ⊓ E_H) a ≤ S ⊓ E_H := by
    refine le_inf (GI.Multicoset.relDerived_le inf_le_left a) ?_
    exact (GI.Multicoset.relDerived_mono hEK hSK
      (inf_le_right.trans (GI.Multicoset.le_relDerived hEK a)) a le_rfl).trans ha
  exact GI.Multicoset.isSolvable_quot_of_relDerived
    (GI.RadicalFreeOrder.relDerived_trans hRM haS hb)

end GI.Impl
