import Workspace.MulticosetSupplement
import Workspace.CitedChecks.AlgoChecks
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.Factorization.Basic

/-!
# T4, the mathematics: Sylow subgroups, the Frattini correction and the prime sieve

The proof of Lemma A.19 keeps `S ≤ R` with `S N = R` and looks at `K = S ∩ N`. If `K` is not
nilpotent, it takes a Sylow subgroup `P` of `K` that is not normal in `K`, and replaces each
generator `s` of `S` by `t = g s`, where `g ∈ K` conjugates `s P s⁻¹` back to `P` (Sylow
conjugacy). This file proves the facts the program needs.

* `sup_isSylowOf_iff`: the cited output form `IsSylowOf p K P` is "`P ≤ K` of order the full
  power of `p` in `|K|`". So conjugation keeps it (`sup_isSylowOf_conj`).
* `sup_corr_normalizer`, `sup_corr_step`: the corrected elements normalize `P`, the new group
  `S₁` still satisfies `S₁ N = R`, and `S₁ ∩ N < K`, so `2 |S₁ ∩ N| ≤ |K|`.
* `sup_nilpotent_of_normal`: if every prime `q ≤ n` dividing `|K|` has a Sylow subgroup that is
  normal in `K`, then `K` is nilpotent. Primes above `n` do not divide `|K|`, since `|K|`
  divides `n!`.
* `sup_prime_of_sieve`, `sup_sieve_step`: the search runs over `d = 2, …, n` and keeps the part
  `r` of `|K|` free of primes below `d`. Then `d ∣ r` forces `d` to be prime, and removing the
  order of a Sylow `d`-subgroup from `r` keeps this property.
* `sup_solvable`: when `K` is nilpotent, `S` is solvable (`solvable_of_nilpotent_kernel`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n : ℕ}

/-- `K` normalizes `P`. The test of the program is "the normal closure of `P` in `K` lies in
`P`". -/
def SupNormIn (K P : Subgroup (Perm (Fin n))) : Prop := ∀ g ∈ K, ∀ x ∈ P, g * x * g⁻¹ ∈ P

/-! ### The output form of the Sylow tasks -/

/-- `P ≤ K` as a subgroup of `K` is isomorphic to `P`. -/
theorem sup_card_subgroupOf {K P : Subgroup (Perm (Fin n))} (h : P ≤ K) :
    Nat.card (P.subgroupOf K) = Nat.card P :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

/-- **`IsSylowOf` is the order condition.** -/
theorem sup_isSylowOf_iff {p : ℕ} [Fact p.Prime] {K P : Subgroup (Perm (Fin n))} :
    IsSylowOf p K P ↔ P ≤ K ∧ Nat.card P = p ^ (Nat.card K).factorization p := by
  constructor
  · rintro ⟨hle, hpg, hidx⟩
    have hpg' : IsPGroup p (P.subgroupOf K) := hpg.comap_of_injective K.subtype
      Subtype.coe_injective
    refine ⟨hle, ?_⟩
    rw [← sup_card_subgroupOf hle]
    exact (hpg'.toSylow hidx).card_eq_multiplicity
  · rintro ⟨hle, hc⟩
    rw [← sup_card_subgroupOf hle] at hc
    let Q := Sylow.ofCard (P.subgroupOf K) hc
    refine ⟨hle, ?_, ?_⟩
    · exact (Q.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe hle)
    · exact Q.not_dvd_index

/-- The Sylow subgroup of `K` given by an `IsSylowOf` subgroup. -/
noncomputable def supSylow {p : ℕ} [Fact p.Prime] {K P : Subgroup (Perm (Fin n))}
    (h : IsSylowOf p K P) : Sylow p K :=
  Sylow.ofCard (P.subgroupOf K) (by
    rw [sup_card_subgroupOf (sup_isSylowOf_iff.mp h).1]; exact (sup_isSylowOf_iff.mp h).2)

/-- Conjugation by `s` as a map of subgroups. -/
theorem sup_gens_conj (s : Perm (Fin n)) (ps : List (Perm (Fin n))) :
    gens (ps.map fun x => s * x * s⁻¹) = (gens ps).map (MulAut.conj s).toMonoidHom := by
  unfold gens
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem sup_mem_conj {s : Perm (Fin n)} {P : Subgroup (Perm (Fin n))} {x : Perm (Fin n)} :
    x ∈ P.map (MulAut.conj s).toMonoidHom ↔ s⁻¹ * x * s ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨s⁻¹ * x * s, h, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- **Conjugation keeps `IsSylowOf`** when `s` normalizes `K`. -/
theorem sup_isSylowOf_conj {p : ℕ} (hp : p.Prime) {K P : Subgroup (Perm (Fin n))}
    (h : IsSylowOf p K P) {s : Perm (Fin n)} (hs : ∀ k ∈ K, s * k * s⁻¹ ∈ K) :
    IsSylowOf p K (P.map (MulAut.conj s).toMonoidHom) := by
  haveI := Fact.mk hp
  obtain ⟨hle, hc⟩ := sup_isSylowOf_iff.mp h
  refine sup_isSylowOf_iff.mpr ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hs y (hle hy)
  · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hc]

/-! ### The Frattini correction -/

/-- **The corrected element normalizes `P`.** If `g` conjugates `Q = s P s⁻¹` to `P` (the output
of Sylow conjugation: `x ∈ Q ↔ g x g⁻¹ ∈ P`), then `t = g s` normalizes `P`. -/
theorem sup_corr_normalizer {P : Subgroup (Perm (Fin n))} {s g : Perm (Fin n)}
    (hg : ∀ x, x ∈ P.map (MulAut.conj s).toMonoidHom ↔ g * x * g⁻¹ ∈ P) :
    g * s ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [show g * s * x * (g * s)⁻¹ = g * (s * x * s⁻¹) * g⁻¹ by group, ← hg, sup_mem_conj]
  simp [mul_assoc]

/-- **One Frattini step.** Let `S = ⟨ss⟩ ≤ R` with `S ⊔ N = R`, `K = S ∩ N`, and let `P ≤ K` be
not normalized by `K`. If for every generator `s` the element `t s` lies in `K s` and normalizes
`P`, then `S₁ = ⟨t s⟩` satisfies `S₁ ≤ S`, `S₁ ⊔ N = R`, and `2 |S₁ ∩ N| ≤ |K|`. -/
theorem sup_corr_step {R N : Subgroup (Perm (Fin n))} {ss ts : List (Perm (Fin n))}
    {P : Subgroup (Perm (Fin n))} (hSN : gens ss ⊔ N = R)
    (hts : ∀ t ∈ ts, t ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) ∧ ∃ g ∈ gens ss ⊓ N, ∃ s ∈ ss, t = g * s)
    (hcov : ∀ s ∈ ss, ∃ t ∈ ts, ∃ g ∈ gens ss ⊓ N, t = g * s)
    (hnot : ¬ SupNormIn (gens ss ⊓ N) P) :
    gens ts ≤ gens ss ∧ gens ts ⊔ N = R ∧
      2 * Nat.card (gens ts ⊓ N : Subgroup _) ≤ Nat.card (gens ss ⊓ N : Subgroup _) := by
  have hS1 : gens ts ≤ gens ss := by
    refine Subgroup.closure_le _ |>.mpr fun t ht => ?_
    obtain ⟨-, g, hg, s, hs, rfl⟩ := hts t ht
    exact (gens ss).mul_mem hg.1 (Subgroup.subset_closure hs)
  have hSS1 : gens ss ≤ gens ts ⊔ N := by
    refine Subgroup.closure_le _ |>.mpr fun s hs => ?_
    obtain ⟨t, ht, g, hg, rfl⟩ := hcov s hs
    have : s = g⁻¹ * (g * s) := by group
    rw [SetLike.mem_coe, this]
    exact Subgroup.mul_mem_sup (N.inv_mem hg.2) (Subgroup.subset_closure ht) |>
      fun h => by rwa [sup_comm] at h
  have hsup : gens ts ⊔ N = R := le_antisymm (hSN ▸ sup_le_sup_right hS1 _)
    (hSN ▸ sup_le hSS1 le_sup_right)
  refine ⟨hS1, hsup, CitedChecks.two_mul_card_le_of_lt (lt_of_le_of_ne
    (inf_le_inf_right _ hS1) fun heq => hnot ?_)⟩
  intro g hg x hx
  have hgt : g ∈ gens ts ⊓ N := heq ▸ hg
  have hn : gens ts ≤ Subgroup.normalizer (P : Set (Perm (Fin n))) :=
    Subgroup.closure_le _ |>.mpr fun t ht => (hts t ht).1
  exact (Subgroup.mem_normalizer_iff.mp (hn hgt.1) x).mp hx

/-! ### Nilpotency from normal Sylow subgroups -/

/-- A normalized `IsSylowOf` subgroup gives a normal Sylow subgroup of `K`. -/
theorem sup_sylow_normal {p : ℕ} [Fact p.Prime] {K P : Subgroup (Perm (Fin n))}
    (h : IsSylowOf p K P) (hn : SupNormIn K P) : ((supSylow h : Sylow p K) : Subgroup K).Normal :=
  ⟨fun x hx g => hn g g.2 x hx⟩

/-- The prime divisors of the order of a subgroup of `Sym(n)` are at most `n`. -/
theorem sup_prime_le {K : Subgroup (Perm (Fin n))} {q : ℕ} (hq : q.Prime)
    (hd : q ∣ Nat.card K) : q ≤ n := by
  have h1 : Nat.card K ∣ Nat.card (Perm (Fin n)) := Subgroup.card_subgroup_dvd_card K
  rw [Nat.card_eq_fintype_card (α := Perm (Fin n)), Fintype.card_perm, Fintype.card_fin] at h1
  exact (Nat.Prime.dvd_factorial hq).mp (hd.trans h1)

/-- **Nilpotency test.** If every prime `q ≤ n` dividing `|K|` has an `IsSylowOf` subgroup
normalized by `K`, then `K` is nilpotent (all Sylow subgroups normal). -/
theorem sup_nilpotent_of_normal {K : Subgroup (Perm (Fin n))}
    (h : ∀ q, q.Prime → q ≤ n → q ∣ Nat.card K → ∃ P, IsSylowOf q K P ∧ SupNormIn K P) :
    Group.IsNilpotent K := by
  have htfae := (isNilpotent_of_finite_tfae (G := K)).out 0 3
  refine htfae.mpr fun q hq Q => ?_
  by_cases hd : q ∣ Nat.card K
  · obtain ⟨P, hP, hn⟩ := h q hq.out (sup_prime_le hq.out hd) hd
    have hN := sup_sylow_normal hP hn
    letI := Sylow.unique_of_normal (supSylow hP) hN
    rwa [Subsingleton.elim Q (supSylow hP)]
  · have hc : Nat.card Q = 1 := by
      rw [Q.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
    rw [Subgroup.card_eq_one.mp hc]
    exact Subgroup.normal_bot

/-- In a nilpotent `K`, every `IsSylowOf` subgroup is normalized by `K`. -/
theorem sup_normIn_of_nilpotent {K P : Subgroup (Perm (Fin n))} {p : ℕ} (hp : p.Prime)
    (hK : Group.IsNilpotent K) (hP : IsSylowOf p K P) : SupNormIn K P := by
  haveI := Fact.mk hp
  have htfae := (isNilpotent_of_finite_tfae (G := K)).out 0 3
  have hN := htfae.mp hK p inferInstance (supSylow hP)
  intro g hg x hx
  have hle := (sup_isSylowOf_iff.mp hP).1
  have h1 : (⟨x, hle hx⟩ : K) ∈ ((supSylow hP : Sylow p K) : Subgroup K) := hx
  exact hN.conj_mem _ h1 ⟨g, hg⟩

/-! ### The prime sieve -/

/-- **`d` is prime** when `d ≥ 2` divides `r` and no smaller prime divides `r`. -/
theorem sup_prime_of_sieve {d r : ℕ} (h2 : 2 ≤ d) (hd : d ∣ r)
    (hlow : ∀ q, q.Prime → q < d → ¬ q ∣ r) : d.Prime := by
  have hm := Nat.minFac_prime (show d ≠ 1 by omega)
  have hle := Nat.minFac_le (show 0 < d by omega)
  rcases Nat.lt_or_ge (Nat.minFac d) d with hlt | hge
  · exact absurd ((Nat.minFac_dvd d).trans hd) (hlow _ hm hlt)
  · have : Nat.minFac d = d := le_antisymm hle hge
    rw [← this]; exact hm

/-- **One sieve step.** If `c = r m`, the prime factors of `m` are below the prime `d`, and
`d ∣ r`, then `a = d^(v_d c)` divides `r`, `c = (r / a) (m a)`, the prime factors of `m a` are
at most `d`, and `d ∤ r / a`. -/
theorem sup_sieve_step {c r m d : ℕ} (hc : c = r * m) (hc0 : c ≠ 0)
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

/-! ### The end of the descent -/

/-- `S ∩ N` as a subgroup of `G` and `N` as a subgroup of `S` are the same group. -/
def supInfEquiv (S N : Subgroup (Perm (Fin n))) : (S ⊓ N : Subgroup _) ≃* N.subgroupOf S where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun y := ⟨y.1.1, y.1.2, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **`S` is solvable** when `S ≤ R`, `R/N` is solvable and `S ∩ N` is nilpotent. -/
theorem sup_solvable {R N S : Subgroup (Perm (Fin n))} [(N.subgroupOf R).Normal]
    (hR : IsSolvable (R ⧸ N.subgroupOf R)) (hSR : S ≤ R)
    (hK : Group.IsNilpotent (S ⊓ N : Subgroup _)) : IsSolvable S := by
  haveI := hR
  haveI : Group.IsNilpotent (N.subgroupOf S) := nilpotent_of_mulEquiv (supInfEquiv S N)
  exact GI.Multicoset.solvable_of_nilpotent_kernel (N := N) hSR

end GI.Impl
