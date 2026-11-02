import Workspace.Impl.TermSupMath
import Workspace.Impl.TermRadStep

/-!
# T4, the search for a Sylow subgroup that is not normal

The proof of Lemma A.19 asks: "If `K` is not nilpotent, choose a nonnormal Sylow subgroup `P`
of `K`." The program looks at `d = 0, 1, …, n` in turn and keeps the part `r` of `|K|` that is
free of the primes below `d` (`SupSieve`). At `d ≥ 2` with `d ∣ r`, the number `d` is prime
(`sup_prime_of_sieve`). It then computes a Sylow `d`-subgroup `P` of `K` (the cited
**SylowAlgo**) and tests `K`-normality of `P`: the normal closure of `P` in `K` (the cited
**NormalClosure**) lies in `P` (by **Membership**, `le_spec`). If `P` is normal, `r` loses the
order of `P` (the cited **GroupOrder**); otherwise the search records `(d, P)`.

At the end either some `(p, P)` was recorded, or every prime `q ≤ n` dividing `|K|` has a normal
Sylow subgroup, so `K` is nilpotent (`sup_sieve_end`). The state is
`[r, 0, 0, 0]` while searching and `[0, 1, p, P]` once found (`SupSearchInv`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### The sieve invariant -/

/-- After the numbers below `i`: `|K| = r m`, where the prime factors of `m` are below `i`, no
prime below `i` divides `r`, and each prime below `i` dividing `|K|` has a Sylow subgroup
normalized by `K`. -/
def SupSieve (K : Subgroup (Perm (Fin n))) (i r : ℕ) : Prop :=
  ∃ m, Nat.card K = r * m ∧ (∀ q, q.Prime → q ∣ m → q < i) ∧ (∀ q, q.Prime → q < i → ¬ q ∣ r) ∧
    (∀ q, q.Prime → q < i → q ∣ Nat.card K → ∃ P, IsSylowOf q K P ∧ SupNormIn K P)

theorem sup_sieve_zero (K : Subgroup (Perm (Fin n))) : SupSieve K 0 (Nat.card K) :=
  ⟨1, by ring, fun q hq h => absurd (Nat.le_of_dvd one_pos h) (by have := hq.two_le; omega),
    fun q _ h => absurd h (by omega), fun q _ h => absurd h (by omega)⟩

theorem sup_sieve_le {K : Subgroup (Perm (Fin n))} {i r : ℕ} (h : SupSieve K i r) :
    r ≤ Nat.card K := by
  obtain ⟨m, hc, -⟩ := h
  have : 0 < Nat.card K := Nat.card_pos
  exact Nat.le_of_dvd this ⟨m, hc⟩

/-- At `i < 2` nothing changes: there is no prime below `2`. -/
theorem sup_sieve_small {K : Subgroup (Perm (Fin n))} {i r : ℕ} (hi : i < 2)
    (h : SupSieve K i r) : SupSieve K (i + 1) r := by
  obtain ⟨m, hc, h1, h2, h3⟩ := h
  refine ⟨m, hc, fun q hq hd => by have := h1 q hq hd; omega, fun q hq hlt => ?_,
    fun q hq hlt => ?_⟩
  · have := hq.two_le; omega
  · have := hq.two_le; omega

/-- If `i ∤ r`, nothing changes: a prime `i` does not divide `|K| = r m`. -/
theorem sup_sieve_skip {K : Subgroup (Perm (Fin n))} {i r : ℕ} (hd : ¬ i ∣ r)
    (h : SupSieve K i r) : SupSieve K (i + 1) r := by
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

/-- If `2 ≤ i` and `i ∣ r`, then `i` is prime. -/
theorem sup_sieve_prime {K : Subgroup (Perm (Fin n))} {i r : ℕ} (hi : 2 ≤ i) (hd : i ∣ r)
    (h : SupSieve K i r) : i.Prime := by
  obtain ⟨m, -, -, h2, -⟩ := h
  exact sup_prime_of_sieve hi hd h2

theorem sup_sieve_dvd {K : Subgroup (Perm (Fin n))} {i r : ℕ} (hd : i ∣ r)
    (h : SupSieve K i r) : i ∣ Nat.card K := by
  obtain ⟨m, hc, -⟩ := h
  rw [hc]; exact hd.mul_right m

/-- After a normal Sylow `i`-subgroup `P`: `r` becomes `r / |P|`. -/
theorem sup_sieve_next {K P : Subgroup (Perm (Fin n))} {i r : ℕ} (hp : i.Prime) (hd : i ∣ r)
    (h : SupSieve K i r) (hP : IsSylowOf i K P) (hn : SupNormIn K P) :
    SupSieve K (i + 1) (r / Nat.card P) := by
  haveI := Fact.mk hp
  obtain ⟨m, hc, h1, h2, h3⟩ := h
  have hcP := (sup_isSylowOf_iff.mp hP).2
  obtain ⟨-, hc', hm', hnd⟩ := sup_sieve_step hc Nat.card_pos.ne' h1 hp
  rw [← hcP] at hc' hm' hnd
  refine ⟨m * Nat.card P, hc', hm', fun q hq hlt hqr => ?_, fun q hq hlt hqK => ?_⟩
  · rcases Nat.lt_or_ge q i with h' | h'
    · exact h2 q hq h' ((hqr.trans (Nat.div_dvd_of_dvd (by
        obtain ⟨a, -, -⟩ := sup_sieve_step hc Nat.card_pos.ne' h1 hp
        rwa [← hcP] at a))))
    · have : q = i := by omega
      rw [this] at hqr; exact hnd hqr
  · rcases Nat.lt_or_ge q i with h' | h'
    · exact h3 q hq h' hqK
    · have : q = i := by omega
      subst this
      exact ⟨P, hP, hn⟩

/-- **The end of the search**: every prime `q ≤ n` was handled, so `K` is nilpotent. -/
theorem sup_sieve_end {K : Subgroup (Perm (Fin n))} {r : ℕ} (h : SupSieve K (n + 1) r) :
    Group.IsNilpotent K := by
  obtain ⟨m, -, -, -, h3⟩ := h
  exact sup_nilpotent_of_normal fun q hq hqn hqK => h3 q hq (by omega) hqK

/-! ### The normality test -/

/-- The normal closure of `P = ⟨ps⟩ ≤ K` in `K` lies in `P` exactly when `K` normalizes `P`. -/
theorem sup_normIn_iff {K : Subgroup (Perm (Fin n))} {ps cs : List (Perm (Fin n))}
    (hle : gens ps ≤ K)
    (hcs : gens cs = Subgroup.closure {x | ∃ g ∈ K ⊔ gens ps, ∃ y ∈ ps, x = g * y * g⁻¹}) :
    gens cs ≤ gens ps ↔ SupNormIn K (gens ps) := by
  rw [hcs, sup_eq_left.mpr hle]
  constructor
  · intro h g hg x hx
    have hmap : (gens ps).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.closure {x | ∃ g ∈ K, ∃ y ∈ ps, x = g * y * g⁻¹} := by
      rw [← sup_gens_conj]
      refine Subgroup.closure_mono fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact ⟨g, hg, y, hy, rfl⟩
    exact h (hmap ⟨x, hx, by simp [MulAut.conj_apply]⟩)
  · intro h
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    obtain ⟨g, hg, y, hy, rfl⟩ := hz
    exact h g hg y (Subgroup.subset_closure hy)

/-! ### The program -/

/-- The part of the search step after a prime `d ∣ r` is found: a Sylow `d`-subgroup `P` of
`K`, the normal closure of `P` in `K`, and the test. Environment `[a, Sylow, P, closure]`. -/
def supPrimeE (mg le jsy jnc jord : ℕ) : Expr :=
  .letE (.prim jsy (mk2 (arg 0) (arg 1)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
  (.letE (.prim jnc (mk2 (arg 0) (.var 2)))
  (.ite (.call le (mk2 (.var 2) (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 3)))))
    (mk4 (.arith .div (.get (arg 2) (.nat 0)) (.prim jord (.var 2))) (.nat 0) (.nat 0) (.nat 0))
    (mk4 (.nat 0) (.nat 1) (arg 1) (.var 2)))))

/-- **The search step** on `[gens K, d, state]`. -/
def supSearchBody (mg le jsy jnc jord : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 1)) (arg 2)
  (.ite (.arith .lt (arg 1) (.nat 2)) (arg 2)
  (.ite (.arith .mod (.get (arg 2) (.nat 0)) (arg 1)) (arg 2)
  (supPrimeE mg le jsy jnc jord)))

/-- The state of the search after the numbers below `i`. -/
def SupSearchInv (K : Subgroup (Perm (Fin n))) (i : ℕ) (acc : Val) : Prop :=
  (∃ r, acc = .list [.nat r, .nat 0, .nat 0, .nat 0] ∧ SupSieve K i r) ∨
  (∃ p ps, acc = .list [.nat 0, .nat 1, .nat p, encGroup ps] ∧ ps.length ≤ n ^ 2 ∧ p.Prime ∧
    p ≤ n ∧ IsSylowOf p K (gens ps) ∧ ¬ SupNormIn K (gens ps))

/-- The weight of a number at most `|K|`. -/
theorem sup_wt_nat_le {K : Subgroup (Perm (Fin n))} {r : ℕ} (h : r ≤ Nat.card K) :
    (Val.nat r).wt ≤ n ^ 2 + 3 := by
  have h1 := wt_card_le K
  rw [wt_nat] at h1 ⊢
  have := GI.Machine.len_mono h
  omega

theorem sup_search_wt {K : Subgroup (Perm (Fin n))} {i : ℕ} {acc : Val}
    (h : SupSearchInv K i acc) : acc.wt ≤ 700 * (n + 1) ^ 6 := by
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn1 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have h0 := wt_nat_le 0
  have h1 := wt_nat_le 1
  rcases h with ⟨r, rfl, hs⟩ | ⟨p, ps, rfl, hl, -, hpn, -⟩
  · have := sup_wt_nat_le (sup_sieve_le hs)
    have := wt_list4_le (.nat r) (.nat 0) (.nat 0) (.nat 0)
    omega
  · have := wt_encGroup_le_sq hl
    have := wt_list4_le (.nat 0) (.nat 1) (.nat p) (encGroup ps)
    have := wt_nat_le p
    omega

/-- Where the search step and its modules sit. -/
structure SupSearchAt (P : Program) (g mg le jsy jnc jord jm : ℕ) (hsy : SylowAlgo)
    (hnc : NormalClosure) (hord : GroupOrder) (hmem : Membership) : Prop where
  step : P.funs[g]? = some (supSearchBody mg le jsy jnc jord)
  mg : P.HasAt mg (mkGroupFuns mg)
  le : P.HasAt le (leFuns le jm)
  sy : P.prims[jsy]? = some (sylowPrim hsy)
  nc : P.prims[jnc]? = some (normalClosurePrim hnc)
  ord : P.prims[jord]? = some (groupOrderPrim hord)
  mem : P.prims[jm]? = some (membershipPrim hmem)

/-- The cost of a search step, with `Y = 10⁴ (n + 1)⁶`. -/
def supSearchCost (psy pnc pord pm : Prim) (n : ℕ) : ℕ :=
  psy.boundSize (10 ^ 4 * (n + 1) ^ 6) + pnc.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    pord.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 4 * (n + 1) ^ 6 * pm.boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 6 * (10 ^ 4 * (n + 1) ^ 6) ^ 3

/-- `if` with a known test and `EvalAll` branches. -/
theorem sup_ite {P : Program} {env : List Val} {c t e : Expr} {x cc : ℕ}
    (hc : Det P env c (.nat x) cc) {R : Val → ℕ → Prop} (ht : x ≠ 0 → EvalAll P env t R)
    (he : x = 0 → EvalAll P env e R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ce, R w ce ∧ c' ≤ cc + ce + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    by_cases hx : x = 0
    · rw [if_pos hx]
      exact (he hx).mono fun w ce hw => ⟨ce, hw, by omega⟩
    · rw [if_neg hx]
      exact (ht hx).mono fun w ce hw => ⟨ce, hw, by omega⟩

end GI.Impl
