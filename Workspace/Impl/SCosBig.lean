import Workspace.Impl.SCosBig4

/-!
# Function 5 (`bigF`), the specification

`scos_big_spec`: on a problem `[gv, xv, ind]` whose group `𝒢` is transitive on `Φ` with
`|Φ| ≥ 2`, function `5` answers the problem. It computes a minimal block system of `𝒢` on `Φ`
(with `m ≥ 2` blocks of one size `s`), the kernel `K` of the action on the blocks, at most
`ℓ ≤ (m + 1)^c` coset representatives of `K` in `𝒢`, solves one child problem for `K` per
coset (`hrec`, the orbits of `K` on `Φ` have at most `s < |Φ|` points), and pastes the answers.

The cost is the own cost `scosOwnG` plus `ℓ` times the cost of a child and of its share of the
map (`scosOwnC n c`). `scosOwnG` is the sum of the nine `let` steps (each at most
`scosBigD n c`, files `SCosBig2`, `SCosBig3`), the bounds of the two primitive calls (minimal
blocks and preimage), the map over the children and the paste (file `SCosBig4`).
`scosOwnG_le` bounds it by `scosBigK … c * (n + 1) ^ scosBigE … c`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- **The own cost of function 5.** -/
noncomputable def scosOwnG (hps : PointwiseStab) (hpre : Preimage) (hmb : MinimalBlocks)
    (n c : ℕ) : ℕ :=
  (minimalBlocksPrim hmb).boundSize (100000 * scosBigS n c) +
    (preimagePrim hpre).boundSize (100000 * scosBigS n c) + scosOwnP hps n c + scosOwnC n c +
    20 * scosBigD n c

section Prog

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The chain of the nine `let`s, with the own cost as it comes out. -/
theorem scosBig_chain (hc : ScosPalfyC c) {𝒢 : Subgroup (ScosPair n)} {x : ScosPair n}
    {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ) (htr : ScosTrans 𝒢 Φ) (h2 : 2 ≤ Φ.card)
    (hsol : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))))
    {gs : List (Perm (Fin (n + n)))} (hgs : gens gs = 𝒢.map nintSum)
    (hw : (encGroup gs).wt ≤ scosW n)
    (T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ)
    (hrec : ∀ (K : Subgroup (ScosPair n)) (v' : Val) (x' : ScosPair n), K ≤ 𝒢 →
      ScosProb n v' K x' Φ → scosMo K Φ < Φ.card →
        FunAll 𝒫 0 v' (fun w c' => ScosAns n w x' K Φ ∧ c' ≤ T K Φ)) :
    EvalAll 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]] (scosBigF c)
      (ScosBigPost n c T 𝒢 x Φ (scosOwnC n c + scosOwnP hps n c + scosBigD n c +
        (scosBigD n c + 700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + (preimagePrim hpre).boundSize (100000 * scosBigS n c) +
          700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + 700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + 700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + (minimalBlocksPrim hmb).boundSize (100000 * scosBigS n c) +
          700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + 700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + 700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + 700 * (n + n + 1) ^ 6 + 1) +
        (scosBigD n c + 700 * (n + n + 1) ^ 6 + 1))) := by
  unfold scosBigF
  refine scosBig_let (scosBig_step1 gs x Φ hw) ?_
  refine scosBig_let (scosBig_step2 gs x Φ hw) ?_
  refine scosBig_let (scosBig_step3 hinv x hgs hw) ?_
  refine scosBig_let (scosBig_step4 hinv x hw) ?_
  refine scosBig_letR (scosBig_step5 hinv htr h2 x hgs hw) fun v5 hv5 => ?_
  obtain ⟨lab, rfl, hlt, hmbl⟩ := hv5
  refine scosBig_let (scosBig_step6 hinv x hlt) ?_
  refine scosBig_let (scosBig_step7 hinv x hw hlt) ?_
  refine scosBig_letR (scosBig_step8 hinv x hgs hw hlt hmbl) fun kv hkv => ?_
  refine scosBig_letR (scosBig_step9 hc hinv htr hsol x hgs hw hlt hmbl kv) fun w9 hw9 => ?_
  exact scosBig_tail hc hinv htr h2 hsol hgs hw hlt hmbl hkv hw9 T hrec _ rfl rfl

/-- **The specification of function 5** (`bigF`). -/
theorem scos_big_spec (hc : ScosPalfyC c) {v : Val} {𝒢 : Subgroup (ScosPair n)}
    {x : ScosPair n} {Φ : Finset (Fin n)} (hv : ScosProb n v 𝒢 x Φ) (ht : ScosTrans 𝒢 Φ)
    (h2 : 2 ≤ Φ.card)
    (T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ)
    (hrec : ∀ (K : Subgroup (ScosPair n)) (v' : Val) (x' : ScosPair n), K ≤ 𝒢 →
      ScosProb n v' K x' Φ → scosMo K Φ < Φ.card →
        FunAll 𝒫 0 v' (fun w c' => ScosAns n w x' K Φ ∧ c' ≤ T K Φ)) :
    FunAll 𝒫 5 v (fun w cost => ScosAns n w x 𝒢 Φ ∧ ∃ (K : Subgroup (ScosPair n)) (m s ℓ : ℕ),
      K ≤ 𝒢 ∧ 2 ≤ m ∧ 1 ≤ s ∧ m * s ≤ Φ.card ∧ ℓ ≤ (m + 1) ^ c ∧ scosMo K Φ ≤ s ∧
      cost ≤ scosOwnG hps hpre hmb n c + ℓ * (scosOwnC n c + T K Φ)) := by
  obtain ⟨gv, rfl, ⟨gs, rfl, hgs⟩, hw⟩ := hv.val
  refine FunAll.intro scos_big ((scosBig_chain hc hv.inv ht h2 hv.solv hgs hw T hrec).mono
    fun w cost h => (h.mono ?_))
  have hD : 700 * (n + n + 1) ^ 6 + 1 ≤ scosBigD n c := by
    have := (scosBigS_facts n c).1
    have := (scosPaste_Q n).1
    exact scosBigD_of (A := 701) (j := 1) (by rw [pow_one]; omega) (by norm_num) (by norm_num)
  unfold scosOwnG
  omega

end Prog

/-! ### The own cost is a polynomial -/

/-- The constant of `scosOwnG_le`. -/
noncomputable def scosBigK (hps : PointwiseStab) (hpre : Preimage) (hmb : MinimalBlocks)
    (c : ℕ) : ℕ :=
  (minimalBlocksPrim hmb).c * (100002 * 2 ^ (c + 13)) ^ (minimalBlocksPrim hmb).k +
    (preimagePrim hpre).c * (100002 * 2 ^ (c + 13)) ^ (preimagePrim hpre).k +
    ((pointwiseStabPrim hps).c + pstabK + 1000000000000000) *
        10000002 ^ ((pointwiseStabPrim hps).k + 9) *
        (2 ^ (c + 7)) ^ (4 * ((pointwiseStabPrim hps).k + 9)) +
    100000000 * 4 ^ (c + 7) + 20 * (10 ^ 40 * (c + 1) * (2 ^ (c + 13)) ^ 7)

/-- The exponent of `scosOwnG_le`. -/
noncomputable def scosBigE (hps : PointwiseStab) (hpre : Preimage) (hmb : MinimalBlocks)
    (c : ℕ) : ℕ :=
  (c + 12) * ((minimalBlocksPrim hmb).k + (preimagePrim hpre).k + 7) +
    (c + 6) * (4 * ((pointwiseStabPrim hps).k + 9)) + (2 * c + 12)

/-- A monomial bound with a smaller exponent gives one with a larger exponent. -/
theorem scosBig_mono_pow {a A E D : ℕ} (h : a ≤ A * (n + 1) ^ E) (hED : E ≤ D) :
    a ≤ A * (n + 1) ^ D :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hED))

theorem scosBigS_le (n c : ℕ) : scosBigS n c ≤ 2 ^ (c + 13) * (n + 1) ^ (c + 12) := by
  have hM := scosPasteM_le n c
  have hQ : (n + n + 1) ^ 6 ≤ 2 ^ 6 * (n + 1) ^ 6 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 6
  calc scosBigS n c ≤ (2 ^ (c + 7) * (n + 1) ^ (c + 6)) * (2 ^ 6 * (n + 1) ^ 6) :=
        Nat.mul_le_mul hM hQ
    _ = 2 ^ (c + 13) * (n + 1) ^ (c + 12) := by ring

theorem scosBig_boundSize_le (p : Prim) (n c : ℕ) :
    p.boundSize (100000 * scosBigS n c) ≤
      p.c * (100002 * 2 ^ (c + 13)) ^ p.k * (n + 1) ^ ((c + 12) * p.k) := by
  have hS := scosBigS_le n c
  have h1 : 1 ≤ 2 ^ (c + 13) * (n + 1) ^ (c + 12) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : 100000 * scosBigS n c + 2 ≤ 100002 * 2 ^ (c + 13) * (n + 1) ^ (c + 12) := by
    have := Nat.mul_le_mul_left 100000 hS
    have e : 100002 * 2 ^ (c + 13) * (n + 1) ^ (c + 12) =
      100000 * (2 ^ (c + 13) * (n + 1) ^ (c + 12)) + 2 * (2 ^ (c + 13) * (n + 1) ^ (c + 12)) := by
      ring
    omega
  unfold Prim.boundSize
  calc p.c * (100000 * scosBigS n c + 2) ^ p.k ≤
      p.c * (100002 * 2 ^ (c + 13) * (n + 1) ^ (c + 12)) ^ p.k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ = p.c * (100002 * 2 ^ (c + 13)) ^ p.k * (n + 1) ^ ((c + 12) * p.k) := by
        rw [mul_pow, pow_mul]; ring

theorem scosBigD_le (n c : ℕ) :
    20 * scosBigD n c ≤ 20 * (10 ^ 40 * (c + 1) * (2 ^ (c + 13)) ^ 7) * (n + 1) ^ ((c + 12) * 7) := by
  have hS := Nat.pow_le_pow_left (scosBigS_le n c) 7
  unfold scosBigD
  calc 20 * (10 ^ 40 * (c + 1) * scosBigS n c ^ 7) ≤
      20 * (10 ^ 40 * (c + 1) * (2 ^ (c + 13) * (n + 1) ^ (c + 12)) ^ 7) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS)
    _ = 20 * (10 ^ 40 * (c + 1) * (2 ^ (c + 13)) ^ 7) * (n + 1) ^ ((c + 12) * 7) := by
        rw [mul_pow, pow_mul]; ring

/-- **The own cost of function 5 is a polynomial in `n`.** -/
theorem scosOwnG_le (hps : PointwiseStab) (hpre : Preimage) (hmb : MinimalBlocks) (n c : ℕ) :
    scosOwnG hps hpre hmb n c ≤ scosBigK hps hpre hmb c * (n + 1) ^ scosBigE hps hpre hmb c := by
  have e1 := scosBig_mono_pow (D := scosBigE hps hpre hmb c)
    (scosBig_boundSize_le (minimalBlocksPrim hmb) n c) (by
      unfold scosBigE; rw [Nat.mul_add, Nat.mul_add]; omega)
  have e2 := scosBig_mono_pow (D := scosBigE hps hpre hmb c)
    (scosBig_boundSize_le (preimagePrim hpre) n c) (by
      unfold scosBigE; rw [Nat.mul_add, Nat.mul_add]; omega)
  have e3 := scosBig_mono_pow (D := scosBigE hps hpre hmb c) (scosOwnP_le hps n c) (by
      unfold scosBigE; omega)
  have e4 := scosBig_mono_pow (D := scosBigE hps hpre hmb c) (scosOwnC_le n c) (by
      unfold scosBigE; omega)
  have e5 := scosBig_mono_pow (D := scosBigE hps hpre hmb c) (scosBigD_le n c) (by
      unfold scosBigE; rw [Nat.mul_add, Nat.mul_add]; omega)
  unfold scosOwnG scosBigK
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  generalize (n + 1) ^ scosBigE hps hpre hmb c = Y at *
  omega

end GI.Impl
