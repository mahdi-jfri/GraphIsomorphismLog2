import Workspace.Impl.SCosNode
import Workspace.Impl.SCosBase
import Workspace.Impl.SCosSolveMath

/-!
# The recursion, by induction on `|Φ|`

`scos_solve_all`: on every problem, the solve function returns a correct answer at cost at most
`scosT Q c 𝒢 Φ`, for any `Q` that bounds the own costs of one node. The transitive step with at
least two points enters as the hypothesis `hG` (the shape of `scos_big_spec`).

The induction is on `k = |Φ|`. At a level `k`, the problems whose group is not transitive on
`Φ` come first (`scos_level_intrans`): they split into two smaller problems. Then all problems
of the level: a transitive problem with `|Φ| ≥ 2` has children on the same `Φ` under the
kernel `K`, which is not transitive, so the first part applies to them.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

section Solve

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The shape of the transitive step with at least two points (`scos_big_spec`). -/
def ScosBigHyp (c : ℕ) (hps : PointwiseStab) (hpre : Preimage) (hmb : MinimalBlocks)
    (n OG OC : ℕ) : Prop :=
  ∀ (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n) (Φ : Finset (Fin n)),
    ScosProb n v 𝒢 x Φ → ScosTrans 𝒢 Φ → 2 ≤ Φ.card →
    ∀ T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ,
    (∀ (K : Subgroup (ScosPair n)) (v' : Val) (x' : ScosPair n), K ≤ 𝒢 → ScosProb n v' K x' Φ →
      scosMo K Φ < Φ.card →
        FunAll (scosProgram c hps hpre hmb) 0 v' (fun w c' => ScosAns n w x' K Φ ∧ c' ≤ T K Φ)) →
    FunAll (scosProgram c hps hpre hmb) 5 v (fun w cost => ScosAns n w x 𝒢 Φ ∧
      ∃ (K : Subgroup (ScosPair n)) (m s ℓ : ℕ), K ≤ 𝒢 ∧ 2 ≤ m ∧ 1 ≤ s ∧ m * s ≤ Φ.card ∧
        ℓ ≤ (m + 1) ^ c ∧ scosMo K Φ ≤ s ∧ cost ≤ OG + ℓ * (OC + T K Φ))

/-- The own costs of one node are at most `Q`. -/
structure ScosQ (hps : PointwiseStab) (n Q OG OC : ℕ) : Prop where
  e : scosOwnE n ≤ Q
  b : scosOwnN n + scosOwnB hps n ≤ Q
  g : scosOwnN n + OG ≤ Q
  ch : OC ≤ Q
  nn : scosOwnN n ≤ Q

/-- The recursive calls on the two parts of an intransitive split, by the induction
hypothesis. -/
theorem scos_hrec {Q k : ℕ}
    (IH : ∀ k' < k, ∀ (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n)
      (Φ : Finset (Fin n)), Φ.card = k' → ScosProb n v 𝒢 x Φ →
        FunAll (𝒫) 0 v (fun w cost => ScosAns n w x 𝒢 Φ ∧ cost ≤ scosT Q c 𝒢 Φ))
    {Φ : Finset (Fin n)} (hk : Φ.card = k) :
    ∀ v' 𝒢' x' Φ', ScosProb n v' 𝒢' x' Φ' → Φ' ⊂ Φ → 𝒢' ≤ 𝒢' →
      FunAll (𝒫) 0 v' (fun w c' => ScosAns n w x' 𝒢' Φ' ∧ c' ≤ scosT Q c 𝒢' Φ') :=
  fun v' 𝒢' x' Φ' hv' hsub _ =>
    IH Φ'.card (hk ▸ Finset.card_lt_card hsub) v' 𝒢' x' Φ' rfl hv'

/-- The intransitive split, as a bound by `scosT`. -/
theorem scos_split_bound {Q cost : ℕ} {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)}
    (hN : scosOwnN n ≤ Q) {O : Finset (Fin n)} (hO1 : O.Nonempty) (hOΦ : O ⊂ Φ)
    (hO : ∃ a ∈ O, ∀ b, b ∈ O ↔ b ∈ Φ ∧ ∃ g ∈ 𝒢, g.1 a = b)
    (hc : cost ≤ scosOwnN n + scosT Q c 𝒢 O + scosT Q c (scosL 𝒢 O) (Φ \ O)) :
    cost ≤ scosT Q c 𝒢 Φ := by
  obtain ⟨a, ha, hOa⟩ := hO
  exact hc.trans (scosT_split hN (scosL_le 𝒢 O) hOΦ hO1 (scosMo_orbit_card ha hOa))

/-- **Intransitive problems of a level.** -/
theorem scos_level_intrans {Q k : ℕ}
    (IH : ∀ k' < k, ∀ (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n)
      (Φ : Finset (Fin n)), Φ.card = k' → ScosProb n v 𝒢 x Φ →
        FunAll (𝒫) 0 v (fun w cost => ScosAns n w x 𝒢 Φ ∧ cost ≤ scosT Q c 𝒢 Φ))
    (hE : scosOwnE n ≤ Q) (hN : scosOwnN n ≤ Q)
    (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n) (Φ : Finset (Fin n))
    (hk : Φ.card = k) (hv : ScosProb n v 𝒢 x Φ) (hmo : scosMo 𝒢 Φ < Φ.card) :
    FunAll (𝒫) 0 v (fun w cost => ScosAns n w x 𝒢 Φ ∧ cost ≤ scosT Q c 𝒢 Φ) := by
  have hnt : ¬ ScosTrans 𝒢 Φ := fun ht => by rw [scosMo_trans ht] at hmo; omega
  have hrec : ∀ v' 𝒢' x' Φ', ScosProb n v' 𝒢' x' Φ' → Φ' ⊂ Φ → 𝒢' ≤ 𝒢 →
      FunAll (𝒫) 0 v' (fun w c' => ScosAns n w x' 𝒢' Φ' ∧ c' ≤ scosT Q c 𝒢' Φ') :=
    fun v' 𝒢' x' Φ' hv' hsub _ => scos_hrec IH hk v' 𝒢' x' Φ' hv' hsub le_rfl
  refine (scos_solve_step hv (scosT Q c) hrec (fun _ => False) (fun _ => False)
    (fun ht => absurd ht hnt) (fun ht => absurd ht hnt)).mono fun w cost h => ⟨h.1, ?_⟩
  rcases h.2 with ⟨rfl, hc⟩ | ⟨O, hO1, hOΦ, hO, hc⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
  · exact scosT_empty 𝒢 (hc.trans hE)
  · exact scos_split_bound hN hO1 hOΦ hO hc
  · exact absurd ht hnt
  · exact absurd ht hnt

/-- **All problems**, by strong induction on `|Φ|`. -/
theorem scos_solve_all {Q OG OC : ℕ} (hQ : ScosQ hps n Q OG OC)
    (hG : ScosBigHyp c hps hpre hmb n OG OC) :
    ∀ (k : ℕ) (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n) (Φ : Finset (Fin n)),
      Φ.card = k → ScosProb n v 𝒢 x Φ →
        FunAll (𝒫) 0 v (fun w cost => ScosAns n w x 𝒢 Φ ∧ cost ≤ scosT Q c 𝒢 Φ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro v 𝒢 x Φ hk hv
  have hrec : ∀ v' 𝒢' x' Φ', ScosProb n v' 𝒢' x' Φ' → Φ' ⊂ Φ → 𝒢' ≤ 𝒢 →
      FunAll (𝒫) 0 v' (fun w c' => ScosAns n w x' 𝒢' Φ' ∧ c' ≤ scosT Q c 𝒢' Φ') :=
    fun v' 𝒢' x' Φ' hv' hsub _ => scos_hrec IH hk v' 𝒢' x' Φ' hv' hsub le_rfl
  have hbase : ScosTrans 𝒢 Φ → Φ.card = 1 → FunAll (𝒫) 4 v
      (fun w c' => ScosAns n w x 𝒢 Φ ∧ c' ≤ scosOwnB hps n) :=
    fun _ h1 => scos_base_spec hv h1
  have hbig : ScosTrans 𝒢 Φ → 2 ≤ Φ.card → FunAll (𝒫) 5 v (fun w cost => ScosAns n w x 𝒢 Φ ∧
      ∃ (K : Subgroup (ScosPair n)) (m s ℓ : ℕ), K ≤ 𝒢 ∧ 2 ≤ m ∧ 1 ≤ s ∧ m * s ≤ Φ.card ∧
        ℓ ≤ (m + 1) ^ c ∧ scosMo K Φ ≤ s ∧ cost ≤ OG + ℓ * (OC + scosT Q c K Φ)) :=
    fun ht h2 => hG v 𝒢 x Φ hv ht h2 (scosT Q c) fun K v' x' _ hv' hmo =>
      scos_level_intrans IH hQ.e hQ.nn v' K x' Φ hk hv' hmo
  refine (scos_solve_step hv (scosT Q c) hrec _ _ hbase hbig).mono fun w cost h => ⟨h.1, ?_⟩
  rcases h.2 with ⟨rfl, hc⟩ | ⟨O, hO1, hOΦ, hO, hc⟩ | ⟨-, -, cb, hcb, hc⟩ |
    ⟨ht, h2, cg, ⟨K, m, s, ℓ, -, hm, hs, hms, hℓ, hK, hcg⟩, hc⟩
  · exact scosT_empty 𝒢 (hc.trans hQ.e)
  · exact scos_split_bound hQ.nn hO1 hOΦ hO hc
  · exact scosT_base 𝒢 Φ ((hc.trans (Nat.add_le_add_left hcb _)).trans hQ.b)
  · have h1 : cost ≤ (scosOwnN n + OG) + ℓ * (OC + scosT Q c K Φ) := by omega
    exact h1.trans (scosT_big hQ.g hQ.ch ht h2 hm hs hms hℓ hK)

end Solve

end GI.Impl
