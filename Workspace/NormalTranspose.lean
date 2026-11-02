import Workspace.TowerRank
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group

/-! Group theory used in the proof of Lemma A.14 (`lem:normal-transpose`).

* the modular index split (eq. `modular-index-split`): for `N ◁ H` and
  `L' ≤ L ≤ H`, `[L : L'] = [L ∩ N : L' ∩ N] [NL : NL']`;
* the lower action: with `B = L ∩ NP` and `B' = L' ∩ NP` (`P ≤ L'`),
  `B ∩ L' = B'`, `B = (L ∩ N) P`, and `[B : B'] = [L ∩ N : L' ∩ N]`;
* the upper action: `L` is transitive on the cosets of `NL'` in `NL`, with
  base-coset stabilizer `L ∩ NL'`, and `N` acts trivially;
* `f(a) + f(b) ≤ f(ab)` for `f(r) = 2⌊log₂ r⌋ - 1`, `f(1) = 0`
  (`GI.towerRank`), so `ρ` does not increase;
* the interchange of the ratio sequence inside `Alt(m) × Q`.

Here `NL` is written `N ⊔ L`; it is the set of products because `N` is
normal. Lean's cosets are left cosets; the paper's right cosets give the same
indices and equivalent actions. -/

namespace GI.NormalTranspose

open Subgroup

section Modular

variable {H : Type*} [Group H] (N : Subgroup H) [N.Normal]

theorem relIndex_ne_zero_of_finite [Finite H] (A C : Subgroup H) : A.relIndex C ≠ 0 := by
  intro h
  have hd := relIndex_dvd_card (H := A) (K := C)
  rw [h, zero_dvd_iff] at hd
  exact (Nat.card_pos (α := C)).ne' hd

/-- The paper's eq. `modular-index-split`:
`[L_i : L_{i-1}] = [L_i ∩ N : L_{i-1} ∩ N] [N L_i : N L_{i-1}]`. -/
theorem modular_index_split [Finite H] {L' L : Subgroup H} (hle : L' ≤ L) :
    L'.relIndex L = (L' ⊓ N).relIndex (L ⊓ N) * (N ⊔ L').relIndex (N ⊔ L) := by
  -- Two chains from `N ∩ L'` up to `L`.
  have h1 := relIndex_mul_relIndex (N ⊓ L') L' L inf_le_right hle
  have h2 := relIndex_mul_relIndex (N ⊓ L') (N ⊓ L) L (inf_le_inf_left N hle) inf_le_right
  -- `[N L : N] = [L : N ∩ L]`, and the chain `N ≤ N L' ≤ N L`.
  have h3 := relIndex_mul_relIndex N (N ⊔ L') (N ⊔ L) le_sup_left (sup_le_sup_left hle N)
  rw [relIndex_sup_left, relIndex_sup_left] at h3
  rw [inf_relIndex_right] at h1 h2
  have hne : N.relIndex L' ≠ 0 := relIndex_ne_zero_of_finite N L'
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
  rw [h1, ← h2, ← h3, inf_comm L' N, inf_comm L N]
  ring

/-- Dedekind's rule in the form used for `B_i`: for `P ≤ L`,
`L ∩ NP = (L ∩ N) P`. -/
theorem inf_sup_eq_of_le {P L : Subgroup H} (hPL : P ≤ L) :
    L ⊓ (N ⊔ P) = (L ⊓ N) ⊔ P := by
  apply le_antisymm
  · rintro x ⟨hxL, hx⟩
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_sup_of_normal_left.mp hx
    have hnL : n ∈ L := by
      have h := L.mul_mem hxL (L.inv_mem (hPL hp))
      rwa [mul_inv_cancel_right] at h
    exact mul_mem_sup ⟨hnL, hn⟩ hp
  · exact sup_le (inf_le_inf_left L le_sup_left) (le_inf hPL le_sup_right)

omit [N.Normal] in
/-- The lower groups: `B_i ∩ L_{i-1} = B_{i-1}` for `B_i = L_i ∩ NP`. -/
theorem lower_inf {P L' L : Subgroup H} (hle : L' ≤ L) :
    (L ⊓ (N ⊔ P)) ⊓ L' = L' ⊓ (N ⊔ P) := by
  rw [inf_right_comm, inf_of_le_right hle]

omit [N.Normal] in
/-- The lower action: an element of `B_i` fixes the base coset of `L_{i-1}`
in `L_i` exactly when it lies in `B_{i-1}`. So the `B_i`-orbit of the base
coset, in the old action of `L_i` on the cosets of `L_{i-1}`, is the action of
`B_i` on the cosets of `B_{i-1}`. -/
theorem lower_stabilizer {P L' L : Subgroup H} (x : L) (hx : x.val ∈ N ⊔ P) :
    x • ((1 : L) : L ⧸ L'.subgroupOf L) = ((1 : L) : L ⧸ L'.subgroupOf L) ↔
      x.val ∈ L' ⊓ (N ⊔ P) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff, mem_subgroupOf]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

/-- The lower index: `[B_i : B_{i-1}] = [L_i ∩ N : L_{i-1} ∩ N]`. -/
theorem lower_index [Finite H] {P L' L : Subgroup H} (hPL' : P ≤ L') (hle : L' ≤ L) :
    (L' ⊓ (N ⊔ P)).relIndex (L ⊓ (N ⊔ P)) = (L' ⊓ N).relIndex (L ⊓ N) := by
  have hsplit := modular_index_split N (L := L ⊓ (N ⊔ P)) (L' := L' ⊓ (N ⊔ P))
    (inf_le_inf_right _ hle)
  -- `B ∩ N = L ∩ N`, and `NB = NP` for both lower groups.
  have hN : ∀ L₀ : Subgroup H, L₀ ⊓ (N ⊔ P) ⊓ N = L₀ ⊓ N := by
    intro L₀
    rw [inf_assoc, inf_of_le_right (le_sup_left : N ≤ N ⊔ P)]
  have hsup : ∀ L₀ : Subgroup H, P ≤ L₀ → N ⊔ (L₀ ⊓ (N ⊔ P)) = N ⊔ P := by
    intro L₀ hP
    apply le_antisymm
    · exact sup_le le_sup_left inf_le_right
    · exact sup_le le_sup_left (le_sup_of_le_right (le_inf hP le_sup_right))
  rw [hN, hN, hsup L' hPL', hsup L (hPL'.trans hle), relIndex_self, mul_one] at hsplit
  exact hsplit

/-- The upper action is transitive: every coset of `N L_{i-1}` in `N L_i`
contains an element of `L_i`. -/
theorem upper_transitive {L' L : Subgroup H} (y : H) (hy : y ∈ N ⊔ L) :
    ∃ x ∈ L, y⁻¹ * x ∈ N ⊔ L' := by
  obtain ⟨n, hn, l, hl, rfl⟩ := mem_sup_of_normal_left.mp hy
  refine ⟨l, hl, ?_⟩
  have : (n * l)⁻¹ * l = l⁻¹ * n⁻¹ * l := by group
  rw [this]
  exact Subgroup.mem_sup_left ((inferInstance : N.Normal).conj_mem' _ (N.inv_mem hn) l)

/-- `N` acts trivially on the cosets of `N L_{i-1}`. -/
theorem upper_normal_trivial {L' : Subgroup H} (n y : H) (hn : n ∈ N) :
    (n * y)⁻¹ * y ∈ N ⊔ L' := by
  have : (n * y)⁻¹ * y = y⁻¹ * n⁻¹ * y := by group
  rw [this]
  exact Subgroup.mem_sup_left ((inferInstance : N.Normal).conj_mem' _ (N.inv_mem hn) y)

/-- The upper action is a block quotient of the old constituent:
`L_{i-1} ≤ L_i ∩ N L_{i-1} ≤ L_i`, and its degree is
`[N L_i : N L_{i-1}] = [L_i : L_i ∩ N L_{i-1}]`. -/
theorem upper_index [Finite H] {L' L : Subgroup H} (hle : L' ≤ L) :
    L' ≤ L ⊓ (N ⊔ L') ∧ (N ⊔ L').relIndex (N ⊔ L) = (L ⊓ (N ⊔ L')).relIndex L := by
  refine ⟨le_inf hle le_sup_right, ?_⟩
  have hX : L' ≤ L ⊓ (N ⊔ L') := le_inf hle le_sup_right
  have hchain := relIndex_mul_relIndex L' (L ⊓ (N ⊔ L')) L hX inf_le_left
  -- `[L_i ∩ N L_{i-1} : L_{i-1}] = [L_i ∩ N : L_{i-1} ∩ N]` (the lower index with `P = L_{i-1}`).
  have hlow := lower_index N (P := L') le_rfl hle
  have hself : L' ⊓ (N ⊔ L') = L' := inf_of_le_left le_sup_right
  rw [hself] at hlow
  rw [hlow, modular_index_split N hle] at hchain
  have hne : (L' ⊓ N).relIndex (L ⊓ N) ≠ 0 := relIndex_ne_zero_of_finite _ _
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hchain).symm

end Modular

section Rho

/-- `f(a) + f(b) ≤ f(ab)` for `f(r) = 2⌊log₂ r⌋ - 1` and `f(1) = 0`. -/
theorem towerRank_add_le_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    towerRank a + towerRank b ≤ towerRank (a * b) := by
  by_cases ha1 : a = 1
  · subst ha1
    simp [towerRank]
  by_cases hb1 : b = 1
  · subst hb1
    simp [towerRank]
  have h := tower_rank_split (a := a) (b := b) (by omega) (by omega)
  omega

/-- `ρ` of a sequence of ratios. -/
def rho (l : List ℕ) : ℤ := (l.map towerRank).sum

/-- Splitting every ratio `d = ab` of a tower into a lower factor `a` and an
upper factor `b` does not increase `ρ`. -/
theorem rho_split_le (l : List (ℕ × ℕ)) (hpos : ∀ p ∈ l, 0 < p.1 ∧ 0 < p.2) :
    rho (l.map Prod.fst) + rho (l.map Prod.snd) ≤ rho (l.map fun p => p.1 * p.2) := by
  induction l with
  | nil => simp [rho]
  | cons p l ih =>
    have hp := hpos p (by simp)
    have hl := ih (fun q hq => hpos q (List.mem_cons_of_mem p hq))
    simp only [rho, List.map_cons, List.sum_cons] at hl ⊢
    have := towerRank_add_le_mul hp.1 hp.2
    linarith

end Rho

section Interchange

variable {A Q : Type*} [Group A] [Group Q]

/-- "Each intermediate subgroup contains `Alt(m-1) × 1` and is therefore exactly
`Alt(m-1) × V`": a subgroup between `A₁ × 1` and `A₁ × Q` is `A₁ × V` for its
projection `V` to `Q`. -/
theorem prod_intermediate (A₁ : Subgroup A) (X : Subgroup (A × Q))
    (hlow : A₁.prod ⊥ ≤ X) (hhigh : X ≤ A₁.prod ⊤) :
    X = A₁.prod (X.map (MonoidHom.snd A Q)) := by
  ext ⟨a, q⟩
  constructor
  · intro hx
    exact ⟨(hhigh hx).1, ⟨(a, q), hx, rfl⟩⟩
  · rintro ⟨ha, ⟨⟨a', q'⟩, hx', hq⟩⟩
    change q' = q at hq
    subst hq
    have ha' : a' ∈ A₁ := (hhigh hx').1
    have hlowmem : (a * a'⁻¹, (1 : Q)) ∈ X :=
      hlow ⟨A₁.mul_mem ha (A₁.inv_mem ha'), Subgroup.mem_bot.mpr rfl⟩
    have := X.mul_mem hlowmem hx'
    simpa using this

theorem relIndex_prod [Finite A] [Finite Q] {A₀ A₁ : Subgroup A} {V₀ V₁ : Subgroup Q}
    (hA : A₀ ≤ A₁) (hV : V₀ ≤ V₁) :
    (A₀.prod V₀).relIndex (A₁.prod V₁) = A₀.relIndex A₁ * V₀.relIndex V₁ := by
  have h1 := relIndex_mul_index (Subgroup.prod_mono hA hV)
  have h2 := relIndex_mul_index hA
  have h3 := relIndex_mul_index hV
  rw [index_prod, index_prod, ← h2, ← h3] at h1
  have hne : A₁.index * V₁.index ≠ 0 :=
    Nat.mul_ne_zero (index_ne_zero_of_finite) (index_ne_zero_of_finite)
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne)
  rw [h1]
  ring

/-- The interchange of the ratio sequence. For a chain `V₀ ≤ ⋯ ≤ V_s = Q`, the
old chain `A₁ × V₀ ≤ ⋯ ≤ A₁ × Q ≤ A × Q` has ratios `r₁, …, r_s, m` and the new
chain `A₁ × V₀ ≤ A × V₀ ≤ ⋯ ≤ A × Q` has ratios `m, r₁, …, r_s`, with
`r_l = [V_l : V_{l-1}]` and `m = [A : A₁]`. -/
theorem ratio_interchange [Finite A] [Finite Q] (A₁ : Subgroup A) {V₀ V₁ : Subgroup Q}
    (hV : V₀ ≤ V₁) :
    (A₁.prod V₀).relIndex (A₁.prod V₁) = V₀.relIndex V₁ ∧
      ((⊤ : Subgroup A).prod V₀).relIndex ((⊤ : Subgroup A).prod V₁) = V₀.relIndex V₁ ∧
      (A₁.prod V₀).relIndex ((⊤ : Subgroup A).prod V₀) = A₁.index := by
  refine ⟨?_, ?_, ?_⟩
  · rw [relIndex_prod le_rfl hV, relIndex_self, one_mul]
  · rw [relIndex_prod le_rfl hV, relIndex_self, one_mul]
  · rw [relIndex_prod le_top le_rfl, relIndex_self, mul_one, relIndex_top_right]

end Interchange

end GI.NormalTranspose
