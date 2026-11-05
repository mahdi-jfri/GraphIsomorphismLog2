module

public import Workspace.Proved.SolvOrder
public import Workspace.Cited.DixonDerivedLength

@[expose] public section

/-!
# Derived length of solvable permutation groups: the reduction to primitive groups

We write `solvL n = Nat.log 3 (n^5)`, the largest `t` with `3^t ≤ n^5`. It satisfies
`solvL m + solvL k ≤ solvL (m k)` and `solvL n ≤ 5 log₃ n`.

`GI.Proved.solvDL_of_primitive` proves `GI.Cited.DixonDerivedLength` from the primitive case:
if every primitive solvable group of degree `n` has `S^{(solvL n)} = 1` (assuming the result for
all smaller degrees), then every solvable group of degree `n` does. The reduction is the same as
for the order (`Workspace/Proved/SolvOrder.lean`): an orbit and its complement give `max`, a
block system gives a sum.
-/

namespace GI.Proved

open MulAction Pointwise

universe u

/-- `solvL n = ⌊5 log₃ n⌋`, computed as `Nat.log 3 (n^5)`. -/
def solvL (n : ℕ) : ℕ := Nat.log 3 (n ^ 5)

theorem solvL_add_le (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : solvL m + solvL k ≤ solvL (m * k) := by
  unfold solvL
  apply Nat.le_log_of_pow_le (by norm_num)
  rw [pow_add, mul_pow]
  exact Nat.mul_le_mul (Nat.pow_log_le_self 3 (by positivity))
    (Nat.pow_log_le_self 3 (by positivity))

theorem solvL_mono {m n : ℕ} (h : m ≤ n) : solvL m ≤ solvL n :=
  Nat.log_mono_right (Nat.pow_le_pow_left h 5)

/-- If `S^{(a)} ≤ K`, then `S^{(a+b)}` lies in the image of `K^{(b)}`. -/
theorem solv_derivedSeries_add_le {G : Type*} [Group G] (K : Subgroup G) (a : ℕ)
    (h : derivedSeries G a ≤ K) :
    ∀ b, derivedSeries G (a + b) ≤ (derivedSeries K b).map K.subtype := by
  intro b
  induction b with
  | zero =>
    simpa [derivedSeries_zero, ← MonoidHom.range_eq_map] using h
  | succ b ih =>
    rw [← add_assoc, derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator]
    exact Subgroup.commutator_mono ih ih

/-- Derived series through an injective homomorphism. -/
theorem solv_derivedSeries_eq_bot_of_injective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) (n : ℕ) (h : derivedSeries G' n = ⊥) :
    derivedSeries G n = ⊥ := by
  have h1 := map_derivedSeries_le_derivedSeries f n
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hf] at h1
  exact h1

/-- The induction hypothesis: the bound holds in every smaller nonempty degree. -/
def SolvDLIH (n : ℕ) : Prop :=
  ∀ (β : Type u) [Finite β], 1 ≤ Nat.card β → Nat.card β < n →
    ∀ G : Subgroup (Equiv.Perm β), IsSolvable G → derivedSeries G (solvL (Nat.card β)) = ⊥

theorem SolvDLIH.range {n : ℕ} (ih : SolvDLIH.{u} n) {H : Type*} [Group H] [Group.IsSolvable H]
    {β : Type u} [Finite β] (hβ : 1 ≤ Nat.card β) (hβn : Nat.card β < n)
    (ρ : H →* Equiv.Perm β) : derivedSeries ρ.range (solvL (Nat.card β)) = ⊥ :=
  ih β hβ hβn ρ.range (solvable_of_surjective ρ.rangeRestrict_surjective)

/-- `derivedSeries` vanishes from a smaller index on. -/
theorem solv_derivedSeries_bot_mono {G : Type*} [Group G] {a b : ℕ} (hab : a ≤ b)
    (h : derivedSeries G a = ⊥) : derivedSeries G b = ⊥ :=
  le_bot_iff.mp (h ▸ derivedSeries_antitone G hab)

/-- An element of `G^{(t)}` is killed by every homomorphism whose image has trivial `t`-th
derived subgroup. -/
theorem solv_map_derived_eq_one {G H : Type*} [Group G] [Group H] (ρ : G →* H) (t : ℕ)
    (h : derivedSeries ρ.range t = ⊥) {x : G} (hx : x ∈ derivedSeries G t) : ρ x = 1 := by
  have h1 := map_derivedSeries_le_derivedSeries ρ.rangeRestrict t
  rw [h, le_bot_iff] at h1
  have h2 : ρ.rangeRestrict x = 1 := by
    have : ρ.rangeRestrict x ∈ (derivedSeries G t).map ρ.rangeRestrict := ⟨x, hx, rfl⟩
    rw [h1] at this
    exact this
  exact congrArg Subtype.val h2

/-- The intransitive step. -/
theorem solvDL_intransitive {α : Type u} [Finite α] (ih : SolvDLIH.{u} (Nat.card α))
    (G : Subgroup (Equiv.Perm α)) [Group.IsSolvable G] (s : Set α)
    (hs : ∀ (g : G) (x : α), g • x ∈ s ↔ x ∈ s) (hne : s.Nonempty) (hne' : sᶜ.Nonempty) :
    derivedSeries G (solvL (Nat.card α)) = ⊥ := by
  have hs' : ∀ (g : G) (x : α), g • x ∈ sᶜ ↔ x ∈ sᶜ := fun g x => not_congr (hs g x)
  have hsum : Nat.card s + Nat.card (sᶜ : Set α) = Nat.card α := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_add_ncard_compl]
  have h1 : 1 ≤ Nat.card s := by
    rw [Nat.card_coe_set_eq]
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr hne).ne'
  have h2 : 1 ≤ Nat.card (sᶜ : Set α) := by
    rw [Nat.card_coe_set_eq]
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr hne').ne'
  have hb1 := solv_derivedSeries_bot_mono (solvL_mono (by omega : Nat.card s ≤ Nat.card α))
    (ih.range h1 (by omega) (solvRes s hs))
  have hb2 := solv_derivedSeries_bot_mono
    (solvL_mono (by omega : Nat.card (sᶜ : Set α) ≤ Nat.card α))
    (ih.range h2 (by omega) (solvRes sᶜ hs'))
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have e1 := solv_map_derived_eq_one _ _ hb1 hg
  have e2 := solv_map_derived_eq_one _ _ hb2 hg
  apply eq_of_smul_eq_smul (α := α)
  intro x
  rw [one_smul]
  by_cases hx : x ∈ s
  · exact congrArg Subtype.val (Equiv.ext_iff.mp e1 ⟨x, hx⟩)
  · exact congrArg Subtype.val (Equiv.ext_iff.mp e2 ⟨x, hx⟩)

/-- The imprimitive step. -/
theorem solvDL_imprimitive {α : Type u} [Finite α] (ih : SolvDLIH.{u} (Nat.card α))
    (G : Subgroup (Equiv.Perm α)) [Group.IsSolvable G] [IsPretransitive G α] (B : Set α)
    (hB : IsBlock G B) (hBnt : ¬ IsTrivialBlock B) :
    derivedSeries G (solvL (Nat.card α)) = ⊥ := by
  classical
  rw [IsTrivialBlock, not_or] at hBnt
  obtain ⟨hBs, hBu⟩ := hBnt
  have hBnt' : B.Nontrivial := Set.not_subsingleton_iff.mp hBs
  have hBne : B.Nonempty := hBnt'.nonempty
  set m := B.ncard with hm
  have hm2 : 1 < m := (Set.one_lt_ncard_iff_nontrivial).mpr hBnt'
  have hmn : m < Nat.card α := Set.ncard_lt_card hBu
  let Ω := orbit G B
  have hmk : m * Nat.card Ω = Nat.card α := by
    rw [Nat.card_coe_set_eq]; exact hB.ncard_block_mul_ncard_orbit_eq hBne
  set k := Nat.card Ω with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hmk; omega
    · exact h
  have hkn : k < Nat.card α := by
    rw [← hmk]; exact lt_mul_left (by omega) hm2
  let φ := MulAction.toPermHom G Ω
  have hφ := ih.range hk1 hkn φ
  let K := φ.ker
  haveI : Group.IsSolvable K := solvable_of_solvable_injective K.subtype_injective
  let ψ : ∀ C : Ω, K →* Equiv.Perm C.1 :=
    fun C => solvRes C.1 (fun x v => solvKer_mem_iff G B x C v)
  have hCcard : ∀ C : Ω, Nat.card C.1 = m := by
    intro C
    obtain ⟨g, hg⟩ := C.2
    rw [Nat.card_coe_set_eq, ← hg]
    exact Set.ncard_smul_set _ _
  have hψ : ∀ C : Ω, derivedSeries (ψ C).range (solvL m) = ⊥ := by
    intro C
    have h := ih.range (β := C.1) (by rw [hCcard]; omega) (by rw [hCcard]; exact hmn) (ψ C)
    rwa [hCcard] at h
  -- `G^{(solvL k)}` lies in the kernel.
  have hK : derivedSeries G (solvL k) ≤ K := fun g hg => solv_map_derived_eq_one φ _ hφ hg
  have hKb : derivedSeries K (solvL m) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hC : ∀ C : Ω, ψ C x = 1 := fun C => solv_map_derived_eq_one (ψ C) _ (hψ C) hx
    apply eq_of_smul_eq_smul (α := α)
    intro v
    rw [one_smul]
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨g, rfl⟩ := exists_smul_eq G b v
    let C : Ω := ⟨g • B, mem_orbit B g⟩
    have hv : g • b ∈ C.1 := Set.smul_mem_smul_set hb
    exact congrArg Subtype.val (Equiv.ext_iff.mp (hC C) ⟨g • b, hv⟩)
  have h1 := solv_derivedSeries_add_le K (solvL k) hK (solvL m)
  rw [hKb, Subgroup.map_bot, le_bot_iff] at h1
  apply solv_derivedSeries_bot_mono _ h1
  calc solvL k + solvL m = solvL m + solvL k := add_comm _ _
    _ ≤ solvL (m * k) := solvL_add_le m k (by omega) hk1
    _ = solvL (Nat.card α) := by rw [hmk]

/-- The primitive case, with the induction hypothesis for smaller degrees available. -/
def SolvDLPrimitive : Prop :=
  ∀ (α : Type) [Finite α], 1 ≤ Nat.card α → SolvDLIH.{0} (Nat.card α) →
    ∀ G : Subgroup (Equiv.Perm α), IsSolvable G → IsPreprimitive G α → Nontrivial G →
      derivedSeries G (solvL (Nat.card α)) = ⊥

theorem solvDL_aux (hP : SolvDLPrimitive) : ∀ (n : ℕ) (α : Type) [Finite α], Nat.card α = n →
    1 ≤ n → ∀ G : Subgroup (Equiv.Perm α), IsSolvable G → derivedSeries G (solvL n) = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α _ hα hn G hG
  haveI : Group.IsSolvable G := hG
  subst hα
  have ih' : SolvDLIH.{0} (Nat.card α) := fun β _ h1 hlt G hG => ih _ hlt β rfl h1 G hG
  by_cases hnt : Nontrivial G
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact Subgroup.eq_bot_of_subsingleton _
  by_cases ht : IsPretransitive G α
  swap
  · have hex : ∃ a b : α, ∀ g : G, g • a ≠ b := by
      by_contra h
      push Not at h
      exact ht ⟨fun a b => h a b⟩
    obtain ⟨a, b, hab⟩ := hex
    refine solvDL_intransitive ih' G (orbit G a) ?_ ⟨a, mem_orbit_self a⟩ ⟨b, ?_⟩
    · intro g x
      rw [← orbit_eq_iff, orbit_smul, orbit_eq_iff]
    · rintro ⟨g, hg⟩
      exact hab g hg
  by_cases hp : IsPreprimitive G α
  · exact hP α hn ih' G hG hp hnt
  · have hex : ∃ B : Set α, IsBlock G B ∧ ¬ IsTrivialBlock B := by
      by_contra h
      push Not at h
      exact hp { toIsPretransitive := ht, isTrivialBlock_of_isBlock := fun hB => h _ hB }
    obtain ⟨B, hB, hBnt⟩ := hex
    exact solvDL_imprimitive ih' G B hB hBnt

/-- `solvL n ≤ 5 log₃ n`. -/
theorem solvL_le_logb (n : ℕ) (hn : 1 ≤ n) : (solvL n : ℝ) ≤ 5 * Real.logb 3 n := by
  have hpos : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
  rw [show (5 : ℝ) * Real.logb 3 n = Real.logb 3 ((n : ℝ) ^ 5) by
    rw [Real.logb_pow]; push_cast; ring, Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 3 (by positivity : n ^ 5 ≠ 0)

/-- **Dixon's derived length bound from the primitive case.** -/
theorem solvDL_of_primitive (hP : SolvDLPrimitive) : GI.Cited.DixonDerivedLength := by
  intro n S hS k hk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subgroup.eq_bot_of_subsingleton _
  have h := solvDL_aux hP n (Fin n) (by simp) hn S hS
  apply solv_derivedSeries_bot_mono _ h
  exact_mod_cast (solvL_le_logb n hn).trans hk

end GI.Proved
