import Workspace.Proved.VsMHardA
import Workspace.Proved.Palfy

/-!
# The hard case, part B (Pálfy on `Ȳ`, the pieces, **M6**)

`H` acts on `Ȳ = Y / (Y ∩ S)` by conjugation. `Ȳ` is an elementary abelian `r`-group, and the
action is irreducible by minimality of `Y`. Pálfy's bound (`palfy_affine_core`) gives
`|H : K| ≤ |Ȳ|^69` for the units `K = vsMKer S Y` that normalize `S` and act trivially on `Ȳ`.
Elements of `K` move `t_i = e_i λ_i⁻¹` and `ζ` only by scalars, so `VsMSplitHyp.pieces` bounds
the index of the stabilizer of the pieces in `H ∩ K` by `r^k · r`. This proves `vsM_hard`.
-/

namespace GI.Proved

open Module
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "𝔼" => End (ZMod p) V

/-- The units that normalize `S` and act trivially on `Y` modulo `S`. -/
def vsMKer (S Y : Subgroup 𝔼ˣ) : Subgroup 𝔼ˣ where
  carrier := {g | (∀ s ∈ S, g * s * g⁻¹ ∈ S ∧ g⁻¹ * s * g ∈ S) ∧
    ∀ z ∈ Y, z⁻¹ * (g * z * g⁻¹) ∈ S ∧ z⁻¹ * (g⁻¹ * z * g) ∈ S}
  mul_mem' := by
    rintro g g' ⟨hgS, hgY⟩ ⟨hg'S, hg'Y⟩
    refine ⟨fun s hs => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
    · have : g * g' * s * (g * g')⁻¹ = g * (g' * s * g'⁻¹) * g⁻¹ := by group
      rw [this]; exact (hgS _ (hg'S s hs).1).1
    · have : (g * g')⁻¹ * s * (g * g') = g'⁻¹ * (g⁻¹ * s * g) * g' := by group
      rw [this]; exact (hg'S _ (hgS s hs).2).2
    · have : z⁻¹ * (g * g' * z * (g * g')⁻¹) =
          (z⁻¹ * (g * z * g⁻¹)) * (g * (z⁻¹ * (g' * z * g'⁻¹)) * g⁻¹) := by group
      rw [this]; exact S.mul_mem (hgY z hz).1 (hgS _ (hg'Y z hz).1).1
    · have : z⁻¹ * ((g * g')⁻¹ * z * (g * g')) =
          (z⁻¹ * (g'⁻¹ * z * g')) * (g'⁻¹ * (z⁻¹ * (g⁻¹ * z * g)) * g') := by group
      rw [this]; exact S.mul_mem (hg'Y z hz).2 (hg'S _ (hgY z hz).2).2
  one_mem' := ⟨fun s hs => by simpa using hs, fun z _ => by simp [S.one_mem]⟩
  inv_mem' := by
    rintro g ⟨hgS, hgY⟩
    refine ⟨fun s hs => ?_, fun z hz => ?_⟩
    · rw [inv_inv]; exact ⟨(hgS s hs).2, (hgS s hs).1⟩
    · rw [inv_inv]; exact ⟨(hgY z hz).2, (hgY z hz).1⟩

variable {H A Y : Subgroup (End (ZMod p) V)ˣ} {r : ℕ}

/-- Elements of `K` move `y l⁻¹` (`y ∈ Y`, `l ∈ S`) only by a scalar. -/
theorem VsMHard.ker_comm (h : VsMHard H A Y r) {g : 𝔼ˣ} (hg : g ∈ vsMKer (vsMScal A) Y)
    {y l : 𝔼ˣ} (hy : y ∈ Y) (hl : l ∈ vsMScal A) : ⁅g, y * l⁻¹⁆ ∈ vsMScal A := by
  have hc : y⁻¹ * (g * y * g⁻¹) * (g * l⁻¹ * g⁻¹) * l ∈ vsMScal A :=
    mul_mem (mul_mem (hg.2 y hy).1 (hg.1 _ (inv_mem hl)).1) hl
  have e1 : ⁅g, y * l⁻¹⁆ = y * (y⁻¹ * (g * y * g⁻¹) * (g * l⁻¹ * g⁻¹) * l) * y⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e1, h.scal_comm hy hc, mul_inv_cancel_right]
  exact hc

/-- **Pálfy on `Ȳ`.** The units of `H` acting trivially on `Ȳ` (and normalizing `S`) have
index at most `|Ȳ|^69`. -/
theorem VsMHard.ker_index [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (h : VsMHard H A Y r) :
    (H ⊓ vsMKer (vsMScal A) Y).relIndex H ≤ (vsMScal A).relIndex Y ^ 69 := by
  classical
  haveI : Fact r.Prime := ⟨h.prime⟩
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  haveI : Finite 𝔼 := Module.finite_of_finite (ZMod p)
  set S := vsMScal A with hSdef
  have hSn : VsMNorm H S := vsM_scal_norm h.abn
  let Yb : Subgroup Y := S.subgroupOf Y
  haveI hYbn : Yb.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have : ((g * n * g⁻¹ : Y) : 𝔼ˣ) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h.scal_comm g.2 hn, mul_inv_cancel_right]
    rw [this]; exact hn⟩
  letI instC : CommGroup (Y ⧸ Yb) :=
    { (inferInstance : Group (Y ⧸ Yb)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have hc := h.comm _ (Y.inv_mem b.2) _ (Y.inv_mem a.2)
        have : (((a * b)⁻¹ * (b * a) : Y) : 𝔼ˣ) = ⁅(b : 𝔼ˣ)⁻¹, (a : 𝔼ˣ)⁻¹⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
        rw [this]; exact hc }
  letI instM : Module (ZMod r) (Additive (Y ⧸ Yb)) := AddCommGroup.zmodModule (fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, ofMul_eq_zero]
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← hy, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, SubgroupClass.coe_pow]
    exact h.pow y y.2)
  -- the conjugation action of `H` on `Ȳ`
  let φ : H → (Y →* Y) := fun g =>
    { toFun := fun y => ⟨(g : 𝔼ˣ) * y * (g : 𝔼ˣ)⁻¹, h.norm g g.2 y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : ∀ g : H, Yb ≤ Yb.comap (φ g) := fun g n hn => by
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hSn g g.2 n hn
  let σ : H → (Y ⧸ Yb →* Y ⧸ Yb) := fun g => QuotientGroup.map Yb Yb (φ g) (hφ g)
  have hσ : ∀ (g : H) (y : Y), σ g (y : Y ⧸ Yb) = ((φ g y : Y) : Y ⧸ Yb) := fun g y => rfl
  letI act : MulDistribMulAction H (Y ⧸ Yb) :=
    { smul := fun g x => σ g x
      one_smul := fun x => by
        induction x using QuotientGroup.induction_on with | H y => ?_
        show σ 1 (y : Y ⧸ Yb) = y
        rw [hσ]; congr 1
      mul_smul := fun g g' x => by
        induction x using QuotientGroup.induction_on with | H y => ?_
        show σ (g * g') (y : Y ⧸ Yb) = σ g (σ g' y)
        rw [hσ, hσ, hσ]; congr 1
      smul_mul := fun g a b => map_mul (σ g) a b
      smul_one := fun g => map_one (σ g) }
  let ρ : H →* MulAut (Y ⧸ Yb) := MulDistribMulAction.toMulAut H (Y ⧸ Yb)
  have hρ : ∀ (g : H) (y : Y), ρ g (y : Y ⧸ Yb) = ((φ g y : Y) : Y ⧸ Yb) := fun g y => rfl
  haveI : IsSolvable H := h.solv
  haveI : IsSolvable ρ.range := solvable_of_surjective ρ.rangeRestrict_surjective
  haveI : Nontrivial (Y ⧸ Yb) := by
    obtain ⟨x, hx, y, hy, hxy⟩ := h.nab
    refine ⟨⟨((⟨x, hx⟩ : Y) : Y ⧸ Yb), 1, fun h1 => hxy ?_⟩⟩
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact (h.scal_comm hy h1).symm
  have hirr : ∀ W : Subgroup (Y ⧸ Yb), (∀ τ ∈ ρ.range, ∀ w ∈ W, τ w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    rcases Subgroup.bot_or_exists_ne_one W with hb | ⟨xb, hxbW, hxb1⟩
    · exact Or.inl hb
    right
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective xb
    have hwS : (w : 𝔼ˣ) ∉ S := fun hS =>
      hxb1 ((QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hS))
    let W' : Subgroup 𝔼ˣ := (W.comap (QuotientGroup.mk' Yb)).map Y.subtype
    have hW'Y : W' ≤ Y := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hspin : vsMSpin H w ≤ W' := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨φ ⟨g, hg⟩ w, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply, ← hρ]
      exact hW _ ⟨⟨g, hg⟩, rfl⟩ _ hxbW
    have hle := h.min w w.2 hwS
    rw [eq_top_iff]
    intro zb _
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zb
    have hz : (z : 𝔼ˣ) ∈ W' ⊔ S := sup_le_sup_right hspin _ (hle z.2)
    obtain ⟨a, ha, c, hc, hac⟩ :=
      vsM_mem_sup_comm (fun a ha c hc => h.scal_comm (hW'Y ha) hc) hz
    obtain ⟨a', ha'W, rfl⟩ := ha
    have e1 : ((z : Y) : Y ⧸ Yb) = (a' : Y ⧸ Yb) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : ((z⁻¹ * a' : Y) : 𝔼ˣ) = c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hac, Subgroup.coe_subtype]; group
      rw [this]; exact inv_mem hc
    rw [e1]
    exact ha'W
  have hpal := palfy_affine_core r ρ.range hirr
  -- the index of the kernel
  have hidx : (H ⊓ vsMKer S Y).relIndex H ≤ Nat.card ρ.range := by
    have hb := vsM_relIndex_le (H ⊓ vsMKer S Y) H
      (fun g => if hg : g ∈ H then ρ ⟨g, hg⟩ else 1) (ρ.range : Set (MulAut (Y ⧸ Yb)))
      (Set.toFinite _) (fun g hg => by simp only [dif_pos hg]; exact ⟨⟨g, hg⟩, rfl⟩) ?_
    · rwa [← Nat.card_coe_set_eq] at hb
    · intro g hg g' hg' hf
      simp only [dif_pos hg, dif_pos hg'] at hf
      have hx : g⁻¹ * g' ∈ H := H.mul_mem (H.inv_mem hg) hg'
      have h1 : ρ ⟨g⁻¹ * g', hx⟩ = 1 := by
        rw [show (⟨g⁻¹ * g', hx⟩ : H) = ⟨g, hg⟩⁻¹ * ⟨g', hg'⟩ from rfl, map_mul, map_inv, hf,
          inv_mul_cancel]
      have h2 : ρ ⟨(g⁻¹ * g')⁻¹, H.inv_mem hx⟩ = 1 := by
        rw [show (⟨(g⁻¹ * g')⁻¹, H.inv_mem hx⟩ : H) = (⟨g⁻¹ * g', hx⟩ : H)⁻¹ from rfl, map_inv,
          h1, inv_one]
      have htriv : ∀ (x : 𝔼ˣ) (hxH : x ∈ H), ρ ⟨x, hxH⟩ = 1 → ∀ z ∈ Y, z⁻¹ * (x * z * x⁻¹) ∈ S := by
        intro x hxH hρ1 z hz
        have := DFunLike.congr_fun hρ1 ((⟨z, hz⟩ : Y) : Y ⧸ Yb)
        rw [hρ, MulAut.one_apply, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
        simpa [φ] using this
      refine ⟨hx, fun s hs => ⟨hSn _ hx s hs, ?_⟩, fun z hz => ⟨htriv _ hx h1 z hz, ?_⟩⟩
      · have := hSn _ (H.inv_mem hx) s hs
        rwa [inv_inv] at this
      · have := htriv _ (H.inv_mem hx) h2 z hz
        rwa [inv_inv] at this
  have hcard : Nat.card (Y ⧸ Yb) = S.relIndex Y := rfl
  calc (H ⊓ vsMKer S Y).relIndex H ≤ Nat.card ρ.range := hidx
    _ ≤ Nat.card ρ.range ^ 3 := Nat.le_self_pow (by norm_num) _
    _ ≤ Nat.card (Y ⧸ Yb) ^ 69 := hpal
    _ = S.relIndex Y ^ 69 := by rw [hcard]

/-- **M6** (LM §5.5). In the hard case with a maximal good isotropic `E` of dimension `k`:
`|Ȳ| ≤ r^(2k+2)`, `k = 0` only for `r = 2`, and `𝔽_p[A ∪ E]` splits `V` into exactly `r^k`
pieces of equal dimension whose stabilizer has index at most `|Ȳ|^69 · r · r^k` in `H`. -/
theorem vsM_hard [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMHardStmt p V := by
  intro H A Y r k e h he
  refine ⟨h.index_le he, h.r_two he, ?_⟩
  classical
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  haveI : Finite 𝔼 := Module.finite_of_finite (ZMod p)
  obtain ⟨ζ, hζ, hζ1, hζr⟩ := h.exists_zeta
  choose l hlS hl using he.2.1
  obtain ⟨t, ht⟩ : ∃ t : Fin k → 𝔼ˣ, ∀ i, t i = e i * (l i)⁻¹ := ⟨_, fun _ => rfl⟩
  have hel : ∀ i j, Commute (e i) (l j) := fun i j => h.scal_comm (he.1 i) (hlS j)
  have hll : ∀ i j, Commute (l i) (l j) := fun i j => vsM_scal_comm h.hA (hlS i) (hlS j)
  have hsplit : VsMSplitHyp A r ζ t :=
    { hA := h.hA, hdom := h.dom, hr := h.prime, hζ := hζ, hζ1 := hζ1, hζr := hζr
      htA := fun i => by
        rw [ht i]
        exact Subgroup.mul_mem _ (h.cent (he.1 i))
          (Subgroup.inv_mem _ (vsM_scal_le_centralizer h.hA (hlS i)))
      htt := fun i j => by
        rw [ht i, ht j]
        exact (Commute.mul_left (Commute.mul_right (he.2.2.1 i j) (hel i j).inv_right)
          (Commute.mul_right (hel j i).symm (hll i j).inv_right).inv_left).eq
      htr := fun i => by
        rw [ht i, ((hel i i).inv_right).mul_pow, inv_pow, hl i, mul_inv_cancel] }
  have hEq : vsMAlgE A e = vsMAlgE A t := by
    apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro _ (hx | ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · show ((e i : 𝔼ˣ) : 𝔼) ∈ vsMAlgE A t
        have : ((e i : 𝔼ˣ) : 𝔼) = (t i : 𝔼) * (l i : 𝔼) := by
          rw [← Units.val_mul, ht i, inv_mul_cancel_right]
        rw [this]
        exact mul_mem (hsplit.t_mem i) (hsplit.L_le (hlS i).1)
    · refine Algebra.adjoin_le ?_
      rintro _ (hx | ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · show ((t i : 𝔼ˣ) : 𝔼) ∈ vsMAlgE A e
        rw [ht i, Units.val_mul]
        exact mul_mem (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
          (Algebra.adjoin_mono Set.subset_union_left (hlS i).2)
  obtain ⟨s, hsY, hs⟩ := h.shifts he hζ hζ1 hζr
  have hst : ∀ i j, s i * t j * (s i)⁻¹ = if j = i then ζ * t j else t j := by
    intro i j
    have hc : (l j)⁻¹ * (s i)⁻¹ = (s i)⁻¹ * (l j)⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, h.scal_comm (hsY i) (hlS j)]
    have e1 : s i * t j * (s i)⁻¹ = ⁅s i, e j⁆ * t j := by
      rw [ht j, commutatorElement_def]
      calc s i * (e j * (l j)⁻¹) * (s i)⁻¹ = s i * e j * ((l j)⁻¹ * (s i)⁻¹) := by group
        _ = s i * e j * ((s i)⁻¹ * (l j)⁻¹) := by rw [hc]
        _ = s i * e j * (s i)⁻¹ * (e j)⁻¹ * (e j * (l j)⁻¹) := by group
    rw [e1, hs i j]
    split_ifs <;> simp
  rw [hEq]
  obtain ⟨π, hπ⟩ := hsplit.idem
  refine ⟨hsplit.reduced hπ, @fun ι f hfB hf hspan => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsplit.pieces s (fun i => h.cent (hsY i)) hst f hfB hf hspan
  refine ⟨h1, h2, ?_⟩
  have hK := h3 (H ⊓ vsMKer (vsMScal A) Y) (fun g hg =>
    ⟨fun i => by rw [ht i]; exact h.ker_comm hg.2 (he.1 i) (hlS i), (hg.2.1 ζ hζ).1⟩)
  have hKH := h.ker_index
  have hne : (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1) ⊓
      (H ⊓ vsMKer (vsMScal A) Y)).relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)).relIndex H
      ≤ (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1) ⊓
          (H ⊓ vsMKer (vsMScal A) Y)).relIndex H :=
        Subgroup.relIndex_le_of_le_left inf_le_left hne
    _ = (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)).relIndex
          ((H ⊓ vsMKer (vsMScal A) Y) ⊓ H) * (H ⊓ vsMKer (vsMScal A) Y).relIndex H :=
        (Subgroup.relIndex_inf_mul_relIndex _ _ _).symm
    _ = (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)).relIndex
          (H ⊓ vsMKer (vsMScal A) Y) * (H ⊓ vsMKer (vsMScal A) Y).relIndex H := by
        rw [inf_eq_left.2 inf_le_left]
    _ ≤ (r ^ k * r) * (vsMScal A).relIndex Y ^ 69 := Nat.mul_le_mul hK hKH
    _ = (vsMScal A).relIndex Y ^ 69 * r * r ^ k := by ring

end GI.Proved
