import Workspace.Paper.QuotientAlgorithms
import Workspace.RadicalIndex
import Workspace.RadicalCentralizers

/-!
# Paper statements: "A radical-free order bound and its constructive use"

Appendix A, subsubsection after Theorem A.20 (`lem:radical-free-order` and the first step of
`cor:transitive-kernel-multicoset`).

* `a(Q)`, `b(Q)`: `GI.Composition.aFac`, `GI.Composition.bFac`, the products of the orders of
  the abelian and the nonabelian composition factors. A composition series with products
  `a`, `b` is `GI.Cited.CompositionProducts Q a b` (trusted definition). Well defined:
  `GI.Paper.def_composition_products`. Facts used by the proof (`Workspace/CompositionFactors.lean`):
  `bFac_mul` (`b(Q) = b(K) b(Q/K)` for `K ◁ Q`), `aFac_mul`, `bFac_of_solvable`,
  `bFac_of_simple`, `aFac_mul_bFac` (`a(Q) b(Q) = |Q|`), `aFac_congr`, `bFac_congr`; for the
  socle `E` of a radical-free `Q₀`: `GI.RadicalFreeOrder.card_socle_le_bFac` (`|E| ≤ b(Q₀)`).
* Lemma A.21: `GI.Paper.lem_radical_free_order`.
* The paragraph after Lemma A.21 (mathematical content; the polynomial-time clause is stage 2):
  `GI.Paper.par_radical_chief_centralizers`, `GI.Paper.par_radical_preimage_centralizers`.
* The first displayed step of the proof of Corollary A.22:
  `GI.Paper.cor_transitive_kernel_multicoset_index`, and in the form of the hypothesis `hidx`,
  `GI.Paper.cor_transitive_kernel_multicoset_hidx`.
* Corollary A.22 and Theorem A.23 without `hidx`, with `N` transitive:
  `GI.Paper.cor_transitive_kernel_multicoset_transitive`,
  `GI.Paper.thm_transitive_gat_terminal_transitive`.

The cited inputs ([GMP, Proposition 6.1, Lemma 7.7, Theorem 1.4]) are the hypotheses
`hAb : GI.Cited.GMPAbelianFactors`, `hOut : GI.Cited.GMPOutBound`,
`hTr : GI.Cited.GMPTransitiveNonabelian` (`Workspace/Cited/GMP.lean`).

One step uses less than the paper: the paper says "since every `|T_i| ≥ 60`"; the inequality
`2 · 24^{1/3} < √|T_i|` only needs `|T_i| ≥ 34`, which `GI.SmallSimple.thirtyfour_le_card`
proves without the classification.
-/

namespace GI.Paper

open GI.Cited GI.Composition GI.Multicoset

universe u

/-- **`a(Q)` and `b(Q)` are well defined** (the definitions before Lemma A.21). Every finite
group has a composition series, and any two give the same products `a` and `b`
(Jordan-Hölder). `GI.Composition.aFac`, `bFac` are these products. -/
theorem def_composition_products (Q : Type u) [Group Q] [Finite Q] :
    CompositionProducts Q (aFac Q) (bFac Q) ∧
      ∀ a b : ℕ, CompositionProducts Q a b → a = aFac Q ∧ b = bFac Q :=
  ⟨spec Q, fun _ _ h => ⟨(aFac_eq h).symm, (bFac_eq h).symm⟩⟩

/-- **Lemma A.21** (`lem:radical-free-order`). For every finite group `Q`,
`|Q/Rad(Q)| ≤ b(Q)²`. Proved from [GMP, Proposition 6.1] and [GMP, Lemma 7.7]. -/
theorem lem_radical_free_order (hAb : GMPAbelianFactors) (hOut : GMPOutBound)
    (Q : Type u) [Group Q] [Finite Q] :
    Nat.card (Q ⧸ GI.RadicalSocle.solvableRadical Q) ≤ bFac Q ^ 2 :=
  GI.RadicalFreeOrder.card_radical_quotient_le hAb hOut Q

/-- **Paragraph after Lemma A.21**, for a finite group `Q` with a chief series `s`: the
solvable radical is the intersection, over the nonabelian chief factors `U/V = s(i+1)/s(i)`,
of the preimages of `C_{Q/V}(U/V)`. -/
theorem par_radical_chief_centralizers {Q : Type u} [Group Q] [Finite Q] {n : ℕ}
    {s : ℕ → Subgroup Q} (hs : GI.RadicalCentralizers.IsChiefSeries n s) :
    GI.RadicalSocle.solvableRadical Q =
      ⨅ (i : ℕ) (_ : i < n) (_ : ¬ ⁅s (i + 1), s (i + 1)⁆ ≤ s i),
        GI.RadicalCentralizers.centPre (s (i + 1)) (s i) (hs.normal i) :=
  GI.RadicalCentralizers.radical_eq_centInter hs

/-- **Paragraph after Lemma A.21**, for `N ◁ H`: the radical preimage `R` is the preimage in
`H` of that intersection, for any chief series of `H/N`. -/
theorem par_radical_preimage_centralizers {B : Type u} [Fintype B]
    {H N : Subgroup (Equiv.Perm B)} [(N.subgroupOf H).Normal] {n : ℕ}
    {s : ℕ → Subgroup (H ⧸ N.subgroupOf H)} (hs : GI.RadicalCentralizers.IsChiefSeries n s) :
    radicalPreimage H N =
      ((⨅ (i : ℕ) (_ : i < n) (_ : ¬ ⁅s (i + 1), s (i + 1)⁆ ≤ s i),
        GI.RadicalCentralizers.centPre (s (i + 1)) (s i) (hs.normal i)).comap
          (QuotientGroup.mk' (N.subgroupOf H))).map H.subtype := by
  rw [radicalPreimage, dif_pos (inferInstance : (N.subgroupOf H).Normal),
    par_radical_chief_centralizers hs]

/-- **Corollary A.22, first step of the proof**: for `N ◁ H ≤ Sym(B)` with `N` transitive,
`Q = H/N` and `R` the radical preimage, `[H : R] ≤ b(Q)² ≤ b^{2 log₂ b}`
("Theorem 1.4 of [GMP] and Lemma A.21 give ..."). -/
theorem cor_transitive_kernel_multicoset_index (hAb : GMPAbelianFactors) (hOut : GMPOutBound)
    (hTr : GMPTransitiveNonabelian) {B : Type u} [Fintype B]
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B) :
    ((radicalPreimage H N).subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 ∧
    ((bFac (H ⧸ N.subgroupOf H) ^ 2 : ℕ) : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)) :=
  GI.RadicalIndex.radical_index_chain hAb hOut hTr hNH htr

/-- The radical index bound in exactly the form of the hypothesis `hidx` of
`cor_transitive_kernel_multicoset` and `thm_transitive_gat_terminal`. -/
theorem cor_transitive_kernel_multicoset_hidx (hAb : GMPAbelianFactors) (hOut : GMPOutBound)
    (hTr : GMPTransitiveNonabelian) {B : Type u} [Fintype B]
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B) :
    (((radicalPreimage H N).subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)) :=
  GI.RadicalIndex.radical_index_le hAb hOut hTr hNH htr

/-- **Corollary A.22** (`cor:transitive-kernel-multicoset`), stage 1, with `N` transitive as
in the paper. Same conclusions as `cor_transitive_kernel_multicoset`; the hypothesis `hidx`
is discharged by `cor_transitive_kernel_multicoset_hidx`. -/
theorem cor_transitive_kernel_multicoset_transitive (dixon : GI.Cited.DixonDerivedLength)
    (hAb : GMPAbelianFactors) (hOut : GMPOutBound) (hTr : GMPTransitiveNonabelian)
    {B : Type u} [Fintype B] [DecidableEq B] {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] (htr : MulAction.IsPretransitive N B)
    {κ : Type u} (L : κ → Subgroup (Equiv.Perm B)) (hL : ∀ c, N ≤ L c ∧ L c ≤ H)
    (X Y : Multiset (CObj κ (Equiv.Perm B)))
    (hXo : ∀ o ∈ X, ∃ c, ∃ h ∈ H, o = cobj L c h) (hYo : ∀ o ∈ Y, ∃ c, ∃ h ∈ H, o = cobj L c h)
    (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M) :
    (radicalTransport H N X Y).set = Iso H X Y ∧
    ((radicalTransport H N X Y).calls : ℝ) ≤
      Real.exp (45 * (Real.log ((Fintype.card B : ℝ) + 2) ^ 2 +
        Real.log ((M : ℝ) + 2) * Real.log ((Fintype.card B : ℝ) + 2))) :=
  cor_transitive_kernel_multicoset dixon hNH
    (cor_transitive_kernel_multicoset_hidx hAb hOut hTr hNH htr) L hL X Y hXo hYo M hX hY

/-- **Theorem A.23** (`thm:transitive-gat-terminal`), stage 1, with `N` transitive as in the
paper. Same conclusions as `thm_transitive_gat_terminal`; the hypothesis `hidx` is discharged
by `cor_transitive_kernel_multicoset_hidx`. -/
theorem thm_transitive_gat_terminal_transitive (dixon : GI.Cited.DixonDerivedLength)
    (hAb : GMPAbelianFactors) (hOut : GMPOutBound) (hTr : GMPTransitiveNonabelian)
    {B : Type u} [Fintype B] [DecidableEq B] {Ω : Type u} [RAct (Equiv.Perm B) Ω]
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B)
    {A : Type*} [CommGroup A] (φ : N →* A) {m : ℕ} (k : Equiv.Perm B → Fin m → Equiv.Perm B)
    (hk : ∀ h ∈ H, ∀ i, h⁻¹ * k h i ∈ N)
    (x y : Fin m → Ω) :
    terminalTransport H N φ k x y = isoG H N φ k x y ∧
    (∀ p ∈ isoG H N φ k x y, ∃ h ∈ H, types N x ↼ h = types N y ∧
      ∃ μ, InJ N φ μ p.2 ∧ p.1 = k h * μ) ∧
    (∀ (z : Fin m → Ω) (π : Equiv.Perm (Fin m)), π ∈ alternatingGroup (Fin m) →
      ∀ n : Fin m → Equiv.Perm B, (∀ i, n i ∈ N) → (∀ i, x i ↼ n i = z (π i)) →
        ((∃ μ, InJ N φ μ π ∧ rowAct μ π x = z) ↔ ∏ i, phiT N φ (n i) ∈ labelGroup N φ x)) ∧
    (∀ (z : Fin m → Ω) (i j : Fin m), i ≠ j → ∀ c ∈ N, x i ↼ c = x j →
      ((∃ π ∈ alternatingGroup (Fin m), LabelOK N φ x z π) ↔ ∃ π, LabelOK N φ x z π)) ∧
    ((radicalTransport H N (types N x) (types N y)).calls : ℝ) ≤
      Real.exp (45 * (Real.log ((Fintype.card B : ℝ) + 2) ^ 2 +
        Real.log ((m : ℝ) + 2) * Real.log ((Fintype.card B : ℝ) + 2))) ∧
    terminalStringCalls m ≤ 3 * (m + 1) ^ 2 :=
  thm_transitive_gat_terminal dixon hNH φ k hk
    (cor_transitive_kernel_multicoset_hidx hAb hOut hTr hNH htr) x y

end GI.Paper
