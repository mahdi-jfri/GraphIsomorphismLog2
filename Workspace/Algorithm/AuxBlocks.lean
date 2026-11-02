import Workspace.Algorithm.AggregationPlan
import Workspace.Algorithm.Cases
import Workspace.AlternatingSubsetTransitive

/-!
# The Johnson block map from the kernel-orbit map (Corollary A.25)

Lemma A.11 starts from "its actual equivariant block map `p : Ω → binom(Γ, h)`, `1 ≤ h ≤ q/2`".
In the recursion this map comes from Corollary A.25 (`GI.Paper.cor_physical_support_thresholds`):
when `q > λ = N^α`, the kernel orbits of the transitive action on the domain are indexed by one
label, by an ordered pair of labels, or by an unordered pair of labels. Section 6.2: "The support
classification therefore gives precisely the one-label and two-label cases."

This file turns each of the three outcomes into a `JohnsonBlocks` (`h = 1` for one label, `h = 2`
for both kinds of pairs) and proves the existence statement `exists_blocks`: for all large `N`,
every transitive state with `q > N^α` has its Johnson block map. The fibers of the block map have
equal size because the even permutations move any `h`-set to any other and lift to the action
(`JohnsonBlocks.ofMap`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.StabilizerQuotient Pointwise

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The label map on the domain action is onto, since `π` is. -/
theorem πd_surjective {πd : S.domGroup →* alternatingGroup (Fin L.q)}
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) : Function.Surjective πd := by
  intro a
  obtain ⟨g, rfl⟩ := L.π_surj a
  exact ⟨_, hπ g⟩

/-- The domain action of a transitive state is transitive. -/
theorem domGroup_pretransitive (htr : S.Transitive) :
    MulAction.IsPretransitive S.domGroup S.dom := by
  refine ⟨fun v w => ?_⟩
  obtain ⟨g, hg, h⟩ := htr v.1 v.2 w.1 w.2
  exact ⟨⟨S.domHom ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩, Subtype.ext h⟩

theorem map_eq_smul {q : ℕ} (τ : Perm (Fin q)) (s : Finset (Fin q)) :
    s.map τ.toEmbedding = τ • s := by
  ext b
  rw [Finset.mem_map_equiv, Finset.mem_smul_finset]
  constructor
  · intro h; exact ⟨_, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

/-- **Johnson blocks from an equivariant block map.** All fibers have the size of the fiber of
the first `h` labels: an even permutation moves those labels to any other `h`-set
(`exists_alternating_finset_eq`), and a lift of it to the action maps fiber to fiber. -/
noncomputable def JohnsonBlocks.ofMap (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (h : ℕ) (p : S.dom → Finset (Fin L.q))
    (hp : ∀ (g : S.domGroup) v,
      p ((g : Perm S.dom) v) = (p v).map ((πd g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)).toEmbedding)
    (card : ∀ v, (p v).card = h) (one_le : 1 ≤ h) (half : 2 * h ≤ L.q) (hq : 3 ≤ L.q) :
    JohnsonBlocks S L where
  h := h
  f := Nat.card {v : S.dom // p v = Finset.univ.map (Fin.castLEEmb (by omega : h ≤ L.q))}
  p := p
  equivariant g v := by
    have e := hp ⟨S.domHom g, g, rfl⟩ v
    rw [hπ] at e
    exact e
  card := card
  fibers Bl hBl := by
    classical
    set Bl₀ := Finset.univ.map (Fin.castLEEmb (by omega : h ≤ L.q))
    obtain ⟨σ, hσ⟩ := GI.AlternatingActions.exists_alternating_finset_eq (by simpa using hq) Bl₀ Bl
      (by rw [hBl, Finset.card_map, Finset.card_univ, Fintype.card_fin])
    obtain ⟨g, hg⟩ := πd_surjective hπ σ
    symm
    refine Nat.card_congr
      { toFun := fun v => ⟨(g : Perm S.dom) v.1, ?_⟩
        invFun := fun v => ⟨((g⁻¹ : S.domGroup) : Perm S.dom) v.1, ?_⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
    · rw [hp, hg, v.2, map_eq_smul, hσ]
    · have e := hp g (((g⁻¹ : S.domGroup) : Perm S.dom) v.1)
      have e2 : (g : Perm S.dom) (((g⁻¹ : S.domGroup) : Perm S.dom) v.1) = v.1 := by simp
      rw [e2, v.2, hg] at e
      exact (smul_left_cancel _ (hσ.trans (e.trans (map_eq_smul _ _)))).symm
  one_le := one_le
  half := half

/-- **The support classification at phase size `N`** (Corollary A.25 at the scale `q > λ`,
Section 6.2: "For `q > λ` and sufficiently large `N`, we have `C(q,3) > N`. Also `q` exceeds the
logarithmic transitive-kernel threshold. The support classification therefore gives precisely
the one-label and two-label cases"): every transitive group on at most `N` points with a map
onto `Alt(Γ)`, `|Γ| > N^α`, has a kernel-orbit quotient onto the single labels, the ordered
pairs or the unordered pairs of `Γ`. -/
def SupportCases (α : ℝ) (N : ℕ) : Prop :=
  ∀ {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
    (G : Subgroup (Equiv.Perm Ω)) [MulAction.IsPretransitive G Ω]
    (φ : G →* alternatingGroup Γ), Function.Surjective φ →
    Fintype.card Ω ≤ N → (N : ℝ) ^ α < Fintype.card Γ →
    (Nonempty (KernelQuotient φ Ω Γ) ∨
      Nonempty (KernelQuotient φ Ω (GI.Pairs.OrderedPair Γ)) ∨
      Nonempty (KernelQuotient φ Ω (GI.Johnson.SubsetVertex Γ 2)))

/-- Corollary A.25 gives the support classification for all large `N`
(`large_giant_support_cases`). -/
theorem supportCases_of_large (hcite : GI.Cited.TransitiveAffected) {α : ℝ} (hα : 1 / 3 < α) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → SupportCases α N :=
  large_giant_support_cases hcite hα

/-- **The support classification gives the Johnson block map** when `q > N^α`: every transitive
state with `q > N^α` labels and at most `N` domain points has a Johnson block map with `h = 1`
(natural labels) or `h = 2` (ordered or unordered pairs of labels). -/
theorem blocks_of_cases {α : ℝ} {Ω C : Type} {S : State Ω C} (L : GiantLabels S)
    (hc : SupportCases α S.N) (fin : Finite Ω)
    (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (htr : S.Transitive)
    (hsize : S.size ≤ S.N) (hq : 4 ≤ L.q) (hlam : (S.N : ℝ) ^ α < L.q) :
    Nonempty (JohnsonBlocks S L) := by
  classical
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  haveI := domGroup_pretransitive htr
  have hcard : Fintype.card S.dom ≤ S.N := by
    rw [← Nat.card_eq_fintype_card]; exact hsize
  have hlam' : (S.N : ℝ) ^ α < Fintype.card (Fin L.q) := by rw [Fintype.card_fin]; exact hlam
  rcases hc S.domGroup πd (πd_surjective hπ) hcard hlam' with hQ | hQ | hQ
  · obtain ⟨Q⟩ := hQ
    refine ⟨JohnsonBlocks.ofMap πd hπ 1 (fun v => {Q.map v}) (fun g v => ?_) (fun v => by simp)
      le_rfl (by omega) (by omega)⟩
    have e := Q.equivariant g v
    simp only [Finset.map_singleton]
    exact congrArg _ e
  · obtain ⟨Q⟩ := hQ
    refine ⟨JohnsonBlocks.ofMap πd hπ 2 (fun v => {(Q.map v).1.1, (Q.map v).1.2})
      (fun g v => ?_) (fun v => Finset.card_pair (Q.map v).2) (by norm_num) (by omega) (by omega)⟩
    have e := Q.equivariant g v
    simp only [Finset.map_insert, Finset.map_singleton]
    change {(Q.map (g • v)).1.1, (Q.map (g • v)).1.2} = _
    rw [e]
    rfl
  · obtain ⟨Q⟩ := hQ
    refine ⟨JohnsonBlocks.ofMap πd hπ 2 (fun v => (Q.map v).1) (fun g v => ?_)
      (fun v => (Q.map v).2) (by norm_num) (by omega) (by omega)⟩
    have e := Q.equivariant g v
    change (Q.map (g • v)).1 = _
    rw [e, map_eq_smul]
    rfl

/-- **Corollary A.25 gives the Johnson block map** when `q > N^α`: for all large `N`, every
transitive state with `q > N^α` labels and at most `N` domain points has a Johnson block map with
`h = 1` (natural labels) or `h = 2` (ordered or unordered pairs of labels). -/
theorem exists_blocks (hcite : GI.Cited.TransitiveAffected) {α : ℝ} (hα : 1 / 3 < α) :
    ∃ N₁ : ℕ, ∀ {Ω C : Type} {S : State Ω C} (L : GiantLabels S) (fin : Finite Ω)
      (πd : S.domGroup →* alternatingGroup (Fin L.q)),
      (∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) → S.Transitive →
      N₁ ≤ S.N → S.size ≤ S.N → 4 ≤ L.q → (S.N : ℝ) ^ α < L.q → Nonempty (JohnsonBlocks S L) := by
  obtain ⟨N₁, hN₁⟩ := supportCases_of_large hcite hα
  exact ⟨N₁, fun L fin πd hπ htr hN hsize hq hlam =>
    blocks_of_cases L (hN₁ _ hN) fin πd hπ htr hsize hq hlam⟩

end GI.Algorithm
