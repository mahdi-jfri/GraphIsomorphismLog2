import Workspace.OrbitBudget
import Workspace.OrbitLocalization
import Workspace.BlockPartition
import Workspace.CartesianHereditary
import Workspace.JohnsonBound

/-!
# Paper, Appendix A, Section "A hereditary budget": Definition A.2 to Lemma A.7

Faithful statements, derived from the library. Throughout, `kcert` is the paper's
`κ_cert`, the lower bound on marked weights. A marked step of the paper
(`eq:visible-mark`) is `GI.VisibleStep a H L k`: a surjection `H → Alt(k)` with
kernel exactly `L` (so `L ◁ H` and `H/L ≅ Alt(k)`), `L` transitive on the active
orbit `a^H`, and every element of `H` fixing `a^H` pointwise in the kernel.
A chain with unmarked restrictions and marked steps of total weight `w` is
`GI.MarkedChain kcert a G w`.
-/

namespace GI.Paper

open GI

/-- **Definition A.2** (`def:hereditary-budget`). `σ(G, Ω, α)`: the maximum of the
total marked weight over all chains starting at `G` with base point `α`. -/
noncomputable def def_hereditary_budget (kcert : ℕ) {Ω : Type*} (G : Subgroup (Equiv.Perm Ω))
    (α : Ω) : ℕ :=
  sigma kcert α G

/-- Definition A.2: the maximum exists ("The maximum is finite"), for `kcert ≥ 5`
(the paper has `κ_cert ≥ 64`). -/
theorem def_hereditary_budget_isGreatest {kcert : ℕ} (hk : 5 ≤ kcert) {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) (α : Ω) :
    IsGreatest {w | MarkedChain kcert α G w} (def_hereditary_budget kcert G α) :=
  ⟨sigma_achieved hk α G, fun _ hw => sigma_bounds_chain hk hw⟩

/-- Definition A.2: for a transitive action the value does not depend on `α`. -/
theorem def_hereditary_budget_basepoint (kcert : ℕ) {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) [MulAction.IsPretransitive G Ω] (α β : Ω) :
    def_hereditary_budget kcert G α = def_hereditary_budget kcert G β := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G α β
  exact sigma_basepoint kcert G ⟨g, hg⟩

/-- **Lemma A.3** (`lem:budget-inheritance`), first assertion: the budget does not
increase under subgroup restriction followed by passage to the faithful image on one
orbit `D = β^H` of the subgroup. Here `G` is transitive. -/
theorem lem_budget_inheritance {kcert : ℕ} (hk : 5 ≤ kcert) {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) [MulAction.IsPretransitive G Ω] (α : Ω)
    {H : Subgroup (Equiv.Perm Ω)} (hle : H ≤ G) (β : Ω) [Fintype (ActiveOrbit H β)] :
    sigma kcert (activeOrbitBase H β) (faithfulOrbitImage H β) ≤ sigma kcert α G := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G α β
  exact sigma_faithfulOrbit_subgroup_le hk hle ⟨g, hg⟩

/-- **Lemma A.3**, marked decrease: if `N ◁ G` is transitive on `Ω` and
`G/N ≅ Alt(k)` with `k ≥ κ_cert`, then `σ(N, Ω) ≤ σ(G, Ω) - k`. -/
theorem lem_budget_inheritance_decrease {kcert k : ℕ} (hk5 : 5 ≤ kcert) (hk : kcert ≤ k)
    {Ω : Type*} [Fintype Ω] {G N : Subgroup (Equiv.Perm Ω)} (hNG : N ≤ G)
    [(N.subgroupOf G).Normal] (transitive : ∀ x y : Ω, ∃ n ∈ N, n x = y)
    (e : G ⧸ N.subgroupOf G ≃* alternatingGroup (Fin k)) (α : Ω) :
    sigma kcert α N + k ≤ sigma kcert α G := by
  let q : G →* alternatingGroup (Fin k) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf G))
  have hq1 : ∀ g : G, q g = 1 ↔ (g : Equiv.Perm Ω) ∈ N := by
    intro g
    change e (QuotientGroup.mk g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  let step : VisibleStep α G N k :=
    { lower := hNG
      quotient := q
      onto := e.surjective.comp (QuotientGroup.mk'_surjective _)
      kernel := hq1
      transitiveKernel := by
        intro h
        obtain ⟨n, hn, hna⟩ := transitive α ((h : Equiv.Perm Ω) α)
        exact ⟨⟨n, hn⟩, hna⟩
      visible := by
        intro h hfix
        have hone : (h : Equiv.Perm Ω) = 1 := by
          ext x
          obtain ⟨n, hn, rfl⟩ := transitive α x
          exact hfix ⟨n, hNG hn⟩
        rw [hq1, hone]
        exact N.one_mem }
  exact sigma_marked_decrease hk5 hk step

/-- **Lemma A.3**, last assertion: `σ(G, Ω, α)` equals the budget of the faithful
image of `G` on `α^G`. -/
theorem lem_budget_inheritance_orbit (kcert : ℕ) {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) (α : Ω) [Fintype (ActiveOrbit G α)] :
    sigma kcert α G = sigma kcert (activeOrbitBase G α) (faithfulOrbitImage G α) :=
  sigma_faithfulOrbit kcert G α

/-- **Lemma A.4** (`lem:budget-simple-localization`), first assertion: if
`φ : U ↠ S` has nonabelian simple image and normal subgroups `K_1, …, K_t` of `U`
have intersection in `ker φ`, then `φ(K_j) = 1` for some `j`. -/
theorem lem_budget_simple_localization {U S : Type*} [Group U] [Group S] [IsSimpleGroup S]
    (φ : U →* S) (hφ : Function.Surjective φ) (nonabelian : ∃ a b : S, a * b ≠ b * a)
    {t : ℕ} (K : Fin t → Subgroup U) (hK : ∀ j, (K j).Normal)
    (hcap : ∀ u : U, (∀ j, u ∈ K j) → φ u = 1) :
    ∃ j, (K j).map φ = ⊥ := by
  have hk : commonKernel (List.ofFn K) ≤ φ.ker := by
    intro u hu
    rw [mem_commonKernel_iff] at hu
    exact hcap u (fun j => hu (K j) (List.mem_ofFn.mpr ⟨j, rfl⟩))
  obtain ⟨L, hL, hmap⟩ := simple_quotient_localization φ hφ nonabelian (List.ofFn K)
    (fun L hL => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL; exact hK j) hk
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
  exact ⟨j, hmap⟩

/-- **Lemma A.4**, last assertion: if `U ◁ H`, `φ` is the restriction to `U` of a
homomorphism `ψ` on `H` and maps `U` onto a nonabelian simple group, `H` is
transitive on `D`, and the pointwise kernel `U_(D)` is killed, then the pointwise
kernel of `U` on every `U`-orbit `a^U` is killed. -/
theorem lem_budget_simple_localization_orbits {H S D : Type*} [Group H] [Group S]
    [MulAction H D] [Fintype D] [IsSimpleGroup S]
    (U : Subgroup H) [U.Normal] (ψ : H →* S) (onto : Function.Surjective (ψ.comp U.subtype))
    (nonabelian : ∃ a b : S, a * b ≠ b * a) (transitive : ∀ a b : D, ∃ h : H, h • a = b)
    (wholeKilled : ∀ k : U, (∀ d : D, (k : H) • d = d) → ψ k = 1) (a : D) :
    ∀ k ∈ orbitKernel U a, ψ (k : H) = 1 :=
  fun k hk => every_orbit_kernel_killed U ψ onto nonabelian transitive wholeKilled a k hk

/-- **Lemma A.5** (`lem:budget-blocks`). For a system of blocks preserved by `G`,
with `C` the block of `α`:
`σ(G, Ω) ≤ σ(G^𝓑, 𝓑) + σ(G_C^C, C)`. Here `G^𝓑` is the image on the blocks and
`G_C^C` the image of the block stabilizer on `C`. The proof needs neither
transitivity of `G` nor equal block sizes, so the statement omits them. -/
theorem lem_budget_blocks {kcert : ℕ} (hk : 5 ≤ kcert) {Ω : Type*} [Fintype Ω]
    {G : Subgroup (Equiv.Perm Ω)} (blocks : InvariantPartition G) (α : Ω) :
    letI := Classical.decEq Ω
    letI : Fintype (Quotient blocks.setoid) := Fintype.ofFinite _
    letI : Fintype {x : Ω // blocks.blockCover.label x = blocks.blockCover.label α} :=
      Fintype.ofFinite _
    sigma kcert α G ≤
      sigma kcert (blocks.blockCover.label α) blocks.blockCover.project.range +
      sigma kcert (blocks.blockCover.localBase α) (blocks.blockCover.localProject α).range := by
  classical
  exact BlockCover.sigma_block_le hk blocks.blockCover α

/-- Data saying that `G ≤ Sym(D) wr Sym(s)` acts on `D^s` in product action:
each `g` moves coordinate `i` to `positions g i` through the component
permutation `comp g i`. -/
structure ProductActionData {D : Type*} {s : ℕ} (G : Subgroup (Equiv.Perm (Fin s → D))) where
  positions : G →* Equiv.Perm (Fin s)
  comp : G → Fin s → Equiv.Perm D
  law : ∀ (g : G) (x : Fin s → D) (i : Fin s),
    (g : Equiv.Perm (Fin s → D)) x (positions g i) = comp g i (x i)

namespace ProductActionData

variable {D : Type*} {s : ℕ} {G : Subgroup (Equiv.Perm (Fin s → D))}

/-- The component action of the stabilizer `G_i` of coordinate `i`. -/
def componentHom (P : ProductActionData G) (i : Fin s) :
    coordinateStabilizer P.positions i →* Equiv.Perm D where
  toFun h := P.comp h.1 i
  map_one' := by
    ext d
    have h := P.law 1 (fun _ => d) i
    rw [map_one] at h
    exact h.symm
  map_mul' g h := by
    ext d
    have hg : P.positions g.1 i = i := g.2
    have hh : P.positions h.1 i = i := h.2
    have hgh : P.positions (g.1 * h.1) i = i := by
      rw [map_mul, Equiv.Perm.mul_apply, hh, hg]
    have e1 := P.law (g.1 * h.1) (fun _ => d) i
    have e2 := P.law h.1 (fun _ => d) i
    have e3 := P.law g.1 ((h.1 : Equiv.Perm (Fin s → D)) (fun _ => d)) i
    rw [hgh] at e1
    rw [hh] at e2
    rw [hg] at e3
    change P.comp (g.1 * h.1) i d = P.comp g.1 i (P.comp h.1 i d)
    rw [← e1, ← e2, ← e3]
    rfl

/-- The library's Cartesian cover built from product-action data. -/
def toCover (P : ProductActionData G) : CartesianCover G where
  positions := P.positions
  component := P.componentHom
  equivariant i h x := by
    have e := P.law h.1 x i
    rw [show P.positions h.1 i = i from h.2] at e
    exact e.symm

end ProductActionData

/-- **Lemma A.6** (`lem:budget-cartesian`). For `G ≤ Sym(D) wr Sym(s)` in product
action on `D^s`, with `A_i` the component image of the stabilizer of coordinate `i`:
`σ(G, D^s, v) ≤ 3(s-1) + Σ_i σ(A_i, D, v_i)`. No transitivity is assumed. -/
theorem lem_budget_cartesian {kcert : ℕ} (hk : 64 ≤ kcert) {D : Type*} [Fintype D]
    [DecidableEq D] {s : ℕ} {G : Subgroup (Equiv.Perm (Fin s → D))}
    (P : ProductActionData G) (v : Fin s → D) :
    sigma kcert v G ≤ 3 * (s - 1) + ∑ i, sigma kcert (v i) (P.componentHom i).range := by
  have h := CartesianCover.sigma_cartesian_le hk P.toCover v
  rwa [Fintype.card_fin] at h

/-- **Lemma A.7** (`lem:budget-johnson`). Let `m ≥ 4`, `2 ≤ t ≤ m/2`, `C ≥ C_* = 128`,
`B = C + 6`. If the natural actions satisfy `σ(Sym(r), [r]) ≤ C log r - B` for
`3 ≤ r ≤ m` and `σ(Sym(r), [r]) = 0` for `r ≤ 2`, then
`σ(Sym(m), D) ≤ C log (m choose t) - B` on `D` = the `t`-subsets of `[m]`. -/
theorem lem_budget_johnson {kcert m t : ℕ} {C B : ℝ} (hk : 64 ≤ kcert) (_hm : 4 ≤ m)
    (ht : 2 ≤ t) (hhalf : 2 * t ≤ m) (hC : 128 ≤ C) (hB : B = C + 6)
    (natural : ∀ r : ℕ, 3 ≤ r → r ≤ m → ∀ a : Fin r,
      (sigma kcert a (⊤ : Subgroup (Equiv.Perm (Fin r))) : ℝ) ≤ C * Real.log r - B)
    (_small : ∀ r : ℕ, r ≤ 2 → ∀ a : Fin r,
      sigma kcert a (⊤ : Subgroup (Equiv.Perm (Fin r))) = 0)
    (T : Johnson.SubsetVertex (Fin m) t) :
    (sigma kcert T (Johnson.subsetImage t) : ℝ) ≤ C * Real.log (m.choose t) - B := by
  subst hB
  exact Johnson.johnson_anchor_bound hk hC ht hhalf natural T

end GI.Paper
