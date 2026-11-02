import Workspace.Impl.TermGlue

/-!
# The `J`-part of one radical coset (Theorem A.23), as a hypothesis

Theorem A.23: "Lift the surviving quotient representative and correct it by the constructed
`J`-transporter. ... It also constructs `Aut_J(x)`." Above the label coset `tmGlLab I r` (the
residual elements in `R r` that pass the total and the sign, `TermGlueLabSpec`), the piece
`tmCosetT I r` of the table transport is the set of pairs `(k(h) μ, π)` with `h` in the label
coset and `μ` a `J`-element with matching `π` that corrects the lifts into the stored cosets
(`tmGl_cosetT_eq`). Writing this set as one coset needs, besides the label coset, a correcting
`J`-element for one representative and for each generator, and generators of the kernel
`Aut_J(x)`. These are solutions of the same finite abelian equations (zero-sum totals in
`A = N/N*` and the sign), so they belong to the affine layer, like
`TermGlueLabSpec`. No existing hypothesis gives them: `TermGlueLabSpec` returns only the set of
`h`.

**`Iface.TermJSpec Pg K D g`**: on `[V, encPerm r, w]`, with `V` the input of `TermCosetSpec`,
`r ∈ H` and `w` a canonical answer for `tmGlLab I r`, the function `g` returns a canonical answer
for the pairs of `tmCosetT I r`, each pair `(d, π)` written as the permutation
`(c, i) ↦ (d_i⁻¹ c, π i)` of `Fin m × Fin q` (`tmJPerm`), numbered by `finProdFinEquiv`. The cost
is `K (w + 1)^D` in the input weight.

The relabeling of such an answer to the domain positions of the state is done by a program
(`TermCosetRel*.lean`); `tmJ_domSet_eq` is its mathematics: the domain set `tmDomSet E T` is the
conjugate of `tmJSet T` by `E`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

/-- **A pair as a permutation of `Fin m × Fin q`**: `(c, i) ↦ (d_i⁻¹ c, π i)`. -/
def tmJPerm {m q : ℕ} (p : (Fin q → Perm (Fin m)) × Perm (Fin q)) : Perm (Fin m × Fin q) where
  toFun a := ((p.1 a.2)⁻¹ a.1, p.2 a.2)
  invFun b := (p.1 (p.2.symm b.2) b.1, p.2.symm b.2)
  left_inv a := by
    obtain ⟨c, i⟩ := a
    simp only [Equiv.symm_apply_apply, Prod.mk.injEq, and_true]
    exact (p.1 i).apply_symm_apply c
  right_inv b := by
    obtain ⟨c, i⟩ := b
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq, and_true]
    exact (p.1 (p.2.symm i)).symm_apply_apply c

@[simp] theorem tmJPerm_apply {m q : ℕ} (p : (Fin q → Perm (Fin m)) × Perm (Fin q))
    (a : Fin m × Fin q) : tmJPerm p a = ((p.1 a.2)⁻¹ a.1, p.2 a.2) := rfl

/-- The pairs of `T` as permutations of `Fin m × Fin q`. -/
def tmJSet {m q : ℕ} (T : Set ((Fin q → Perm (Fin m)) × Perm (Fin q))) :
    Set (Perm (Fin m × Fin q)) :=
  tmJPerm '' T

variable {Ω C : Type}

/-- **The domain set is the conjugate of the pair set** by the coordinates `E`. -/
theorem tmJ_domSet_eq {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (T : Set ((Fin q → Perm (Fin m)) × Perm (Fin q))) :
    tmDomSet E T = (fun σ => E.permCongr σ) '' tmJSet T := by
  ext σ
  simp only [tmDomSet, tmJSet, Set.mem_setOf_eq, Set.mem_image, exists_exists_and_eq_and]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  constructor
  · intro h
    ext a
    obtain ⟨⟨c, i⟩, rfl⟩ := E.surjective a
    simp [Equiv.permCongr_apply, h c i]
  · rintro rfl c i
    simp [Equiv.permCongr_apply]

/-- **Relabeling a canonical answer**: if `toFin e₁ '' A = x ⟨gs⟩` and `e₂ = e₁ ≫ ρ`, then
`toFin e₂ '' A = ρ(x) ⟨ρ(gs)⟩`, with `ρ(σ) = ρ σ ρ⁻¹`. -/
theorem tmJ_toFin_trans {Ω' : Type} {s t : ℕ} (e₁ : Ω' ≃ Fin s) (ρ : Fin s ≃ Fin t)
    {A : Set (Perm Ω')} {x : Perm (Fin s)} {gs : List (Perm (Fin s))}
    (hA : toFin e₁ '' A = x • (gens gs : Set (Perm (Fin s)))) :
    toFin (e₁.trans ρ) '' A =
      toFin ρ x • (gens (gs.map (toFin ρ)) : Set (Perm (Fin t))) := by
  have hcomp : ∀ σ : Perm Ω', toFin (e₁.trans ρ) σ = toFin ρ (toFin e₁ σ) := by
    intro σ; ext a; simp [Equiv.permCongr_apply]
  have hgens : gens (gs.map (toFin ρ)) = (gens gs).map (toFin ρ).toMonoidHom := by
    unfold gens
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image, MulEquiv.coe_toMonoidHom]
  rw [hgens]
  ext τ
  simp only [Set.mem_image, Set.mem_smul_set, SetLike.mem_coe, Subgroup.mem_map, smul_eq_mul]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have : toFin e₁ σ ∈ toFin e₁ '' A := ⟨σ, hσ, rfl⟩
    rw [hA] at this
    obtain ⟨g, hg, he⟩ := this
    refine ⟨toFin ρ g, ⟨g, hg, rfl⟩, ?_⟩
    rw [hcomp, ← he]
    show _ = toFin ρ (x * g)
    rw [map_mul]
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have : x * g ∈ toFin e₁ '' A := by rw [hA]; exact ⟨g, hg, rfl⟩
    obtain ⟨σ, hσ, he⟩ := this
    refine ⟨σ, hσ, ?_⟩
    rw [hcomp, he, map_mul]
    rfl

namespace Iface

variable (Pg : Program)

/-- **The `J`-part of one radical coset** (Theorem A.23, the correcting `J`-elements and
`Aut_J(x)`). On `[V, encPerm r, w]`, with `V` the input of `TermCosetSpec`, `r ∈ H`, and `w` a
canonical answer for the label coset `tmGlLab T0 r`, the function `g` returns a canonical answer
for the pairs of the piece `tmCosetT T0 r`, as permutations of `Fin m × Fin q` (`tmJSet`), at cost
at most `K (w + 1)^D`. -/
def TermJSpec (K D g : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c →
    ∀ (sv lv : Val) (L : SuppliedLabels S), Canon e c sv S → LabValStd e S lv L →
    P₀.q₀ < L.q → Good P₀ .giant S → RowCase P₀.α S L.toGiantLabels →
    ∀ (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
      {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
      (hP : PureCoords S L.toGiantLabels label E)
      (σH σN σS : List (Perm (Fin m))),
      gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb →
      gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb →
      gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
      ∀ (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B),
      σH.length ≤ (k + L.q) ^ 2 → σN.length ≤ (k + L.q) ^ 2 → σS.length ≤ (k + L.q) ^ 2 →
      ∀ (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
        (hqα : (S.N : ℝ) ^ P₀.α < L.q),
      ∀ us vs : List Val,
      List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q) →
      List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q) →
      ∀ r : Perm (Fin m), r ∈ ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).Hb →
      ∀ w : Val, AnsC (Equiv.refl (Fin m)) w
        (tmGlLab ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r) →
      FunAll Pg g (.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r, w])
        (fun u cost => AnsC (finProdFinEquiv : Fin m × Fin L.q ≃ Fin (m * L.q)) u
            (tmJSet (tmCosetT ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard
              hsN hN hqα) r)) ∧
          cost ≤ K * ((Val.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
            encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r, w]).wt + 1) ^ D)

end Iface

end GI.Impl
