module

public import Workspace.Degree.Class
public import Workspace.Cited.MarotiPrimitive
import Mathlib.GroupTheory.Perm.Sign

/-!
# Johnson products

A group of Johnson-product type lies in `Sym(q) wr Sym(r)` in the product action on `r`-tuples of
`h`-subsets of `Fin q`, and contains `Alt(q)^r`. This file sets up the coordinate group, the
subgroup `S ≅ Alt(q)^r`, and the facts that the paper uses about them.

* `WreathStructure P e` is the structure, as in `GI.Cited.MarotiStructure`, for any set of points.
* `wreathPerm` is the homomorphism from `P` to the permutations of the `r` coordinates.
* `card_le_range_mul`: `|P| ≤ |K| (q!)^r`.
* `index_le`: `[P : S] ≤ 2^r |K|`.
* `socle_conj_mem`: `S` is normal in `P`.
* `alternating_section_le`: `q ≤ D` when `P ∈ Γ̂_D` and `q ≥ 5`.
-/

@[expose] public section

namespace GI.Degree

open Equiv GI.Cited

/-- The `h`-subsets of `Fin q`. -/
abbrev JohnsonSet (q h : ℕ) : Type := {A : Finset (Fin q) // A.card = h}

/-- The `r`-tuples of `h`-subsets of `Fin q`. -/
abbrev JohnsonTuple (q h r : ℕ) : Type := Fin r → JohnsonSet q h

/-- The action of `Sym(q)` on `h`-subsets, as a homomorphism. -/
def kSetHom (q h : ℕ) : Perm (Fin q) →* Perm (JohnsonSet q h) where
  toFun := kSetPerm
  map_one' := Equiv.ext fun A => Subtype.ext (Finset.map_refl (s := A.1))
  map_mul' a b := Equiv.ext fun A => Subtype.ext
    (Finset.map_map b.toEmbedding a.toEmbedding A.1).symm

theorem kSetHom_apply {q h : ℕ} (a : Perm (Fin q)) : kSetHom q h a = kSetPerm a := rfl

theorem kSetPerm_inv_apply {q h : ℕ} (a : Perm (Fin q)) (A : JohnsonSet q h) :
    kSetPerm a⁻¹ (kSetPerm a A) = A := by
  rw [← kSetHom_apply, ← kSetHom_apply, map_inv]
  simp

/-- For `1 ≤ h < q` the action on `h`-subsets is faithful. If `a x ≠ x`, take an `h`-subset that
contains `x` and not `a x`. -/
theorem kSetHom_injective {q h : ℕ} (h1 : 1 ≤ h) (h2 : h < q) :
    Function.Injective (kSetHom q h) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, a x ≠ x := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  have hcard : h - 1 ≤ (Finset.univ.erase x |>.erase (a x)).card := by
    rw [Finset.card_erase_of_mem (by simp [hx]), Finset.card_erase_of_mem (by simp)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hcard
  have hxs : x ∉ s := fun hm => by simpa using hs hm
  have hax : a x ∉ s := fun hm => by simpa using hs hm
  let A : JohnsonSet q h := ⟨insert x s, by rw [Finset.card_insert_of_notMem hxs, hsc]; omega⟩
  have hA : kSetHom q h a A = A := by rw [ha]; rfl
  have hm : a x ∈ (kSetHom q h a A).1 := by
    change a x ∈ (insert x s).map a.toEmbedding
    exact Finset.mem_map.2 ⟨x, by simp, rfl⟩
  rw [hA] at hm
  have : a x ∈ insert x s := hm
  rcases Finset.mem_insert.1 this with h' | h'
  · exact hx h'
  · exact hax h'

/-- For `1 ≤ h < q` there are two different `h`-subsets. -/
theorem johnsonSet_nontrivial {q h : ℕ} (h1 : 1 ≤ h) (h2 : h < q) :
    Nontrivial (JohnsonSet q h) := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have hc := kSetHom_injective h1 h2
  have : q ≥ 2 := by omega
  have hsw : Equiv.swap (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ ≠ 1 := by
    intro h0
    have := congrArg (fun p : Perm (Fin q) => p ⟨0, by omega⟩) h0
    simp at this
  exact hsw (hc ((Equiv.ext fun A => Subsingleton.elim _ _).trans (map_one (kSetHom q h)).symm))

variable {α : Type*} {q h r : ℕ}

/-- The coordinatewise action of `Sym(q)^r` on tuples. -/
def tupleHom (q h r : ℕ) : (Fin r → Perm (Fin q)) →* Perm (JohnsonTuple q h r) where
  toFun a := Equiv.piCongrRight fun i => kSetHom q h (a i)
  map_one' := Equiv.ext fun x => funext fun i => by simp
  map_mul' a b := Equiv.ext fun x => funext fun i => by simp

/-- The coordinatewise action of `Sym(q)^r`, read through `e`. -/
def coordHom (e : α ≃ JohnsonTuple q h r) : (Fin r → Perm (Fin q)) →* Perm α :=
  e.symm.permCongrHom.toMonoidHom.comp (tupleHom q h r)

theorem coordHom_apply (e : α ≃ JohnsonTuple q h r) (a : Fin r → Perm (Fin q)) :
    coordHom e a = e.trans ((Equiv.piCongrRight fun i => kSetPerm (a i)).trans e.symm) := rfl

/-- The subgroup `S ≅ Alt(q)^r` of the paper. -/
def johnsonSocle (e : α ≃ JohnsonTuple q h r) : Subgroup (Perm α) :=
  (Subgroup.pi Set.univ fun _ : Fin r => alternatingGroup (Fin q)).map (coordHom e)

/-- `g` is the element `(σ; a)` of `Sym(q) wr Sym(r)`, read through `e`: coordinate `i` of the image
of a point comes from coordinate `σ i`, moved by `a i`. -/
def IsWreathElement (e : α ≃ JohnsonTuple q h r) (g : Perm α) (σ : Perm (Fin r))
    (a : Fin r → Perm (Fin q)) : Prop :=
  ∀ x, e (g x) = fun i => kSetPerm (a i) (e x (σ i))

/-- The Johnson-product structure of `P`, read through `e`. For `α = Fin n` this is
`GI.Cited.MarotiStructure P e`. -/
structure WreathStructure (P : Subgroup (Perm α)) (e : α ≃ JohnsonTuple q h r) : Prop where
  mem_wreath : ∀ g ∈ P, ∃ σ a, IsWreathElement e g σ a
  alt_le : johnsonSocle e ≤ P

/-- The permutations of the coordinates that occur in `P`. -/
def coordinateSet (P : Subgroup (Perm α)) (e : α ≃ JohnsonTuple q h r) : Set (Perm (Fin r)) :=
  {σ | ∃ g ∈ P, ∃ a, IsWreathElement e g σ a}

section Wreath

variable {e : α ≃ JohnsonTuple q h r}

theorem IsWreathElement.one : IsWreathElement e 1 1 1 := by
  intro x
  funext i
  exact (DFunLike.congr_fun (map_one (kSetHom q h)) (e x i)).symm

theorem IsWreathElement.mul {g g' : Perm α} {σ σ' : Perm (Fin r)} {a a' : Fin r → Perm (Fin q)}
    (hg : IsWreathElement e g σ a) (hg' : IsWreathElement e g' σ' a') :
    IsWreathElement e (g * g') (σ' * σ) fun i => a i * a' (σ i) := by
  intro x
  funext i
  rw [Perm.mul_apply, hg, hg']
  exact (DFunLike.congr_fun (map_mul (kSetHom q h) (a i) (a' (σ i))) (e x (σ' (σ i)))).symm

theorem IsWreathElement.inv {g : Perm α} {σ : Perm (Fin r)} {a : Fin r → Perm (Fin q)}
    (hg : IsWreathElement e g σ a) :
    IsWreathElement e g⁻¹ σ⁻¹ fun i => (a (σ⁻¹ i))⁻¹ := by
  intro x
  funext i
  have h1 := congrFun (hg (g⁻¹ x)) (σ⁻¹ i)
  have h2 : g (g⁻¹ x) = x := by simp
  have h3 : σ (σ⁻¹ i) = i := by simp
  rw [h2, h3] at h1
  rw [h1, kSetPerm_inv_apply]

/-- The action of `(σ; a)` determines `σ` and `a`, for `1 ≤ h < q`. If `σ i ≠ σ' i`, fix coordinate
`σ i` of a point and change coordinate `σ' i`: the coordinate `i` of the image changes for `σ'` and
not for `σ`. -/
theorem IsWreathElement.unique (h1 : 1 ≤ h) (h2 : h < q) {g : Perm α} {σ σ' : Perm (Fin r)}
    {a a' : Fin r → Perm (Fin q)} (hg : IsWreathElement e g σ a)
    (hg' : IsWreathElement e g σ' a') : σ = σ' ∧ a = a' := by
  classical
  have hn := johnsonSet_nontrivial h1 h2
  have key (x : JohnsonTuple q h r) (i : Fin r) :
      kSetPerm (a i) (x (σ i)) = kSetPerm (a' i) (x (σ' i)) := by
    have h3 := congrFun (hg (e.symm x)) i
    have h4 := congrFun (hg' (e.symm x)) i
    simp only [Equiv.apply_symm_apply] at h3 h4
    exact h3.symm.trans h4
  have hσ : σ = σ' := by
    ext i
    by_contra hne
    have hne' : σ i ≠ σ' i := fun h0 => hne (congrArg Fin.val h0)
    obtain ⟨A, B, hAB⟩ := exists_pair_ne (JohnsonSet q h)
    have h3 := key (fun _ => A) i
    have h4 := key (Function.update (fun _ => A) (σ' i) B) i
    rw [Function.update_of_ne hne', Function.update_self] at h4
    have h5 := h3.symm.trans h4
    exact hAB ((kSetPerm (a' i)).injective h5)
  subst hσ
  refine ⟨rfl, funext fun i => kSetHom_injective h1 h2 (Equiv.ext fun A => ?_)⟩
  exact key (fun _ => A) i

theorem IsWreathElement.eq_coordHom {g : Perm α} {a : Fin r → Perm (Fin q)}
    (hg : IsWreathElement e g 1 a) : g = coordHom e a := by
  ext1 x
  apply e.injective
  rw [hg x, coordHom_apply]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem isWreathElement_coordHom (a : Fin r → Perm (Fin q)) :
    IsWreathElement e (coordHom e a) 1 a := by
  intro x
  rw [coordHom_apply]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem coordHom_injective (h1 : 1 ≤ h) (h2 : h < q) :
    Function.Injective (coordHom e) := by
  intro a b hab
  have ha := isWreathElement_coordHom (e := e) a
  rw [hab] at ha
  exact (ha.unique h1 h2 (isWreathElement_coordHom b)).2

theorem mem_socle_of_wreath {g : Perm α} {a : Fin r → Perm (Fin q)}
    (hg : IsWreathElement e g 1 a) (ha : ∀ i, a i ∈ alternatingGroup (Fin q)) :
    g ∈ johnsonSocle e :=
  ⟨a, fun i _ => ha i, hg.eq_coordHom.symm⟩

/-- `S` is normalized by the whole wreath product. -/
theorem socle_conj_mem {g s : Perm α} {σ : Perm (Fin r)} {a : Fin r → Perm (Fin q)}
    (hg : IsWreathElement e g σ a) (hs : s ∈ johnsonSocle e) :
    g * s * g⁻¹ ∈ johnsonSocle e := by
  obtain ⟨b, hb, rfl⟩ := hs
  have h3 := (hg.mul (isWreathElement_coordHom b)).mul hg.inv
  have h4 : σ⁻¹ * (1 * σ) = 1 := by simp
  rw [h4] at h3
  refine mem_socle_of_wreath h3 fun i => ?_
  have hb' : b (σ i) ∈ alternatingGroup (Fin q) := hb (σ i) (Set.mem_univ _)
  rw [Equiv.Perm.mem_alternatingGroup] at hb' ⊢
  simp [Equiv.Perm.sign_mul, hb', Equiv.Perm.sign_inv]

end Wreath

section Hom

variable {e : α ≃ JohnsonTuple q h r} {P : Subgroup (Perm α)}

/-- A choice of `σ` for each element of `P`. -/
noncomputable def wreathSigma (hP : WreathStructure P e) (g : P) : Perm (Fin r) :=
  (hP.mem_wreath g g.2).choose

/-- A choice of `a` for each element of `P`. -/
noncomputable def wreathCoord (hP : WreathStructure P e) (g : P) : Fin r → Perm (Fin q) :=
  (hP.mem_wreath g g.2).choose_spec.choose

theorem wreath_spec (hP : WreathStructure P e) (g : P) :
    IsWreathElement e g (wreathSigma hP g) (wreathCoord hP g) :=
  (hP.mem_wreath g g.2).choose_spec.choose_spec

/-- The homomorphism from `P` to the permutations of the `r` coordinates. -/
noncomputable def wreathPerm (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) :
    P →* Perm (Fin r) where
  toFun g := (wreathSigma hP g)⁻¹
  map_one' := by
    rw [((wreath_spec hP 1).unique h1 h2 (IsWreathElement.one (e := e))).1, inv_one]
  map_mul' g g' := by
    rw [((wreath_spec hP (g * g')).unique h1 h2
      ((wreath_spec hP g).mul (wreath_spec hP g'))).1, mul_inv_rev]

theorem wreathPerm_eq (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) (g : P)
    {σ : Perm (Fin r)} {a : Fin r → Perm (Fin q)} (hg : IsWreathElement e g σ a) :
    wreathPerm hP h1 h2 g = σ⁻¹ := by
  change (wreathSigma hP g)⁻¹ = σ⁻¹
  rw [((wreath_spec hP g).unique h1 h2 hg).1]

/-- The set of coordinate permutations is the image of `wreathPerm`. -/
theorem coordinateSet_eq (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) :
    coordinateSet P e = (wreathPerm hP h1 h2).range := by
  ext σ
  constructor
  · rintro ⟨g, hg, a, ha⟩
    refine ⟨⟨g, hg⟩⁻¹, ?_⟩
    rw [map_inv, wreathPerm_eq hP h1 h2 ⟨g, hg⟩ ha, inv_inv]
  · rintro ⟨g, rfl⟩
    exact ⟨(g⁻¹ : P), (g⁻¹ : P).2, _, (wreath_spec hP g).inv⟩

/-- An element of the kernel has trivial coordinate permutation. -/
theorem wreath_spec_ker (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q)
    (g : (wreathPerm hP h1 h2).ker) : IsWreathElement e g.1 1 (wreathCoord hP g.1) := by
  have hs : wreathSigma hP g.1 = 1 := by
    have : (wreathSigma hP g.1)⁻¹ = 1 := g.2
    simpa using this
  have := wreath_spec hP g.1
  rwa [hs] at this

theorem wreathCoord_mul (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q)
    (g g' : (wreathPerm hP h1 h2).ker) :
    wreathCoord hP (g * g').1 = wreathCoord hP g.1 * wreathCoord hP g'.1 := by
  have h3 := (wreath_spec_ker hP h1 h2 g).mul (wreath_spec_ker hP h1 h2 g')
  rw [one_mul] at h3
  exact ((wreath_spec_ker hP h1 h2 (g * g')).unique h1 h2 h3).2

/-- The parities of the coordinates of an element of the kernel. -/
noncomputable def wreathSign (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) :
    (wreathPerm hP h1 h2).ker →* (Fin r → ℤˣ) where
  toFun g i := Perm.sign (wreathCoord hP g.1 i)
  map_one' := by
    funext i
    have := ((wreath_spec_ker hP h1 h2 1).unique h1 h2 (IsWreathElement.one (e := e))).2
    rw [this]
    simp
  map_mul' g g' := by
    funext i
    rw [wreathCoord_mul]
    simp

theorem card_ker_le (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) :
    Nat.card (wreathPerm hP h1 h2).ker ≤ q.factorial ^ r := by
  have hinj : Function.Injective fun g : (wreathPerm hP h1 h2).ker => wreathCoord hP g.1 := by
    intro g g' hgg
    apply Subtype.ext
    apply Subtype.ext
    have hg := (wreath_spec_ker hP h1 h2 g).eq_coordHom
    have hg' := (wreath_spec_ker hP h1 h2 g').eq_coordHom
    simp only at hgg
    rw [hg, hg', hgg]
  calc Nat.card (wreathPerm hP h1 h2).ker
      ≤ Nat.card (Fin r → Perm (Fin q)) := Nat.card_le_card_of_injective _ hinj
    _ = q.factorial ^ r := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- `|P| ≤ |K| (q!)^r`. -/
theorem card_le_range_mul (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) [Finite P] :
    Nat.card P ≤ Nat.card (wreathPerm hP h1 h2).range * q.factorial ^ r := by
  have hG : Nat.card P = Nat.card (wreathPerm hP h1 h2).range *
      Nat.card (wreathPerm hP h1 h2).ker := by
    rw [← Subgroup.card_mul_index (wreathPerm hP h1 h2).ker, Subgroup.index_ker, mul_comm]
  rw [hG]
  exact Nat.mul_le_mul_left _ (card_ker_le hP h1 h2)

/-- `|ker| ≤ 2^r |S|`: an element with all coordinates even lies in `S`. -/
theorem card_ker_le_socle (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) [Finite P] :
    Nat.card (wreathPerm hP h1 h2).ker ≤ 2 ^ r * Nat.card (johnsonSocle e) := by
  have : Finite (johnsonSocle e) := Finite.of_injective (Subgroup.inclusion hP.alt_le)
    (Subgroup.inclusion_injective hP.alt_le)
  set ψ := wreathSign hP h1 h2
  have hK : Nat.card (wreathPerm hP h1 h2).ker = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker, mul_comm]
  have hr : Nat.card ψ.range ≤ 2 ^ r := by
    calc Nat.card ψ.range ≤ Nat.card (Fin r → ℤˣ) := Subgroup.card_le_card_group _
      _ = 2 ^ r := by simp [Nat.card_eq_fintype_card]
  have hk : Nat.card ψ.ker ≤ Nat.card (johnsonSocle e) := by
    have hmem (g : ψ.ker) : ((g.1.1 : P) : Perm α) ∈ johnsonSocle e :=
      mem_socle_of_wreath (wreath_spec_ker hP h1 h2 g.1) fun i => by
        rw [Equiv.Perm.mem_alternatingGroup]
        exact congrFun (MonoidHom.mem_ker.1 g.2) i
    refine Nat.card_le_card_of_injective (fun g : ψ.ker => (⟨_, hmem g⟩ : johnsonSocle e)) ?_
    intro g g' hgg
    exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.mk.inj hgg)))
  rw [hK]
  exact Nat.mul_le_mul hr hk

/-- **The index bound of Lemma 8.2 of the paper.** `[P : S] ≤ 2^r |K|`. -/
theorem index_le (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) [Finite P] :
    ((johnsonSocle e).subgroupOf P).index ≤ 2 ^ r * Nat.card (wreathPerm hP h1 h2).range := by
  have hS : Finite (johnsonSocle e) := Finite.of_injective (Subgroup.inclusion hP.alt_le)
    (Subgroup.inclusion_injective hP.alt_le)
  have hc : Nat.card ((johnsonSocle e).subgroupOf P) = Nat.card (johnsonSocle e) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.alt_le).toEquiv
  have hG : Nat.card P = Nat.card (wreathPerm hP h1 h2).range *
      Nat.card (wreathPerm hP h1 h2).ker := by
    rw [← Subgroup.card_mul_index (wreathPerm hP h1 h2).ker, Subgroup.index_ker, mul_comm]
  have hmul := Subgroup.card_mul_index ((johnsonSocle e).subgroupOf P)
  rw [hc] at hmul
  have hpos : 0 < Nat.card (johnsonSocle e) := Nat.card_pos
  have h3 : Nat.card (johnsonSocle e) * ((johnsonSocle e).subgroupOf P).index ≤
      Nat.card (johnsonSocle e) * (2 ^ r * Nat.card (wreathPerm hP h1 h2).range) := by
    rw [hmul, hG]
    calc _ ≤ Nat.card (wreathPerm hP h1 h2).range * (2 ^ r * Nat.card (johnsonSocle e)) :=
          Nat.mul_le_mul_left _ (card_ker_le_socle hP h1 h2)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h3 hpos

/-- The copy of `Alt(q)` in coordinate `i₀`, as a subgroup of `P`. -/
noncomputable def altSingle (hP : WreathStructure P e) (i₀ : Fin r) :
    alternatingGroup (Fin q) →* P :=
  ((coordHom e).comp ((MonoidHom.mulSingle (fun _ => Perm (Fin q)) i₀).comp
      (alternatingGroup (Fin q)).subtype)).codRestrict P fun a => hP.alt_le ⟨_, fun i _ => by
    by_cases hi : i = i₀
    · subst hi
      simp
    · simp [Pi.mulSingle_eq_of_ne hi, one_mem], rfl⟩

theorem altSingle_injective (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q) (i₀ : Fin r) :
    Function.Injective (altSingle hP i₀) := by
  intro a b hab
  have h3 := coordHom_injective (e := e) h1 h2 (congrArg Subtype.val hab)
  exact Subtype.ext (Pi.mulSingle_injective i₀ h3)

/-- `q ≤ D` when `P ∈ Γ̂_D` and `q ≥ 5`: the first coordinate of `S` is a copy of `Alt(q)` in `P`. -/
theorem alternating_section_le (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q)
    (hr : 1 ≤ r) (hq : 5 ≤ q) {D : ℕ} (hD : GammaHat D P) : q ≤ D := by
  have hι := altSingle_injective hP h1 h2 ⟨0, hr⟩
  let E := MonoidHom.ofInjective hι
  exact hD.le_of_alternating_section hq _ E.symm.toMonoidHom E.symm.surjective

/-- A simple group of Johnson-product type is `Alt(q)`. The subgroup `S` is normal and nontrivial,
so it is the whole group. Then each copy of `Alt(q)` in a coordinate is normal, so it is also the
whole group. -/
theorem nonempty_equiv_alternating (hP : WreathStructure P e) (h1 : 1 ≤ h) (h2 : h < q)
    (hr : 1 ≤ r) (hq : 5 ≤ q) [IsSimpleGroup P] : Nonempty (P ≃* alternatingGroup (Fin q)) := by
  have : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin q)) :=
    alternatingGroup.isSimpleGroup (by simpa using hq)
  let i₀ : Fin r := ⟨0, hr⟩
  have hι := altSingle_injective hP h1 h2 i₀
  let A := (altSingle hP i₀).range
  have hne : A ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin q))
    have hm : altSingle hP i₀ a ∈ A := ⟨a, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hm
    exact ha (hι (hm.trans (map_one _).symm))
  -- Every element of `P` lies in `S`.
  have hS : ∀ g : P, ∃ c : Fin r → Perm (Fin q), (g : Perm α) = coordHom e c := by
    let S : Subgroup P := (johnsonSocle e).subgroupOf P
    have hSn : S.Normal := ⟨fun s hs g => by
      obtain ⟨σ, a, ha⟩ := hP.mem_wreath g g.2
      exact socle_conj_mem ha hs⟩
    have hSne : S ≠ ⊥ := by
      intro hbot
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      have hm : altSingle hP i₀ a ∈ S := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨_, fun i _ => by
          by_cases hi : i = i₀
          · subst hi
            simp
          · simp [Pi.mulSingle_eq_of_ne hi, one_mem], rfl⟩
      rw [hbot] at hm
      exact hm
    have htop := hSn.eq_bot_or_eq_top.resolve_left hSne
    intro g
    have hg : g ∈ S := htop ▸ Subgroup.mem_top g
    obtain ⟨c, -, hc⟩ := hg
    exact ⟨c, hc.symm⟩
  have hAn : A.Normal := ⟨by
    rintro _ ⟨a, rfl⟩ g
    obtain ⟨c, hc⟩ := hS g
    have hconj : ((g * altSingle hP i₀ a * g⁻¹ : P) : Perm α) =
        coordHom e (c * Pi.mulSingle i₀ (a : Perm (Fin q)) * c⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc]
      rfl
    have hsingle : c * Pi.mulSingle i₀ (a : Perm (Fin q)) * c⁻¹ =
        Pi.mulSingle i₀ (c i₀ * a * (c i₀)⁻¹) := by
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Pi.mulSingle_eq_of_ne hi]
    have hmem : c i₀ * a * (c i₀)⁻¹ ∈ alternatingGroup (Fin q) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have : Perm.sign (a : Perm (Fin q)) = 1 := a.2
      simp [Equiv.Perm.sign_mul, this]
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [hconj, hsingle]
    rfl⟩
  have htop := hAn.eq_bot_or_eq_top.resolve_left hne
  have hsurj : Function.Surjective (altSingle hP i₀) := MonoidHom.range_eq_top.1 htop
  exact ⟨(MulEquiv.ofBijective _ ⟨hι, hsurj⟩).symm⟩

end Hom

end GI.Degree
