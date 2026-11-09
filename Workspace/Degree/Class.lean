module

public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The class `Γ̂_d`

The paper and GNS define `Γ̂_d` as the finite groups whose composition factors embed in `Sym(d)`.
Here `GammaHat d G` says that every simple section of `G` embeds in `Sym(d)`. A composition factor
is a simple section, so this implies the paper's condition. The converse holds as well, and is the
content of this file: a group whose composition factors lie in the class lies in the class, by
`GammaHat.of_normal` and induction on a composition series, and a simple subgroup of `Sym(d)` lies
in the class, by `GammaHat.of_injective` and `gammaHat_perm`.

The class is internal to the proof: the final statement does not mention it.

Main results, which are GNS Lemma 2.4 and the bound `aw(H) ≤ D` of Lemma 8.1 of the paper:

* `GammaHat.of_injective`, `GammaHat.of_surjective`: closure under subgroups and images;
* `GammaHat.of_normal`: closure under extensions;
* `gammaHat_of_injective_perm`: subgroups of `Sym(n)` lie in `Γ̂_n`;
* `GammaHat.le_of_alternating_section`: an alternating section `Alt(t)`, `t ≥ 5`, has `t ≤ d`.
-/

@[expose] public section

namespace GI.Degree

open Equiv

universe u v w

/-- `T` embeds in `Sym(d)`. -/
def EmbedsInSym (d : ℕ) (T : Type*) [Group T] : Prop :=
  ∃ f : T →* Perm (Fin d), Function.Injective f

/-- The class `Γ̂_d`: every simple section of `G` embeds in `Sym(d)`. -/
def GammaHat (d : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (A : Subgroup G) (B : Subgroup A) [B.Normal], IsSimpleGroup (A ⧸ B) →
    EmbedsInSym d (A ⧸ B)

theorem EmbedsInSym.of_injective {d : ℕ} {S T : Type*} [Group S] [Group T] (f : S →* T)
    (hf : Function.Injective f) (h : EmbedsInSym d T) : EmbedsInSym d S := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g.comp f, hg.comp hf⟩

theorem EmbedsInSym.mono {d e : ℕ} (hde : d ≤ e) {T : Type*} [Group T] (h : EmbedsInSym d T) :
    EmbedsInSym e T := by
  obtain ⟨g, hg⟩ := h
  let v := (Fin.castLEEmb hde).toEquivRange
  exact ⟨(Perm.extendDomainHom v).comp g, (Perm.extendDomainHom_injective v).comp hg⟩

/-- A group acting faithfully on a finite set of `n` points embeds in `Sym(n)`. -/
theorem embedsInSym_of_perm {X : Type*} [Finite X] {n : ℕ} (hn : Nat.card X ≤ n) {T : Type*}
    [Group T] (φ : T →* Perm X) (hφ : Function.Injective φ) : EmbedsInSym n T := by
  have e : X ≃ Fin (Nat.card X) := Finite.equivFin X
  exact EmbedsInSym.mono hn ⟨(e.permCongrHom.toMonoidHom).comp φ,
    e.permCongrHom.injective.comp hφ⟩

/-- A simple group with a proper subgroup of index at most `n` embeds in `Sym(n)`, by its action
on the cosets. -/
theorem embedsInSym_of_coset {T : Type*} [Group T] [IsSimpleGroup T] (S : Subgroup T) (hS : S ≠ ⊤)
    [Finite (T ⧸ S)] {n : ℕ} (hn : Nat.card (T ⧸ S) ≤ n) : EmbedsInSym n T := by
  refine embedsInSym_of_perm hn (MulAction.toPermHom T (T ⧸ S)) ?_
  rw [injective_iff_map_eq_one]
  by_contra hne
  push Not at hne
  obtain ⟨a, ha, ha1⟩ := hne
  have hker : (MulAction.toPermHom T (T ⧸ S)).ker = ⊤ := by
    rcases (MulAction.toPermHom T (T ⧸ S)).normal_ker.eq_bot_or_eq_top with h | h
    · exact absurd (by simpa [h] using (MonoidHom.mem_ker).2 ha) ha1
    · exact h
  refine hS (eq_top_iff.2 fun t _ => ?_)
  have ht : t ∈ (MulAction.toPermHom T (T ⧸ S)).ker := hker ▸ Subgroup.mem_top t
  have h1 : t • ((1 : T) : T ⧸ S) = ((1 : T) : T ⧸ S) :=
    congrArg (fun p : Perm (T ⧸ S) => p ((1 : T) : T ⧸ S)) (MonoidHom.mem_ker.1 ht)
  have h2 : ((t : T) : T ⧸ S) = ((1 : T) : T ⧸ S) := by
    rw [← h1]
    exact congrArg _ (mul_one t).symm
  simpa using QuotientGroup.eq.1 h2

/-- **The key step.** A simple image `T` of a group `A` that acts faithfully on `n` points
embeds in `Sym(n)`. For a point `x` with stabilizer `A_x`, there are two cases. If `A_x` does not
map onto `T`, then `T` acts faithfully on the cosets of the image, and there are at most `n` of
them. If `A_x` maps onto `T` for all `x`, replace `A` by `A_x`, which acts faithfully on `n - 1`
points. -/
theorem embedsInSym_of_surjective_aux (n : ℕ) : ∀ (X : Type v) [Finite X], Nat.card X = n →
    ∀ (A : Type u) [Group A] (φ : A →* Perm X), Function.Injective φ →
    ∀ (T : Type w) [Group T] [IsSimpleGroup T] (f : A →* T), Function.Surjective f →
      EmbedsInSym n T := by
  induction n with
  | zero =>
    intro X _ hX A _ φ hφ T _ _ f hf
    have hemp : IsEmpty X := (Nat.card_eq_zero.1 hX).resolve_right (fun h => not_finite X)
    have hA : Subsingleton A := ⟨fun a b => hφ (Subsingleton.elim _ _)⟩
    have hT : Subsingleton T := ⟨fun a b => by
      obtain ⟨a, rfl⟩ := hf a
      obtain ⟨b, rfl⟩ := hf b
      rw [Subsingleton.elim a b]⟩
    exact absurd (inferInstance : Nontrivial T) (not_nontrivial_iff_subsingleton.2 hT)
  | succ n ih =>
    intro X _ hX A _ φ hφ T _ _ f hf
    have hne : Nonempty X := by
      rw [← Finite.card_pos_iff, hX]
      exact Nat.succ_pos n
    let St (x : X) : Subgroup A := (MulAction.stabilizer (Perm X) x).comap φ
    have hSt (x : X) (a : A) : a ∈ St x ↔ φ a x = x := by
      simp [St, MulAction.mem_stabilizer_iff]
    by_cases h : ∃ x, (St x).map f ≠ ⊤
    · obtain ⟨x, hx⟩ := h
      -- Pick a preimage in `A` of each coset, and send it to the image of `x`.
      let S := (St x).map f
      have hsec (c : T ⧸ S) : ∃ a : A, ((f a : T) : T ⧸ S) = c := by
        obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
        obtain ⟨a, rfl⟩ := hf t
        exact ⟨a, rfl⟩
      choose s hs using hsec
      have hinj : Function.Injective fun c : T ⧸ S => φ (s c) x := by
        intro c d hcd
        have h1 : (s c)⁻¹ * s d ∈ St x := by
          rw [hSt, map_mul, map_inv, Perm.mul_apply, ← (show φ (s c) x = φ (s d) x from hcd)]
          simp
        rw [← hs c, ← hs d]
        refine QuotientGroup.eq.2 ?_
        rw [← map_inv, ← map_mul]
        exact ⟨_, h1, rfl⟩
      have : Finite (T ⧸ S) := Finite.of_injective _ hinj
      exact embedsInSym_of_coset S hx (hX ▸ Nat.card_le_card_of_injective _ hinj)
    · push Not at h
      obtain ⟨x⟩ := hne
      -- The stabilizer acts faithfully on the other `n` points.
      have hne' (a : St x) (y : X) : y ≠ x ↔ φ (a : A) y ≠ x := by
        have hax : φ (a : A) x = x := (hSt x a).1 a.2
        constructor
        · intro hy h0
          exact hy ((φ (a : A)).injective (h0.trans hax.symm))
        · rintro hy rfl
          exact hy hax
      let ψ : St x →* Perm {y : X // y ≠ x} :=
        { toFun := fun a => (φ (a : A)).subtypePerm fun y => (hne' a y).symm
          map_one' := by
            ext y
            simp
          map_mul' := fun a b => by
            ext y
            simp [Perm.mul_apply]
            rfl }
      have hψ : Function.Injective ψ := by
        intro a b hab
        apply Subtype.ext
        apply hφ
        ext y
        by_cases hy : y = x
        · subst hy
          rw [(hSt y a).1 a.2, (hSt y b).1 b.2]
        · have := congrArg (fun p : Perm {y : X // y ≠ x} => ((p ⟨y, hy⟩ : {y : X // y ≠ x}) : X)) hab
          simpa [ψ] using this
      have hcard : Nat.card {y : X // y ≠ x} = n := by
        classical
        have hsum := Nat.card_congr (Equiv.sumCompl (fun y : X => y = x))
        rw [Nat.card_sum, Nat.card_unique, hX] at hsum
        change 1 + Nat.card {y : X // y ≠ x} = n + 1 at hsum
        omega
      have hsurj : Function.Surjective (f.comp (St x).subtype) := by
        intro t
        have ht : t ∈ (St x).map f := (h x) ▸ Subgroup.mem_top t
        obtain ⟨a, ha, rfl⟩ := ht
        exact ⟨⟨a, ha⟩, rfl⟩
      exact (ih _ hcard _ ψ hψ T _ hsurj).mono (Nat.le_succ n)

/-- A simple image of a group that acts faithfully on `n` points embeds in `Sym(n)`. -/
theorem embedsInSym_of_surjective {X : Type*} [Finite X] {A T : Type*} [Group A] [Group T]
    [IsSimpleGroup T] (φ : A →* Perm X) (hφ : Function.Injective φ) (f : A →* T)
    (hf : Function.Surjective f) : EmbedsInSym (Nat.card X) T :=
  embedsInSym_of_surjective_aux _ X rfl A φ hφ T f hf

/-! ### Closure properties -/

/-- A simple image of a subgroup of a group in the class embeds. This is the definition with a
surjection in place of a quotient. -/
theorem GammaHat.embeds {d : ℕ} {G : Type*} [Group G] (h : GammaHat d G) (A : Subgroup G)
    {T : Type*} [Group T] [hT : IsSimpleGroup T] (f : A →* T) (hf : Function.Surjective f) :
    EmbedsInSym d T := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hs : IsSimpleGroup (A ⧸ f.ker) := e.isSimpleGroup
  exact (h A f.ker hs).of_injective e.symm.toMonoidHom e.symm.injective

theorem GammaHat.of_forall_embeds {d : ℕ} {G : Type u} [Group G]
    (h : ∀ (A : Subgroup G) (T : Type u) [Group T] [IsSimpleGroup T] (f : A →* T),
      Function.Surjective f → EmbedsInSym d T) : GammaHat d G :=
  fun A B _ _ => h A (A ⧸ B) (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)

theorem GammaHat.mono {d e : ℕ} (hde : d ≤ e) {G : Type*} [Group G] (h : GammaHat d G) :
    GammaHat e G :=
  fun A B _ hs => (h A B hs).mono hde

/-- **GNS Lemma 2.4, subgroups.** If `G` embeds in a group in the class, then `G` is in the class. -/
theorem GammaHat.of_injective {d : ℕ} {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) (h : GammaHat d H) : GammaHat d G := by
  refine GammaHat.of_forall_embeds fun A T _ _ f hf => ?_
  let e : A ≃* A.map φ := A.equivMapOfInjective φ hφ
  exact h.embeds (A.map φ) (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

/-- **GNS Lemma 2.4, images.** If `G` maps onto `H` and `G` is in the class, then `H` is. -/
theorem GammaHat.of_surjective {d : ℕ} {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) (h : GammaHat d G) : GammaHat d H := by
  refine GammaHat.of_forall_embeds fun A T _ _ f hf => ?_
  let ψ : A.comap φ →* A := (φ.comp (A.comap φ).subtype).codRestrict A fun a => a.2
  have hψ : Function.Surjective ψ := by
    intro a
    obtain ⟨g, hg⟩ := hφ a
    exact ⟨⟨g, by simp [hg]⟩, Subtype.ext hg⟩
  exact h.embeds (A.comap φ) (f.comp ψ) (hf.comp hψ)

/-- Subgroups of a group in the class are in the class. -/
theorem GammaHat.subgroup {d : ℕ} {G : Type*} [Group G] (h : GammaHat d G) (H : Subgroup G) :
    GammaHat d H :=
  h.of_injective H.subtype H.subtype_injective

/-- **Closure under extensions.** If `N` is normal in `G`, and `N` and `G / N` are in the class,
then so is `G`. Take a simple image `T` of `A ≤ G`. The image of `A ∩ N` is normal in `T`. If it
is `T`, then `T` is a simple image of a subgroup of `N`. If it is trivial, then `T` is a simple image
of the image of `A` in `G / N`. -/
theorem GammaHat.of_normal {d : ℕ} {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : GammaHat d N) (hQ : GammaHat d (G ⧸ N)) : GammaHat d G := by
  refine GammaHat.of_forall_embeds fun A T _ _ f hf => ?_
  let A₀ : Subgroup A := N.comap A.subtype
  have hA₀ : A₀.Normal := inferInstance
  rcases (hA₀.map f hf).eq_bot_or_eq_top with hbot | htop
  · -- `f` factors through the image of `A` in `G / N`.
    let π : A →* A.map (QuotientGroup.mk' N) :=
      ((QuotientGroup.mk' N).comp A.subtype).codRestrict _ fun a => ⟨a, a.2, rfl⟩
    have hπ : Function.Surjective π := by
      rintro ⟨_, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    have hle : π.ker ≤ f.ker := by
      intro a ha
      have ha' : (a : G) ∈ N := by
        have : ((a : G) : G ⧸ N) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 ha)
        exact (QuotientGroup.eq_one_iff _).1 this
      have : f a ∈ A₀.map f := ⟨a, ha', rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
    let g : A.map (QuotientGroup.mk' N) →* T :=
      (QuotientGroup.lift π.ker f hle).comp e.symm.toMonoidHom
    have hg : Function.Surjective g := by
      intro t
      obtain ⟨a, rfl⟩ := hf t
      refine ⟨π a, ?_⟩
      have : e.symm (π a) = (a : A ⧸ π.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      simp only [g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
      rfl
    exact hQ.embeds _ g hg
  · -- `A ∩ N`, seen inside `N`, maps onto `T`.
    let B : Subgroup N := (A.subgroupOf N)
    let j : B →* A :=
      { toFun := fun b => ⟨((b : N) : G), b.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Surjective (f.comp j) := by
      intro t
      have ht : t ∈ A₀.map f := htop ▸ Subgroup.mem_top t
      obtain ⟨a, ha, rfl⟩ := ht
      exact ⟨⟨⟨a, ha⟩, a.2⟩, rfl⟩
    exact hN.embeds B _ hj

/-- A group with a faithful action on `n` points is in `Γ̂_n`. This gives `Sym(n) ∈ Γ̂_n`. -/
theorem gammaHat_of_injective_perm {X G : Type*} [Finite X] [Group G] (φ : G →* Perm X)
    (hφ : Function.Injective φ) : GammaHat (Nat.card X) G :=
  fun A B _ _ => embedsInSym_of_surjective (φ.comp A.subtype) (hφ.comp A.subtype_injective)
    (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)

theorem gammaHat_perm (d : ℕ) : GammaHat d (Perm (Fin d)) := by
  simpa using gammaHat_of_injective_perm (MonoidHom.id (Perm (Fin d))) Function.injective_id

/-- A simple group is in the class exactly when it embeds in `Sym(d)`. So `GammaHat` agrees with
the definition by composition factors. -/
theorem gammaHat_simple_iff {d : ℕ} {T : Type*} [Group T] [IsSimpleGroup T] :
    GammaHat d T ↔ EmbedsInSym d T := by
  constructor
  · intro h
    exact h.embeds ⊤ (Subgroup.topEquiv (G := T)).toMonoidHom Subgroup.topEquiv.surjective
  · rintro ⟨f, hf⟩
    exact (gammaHat_perm d).of_injective f hf

/-- **The bound `aw(H) ≤ D` of Lemma 8.1 of the paper.** If `Alt(t)`, `t ≥ 5`, is an image of a
subgroup of a group in `Γ̂_d`, then `t ≤ d`, because `t! / 2` does not divide `d!` for `d < t`. -/
theorem GammaHat.le_of_alternating_section {d t : ℕ} {G : Type*} [Group G] (h : GammaHat d G)
    (ht : 5 ≤ t) (A : Subgroup G) (f : A →* alternatingGroup (Fin t))
    (hf : Function.Surjective f) : t ≤ d := by
  have : Nontrivial (Fin t) := Fin.nontrivial_iff_two_le.2 (by omega)
  have : IsSimpleGroup (alternatingGroup (Fin t)) :=
    alternatingGroup.isSimpleGroup (by simpa using ht)
  obtain ⟨g, hg⟩ := h.embeds A f hf
  by_contra hlt
  push Not at hlt
  have hc : Fintype.card (alternatingGroup (Fin t)) ≤ Fintype.card (Perm (Fin d)) :=
    Fintype.card_le_of_injective g hg
  have h2 := two_mul_card_alternatingGroup (α := Fin t)
  rw [Fintype.card_perm, Fintype.card_fin] at hc h2
  have h3 : d.factorial * (d + 1) ≤ t.factorial := by
    calc d.factorial * (d + 1) = (d + 1).factorial := by rw [Nat.factorial_succ, mul_comm]
      _ ≤ t.factorial := Nat.factorial_le hlt
  have h4 : 1 ≤ d.factorial := Nat.factorial_pos d
  have h5 : 120 ≤ t.factorial := by
    calc 120 = (5 : ℕ).factorial := rfl
      _ ≤ t.factorial := Nat.factorial_le ht
  rcases Nat.lt_or_ge d 2 with hd | hd
  · have : d.factorial = 1 := by
      interval_cases d <;> rfl
    omega
  · nlinarith

end GI.Degree
