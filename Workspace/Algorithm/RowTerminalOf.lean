import Workspace.Algorithm.DomainRestriction
import Workspace.Paper.RadicalFreeOrder
import Workspace.Paper.RowNormalFormDefs
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Row coordinates, and the group `G = K R₀` of Theorem A.23 from the row normal form

Theorem A.23 (`GI.Paper.thm_transitive_gat_terminal`) is stated on the row-tuple model: a
string on `B × [m]` is a tuple `x : Fin m → Ω₀` of row strings, and the group is
`G = K R₀ = {(k(h) μ, π) : h ∈ H, (μ, π) ∈ J}` (`GI.Multicoset.InG`), for normal data
`N ◁ H ≤ Sym(B)`, a map `φ : N → A` to an abelian group and lifts `k` with
`h⁻¹ k_i(h) ∈ N`. These are the outputs of Theorem A.18 ("All maps and lifts are supplied by
that theorem").

This file connects the model to a state. The row coordinates are a bijection
`e : B × Fin m ≃ dom`. The row string of row `i` is `c ↦ x(e(c, i))`, with the right action
`z^g = z ∘ g` of `Sym(B)`. A pair `(d, π)` moves the position `e(c, i)` to
`e(d_i⁻¹ c, π i)`; with this convention `(x^{(d,π)})_{π i} = x_i^{d_i}` is exactly the
statement that the position map carries `x` to `y` (`colors_iff_rowAct`).

## The group of the state is `K R₀`

The paper's terminal is applied to the faithful image `G|_dom` of the state, with the clean
complement `R₀ = s(Alt(m))` of Theorem A.17 and the row normal form `N* ◁ N ◁ H` of Theorem
A.18 (`GI.Paper.IsRowNormalForm`). We prove that every element of the state's group acts on
the domain as an element of `K R₀` in the sense of the model (`actsAs_inG`):

* the block kernel `K` (`blockKernel`) consists of the blockwise permutations
  `e(b, i) ↦ e(y_i b, i)` in `G|_dom`; conjugating by a pure element moves row `i` to row
  `i0`, so every coordinate `y_i` lies in `H = K[B_{i0}]` (`coords_mem_local`);
* the lift `k(h)` of `h ∈ H` is the coordinate tuple of an element of `K` with coordinate `h`
  at `i0` (`rowLift`); the diagonal clause of A.18 (`K/M` is the diagonal `H/N`) gives
  `h⁻¹ k_i(h) ∈ N` (`rowLift_mem`);
* for `y ∈ K` with `h = y_{i0}`, the quotient `k(h)⁻¹ y` lies in `M` by the same clause, and
  the zero-sum clause (`M/M*` is the zero-sum subgroup of `(N/N*)^m`) says its coordinates
  lie in `N` with total label `1` in `A = N/N*` (`kernel_decomp`);
* by the complement `G|_dom = K R₀`, a general element is `k s(p)` with `p` even, and acts as
  `(d, p)` with `d` the coordinates of an element of `K` (`actsAs_inG`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Multicoset GI.Paper

variable {Ω C : Type}

/-- The right action of `Sym(B)` on strings `B → C`: `z^g = z ∘ g`. -/
@[reducible] def stringRAct (B C : Type) : RAct (Perm B) (B → C) where
  act z g := z ∘ g
  act_one _ := rfl
  act_mul _ _ _ := rfl

attribute [local instance] stringRAct

section Rows

variable {S : State Ω C} {B : Type} {m : ℕ} (e : B × Fin m ≃ S.dom)

/-- The row tuple of a coloring: row `i` is the string `c ↦ x(e(c, i))`. -/
def rowTuple {C' : Type} (x : Ω → C') : Fin m → B → C' := fun i c => x (e (c, i))

/-- A permutation `g` of `Ω` acts on the domain as the pair `(d, π)`: it moves `e(c, i)` to
`e(d_i⁻¹ c, π i)`. -/
def ActsAs (g : Perm Ω) (d : Fin m → Perm B) (π : Perm (Fin m)) : Prop :=
  ∀ c i, g (e (c, i)) = e ((d i)⁻¹ c, π i)

/-- **The coordinates match the row action.** If `g` acts on the domain as `(d, π)`, then
`g` carries `x` to `y` on the domain exactly when `(d, π)` carries the row tuple of `x` to
that of `y` (`(x^{(d,π)})_{π i} = x_i^{d_i}`). -/
theorem colors_iff_rowAct {g : Perm Ω} {d : Fin m → Perm B} {π : Perm (Fin m)}
    (hg : ActsAs e g d π) (x y : Ω → C) :
    (∀ v ∈ S.dom, y (g v) = x v) ↔ rowAct d π (rowTuple e x) = rowTuple e y := by
  rw [rowAct_eq_iff]
  constructor
  · intro h i
    funext b
    have := h (e (d i b, i)) (e (d i b, i)).2
    rw [hg, Perm.inv_apply_self] at this
    exact this.symm
  · intro h v hv
    obtain ⟨⟨c, i⟩, hci⟩ := e.surjective ⟨v, hv⟩
    have hv' : v = e (c, i) := by rw [hci]
    have := congrFun (h i) ((d i)⁻¹ c)
    change x (e (d i ((d i)⁻¹ c), i)) = y (e ((d i)⁻¹ c, π i)) at this
    rw [Perm.apply_inv_self] at this
    rw [hv', hg]
    exact this.symm

end Rows

/-! ### The block kernel and its coordinates -/

section Kernel

variable {S : State Ω C} {B : Type} {m : ℕ} (e : B × Fin m ≃ S.dom)

/-- **The block kernel** `K ≤ G|_dom`: the elements that act blockwise in the coordinates `e`,
`e(b, i) ↦ e(y_i b, i)`. -/
def blockKernel : Subgroup S.domGroup := (cleanRowPerm e).range.subgroupOf S.domGroup

theorem cleanRowPerm_injective : Function.Injective (cleanRowPerm e) := by
  intro x y hxy
  funext i
  apply Equiv.ext
  intro b
  have h := congrArg (fun p : Perm S.dom => p (e (b, i))) hxy
  simp only [cleanRowPerm_apply] at h
  exact congrArg Prod.fst (e.injective h)

/-- The inverse of a pure element moves row `j` back: `s(p)⁻¹ e(b, j) = e(b, p⁻¹ j)`. -/
theorem pure_inv_apply {s : alternatingGroup (Fin m) →* S.domGroup}
    (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (p : alternatingGroup (Fin m))
    (b : B) (j : Fin m) : ((s p).val)⁻¹ (e (b, j)) = e (b, (p.val)⁻¹ j) := by
  rw [Perm.inv_eq_iff_eq, hpure, Perm.apply_inv_self]

/-- Conjugating a blockwise permutation by a pure element permutes its coordinates:
`s(p)⁻¹ (y) s(p) = (y ∘ p)`. -/
theorem conj_pure {s : alternatingGroup (Fin m) →* S.domGroup}
    (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (p : alternatingGroup (Fin m))
    (y : Fin m → Perm B) :
    ((s p).val)⁻¹ * cleanRowPerm e y * (s p).val = cleanRowPerm e (fun i => y (p.val i)) := by
  apply Equiv.ext
  intro v
  obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective v
  simp only [Perm.mul_apply, hpure, cleanRowPerm_apply, pure_inv_apply e hpure,
    Perm.inv_apply_self]

/-- **Every coordinate of an element of the block kernel lies in `H = K[B_{i0}]`.** Conjugate
by a pure element `s(p)` with `p(i0) = r`: it moves row `r` to row `i0` without changing the
within-row coordinate. -/
theorem coords_mem_local {s : alternatingGroup (Fin m) →* S.domGroup}
    (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (hm : 3 ≤ m) (i0 : Fin m)
    {y : Fin m → Perm B} (hy : cleanRowPerm e y ∈ S.domGroup) (r : Fin m) :
    y r ∈ cleanLocalGroup S.domGroup e i0 := by
  haveI : MulAction.IsPretransitive (alternatingGroup (Fin m)) (Fin m) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin m) (by simpa using hm)
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin m)) i0 r
  have hpr : p.val i0 = r := hp
  refine ⟨fun i => y (p.val i), ?_, by simp [rowEval, hpr]⟩
  change cleanRowPerm e (fun i => y (p.val i)) ∈ S.domGroup
  rw [← conj_pure e hpure p y]
  exact S.domGroup.mul_mem (S.domGroup.mul_mem (S.domGroup.inv_mem (s p).2) hy) (s p).2

end Kernel

/-! ### The lifts `k(h)` and the decomposition of the kernel -/

section Lifts

variable {S : State Ω C} {B : Type} [Fintype B] [DecidableEq B] {m : ℕ} (e : B × Fin m ≃ S.dom)
  (i0 : Fin m)

open Classical in
/-- **The lift `k(h)`** of `h ∈ H`: the coordinate tuple of an element of the block kernel whose
coordinate at `i0` is `h` (Theorem A.18: "`K/M` is the diagonal `H/N`"; the terminal's
"blockwise lift `k(τ) ∈ K` of `τ N`"). Off `H` it is the constant tuple. -/
noncomputable def rowLift (h : Perm B) : Fin m → Perm B :=
  if hh : h ∈ cleanLocalGroup S.domGroup e i0 then Classical.choose (Subgroup.mem_map.1 hh)
  else fun _ => h

theorem rowLift_spec {h : Perm B} (hh : h ∈ cleanLocalGroup S.domGroup e i0) :
    cleanRowPerm e (rowLift e i0 h) ∈ S.domGroup ∧ rowLift e i0 h i0 = h := by
  classical
  unfold rowLift
  rw [dif_pos hh]
  exact Classical.choose_spec (Subgroup.mem_map.1 hh)

variable {s : alternatingGroup (Fin m) →* S.domGroup}
  {Nl Nstar : Subgroup (cleanLocalGroup S.domGroup e i0)} [Nl.Normal] [Nstar.Normal]

/-- The coordinates of a blockwise element of `G|_dom`, as elements of `H`. -/
def coordsIn (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (hm : 3 ≤ m) {y : Fin m → Perm B} (hy : cleanRowPerm e y ∈ S.domGroup) :
    Fin m → cleanLocalGroup S.domGroup e i0 :=
  fun r => ⟨y r, coords_mem_local e hpure hm i0 hy r⟩

/-- `θ` of a blockwise element is the class of each of its coordinates. -/
theorem exists_theta (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (hm : 3 ≤ m)
    (hRNF : IsRowNormalForm S.domGroup (blockKernel e) e i0 s Nl Nstar) : ∃ θ : S.domGroup →* cleanLocalGroup S.domGroup e i0 ⧸ Nl,
    (∀ {y : Fin m → Perm B} (hy : cleanRowPerm e y ∈ S.domGroup) (r : Fin m),
      θ ⟨_, hy⟩ = ((coordsIn e i0 hpure hm hy r : cleanLocalGroup S.domGroup e i0) :
        cleanLocalGroup S.domGroup e i0 ⧸ Nl)) ∧
    (θ.comp (blockKernel e).subtype).ker = (rowNormalM S.domGroup (blockKernel e) e i0 Nl).subgroupOf
      (blockKernel e) := by
  obtain ⟨θ, hθ, -, hker, -⟩ := hRNF.diagonal
  exact ⟨θ, fun hy r => hθ ⟨_, hy⟩ (coordsIn e i0 hpure hm hy) r rfl, hker⟩

/-- **The lifts are lifts** (Theorem A.18): `h⁻¹ k_i(h) ∈ N` for `h ∈ H`. -/
theorem rowLift_mem (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (hm : 3 ≤ m)
    (hRNF : IsRowNormalForm S.domGroup (blockKernel e) e i0 s Nl Nstar) {h : Perm B} (hh : h ∈ cleanLocalGroup S.domGroup e i0) (i : Fin m) :
    h⁻¹ * rowLift e i0 h i ∈ Nl.map (cleanLocalGroup S.domGroup e i0).subtype := by
  obtain ⟨θ, hθ, -⟩ := exists_theta e i0 hpure hm hRNF
  obtain ⟨hmem, h0⟩ := rowLift_spec e i0 hh
  have h1 := hθ hmem i
  have h2 := hθ hmem i0
  rw [h1] at h2
  have := QuotientGroup.eq.1 h2.symm
  refine ⟨_, this, ?_⟩
  change (rowLift e i0 h i0)⁻¹ * rowLift e i0 h i = _
  rw [h0]

/-- **Decomposition of the block kernel** (Theorem A.18, the diagonal and zero-sum clauses).
Every blockwise element `y` of `G|_dom` is `k(h) μ` with `h = y_{i0} ∈ H`, `μ_i ∈ N` and total
label `∏ φ(μ_i) = 1`, for any `φ : N → A` with kernel `N*`. -/
theorem kernel_decomp (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (hm : 3 ≤ m)
    (hRNF : IsRowNormalForm S.domGroup (blockKernel e) e i0 s Nl Nstar) {A : Type} [CommGroup A]
    (φ : Nl.map (cleanLocalGroup S.domGroup e i0).subtype →* A)
    (hφ : ∀ n, φ n = 1 ↔ n.val ∈ Nstar.map (cleanLocalGroup S.domGroup e i0).subtype)
    {y : Fin m → Perm B} (hy : cleanRowPerm e y ∈ S.domGroup) :
    ∃ h ∈ cleanLocalGroup S.domGroup e i0, ∃ μ : Fin m → Perm B,
      (∀ i, μ i ∈ Nl.map (cleanLocalGroup S.domGroup e i0).subtype) ∧
      ∏ i, phiT (Nl.map (cleanLocalGroup S.domGroup e i0).subtype) φ (μ i) = 1 ∧
      y = rowLift e i0 (y i0) * μ := by
  classical
  have hh : y i0 ∈ cleanLocalGroup S.domGroup e i0 := coords_mem_local e hpure hm i0 hy i0
  obtain ⟨hlift, hl0⟩ := rowLift_spec e i0 hh
  set x := rowLift e i0 (y i0)
  set μ : Fin m → Perm B := fun i => (x i)⁻¹ * y i
  have hμy : y = x * μ := by funext i; simp [μ]
  -- The element `k(h)⁻¹ y` of `G|_dom`.
  have hcμ : cleanRowPerm e μ = (cleanRowPerm e x)⁻¹ * cleanRowPerm e y := by
    rw [← map_inv, ← map_mul]; rfl
  have hμmem : cleanRowPerm e μ ∈ S.domGroup := by
    rw [hcμ]; exact S.domGroup.mul_mem (S.domGroup.inv_mem hlift) hy
  have hK : (⟨_, hμmem⟩ : S.domGroup) ∈ blockKernel e := ⟨μ, rfl⟩
  -- Its `θ` is trivial, so it lies in `M`.
  obtain ⟨θ, hθ, hker⟩ := exists_theta e i0 hpure hm hRNF
  have hθ1 : θ ⟨_, hμmem⟩ = 1 := by
    rw [hθ hμmem i0, QuotientGroup.eq_one_iff]
    have h1 : (coordsIn e i0 hpure hm hμmem i0 : Perm B) = (x i0)⁻¹ * y i0 := rfl
    have h2 : (coordsIn e i0 hpure hm hμmem i0 : Perm B) = 1 := by rw [h1, hl0, inv_mul_cancel]
    have : coordsIn e i0 hpure hm hμmem i0 = 1 := Subtype.ext h2
    rw [this]; exact Nl.one_mem
  have hM : (⟨_, hμmem⟩ : S.domGroup) ∈ rowNormalM S.domGroup (blockKernel e) e i0 Nl := by
    have : (⟨⟨_, hμmem⟩, hK⟩ : blockKernel e) ∈ (θ.comp (blockKernel e).subtype).ker := hθ1
    rw [hker] at this
    exact this
  -- Its coordinates lie in `N`.
  obtain ⟨z, hz, hzμ⟩ := (Subgroup.mem_inf.1 hM).2
  have hzμ' : (fun r => (z r : Perm B)) = μ := cleanRowPerm_injective e hzμ
  have hμN : ∀ i, μ i ∈ Nl.map (cleanLocalGroup S.domGroup e i0).subtype := fun i => ⟨z i, hz i, by rw [← hzμ']; rfl⟩
  refine ⟨y i0, hh, μ, hμN, ?_, hμy⟩
  -- The zero-sum clause: the total of the coordinates lies in `N*`.
  obtain ⟨ψ, hψ, -, hrange⟩ := hRNF.zero_sum
  have hψz := hψ ⟨_, hM⟩ z (by rw [hzμ]; rfl)
  have hzs : (fun r => ((z r : cleanLocalGroup S.domGroup e i0) :
      cleanLocalGroup S.domGroup e i0 ⧸ Nstar)) ∈ rowZeroSum Nl Nstar := by
    rw [← hrange, ← hψz]; exact ⟨_, rfl⟩
  have htot : ((Finset.univ.toList.map z).prod : cleanLocalGroup S.domGroup e i0 ⧸ Nstar) = 1 := by
    rw [← hzs.2]
    change QuotientGroup.mk' Nstar (Finset.univ.toList.map z).prod = _
    rw [map_list_prod, List.map_map]
    rfl
  rw [QuotientGroup.eq_one_iff] at htot
  -- So the total label is `1`.
  let μN : Fin m → Nl.map (cleanLocalGroup S.domGroup e i0).subtype := fun i => ⟨μ i, hμN i⟩
  have hphi : ∀ i, phiT (Nl.map (cleanLocalGroup S.domGroup e i0).subtype) φ (μ i) = φ (μN i) := fun i => by
    simp only [phiT, dif_pos (hμN i)]; rfl
  simp_rw [hphi]
  rw [← Finset.prod_map_toList, show (fun x => φ (μN x)) = ⇑φ ∘ μN from rfl, ← List.map_map,
    ← map_list_prod, hφ]
  have e1 : (Subgroup.subtype _) (Finset.univ.toList.map μN).prod =
      (Finset.univ.toList.map μ).prod := by
    rw [map_list_prod, List.map_map]; rfl
  have e2 : (cleanLocalGroup S.domGroup e i0).subtype (Finset.univ.toList.map z).prod =
      (Finset.univ.toList.map μ).prod := by
    rw [map_list_prod, List.map_map, ← hzμ']; rfl
  exact ⟨_, htot, e2.trans e1.symm⟩

/-- **The state's group lies in `K R₀`** (the hypothesis of Theorem A.23, derived from Theorems
A.17 and A.18). With the clean complement `R₀ = s(Alt(m))` of the block kernel, every element of
the state's group acts on the domain as `(d, π)` with `(d, π) ∈ G = K R₀` of the model. -/
theorem actsAs_inG (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (hm : 3 ≤ m)
    (hRNF : IsRowNormalForm S.domGroup (blockKernel e) e i0 s Nl Nstar) (hcompl : (blockKernel e).IsComplement' s.range) {A : Type} [CommGroup A]
    (φ : Nl.map (cleanLocalGroup S.domGroup e i0).subtype →* A)
    (hφ : ∀ n, φ n = 1 ↔ n.val ∈ Nstar.map (cleanLocalGroup S.domGroup e i0).subtype) :
    ∀ g ∈ S.G, ∃ d π, InG (cleanLocalGroup S.domGroup e i0)
      (Nl.map (cleanLocalGroup S.domGroup e i0).subtype) φ (rowLift e i0) d π ∧ ActsAs e g d π := by
  intro g hg
  set g' : S.domGroup := ⟨S.domHom ⟨g, hg⟩, ⟨_, rfl⟩⟩
  -- `g = k s(p)` with `k` blockwise.
  obtain ⟨⟨⟨k₀, hk₀⟩, ⟨r, hr⟩⟩, hkr, -⟩ := hcompl.existsUnique g'
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨y, hy⟩ := hk₀
  change cleanRowPerm e y = (k₀ : Perm S.dom) at hy
  have hkr' : (k₀ : Perm S.dom) * (s p).val = S.domHom ⟨g, hg⟩ := congrArg Subtype.val hkr
  -- The coordinates of `s(p)⁻¹ k⁻¹ s(p)`, which act as `d`.
  set d : Fin m → Perm B := fun i => (y (p.val i))⁻¹
  have hd : cleanRowPerm e d = ((s p).val)⁻¹ * (k₀ : Perm S.dom)⁻¹ * (s p).val := by
    rw [← hy, ← map_inv, conj_pure e hpure]
    rfl
  have hdmem : cleanRowPerm e d ∈ S.domGroup := by
    rw [hd]
    exact S.domGroup.mul_mem (S.domGroup.mul_mem (S.domGroup.inv_mem (s p).2)
      (S.domGroup.inv_mem k₀.2)) (s p).2
  obtain ⟨-, -, μ, hμN, hμ1, hdμ⟩ := kernel_decomp e i0 hpure hm hRNF φ hφ hdmem
  refine ⟨d, p.val, ⟨d i0, coords_mem_local e hpure hm i0 hdmem i0, μ, ⟨hμN, hμ1, p.2⟩, hdμ⟩,
    fun c i => ?_⟩
  have := congrArg (fun q : Perm S.dom => (q (e (c, i)) : Ω)) hkr'
  simp only [Perm.mul_apply, hpure, State.domHom_apply] at this
  rw [← this, ← hy, cleanRowPerm_apply]
  simp [d]

end Lifts

end GI.Algorithm
