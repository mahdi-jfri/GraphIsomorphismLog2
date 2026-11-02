import Workspace.Impl.TermAsm

/-!
# The lift of the table transport to the domain (T7, mathematics)

Theorem A.23 ends with the `J`-elements above each residual element, "lifted to `Ω`". The table
transport `I.tableTransport TN TH` is a set of pairs `(d, π)`. A pair acts on the domain by
`e(c, i) ↦ e(d_i⁻¹ c, π i)` (`ActsAs`). This file collects what the program of T7 needs:

* `tmDomSet e T`: the permutations of the domain that act as a pair of `T`;
* `tm_liftAnswer_eq`: for the exact tables, the elements of `G` whose restriction lies in
  `tmDomSet` form the answer of the state (Theorem A.23 through `RowTerminal.exact`);
* `tm_domSet_le`: every permutation in `tmDomSet` lies in `G|_dom`. This is the inclusion
  `K R₀ ≤ G` of Theorems A.17 and A.18, the converse of `actsAs_inG`: the even row
  permutations come from the clean complement `s`, the lifts `k(h)` are blockwise elements of
  `G|_dom` (`rowLift_spec`), and a zero-sum tuple of `N` is an element of `M` times an element of
  `(N*)^m` (the zero-sum clause of A.18 and `M* ≤ G`, `tm_zeroSum_mem`).

The second fact is the precondition of the lift (`lift_spec`: the set to lift lies in the image
of the restriction).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm

variable {Ω C : Type}

/-- The permutations of the domain that act as a pair of `T`: `e(c, i) ↦ e(d_i⁻¹ c, π i)`. -/
def tmDomSet {S : State Ω C} {B : Type} {q : ℕ} (e : B × Fin q ≃ S.dom)
    (T : Set ((Fin q → Perm B) × Perm (Fin q))) : Set (Perm S.dom) :=
  {σ | ∃ p ∈ T, ∀ c i, σ (e (c, i)) = e ((p.1 i)⁻¹ c, p.2 i)}

/-- The restriction of `g` lies in `tmDomSet e T` exactly when `g` acts as a pair of `T`. -/
theorem tm_domHom_mem_domSet {S : State Ω C} {B : Type} {q : ℕ} (e : B × Fin q ≃ S.dom)
    (T : Set ((Fin q → Perm B) × Perm (Fin q))) {g : Perm Ω} (hg : g ∈ S.G) :
    S.domHom ⟨g, hg⟩ ∈ tmDomSet e T ↔ ∃ p ∈ T, ActsAs e g p.1 p.2 := by
  refine exists_congr fun p => and_congr_right fun _ => forall_congr' fun c =>
    forall_congr' fun i => ?_
  rw [Subtype.ext_iff, State.domHom_apply]

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- The table transport of the exact tables. -/
noncomputable def tmExactT (I : RowTerminal P S L) : Set ((Fin L.q → Perm I.B) × Perm (Fin L.q)) :=
  I.tableTransport (fun ac => (I.typeCall ac).answer) (fun ij => (I.cosetCall ij).answer)

/-- **The assembly of the exact tables is the answer of the state** (`RowTerminal.exact`). -/
theorem tmL_assemble_exact :
    I.assemble (fun ac => (I.typeCall ac).answer) (fun ij => (I.cosetCall ij).answer) =
      S.answer := by
  classical
  have h := I.exact
  simp only [RowTerminal.script, Script.evalExact_bind, Script.evalExact] at h
  have hTN : (Script.table I.typeCall I.tests).evalExact = fun ac => (I.typeCall ac).answer :=
    funext fun ac => Script.evalExact_table _ _ ac (I.mem_tests ac)
  have hTH : (Script.table I.cosetCall I.cosets).evalExact = fun ij => (I.cosetCall ij).answer :=
    funext fun ij => Script.evalExact_table _ _ ij (I.mem_cosets ij)
  rwa [hTN, hTH] at h

/-- **The lift of the exact table transport is the answer of the state.** -/
theorem tm_liftAnswer_eq : S.liftAnswer (tmDomSet I.e (tmExactT I)) = S.answer := by
  rw [← tmL_assemble_exact I]
  ext g
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, (tm_domHom_mem_domSet I.e _ hg).1 h⟩
  · rintro ⟨hg, h⟩
    exact ⟨hg, (tm_domHom_mem_domSet I.e _ hg).2 h⟩

/-- **A zero-sum tuple of `N` acts blockwise by an element of `G|_dom`** (Theorem A.18: `M/M*` is
the zero-sum subgroup of `(N/N*)^m`, and `M* = (N*)^m ≤ G`). -/
theorem tm_zeroSum_mem {μ : Fin L.q → Perm I.B} (hμ : ∀ i, μ i ∈ I.Nb)
    (hsum : ∏ i, phiT I.Nb I.φ (μ i) = 1) : cleanRowPerm I.e μ ∈ S.domGroup := by
  classical
  -- `μ` as tuples of `H` and of `N`.
  let μH : Fin L.q → I.Hb := fun i => ⟨μ i, I.Nb_le (hμ i)⟩
  let μN : Fin L.q → I.Nb := fun i => ⟨μ i, hμ i⟩
  -- The total of `μ` lies in `N*`.
  have hphi : ∀ i, phiT I.Nb I.φ (μ i) = I.φ (μN i) := fun i => by
    simp only [phiT, dif_pos (hμ i)]; rfl
  simp_rw [hphi] at hsum
  rw [← Finset.prod_map_toList, show (fun x => I.φ (μN x)) = ⇑I.φ ∘ μN from rfl,
    ← List.map_map, ← map_list_prod, I.φ_ker] at hsum
  obtain ⟨x, hx, hxμ⟩ := hsum
  have e1 : (Subgroup.subtype _) (Finset.univ.toList.map μN).prod =
      (Finset.univ.toList.map μ).prod := by
    rw [map_list_prod, List.map_map]; rfl
  have e2 : I.Hb.subtype (Finset.univ.toList.map μH).prod = (Finset.univ.toList.map μ).prod := by
    rw [map_list_prod, List.map_map]; rfl
  have hxH : x = (Finset.univ.toList.map μH).prod :=
    Subtype.val_injective (hxμ.trans (e1.trans e2.symm))
  -- The classes of `μ` modulo `N*` form a zero-sum tuple.
  have hμNl : ∀ r, μH r ∈ I.Nl := fun r => by
    obtain ⟨n, hn, hnμ⟩ := hμ r
    have : n = μH r := Subtype.val_injective hnμ
    rw [← this]; exact hn
  have hzs : (fun r => ((μH r : I.Hb) : I.Hb ⧸ I.Nstar)) ∈ rowZeroSum I.Nl I.Nstar := by
    refine ⟨fun r => ⟨μH r, hμNl r, rfl⟩, ?_⟩
    change (Finset.univ.toList.map fun r => QuotientGroup.mk' I.Nstar (μH r)).prod = 1
    rw [show (fun r => QuotientGroup.mk' I.Nstar (μH r)) = (QuotientGroup.mk' I.Nstar) ∘ μH from rfl,
      ← List.map_map, ← map_list_prod, ← hxH,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  -- So it is the image of an element `g` of `M`, whose coordinates `z` agree with `μ` mod `N*`.
  obtain ⟨ψ, hψ, -, hrange⟩ := I.rnf.zero_sum
  rw [← hrange] at hzs
  obtain ⟨g, hg⟩ := hzs
  obtain ⟨z, hz, hzg⟩ := (Subgroup.mem_inf.1 g.2).2
  have hψz := hψ g z hzg
  have hrel : ∀ r, (z r)⁻¹ * μH r ∈ I.Nstar := fun r => by
    have := congrFun (hψz.symm.trans hg) r
    exact QuotientGroup.eq.1 this
  -- `μ = z · ((z⁻¹ μ))`, with `cleanLift z ∈ G|_dom` and `(z⁻¹ μ) ∈ (N*)^m`.
  have hstar : cleanLift I.e I.Hb (fun r => (z r)⁻¹ * μH r) ∈ S.domGroup :=
    I.rnf.mstar_le_G ⟨_, hrel, rfl⟩
  have hmul : cleanRowPerm I.e μ =
      cleanLift I.e I.Hb z * cleanLift I.e I.Hb (fun r => (z r)⁻¹ * μH r) := by
    rw [← map_mul]
    change cleanRowPerm I.e μ = cleanRowPerm I.e (fun r => ((z * fun r => (z r)⁻¹ * μH r) r).val)
    congr 1
    funext r
    simp [μH]
  rw [hmul]
  refine S.domGroup.mul_mem ?_ hstar
  have : cleanLift I.e I.Hb z = ((g : S.domGroup) : Perm S.dom) := hzg
  rw [this]
  exact (g : S.domGroup).2

/-- **Every pair of `G = K R₀` acts by an element of `G|_dom`** (the converse of `actsAs_inG`). -/
theorem tm_inG_mem {d : Fin L.q → Perm I.B} {π : Perm (Fin L.q)}
    (h : InG I.Hb I.Nb I.φ (rowLift I.e I.i0) d π) :
    ∃ σ ∈ S.domGroup, ∀ c i, σ (I.e (c, i)) = I.e ((d i)⁻¹ c, π i) := by
  obtain ⟨h, hh, μ, ⟨hμN, hμ1, hπ⟩, rfl⟩ := h
  have hd : cleanRowPerm I.e (rowLift I.e I.i0 h * μ) ∈ S.domGroup := by
    rw [map_mul]
    exact S.domGroup.mul_mem (rowLift_spec I.e I.i0 hh).1 (tm_zeroSum_mem I hμN hμ1)
  refine ⟨(I.s ⟨π, hπ⟩).val * (cleanRowPerm I.e (rowLift I.e I.i0 h * μ))⁻¹,
    S.domGroup.mul_mem (I.s ⟨π, hπ⟩).2 (S.domGroup.inv_mem hd), fun c i => ?_⟩
  rw [Perm.mul_apply, ← map_inv, cleanRowPerm_apply, I.pure]
  rfl

/-- **The lifted table transport lies in `G|_dom`** (exact tables). -/
theorem tm_domSet_le : tmDomSet I.e (tmExactT I) ⊆ (restrictHom S.G S.dom S.dom_inv).range := by
  rintro σ ⟨p, hp, hσ⟩
  have hp' : p ∈ terminalTransport I.Hb I.Nb I.φ (rowLift I.e I.i0) (rowTuple I.e S.x)
      (rowTuple I.e S.y) := by
    rw [← I.tableTransport_exact]; exact hp
  rw [terminalTransport_eq I.Nb_le I.normalizes (fun h hh i => I.lift_mem hh i)] at hp'
  obtain ⟨τ, hτ, hτp⟩ := tm_inG_mem I hp'.1
  have : σ = τ := by
    apply Equiv.ext
    intro v
    obtain ⟨⟨c, i⟩, rfl⟩ := I.e.surjective v
    rw [hσ, hτp]
  rw [this]
  exact hτ

end RT

end GI.Impl
