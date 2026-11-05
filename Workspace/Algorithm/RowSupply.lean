module

public import Workspace.Algorithm.RowFormOf
public import Workspace.Algorithm.SupplyBuild
public import Workspace.Algorithm.Cases

@[expose] public section

/-!
# The row branch of the giant step

Algorithm 4 (RowStep), after the row normal form (`exists_rowForm`):

* "if `L` is transitive on a row then": the terminal data (`RowForm.rowTerminal`), with
  `A = N/N*` from Theorem A.23 and the row size bound of Section 6.2;
* "else": the column step (`RowForm.columnStep`), whose refactored hierarchy satisfies the
  invariant (`ColumnPre.hierInv`, from Lemma A.14 in coordinates).

`GiantSupply.ofAggregate` assembles the giant-step data from the row branch and the
aggregation data of the non-row case. It needs the cited result used by Theorem A.18 and the
parameter condition `Params.RowThreshold`: the threshold `N^α` of the row case is above the
logarithmic threshold of Theorem A.18 (Section 6.2: "for sufficiently large `N`").
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper
open scoped Pointwise

variable {Ω C : Type}

/-- **The row threshold** (Theorem A.18 under the row case): above the base size, `N^α` is at
least the logarithmic threshold `2 max{63, 12 log₂ N} + 3`. It holds for large `N₀` because
`N^α` grows faster than `log N`. -/
def Params.RowThreshold (P : Params) : Prop :=
  ∀ N : ℕ, P.N₀ < N → 2 * max 63 (12 * Real.logb 2 N) + 3 ≤ (N : ℝ) ^ P.α

namespace RowForm

variable {S : State Ω C} {L : GiantLabels S} (F : RowForm S L)

/-- `A = N/N*`. -/
abbrev QuotA : Type := F.Nl ⧸ F.Nstar.subgroupOf F.Nl

/-- `A` is abelian: the row normal form puts the commutators of `N` in `N*`. -/
noncomputable instance : CommGroup F.QuotA :=
  { (inferInstance : Group F.QuotA) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have := F.rnf.abelian (b⁻¹ : F.Nl) (b⁻¹ : F.Nl).2 (a⁻¹ : F.Nl) (a⁻¹ : F.Nl).2
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group }

/-- The identification `N ≅ N.map ι` with the image of `N` in `Sym(B)`. -/
noncomputable def nlEquiv : F.Nl ≃* F.Nl.map F.Hb.subtype :=
  Subgroup.equivMapOfInjective F.Nl F.Hb.subtype Subtype.val_injective

/-- **The terminal data** (Theorem A.23) with a chosen solvable-quotient subgroup `R' ≤ H`:
`N` transitive on `B`, `A = N/N*`. The row size bound uses the row case `N^α < q` and `|B| q = s ≤ N`. -/
noncomputable def rowTerminalWith (P : Params) (htr : MulAction.IsPretransitive F.Nl F.B)
    (hcard : Fintype.card F.B * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hq : (S.N : ℝ) ^ P.α < L.q) (R' : Subgroup (Perm F.B))
    (hRH : R' ≤ F.Hb) (hNR : F.Nb ≤ R')
    (hsolv : ∃ ℓ, GI.Multicoset.relDerived R' F.Nb ℓ ≤ F.Nb) : RowTerminal P S L where
  toRowForm := F
  A := F.QuotA
  φ := (QuotientGroup.mk' _).comp F.nlEquiv.symm.toMonoidHom
  φ_ker n := by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.mem_map]
    have hn : n.val = ((F.nlEquiv.symm.toMonoidHom n : F.Nl) : F.Hb).val := by
      have := congrArg Subtype.val (F.nlEquiv.apply_symm_apply n)
      rw [← this]
      rfl
    constructor
    · intro h
      exact ⟨_, h, hn.symm⟩
    · rintro ⟨x, hx, hxn⟩
      have : x = ((F.nlEquiv.symm.toMonoidHom n : F.Nl) : F.Hb) :=
        Subtype.val_injective (hxn.trans hn)
      rw [← this]
      exact hx
  transitive := htr
  row_size := by
    have := row_size_lt hN (f := Fintype.card F.B) (by rw [hcard]; exact hsN) hq
    exact this.le
  tests := Finset.univ.toList
  tests_nodup := Finset.nodup_toList _
  mem_tests _ := Finset.mem_toList.2 (Finset.mem_univ _)
  cosets := Finset.univ.toList
  cosets_nodup := Finset.nodup_toList _
  mem_cosets _ := Finset.mem_toList.2 (Finset.mem_univ _)
  rad := R'
  rad_le := hRH
  Nb_le_rad := hNR
  rad_solv := hsolv

/-- **The terminal data** (Theorem A.23): `N` transitive on `B`, `A = N/N*`. The row size bound
uses the row case `N^α < q` and `|B| q = s ≤ N`. -/
noncomputable def rowTerminal (P : Params) (htr : MulAction.IsPretransitive F.Nl F.B)
    (hcard : Fintype.card F.B * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hq : (S.N : ℝ) ^ P.α < L.q) : RowTerminal P S L :=
  F.rowTerminalWith P htr hcard hsN hN hq (GI.Multicoset.radicalSubgroup F.Hb F.Nb)
    (GI.Multicoset.radicalSubgroup_spec F.Nb_le F.normalizes).1
    (GI.Multicoset.radicalSubgroup_spec F.Nb_le F.normalizes).2.1
    (GI.Multicoset.radicalSubgroup_spec F.Nb_le F.normalizes).2.2

/-- `N` intransitive on a nonempty `B` has at least two orbits. -/
theorem two_le_orbits [Nonempty F.B] (hnt : ¬ MulAction.IsPretransitive F.Nl F.B) :
    2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)) := by
  by_contra h
  apply hnt
  have h1 : Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)) ≤ 1 := by omega
  haveI : Subsingleton (Quotient (MulAction.orbitRel F.Nl F.B)) :=
    (Finite.card_le_one_iff_subsingleton).1 h1
  refine ⟨fun x y => ?_⟩
  have : (Quotient.mk _ y : Quotient (MulAction.orbitRel F.Nl F.B)) = Quotient.mk _ x :=
    Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact this)
  exact ⟨g, hg⟩

end RowForm

/-- **The selected interval has bound at least `q`** (Section 7.2: "The old cap is at least `q`
because the selected alternating section belongs to that whole constituent"). Its coarse end
holds the domain, and an element that fixes each of its fine classes has trivial label image, so
the whole group is the stabilizer of the coarse class and maps onto `Alt(q)`. -/
theorem SuppliedLabels.le_cap {S : State Ω C} (L : SuppliedLabels S) (hinv : S.HierInv)
    (htr : S.Transitive) (hq : 5 ≤ L.q) (hne : S.dom.Nonempty) : L.q ≤ S.hier[L.sel].cap := by
  obtain ⟨a, ha⟩ := hne
  have hinv' : HierInv S.G S.dom S.hier := hinv
  refine le_of_capAt (caps_getElem ⊥ S.hier hinv'.caps L.sel L.sel.2 a ha) S.dom_inv
    (chain_getElem _ _ hinv'.chain L.sel L.sel.2).1 ha L.π L.π_surj hq
    (fun g => ⟨1, map_one _, ?_⟩) (fun g _ hfix => (L.sel_ker g).2 fun w hw => ?_)
  · have hga : (g : Perm Ω) a ∈ S.dom := (S.dom_inv g g.2 a).2 ha
    simp only [one_mul]
    exact ⟨hga, ⟨g, g.2, rfl⟩, L.sel_univ a ha _ hga⟩
  · exact hfix w ⟨hw, htr a ha w hw, L.sel_univ a ha w hw⟩

/-- Labels on at least three points need a nonempty domain: they are read on the domain. -/
theorem SuppliedLabels.dom_nonempty {S : State Ω C} (L : SuppliedLabels S) (hq : 3 ≤ L.q) :
    S.dom.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  haveI := alternatingGroup.nontrivial_of_three_le_card (α := Fin L.q) (by simpa using hq)
  obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin L.q))
  obtain ⟨g, rfl⟩ := L.π_surj x
  refine hx (L.con.onDomain g ?_)
  ext v
  exact (Set.eq_empty_iff_forall_notMem.1 h v.1 v.2).elim

/-- The selected interval keeps its bound below its ratio (Section 3.3). -/
theorem SuppliedLabels.cap_le_ratio {S : State Ω C} (L : SuppliedLabels S) (hinv : S.HierInv) :
    S.hier[L.sel].cap ≤ S.hier[L.sel].ratio :=
  (chain_getElem _ _ (show HierInv S.G S.dom S.hier from hinv).chain L.sel L.sel.2).2.2.2

/-- **An aggregation round on the supplied labels**: the selected interval and the constituent
data are those of the labels. The script does not change: it reads the constituent data only
through a proof that the labels are read on the domain. -/
noncomputable def Aggregation.withLabels {P : Params} [Finite Ω] {S : State Ω C}
    {L : SuppliedLabels S} (I : Aggregation P S L.toGiantLabels) (hinv : S.HierInv) :
    Aggregation P S L.toGiantLabels :=
  { I with
    sel := L.sel
    sel_cap := L.le_cap hinv I.htr (by have := I.q_ten; omega)
      (L.dom_nonempty (by have := I.q_ten; omega))
    sel_clamped := L.cap_le_ratio hinv
    con := L.con }

/-- **The row branch** (Algorithm 4): the case decision of RowStep. -/
noncomputable def rowBranch {P : Params}
    (hT : P.RowThreshold) [Finite Ω] (S : State Ω C) (hinv : S.HierInv) (hN₀ : P.N₀ < S.N)
    (hsN : S.size ≤ S.N) (htr : S.Transitive) (hγ : (S.N : ℝ) ^ P.γ < S.size)
    (L : SuppliedLabels S) (hrow : RowCase P.α S L.toGiantLabels) : GiantCase P S L := by
  classical
  have hspos : 0 < S.size := by
    have : (0 : ℝ) < S.size := lt_of_le_of_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _) hγ
    exact_mod_cast this
  have hne : S.dom.Nonempty := by
    have : Nonempty S.dom := (Nat.card_pos_iff.1 hspos).1
    exact ⟨this.some.1, this.some.2⟩
  have hthr : 2 * max 63 (12 * Real.logb 2 S.size) + 3 ≤ (L.q : ℝ) := by
    have hlog : Real.logb 2 S.size ≤ Real.logb 2 S.N :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hspos) (by exact_mod_cast hsN)
    have h1 := hT S.N hN₀
    have : max 63 (12 * Real.logb 2 S.size) ≤ max 63 (12 * Real.logb 2 S.N) :=
      max_le_max le_rfl (by linarith)
    linarith [hrow.1]
  have hex := exists_rowForm S L (Classical.choose_spec hrow.2.1) hthr
  let F := Classical.choose hex
  have hcard : Fintype.card F.B * L.q = S.size := (Classical.choose_spec hex).2
  by_cases hNt : MulAction.IsPretransitive F.Nl F.B
  · exact .terminal hrow (F.rowTerminal P hNt hcard hsN (by omega) hrow.1)
  · haveI hB : Nonempty F.B := ⟨(F.e.symm ⟨hne.some, hne.some_mem⟩).1⟩
    let I := F.columnStep (F.two_le_orbits hNt) htr hinv hne
    exact .columns hrow I (I.hierInv htr)

/-- **The giant-step data from the aggregation data.** The row case is the row branch; the other
case is an aggregation round, supplied by `agg`. -/
noncomputable def GiantSupply.ofAggregate {P : Params}
    (hT : P.RowThreshold)
    (agg : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
      S.Transitive → (S.N : ℝ) ^ P.γ < S.size → (L : SuppliedLabels S) → P.q₀ < L.q →
      ¬ RowCase P.α S L →
        {I : Aggregation P S L // I.script.CallsExact fun {Ω' _} _ _ => Finite Ω'}) :
    GiantSupply P where
  giant S hinv hN₀ hsN htr hγ L hq := by
    classical
    by_cases hrow : RowCase P.α S L
    · exact rowBranch hT S hinv hN₀ hsN htr hγ L hrow
    · have I := agg S hinv hN₀ hsN htr hγ L hq hrow
      exact .aggregate hrow (I.1.withLabels hinv) rfl rfl I.2

end GI.Algorithm
