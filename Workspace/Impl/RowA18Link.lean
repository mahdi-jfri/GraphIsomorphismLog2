module

public import Workspace.Impl.RowA18
public import Workspace.Impl.RowKer

@[expose] public section

/-!
# From graph-form generators to the groups of Theorem A.18

The programs of the row step carry subgroups of `G` in graph form (`PairGens`), on the `n`
positions of `Ω`. Theorem A.18 speaks of subgroups of `Sym(B)`, `B = Fin m`, the row-`0` images
of row-preserving subgroups of `G|_dom` (`Hb_eq_rowPart`, `Nb_eq_rowPart`, `Nstar_eq_rowPart`).
This file links the two, for coordinates `E : Fin m × Fin q ≃ dom` whose block `i` is the label
fiber `i`.

* `mem_rowPres_iff`: an element of `G` preserves every row exactly when its label image is
  trivial.
* `mem_fixPos_rowList_iff`, `mem_fixPos_off0_iff`: fixing the positions of row `1` (or of all
  rows but `0`) is fixing these rows of the domain.
* `partNat`: the row-`0` part of a permutation of positions, as the program computes it (for each
  `β`, the index of `a (zs[β])` in the list `zs` of row-`0` positions). For an element of `G`
  that preserves rows it is `rowPart E 0` of its restriction (`partNat_eq`).
* `closure_parts`: the row-`0` parts of graph-form generators of `A` generate the row-`0` image of
  the corresponding subgroup of `G|_dom`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {Ω C : Type} {n : ℕ} (e : Ω ≃ Fin n) {S : State Ω C} {L : GiantLabels S}
  {label : Ω → Fin L.q} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom)

/-! ### Rows and labels -/

theorem label_of_coords (hE : ∀ b i, label (E (b, i)) = i) (w : S.dom) :
    label w = (E.symm w).2 := by
  conv_lhs => rw [← E.apply_symm_apply w]
  exact hE _ _

/-- **Row-preserving is label-trivial.** -/
theorem mem_rowPres_iff (hnat : NaturalRows S L label) (hE : ∀ b i, label (E (b, i)) = i)
    (g : S.G) : S.domHom g ∈ rowPres E ↔ L.π g = 1 := by
  have key : ∀ b i, (E.symm (S.domHom g (E (b, i)))).2 = ((L.π g).val i) := by
    intro b i
    rw [← label_of_coords E hE, State.domHom_apply, hnat.equivariant g _ (E (b, i)).2]
    exact congrArg _ (hE b i)
  constructor
  · intro h
    apply Subtype.ext
    ext i
    obtain ⟨v, hv, hvi⟩ := hnat.onto i
    obtain ⟨⟨b, j⟩, hbj⟩ := E.surjective ⟨v, hv⟩
    have hj : j = i := by
      have := hE b j
      rw [hbj] at this
      exact this.symm.trans hvi
    subst hj
    have := (key b j).symm.trans (h b j)
    simpa using congrArg Fin.val this
  · intro h b i
    rw [key, h]
    rfl

/-- The positions of row `j`, `β = 0, …, m - 1`. -/
def rowList (j : Fin L.q) : List (Fin n) := (List.finRange m).map fun β => e (E (β, j))

theorem toFin_apply_e (g : Perm Ω) (x : Ω) : toFin e g (e x) = e (g x) := by
  simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem fixPos_iff_dom {X : List (Fin n)} (g : S.G) (T : Set S.dom)
    (hX : ∀ i, i ∈ X ↔ ∃ h : e.symm i ∈ S.dom, (⟨e.symm i, h⟩ : S.dom) ∈ T) :
    g.val ∈ fixPos (e := e) X ↔ S.domHom g ∈ fixSet T := by
  constructor
  · intro hg w hw
    apply Subtype.ext
    have hi : e w.val ∈ X := (hX _).2 ⟨by simp, by simpa using hw⟩
    have := hg _ hi
    rw [toFin_apply_e] at this
    rw [State.domHom_apply]
    exact e.injective this
  · intro hg i hi
    obtain ⟨h, hT⟩ := (hX i).1 hi
    have := congrArg Subtype.val (hg _ hT)
    rw [State.domHom_apply] at this
    have h2 : i = e (e.symm i) := by simp
    rw [h2, toFin_apply_e, this]

/-- **Fixing the positions of a row** is fixing the row of the domain. -/
theorem mem_fixPos_rowList_iff (j : Fin L.q) (g : S.G) :
    g.val ∈ fixPos (e := e) (rowList e E j) ↔ S.domHom g ∈ fixSet (rowSet E j) := by
  refine fixPos_iff_dom e g _ fun i => ?_
  simp only [rowList, List.mem_map, List.mem_finRange, true_and, rowSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨β, rfl⟩
    refine ⟨by simp, ?_⟩
    have : (⟨e.symm (e (E (β, j))), by simp⟩ : S.dom) = E (β, j) := by simp
    rw [this, E.symm_apply_apply]
  · rintro ⟨h, hj⟩
    refine ⟨(E.symm ⟨e.symm i, h⟩).1, ?_⟩
    have : ((E.symm ⟨e.symm i, h⟩).1, j) = E.symm ⟨e.symm i, h⟩ := Prod.ext rfl hj.symm
    rw [this, E.apply_symm_apply]
    simp

/-- **Fixing the positions outside row `0`** (in the domain) is fixing the complement of row `0`
in the domain. -/
theorem mem_fixPos_off0_iff (i0 : Fin L.q) {X : List (Fin n)}
    (hX : ∀ i, i ∈ X ↔ ∃ h : e.symm i ∈ S.dom, (E.symm ⟨e.symm i, h⟩).2 ≠ i0) (g : S.G) :
    g.val ∈ fixPos (e := e) X ↔ S.domHom g ∈ fixSet (rowSet E i0)ᶜ :=
  fixPos_iff_dom e g _ fun i => (hX i).trans Iff.rfl

/-! ### The row-`0` part, as the program computes it -/

/-- Entry `i` of a permutation of `Fin n`, as a number (`0` out of range). -/
def permNat (a : Perm (Fin n)) (i : ℕ) : ℕ := if h : i < n then a ⟨i, h⟩ else 0

/-- **The row-`0` part as numbers**: for each `β < |zs|`, the index of `a (zs[β])` in `zs`. -/
def partNat (zs : List ℕ) (a : Perm (Fin n)) : List ℕ :=
  (List.range zs.length).map fun β => zs.findIdx fun x => decide (x = permNat a (zs.getD β 0))

theorem rowList_length (j : Fin L.q) : (rowList e E j).length = m := by simp [rowList]

theorem findIdx_rowList (j : Fin L.q) (γ : Fin m) :
    ((rowList e E j).map Fin.val).findIdx (fun x => decide (x = (e (E (γ, j)) : ℕ))) = γ := by
  have hnd : ((rowList e E j).map Fin.val).Nodup := by
    rw [List.nodup_map_iff Fin.val_injective]
    refine (List.nodup_finRange m).map ?_
    intro a b h
    have := E.injective (Subtype.ext (e.injective h))
    exact congrArg Prod.fst this
  have hlt : (γ : ℕ) < ((rowList e E j).map Fin.val).length := by simp [rowList]
  have hget : ((rowList e E j).map Fin.val)[(γ : ℕ)] = (e (E (γ, j)) : ℕ) := by simp [rowList]
  rw [← hget]
  refine (List.findIdx_eq hlt).2 ⟨by simp, fun k hk => ?_⟩
  have hne : ((rowList e E j).map Fin.val)[k] ≠ ((rowList e E j).map Fin.val)[(γ : ℕ)] := by
    intro h
    have := (hnd.getElem_inj_iff (hi := by omega) (hj := hlt)).1 h
    omega
  simpa using hne

/-- **The program's row-`0` part is `rowPart`.** -/
theorem partNat_eq (i0 : Fin L.q) (g : S.G) (hg : S.domHom g ∈ rowPres E) :
    partNat ((rowList e E i0).map Fin.val) (toFin e g.val) =
      (List.finRange m).map fun β => ((rowPart E i0 ⟨_, hg⟩ β : Fin m) : ℕ) := by
  unfold partNat
  rw [List.length_map, rowList_length]
  apply List.ext_getElem (by simp)
  intro β h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  have hβ : β < m := by simpa using h1
  have hz : ((rowList e E i0).map Fin.val).getD β 0 = (e (E (⟨β, hβ⟩, i0)) : ℕ) := by
    simp [rowList, List.getD_eq_getElem?_getD, hβ]
  rw [hz]
  have hp : permNat (toFin e g.val) (e (E (⟨β, hβ⟩, i0)) : ℕ) =
      (e (E (rowPart E i0 ⟨_, hg⟩ ⟨β, hβ⟩, i0)) : ℕ) := by
    unfold permNat
    rw [dif_pos (e _).2]
    simp only [Fin.eta]
    rw [toFin_apply_e]
    congr 2
    have := rowPres_apply E hg ⟨β, hβ⟩ i0
    exact congrArg Subtype.val this
  rw [hp, findIdx_rowList]
  rfl

/-! ### Generators of the row-`0` image -/

variable {e}

theorem gpair_injective : Function.Injective (gpair e L) := by
  intro x y h
  have := congrArg Prod.fst h
  exact Subtype.ext ((toFin e).injective this)

/-- **Graph-form generators give generators of the row-`0` image.** If the pairs `qs` generate
the graph of `A`, and an element of `G` lies in `A` exactly when its restriction lies in
`Y ≤ rowPres E`, then the row-`0` parts of the first parts of `qs` (as the program computes
them) are the encodings of a list `σs` that generates the row-`0` image of `G|_dom ⊓ Y`. -/
theorem closure_parts (i0 : Fin L.q) {A : Subgroup (Perm Ω)}
    {qs : List (Perm (Fin n) × Perm (Fin L.q))} (hqs : PairGens e L A qs)
    (Y : Subgroup (Perm S.dom)) (hY : Y ≤ rowPres E)
    (hAY : ∀ g : S.G, g.val ∈ A ↔ S.domHom g ∈ Y) :
    ∃ σs : List (Perm (Fin m)),
      qs.map (fun p => natList (partNat ((rowList e E i0).map Fin.val) p.1)) = σs.map encPerm ∧
      σs.length = qs.length ∧
      Subgroup.closure {σ | σ ∈ σs} =
        ((S.domGroup ⊓ Y).subgroupOf (rowPres E)).map (rowPart E i0) := by
  classical
  -- every pair comes from an element of `G ∩ A`
  have hmem : ∀ p ∈ qs, ∃ x : S.G, x.val ∈ A ∧ gpair e L x = p := by
    intro p hp
    have : p ∈ graphOf e L A := hqs ▸ Subgroup.subset_closure hp
    obtain ⟨g, hg, hA, h1, h2⟩ := (mem_graphOf e L).1 this
    exact ⟨⟨g, hg⟩, hA, Prod.ext h1 h2⟩
  let xOf : {p // p ∈ qs} → S.G := fun p => (hmem p.1 p.2).choose
  have hxA : ∀ p, (xOf p).val ∈ A := fun p => (hmem p.1 p.2).choose_spec.1
  have hxp : ∀ p, gpair e L (xOf p) = p.1 := fun p => (hmem p.1 p.2).choose_spec.2
  have hxY : ∀ p, S.domHom (xOf p) ∈ rowPres E := fun p => hY ((hAY _).1 (hxA p))
  let σOf : {p // p ∈ qs} → Perm (Fin m) := fun p => rowPart E i0 ⟨_, hxY p⟩
  refine ⟨qs.attach.map σOf, ?_, by simp, ?_⟩
  · -- the encodings
    conv_lhs => rw [← List.attach_map_subtype_val qs]
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    have h1 : p.1.1 = toFin e (xOf p).val := by rw [← hxp p]; rfl
    rw [h1, partNat_eq e E i0 _ (hxY p)]
    show Val.list _ = Val.list _
    rw [List.map_map]
    rfl
  · -- the generated group: the subgroup `A ⊓ G` is generated by the elements `xOf p`
    set T : Set S.G := {x | gpair e L x ∈ qs} with hT
    have hK : Subgroup.closure T = A.subgroupOf S.G := by
      apply Subgroup.map_injective (gpair_injective (L := L) (e := e))
      rw [MonoidHom.map_closure]
      show _ = graphOf e L A
      rw [← hqs]
      congr 1
      ext p
      simp only [Set.mem_image, Set.mem_setOf_eq, hT]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hp
        obtain ⟨x, -, hx⟩ := hmem p hp
        exact ⟨x, hx ▸ hp, hx⟩
    -- the row-`0` part on `A ∩ G`
    have hrow : ∀ x : A.subgroupOf S.G, S.domHom x.val ∈ rowPres E := fun x =>
      hY ((hAY _).1 (Subgroup.mem_subgroupOf.1 x.2))
    let χ : A.subgroupOf S.G →* Perm (Fin m) :=
      (rowPart E i0).comp (MonoidHom.codRestrict (S.domHom.comp (A.subgroupOf S.G).subtype)
        (rowPres E) hrow)
    have hrange : χ.range = ((S.domGroup ⊓ Y).subgroupOf (rowPres E)).map (rowPart E i0) := by
      ext σ
      simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨⟨_, hrow x⟩, ⟨⟨x.val, rfl⟩, (hAY _).1 (Subgroup.mem_subgroupOf.1 x.2)⟩, rfl⟩
      · rintro ⟨y, ⟨⟨g, hg⟩, hyY⟩, rfl⟩
        have hgA : g.val ∈ A := (hAY g).2 (by rw [hg]; exact hyY)
        refine ⟨⟨g, Subgroup.mem_subgroupOf.2 hgA⟩, ?_⟩
        show rowPart E i0 _ = _
        congr 1
        exact Subtype.ext hg
    rw [← hrange]
    -- `A ∩ G` is generated by the preimage of `T`
    have htop : Subgroup.closure (((A.subgroupOf S.G).subtype) ⁻¹' T) = ⊤ := by
      have h := Subgroup.closure_closure_coe_preimage (k := T)
      rw [hK] at h
      exact h
    rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
    congr 1
    ext σ
    simp only [List.mem_map, List.mem_attach, true_and, Set.mem_setOf_eq, Set.mem_image,
      Set.mem_preimage, Subgroup.coe_subtype]
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨⟨xOf p, Subgroup.mem_subgroupOf.2 (hxA p)⟩, by
        show gpair e L (xOf p) ∈ qs; rw [hxp p]; exact p.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨_, hx⟩, ?_⟩
      have : xOf ⟨_, hx⟩ = x.val := gpair_injective (hxp ⟨_, hx⟩)
      show rowPart E i0 _ = rowPart E i0 _
      congr 1
      apply Subtype.ext
      show S.domHom (xOf _) = S.domHom x.val
      rw [this]

/-! ### The three groups of Theorem A.18 -/

section Groups

variable (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) (hP : PureCoords S L label E) (b₀ : Fin m)

/-- The label kernel of `G`. -/
abbrev kerG (S : State Ω C) (L : GiantLabels S) : Subgroup (Perm Ω) :=
  S.G ⊓ labPre (L := L) (gens ([] : List (Perm (Fin L.q))))

theorem mem_kerG_iff (g : S.G) : g.val ∈ kerG S L ↔ L.π g = 1 := by
  have hg : gens ([] : List (Perm (Fin L.q))) = ⊥ := by simp [gens]
  constructor
  · rintro ⟨-, hg', hπ⟩
    rw [hg, Subgroup.mem_bot] at hπ
    exact Subtype.ext hπ
  · intro h
    refine ⟨g.2, g.2, ?_⟩
    rw [hg, Subgroup.mem_bot]
    have : (⟨g.val, g.2⟩ : S.G) = g := rfl
    rw [this, h]; rfl

/-- **Generators of `H`** from graph-form generators of the label kernel. -/
theorem Hb_gens {ks : List (Perm (Fin n) × Perm (Fin L.q))} (hks : PairGens e L (kerG S L) ks) :
    ∃ σs : List (Perm (Fin m)),
      ks.map (fun p => natList (partNat ((rowList e E ⟨0, by omega⟩).map Fin.val) p.1)) =
        σs.map encPerm ∧ σs.length = ks.length ∧
      Subgroup.closure {σ | σ ∈ σs} = (RowForm.ofPure hnat hq E hP b₀).Hb := by
  obtain ⟨σs, h1, h2, h3⟩ := closure_parts E ⟨0, by omega⟩ hks (rowPres E) le_rfl
    fun g => (mem_kerG_iff g).trans (mem_rowPres_iff E hnat hP.label_e g).symm
  refine ⟨σs, h1, h2, h3.trans ?_⟩
  rw [Hb_eq_rowPart hnat hq E hP b₀]

/-- **Generators of `N`** from graph-form generators of the part of the label kernel that fixes
row `1`. -/
theorem Nb_gens {ns : List (Perm (Fin n) × Perm (Fin L.q))}
    (hns : PairGens e L (kerG S L ⊓ fixPos (e := e) (rowList e E ⟨1, by omega⟩)) ns) :
    ∃ σs : List (Perm (Fin m)),
      ns.map (fun p => natList (partNat ((rowList e E ⟨0, by omega⟩).map Fin.val) p.1)) =
        σs.map encPerm ∧ σs.length = ns.length ∧
      Subgroup.closure {σ | σ ∈ σs} = (RowForm.ofPure hnat hq E hP b₀).Nb := by
  obtain ⟨σs, h1, h2, h3⟩ := closure_parts E ⟨0, by omega⟩ hns
    (rowPres E ⊓ fixSet (rowSet E ⟨1, by omega⟩)) inf_le_left
    fun g => by
      show g.val ∈ kerG S L ∧ _ ↔ _ ∧ _
      exact and_congr ((mem_kerG_iff g).trans (mem_rowPres_iff E hnat hP.label_e g).symm)
        (mem_fixPos_rowList_iff e E _ g)
  refine ⟨σs, h1, h2, h3.trans ?_⟩
  rw [Nb_eq_rowPart hnat hq E hP b₀, inf_assoc]

/-- **Generators of `N*`** from graph-form generators of the part of `G` that fixes every point of
the domain outside row `0`. -/
theorem Nstar_gens {X : List (Fin n)}
    (hX : ∀ i, i ∈ X ↔ ∃ h : e.symm i ∈ S.dom, (E.symm ⟨e.symm i, h⟩).2 ≠ ⟨0, by omega⟩)
    {ss : List (Perm (Fin n) × Perm (Fin L.q))} (hss : PairGens e L (S.G ⊓ fixPos (e := e) X) ss) :
    ∃ σs : List (Perm (Fin m)),
      ss.map (fun p => natList (partNat ((rowList e E ⟨0, by omega⟩).map Fin.val) p.1)) =
        σs.map encPerm ∧ σs.length = ss.length ∧
      Subgroup.closure {σ | σ ∈ σs} = (RowForm.ofPure hnat hq E hP b₀).Nstar.map
        (RowForm.ofPure hnat hq E hP b₀).Hb.subtype := by
  obtain ⟨σs, h1, h2, h3⟩ := closure_parts E ⟨0, by omega⟩ hss
    (fixSet (rowSet E ⟨0, by omega⟩)ᶜ) (fixSet_compl_le E _)
    fun g => by
      rw [Subgroup.mem_inf, mem_fixPos_off0_iff e E _ hX]
      exact and_iff_right g.2
  refine ⟨σs, h1, h2, h3.trans ?_⟩
  rw [Nstar_eq_rowPart hnat hq E hP b₀]

/-- **Transitivity of `N`** is transitivity of the group generated by its generators. -/
theorem transitive_iff {σs : List (Perm (Fin m))}
    (hσ : Subgroup.closure {σ | σ ∈ σs} = (RowForm.ofPure hnat hq E hP b₀).Nb) :
    MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP b₀).Nl
        (RowForm.ofPure hnat hq E hP b₀).B ↔
      ∀ x y : Fin m, y ∈ genOrbit σs x := by
  set F := RowForm.ofPure hnat hq E hP b₀
  have key : ∀ x y : F.B, (∃ g : F.Nl, g • x = y) ↔ y ∈ genOrbit σs x := by
    intro x y
    refine Iff.trans ?_ (mem_genOrbit (gs := σs) (x := x) (y := y)).symm
    show (∃ g : F.Nl, g.val.val x = y) ↔ ∃ g ∈ Subgroup.closure {σ | σ ∈ σs}, g x = y
    rw [hσ]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.val.val, ⟨g.val, g.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  constructor
  · intro h x y
    exact (key x y).1 (h.exists_smul_eq x y)
  · intro h
    exact ⟨fun x y => (key x y).2 (h x y)⟩

end Groups

end GI.Impl
