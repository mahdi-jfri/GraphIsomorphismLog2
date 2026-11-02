import Workspace.Impl.TermLiftMath

/-!
# The split of the table transport over the radical cosets (mathematics)

Corollary A.22: "enumerate the radical cosets, solve each by Theorem A.20". `R` is the full
preimage in `H` of the solvable radical of `H/N` (`radicalPreimage`). For right coset
representatives `r` of `R` in `H`, the piece of the table transport over `R r` is
`tmCosetT I r`: the pairs `(d, π)` of the exact table transport with `d_{i0} ∈ R r`. Since
`d_{i0} = h μ_{i0}` with `h` the residual element and `μ_{i0} ∈ N ≤ R`, this is the part of the
procedure of A.23 above the residual elements in `R r`.

* `tm_exactT_eq_iUnion`: the table transport is the union of its pieces over any covering list of
  representatives.
* `tm_domSet_cosetOrEmpty`: its lift to the domain is empty or a left coset (it is the answer of
  the restricted instance), so the pieces can be combined into one coset (`ce_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Paper Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- The radical preimage `R ≤ H` of Corollary A.22. -/
noncomputable def tmRad : Subgroup (Perm I.B) := radicalPreimage I.Hb I.Nb

/-- **The piece of the table transport over the radical coset `R r`.** -/
def tmCosetT (r : Perm I.B) : Set ((Fin L.q → Perm I.B) × Perm (Fin L.q)) :=
  {p | p ∈ tmExactT I ∧ ∃ x ∈ tmRad I, p.1 I.i0 = x * r}

/-- The coordinate at `i0` of a pair of the table transport lies in `H`. -/
theorem tm_exactT_fst_mem {p : (Fin L.q → Perm I.B) × Perm (Fin L.q)} (hp : p ∈ tmExactT I) :
    p.1 I.i0 ∈ I.Hb := by
  obtain ⟨h, hh, μ, hJ, h1, -⟩ := hp
  have hX : I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inl =
      types I.Nb (rowTuple I.e S.x) := I.typesOf_exact _
  have hY : I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inr =
      types I.Nb (rowTuple I.e S.y) := I.typesOf_exact _
  have hhH : h ∈ I.Hb := by
    rw [hX, hY, radicalTransport_set I.Nb_le I.normalizes (fixes_types _ _) (fixes_types _ _)] at hh
    exact hh.1
  rw [h1, Pi.mul_apply, (rowLift_spec I.e I.i0 hhH).2]
  exact I.Hb.mul_mem hhH (I.Nb_le (hJ.1 I.i0))

/-- **The table transport is the union of its pieces** over a list of representatives whose
right cosets `R r` cover `H`. -/
theorem tm_exactT_eq_iUnion {reps : List (Perm I.B)}
    (hcov : ∀ h ∈ I.Hb, ∃ r ∈ reps, ∃ x ∈ tmRad I, h = x * r) :
    tmExactT I = ⋃ r ∈ reps, tmCosetT I r := by
  ext p
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hp
    obtain ⟨r, hr, x, hx, hxr⟩ := hcov _ (tm_exactT_fst_mem I hp)
    exact ⟨r, hr, hp, x, hx, hxr⟩
  · rintro ⟨r, -, hp, -⟩
    exact hp

end RT

theorem tmDomSet_iUnion {S : State Ω C} {B : Type} {q : ℕ} (e : B × Fin q ≃ S.dom) {ι : Type}
    (l : List ι) (X : ι → Set ((Fin q → Perm B) × Perm (Fin q))) :
    tmDomSet e (⋃ r ∈ l, X r) = ⋃ r ∈ l, tmDomSet e (X r) := by
  ext σ
  simp only [tmDomSet, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨p, ⟨r, hr, hp⟩, h⟩; exact ⟨r, hr, p, hp, h⟩
  · rintro ⟨r, hr, p, hp, h⟩; exact ⟨p, ⟨r, hr, hp⟩, h⟩

/-- The lift of sets inside the image of the restriction is injective. -/
theorem tm_liftAnswer_inj (S : State Ω C) {X Y : Set (Perm S.dom)}
    (hX : X ⊆ (restrictHom S.G S.dom S.dom_inv).range)
    (hY : Y ⊆ (restrictHom S.G S.dom S.dom_inv).range)
    (h : S.liftAnswer X = S.liftAnswer Y) : X = Y := by
  have key : ∀ {X Y : Set (Perm S.dom)}, X ⊆ (restrictHom S.G S.dom S.dom_inv).range →
      S.liftAnswer X ⊆ S.liftAnswer Y → X ⊆ Y := by
    intro X Y hX h σ hσ
    obtain ⟨g, rfl⟩ := hX hσ
    have hg : (g : Perm Ω) ∈ S.liftAnswer X := ⟨g.2, hσ⟩
    obtain ⟨hg', hY⟩ := h hg
    exact hY
  exact (key hX h.le).antisymm (key hY h.ge)

/-- **The lift of the exact table transport is empty or a left coset**, on the domain positions:
it is the answer of the restricted instance (`answer_restrict_image`). -/
theorem tm_domSet_cosetOrEmpty {k : ℕ} (e : Ω ≃ Fin k) {P : Params} {S : State Ω C}
    {L : GiantLabels S} (I : RowTerminal P S L) :
    toFin (domEquiv e S.dom) '' tmDomSet I.e (tmExactT I) = ∅ ∨
      ∃ (c : Perm (Fin (domFin e S.dom).length)) (H : Subgroup (Perm (Fin (domFin e S.dom).length))),
        toFin (domEquiv e S.dom) '' tmDomSet I.e (tmExactT I) = c • (H : Set _) := by
  set ρ := restrictHom S.G S.dom S.dom_inv
  set A'' := answer ρ.range Set.univ (S.x ∘ Subtype.val) (S.y ∘ Subtype.val)
  have hA'' : A'' ⊆ ρ.range := fun σ hσ => hσ.1
  have hlift : S.liftAnswer A'' = S.answer := by
    unfold State.liftAnswer State.answer
    rw [answer_restrict_image S.G S.dom S.dom_inv S.x S.y]
    rfl
  have hD : tmDomSet I.e (tmExactT I) = A'' :=
    tm_liftAnswer_inj S (tm_domSet_le I) hA'' ((tm_liftAnswer_eq I).trans hlift.symm)
  rw [hD]
  rcases Set.eq_empty_or_nonempty A'' with h | ⟨t, ht⟩
  · left; rw [h, Set.image_empty]
  · right
    have hinv : Invariant ρ.range Set.univ := fun _ _ _ => by simp
    have hc : A'' = t • (autGroup ρ.range Set.univ hinv (S.x ∘ Subtype.val) : Set _) :=
      answer_eq_smul_aut hinv ht
    rw [hc, Set.image_smul_distrib]
    refine ⟨toFin (domEquiv e S.dom) t,
      (autGroup ρ.range Set.univ hinv (S.x ∘ Subtype.val)).map
        (toFin (domEquiv e S.dom)).toMonoidHom, ?_⟩
    rw [Subgroup.coe_map]
    rfl

end GI.Impl
