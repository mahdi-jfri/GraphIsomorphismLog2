import Workspace.Impl.TermGlueLabPSup
import Workspace.Impl.TermGlueLabRT

/-!
# The preconditions of the supplement call (step 4 of the label program)

Proof of Theorem A.23: "Compute a solvable supplement `S` with `S N = D ∩ R` by
Lemma A.19". Lemma A.19 needs `N ≤ D ∩ R`, `N` normal in `D ∩ R`, and `(D ∩ R)/N` solvable.

The program does not see `D ∩ R` directly. It sees the residual answer `[τ, U]` with
`Res = τ ⟨U⟩`, and it passes `R' = τ ⟨U⟩ τ⁻¹` to T4 (`tmGLPSup_spec`). Here we show
`R' = D ∩ R` (`tmGLS_res_conj`, from `tmGL_res_iff`), and then the three preconditions
(`tmGLS_t4_pre`):

* `N ≤ D`, since `N ≤ H` and `N` fixes every type; `N ≤ R` by the definition of the radical
  preimage;
* `N` is normal in `D ∩ R`, since `N` is normal in `H` and `D ∩ R ≤ H`;
* `(D ∩ R)/N` is solvable, since `D ∩ R ≤ R` and `R/N` is solvable (the derived series of
  `R` relative to `N` reaches `N`, and so does the one of `D ∩ R`, by `relDerived_mono`).

`tmGLS_t4_gens` states the same for the generator lists that the program uses, in the form
`tmGLPSup_spec` takes.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset Equiv
open GI.Cited (gens)
open scoped Pointwise

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

/-- **The conjugated residual group is `D ∩ R`.** If the residual set is `τ U`, then
`τ U τ⁻¹ = D ∩ R`. -/
theorem tmGLS_res_conj {r τ : Perm I.B} {Ub : Subgroup (Perm I.B)}
    (hres : tmGlRes I r = τ • (Ub : Set (Perm I.B))) :
    Ub.map (MulAut.conj τ).toMonoidHom =
      Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I := by
  have hτ : τ ∈ tmGlRes I r := by
    rw [hres]; exact ⟨1, Ub.one_mem, mul_one τ⟩
  ext g
  -- `g ∈ D ∩ R` exactly when `g τ` is residual (`tmGL_res_iff` at `h = g τ`)
  have h1 := tmGL_res_iff hτ (g * τ)
  rw [mul_inv_cancel_right] at h1
  rw [← h1, hres]
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Set.mem_smul_set,
    SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by group⟩
  · rintro ⟨y, hy, he⟩
    refine ⟨y, hy, ?_⟩
    calc τ * y * τ⁻¹ = g * τ * τ⁻¹ := by rw [he]
      _ = g := by group

/-- **The preconditions of Lemma A.19 for `D ∩ R`.** -/
theorem tmGLS_t4_pre :
    I.Nb ≤ Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I ∧
    (I.Nb.subgroupOf (Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I)).Normal ∧
    ∃ _ : (I.Nb.subgroupOf (Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I)).Normal,
      IsSolvable ((Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I : Subgroup (Perm I.B)) ⧸
        I.Nb.subgroupOf (Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I)) := by
  obtain ⟨hRH, hNR, ℓ, hℓ⟩ := radicalPreimage_spec I.Nb_le I.normalizes
  set D' := Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I
  -- `N ≤ D`: `N ≤ H`, and `N` fixes the types
  have hND : I.Nb ≤ D' := fun n hn =>
    ⟨⟨I.Nb_le hn, (fixes_types I.Nb (rowTuple I.e S.x)).act_eq hn⟩, hNR hn⟩
  -- `N` is normal in `D'`, since `D' ≤ H` and `N` is normal in `H`
  have hD'H : D' ≤ I.Hb := fun g hg => hRH hg.2
  have hnorm : (I.Nb.subgroupOf D').Normal := normal_of_normalizes (I.normalizes.mono hD'H)
  refine ⟨hND, hnorm, hnorm, ?_⟩
  -- the series of `D'` relative to `N` lies in that of `R`, which reaches `N`
  have hmono := relDerived_mono hNR (inf_le_right : D' ≤ tmRad I)
    (le_relDerived hNR ℓ) ℓ le_rfl
  exact isSolvable_quot_of_relDerived (hmono.trans hℓ)

end RT

/-- Moving the preconditions of Lemma A.19 along equalities of the two groups. -/
theorem tmGLS_t4_transfer {G : Type*} [Group G] {N R N' R' : Subgroup G} (hN : N = N')
    (hR : R = R') (h : N' ≤ R' ∧ ∃ _ : (N'.subgroupOf R').Normal, IsSolvable (R' ⧸ N'.subgroupOf R')) :
    N ≤ R ∧ ∃ _ : (N.subgroupOf R).Normal, IsSolvable (R ⧸ N.subgroupOf R) := by
  subst hN; subst hR; exact h

section Pure

open GI.Cited (encPerm encGroup)

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- **The preconditions of the supplement call, for the program's lists** (in the form of
`tmGLPSup_spec`). Let `I` be the row terminal of the label step, with `B = Fin m`, `gens σN = N`
and the residual answer `[τ, U]`. Then `R' = τ ⟨U⟩ τ⁻¹` is `D ∩ R`, and `N ≤ R'`, `N` is normal in
`R'`, and `R'/N` is solvable. -/
theorem tmGLS_t4_gens (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ P.α < L.q) {σN U : List (Perm (Fin m))}
    (hσN : gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb) {r τ : Perm (Fin m)}
    (hw : AnsC (Equiv.refl (Fin m)) (.list [encPerm τ, encGroup U])
      (tmGlRes ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN hqα) r)) :
    gens (U.map fun x => τ * x * τ⁻¹) =
      Aut ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN hqα).Hb
        (types ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN hqα).Nb
          (rowTuple ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN hqα).e
            S.x)) ⊓ tmRad ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN hqα) ∧
    gens σN ≤ gens (U.map fun x => τ * x * τ⁻¹) ∧
    ∃ _ : ((gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹))).Normal,
      IsSolvable ((gens (U.map fun x => τ * x * τ⁻¹)) ⧸
        (gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹))) := by
  set I := (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN hqα
  -- the residual set is `τ ⟨U⟩`
  have hres : tmGlRes I r = τ • ((gens U : Subgroup (Perm (Fin m))) : Set (Perm (Fin m))) :=
    tmCs_ansC_cons hw rfl
  have hR : gens (U.map fun x => τ * x * τ⁻¹) =
      Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I := by
    rw [sup_gens_conj]; exact tmGLS_res_conj I hres
  obtain ⟨h1, -, h3⟩ := tmGLS_t4_pre I
  exact ⟨hR, tmGLS_t4_transfer hσN hR ⟨h1, h3⟩⟩

end Pure

end GI.Impl
