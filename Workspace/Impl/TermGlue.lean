import Workspace.Impl.TermSplit
import Workspace.MulticosetSolvable

/-!
# The affine glue of Theorem A.20 and the labels of Theorem A.23 (T6, as a hypothesis)

The paper's paragraph "Solving the affine compatibility condition" (proof of Theorem A.20) is a
finite abelian affine transporter procedure. It is used twice:

* at every level of the recursion of Theorem A.20, to turn the profile transporter `B τ` into the
  full transporter `Iso_H(X, Y)` (stage 1: `MulticosetSolvable.glue`, `glue_eq`);
* in Theorem A.23, inside one radical coset, to impose the total label in `A/B(x)` and the sign
  ("The finite abelian affine transporter procedure in the proof of Theorem A.20 now imposes both
  labels in polynomial time within this radical coset").

`Iface.TermGlueSpec Pg K D gObj gLab` states both as polynomial-time functions of a `GI.Lang`
program. The rest of the terminal case uses T6 only through it.

**The object model.** An object of Theorem A.20 is a coset object `L h` with an orbit color
(`GI.Multicoset.CObj`). A program lists it as `[c, gens L, h]` (`tmGlObjVal`); its meaning is
`tmGlObj c σL h = ⟨c, ⟨σL⟩ h⟩`. Colors are numbers. The profiles of the recursion are coset
objects of the same kind: the profile of a piece `S` is the coset `A · Iso_H(r, S)` of the group
`A · Aut_H(r)`, with the color of its class representative `r`, so one encoding serves every
level.

**The glue, set-level** (`TermGlueObjSpec`). Input `[gens H, gens N, gens A, X, Y, gens B, τ]`.
The preconditions are those of the paper's step: `N ≤ A ≤ H`, both normal in `H`, `A/N` abelian,
the cover `H` solvable ("Henceforth all covering groups are solvable subgroups of `Sym(B)`"), `N`
fixes every listed object, and `B τ` is a profile transporter: `A ≤ B ≤ H`, `τ ∈ H`, and the five
properties of `glue_eq` (P1–P5 below). The output is a canonical answer for `Iso_H(X, Y)`.
`tmGl_glue_eq` checks that this is exactly the stage-1 `glue A X Y (B τ)`.

**The labels** (`TermGlueLabSpec`). Input `[V, r, w]`: the terminal input `V` of
`TermCosetSpec`, a representative `r ∈ H`, and a canonical answer `w` for the residual set
`tmGlRes I r` (the elements `h ∈ R r` carrying the type multiset of `x` to that of `y`, the answer
of Corollary A.22 in this radical coset). The output is a canonical answer for `tmGlLab I r`, the
residual elements that also pass the label test (total and sign): some `J`-element `μ` corrects
the lifts `k_i(h)` into the stored cosets `Iso_H(x_i, y_{π i})`. This is the paper's "label
stabilizer and transporter" in `D`; adjoining `N` is already done, since the set is a union of
`N`-cosets.

Both costs are `K (w + 1)^D` in the input weight `w`: "the entire affine calculation is
polynomial in `b + M`".
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

/-! ### Encoded coset objects -/

/-- The coset object `⟨σL⟩ h` of color `c`. -/
def tmGlObj {n : ℕ} (c : ℕ) (σL : List (Perm (Fin n))) (h : Perm (Fin n)) :
    CObj ℕ (Perm (Fin n)) :=
  ⟨c, (fun l => l * h) '' (gens σL : Set (Perm (Fin n)))⟩

/-- The value of one listed object: `[c, gens L, h]`. -/
def tmGlObjVal {n : ℕ} (o : ℕ × List (Perm (Fin n)) × Perm (Fin n)) : Val :=
  .list [.nat o.1, encGroup o.2.1, encPerm o.2.2]

/-- The value of a list of objects. -/
def tmGlObjsVal {n : ℕ} (X : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))) : Val :=
  .list (X.map tmGlObjVal)

/-- The multiset of objects that a list describes. -/
def tmGlMs {n : ℕ} (X : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))) :
    Multiset (CObj ℕ (Perm (Fin n))) :=
  ((X.map fun o => tmGlObj o.1 o.2.1 o.2.2 : List (CObj ℕ (Perm (Fin n)))) :
    Multiset (CObj ℕ (Perm (Fin n))))

/-- The input of the glue: `[gens H, gens N, gens A, X, Y, gens B, τ]`. -/
def tmGlIn {n : ℕ} (σH σN σA : List (Perm (Fin n)))
    (X Y : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))) (σB : List (Perm (Fin n)))
    (τ : Perm (Fin n)) : Val :=
  .list [encGroup σH, encGroup σN, encGroup σA, tmGlObjsVal X, tmGlObjsVal Y, encGroup σB,
    encPerm τ]

/-! ### The glue is `glue` of stage 1 -/

section Bridge

variable {G : Type} [Group G] {Ω : Type} [RAct G Ω]

/-- The coset `B τ` as a set. -/
def tmGlCoset (B : Subgroup G) (τ : G) : Set G := (fun b => b * τ) '' (B : Set G)

/-- The profile transporter `B τ` is the transporter `Iso_H(U, U^τ)` of the object `U = B`
(one color), when `B ≤ H` and `τ ∈ H`. -/
private theorem iso_unitObj {H B : Subgroup G} (hBH : B ≤ H) {τ : G} (hτ : τ ∈ H) :
    Iso H (⟨(), (B : Set G)⟩ : CObj Unit G) (⟨(), (B : Set G)⟩ ↼ τ) = tmGlCoset B τ := by
  ext h
  simp only [mem_iso, tmGlCoset, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hh, he⟩
    have hc := congrArg CObj.coset he
    simp only [cobj_act_coset] at hc
    have : h ∈ (fun x => x * τ) '' (B : Set G) := by
      rw [← hc]; exact ⟨1, B.one_mem, by simp⟩
    exact this
  · rintro ⟨b, hb, rfl⟩
    refine ⟨H.mul_mem (hBH hb) hτ, CObj.ext rfl ?_⟩
    simp only [cobj_act_coset]
    ext z
    simp only [Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x * b, B.mul_mem hx hb, by group⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x * b⁻¹, B.mul_mem hx (B.inv_mem hb), by group⟩

private theorem aut_unitObj {H B : Subgroup G} (hBH : B ≤ H) {g : G} :
    g ∈ Aut H (⟨(), (B : Set G)⟩ : CObj Unit G) ↔ g ∈ B := by
  have h1 := iso_unitObj hBH H.one_mem (τ := 1)
  rw [act_one] at h1
  have : g ∈ Iso H (⟨(), (B : Set G)⟩ : CObj Unit G) ⟨(), (B : Set G)⟩ ↔ g ∈ tmGlCoset B 1 := by
    rw [h1]
  rw [iso_self] at this
  rw [SetLike.mem_coe] at this
  rw [this]
  simp [tmGlCoset]

/-- **The set-level glue of the hypothesis is the stage-1 `glue`.** Under the preconditions of
`TermGlueObjSpec` (P1–P5 for `B τ`), `glue A X Y (B τ) = Iso_H(X, Y)`. -/
theorem tmGl_glue_eq {H A B : Subgroup G} (hAH : A ≤ H) (hAn : Normalizes H A) (hBH : B ≤ H)
    {τ : G} (hτ : τ ∈ H) {X Y : Multiset Ω}
    (hP1 : ∀ g ∈ B, Conf A X (X ↼ g)) (hP2 : ∀ g ∈ B, Conf A Y (X ↼ (g * τ)))
    (hP3 : ∀ g ∈ B, Conf A Y (Y ↼ (τ⁻¹ * g * τ)))
    (hP4 : ∀ h ∈ Iso H X Y, h * τ⁻¹ ∈ B) (hP5 : Aut H X ≤ B) :
    glue A X Y (tmGlCoset B τ) = Iso H X Y := by
  set U : CObj Unit G := ⟨(), (B : Set G)⟩
  rw [← iso_unitObj hBH hτ]
  refine glue_eq hAH hAn ?_ ?_ ?_ ?_ ?_
  · intro g hg; exact hP1 g ((aut_unitObj hBH).1 hg)
  · intro t ht
    rw [iso_unitObj hBH hτ] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    exact hP2 b hb
  · intro g hg
    -- `U^τ g = U^τ` gives `τ g τ⁻¹ ∈ Aut_H(U) = B`
    have hg' : τ * g * τ⁻¹ ∈ Aut H U := by
      refine ⟨H.mul_mem (H.mul_mem hτ hg.1) (H.inv_mem hτ), ?_⟩
      have := hg.2
      rw [act_act] at this
      rw [← act_act, ← act_act, act_act U τ g, this, act_act, mul_inv_cancel, act_one]
    have := hP3 _ ((aut_unitObj hBH).1 hg')
    simpa [mul_assoc] using this
  · intro h hh
    rw [iso_unitObj hBH hτ]
    exact ⟨h * τ⁻¹, hP4 h hh, by group⟩
  · intro g hg; exact (aut_unitObj hBH).2 (hP5 hg)

end Bridge

/-! ### The labels of Theorem A.23 in one radical coset -/

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- **The residual elements above the radical coset `R r`**: `h ∈ R r` carrying the type
multiset of `x` to that of `y` (Corollary A.22 in this coset). -/
def tmGlRes (r : Perm I.B) : Set (Perm I.B) :=
  {h | h ∈ Iso I.Hb (types I.Nb (rowTuple I.e S.x)) (types I.Nb (rowTuple I.e S.y)) ∧
    ∃ x ∈ tmRad I, h = x * r}

/-- **The residual elements that pass the labels** (total in `A/B(x)` and sign, Theorem A.23):
some `J`-element `μ` with matching `π` corrects the lifts `k_i(h)` into the stored cosets
`Iso_H(x_i, y_{π i})`. -/
def tmGlLab (r : Perm I.B) : Set (Perm I.B) :=
  {h | h ∈ tmGlRes I r ∧ ∃ (μ : Fin L.q → Perm I.B) (π : Perm (Fin L.q)),
    InJ I.Nb I.φ μ π ∧ ∀ i, rowLift I.e I.i0 h i * μ i ∈ (I.cosetCall (i, π i)).answer}

/-- **The piece above `R r` is built from the label coset**: its pairs are `(k(h) μ, π)` with
`h ∈ tmGlLab I r` and the `J`-elements `μ` that correct the lifts. So `TermGlueLabSpec` returns
exactly the residual part of the piece `tmCosetT I r` of `TermCosetSpec`. -/
theorem tmGl_cosetT_eq (r : Perm I.B) :
    tmCosetT I r = {p | ∃ h ∈ tmGlLab I r, ∃ μ, InJ I.Nb I.φ μ p.2 ∧
      p.1 = rowLift I.e I.i0 h * μ ∧
      ∀ i, rowLift I.e I.i0 h i * μ i ∈ (I.cosetCall (i, p.2 i)).answer} := by
  have hX : I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inl =
      types I.Nb (rowTuple I.e S.x) := I.typesOf_exact _
  have hY : I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inr =
      types I.Nb (rowTuple I.e S.y) := I.typesOf_exact _
  have hset : (radicalTransport I.Hb I.Nb (I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inl)
      (I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inr)).set =
      Iso I.Hb (types I.Nb (rowTuple I.e S.x)) (types I.Nb (rowTuple I.e S.y)) := by
    rw [hX, hY, radicalTransport_set I.Nb_le I.normalizes (fixes_types _ _) (fixes_types _ _)]
  have hRH : tmRad I ≤ I.Hb := (radicalPreimage_spec I.Nb_le I.normalizes).1
  have hNR : I.Nb ≤ tmRad I := (radicalPreimage_spec I.Nb_le I.normalizes).2.1
  -- the coordinate at `i0` is `h μ_{i0}`, and `μ_{i0} ∈ N`, normal in `H`, lies in `R`
  have hi0 : ∀ {h : Perm I.B} {μ : Fin L.q → Perm I.B}, h ∈ I.Hb → μ I.i0 ∈ I.Nb →
      ((∃ x ∈ tmRad I, (rowLift I.e I.i0 h * μ) I.i0 = x * r) ↔ ∃ x ∈ tmRad I, h = x * r) := by
    intro h μ hh hμ
    rw [Pi.mul_apply, (rowLift_spec I.e I.i0 hh).2]
    constructor
    · rintro ⟨x, hx, he⟩
      have hr : r ∈ I.Hb := by
        have : r = x⁻¹ * (h * μ I.i0) := by rw [he]; group
        rw [this]
        exact I.Hb.mul_mem (I.Hb.inv_mem (hRH hx)) (I.Hb.mul_mem hh (I.Nb_le hμ))
      have hc : r * (μ I.i0)⁻¹ * r⁻¹ ∈ tmRad I := hNR (I.normalizes r hr _ (I.Nb.inv_mem hμ))
      refine ⟨x * (r * (μ I.i0)⁻¹ * r⁻¹), (tmRad I).mul_mem hx hc, ?_⟩
      have : h = x * r * (μ I.i0)⁻¹ := by rw [← he]; group
      rw [this]; group
    · rintro ⟨x, hx, rfl⟩
      have hr : r ∈ I.Hb := by
        have : r = x⁻¹ * (x * r) := by group
        rw [this]
        exact I.Hb.mul_mem (I.Hb.inv_mem (hRH hx)) hh
      have hc : r * μ I.i0 * r⁻¹ ∈ tmRad I := hNR (I.normalizes r hr _ hμ)
      exact ⟨x * (r * μ I.i0 * r⁻¹), (tmRad I).mul_mem hx hc, by group⟩
  ext ⟨d, π⟩
  simp only [tmCosetT, tmExactT, tableTransport, tmGlLab, tmGlRes, Set.mem_setOf_eq, hset]
  constructor
  · rintro ⟨⟨h, hh, μ, hJ, hd, hT⟩, hR⟩
    subst hd
    exact ⟨h, ⟨⟨hh, (hi0 hh.1 (hJ.1 I.i0)).1 hR⟩, μ, π, hJ, hT⟩, μ, hJ, rfl, hT⟩
  · rintro ⟨h, ⟨⟨hh, hR⟩, -⟩, μ, hJ, hd, hT⟩
    subst hd
    exact ⟨⟨h, hh, μ, hJ, rfl, hT⟩, (hi0 hh.1 (hJ.1 I.i0)).2 hR⟩

end RT

namespace Iface

variable (Pg : Program)

/-- **The glue of one level of Theorem A.20** ("Solving the affine compatibility condition"). On
`[gens H, gens N, gens A, X, Y, gens B, τ]`, with `N ≤ A ≤ H` normal in the solvable cover `H`,
`A/N` abelian, `N` fixing the listed objects, and `B τ` a profile transporter (`A ≤ B ≤ H`,
`τ ∈ H`, P1–P5), the function `g` returns a canonical answer for `Iso_H(X, Y)` at cost at most
`K (w + 1)^D`. -/
def TermGlueObjSpec (K D g : ℕ) : Prop :=
  ∀ {n : ℕ} (σH σN σA : List (Perm (Fin n))) (X Y : List (ℕ × List (Perm (Fin n)) × Perm (Fin n)))
    (σB : List (Perm (Fin n))) (τ : Perm (Fin n)),
    IsSolvable (gens σH) → gens σN ≤ gens σA → gens σA ≤ gens σH →
    GI.Multicoset.Normalizes (gens σH) (gens σN) → GI.Multicoset.Normalizes (gens σH) (gens σA) →
    (∀ a ∈ gens σA, ∀ b ∈ gens σA, a * b * a⁻¹ * b⁻¹ ∈ gens σN) →
    Fixes (gens σN) (tmGlMs X) → Fixes (gens σN) (tmGlMs Y) →
    gens σA ≤ gens σB → gens σB ≤ gens σH → τ ∈ gens σH →
    -- P1: the source profile stabilizer keeps the configuration of `X`
    (∀ g ∈ gens σB, Conf (gens σA) (tmGlMs X) (tmGlMs X ↼ g)) →
    -- P2: the profile transporters carry `X` to a configuration of `Y`
    (∀ g ∈ gens σB, Conf (gens σA) (tmGlMs Y) (tmGlMs X ↼ (g * τ))) →
    -- P3: the target profile stabilizer `τ⁻¹ B τ` keeps the configuration of `Y`
    (∀ g ∈ gens σB, Conf (gens σA) (tmGlMs Y) (tmGlMs Y ↼ (τ⁻¹ * g * τ))) →
    -- P4: every transporter lies in `B τ`
    (∀ h ∈ Iso (gens σH) (tmGlMs X) (tmGlMs Y), h * τ⁻¹ ∈ gens σB) →
    -- P5: every automorphism lies in `B`
    Aut (gens σH) (tmGlMs X) ≤ gens σB →
    FunAll Pg g (tmGlIn σH σN σA X Y σB τ) (fun u cost =>
      AnsC (Equiv.refl (Fin n)) u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧
      cost ≤ K * ((tmGlIn σH σN σA X Y σB τ).wt + 1) ^ D)

/-- **The labels of Theorem A.23 in one radical coset.** On `[V, encPerm r, w]`, with `V` the
input of `TermCosetSpec`, `r ∈ H`, and `w` a canonical answer for the residual set `tmGlRes T0 r`,
the function `g` returns a canonical answer for `tmGlLab T0 r` at cost at most `K (w + 1)^D`. -/
def TermGlueLabSpec (K D g : ℕ) : Prop :=
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
        (tmGlRes ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r) →
      FunAll Pg g (.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r, w])
        (fun u cost => AnsC (Equiv.refl (Fin m)) u
            (tmGlLab ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r) ∧
          cost ≤ K * ((Val.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
            encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r, w]).wt + 1) ^ D)

/-- **T6: the finite abelian affine transporter procedure**, in its two uses: the glue of one
level of Theorem A.20 (function `gObj`) and the labels of Theorem A.23 (function `gLab`). -/
def TermGlueSpec (K D gObj gLab : ℕ) : Prop :=
  TermGlueObjSpec Pg K D gObj ∧ TermGlueLabSpec Pg K D gLab

end Iface

end GI.Impl
