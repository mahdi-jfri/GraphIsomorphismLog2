module

public import Workspace.Impl.TermJGroup
public import Workspace.Impl.TermJCoset
public import Workspace.Impl.TermJYoung
public import Workspace.Impl.TermJMatch

@[expose] public section

/-!
# The `J`-step as an algorithm on mathematical values

This file states the `J`-step of Theorem A.23 with the outputs of the cited calls as data, and
proves that the result is the piece `tmJP '' tmCosetT I r` as a coset (`tmJ_alg`). The program
of `TermJSpec` only has to produce these data.

* `tmJ_mem_closure_append`: in a finite group, if `gs` normalizes `⟨ns⟩` then
  `⟨gs, ns⟩ = ⟨gs⟩ ⟨ns⟩`. This is the precondition of NormalizedFactor after a Membership test.
* `tmJ_local_iff`, `tmJ_local_of_fac`: **the local transporters in the class `h N`.** For the
  stored coset `Iso_H(x_a, y_j) = g ⟨gs⟩` (with `⟨gs⟩ = Aut_H(y_j)`), some transporter lies in
  `h N` exactly when `g⁻¹ h ∈ ⟨gs, N⟩` (a Membership test), and a factorization
  `g⁻¹ h = s n` gives the transporter `g s` (the paper: "the known membership in
  `N Iso_H(z_a, z_c)`, together with constructive factorization in the normalized product …,
  supplies the required local `N`-transporter").
* `tmJ_local_rect`, `tmJ_local_match`: the 0/1 matrix of these tests has the rectangle property
  and, for a label element `h`, a perfect matching (`tmJ_lab_exists`); so `tmJMatch_spec`
  applies.
* `tmJ_corr`: the corrected lift of a label element (`tmJ_correct`).
* `tmJ_alg`: the output coset.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm

/-! ### Products of a normalizing and a normalized subgroup -/

/-- **`⟨gs, ns⟩ = ⟨gs⟩⟨ns⟩`** when `gs` normalizes `⟨ns⟩`, in a finite group. -/
theorem tmJ_mem_closure_append {G : Type} [Group G] [Finite G] {gs ns : List G}
    (hn : ∀ g ∈ gs, ∀ x ∈ Subgroup.closure {y | y ∈ ns},
      g * x * g⁻¹ ∈ Subgroup.closure {y | y ∈ ns}) {x : G} :
    x ∈ Subgroup.closure {y | y ∈ gs ++ ns} ↔ ∃ a ∈ Subgroup.closure {y | y ∈ gs},
      ∃ b ∈ Subgroup.closure {y | y ∈ ns}, x = a * b := by
  set Nn := Subgroup.closure {y | y ∈ ns}
  set Gg := Subgroup.closure {y | y ∈ gs}
  -- every element of `⟨gs⟩` normalizes `⟨ns⟩`
  have hpow : ∀ a : G, (∀ y ∈ Nn, a * y * a⁻¹ ∈ Nn) → ∀ k : ℕ, ∀ y ∈ Nn,
      a ^ k * y * (a ^ k)⁻¹ ∈ Nn := by
    intro a ha k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have := ha _ (ih y hy)
      rw [pow_succ']
      simpa [mul_assoc] using this
  have hall : ∀ a ∈ Gg, ∀ y ∈ Nn, a * y * a⁻¹ ∈ Nn := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact hn a ha
    | one => intro y hy; simpa using hy
    | mul a b _ _ iha ihb =>
      intro y hy
      have := iha _ (ihb y hy)
      simpa [mul_assoc] using this
    | inv a _ iha =>
      intro y hy
      have hfin : a⁻¹ = a ^ (orderOf a - 1) := by
        rw [← mul_left_cancel_iff (a := a), mul_inv_cancel, ← pow_succ',
          Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      rw [hfin]
      exact hpow a iha _ y hy
  -- the product set is a subgroup
  let Pr : Subgroup G :=
    { carrier := {x | ∃ a ∈ Gg, ∃ b ∈ Nn, x = a * b}
      one_mem' := ⟨1, Gg.one_mem, 1, Nn.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', Gg.mul_mem ha ha', a'⁻¹ * b * a'⁻¹⁻¹ * b',
          Nn.mul_mem (hall _ (Gg.inv_mem ha') _ hb) hb', by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, Gg.inv_mem ha, a * b⁻¹ * a⁻¹, hall _ ha _ (Nn.inv_mem hb), by group⟩ }
  constructor
  · intro hx
    have hle : Subgroup.closure {y | y ∈ gs ++ ns} ≤ Pr := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact ⟨y, Subgroup.subset_closure hy, 1, Nn.one_mem, by simp⟩
      · exact ⟨1, Gg.one_mem, y, Subgroup.subset_closure hy, by simp⟩
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.closure_mono (fun y hy => List.mem_append_left _ hy) ha
    · exact Subgroup.closure_mono (fun y hy => List.mem_append_right _ hy) hb

/-! ### The row terminal -/

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- The stored coset `Iso_H(x_a, y_j)`. -/
theorem tmJ_coset_answer (a j : Fin L.q) (u : Perm I.B) :
    u ∈ (I.cosetCall (a, j)).answer ↔ u ∈ I.Hb ∧ rowTuple I.e S.x a ∘ u = rowTuple I.e S.y j := by
  rw [cosetCall, rowState_answer]; rfl

/-- The matrix of local tests of the class `h`: `x_a` has a transporter to `y_j` in `h N`. -/
def tmJLocal (h : Perm I.B) (a j : Fin L.q) : Prop :=
  ∃ u ∈ (I.cosetCall (a, j)).answer, h⁻¹ * u ∈ I.Nb

/-- **The local test is a Membership test.** -/
theorem tmJ_local_iff {h : Perm I.B} {a j : Fin L.q} {g : Perm I.B}
    {gs ns : List (Perm I.B)} (hns : Subgroup.closure {y | y ∈ ns} = I.Nb)
    (hgs : ∀ s ∈ gs, s ∈ I.Hb)
    (hA : (I.cosetCall (a, j)).answer = (g * ·) '' (Subgroup.closure {y | y ∈ gs} : Set _)) :
    tmJLocal I h a j ↔ g⁻¹ * h ∈ Subgroup.closure {y | y ∈ gs ++ ns} := by
  have hn : ∀ s ∈ gs, ∀ x ∈ Subgroup.closure {y | y ∈ ns},
      s * x * s⁻¹ ∈ Subgroup.closure {y | y ∈ ns} := by
    intro s hs x hx; rw [hns] at hx ⊢; exact I.normalizes s (hgs s hs) x hx
  rw [tmJ_mem_closure_append hn, hns]
  constructor
  · rintro ⟨u, hu, hun⟩
    rw [hA] at hu
    obtain ⟨s, hs, rfl⟩ := hu
    exact ⟨s, hs, (h⁻¹ * (g * s))⁻¹, I.Nb.inv_mem hun, by group⟩
  · rintro ⟨s, hs, n, hn', he⟩
    refine ⟨g * s, by rw [hA]; exact ⟨s, hs, rfl⟩, ?_⟩
    have : h⁻¹ * (g * s) = n⁻¹ := by
      have : g * s = h * n⁻¹ := by
        have := congrArg (g * ·) he
        rw [mul_inv_cancel_left] at this
        rw [this]; group
      rw [this]; group
    rw [this]; exact I.Nb.inv_mem hn'

/-- **The local transporter from a factorization** `g⁻¹ h = s n`. -/
theorem tmJ_local_of_fac {h : Perm I.B} {a j : Fin L.q} {g s n : Perm I.B}
    {gs : List (Perm I.B)}
    (hA : (I.cosetCall (a, j)).answer = (g * ·) '' (Subgroup.closure {y | y ∈ gs} : Set _))
    (hs : s ∈ Subgroup.closure {y | y ∈ gs}) (hn : n ∈ I.Nb) (he : g⁻¹ * h = s * n) :
    g * s ∈ (I.cosetCall (a, j)).answer ∧ h⁻¹ * (g * s) ∈ I.Nb := by
  refine ⟨by rw [hA]; exact ⟨s, hs, rfl⟩, ?_⟩
  have : g * s = h * n⁻¹ := by
    have h1 : h = g * (s * n) := by rw [← he]; group
    rw [h1]; group
  rw [this, inv_mul_cancel_left]; exact I.Nb.inv_mem hn

/-- **The local tests have the rectangle property.** -/
theorem tmJ_local_rect {h : Perm I.B} {a a' j j' : Fin L.q} (h1 : tmJLocal I h a j)
    (h2 : tmJLocal I h a' j) (h3 : tmJLocal I h a j') : tmJLocal I h a' j' := by
  obtain ⟨u1, hu1, hn1⟩ := h1
  obtain ⟨u2, hu2, hn2⟩ := h2
  obtain ⟨u3, hu3, hn3⟩ := h3
  rw [tmJ_coset_answer] at hu1 hu2 hu3
  refine ⟨u2 * u1⁻¹ * u3, (tmJ_coset_answer I _ _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact I.Hb.mul_mem (I.Hb.mul_mem hu2.1 (I.Hb.inv_mem hu1.1)) hu3.1
  · have e1 : rowTuple I.e S.x a' ∘ ⇑(u2 * u1⁻¹) = rowTuple I.e S.x a := by
      rw [coe_mul, ← Function.comp_assoc, hu2.2, ← hu1.2]; funext c; simp
    rw [← hu3.2, coe_mul, ← Function.comp_assoc, e1]
  · have e : h⁻¹ * (u2 * u1⁻¹ * u3) = (h⁻¹ * u2) * (h⁻¹ * u1)⁻¹ * (h⁻¹ * u3) := by group
    rw [e]
    exact I.Nb.mul_mem (I.Nb.mul_mem hn2 (I.Nb.inv_mem hn1)) hn3

/-- **A label element has a perfect matching of local tests**: the matching of an element of
the piece in its class. -/
theorem tmJ_local_match [Nonempty I.B] {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r) :
    ∃ π : Perm (Fin L.q), ∀ a, tmJLocal I h a (π a) := by
  obtain ⟨t, ht, hc⟩ := tmJ_lab_exists I hL
  obtain ⟨-, hY, -⟩ := (tmJ_mem_T I hr).1 ht
  obtain ⟨p, rfl, hp⟩ := hc
  have hhH : h ∈ I.Hb := tmJ_lab_le I hL
  refine ⟨p.2, fun a => ⟨p.1 a, (tmJ_coset_answer I _ _ _).2 ⟨?_, ?_⟩, hp a⟩⟩
  · have := I.Hb.mul_mem hhH (I.Nb_le (hp a)); rwa [mul_inv_cancel_left] at this
  · exact (tmJ_mem_iso _ _ p).1 hY a

/-- **The local transporter `z`**: a pair `(d; σ)` with `d_a` a transporter `x_a → y_{σ a}` in
`h N` carries `X` to `Y` and has class `h`. -/
theorem tmJ_z_spec {h : Perm I.B} (σ : Perm (Fin L.q)) (d : Fin L.q → Perm I.B)
    (hd : ∀ a, d a ∈ (I.cosetCall (a, σ a)).answer ∧ h⁻¹ * d a ∈ I.Nb) :
    tmJStr (rowTuple I.e S.y) ∘ tmJP (d, σ) = tmJStr (rowTuple I.e S.x) ∧
      tmJP (d, σ) ∈ tmJCls I.Nb h :=
  ⟨(tmJ_mem_iso _ _ (d, σ)).2 fun a => ((tmJ_coset_answer I _ _ _).1 (hd a).1).2,
    ⟨_, rfl, fun a => (hd a).2⟩⟩

/-! ### The correction and the output -/

/-- **The corrected lift of a label element** (Theorem A.23: "lift the surviving quotient
representative and correct it by the constructed `J`-transporter"). Let `g` come from a
factorization `(h; 1) = g w` in `G|_dom · N ≀ Sym(q)` and `z` be a local transporter of class
`h`. Then `z⁻¹ g` factors in `Aut_{N≀Sym}(X) · J`, and every factorization `z⁻¹ g = a j` gives
an element `z a` of the piece of class `h`. -/
theorem tmJ_corr [Nonempty I.B] {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r)
    {g w z : Perm (I.B × Fin L.q)} (hg : g ∈ tmJG I) (hw : w ∈ tmJW I.Nb)
    (hf : tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * w)
    (hzY : tmJStr (rowTuple I.e S.y) ∘ z = tmJStr (rowTuple I.e S.x))
    (hzc : z ∈ tmJCls I.Nb h) :
    (∃ a ∈ tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)), ∃ j ∈ tmJJ I, z⁻¹ * g = a * j) ∧
    ∀ a ∈ tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)), ∀ j ∈ tmJJ I, z⁻¹ * g = a * j →
      z * a ∈ tmJP '' tmCosetT I r ∧ z * a ∈ tmJCls I.Nb h := by
  have hhH : h ∈ I.Hb := tmJ_lab_le I hL
  have hgc : g ∈ tmJCls I.Nb h := tmJ_lift_cls I.normalizes hw hf hhH
  obtain ⟨xh, hxh, hxr⟩ := hL.1.2
  refine ⟨?_, fun a ha j hj he => ?_⟩
  · obtain ⟨t, ht, htc⟩ := tmJ_lab_exists I hL
    obtain ⟨htG, htY, -⟩ := (tmJ_mem_T I hr).1 ht
    exact tmJ_correct_pre I.normalizes (tmJG I) hhH hzY hzc hg hgc htG htY htc
  · obtain ⟨h1, h2, h3⟩ := tmJ_correct I.normalizes (tmJG I) hhH hzY hg hgc ha hj he
    refine ⟨(tmJ_mem_T I hr).2 ⟨h1, h2, xh, hxh, ?_⟩, h3⟩
    rw [← hxr]; exact h3

/-- **The output coset of the `J`-step.** With `tmGlLab I r = h₀ ⟨U⟩`, corrected lifts `t h₀` and
`t (h₀ u)` in the piece of the right classes, and `ks` generating `Aut_J(X)`, the piece is
`t h₀ ⟨(t h₀)⁻¹ t (h₀ u) (u ∈ U), ks⟩`. -/
theorem tmJ_alg [Nonempty I.B] {r : Perm I.B} (hr : r ∈ I.Hb) (h0 : Perm I.B)
    (U : List (Perm I.B))
    (hLab : tmGlLab I r = (h0 * ·) '' (Subgroup.closure {u | u ∈ U} : Set (Perm I.B)))
    (t : Perm I.B → Perm (I.B × Fin L.q))
    (ht : ∀ h ∈ tmGlLab I r, t h ∈ tmJP '' tmCosetT I r ∧ t h ∈ tmJCls I.Nb h)
    (ks : List (Perm (I.B × Fin L.q)))
    (hks : Subgroup.closure {k | k ∈ ks} =
      (tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x))) ⊓ tmJJ I) :
    tmJP '' tmCosetT I r = (t h0 * ·) '' (Subgroup.closure
      ({a | ∃ u ∈ U, a = (t h0)⁻¹ * t (h0 * u)} ∪ {k | k ∈ ks}) : Set (Perm (I.B × Fin L.q))) := by
  have hNR : I.Nb ≤ tmRad I := I.Nb_le_rad
  have hRH : tmRad I ≤ I.Hb := I.rad_le
  have h0L : h0 ∈ tmGlLab I r := by rw [hLab]; exact ⟨1, Subgroup.one_mem _, mul_one h0⟩
  have huL : ∀ u ∈ U, h0 * u ∈ tmGlLab I r := fun u hu => by
    rw [hLab]; exact ⟨u, Subgroup.subset_closure hu, rfl⟩
  refine tmJ_coset_eq I.normalizes (tmJG I) (tmRad I) hRH hr _ (fun σ => tmJ_mem_T I hr)
    (tmGlLab I r) h0 U hLab (fun h hh => hh.1.2) (fun t ht => tmJ_T_lab I ht) (t h0)
    (ht h0 h0L).1 (ht h0 h0L).2 (fun u => t (h0 * u)) (fun u hu => ht _ (huL u hu)) ks ?_
  rw [hks, tmJJ]
  ext σ
  simp only [Subgroup.mem_inf]
  tauto

end RT

end GI.Impl
