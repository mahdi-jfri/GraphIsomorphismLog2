import Workspace.Impl.TermJProgTop
import Workspace.Impl.TermJOMath
import Workspace.Impl.TermJAlg
import Workspace.Impl.TermJLabTr

/-!
# Glue of the `J`-step to the row terminal (mathematics)

The programs of the `J`-step (`tmJ_ne_spec`, `tmJH_spec`) are stated for generic data. This file
proves the facts that connect them to the row terminal of Theorem A.23.

* `tmJ_rt_le`, `tmJ_rt_comm`, `tmJ_rt_conj`: `N* ≤ N`, the commutators of `N` lie in `N*`, and
  `N*` is normal in `N` (row normal form, A.18); `tmJ_normal_of`, `tmJ_comm_of`: so the quotient
  `⟨σN⟩/⟨σS⟩` is a commutative group.
* `tmJ_sameKer_of`: the row terminal's `φ` and the Lin* quotient map have the same kernel.
* `tmJ_ker_iff`: the kernel of the sum map in Lin* coordinates.
* `tmJ_autJ_rt`: `Aut_J(x)` of `TermJAutJ3` is `Aut_{N≀Sym}(X) ∩ J`.
* `tmJ_alg_list`: the output coset from a list of corrected lifts, one for each label of
  `h₀ · (1 :: U)` (the list may repeat labels).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Paper Equiv Equiv.Perm
open GI.Cited (gens)
open scoped IsMulCommutative

variable {Ω C : Type}

/-! ### The quotient `⟨σN⟩ / ⟨σS⟩` at a row form -/

section Form

variable {S : State Ω C} {L : GiantLabels S} (F : RowForm S L)

theorem tmJ_rt_le : F.Nstar.map F.Hb.subtype ≤ F.Nb :=
  Subgroup.map_mono F.rnf.nstar_le

theorem tmJ_rt_comm :
    ∀ x ∈ F.Nb, ∀ y ∈ F.Nb, x * y * x⁻¹ * y⁻¹ ∈ F.Nstar.map F.Hb.subtype := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact ⟨_, F.rnf.abelian a ha b hb, by simp⟩

theorem tmJ_rt_conj :
    ∀ x ∈ F.Nstar.map F.Hb.subtype, ∀ y ∈ F.Nb, y * x * y⁻¹ ∈ F.Nstar.map F.Hb.subtype := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, -, rfl⟩
  exact ⟨_, F.Nstar_normal.conj_mem a ha b, by simp⟩

end Form

/-! ### Two presentations with the same kernel -/

section Lin

variable {m q : ℕ} {N : Subgroup (Perm (Fin m))} {A : Type*} [CommGroup A] {φ : N →* A}
  {σS σN : List (Perm (Fin m))} [((gens σS).subgroupOf (gens σN)).Normal]
  [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))]

theorem tmJ_normal_of {σS σN : List (Perm (Fin m))} (hle : gens σS ≤ gens σN)
    (hc : ∀ x ∈ gens σS, ∀ y ∈ gens σN, y * x * y⁻¹ ∈ gens σS) :
    ((gens σS).subgroupOf (gens σN)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hle]
  exact fun x y hx hy => hc x hx y hy

theorem tmJ_comm_of {σS σN : List (Perm (Fin m))} [((gens σS).subgroupOf (gens σN)).Normal]
    (hc : ∀ x ∈ gens σN, ∀ y ∈ gens σN, x * y * x⁻¹ * y⁻¹ ∈ gens σS) :
    IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have := hc _ ((gens σN).inv_mem b.2) _ ((gens σN).inv_mem a.2)
  simpa [mul_assoc] using this

/-- **The same kernel**: `φ` has kernel `⟨σS⟩` on `N = ⟨σN⟩`. -/
theorem tmJ_sameKer_of (hN : gens σN = N) (hk : ∀ n : N, φ n = 1 ↔ n.val ∈ gens σS) :
    TmJSameKer φ (tmJHPsi σS σN) := by
  refine ⟨fun g => by rw [hN], fun g h h' => ?_⟩
  rw [hk ⟨g, h⟩]
  show _ ↔ QuotientGroup.mk' _ _ = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

/-- **The kernel of the sum map in Lin* coordinates.** -/
theorem tmJ_ker_iff (hk : TmJSameKer φ (tmJHPsi σS σN))
    {M : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hcert : linPresentationCertificate M (tmJHF σS σN))
    {lg : List (Fin q × Perm (Fin m))} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
    (hB : ∀ k, tmJHF σS σN (Bm k) = Additive.ofMul (QuotientGroup.mk'
      ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) (lg.get k).2)))
    (c : Fin lg.length → ℤ) :
    (∃ y : Fin σN.length → ℤ, Matrix.vecMul c Bm + Matrix.vecMul y M = 0) ↔
      tmJSumT N φ lg c = 1 := by
  have hlg' : ∀ k : Fin lg.length, (lg.get k).2 ∈ gens σN := fun k => (hk.1 _).1 (hlg k)
  rw [tmJSumT_eq_one_iff hk hlg c]
  have hfB := tmJH_f_B hlg' Bm hB c
  constructor
  · rintro ⟨y, hy⟩
    have e3 : tmJHF σS σN (Matrix.vecMul y M) = 0 := hcert.2.2.1 ⟨y, rfl⟩
    have := congrArg (tmJHF σS σN) hy
    rw [map_add, hfB, e3, add_zero, map_zero] at this
    exact Additive.ofMul.injective this
  · intro h1
    have h0 : tmJHF σS σN (Matrix.vecMul c Bm) = 0 := by rw [hfB, h1]; rfl
    obtain ⟨y', hy'⟩ := (tmJ_cert_ker hcert _).1 h0
    refine ⟨-y', ?_⟩
    change Matrix.vecMul y' M = _ at hy'
    rw [Matrix.neg_vecMul, hy', add_neg_cancel]

end Lin

/-! ### The row terminal -/

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- **`Aut_J(x)` is `Aut_{N≀Sym}(X) ∩ J`.** -/
theorem tmJ_autJ_rt [Nonempty I.B] :
    tmJAutJ I.φ (rowTuple I.e S.x) =
      (tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x))) ⊓ tmJJ I := by
  ext σ
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hX, hl, hs⟩
    refine ⟨⟨⟨p, hp, rfl⟩, hX⟩, (tmJJ_iff_lab I hp).2 ⟨?_, ?_⟩⟩
    · rw [← tmJLabOf_tmJP hp]; exact hl
    · rw [← tmJTop_tmJP (N := I.Nb) hp]; exact Equiv.Perm.mem_alternatingGroup.2 hs
  · rintro ⟨⟨⟨p, hp, rfl⟩, hX⟩, hJ⟩
    obtain ⟨h1, h2⟩ := (tmJJ_iff_lab I hp).1 hJ
    refine ⟨⟨p, hp, rfl⟩, hX, ?_, ?_⟩
    · rw [tmJLabOf_tmJP hp]; exact h1
    · rw [tmJTop_tmJP hp]; exact Equiv.Perm.mem_alternatingGroup.1 h2

/-- A label of a list related entrywise to a list has a partner in the zipped list. -/
theorem tmJ_forall₂_zip {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {ws : List β}, List.Forall₂ R l ws →
      ∀ a ∈ l, ∃ b, (a, b) ∈ l.zip ws ∧ R a b
  | [], [], _, a, ha => absurd ha (List.not_mem_nil)
  | x :: _, y :: _, List.Forall₂.cons h t, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons_self .., h⟩
    · obtain ⟨b, hb, hR⟩ := tmJ_forall₂_zip t a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hR⟩

/-- An element of the right list has a partner. -/
theorem tmJ_forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {ws : List β}, List.Forall₂ R l ws → ∀ b ∈ ws, ∃ a, R a b
  | [], [], _, b, hb => absurd hb (List.not_mem_nil)
  | x :: _, y :: _, List.Forall₂.cons h t, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨x, h⟩
    · exact tmJ_forall₂_right t b hb

/-- **The output coset from a list of corrected lifts** (`tmJ_alg`). The list `t₀ :: ts` has one
element of the piece in the class of each label of `h₀ · (1 :: U)`, in order. -/
theorem tmJ_alg_list [Nonempty I.B] {r : Perm I.B} (hr : r ∈ I.Hb) (h0 : Perm I.B)
    (U : List (Perm I.B))
    (hLab : tmGlLab I r = (h0 * ·) '' (Subgroup.closure {u | u ∈ U} : Set (Perm I.B)))
    (t0 : Perm (I.B × Fin L.q)) (ts : List (Perm (I.B × Fin L.q)))
    (hts : List.Forall₂ (fun h t => t ∈ tmJP '' tmCosetT I r ∧ t ∈ tmJCls I.Nb h)
      ((1 :: U).map (h0 * ·)) (t0 :: ts))
    (ks : List (Perm (I.B × Fin L.q)))
    (hks : Subgroup.closure {k | k ∈ ks} =
      (tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x))) ⊓ tmJJ I) :
    tmJP '' tmCosetT I r = (t0 * ·) '' (Subgroup.closure
      ({a | ∃ t ∈ t0 :: ts, a = t0⁻¹ * t} ∪ {k | k ∈ ks}) : Set (Perm (I.B × Fin L.q))) := by
  classical
  set l := (1 :: U).map (h0 * ·) with hl
  have hall : ∀ t ∈ t0 :: ts, t ∈ tmJP '' tmCosetT I r := by
    intro t ht
    obtain ⟨a, hR⟩ := tmJ_forall₂_right hts t ht
    exact hR.1
  let t : Perm I.B → Perm (I.B × Fin L.q) := fun h =>
    if h = h0 then t0 else if hh : ∃ τ, (h, τ) ∈ l.zip (t0 :: ts) then hh.choose
    else if hl' : h ∈ tmGlLab I r then (tmJ_lab_exists I hl').choose else 1
  have hhd : (fun h t => t ∈ tmJP '' tmCosetT I r ∧ t ∈ tmJCls I.Nb h) h0 t0 := by
    have := (List.forall₂_cons.1 hts).1
    simpa using this
  have ht : ∀ h ∈ tmGlLab I r, t h ∈ tmJP '' tmCosetT I r ∧ t h ∈ tmJCls I.Nb h := by
    intro h hh
    by_cases e0 : h = h0
    · subst e0; simp only [t, if_pos rfl]; exact hhd
    · by_cases hz : ∃ τ, (h, τ) ∈ l.zip (t0 :: ts)
      · simp only [t, if_neg e0, dif_pos hz]
        exact (List.forall₂_iff_zip.1 hts).2 hz.choose_spec
      · simp only [t, if_neg e0, dif_neg hz, dif_pos hh]
        exact (tmJ_lab_exists I hh).choose_spec
  have ht0 : t h0 = t0 := by simp [t]
  have hA := tmJ_alg I hr h0 U hLab t ht ks hks
  rw [ht0] at hA
  rw [hA]
  congr 2
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro a (⟨u, hu, rfl⟩ | hk)
    · apply Subgroup.subset_closure
      left
      by_cases e0 : h0 * u = h0
      · exact ⟨t0, List.mem_cons_self .., by rw [e0, ht0]⟩
      · have hmem : h0 * u ∈ l := List.mem_map.2 ⟨u, List.mem_cons_of_mem _ hu, rfl⟩
        obtain ⟨τ, hτ, -⟩ := tmJ_forall₂_zip hts _ hmem
        have hz : ∃ τ, (h0 * u, τ) ∈ l.zip (t0 :: ts) := ⟨τ, hτ⟩
        refine ⟨t (h0 * u), ?_, rfl⟩
        simp only [t, if_neg e0, dif_pos hz]
        exact (List.of_mem_zip hz.choose_spec).2
    · exact Subgroup.subset_closure (Or.inr hk)
  · rw [Subgroup.closure_le]
    rintro a (⟨τ, hτ, rfl⟩ | hk)
    · have hτP := hall τ hτ
      rw [hA] at hτP
      obtain ⟨c, hc, he⟩ := hτP
      simp only at he
      rw [← he, inv_mul_cancel_left]
      exact hc
    · exact Subgroup.subset_closure (Or.inr hk)

end RT

end GI.Impl
