module

public import Workspace.Impl.TermJGlueMath

@[expose] public section

/-!
# Glue of the `J`-step: the generators of `Aut_J(x)`

`tmJ_aut_closure`: the list `al` that `tmJ_aut_spec` returns generates `Aut_J(x)` of
`TermJAutJ3` (`tmJ_autJ_gens`). The three parts are the local `N*`-stabilizers (the rows of the
NormalizedIntersection calls), the local products of the kernel rows of the sum map, and the
products `t₀ t` of lifted transpositions (proof of Theorem A.23: "Solving these finite abelian
equations constructs a transporter. It also constructs `Aut_J(x)`").

When `σN = []` the program has no kernel rows. Then `N = 1`, the sum map is trivial, and
`tmJ_autJ_gens` is applied with the unit vectors, whose local products are `1`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Paper Equiv Equiv.Perm
open GI.Cited (gens encPerm)
open scoped IsMulCommutative

variable {m q : ℕ}

theorem tmJPermsVal_injective : Function.Injective (tmJPermsVal (m := m) (q := q)) := by
  intro a b h
  simp only [tmJPermsVal] at h
  injection h with h
  exact (List.map_injective_iff.2 (fun x y hxy => (toFin _).injective (GI.Lang.encPerm_injective hxy))) h

theorem tmJLam_triv {B : Type} {lg : List (Fin q × Perm B)} (h : ∀ k : Fin lg.length, (lg.get k).2 = 1)
    (c : Fin lg.length → ℤ) : tmJLam lg c = 1 := by
  unfold tmJLam tmJLamD
  have e : (fun a : Fin q => ((List.finRange lg.length).map fun k =>
      if (lg.get k).1 = a then (lg.get k).2 ^ c k else 1).prod) = 1 := by
    funext a
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    split_ifs
    · rw [h k, one_zpow]
    · rfl
  rw [e]
  exact tmJP_one

theorem tmJ_gens_nil : gens ([] : List (Perm (Fin m))) = ⊥ := by
  unfold gens
  simp

/-- Every integer vector lies in the span of the unit vectors. -/
theorem tmJ_units_span {n : ℕ} (e : Fin n → ℤ) :
    e ∈ AddSubgroup.closure {c | c ∈ (List.finRange n).map fun k => (Pi.single k 1 : Fin n → ℤ)} := by
  rw [← Finset.univ_sum_single e]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  have : (Pi.single k (e k) : Fin n → ℤ) = e k • (Pi.single k 1 : Fin n → ℤ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this]
  apply AddSubgroup.zsmul_mem
  apply AddSubgroup.subset_closure
  exact List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩

theorem tmJ_mem_S3 {Tl : List (Fin q × Fin q × Perm (Fin m))} {σ : Perm (Fin m × Fin q)}
    (h : σ ∈ tmJS3List Tl) : ∃ t0 ∈ Tl.head?, ∃ t ∈ Tl,
      σ = tmJSw t0.1 t0.2.1 t0.2.2 * tmJSw t.1 t.2.1 t.2.2 := by
  cases Tl with
  | nil => simp [tmJS3List] at h
  | cons x Tl =>
    simp only [tmJS3List, tmJTsList, List.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨x, rfl, t, ht, rfl⟩

theorem tmJ_S3_mem {Tl : List (Fin q × Fin q × Perm (Fin m))} {t0 t : Fin q × Fin q × Perm (Fin m)}
    (h0 : t0 ∈ Tl.head?) (ht : t ∈ Tl) :
    tmJSw t0.1 t0.2.1 t0.2.2 * tmJSw t.1 t.2.1 t.2.2 ∈ tmJS3List Tl := by
  cases Tl with
  | nil => simp at ht
  | cons x Tl =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h0
    subst h0
    simp only [tmJS3List, tmJTsList, List.mem_map]
    exact ⟨t, ht, rfl⟩

theorem tmJ_closure_inv_list {G : Type*} [Group G] (l : List G) :
    Subgroup.closure {s | s ∈ l.map (·⁻¹)} = Subgroup.closure {s | s ∈ l} := by
  have : {s | s ∈ l.map (·⁻¹)} = {s | s ∈ l}⁻¹ := by
    ext s
    simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_inv]
    constructor
    · rintro ⟨t, ht, rfl⟩; simpa using ht
    · intro h; exact ⟨s⁻¹, h, inv_inv s⟩
  rw [this, Subgroup.closure_inv]

/-- **The `Aut_J` list generates `Aut_J(x)`.** -/
theorem tmJ_aut_closure (hm : 0 < m) {N : Subgroup (Perm (Fin m))} {A : Type*} [CommGroup A]
    {φ : N →* A} {C : Type} (x : Fin q → Fin m → C) {σS σN : List (Perm (Fin m))}
    [((gens σS).subgroupOf (gens σN)).Normal]
    [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))]
    (hN : gens σN = N) (hS : φ.ker.map N.subtype = gens σS) (hk : TmJSameKer φ (tmJHPsi σS σN))
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs) ∧
      Subgroup.closure {s | s ∈ gs} = tmJRowAut N (x a))
    (hsome : ∀ a a' b gs, O a a' = some (b, gs) → b ∈ N ∧ x a ∘ b = x a')
    (hnone : ∀ a a', O a a' = none → ∀ b ∈ N, x a ∘ b ≠ x a')
    {M : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hcert : linPresentationCertificate M (tmJHF σS σN))
    {Bm : Matrix (Fin (tmJLgList O).length) (Fin σN.length) ℤ}
    (hB : ∀ k, tmJHF σS σN (Bm k) = Additive.ofMul (QuotientGroup.mk'
      ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) ((tmJLgList O).get k).2)))
    (al : List (Perm (Fin m × Fin q)))
    (hal : tmJAutOut O σS σN (tmJLgList O) (tmJTlList O) Bm M (tmJPermsVal al)) :
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    Subgroup.closure {k | k ∈ al} = tmJAutJ φ x := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  classical
  obtain ⟨hsA, Ks, h1, h2, h3, hout⟩ := hal
  have hal' := tmJPermsVal_injective hout
  subst hal'
  have hlgN : ∀ k : Fin (tmJLgList O).length, ((tmJLgList O).get k).2 ∈ N := fun k => (tmJTab_lg_mem hloc k).1
  have hTl : ∀ t ∈ (tmJTlList O), t.1 ≠ t.2.1 ∧ t.2.2 ∈ N := fun t ht =>
    ⟨(tmJTab_tl_mem hsome t ht).1, (tmJTab_tl_mem hsome t ht).2.1⟩
  set Cs : List (Fin (tmJLgList O).length → ℤ) :=
    if σN = [] then (List.finRange (tmJLgList O).length).map fun k => Pi.single k 1 else Ks with hCs
  have hNbot : σN = [] → N = ⊥ := fun h0 => by rw [← hN, h0, tmJ_gens_nil]
  have hC : ∀ e, e ∈ AddSubgroup.closure {c | c ∈ Cs} ↔ tmJSumT N φ (tmJLgList O) e = 1 := by
    intro e
    by_cases h0 : σN = []
    · have hb := hNbot h0
      simp only [hCs, if_pos h0]
      refine ⟨fun _ => ?_, fun _ => tmJ_units_span e⟩
      unfold tmJSumT
      refine Finset.prod_eq_one fun k _ => ?_
      have : ((tmJLgList O).get k).2 = 1 := by have := hlgN k; rw [hb] at this; exact this
      rw [this, phiT_one, one_zpow]
    · simp only [hCs, if_neg h0]
      rw [h3 h0 e]
      exact tmJ_ker_iff hk hcert hlgN Bm hB e
  have hns : ∀ a, Subgroup.closure {s | s ∈ (hsA a).map (·⁻¹)} =
      tmJRowAut (φ.ker.map N.subtype) (x a) := by
    intro a
    obtain ⟨r, gs, hO, hgs⟩ := hloc a
    rw [tmJ_closure_inv_list]
    change gens (hsA a) = _
    rw [h1 a r gs hO, ← hS]
    change Subgroup.closure {s | s ∈ gs} ⊓ _ = _
    rw [hgs]
    ext s
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hz⟩, hs⟩; exact ⟨hs, hz⟩
    · rintro ⟨hs, hz⟩; exact ⟨⟨Subgroup.map_subtype_le _ hs, hz⟩, hs⟩
  have hgen := tmJ_autJ_gens (φ := φ) (x := x) (tmJHLocs (tmJLgList O)) (tmJH_locs_top hlgN) (tmJTlList O) hTl
    (tmJTab_aut hloc hsome hnone) (tmJLgList O) (tmJTab_lg_row hloc) (fun a => (hsA a).map (·⁻¹)) hns Cs hC
  rw [← hgen]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro σ hσ
    simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map] at hσ
    rcases hσ with (hσ | ⟨c, hc, rfl⟩) | hσ
    · simp only [tmJNsList, List.mem_flatten] at hσ
      obtain ⟨l, hl, hσl⟩ := hσ
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hl
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hσl
      exact Subgroup.subset_closure (Or.inl (Or.inl ⟨a, s⁻¹, List.mem_map.2 ⟨s, hs, rfl⟩, rfl⟩))
    · have h0 : σN ≠ [] := fun h0 => by rw [h2 h0] at hc; simp at hc
      refine Subgroup.subset_closure (Or.inl (Or.inr ⟨c, ?_, rfl⟩))
      simp only [hCs, if_neg h0]; exact hc
    · obtain ⟨t0, ht0, t, ht, rfl⟩ := tmJ_mem_S3 hσ
      exact Subgroup.subset_closure (Or.inr ⟨t0, ht0, t, ht, rfl⟩)
  · rw [Subgroup.closure_le]
    rintro σ ((⟨a, s, hs, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨t0, ht0, t, ht, rfl⟩)
    · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
      refine Subgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq, List.mem_append]
      refine Or.inl (Or.inl ?_)
      exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨a, List.mem_finRange a, rfl⟩,
        List.mem_map.2 ⟨s', hs', rfl⟩⟩
    · by_cases h0 : σN = []
      · have hb := hNbot h0
        have : tmJLam (tmJLgList O) c = 1 := tmJLam_triv (fun k => by
          have := hlgN k; rw [hb] at this; exact this) c
        rw [this]
        exact Subgroup.one_mem _
      · simp only [hCs, if_neg h0] at hc
        refine Subgroup.subset_closure ?_
        simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
    · refine Subgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq, List.mem_append]
      exact Or.inr (tmJ_S3_mem ht0 ht)

end GI.Impl
