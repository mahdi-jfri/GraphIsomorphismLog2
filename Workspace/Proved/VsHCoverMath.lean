module

public import Workspace.Proved.VsPPairMath
public import Workspace.Impl.VsPEnum

@[expose] public section

/-!
# The words cover `Ȳ` modulo `S`

If `N = ⟨gs⟩` has commutators and `r`-th powers in `S`, and `S` commutes with `N`, then every
element of `N ⊔ S` is a word `∏ g_i^{c_i}` (`c_i < r`) times an element of `S`
(`vsH_cover_W`). For permutations, these words are listed by `vsPEnum r B` (`vsPEnum_W_mem`).
-/

namespace GI.Proved

open GI.Impl Equiv

variable {G : Type*} [Group G]

/-- **Words cover `N ⊔ S` modulo `S`.** -/
theorem vsH_cover_W {N S : Subgroup G} {r : ℕ} (hr : 0 < r) (hQ : VsPQuotHyp N S r) {gs : List G}
    (hN : N = Subgroup.closure {g | g ∈ gs}) :
    ∀ x ∈ N ⊔ S, ∃ e : List ℕ, e.length = gs.length ∧ (∀ c ∈ e, c < r) ∧ (vsPW gs e)⁻¹ * x ∈ S := by
  classical
  have hgN : ∀ g ∈ gs, g ∈ N := fun g hg => hN ▸ Subgroup.subset_closure hg
  haveI := hQ.normal
  letI : CommGroup (N ⧸ S.subgroupOf N) := hQ.commGroup
  set ψ : N →* N ⧸ S.subgroupOf N := QuotientGroup.mk' (S.subgroupOf N)
  have hψr : ∀ q : N ⧸ S.subgroupOf N, q ^ r = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    erw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      SubgroupClass.coe_pow]
    exact hQ.pow y y.2
  let gN : Fin gs.length → N := fun i => ⟨gs[i], hgN _ (List.getElem_mem i.2)⟩
  -- the closure of the generators in `N` is everything
  have htop : Subgroup.closure (Set.range gN) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have : ∀ y ∈ Subgroup.closure {g | g ∈ gs}, ∀ hy : y ∈ N,
        (⟨y, hy⟩ : N) ∈ Subgroup.closure (Set.range gN) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        intro hyN
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
        exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
      | one => intro _; exact one_mem _
      | mul y z hy hz ihy ihz =>
        intro hyz
        have hyN : y ∈ N := hN ▸ hy
        have hzN : z ∈ N := hN ▸ hz
        have := mul_mem (ihy hyN) (ihz hzN)
        exact this
      | inv y hy ihy =>
        intro hyN
        have hyN' : y ∈ N := hN ▸ hy
        exact inv_mem (ihy hyN')
    exact this x (hN ▸ hx) hx
  intro x hx
  have hSN : ∀ a ∈ N, ∀ t ∈ S, a * t = t * a := fun a ha t ht => (hQ.sc t ht a ha).symm
  obtain ⟨a, ha, t, ht, rfl⟩ := vsM_mem_sup_comm hSN hx
  have hψa : ψ ⟨a, ha⟩ ∈ Subgroup.closure (Set.range (fun i => ψ (gN i))) := by
    have : ψ ⟨a, ha⟩ ∈ (Subgroup.closure (Set.range gN)).map ψ :=
      Subgroup.mem_map_of_mem _ (by rw [htop]; trivial)
    rwa [MonoidHom.map_closure, ← Set.range_comp] at this
  obtain ⟨z, hz⟩ := Subgroup.exists_of_mem_closure_range _ _ hψa
  set c : Fin gs.length → ℕ := fun i => (z i % (r : ℤ)).toNat
  have hc : ∀ i, ((c i : ℕ) : ℤ) = z i % (r : ℤ) := fun i =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hr.ne'))
  refine ⟨List.ofFn c, by simp, fun d hd => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
    have := hc i
    have h2 : z i % (r : ℤ) < r := Int.emod_lt_of_pos _ (by exact_mod_cast hr)
    omega
  · have hwN : vsPW gs (List.ofFn c) ∈ N := vsPW_mem hgN _
    have hw : vsPW gs (List.ofFn c) = ((List.ofFn fun i => gN i ^ c i).prod : N) := by
      rw [Subgroup.val_list_prod, vsPW, vsP_zipWith_ofFn _ _ _ (by simp)]
      simp [List.map_ofFn, Function.comp_def, gN]
    have hψw : ψ ⟨vsPW gs (List.ofFn c), hwN⟩ = ψ ⟨a, ha⟩ := by
      have e1 : (⟨vsPW gs (List.ofFn c), hwN⟩ : N) = (List.ofFn fun i => gN i ^ c i).prod :=
        Subtype.ext hw
      rw [e1, map_list_prod, List.map_ofFn, hz, List.prod_ofFn]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Function.comp_apply, map_pow]
      rw [← zpow_natCast, hc i, ← zpow_eq_zpow_emod' _ (hψr _)]
    have hS' : ((⟨vsPW gs (List.ofFn c), hwN⟩ : N)⁻¹ * ⟨a, ha⟩ : N) ∈ S.subgroupOf N := by
      rw [← QuotientGroup.eq]; exact hψw
    rw [Subgroup.mem_subgroupOf] at hS'
    have e2 : (vsPW gs (List.ofFn c))⁻¹ * (a * t) = ((vsPW gs (List.ofFn c))⁻¹ * a) * t := by group
    rw [e2]
    exact mul_mem (by simpa using hS') ht

/-- The words with exponents below `r` are listed by `vsPEnum`. -/
theorem vsPEnum_W_mem {n r : ℕ} (B : List (Perm (Fin n))) :
    ∀ e : List ℕ, e.length = B.length → (∀ c ∈ e, c < r) → vsPW B e ∈ vsPEnum r B := by
  have key : ∀ (B : List (Perm (Fin n))) (E : List (Perm (Fin n))) (w : Perm (Fin n)), w ∈ E →
      ∀ e : List ℕ, e.length = B.length → (∀ c ∈ e, c < r) →
        w * vsPW B e ∈ B.foldl (fun E b => E.flatMap fun e => (List.range r).map fun c => e * b ^ c) E := by
    intro B
    induction B with
    | nil => intro E w hw e he _; simp at he; subst he; simpa [vsPW] using hw
    | cons b B ih =>
      intro E w hw e he hr
      cases e with
      | nil => simp at he
      | cons c e =>
        rw [vsPW_cons, List.foldl_cons, ← mul_assoc]
        refine ih _ _ ?_ e (by simpa using he) (fun d hd => hr d (by simp [hd]))
        simp only [List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨w, hw, c, hr c (by simp), rfl⟩
  intro e he hr
  simpa [vsPEnum] using key B [1] 1 (by simp) e he hr

end GI.Proved
