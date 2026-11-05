module

public import Workspace.Proved.VsHCountMath

@[expose] public section

/-!
# Words of a family that commutes modulo `S`

The generators `ys` of `Ȳ` commute only modulo `S`. A family of them that is independent
modulo `S` still has distinct words modulo `S` (`vsH_W_inj'`), so `r ^ k ≤ |Y : S|`
(`vsH_pow_le_index'`). This bounds the greedy pass that picks a basis of `Ȳ / S`.
-/

namespace GI.Proved

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem VsPQuotHyp.mono {N N' S : Subgroup G} {r : ℕ} (h : VsPQuotHyp N S r) (hle : N' ≤ N) :
    VsPQuotHyp N' S r :=
  ⟨fun s hs x hx => h.sc s hs x (hle hx), fun x hx y hy => h.comm x (hle hx) y (hle hy),
    fun x hx => h.pow x (hle hx)⟩

/-- **Distinct words modulo `S`**, for a family that commutes modulo `S`. -/
theorem vsH_W_inj' {S : Subgroup G} {r : ℕ} (hr : r.Prime) :
    ∀ (gs : List G), VsPQuotHyp (Subgroup.closure {a | a ∈ gs}) S r →
      (∀ (i : ℕ) (hi : i < gs.length), gs[i] ∉ Subgroup.closure {a | a ∈ gs.take i} ⊔ S) →
      ∀ c d : List ℕ, c.length = gs.length → d.length = gs.length → (∀ x ∈ c, x < r) →
        (∀ x ∈ d, x < r) → (vsPW gs c)⁻¹ * vsPW gs d ∈ S → c = d := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ _ c d hc hd _ _ _; simp at hc hd; rw [hc, hd]
  | append_singleton gs x ih =>
    intro hQ hind c d hc hd hcr hdr hcd
    obtain ⟨c', a, rfl⟩ : ∃ c' a, c = c' ++ [a] := by
      rcases List.eq_nil_or_concat c with h | ⟨c', a, h⟩
      · rw [h] at hc; simp at hc
      · exact ⟨c', a, by simpa using h⟩
    obtain ⟨d', b, rfl⟩ : ∃ d' b, d = d' ++ [b] := by
      rcases List.eq_nil_or_concat d with h | ⟨d', b, h⟩
      · rw [h] at hd; simp at hd
      · exact ⟨d', b, by simpa using h⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hc hd
    set T := Subgroup.closure {a | a ∈ gs ++ [x]}
    set K := Subgroup.closure {a | a ∈ gs}
    have hKT : K ≤ T :=
      Subgroup.closure_mono fun a ha => by simp [Set.mem_setOf_eq] at ha ⊢; exact Or.inl ha
    have hxT : x ∈ T := Subgroup.subset_closure (by simp)
    have hW : vsPW gs c' ∈ K := vsPW_mem (fun g hg => Subgroup.subset_closure hg) c'
    have hV : vsPW gs d' ∈ K := vsPW_mem (fun g hg => Subgroup.subset_closure hg) d'
    rw [vsPW_append _ _ _ _ hc, vsPW_append _ _ _ _ hd] at hcd
    have hxi : x ∉ K ⊔ S := by
      have := hind gs.length (by simp)
      simpa [List.take_left' rfl] using this
    set P := (vsPW gs c')⁻¹ * vsPW gs d'
    have hP : P ∈ T := mul_mem (inv_mem (hKT hW)) (hKT hV)
    have hu : (x ^ a)⁻¹ ∈ T := inv_mem (pow_mem hxT a)
    -- `u P = P u c` with `c = ⁅u, P⁆ ∈ S` central
    set c := ⁅(x ^ a)⁻¹, P⁆
    have hcS : c ∈ S := hQ.comm _ hu _ hP
    have hc1 : c * (P * (x ^ a)⁻¹) = (P * (x ^ a)⁻¹) * c :=
      hQ.sc c hcS _ (mul_mem hP hu)
    have hc2 : c * x ^ b = x ^ b * c := hQ.sc c hcS _ (pow_mem hxT b)
    have e1 : (vsPW gs c' * x ^ a)⁻¹ * (vsPW gs d' * x ^ b) =
        (P * (x ^ b * (x ^ a)⁻¹)) * c := by
      calc (vsPW gs c' * x ^ a)⁻¹ * (vsPW gs d' * x ^ b)
          = ((x ^ a)⁻¹ * P) * x ^ b := by simp only [P]; group
        _ = (c * (P * (x ^ a)⁻¹)) * x ^ b := by rw [vsM_swap P (x ^ a)⁻¹]
        _ = P * (x ^ a)⁻¹ * (c * x ^ b) := by rw [hc1]; group
        _ = P * (x ^ a)⁻¹ * (x ^ b * c) := by rw [hc2]
        _ = P * ((x ^ a)⁻¹ * x ^ b) * c := by group
        _ = (P * (x ^ b * (x ^ a)⁻¹)) * c := by
          rw [((Commute.refl x).pow_pow a b).inv_left.eq]
    rw [e1] at hcd
    have hcd' : P * (x ^ b * (x ^ a)⁻¹) ∈ S := by
      have := mul_mem hcd (inv_mem hcS)
      rwa [mul_inv_cancel_right] at this
    have hab : a = b := by
      by_contra hne
      have hxr : x ^ r ∈ K ⊔ S := Subgroup.mem_sup_right (hQ.pow x hxT)
      have hpart : x ^ b * (x ^ a)⁻¹ ∈ K ⊔ S := by
        have : x ^ b * (x ^ a)⁻¹ = P⁻¹ * (P * (x ^ b * (x ^ a)⁻¹)) := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left (inv_mem (mul_mem (inv_mem hW) hV)))
          (Subgroup.mem_sup_right hcd')
      have har : a < r := hcr a (by simp)
      have hbr : b < r := hdr b (by simp)
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have e2 : x ^ b * (x ^ a)⁻¹ = x ^ (b - a) := by
          have : x ^ b = x ^ (b - a) * x ^ a := by rw [← pow_add, Nat.sub_add_cancel h.le]
          rw [this, mul_inv_cancel_right]
        rw [e2] at hpart
        exact hxi (vsH_mem_of_pow hr (a := b - a) (by omega) (by omega) hpart hxr)
      · have e2 : x ^ b * (x ^ a)⁻¹ = (x ^ (a - b))⁻¹ := by
          have : x ^ a = x ^ (a - b) * x ^ b := by rw [← pow_add, Nat.sub_add_cancel h.le]
          rw [this, mul_inv_rev, mul_inv_cancel_left]
        rw [e2] at hpart
        exact hxi (vsH_mem_of_pow hr (a := a - b) (by omega) (by omega)
          (by simpa using inv_mem hpart) hxr)
    subst hab
    rw [mul_inv_cancel, mul_one] at hcd'
    have := ih (hQ.mono hKT)
      (fun i hi => by
        have := hind i (by simp; omega)
        rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le] at this)
      c' d' hc hd (fun y hy => hcr y (by simp [hy])) (fun y hy => hdr y (by simp [hy])) hcd'
    rw [this]

/-- `r ^ k ≤ |Y : Y ∩ S|` for a family of `k` elements of `Y` that commutes modulo `S` and is
independent modulo `S`. -/
theorem vsH_pow_le_index' {S Y : Subgroup G} {r : ℕ} (hr : r.Prime) {gs : List G}
    (hY : ∀ a ∈ gs, a ∈ Y) (hQ : VsPQuotHyp (Subgroup.closure {a | a ∈ gs}) S r)
    (hind : ∀ (i : ℕ) (hi : i < gs.length), gs[i] ∉ Subgroup.closure {a | a ∈ gs.take i} ⊔ S)
    [Finite (Y ⧸ S.subgroupOf Y)] :
    r ^ gs.length ≤ S.relIndex Y := by
  classical
  have hWY : ∀ e, vsPW gs e ∈ Y := vsPW_mem hY
  let g : (Fin gs.length → Fin r) → Y ⧸ S.subgroupOf Y := fun c =>
    ((⟨vsPW gs (List.ofFn fun i => (c i : ℕ)), hWY _⟩ : Y) : Y ⧸ S.subgroupOf Y)
  have hg : Function.Injective g := by
    intro c d hcd
    simp only [g] at hcd
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hcd
    have := vsH_W_inj' hr gs hQ hind (List.ofFn fun i => (c i : ℕ))
      (List.ofFn fun i => (d i : ℕ)) (List.length_ofFn) (List.length_ofFn)
      (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact (c i).2)
      (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact (d i).2) (by simpa using hcd)
    funext i
    have h2 := congrArg (fun l : List ℕ => l.getD i 0) this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at h2
    exact Fin.ext (by simpa using h2)
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_fun, Nat.card_fin, Nat.card_fin] at this
  unfold Subgroup.relIndex Subgroup.index
  exact this

/-! ### The basis pass -/

section Bas

variable {α : Type*} {f : α → G} {S : Subgroup G} {t : List α → α → Bool}

/-- The test of the basis pass: keep `y` when it is outside `⟨kept⟩ S`. -/
def VsHBTest (f : α → G) (S : Subgroup G) (t : List α → α → Bool) (kept : List α) (y : α) :
    Prop :=
  t kept y = true ↔ f y ∉ Subgroup.closure (f '' {e | e ∈ kept}) ⊔ S

/-- The invariant of the basis pass. -/
structure VsHBInv (f : α → G) (S : Subgroup G) (L kept : List α) : Prop where
  sub : ∀ e ∈ kept, e ∈ L
  indep : ∀ (i : ℕ) (hi : i < kept.length),
    f kept[i] ∉ Subgroup.closure (f '' {e | e ∈ kept.take i}) ⊔ S
  cov : ∀ y ∈ L, f y ∈ Subgroup.closure (f '' {e | e ∈ kept}) ⊔ S

theorem vsHBas_inv (Pr : α → Prop)
    (ht : ∀ kept y, (∀ e ∈ kept, Pr e) → Pr y → VsHBTest f S t kept y) :
    ∀ (L0 L : List α), (∀ y ∈ L0 ++ L, Pr y) → ∀ (kept : List α), VsHBInv f S L0 kept →
      VsHBInv f S (L0 ++ L) (L.foldl (fun kept y => if t kept y then kept ++ [y] else kept) kept) := by
  intro L0 L
  induction L generalizing L0 with
  | nil => intro _ kept h; simpa using h
  | cons y L ih =>
    intro hP kept h
    have := ih (L0 ++ [y]) (by simpa using hP) (if t kept y then kept ++ [y] else kept) ?_
    · simpa using this
    have hPk : ∀ e ∈ kept, Pr e := fun e he => hP e (List.mem_append_left _ (h.sub e he))
    have hPy : Pr y := hP y (by simp)
    have hmono : ∀ T : Set α, ∀ T' : Set α, T ⊆ T' →
        Subgroup.closure (f '' T) ⊔ S ≤ Subgroup.closure (f '' T') ⊔ S := fun T T' hT =>
      sup_le_sup_right (Subgroup.closure_mono (Set.image_mono hT)) S
    by_cases hy : t kept y = true
    · rw [if_pos hy]
      have hn := (ht kept y hPk hPy).1 hy
      refine ⟨fun e he => ?_, fun i hi => ?_, fun z hz => ?_⟩
      · rcases List.mem_append.1 he with he | he
        · exact List.mem_append_left _ (h.sub e he)
        · simp at he; subst he; simp
      · rw [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_or_ge i kept.length with hik | hik
        · rw [List.getElem_append_left hik, List.take_append_of_le_length hik.le]
          exact h.indep i hik
        · have hi' : i = kept.length := by omega
          subst hi'
          rw [List.getElem_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem_singleton, List.take_left' rfl]
          exact hn
      · rcases List.mem_append.1 hz with hz | hz
        · exact hmono _ _ (fun e he => List.mem_append_left _ he) (h.cov z hz)
        · simp at hz; subst hz
          exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨z, by simp, rfl⟩)
    · rw [if_neg hy]
      refine ⟨fun e he => List.mem_append_left _ (h.sub e he), h.indep, fun z hz => ?_⟩
      rcases List.mem_append.1 hz with hz | hz
      · exact h.cov z hz
      · simp at hz; subst hz
        by_contra hn
        exact hy ((ht kept z hPk hPy).2 hn)

/-- **The basis pass.** The kept list is independent modulo `S` and spans `⟨L⟩ S`. -/
theorem vsHBas_spec (Pr : α → Prop)
    (ht : ∀ kept y, (∀ e ∈ kept, Pr e) → Pr y → VsHBTest f S t kept y) (L : List α)
    (hL : ∀ y ∈ L, Pr y) :
    (∀ e ∈ vsHGreedy t L, e ∈ L) ∧
    (∀ (i : ℕ) (hi : i < (vsHGreedy t L).length),
      f (vsHGreedy t L)[i] ∉ Subgroup.closure (f '' {e | e ∈ (vsHGreedy t L).take i}) ⊔ S) ∧
    Subgroup.closure (f '' {e | e ∈ L}) ⊔ S =
      Subgroup.closure (f '' {e | e ∈ vsHGreedy t L}) ⊔ S := by
  have h := vsHBas_inv Pr ht [] L (by simpa using hL) [] ⟨by simp, by simp, by simp⟩
  simp only [List.nil_append] at h
  refine ⟨h.sub, h.indep, le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact h.cov y hy
  · exact le_sup_of_le_left (Subgroup.closure_mono (Set.image_mono fun e he => h.sub e he))

end Bas

end GI.Proved
