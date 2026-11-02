import Workspace.Proved.VsHKeptMath
import Workspace.Proved.VsMIndep

/-!
# Few kept elements

* `vsH_W_inj`: for an independent family of commuting elements with `r`-th powers in `S`
  (`r` prime), different words are different modulo `S`.
* `vsH_rad`: in the hard case, an element of `Ȳ` commuting with all of `Ȳ` lies in `S`
  (minimality), so `|Ȳ : S| ≤ D²` (`vsH_index_le`, by `vsM_indep`).
* `vsH_pow_le_index`: `r ^ k ≤ |Ȳ : S|` for an independent family of `k` elements of `Ȳ`.
-/

namespace GI.Proved

open Module
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem vsPW_append (gs : List G) (e : List ℕ) (x : G) (a : ℕ) (h : e.length = gs.length) :
    vsPW (gs ++ [x]) (e ++ [a]) = vsPW gs e * x ^ a := by
  unfold vsPW
  rw [List.zipWith_append h.symm, List.prod_append]
  simp

/-- An element whose power `x^a` (`0 < a < r`, `r` prime) and `x^r` lie in a subgroup `K`
lies in `K`. -/
theorem vsH_mem_of_pow {K : Subgroup G} {r : ℕ} (hr : r.Prime) {x : G} {a : ℕ} (ha0 : 0 < a)
    (har : a < r) (hxa : x ^ a ∈ K) (hxr : x ^ r ∈ K) : x ∈ K := by
  have hcop : Nat.Coprime a r := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hr).2
    (fun h => absurd (Nat.le_of_dvd ha0 h) (by omega))))
  have key := Nat.gcd_eq_gcd_ab a r
  rw [hcop.gcd_eq_one] at key
  have : x = (x ^ a) ^ (a.gcdA r) * (x ^ r) ^ (a.gcdB r) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← key]
    simp
  rw [this]
  exact mul_mem (zpow_mem hxa _) (zpow_mem hxr _)

/-- **Different words are different modulo `S`.** -/
theorem vsH_W_inj {S : Subgroup G} {r : ℕ} (hr : r.Prime) :
    ∀ (gs : List G), (∀ a ∈ gs, ∀ b ∈ gs, a * b = b * a) → (∀ a ∈ gs, a ^ r ∈ S) →
      (∀ s ∈ S, ∀ a ∈ gs, s * a = a * s) →
      (∀ (i : ℕ) (hi : i < gs.length), gs[i] ∉ Subgroup.closure {a | a ∈ gs.take i} ⊔ S) →
      ∀ c d : List ℕ, c.length = gs.length → d.length = gs.length → (∀ x ∈ c, x < r) →
        (∀ x ∈ d, x < r) → (vsPW gs c)⁻¹ * vsPW gs d ∈ S → c = d := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ _ _ _ c d hc hd _ _ _; simp at hc hd; rw [hc, hd]
  | append_singleton gs x ih =>
    intro hcomm hpow hsc hind c d hc hd hcr hdr hcd
    obtain ⟨c', a, rfl⟩ : ∃ c' a, c = c' ++ [a] := by
      rcases List.eq_nil_or_concat c with h | ⟨c', a, h⟩
      · rw [h] at hc; simp at hc
      · exact ⟨c', a, by simpa using h⟩
    obtain ⟨d', b, rfl⟩ : ∃ d' b, d = d' ++ [b] := by
      rcases List.eq_nil_or_concat d with h | ⟨d', b, h⟩
      · rw [h] at hd; simp at hd
      · exact ⟨d', b, by simpa using h⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hc hd
    have hcomm' : ∀ a ∈ gs, ∀ b ∈ gs, a * b = b * a := fun a ha b hb =>
      hcomm a (by simp [ha]) b (by simp [hb])
    have hT := vsH_closure_comm (T := {a | a ∈ gs ++ [x]}) hcomm
    set K := Subgroup.closure {a | a ∈ gs}
    have hKT : K ≤ Subgroup.closure {a | a ∈ gs ++ [x]} :=
      Subgroup.closure_mono fun a ha => by simp [Set.mem_setOf_eq] at ha ⊢; exact Or.inl ha
    have hxT : x ∈ Subgroup.closure {a | a ∈ gs ++ [x]} := Subgroup.subset_closure (by simp)
    have hW : vsPW gs c' ∈ K := vsPW_mem (fun g hg => Subgroup.subset_closure hg) c'
    have hV : vsPW gs d' ∈ K := vsPW_mem (fun g hg => Subgroup.subset_closure hg) d'
    rw [vsPW_append _ _ _ _ hc, vsPW_append _ _ _ _ hd] at hcd
    have hxi : x ∉ K ⊔ S := by
      have := hind gs.length (by simp)
      simpa [List.take_left' rfl] using this
    -- rearrange: `(W x^a)⁻¹ (V x^b) = (W⁻¹ V) x^b x^(-a)`
    have hcm : ∀ y ∈ Subgroup.closure {a | a ∈ gs ++ [x]}, ∀ z ∈ Subgroup.closure {a | a ∈ gs ++ [x]},
        y * z = z * y := hT
    have hP : (vsPW gs c')⁻¹ * vsPW gs d' ∈ Subgroup.closure {a | a ∈ gs ++ [x]} :=
      mul_mem (inv_mem (hKT hW)) (hKT hV)
    have h1 := hcm _ (inv_mem (pow_mem hxT a)) _ hP
    have e1 : (vsPW gs c' * x ^ a)⁻¹ * (vsPW gs d' * x ^ b) =
        ((vsPW gs c')⁻¹ * vsPW gs d') * (x ^ b * (x ^ a)⁻¹) := by
      calc (vsPW gs c' * x ^ a)⁻¹ * (vsPW gs d' * x ^ b)
          = (x ^ a)⁻¹ * ((vsPW gs c')⁻¹ * vsPW gs d') * x ^ b := by group
        _ = ((vsPW gs c')⁻¹ * vsPW gs d') * (x ^ a)⁻¹ * x ^ b := by rw [h1]
        _ = ((vsPW gs c')⁻¹ * vsPW gs d') * ((x ^ a)⁻¹ * x ^ b) := mul_assoc _ _ _
        _ = ((vsPW gs c')⁻¹ * vsPW gs d') * (x ^ b * (x ^ a)⁻¹) := by
          rw [((Commute.refl x).pow_pow a b).inv_left.eq]
    rw [e1] at hcd
    have hab : a = b := by
      by_contra hne
      have hxr : x ^ r ∈ K ⊔ S := Subgroup.mem_sup_right (hpow x (by simp))
      -- `x^(b-a)` or `x^(a-b)` lies in `K ⊔ S`
      have hpart : x ^ b * (x ^ a)⁻¹ ∈ K ⊔ S := by
        have : x ^ b * (x ^ a)⁻¹ = ((vsPW gs c')⁻¹ * vsPW gs d')⁻¹ *
            (((vsPW gs c')⁻¹ * vsPW gs d') * (x ^ b * (x ^ a)⁻¹)) := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left (inv_mem (mul_mem (inv_mem hW) hV)))
          (Subgroup.mem_sup_right hcd)
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
        exact hxi (vsH_mem_of_pow hr (a := a - b) (by omega) (by omega) (by simpa using inv_mem hpart) hxr)
    subst hab
    rw [mul_inv_cancel, mul_one] at hcd
    have := ih hcomm' (fun a ha => hpow a (by simp [ha])) (fun s hs a ha => hsc s hs a (by simp [ha]))
      (fun i hi => by
        have := hind i (by simp; omega)
        rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le] at this)
      c' d' hc hd (fun y hy => hcr y (by simp [hy])) (fun y hy => hdr y (by simp [hy])) hcd
    rw [this]

/-- `r ^ k ≤ |Y : Y ∩ S|` for an independent family of `k` elements of `Y`. -/
theorem vsH_pow_le_index {S Y : Subgroup G} {r : ℕ} (hr : r.Prime) {gs : List G}
    (hY : ∀ a ∈ gs, a ∈ Y) (hcomm : ∀ a ∈ gs, ∀ b ∈ gs, a * b = b * a) (hpow : ∀ a ∈ gs, a ^ r ∈ S)
    (hsc : ∀ s ∈ S, ∀ a ∈ gs, s * a = a * s)
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
    have := vsH_W_inj hr gs hcomm hpow hsc hind (List.ofFn fun i => (c i : ℕ))
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

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

/-- **The radical of a hard `Y` lies in `S`.** If `x ∈ Y \ S` commuted with all of `Y`, so
would its conjugates, and `S` commutes with `Y`; by minimality `Y ≤ spin x ⊔ S`, so `Y` would
be abelian. -/
theorem vsH_rad {H A Y : Subgroup (End (ZMod p) V)ˣ} {r : ℕ} (h : VsMHard H A Y r) :
    ∀ x ∈ Y, (∀ y ∈ Y, x * y = y * x) → x ∈ vsMScal A := by
  obtain ⟨-, -, -, -, hYn, hYC, -, -, hmin, x0, hx0, y0, hy0, hne⟩ := h
  intro x hx hcen
  by_contra hxS
  set C := Subgroup.centralizer (Y : Set (End (ZMod p) V)ˣ)
  have hspin : vsMSpin H x ≤ C := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Y := hYn _ (inv_mem hg) _ hy
    have e := hcen _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [e]
      _ = g * x * g⁻¹ * y := by group
  have hS : vsMScal A ≤ C := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact vsM_comm_scal (hYC hy) ht
  have hYC' : Y ≤ C := (hmin x hx hxS).trans (sup_le hspin hS)
  exact hne (Subgroup.mem_centralizer_iff.1 (hYC' hy0) x0 hx0)

/-- **`|Y : S| ≤ D²`** in the hard case. -/
theorem vsH_index_le [FiniteDimensional (ZMod p) V] [Nontrivial V]
    {H A Y : Subgroup (End (ZMod p) V)ˣ} {r : ℕ} (h : VsMHard H A Y r) :
    (vsMScal A).relIndex Y ≤ finrank (ZMod p) V ^ 2 :=
  vsM_indep A Y h.2.1.2.2 h.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 (vsH_rad h)

end GI.Proved
