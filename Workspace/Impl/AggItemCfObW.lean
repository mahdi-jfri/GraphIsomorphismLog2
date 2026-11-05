module

public import Workspace.Impl.AggItemCfSpec

@[expose] public section

/-!
# Cases 2b and 3: the weight of the object values

An object of Cases 2b/3 is a colored partition, a pair configuration, or nothing. Its value
`itCfOutV o` lists `q` rows of `q` numbers, so its weight is polynomial in `q` and in a bound
`B` on its colors (`itCfOutV_wt_le`, with the bound `itCfObjB q B`).

* Case 2b (`itCf_objW_twoB`): the object `orbitalOut (fun _ => d) H t` reads its colors from the
  binary values `d`, which the cache keeps below `2q²` (`ItCfCache`).
* Case 3 (`itCf_objW_three`): the object `designOut c t` reads its colors from `c`, and its
  dominant color is a color of `c`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val skel₁ skel₂)

variable {q : ℕ}

/-- The weight bound of an object value with colors at most `B`. -/
def itCfObjB (q B : ℕ) : ℕ := 20 * (q + 1) ^ 2 * (B + 5)

theorem itCf_wt_rows_le {f : Fin q → Fin q → ℕ} {B : ℕ} (hf : ∀ a b, f a b ≤ B) :
    (Val.list ((List.finRange q).map fun a => encFun (f a))).wt ≤
      q * (2 * (q * (2 * B + 5) + 4) + 1) + 4 := by
  have := wt_list_map_le (List.finRange q) (fun a => encFun (f a))
    (W := q * (2 * B + 5) + 4) fun a _ => wt_encFun_le _ (hf a)
  simpa using this

/-- **The weight of an object value** with colors at most `B`. -/
theorem itCfOutV_wt_le {o : CfgOut q} {B : ℕ} (h : itCfColsLe o B) :
    (itCfOutV o).wt ≤ itCfObjB q B := by
  unfold itCfObjB
  have hq2 : (q + 1) ^ 2 = q * q + 2 * q + 1 := by ring
  cases o with
  | none =>
    have := wt_list1_le (.nat 0)
    have := wt_nat_le 0
    simp only [itCfOutV]
    nlinarith
  | part z =>
    have hb : (itCfBlkV z).wt ≤ q * (2 * (q * (2 * 1 + 5) + 4) + 1) + 4 := by
      unfold itCfBlkV
      exact itCf_wt_rows_le (B := 1) fun a b => by split_ifs <;> omega
    have hc : (encFun z.col).wt ≤ q * (2 * B + 5) + 4 := wt_encFun_le _ h
    have h3 := wt_list3_le (.nat 1) (itCfBlkV z) (encFun z.col)
    have := wt_nat_le 1
    simp only [itCfOutV]
    nlinarith
  | pair X x₀ =>
    obtain ⟨hcol, hj⟩ := h
    have hr : (rcColVal X).wt ≤ q * (2 * (q * (2 * B + 5) + 4) + 1) + 4 := by
      unfold rcColVal
      exact itCf_wt_rows_le hcol
    have h3 := wt_list3_le (rcColVal X) (.nat X.j) (.nat x₀)
    have := wt_nat_le X.j
    have := wt_nat_le (x₀ : ℕ)
    have := x₀.isLt
    have h2 := wt_list2_le (.nat 2) (rcCertIn X x₀)
    have := wt_nat_le 2
    simp only [itCfOutV]
    unfold rcCertIn at h2 ⊢
    nlinarith

/-- **The object of Case 2b has the colors of the refined coloring.** -/
theorem itCf_orbitalOut_cols (R : Refiner2 q) (H : Subgroup (Perm (Fin q))) {ℓ : ℕ}
    (t : Fin ℓ → Fin q) {B : ℕ} (hR : ∀ z, R (orbColOut H t) z ≤ B) :
    itCfColsLe (orbitalOut R H t) B := by
  unfold orbitalOut orbitalAt
  split_ifs with hd
  · have e : orbColOut H t = orbCol H (domSet H \ ancSet t (transDeg H (domSet H)))
        (ancSet t (transDeg H (domSet H))) (ancList t (transDeg H (domSet H)))
        (t ⟨transDeg H (domSet H) - 1, by omega⟩)
        (t ⟨transDeg H (domSet H), hd⟩) := by
      unfold orbColOut orbColAt
      rw [dif_pos hd]
    rw [e] at hR
    exact ⟨fun a b => hR _, hR _⟩
  · trivial

/-- **The weight of the objects of Case 2b**: binary values below `2q²`. -/
theorem itCf_objW_twoB (d : (Fin 2 → Fin q) → ℕ) (hd : ∀ z, d z < 2 * q ^ 2)
    (H : Subgroup (Perm (Fin q))) {ℓ : ℕ} (t : Fin ℓ → Fin q) :
    (itCfOutV (orbitalOut (fun _ => d) H t)).wt ≤ itCfObjB q (2 * q ^ 2) :=
  itCfOutV_wt_le (itCf_orbitalOut_cols _ H t fun z => (hd z).le)

/-- A dominant color of `c` (for `q ≠ 0`) is a color of `c`. -/
theorem itCf_dom_le {κ m : ℕ} (c : (Fin κ → Fin q) → ℕ) (x : Fin m → Fin q) (j : ℕ) (hq : q ≠ 0)
    (h : Dominant c x j) {B : ℕ} (hc : ∀ z, c z ≤ B) : j ≤ B := by
  classical
  unfold Dominant vcard at h
  have hpos : 0 < (Finset.univ.filter fun z => skel₁ c x z = j).card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_filter] at hz
  rw [← hz.2]
  exact hc _

/-- **The object of Case 3 has the colors of `c`.** The dominant color is a color of `c`: its
class has at least `3q/4` points, so it is nonempty unless `q = 0`, and for `q = 0` the least
dominant color is `0`. -/
theorem itCf_designOut_cols {κ : ℕ} (c : (Fin κ → Fin q) → ℕ) {ℓ : ℕ} (t : Fin ℓ → Fin q)
    {B : ℕ} (hc : ∀ z, c z ≤ B) : itCfColsLe (designOut c t) B := by
  classical
  unfold designOut
  split_ifs with hkl hex
  · unfold designAt
    split_ifs with hb hd
    · exact fun a => hc _
    · refine ⟨fun a b => hc _, ?_⟩
      show Nat.find hd ≤ B
      by_cases hq : q = 0
      · subst hq
        have h0 : Dominant c (preT t (by omega) (Nat.find hex)) 0 := by
          unfold Dominant; omega
        have := Nat.find_min' hd h0
        omega
      · exact itCf_dom_le c _ _ hq (Nat.find_spec hd) hc
    · trivial
  · trivial
  · trivial

/-- **The weight of the objects of Case 3**: colors at most `B`. -/
theorem itCf_objW_three {κ : ℕ} (c : (Fin κ → Fin q) → ℕ) {ℓ : ℕ} (t : Fin ℓ → Fin q)
    {B : ℕ} (hc : ∀ z, c z ≤ B) : (itCfOutV (designOut c t)).wt ≤ itCfObjB q B :=
  itCfOutV_wt_le (itCf_designOut_cols c t hc)

/-- **The weight of the objects of a branch**, from `ItCfObjOf`. -/
theorem itCfObjOf_wt {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {K : ItSCtx k S L} {b : Fin (P₀.κ + 1) → Fin L.q} {oX oY : CfgOut L.q}
    (h : ItCfObjOf K b oX oY) :
    (itCfOutV oX).wt ≤ itCfObjB L.q (2 * L.q ^ P₀.κ) ∧
      (itCfOutV oY).wt ≤ itCfObjB L.q (2 * L.q ^ P₀.κ) := by
  obtain ⟨-, -, -, hX, hY⟩ := h
  exact ⟨itCfOutV_wt_le hX, itCfOutV_wt_le hY⟩

end GI.Impl
