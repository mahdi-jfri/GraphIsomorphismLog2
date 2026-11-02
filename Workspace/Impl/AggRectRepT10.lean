import Workspace.Impl.AggRectRepT9

/-!
# Shared facts for the two cases of the program

* `rcR_val_eq`: the output of stage 4 is the value `rcRepVal` of a representation, once the label
  parts and the cells are right and the twist is `none`.
* `rcR_wt_Q2`: the result of stage 2 is small.
* `rcR_gens_length`: there are `q²` listed generators of `P`.
* `rcR_gensV`: the program's list of generators of `P` is `⟨rcRGens W R w₀ w₁⟩`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (Val gens encPerm encGroup encPts PointwiseStab)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- **The output is the value of the representation.** -/
theorem rcR_val_eq {k : ℕ} (e : Ω ≃ Fin k) {W R : Finset (Fin L.q)} (rep : RectRep P₀ S L W R)
    (hs : List (Perm (Fin k))) (Lk : List (List ℕ)) (cellf : ℕ → ℕ)
    (hpi : ∀ h ∈ hs, (List.finRange L.q).map (fun j : Fin L.q =>
        rcRPiN Lk k (fun v => (rcRL fun i => (h i : ℕ)).getD v 0) (j : ℕ)) =
        (List.finRange L.q).map fun j => (rcRPiT e rep.H h j : ℕ))
    (hcell : ∀ i : Fin k, cellf i = rcCellCode (rep.cell (e.symm i)))
    (htw : rep.twist = none) :
    Val.list [.list (hs.map (rcROutV Lk k L.q)), natList ((List.range k).map cellf), .list []] =
      rcRepVal e rep (hs.map fun h => (h, rcRPiT e rep.H h)) := by
  unfold rcRepVal
  rw [htw, List.map_map]
  congr 3
  · refine List.map_congr_left fun h hh => ?_
    simp only [Function.comp_apply, rcROutV, pairV]
    rw [rcR_encPerm (rcRPiT e rep.H h), rcR_range_finRange]
    rw [hpi h hh]
  · rw [rcR_encFun_eq, rcR_range_finRange]
    congr 1
    exact List.map_congr_left fun i _ => hcell i

theorem rcR_gens_length {q : ℕ} (W R : Finset (Fin q)) (w₀ w₁ : Fin q) :
    (rcRGens W R w₀ w₁).length = q * q := by
  simp [rcRGens, List.length_flatMap]

/-- The program's list of generators of `P`. -/
theorem rcR_gensV {q : ℕ} (W R : Finset (Fin q)) (h0 : rcRW0 (rcRInd W) < q)
    (h1 : rcRW1 (rcRInd W) q < q) :
    rcTV (rcRGenLs (rcRInd W) (rcRInd R) (rcRW0 (rcRInd W)) (rcRW1 (rcRInd W) q) q) =
      .list ((rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩).map encPerm) := by
  have h := rcR_genLs_eq W R ⟨_, h0⟩ ⟨_, h1⟩
  unfold rcTV
  rw [show rcRGenLs (rcRInd W) (rcRInd R) (rcRW0 (rcRInd W)) (rcRW1 (rcRInd W) q) q = _ from h,
    List.map_map]
  congr 1
  exact List.map_congr_left fun σ _ => (rcR_encPerm σ).symm

theorem rcR_wt_gl {q M : ℕ} (W R : Finset (Fin q)) (hq : q ≤ M) :
    (rcTV (rcRGenLs (rcRInd W) (rcRInd R) (rcRW0 (rcRInd W)) (rcRW1 (rcRInd W) q) q)).wt ≤
      300 * (M + 1) ^ 5 := by
  by_cases h0 : rcRW0 (rcRInd W) ≤ M
  · by_cases h1 : rcRW1 (rcRInd W) q ≤ M
    · have := rcR_wt_gens (wl := rcRInd W) (rl := rcRInd R) h0 h1 hq
      have hp : (M + 1) ^ 4 ≤ (M + 1) ^ 5 := rcR_pow_le_pow (by omega) (by norm_num)
      unfold rcTV rcRGenLs
      rw [List.map_map]
      exact this.trans (by omega)
    · exfalso
      have : rcRW1 (rcRInd W) q ≤ q := by
        unfold rcRW1
        exact List.findIdx_le_length.trans (by simp)
      omega
  · exfalso
    have : rcRW0 (rcRInd W) ≤ q := by
      unfold rcRW0
      exact List.findIdx_le_length.trans (by rw [rcR_ind_length])
    omega

section Q2

variable {k : ℕ} (e : Ω ≃ Fin k) {x : Ω}

/-- The result of stage 2 is small. -/
theorem rcR_wt_Q2 {W R : Finset (Fin L.q)} {car : Bool} {d₁ d₂ : Fin L.q} {M : ℕ} (hk : k ≤ M)
    (hq : L.q ≤ M) {R2 : Val} (h : rcRQ2 e S L x W R car d₁ d₂ R2) :
    R2.wt ≤ 5000 * (M + 1) ^ 5 := by
  obtain ⟨Lt, rfl, -, hl, hl3⟩ := h
  exact rcR_wt_R2 _ _ (by have := d₁.2; omega) (by have := d₂.2; omega) hk
    (rcR_wt_keys hk hq Lt hl hl3) (rcR_wt_gl W R hq)

end Q2

/-- The four results together are small. -/
theorem rcR_wt_four {M Wb : ℕ} (a b c d : Val) (hM : 1 ≤ M) (ha : a.wt ≤ M)
    (hb : b.wt ≤ 50 * (M + 1) ^ 2) (hc : c.wt ≤ 5000 * (M + 1) ^ 5)
    (hd : d.wt ≤ 500000 * (M + 1) ^ 6) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ Wb) :
    (Val.list [a, b, c, d]).wt ≤ Wb ∧ (Val.list [a, b]).wt ≤ Wb ∧ (Val.list [a, c]).wt ≤ Wb := by
  have h1 : (M + 1) ^ 2 ≤ (M + 1) ^ 6 := rcR_pow_le_pow (by omega) (by norm_num)
  have h2 : (M + 1) ^ 5 ≤ (M + 1) ^ 6 := rcR_pow_le_pow (by omega) (by norm_num)
  have h3 : M + 1 ≤ (M + 1) ^ 6 := (rcR_one_le_sq M).trans h1
  have h4 : 16 * (M + 1) ^ 6 ≤ (M + 1) ^ 10 := by
    have : 2 ^ 4 ≤ (M + 1) ^ 4 := rcR_pow_mono (by omega) 4
    calc 16 * (M + 1) ^ 6 ≤ (M + 1) ^ 4 * (M + 1) ^ 6 := Nat.mul_le_mul_right _ (by simpa using this)
      _ = (M + 1) ^ 10 := by rw [← pow_add]
  have h5 : 1 ≤ (M + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have w4 := wt_list4_le a b c d
  have w2 := wt_list2_le a b
  have w3 := wt_list2_le a c
  refine ⟨by omega, by omega, by omega⟩

end GI.Impl
