module

public import Workspace.Impl.AggCertMvRound
public import Workspace.Impl.GenCls

@[expose] public section

/-!
# The move program: the window indicator and the points left outside

The increment `V_t` reaches the move program as the list `incP` of the positions of its points.
Two small programs turn it into what the next steps need.

* `cpIndF` (at `b + 11`) gives the indicator of `V_t` on the `k` points of `Ω`, the form that
  the window colors (`wp_spec`) and the window value read (`cp_ind_spec`).
* `cpDiffTestF` (at `b + 8`) tests whether a position is not in `incP`. Filtering the list of
  outside points with it gives the outside points of the next window (`cp_diff_spec`).

Both count how often a position occurs in `incP`; since `incP` has no repeats, the count is one
for the points of `V_t` and zero for the others (`cp_count_pos`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

section Ind

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {q : ℕ}

/-- The positions of a list of points, as numbers. -/
def cpPosN (e : Ω ≃ Fin k) (q : ℕ) (l : List S.dom) : List ℕ :=
  l.map fun v => (domPos e q v : ℕ)

theorem encPts_posN (l : List S.dom) : encPts (l.map (domPos e q)) = natList (cpPosN e q l) := by
  rw [encPts_map_posOf]; simp [cpPosN, natList]

theorem cpPosN_nodup {l : List S.dom} (h : l.Nodup) : (cpPosN e q l).Nodup :=
  h.map fun u v huv => posOf_injective e q (Fin.ext huv)

theorem mem_cpPosN_iff (l : List S.dom) (v : S.dom) :
    (domPos e q v : ℕ) ∈ cpPosN e q l ↔ v ∈ l := by
  simp only [cpPosN, List.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    rwa [posOf_injective e q (Fin.ext huv)] at hu
  · exact fun hv => ⟨v, hv, rfl⟩

open Classical in
/-- **How often a position occurs** in the positions of a list without repeats. -/
theorem cp_count_pos {l : List S.dom} (h : l.Nodup) (i : Fin k) :
    (cpPosN e q l).count (i : ℕ) = if e.symm i ∈ Subtype.val '' {v | v ∈ l} then 1 else 0 := by
  classical
  have hnd := cpPosN_nodup (e := e) (q := q) h
  have hmem : (i : ℕ) ∈ cpPosN e q l ↔ e.symm i ∈ Subtype.val '' {v | v ∈ l} := by
    simp only [cpPosN, List.mem_map, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, hui⟩
      refine ⟨u, hu, ?_⟩
      have : e u = i := Fin.ext (by simpa [domPos] using hui)
      rw [← this, Equiv.symm_apply_apply]
    · rintro ⟨u, hu, hui⟩
      refine ⟨u, hu, ?_⟩
      simp [domPos, hui]
  split_ifs with hi
  · exact List.count_eq_one_of_mem hnd (hmem.mpr hi)
  · exact List.count_eq_zero_of_not_mem (fun h' => hi (hmem.mp h'))

theorem cp_posN_le {l : List S.dom} : ∀ x ∈ cpPosN e q l, x ≤ k + q := by
  intro x hx
  simp only [cpPosN, List.mem_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  exact (domPos e q u).isLt.le

theorem cp_posN_length (l : List S.dom) : (cpPosN e q l).length = l.length := by
  simp [cpPosN]

end Ind

section Prog

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {q : ℕ}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- The count step of the indicator, on `[incP, i]`. -/
theorem cp_indStep {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    {l : List S.dom} (hl : l.length ≤ k) {i : ℕ} (hi : i ≤ k) :
    FunDet Pg (b + 7) (.list [natList (cpPosN e q l), .nat i]) (.nat ((cpPosN e q l).count i))
      (2 * (2 * (Val.list [natList (cpPosN e q l), .nat i]).wt + 6) +
        2 * (Val.list [.nat i, natList (cpPosN e q l)]).wt + 7 + countK * (k + q + 1) ^ 3 +
        (Val.nat ((cpPosN e q l).count i)).wt + 1) := by
  refine FunDet.intro hat.indStep ?_
  unfold cpIndStepF
  refine (Det.call (Det.mk2 (Det.arg' (rest := []) (j := 1) rfl) (Det.arg' (rest := []) (j := 0)
    rfl)) (count_spec hat.cnt (B := k + q) cp_posN_le (by omega)
      (by rw [cp_posN_length]; omega))).mono ?_
  omega

open Classical in
/-- **The window indicator.** For a list `l` of points without repeats, `cpIndF` gives the
indicator of its points. -/
theorem cp_ind_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    {l : List S.dom} (hnd : l.Nodup) (hl : l.length ≤ k) {W : ℕ}
    (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg (b + 11) (.list [.nat k, encPts (l.map (domPos e q))]) W (cpG hst hpre hm W)
      (fun w => DomVal e w (Subtype.val '' {v | v ∈ l})) := by
  rw [encPts_posN]
  set P := cpPosN e q l with hP
  set f : Fin k → ℕ := fun i => if e.symm i ∈ Subtype.val '' {v | v ∈ l} then 1 else 0 with hf
  have hout : Val.list ((List.range k).map fun i => Val.nat (P.count i)) = encFun f := by
    unfold encFun
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, hf, hP]
    rw [cp_count_pos hnd i]
  have hPl : P.length ≤ k := by rw [hP, cp_posN_length]; exact hl
  have hPw : (natList P).wt ≤ k * (2 * (k + q) + 5) + 4 := by
    have := wt_natList_le (B := k + q) (xs := P) cp_posN_le
    have := Nat.mul_le_mul_right (2 * (k + q) + 5) hPl
    omega
  have hfw : (encFun f).wt ≤ k * (2 * 1 + 5) + 4 :=
    wt_encFun_le f fun i => by simp only [hf]; split_ifs <;> omega
  have hk2 : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk12 : k + q + 1 ≤ (k + q + 1) ^ 12 := Nat.le_self_pow (by omega) _
  have hsq : k * (2 * (k + q) + 5) ≤ 5 * (k + q + 1) ^ 2 := by
    have : k * (2 * (k + q) + 5) ≤ (k + q + 1) * (5 * (k + q + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e1 : (k + q + 1) * (5 * (k + q + 1)) = 5 * (k + q + 1) ^ 2 := by ring
    omega
  -- the steps of the map
  have hstep : ∀ i ∈ List.range k, FunDet Pg (b + 7) (.list [natList P, .nat i])
      (.nat (P.count i)) (100 * (k + q + 1) ^ 2 + countK * (k + q + 1) ^ 3 + 200) := by
    intro i hi
    have hi' : i ≤ k := (List.mem_range.mp hi).le
    have h7 := cp_indStep (e := e) (q := q) hat hl hi'
    rw [← hP] at h7
    refine h7.mono ?_
    have := wt_list2_le (natList P) (.nat i)
    have := wt_list2_le (.nat i) (natList P)
    have := wt_nat_le i
    have := wt_nat_le (P.count i)
    have : P.count i ≤ k := (List.count_le_length).trans hPl
    have : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hmap := mapList_spec hat.mapInd (List.range k) Val.nat (fun i => Val.nat (P.count i))
    (c := natList P) (fun a _ a' _ h => by cases h; rfl) hstep
  have hrange := GI.Impl.range_det hat.range k
  rw [hout] at hmap
  have hbody := Det.letE (P := Pg) (env := [.list [.nat k, natList P]])
    (Det.call (Det.arg' (rest := []) (j := 0) rfl) hrange)
    (Det.call (Det.mk2 (Det.arg' (rest := [natList (List.range k)]) (j := 1) rfl)
      (Det.var' (i := 1) rfl)) hmap)
  refine CpFB.det (FunDet.intro hat.ind hbody) ?_ (by omega) rfl
  -- the cost
  have hrw : (natList (List.range k)).wt ≤ k * (2 * k + 5) + 4 := by
    have := wt_natList_le (B := k) (xs := List.range k) fun x hx => (List.mem_range.mp hx).le
    simpa using this
  have hkk : k * (2 * k + 5) ≤ 5 * (k + q + 1) ^ 2 := by
    have : k * (2 * k + 5) ≤ k * (2 * (k + q) + 5) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hmw : (Val.list [natList P, .list ((List.range k).map Val.nat)]).wt ≤
      2 * (k * (2 * (k + q) + 5) + 4 + (k * (2 * k + 5) + 4)) + 6 := by
    have := wt_list2_le (natList P) (.list ((List.range k).map Val.nat))
    have e1 : Val.list ((List.range k).map Val.nat) = natList (List.range k) := rfl
    rw [e1] at this ⊢
    omega
  have hw1 := wt_list2_le (.nat k) (natList P)
  have := wt_nat_le k
  have hc3 : countK * (k + q + 1) ^ 3 ≤ countK * (k + q + 1) ^ 12 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hr3 : 7000 * (k + 1) ^ 3 ≤ 7000 * (k + q + 1) ^ 12 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 3).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hlen : (List.range k).length * (100 * (k + q + 1) ^ 2 + countK * (k + q + 1) ^ 3 + 200) ≤
      (k + q + 1) ^ 12 * (100 * (k + q + 1) ^ 12 + countK * (k + q + 1) ^ 12 + 200) := by
    rw [List.length_range]
    exact Nat.mul_le_mul (by have : k + q + 1 ≤ (k + q + 1) ^ 12 := Nat.le_self_pow (by omega) _
                             omega) (by omega)
  have hmk : mapK * ((List.range k).length + 1) *
      ((Val.list [natList P, .list ((List.range k).map Val.nat)]).wt + (encFun f).wt + 1) ≤
      mapK * (W + 1) * (W + 1) := by
    rw [List.length_range]
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    omega
  -- everything is within `10²⁵ W²⁴`
  have hC1 : countK = 100000 := rfl
  have hM1 : mapK = 1000 := rfl
  rw [hC1] at hc3 hlen
  rw [hM1] at hmk
  have hX : (k + q + 1) ^ 12 * (100 * (k + q + 1) ^ 12 + 100000 * (k + q + 1) ^ 12 + 200) ≤
      (W + 1) * (100100 * (W + 1) + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : (W + 1) * (100100 * (W + 1) + 200) = 100100 * (W + 1) ^ 2 + 200 * (W + 1) := by ring
  have e3 : 1000 * (W + 1) * (W + 1) = 1000 * (W + 1) ^ 2 := by ring
  have hp := cp_poly_le (W := W) (K := 102000) (d := 2) (by norm_num) (by norm_num) (by omega)
  have : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have := cpG_poly hst hpre hm (W := W)
  have : (Val.nat k).wt ≤ k + 2 := wt_nat_le k
  have : (Val.list [natList P, natList (List.range k)]).wt =
      (Val.list [natList P, .list ((List.range k).map Val.nat)]).wt := rfl
  rw [hC1, hM1]
  omega

end Prog

end GI.Impl
