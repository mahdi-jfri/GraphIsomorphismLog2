module

public import Workspace.Impl.TermGlueLabPMatP
public import Workspace.Lang.Lib.LinIntTail

@[expose] public section

/-!
# The coordinate matrix `C(s)` of a conjugation

Step 5 of the label program. For the matrix of `κ_h` (`tmGLP_mat`) the program
needs a matrix `C` whose row `j` is a coordinate vector of `h⁻¹ a_j h`, where `a_j` are the
stored generators of `N`. `tmGLPCMatF mcj tl mec` on `[gens N, [s, s⁻¹]]` (with `s = h⁻¹`)
conjugates the stored list `1, a_1, …, a_t` (Lemma A.19's `supConjF`, mapped at `mcj`), drops
the first entry (`linTail` at `tl`), and maps `linElementCoordinates` over the rest (at `mec`).
The result is `encIntMatrix C` with `TmGLPCoordOf σN (s a_j s⁻¹) (C j)` (`tmGLPCMat_spec`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encInt encIntMatrix encPerm encGroup gens memberInput)

variable {n : ℕ}

/-- **The rows of a matrix from a list of computed coordinate vectors.** -/
theorem tmGLP_rows_of {σN : List (Perm (Fin n))} (f : Perm (Fin n) → Perm (Fin n))
    (hmem : ∀ a ∈ σN, f a ∈ gens σN) {ws : List Val}
    (h : List.Forall₂ (fun x w => ∀ y, x = encPerm y → y ∈ gens σN →
      ∃ z : Fin σN.length → ℤ, TmGLPCoordOf σN y z ∧ w = linVecVal z)
      (σN.map fun a => encPerm (f a)) ws) :
    ∃ C : Matrix (Fin σN.length) (Fin σN.length) ℤ, Val.list ws = encIntMatrix C ∧
      ∀ j : Fin σN.length, TmGLPCoordOf σN (f σN[j.val]) (C j) := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
  simp only [List.length_map] at hlen
  have hz : ∀ j : Fin σN.length, ∃ z : Fin σN.length → ℤ,
      TmGLPCoordOf σN (f σN[j.val]) z ∧ ws[j.val]'(hlen ▸ j.isLt) = linVecVal z := by
    intro j
    have := hget j.val (by simp) (hlen ▸ j.isLt)
    simp only [List.get_eq_getElem, List.getElem_map] at this
    exact this _ rfl (hmem _ (List.getElem_mem _))
  choose C hC hCw using hz
  refine ⟨C, ?_, hC⟩
  change Val.list ws = .list ((List.finRange σN.length).map fun j => linVecVal (C j))
  congr 1
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_finRange]
  exact hCw ⟨i, by omega⟩

/-- **The coordinate matrix of a conjugation**, on `[gens N, [s, s⁻¹]]`. -/
def tmGLPCMatF (mcj tl mec : ℕ) : Expr :=
  .call mec (mk2 (arg 0) (.call tl (.call mcj (mk2 (arg 1) (.get (arg 0) (.nat 1))))))

/-- **One coordinate call**, with the bound `tmGLPBud` at a weight bound `W` of the group. -/
theorem tmGLP_coord_call (hm : GI.Cited.ConstructiveMembership) {P : Program} {ec jm : ℕ}
    (hec : linElementCoordinatesAt P ec jm hm) {Ce De : ℕ}
    (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De) (σN : List (Perm (Fin n)))
    {W : ℕ} (hgW : (encGroup σN).wt ≤ W) (hnW : n ≤ W) (x : Perm (Fin n)) (hx : x ∈ gens σN) :
    FunAll P ec (.list [encGroup σN, encPerm x]) (fun w c =>
      ∃ z : Fin σN.length → ℤ, TmGLPCoordOf σN x z ∧ w = linVecVal z ∧
        c ≤ tmGLPBud Ce De W ∧ w.wt ≤ tmGLPBud Ce De W) := by
  have hsp := linElementCoordinates_spec hm hec ⟨n, σN, x⟩ hx
  refine (FunAll.wt_lt hsp).mono fun w c ⟨⟨⟨prog, z, hw, hp, he⟩, hc⟩, hwc⟩ => ?_
  have hmi : (memberInput ⟨n, σN, x⟩).wt ≤ 20 * (W + 1) ^ 2 := by
    have := wt_list2_le (encGroup σN) (encPerm x)
    have := wt_encPerm_le x
    have := Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2
    have := Nat.le_self_pow (show 2 ≠ 0 by norm_num) (W + 1)
    change (Val.list [encGroup σN, encPerm x]).wt ≤ _
    omega
  have hcB : c ≤ tmGLPBud Ce De W := by
    refine hc.trans ((linElementCoordinatesCost_le hm _).trans ((hEB _).trans ?_))
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  exact ⟨z, ⟨prog, hp, he⟩, hw, hcB, by omega⟩

/-- The weight bound of the conjugated list. -/
def tmGLPCL (W : ℕ) : ℕ := tmGLPColW (4 * (W + 1) ^ 2) (W + 1)

/-- **The cost bound of the coordinate matrix.** -/
def tmGLPCMatC (Ce De W : ℕ) : ℕ :=
  (W + 1) * (10 ^ 5 * (W + 1) ^ 3) + mapK * (W + 2) * (6 * W + tmGLPCL W + 20) +
    linTailCost (tmGLPCL W) + W * tmGLPBud Ce De W +
    mapK * (W + 1) * (2 * (W + tmGLPCL W) + tmGLPColW (tmGLPBud Ce De W) W + 20) +
    100 * (W + tmGLPCL W + 10) + 2 * tmGLPColW (tmGLPBud Ce De W) W

theorem tmGLPColW_mono {W W' r r' : ℕ} (h1 : W ≤ W') (h2 : r ≤ r') :
    tmGLPColW W r ≤ tmGLPColW W' r' := by
  unfold tmGLPColW
  have := Nat.mul_le_mul h2 h1
  omega

/-- A property of all right entries of a `Forall₂`. -/
theorem tmGLP_forall₂_right {α β : Type*} {R : α → β → Prop} {Q : β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (hQ : ∀ a b, R a b → Q b) : ∀ b ∈ l₂, Q b := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hQ _ _ hab
    · exact ih b hb

/-- **The coordinate matrix of a conjugation.** On `[gens N, [s, s⁻¹]]`, when every
`s a s⁻¹` (`a` a stored generator) lies in `N`, the result is `encIntMatrix C` with row `j` a
coordinate vector of `s a_j s⁻¹`. -/
theorem tmGLPCMat_spec (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {f mcj cj cp tl mec ec jm : ℕ} (hf : P.funs[f]? = some (tmGLPCMatF mcj tl mec))
    (hcp : P.HasAt cp (composeFuns cp)) (hcj : P.funs[cj]? = some (supConjF cp))
    (hmcj : P.HasAt mcj (mapFuns mcj cj)) (htl : P.HasAt tl (linTailFuns tl))
    (hmec : P.HasAt mec (mapFuns mec ec)) (hec : linElementCoordinatesAt P ec jm hm)
    {Ce De : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (σN : List (Perm (Fin n))) (s : Perm (Fin n)) (hs : ∀ a ∈ σN, s * a * s⁻¹ ∈ gens σN) :
    FunAll P f (.list [encGroup σN, .list [encPerm s, encPerm s⁻¹]]) (fun w c =>
      ∃ C : Matrix (Fin σN.length) (Fin σN.length) ℤ, w = encIntMatrix C ∧
        (∀ j : Fin σN.length, TmGLPCoordOf σN (s * σN[j.val] * s⁻¹) (C j)) ∧
        c ≤ tmGLPCMatC Ce De (Val.list [encGroup σN, .list [encPerm s, encPerm s⁻¹]]).wt) := by
  set W := (Val.list [encGroup σN, .list [encPerm s, encPerm s⁻¹]]).wt with hW
  set t := σN.length with ht
  have wg : (encGroup σN).wt < W := wt_le_wt_list (by simp)
  have wp : (Val.list [encPerm s, encPerm s⁻¹]).wt < W := wt_le_wt_list (by simp)
  have hnW : n < W := (tmGLP_n_lt_encGroup σN).trans wg
  have htW : t < W := (tmGLP_len_lt_encGroup σN).trans wg
  have wl : (Val.list ((1 :: σN).map encPerm)).wt < (encGroup σN).wt := wt_le_wt_list (by simp)
  have hPW : ∀ y : Perm (Fin n), (encPerm y).wt ≤ 4 * (W + 1) ^ 2 := fun y =>
    (wt_encPerm_le y).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hK : 10 ^ 5 * (n + 1) ^ 3 ≤ 10 ^ 5 * (W + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  apply FunAll.intro hf
  have g0 := Det.arg' (P := P) (vs := [encGroup σN, .list [encPerm s, encPerm s⁻¹]]) (rest := [])
    (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [encGroup σN, .list [encPerm s, encPerm s⁻¹]]) (rest := [])
    (j := 1) rfl
  have dl := Det.get' g0 (Det.nat 1) (vs := [.nat n, .list ((1 :: σN).map encPerm)])
    (v := .list ((1 :: σN).map encPerm)) rfl
  -- stage 1: conjugate the stored list
  set L1 : List Val := (1 :: σN).map fun y => encPerm (s * y * s⁻¹) with hL1
  have hs1 : ∀ x ∈ (1 :: σN).map encPerm, FunAll P cj (.list [.list [encPerm s, encPerm s⁻¹], x])
      (fun w cost => (∀ y, x = encPerm y → w = encPerm (s * y * s⁻¹)) ∧
        cost ≤ 10 ^ 5 * (W + 1) ^ 3) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    refine FunAll.mono (supConj_spec hcp hcj s y) fun w c ⟨hw, hc⟩ => ⟨fun y' hy' => ?_, hc.trans hK⟩
    rw [hw, encPerm_injective hy']
  have wL1 : (Val.list L1).wt ≤ tmGLPCL W := by
    have := tmGLP_wt_list_le (vs := L1) (B := 4 * (W + 1) ^ 2) (by
      intro v hv
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hv
      exact hPW _)
    refine this.trans (tmGLPColW_mono le_rfl ?_)
    simp [hL1]; omega
  have hm1 : FunDet P mcj (.list [.list [encPerm s, encPerm s⁻¹], .list ((1 :: σN).map encPerm)])
      (.list L1) ((t + 1) * (10 ^ 5 * (W + 1) ^ 3) + mapK * (t + 2) * (6 * W + tmGLPCL W + 20)) := by
    refine (map_spec hmcj hs1).mono fun w cost ⟨ws, hw, hws, hc⟩ => ?_
    have e : ws = L1 := forall₂_map_eq (fun y _ w hw => hw y rfl) hws
    subst e
    refine ⟨hw, ?_⟩
    have hsum : (((1 :: σN).map encPerm).map fun _ => 10 ^ 5 * (W + 1) ^ 3).sum =
        (t + 1) * (10 ^ 5 * (W + 1) ^ 3) := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul]; simp [ht]
    have hlen : ((1 :: σN).map encPerm).length + 1 = t + 2 := by simp [ht]
    rw [hsum, hlen] at hc
    have w2 := wt_list2_le (.list [encPerm s, encPerm s⁻¹]) (.list ((1 :: σN).map encPerm))
    rw [hw] at hc
    refine hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    omega
  have dm := Det.call (Det.mk2 g1 dl) hm1
  -- stage 2: drop the first entry
  have hL2 : L1.drop 1 = σN.map fun y => encPerm (s * y * s⁻¹) := by simp [hL1]
  have ht2 := linTail_spec htl L1
  rw [hL2] at ht2
  have dt := Det.call dm ht2
  -- stage 3: the coordinates of each entry
  have wL2 : (Val.list (σN.map fun y => encPerm (s * y * s⁻¹))).wt ≤ tmGLPCL W := by
    rw [← hL2]
    exact (wt_list_sublist (List.drop_sublist 1 L1)).trans wL1
  have hs3 : ∀ x ∈ σN.map (fun y => encPerm (s * y * s⁻¹)),
      FunAll P ec (.list [encGroup σN, x]) (fun w cost =>
        ((∀ y, x = encPerm y → y ∈ gens σN →
          ∃ z : Fin σN.length → ℤ, TmGLPCoordOf σN y z ∧ w = linVecVal z) ∧
          w.wt ≤ tmGLPBud Ce De W) ∧ cost ≤ tmGLPBud Ce De W) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    refine (tmGLP_coord_call hm hec hEB σN wg.le hnW.le _ (hs a ha)).mono
      fun w c ⟨z, hz, hw, hc, hwc⟩ => ⟨⟨fun y hy _ => ?_, hwc⟩, hc⟩
    rw [← encPerm_injective hy]
    exact ⟨z, hz, hw⟩
  have dargs := Det.mk2 g0 dt
  refine EvalAll.call_funAll dargs fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (map_spec hmec hs3).mono ?_
  rintro w cost ⟨ws, rfl, hws, hc⟩
  obtain ⟨C, hC, hCz⟩ := tmGLP_rows_of (fun y => s * y * s⁻¹) hs (hws.imp fun _ _ h => h.1)
  refine ⟨C, hC, hCz, ?_⟩
  -- the cost
  have hwsB : ∀ v ∈ ws, v.wt ≤ tmGLPBud Ce De W := tmGLP_forall₂_right hws fun _ _ h => h.2
  have wO : (Val.list ws).wt ≤ tmGLPColW (tmGLPBud Ce De W) W := by
    refine (tmGLP_wt_list_le hwsB).trans (tmGLPColW_mono le_rfl ?_)
    have := hws.length_eq
    simp only [List.length_map] at this
    omega
  have hsum : ((σN.map fun y => encPerm (s * y * s⁻¹)).map fun _ => tmGLPBud Ce De W).sum =
      t * tmGLPBud Ce De W := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]; simp [ht]
  have hlen : (σN.map fun y => encPerm (s * y * s⁻¹)).length + 1 = t + 1 := by simp [ht]
  rw [hsum, hlen] at hc
  have w3 := wt_list2_le (encGroup σN) (.list (σN.map fun y => encPerm (s * y * s⁻¹)))
  have w4 := wt_list2_le (.list [encPerm s, encPerm s⁻¹]) (.list ((1 :: σN).map encPerm))
  have hT := linTailCost_mono wL1
  have hA : t * tmGLPBud Ce De W ≤ W * tmGLPBud Ce De W := Nat.mul_le_mul_right _ htW.le
  have hB : (t + 1) * (10 ^ 5 * (W + 1) ^ 3) ≤ (W + 1) * (10 ^ 5 * (W + 1) ^ 3) :=
    Nat.mul_le_mul_right _ (by omega)
  have hC1 : mapK * (t + 2) * (6 * W + tmGLPCL W + 20) ≤
      mapK * (W + 2) * (6 * W + tmGLPCL W + 20) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hD : mapK * (t + 1) * ((Val.list [encGroup σN,
      .list (σN.map fun y => encPerm (s * y * s⁻¹))]).wt + (Val.list ws).wt + 1) ≤
      mapK * (W + 1) * (2 * (W + tmGLPCL W) + tmGLPColW (tmGLPBud Ce De W) W + 20) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  unfold tmGLPCMatC
  omega

end GI.Impl
