module

public import Workspace.Impl.SCosBig1

@[expose] public section

/-!
# Function 5 (`bigF`), steps 1–5

On the problem `[encGroup gs, encPerm (nintSum x), scosInd Φ]` the first five `let`s compute:

1. the positions `P` of `D = scosPhiF Φ` (`domList_spec`);
2. the table of positions (`posTab_spec`);
3. the restrictions of the generators `1 :: gs` (`restrList_spec`), the list `scosBigHs`;
4. the group value of the restricted group (`mkGroup_spec`);
5. the minimal block labels `lab` of the restricted group (primitive `2`).

Each step costs at most `scosBigD n c` (the primitive step also its bound).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- `a ≤ A S^j` with `A ≤ 10^40` and `j ≤ 7` gives `a ≤ scosBigD n c`. -/
theorem scosBigD_of {c a A j : ℕ} (h : a ≤ A * scosBigS n c ^ j) (hA : A ≤ 10 ^ 40)
    (hj : j ≤ 7) : a ≤ scosBigD n c := by
  have hS := (scosBigS_facts n c).2.2.2.2
  have h1 : scosBigS n c ^ j ≤ scosBigS n c ^ 7 := Nat.pow_le_pow_right hS hj
  have h2 : A * scosBigS n c ^ j ≤ 10 ^ 40 * scosBigS n c ^ 7 := Nat.mul_le_mul hA h1
  have h3 : 10 ^ 40 * scosBigS n c ^ 7 ≤ scosBigD n c := by
    unfold scosBigD
    rw [Nat.mul_right_comm]
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The same with a factor `c + 1`. -/
theorem scosBigD_of' {c a A j : ℕ} (h : a ≤ (c + 1) * (A * scosBigS n c ^ j))
    (hA : A ≤ 10 ^ 40) (hj : j ≤ 7) : a ≤ scosBigD n c := by
  have hS := (scosBigS_facts n c).2.2.2.2
  have h1 : scosBigS n c ^ j ≤ scosBigS n c ^ 7 := Nat.pow_le_pow_right hS hj
  have h2 : A * scosBigS n c ^ j ≤ 10 ^ 40 * scosBigS n c ^ 7 := Nat.mul_le_mul hA h1
  have h3 : (c + 1) * (10 ^ 40 * scosBigS n c ^ 7) = scosBigD n c := by unfold scosBigD; ring
  have h4 := Nat.mul_le_mul_left (c + 1) h2
  omega

/-- The restricted generators. -/
noncomputable def scosBigHs (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (hinv : ScosInv 𝒢 Φ)
    (gs : List (Perm (Fin (n + n)))) : List (Perm (Fin (scosBMk Φ))) :=
  (1 :: gs).map (restrP (Equiv.refl (Fin (n + n))) (𝒢.map nintSum) (scosPhiF Φ)
    (scosBM_invariant 𝒢 Φ hinv))

theorem length_scosBigHs (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (hinv : ScosInv 𝒢 Φ)
    (gs : List (Perm (Fin (n + n)))) : (scosBigHs 𝒢 Φ hinv gs).length = gs.length + 1 := by
  simp [scosBigHs]

/-! ### Weights -/

theorem scosBig_wt0 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (Φ : Finset (Fin n))
    (hw : (encGroup gs).wt ≤ scosW n) :
    (Val.list [encGroup gs, encPerm (nintSum x), scosInd Φ]).wt ≤ 1000 * (n + n + 1) ^ 6 := by
  have h1 := wt_list3_le (encGroup gs) (encPerm (nintSum x)) (scosInd Φ)
  have h2 := scosPaste_wt_perm (nintSum x)
  have h3 := scosPaste_wt_ind Φ
  have := (scosPaste_Q n).1
  unfold scosW at hw
  omega

theorem scosBig_gsl (gs : List (Perm (Fin (n + n)))) (hw : (encGroup gs).wt ≤ scosW n) :
    gs.length + 2 ≤ 320 * (n + n + 1) ^ 6 := by
  have := scosBig_length_lt gs
  unfold scosW at hw
  omega

theorem scosBig_kQ (Φ : Finset (Fin n)) :
    (scosBMk Φ + 1) ^ 2 ≤ (n + n + 1) ^ 6 ∧ scosBMk Φ + 1 ≤ (n + n + 1) ^ 6 := by
  have hk := scosBMk_le Φ
  have hQ := scosPaste_Q n
  have : (scosBMk Φ + 1) ^ 2 ≤ (n + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  constructor <;> omega

/-- The list of the restricted generators, as values. -/
theorem scosBig_wt3 (c : ℕ) {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    {gs : List (Perm (Fin (n + n)))} (hw : (encGroup gs).wt ≤ scosW n) :
    (Val.list ((scosBigHs 𝒢 Φ hinv gs).map encPerm)).wt ≤ 3000 * scosBigS n c ∧
    (encGroup (scosBigHs 𝒢 Φ hinv gs)).wt ≤ 10000 * scosBigS n c := by
  have hk := scosBig_kQ Φ
  have hgs := scosBig_gsl gs hw
  have hS := scosBigS_facts n c
  have hQ := scosPaste_Q n
  have hp : ∀ σ : Perm (Fin (scosBMk Φ)), (encPerm σ).wt ≤ 4 * (n + n + 1) ^ 6 := fun σ =>
    (wt_encPerm_le σ).trans (by omega)
  have hl1 := GI.Lang.wt_list_le_of ((scosBigHs 𝒢 Φ hinv gs).map encPerm)
    (c := 4 * (n + n + 1) ^ 6) (by
      intro v hv
      obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv
      exact hp σ)
  have hl2 := GI.Lang.wt_list_le_of ((1 :: scosBigHs 𝒢 Φ hinv gs).map encPerm)
    (c := 4 * (n + n + 1) ^ 6) (by
      intro v hv
      obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv
      exact hp σ)
  simp only [List.length_map, List.length_cons, length_scosBigHs] at hl1 hl2
  have hm1 : (gs.length + 1) * (2 * (4 * (n + n + 1) ^ 6) + 1) ≤
      2880 * ((n + n + 1) ^ 6 * (n + n + 1) ^ 6) := by
    calc (gs.length + 1) * (2 * (4 * (n + n + 1) ^ 6) + 1) ≤
        (320 * (n + n + 1) ^ 6) * (9 * (n + n + 1) ^ 6) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2880 * ((n + n + 1) ^ 6 * (n + n + 1) ^ 6) := by ring
  have hm2 : (gs.length + 1 + 1) * (2 * (4 * (n + n + 1) ^ 6) + 1) ≤
      2880 * ((n + n + 1) ^ 6 * (n + n + 1) ^ 6) := by
    calc (gs.length + 1 + 1) * (2 * (4 * (n + n + 1) ^ 6) + 1) ≤
        (320 * (n + n + 1) ^ 6) * (9 * (n + n + 1) ^ 6) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2880 * ((n + n + 1) ^ 6 * (n + n + 1) ^ 6) := by ring
  have hg := wt_list2_le (.nat (scosBMk Φ)) (.list ((1 :: scosBigHs 𝒢 Φ hinv gs).map encPerm))
  have hn := wt_nat_le (scosBMk Φ)
  have e : encGroup (scosBigHs 𝒢 Φ hinv gs) =
      .list [.nat (scosBMk Φ), .list ((1 :: scosBigHs 𝒢 Φ hinv gs).map encPerm)] := rfl
  rw [e]
  generalize (n + n + 1) ^ 6 * (n + n + 1) ^ 6 = QQ at *
  generalize (n + n + 1) ^ 6 = Q at *
  constructor <;> omega

section Prog

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-! ### Step 1: the positions -/

theorem scosBig_step1 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (Φ : Finset (Fin n))
    (hw : (encGroup gs).wt ≤ scosW n) :
    Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]] (.call 125 (arg 2))
      (natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))) (scosBigD n c) := by
  have d := Det.call (Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ])
    (rest := []) (j := 2) rfl) (domList_spec scos_domAt (Equiv.refl (Fin (n + n))) (scosPhiF Φ))
  refine d.mono (scosBigD_of (A := 100000000) (j := 1) ?_ (by norm_num) (by norm_num))
  have h0 := scosBig_wt0 gs x Φ hw
  have h1 := wt_domNat_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  have hQ := scosPaste_Q n
  have hS := (scosBigS_facts n c).1
  have e : domListK = 1000000 := rfl
  rw [e, pow_one]
  generalize (Val.list [encGroup gs, encPerm (nintSum x), scosInd Φ]).wt = A at *
  omega

/-! ### Step 2: the table of positions -/

theorem scosBig_step2 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (Φ : Finset (Fin n))
    (hw : (encGroup gs).wt ≤ scosW n) :
    Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))]
      (.call 133 (mk2 (.var 1) (.length (arg 2))))
      (posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) (scosBigD n c) := by
  have da := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ])
    (rest := [natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))]) (j := 2)
    (v := .list ((List.finRange (n + n)).map fun i =>
      .nat (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) i))) rfl
  have dl := Det.length da
  simp only [List.length_map, List.length_finRange] at dl
  have dv := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))]) (i := 1)
    (v := natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))) rfl
  have d := Det.call (Det.mk2 dv dl)
    (posTab_spec scos_domAt (Equiv.refl (Fin (n + n))) (scosPhiF Φ))
  refine d.mono (scosBigD_of (A := 1000000000) (j := 1) ?_ (by norm_num) (by norm_num))
  have h0 := scosBig_wt0 gs x Φ hw
  have h1 := wt_domNat_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  have h2 := wt_posVal_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  have h3 := wt_list2_le (natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))) (.nat (n + n))
  have h4 := wt_nat_le (n + n)
  have hQ := scosPaste_Q n
  have hS := (scosBigS_facts n c).1
  have e : posTabK = 10000000 := rfl
  rw [e, pow_one]
  generalize (Val.list [encGroup gs, encPerm (nintSum x), scosInd Φ]).wt = A at *
  omega

/-! ### Step 3: the restricted generators -/

theorem scosBig_memG {𝒢 : Subgroup (ScosPair n)} {gs : List (Perm (Fin (n + n)))}
    (hgs : gens gs = 𝒢.map nintSum) :
    ∀ g ∈ (1 :: gs), g ∈ groupFin (Equiv.refl (Fin (n + n))) (𝒢.map nintSum) := by
  intro g hg
  rw [scosBM_groupFin, ← hgs]
  rcases List.mem_cons.1 hg with rfl | hg
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure hg

/-- The restricted generators generate the restricted group. -/
theorem scosBig_gensHs {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    {gs : List (Perm (Fin (n + n)))} (hgs : gens gs = 𝒢.map nintSum) :
    gens (scosBigHs 𝒢 Φ hinv gs) = (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range := by
  rw [range_restrK]
  refine gens_restrP _ _ _ _ ?_
  rw [scosBig_gens_one, hgs, scosBM_groupFin]

theorem scosBig_step3 {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    {gs : List (Perm (Fin (n + n)))} (x : ScosPair n) (hgs : gens gs = 𝒢.map nintSum)
    (hw : (encGroup gs).wt ≤ scosW n) :
    Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
        posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)]
      (.call 147 (mk2 (mk2 (.var 1) (.var 2)) (.get (arg 0) (.nat 1))))
      (.list ((scosBigHs 𝒢 Φ hinv gs).map encPerm)) (scosBigD n c) := by
  have dv1 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)]) (i := 1)
    (v := natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))) rfl
  have dv2 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)]) (i := 2)
    (v := posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) rfl
  have da := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ])
    (rest := [natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
      posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)]) (j := 0) (v := encGroup gs) rfl
  have dg := Det.get' da (Det.nat 1) (v := .list ((1 :: gs).map encPerm))
    (show [Val.nat (n + n), Val.list ((1 :: gs).map encPerm)][1]? = some _ from rfl)
  have hr := restrList_spec (Equiv.refl (Fin (n + n))) (𝒢.map nintSum) (scosPhiF Φ)
    (scosBM_invariant 𝒢 Φ hinv) (scos_domAt (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (scosBig_memG hgs)
  have d := Det.call (Det.mk2 (Det.mk2 dv1 dv2) dg) hr
  have e : (1 :: gs).map (fun g => encPerm (restrP (Equiv.refl (Fin (n + n))) (𝒢.map nintSum)
      (scosPhiF Φ) (scosBM_invariant 𝒢 Φ hinv) g)) = (scosBigHs 𝒢 Φ hinv gs).map encPerm := by
    simp [scosBigHs, List.map_map, Function.comp_def]
  rw [e] at d
  refine d.mono (scosBigD_of (A := 10 ^ 40) (j := 7) ?_ le_rfl le_rfl)
  have h0 := scosBig_wt0 gs x Φ hw
  have h1 := wt_domNat_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  have h2 := wt_posVal_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  have h3 := wt_list2_le (natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)))
    (posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ))
  have h4 := wt_list2_le (.list [natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)]) (.list ((1 :: gs).map encPerm))
  have h5 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (vs := [Val.nat (n + n), Val.list ((1 :: gs).map encPerm)]) (by simp)
  have h6 := (scosBig_wt3 c hinv hw).1
  have hgsl := scosBig_gsl gs hw
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  unfold scosW at hw
  -- the restriction
  have hT : ((1 :: gs).length + 1) * (n + n + 1) ≤ 320 * scosBigS n c := by
    calc ((1 :: gs).length + 1) * (n + n + 1) ≤ (320 * (n + n + 1) ^ 6) * (n + n + 1) ^ 6 :=
          Nat.mul_le_mul (by simp only [List.length_cons]; omega) hQ.2.1
      _ = 320 * ((n + n + 1) ^ 6 * (n + n + 1) ^ 6) := by ring
      _ ≤ 320 * scosBigS n c := Nat.mul_le_mul_left _ hS.2.1
  have hT7 : restrListK * (((1 :: gs).length + 1) * (n + n + 1)) ^ 7 ≤
      10 ^ 13 * 320 ^ 7 * scosBigS n c ^ 7 := by
    calc restrListK * (((1 :: gs).length + 1) * (n + n + 1)) ^ 7 ≤
        10 ^ 13 * (320 * scosBigS n c) ^ 7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT 7)
      _ = 10 ^ 13 * 320 ^ 7 * scosBigS n c ^ 7 := by ring
  have hS7 : scosBigS n c ≤ scosBigS n c ^ 7 := Nat.le_self_pow (by norm_num) _
  have hK : 10 ^ 13 * 320 ^ 7 + 100000 ≤ 10 ^ 40 := by norm_num
  generalize 10 ^ 13 * 320 ^ 7 = K13 at *
  generalize (10 : ℕ) ^ 40 = K40 at *
  have hS7' : K40 * scosBigS n c ^ 7 ≥ K13 * scosBigS n c ^ 7 + 100000 * scosBigS n c ^ 7 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hK
  generalize restrListK * (((1 :: gs).length + 1) * (n + n + 1)) ^ 7 = R at *
  generalize K13 * scosBigS n c ^ 7 = R' at *
  generalize K40 * scosBigS n c ^ 7 = R'' at *
  generalize scosBigS n c ^ 7 = S7 at *
  generalize (Val.list [encGroup gs, encPerm (nintSum x), scosInd Φ]).wt = A at *
  omega

/-! ### Step 4: the restricted group -/

theorem scosBig_lenDom (Φ : Finset (Fin n)) :
    ((domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)).map Val.nat).length = scosBMk Φ := by
  rw [List.length_map, length_domNat]

theorem scosBig_step4 {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    {gs : List (Perm (Fin (n + n)))} (x : ScosPair n) (hw : (encGroup gs).wt ≤ scosW n) :
    Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
        posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
        .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm)]
      (.call 150 (mk2 (.length (.var 1)) (.var 3)))
      (encGroup (scosBigHs 𝒢 Φ hinv gs)) (scosBigD n c) := by
  have dv1 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm)]) (i := 1)
    (v := .list ((domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)).map Val.nat)) rfl
  have dl := Det.length dv1
  rw [scosBig_lenDom] at dl
  have dv3 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm)]) (i := 3)
    (v := .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm)) rfl
  have d := Det.call (Det.mk2 dl dv3) (mkGroup_spec scos_mkGroup (scosBigHs 𝒢 Φ hinv gs))
  refine d.mono (scosBigD_of (A := 10 ^ 40) (j := 7) ?_ le_rfl le_rfl)
  have h1 := wt_domNat_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  have h1' : (Val.list ((domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)).map Val.nat)).wt =
    (natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))).wt := rfl
  have h3 := scosBig_wt3 c hinv hw
  have h4 := wt_list2_le (.nat (scosBMk Φ)) (.list ((scosBigHs 𝒢 Φ hinv gs).map encPerm))
  have h5 := wt_nat_le (scosBMk Φ)
  have hgsl := scosBig_gsl gs hw
  have hk := scosBig_kQ Φ
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have hT : ((scosBigHs 𝒢 Φ hinv gs).length + 2) * (scosBMk Φ + 1) ≤ 321 * scosBigS n c := by
    calc ((scosBigHs 𝒢 Φ hinv gs).length + 2) * (scosBMk Φ + 1) ≤
        (321 * (n + n + 1) ^ 6) * (n + n + 1) ^ 6 :=
          Nat.mul_le_mul (by rw [length_scosBigHs]; omega) hk.2
      _ = 321 * ((n + n + 1) ^ 6 * (n + n + 1) ^ 6) := by ring
      _ ≤ 321 * scosBigS n c := Nat.mul_le_mul_left _ hS.2.1
  have hT3 : mkGroupK * (((scosBigHs 𝒢 Φ hinv gs).length + 2) * (scosBMk Φ + 1)) ^ 3 ≤
      mkGroupK * 321 ^ 3 * scosBigS n c ^ 7 := by
    calc mkGroupK * (((scosBigHs 𝒢 Φ hinv gs).length + 2) * (scosBMk Φ + 1)) ^ 3 ≤
        mkGroupK * (321 * scosBigS n c) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT 3)
      _ = mkGroupK * 321 ^ 3 * scosBigS n c ^ 3 := by ring
      _ ≤ mkGroupK * 321 ^ 3 * scosBigS n c ^ 7 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS.2.2.2.2 (by norm_num))
  have hS7 : scosBigS n c ≤ scosBigS n c ^ 7 := Nat.le_self_pow (by norm_num) _
  have hK : mkGroupK * 321 ^ 3 + 100000 ≤ 10 ^ 40 := by
    have e : mkGroupK = 100000 := rfl
    rw [e]; norm_num
  obtain ⟨K13, hK13⟩ : ∃ K, K = mkGroupK * 321 ^ 3 := ⟨_, rfl⟩
  rw [← hK13] at hT3 hK
  obtain ⟨K40, hK40⟩ : ∃ K, K = (10 : ℕ) ^ 40 := ⟨_, rfl⟩
  rw [← hK40] at hK ⊢
  have hS7' : K40 * scosBigS n c ^ 7 ≥ K13 * scosBigS n c ^ 7 + 100000 * scosBigS n c ^ 7 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hK
  generalize mkGroupK * (((scosBigHs 𝒢 Φ hinv gs).length + 2) * (scosBMk Φ + 1)) ^ 3 = R at *
  generalize K13 * scosBigS n c ^ 7 = R' at *
  generalize K40 * scosBigS n c ^ 7 = R'' at *
  generalize scosBigS n c ^ 7 = S7 at *
  omega

/-! ### Step 5: the minimal blocks -/

/-- The output of step 5: minimal block labels of the restricted group. -/
def ScosBigLab (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (hinv : ScosInv 𝒢 Φ)
    (w : Val) : Prop :=
  ∃ lab : Fin (scosBMk Φ) → ℕ, w = encFun lab ∧ (∀ j, lab j < scosBMk Φ) ∧
    IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab

theorem scosBig_step5 {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    (htr : ScosTrans 𝒢 Φ) (h2 : 2 ≤ Φ.card)
    {gs : List (Perm (Fin (n + n)))} (x : ScosPair n) (hgs : gens gs = 𝒢.map nintSum)
    (hw : (encGroup gs).wt ≤ scosW n) :
    EvalAll 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
        posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
        .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs)]
      (.prim 2 (.var 4)) (fun w c' => ScosBigLab 𝒢 Φ hinv w ∧
        c' ≤ scosBigD n c + (minimalBlocksPrim hmb).boundSize (100000 * scosBigS n c)) := by
  have dv4 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs)]) (i := 4)
    (v := encGroup (scosBigHs 𝒢 Φ hinv gs)) rfl
  have hG : GroupVal (scosBMk Φ) (encGroup (scosBigHs 𝒢 Φ hinv gs))
      (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ) (scosBM_invariant 𝒢 Φ hinv)).range :=
    ⟨_, rfl, scosBig_gensHs hinv hgs⟩
  have hk2 : 2 ≤ scosBMk Φ := by rw [scosBMk_eq]; exact h2
  have h := minimalBlocks_call hmb scos_prim2 dv4 hG hk2 (scosBM_trans 𝒢 Φ hinv htr)
  refine h.mono fun w c' hw' => ⟨?_, ?_⟩
  · obtain ⟨lab, h1, h2, h3⟩ := hw'.1
    exact ⟨lab, h1, h2, h3⟩
  · have h3 := (scosBig_wt3 c hinv hw).2
    have hsz := Val.size_le_wt (encGroup (scosBigHs 𝒢 Φ hinv gs))
    have hsz' : (encGroup (scosBigHs 𝒢 Φ hinv gs)).size ≤ 100000 * scosBigS n c := by omega
    have hb := GI.Lang.Prim.bound_le (minimalBlocksPrim hmb) hsz'
    have hk := scosBig_kQ Φ
    have hS := scosBigS_facts n c
    have hD : 20000 * scosBigS n c ≤ scosBigD n c :=
      scosBigD_of (A := 20000) (j := 1) (by rw [pow_one]) (by norm_num) (by norm_num)
    have := hw'.2
    omega

end Prog

end GI.Impl
