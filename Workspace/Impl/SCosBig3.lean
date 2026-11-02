import Workspace.Impl.SCosBig2

/-!
# Function 5 (`bigF`), steps 6–9

With the minimal block labels `lab` of step 5, the next four `let`s compute:

6. the labels `labN = scosBMLab Φ lab` on `Fin (n + n)` (`gather_spec`);
7. the class representatives of `labN` (`cls_spec`, third entry);
8. the kernel `K = scosBMKer 𝒢 Φ lab` (`ker_spec`, primitive `1`);
9. the orbit of `labN` with a transversal (`cosets_spec`, with `B = (n + n + 1)^c`).

Each step costs at most `scosBigD n c` (the kernel step also the bound of the preimage call).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The weight of the result of a deterministic function is below its cost. -/
theorem scosBig_funDet_wt {P : Program} {f : ℕ} {v w : Val} {c : ℕ} (h : FunDet P f v w c) :
    w.wt < c := by
  obtain ⟨body, -, h'⟩ := FunAll.wt_lt h
  obtain ⟨v', c', -, hq⟩ := h'.exists_eval
  obtain ⟨⟨rfl, h1⟩, h2⟩ := hq
  omega

theorem scosBig_posVal (Φ : Finset (Fin n)) :
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ) = natList ((List.finRange (n + n)).map
      fun i : Fin (n + n) => posOf (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) i) := by
  simp [posVal, encFun, natList, List.map_map, Function.comp_def]

/-- `Q^3 ≤ S^3`, `Q ≤ S^7`, and the like. -/
theorem scosBig_SQ (n c : ℕ) {j : ℕ} (hj : 1 ≤ j) : (n + n + 1) ^ 6 ≤ scosBigS n c ^ j := by
  have hS := scosBigS_facts n c
  exact hS.1.trans (Nat.le_self_pow (by omega) _)

section Prog

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-! ### Step 6: the labels on `Fin (n + n)` -/

theorem scosBig_step6 {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    {gs : List (Perm (Fin (n + n)))} (x : ScosPair n)
    {lab : Fin (scosBMk Φ) → ℕ} (hlt : ∀ j, lab j < scosBMk Φ) :
    Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
        posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
        .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
        encFun lab]
      (.call 157 (mk2 (.snoc (.var 5) (.length (.var 1))) (.var 2)))
      (encFun (scosBMLab Φ lab)) (scosBigD n c) := by
  have dv5 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
    encFun lab]) (i := 5)
    (v := .list ((List.finRange (scosBMk Φ)).map fun j => .nat (lab j))) rfl
  have dv1 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
    encFun lab]) (i := 1)
    (v := .list ((domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)).map Val.nat)) rfl
  have dl := Det.length dv1
  rw [scosBig_lenDom] at dl
  have ds := Det.snoc dv5 dl
  have dv2 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
    encFun lab]) (i := 2) (v := natList ((List.finRange (n + n)).map
      fun i : Fin (n + n) => posOf (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) i))
    (congrArg some (scosBig_posVal Φ))
  have hg := gather_spec (scos_gather (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (L := (List.finRange (scosBMk Φ)).map (fun j => Val.nat (lab j)) ++ [Val.nat (scosBMk Φ)])
    (is := (List.finRange (n + n)).map
      fun i : Fin (n + n) => posOf (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) i) (by
        intro i hi
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
        have := posOf_le (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) j
        rw [length_domNat] at this
        have e : scosBMk Φ = (domFin (Equiv.refl (Fin (n + n))) (scosPhiF Φ)).length := rfl
        simp only [List.length_append, List.length_map, List.length_finRange, List.length_cons,
          List.length_nil]
        omega)
  have d := Det.call (Det.mk2 ds dv2) hg
  rw [scosBig_gather_eq] at d
  have hK : gatherK * 40 ^ 3 + 100000 ≤ 10 ^ 40 := by
    have e : gatherK = 100000 := rfl
    rw [e]; norm_num
  refine d.mono (scosBigD_of (j := 7) ?_ hK le_rfl)
  -- weights
  have hk := scosBig_kQ Φ
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have w5 := wt_encFun_le_sq lab fun j => (hlt j).le
  have w5' : (Val.list ((List.finRange (scosBMk Φ)).map fun j => .nat (lab j))).wt =
    (encFun lab).wt := rfl
  have w1 := wt_domNat_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  have w1' : (Val.list ((domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)).map Val.nat)).wt =
    (natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ))).wt := rfl
  have w2 := wt_posVal_le (Equiv.refl (Fin (n + n))) (scosPhiF Φ)
  rw [scosBig_posVal] at w2
  have wsn := wt_list_snoc_le ((List.finRange (scosBMk Φ)).map fun j => Val.nat (lab j))
    (.nat (scosBMk Φ))
  have wn := wt_nat_le (scosBMk Φ)
  have wa := wt_list2_le (.list ((List.finRange (scosBMk Φ)).map (fun j => Val.nat (lab j)) ++
    [Val.nat (scosBMk Φ)])) (natList ((List.finRange (n + n)).map
      fun i : Fin (n + n) => posOf (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) i))
  have wo := wt_encFun_le_sq (scosBMLab Φ lab) (scosBMLab_le Φ lab hlt)
  have hA : (Val.list [.list ((List.finRange (scosBMk Φ)).map (fun j => Val.nat (lab j)) ++
      [Val.nat (scosBMk Φ)]), natList ((List.finRange (n + n)).map
      fun i : Fin (n + n) => posOf (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) i)]).wt + 1 ≤
      40 * scosBigS n c := by omega
  have hA3 := Nat.mul_le_mul_left gatherK (Nat.pow_le_pow_left hA 3)
  rw [mul_pow, ← Nat.mul_assoc] at hA3
  have h37 : scosBigS n c ^ 3 ≤ scosBigS n c ^ 7 := Nat.pow_le_pow_right hS.2.2.2.2 (by norm_num)
  have h17 : scosBigS n c ≤ scosBigS n c ^ 7 := Nat.le_self_pow (by norm_num) _
  have hm := Nat.mul_le_mul_left (gatherK * 40 ^ 3) h37
  rw [Nat.add_mul]
  obtain ⟨K, hKe⟩ : ∃ K, K = gatherK * 40 ^ 3 := ⟨_, rfl⟩
  rw [← hKe] at hA3 hm ⊢
  generalize scosBigS n c ^ 7 = S7 at *
  generalize scosBigS n c ^ 3 = S3 at *
  omega

/-! ### Step 7: the class representatives -/

/-- The representatives of the classes of `labN`. -/
noncomputable abbrev scosBigRep (Φ : Finset (Fin n)) (lab : Fin (scosBMk Φ) → ℕ) : Val :=
  encFun (Cls.repOf (Cls.keyOf (scosBMLab Φ lab) (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ))))

theorem scosBig_wtRep (Φ : Finset (Fin n)) (lab : Fin (scosBMk Φ) → ℕ) :
    (scosBigRep Φ lab).wt ≤ 4 * (n + n + 1) ^ 2 :=
  wt_encFun_le_sq _ fun i => (Cls.repOf_lt _ i).le

theorem scosBig_step7 {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    {gs : List (Perm (Fin (n + n)))} (x : ScosPair n) (hw : (encGroup gs).wt ≤ scosW n)
    {lab : Fin (scosBMk Φ) → ℕ} (hlt : ∀ j, lab j < scosBMk Φ) :
    Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
        posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
        .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
        encFun lab, encFun (scosBMLab Φ lab)]
      (.get (.call 161 (mk2 (.var 6) (arg 2))) (.nat 2))
      (scosBigRep Φ lab) (scosBigD n c) := by
  have dv6 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
    encFun lab, encFun (scosBMLab Φ lab)]) (i := 6) (v := encFun (scosBMLab Φ lab)) rfl
  have da := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ])
    (rest := [natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
      posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
      .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
      encFun lab, encFun (scosBMLab Φ lab)]) (j := 2)
    (v := encFun (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ))) rfl
  have hc := cls_spec (scos_cls (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (scosBMLab Φ lab) (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) (X := n + n)
    (scosBMLab_le Φ lab hlt) (indF_le_one _ _) le_rfl
  have hcw := scosBig_funDet_wt hc
  have dc := Det.call (Det.mk2 dv6 da) hc
  have dg := Det.get' dc (Det.nat 2) (v := scosBigRep Φ lab) rfl
  have hK : 100000 + 10 * clsK ≤ 10 ^ 40 := by
    have e : clsK = 10 ^ 9 := rfl
    rw [e]; norm_num
  refine dg.mono (scosBigD_of (j := 1) ?_ hK (by norm_num))
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have w0 := scosBig_wt0 gs x Φ hw
  have w6 := wt_encFun_le_sq (scosBMLab Φ lab) (scosBMLab_le Φ lab hlt)
  have wi := scosPaste_wt_ind Φ
  have wi' : (encFun (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ))).wt = (scosInd Φ).wt := rfl
  have wa := wt_list2_le (encFun (scosBMLab Φ lab))
    (encFun (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ)))
  have wr := scosBig_wtRep Φ lab
  have h4 : clsK * (n + n + 1) ^ 4 ≤ clsK * scosBigS n c :=
    Nat.mul_le_mul_left _ (hQ.2.2.2.2.trans hS.1)
  rw [pow_one, Nat.add_mul]
  obtain ⟨K, hKe⟩ : ∃ K, K = clsK := ⟨_, rfl⟩
  rw [← hKe] at h4 hcw ⊢
  generalize (Val.list [encGroup gs, encPerm (nintSum x), scosInd Φ]).wt = A at *
  generalize K * (n + n + 1) ^ 4 = K4 at *
  have h10 : 10 * K * scosBigS n c = 10 * (K * scosBigS n c) := by ring
  rw [h10]
  omega

/-! ### Step 8: the kernel -/

/-- The output of step 8: a group value of the kernel, of weight at most `scosW n`. -/
def ScosBigKer (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (lab : Fin (scosBMk Φ) → ℕ)
    (w : Val) : Prop :=
  GroupVal (n + n) w ((scosBMKer 𝒢 Φ lab).map nintSum) ∧ w.wt ≤ scosW n

theorem scosBig_step8 {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ)
    {gs : List (Perm (Fin (n + n)))} (x : ScosPair n) (hgs : gens gs = 𝒢.map nintSum)
    (hw : (encGroup gs).wt ≤ scosW n)
    {lab : Fin (scosBMk Φ) → ℕ} (hlt : ∀ j, lab j < scosBMk Φ)
    (hmbl : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab) :
    EvalAll 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
        posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
        .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
        encFun lab, encFun (scosBMLab Φ lab), scosBigRep Φ lab]
      (.call 185 (mk2 (arg 0) (.var 7)))
      (fun w c' => ScosBigKer 𝒢 Φ lab w ∧
        c' ≤ scosBigD n c + (preimagePrim hpre).boundSize (100000 * scosBigS n c)) := by
  have da := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ])
    (rest := [natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
      posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
      .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
      encFun lab, encFun (scosBMLab Φ lab), scosBigRep Φ lab]) (j := 0)
    (v := encGroup gs) rfl
  have dv7 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
    encFun lab, encFun (scosBMLab Φ lab), scosBigRep Φ lab]) (i := 7)
    (v := scosBigRep Φ lab) rfl
  have hG : GroupVal (n + n) (encGroup gs) (𝒢.map nintSum) := ⟨gs, rfl, hgs⟩
  have hk := ker_spec hpre (scos_ker (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    scos_prim1 hG (scosBig_reprVal Φ lab hlt) (scosBM_pres 𝒢 Φ hinv lab hlt hmbl)
  -- weights
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have w0 := scosBig_wt0 gs x Φ hw
  have wr := scosBig_wtRep Φ lab
  have wa := wt_list2_le (encGroup gs) (scosBigRep Φ lab)
  have hW : (Val.list [encGroup gs, scosBigRep Φ lab]).wt ≤ 700 * (n + n + 1) ^ 6 := by
    unfold scosW at hw; omega
  have hb : (preimagePrim hpre).boundSize (3 * (Val.list [encGroup gs, scosBigRep Φ lab]).wt) ≤
      (preimagePrim hpre).boundSize (100000 * scosBigS n c) :=
    scosBig_boundSize_mono _ (by omega)
  have h9 : kerK * (Val.list [encGroup gs, scosBigRep Φ lab]).wt ^ 9 ≤
      kerK * 700 ^ 9 * scosBigS n c ^ 7 := by
    have hQ1 := hQ.1
    have hSQ := hS.2.1
    have hS1 := hS.2.2.2.2
    generalize (n + n + 1) ^ 6 = Q at hW hQ1 hSQ
    calc kerK * (Val.list [encGroup gs, scosBigRep Φ lab]).wt ^ 9 ≤
        kerK * (700 * Q) ^ 9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW 9)
      _ = kerK * 700 ^ 9 * Q ^ 9 := by rw [mul_pow, Nat.mul_assoc]
      _ ≤ kerK * 700 ^ 9 * (Q * Q) ^ 5 := by
          refine Nat.mul_le_mul_left _ ?_
          rw [← pow_two, ← pow_mul]
          exact Nat.pow_le_pow_right hQ1 (by norm_num)
      _ ≤ kerK * 700 ^ 9 * scosBigS n c ^ 5 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSQ 5)
      _ ≤ kerK * 700 ^ 9 * scosBigS n c ^ 7 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by norm_num))
  have hK : kerK * 700 ^ 9 + 100000 ≤ 10 ^ 40 := by
    have e : kerK = 10000000 := rfl
    rw [e]; norm_num
  have hD := scosBigD_of (n := n) (c := c) (a := (kerK * 700 ^ 9 + 100000) * scosBigS n c ^ 7)
    (j := 7) le_rfl hK le_rfl
  have h17 : scosBigS n c ≤ scosBigS n c ^ 7 := Nat.le_self_pow (by norm_num) _
  refine EvalAll.call_funAll (Det.mk2 da dv7) fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine hk.mono fun w cb hw' => ⟨⟨?_, hw'.2.1⟩, ?_⟩
  · obtain ⟨K', hK', hmem⟩ := hw'.1
    have e : K' = (scosBMKer 𝒢 Φ lab).map nintSum := by
      ext g
      rw [hmem, mem_map_scosBMKer]
    exact e ▸ hK'
  · have h1 := hw'.2.1
    have h2 := hw'.2.2
    unfold scosW at h1
    rw [Nat.add_mul] at hD
    obtain ⟨K, hKe⟩ : ∃ K, K = kerK * 700 ^ 9 := ⟨_, rfl⟩
    rw [← hKe] at h9 hD
    generalize kerK * (Val.list [encGroup gs, scosBigRep Φ lab]).wt ^ 9 = R at *
    generalize (preimagePrim hpre).boundSize
      (3 * (Val.list [encGroup gs, scosBigRep Φ lab]).wt) = B1 at *
    generalize (preimagePrim hpre).boundSize (100000 * scosBigS n c) = B2 at *
    generalize (Val.list [encGroup gs, encPerm (nintSum x), scosInd Φ]).wt = A at *
    generalize scosBigS n c ^ 7 = S7 at *
    omega

/-! ### Step 9: the cosets -/

/-- The output of step 9: the orbit of `labN` with a transversal. -/
def ScosBigCos (Φ : Finset (Fin n)) (lab : Fin (scosBMk Φ) → ℕ) (gs : List (Perm (Fin (n + n))))
    (w : Val) : Prop :=
  ∃ L : List ((Fin (n + n) → ℕ) × Perm (Fin (n + n))), w = encPairs labKey L ∧
    (L.map Prod.fst).Nodup ∧
    (∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct (1 :: gs) (scosBMLab Φ lab)) ∧
    (∀ p ∈ L, p.2 ∈ genGroup (1 :: gs) ∧ labAct p.2 (scosBMLab Φ lab) = p.1)

theorem scosBig_step9 (hc : ScosPalfyC c) {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)}
    (hinv : ScosInv 𝒢 Φ) (htr : ScosTrans 𝒢 Φ)
    (hsol : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))))
    {gs : List (Perm (Fin (n + n)))} (x : ScosPair n) (hgs : gens gs = 𝒢.map nintSum)
    (hw : (encGroup gs).wt ≤ scosW n)
    {lab : Fin (scosBMk Φ) → ℕ} (hlt : ∀ j, lab j < scosBMk Φ)
    (hmbl : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab) (kv : Val) :
    EvalAll 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
        natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
        posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
        .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
        encFun lab, encFun (scosBMLab Φ lab), scosBigRep Φ lab, kv]
      (.call 206 (scosMk5 (.nat 0) (.get (arg 0) (.nat 1)) (.var 6)
        (scosPowE c (.arith .add (.length (arg 1)) (.nat 1))) (.length (arg 1))))
      (fun w c' => ScosBigCos Φ lab gs w ∧ c' ≤ scosBigD n c) := by
  have da0 := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ])
    (rest := [natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
      posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
      .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
      encFun lab, encFun (scosBMLab Φ lab), scosBigRep Φ lab, kv]) (j := 0)
    (v := encGroup gs) rfl
  have dg := Det.get' da0 (Det.nat 1) (v := .list ((1 :: gs).map encPerm))
    (show [Val.nat (n + n), Val.list ((1 :: gs).map encPerm)][1]? = some _ from rfl)
  have da1 := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ])
    (rest := [natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
      posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
      .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
      encFun lab, encFun (scosBMLab Φ lab), scosBigRep Φ lab, kv]) (j := 1)
    (v := .list ((List.finRange (n + n)).map fun i => .nat (nintSum x i))) rfl
  have dl := Det.length da1
  simp only [List.length_map, List.length_finRange] at dl
  have dadd := Det.arith' (op := BinOp.add) dl (Det.nat 1) (z := n + n + 1) rfl
  have dpow := scosBig_powE dadd (by omega) c
  have dv6 := Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ],
    natList (domNat (Equiv.refl (Fin (n + n))) (scosPhiF Φ)),
    posVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ),
    .list ((scosBigHs 𝒢 Φ hinv gs).map encPerm), encGroup (scosBigHs 𝒢 Φ hinv gs),
    encFun lab, encFun (scosBMLab Φ lab), scosBigRep Φ lab, kv]) (i := 6)
    (v := encFun (scosBMLab Φ lab)) rfl
  have d5 := Det.snoc (Det.mk4 (Det.nat 0) dg dv6 dpow) dl
  simp only [List.cons_append, List.nil_append] at d5
  have hgen : genGroup (1 :: gs) = 𝒢.map nintSum := (scosBig_genGroup gs).trans hgs
  have hB : (actOrbit labAct (1 :: gs) (scosBMLab Φ lab)).ncard ≤ (n + n + 1) ^ c :=
    (scosBM_ncard_le 𝒢 Φ hinv lab hc htr hsol hmbl (1 :: gs) hgen).trans (scosBM_pow_le Φ lab c)
  have hco := FunAll.wt_lt (cosets_spec (scos_cosets (c := c) (hps := hps) (hpre := hpre)
    (hmb := hmb)) (1 :: gs) (scosBMLab Φ lab) (scosBMLab_le Φ lab hlt) hB)
  -- weights
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have w0 := scosBig_wt0 gs x Φ hw
  have hgsl := scosBig_gsl gs hw
  have w1 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (vs := [Val.nat (n + n), Val.list ((1 :: gs).map encPerm)]) (by simp)
  have w6 := wt_encFun_le_sq (scosBMLab Φ lab) (scosBMLab_le Φ lab hlt)
  have wx : (Val.list ((List.finRange (n + n)).map fun i => .nat (nintSum x i))).wt =
    (encPerm (nintSum x)).wt := rfl
  have wx' := scosPaste_wt_perm (nintSum x)
  have w5 := wt_list_snoc_le [Val.nat 0, Val.list ((1 :: gs).map encPerm),
    encFun (scosBMLab Φ lab), Val.nat ((n + n + 1) ^ c)] (Val.nat (n + n))
  simp only [List.cons_append, List.nil_append] at w5
  have w4 := wt_list4_le (Val.nat 0) (Val.list ((1 :: gs).map encPerm)) (encFun (scosBMLab Φ lab))
    (Val.nat ((n + n + 1) ^ c))
  have wn0 := wt_nat_le 0
  have wn1 := wt_nat_le ((n + n + 1) ^ c)
  have wn2 := wt_nat_le (n + n)
  have wn3 := wt_nat_le (n + n + 1)
  unfold scosW at hw
  -- the cosets
  have hT : (1 :: gs).length + (n + n + 1) ^ c + 4 * (n + n + 1) ^ 2 + 20 ≤
      400 * scosBigS n c := by simp only [List.length_cons]; omega
  have h6 : cosetsK * ((1 :: gs).length + (n + n + 1) ^ c + 4 * (n + n + 1) ^ 2 + 20) ^ 6 ≤
      cosetsK * 400 ^ 6 * scosBigS n c ^ 7 := by
    calc cosetsK * ((1 :: gs).length + (n + n + 1) ^ c + 4 * (n + n + 1) ^ 2 + 20) ^ 6 ≤
        cosetsK * (400 * scosBigS n c) ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT 6)
      _ = cosetsK * 400 ^ 6 * scosBigS n c ^ 6 := by rw [mul_pow, Nat.mul_assoc]
      _ ≤ cosetsK * 400 ^ 6 * scosBigS n c ^ 7 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS.2.2.2.2 (by norm_num))
  have hK : 2 * (cosetsK * 400 ^ 6) + 100000 ≤ 10 ^ 40 := by
    have e : cosetsK = 10 ^ 9 := rfl
    rw [e]; norm_num
  have h17 : scosBigS n c ≤ scosBigS n c ^ 7 := Nat.le_self_pow (by norm_num) _
  refine EvalAll.call_funAll d5 fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine hco.mono fun w cb hw' => ⟨?_, ?_⟩
  · obtain ⟨⟨L, h1, h2, h3, h4, -⟩, -⟩ := hw'
    exact ⟨L, h1, h2, h3, h4⟩
  · obtain ⟨⟨L, -, -, -, -, h5⟩, h6'⟩ := hw'
    refine scosBigD_of' (A := 2 * (cosetsK * 400 ^ 6) + 100000) (j := 7) ?_ hK le_rfl
    clear hK
    obtain ⟨K, hKe⟩ : ∃ K, K = cosetsK * 400 ^ 6 := ⟨_, rfl⟩
    rw [← hKe] at h6 ⊢
    clear hKe
    have hX : 2 * (Val.list [encGroup gs, encPerm (nintSum x), scosInd Φ]).wt + 1 + 5 + (n + n) +
        3 + (1 + 3) + (n + n + 1) + 3 + (n + n + 1) ^ c + 3 ≤ 10000 * scosBigS n c ^ 7 := by
      omega
    have hcX := Nat.mul_le_mul_left c hX
    have hR : (c + 1) * ((2 * K + 100000) * scosBigS n c ^ 7) =
        c * (2 * K * scosBigS n c ^ 7) + 10 * (c * (10000 * scosBigS n c ^ 7)) +
          2 * (K * scosBigS n c ^ 7) + 100000 * scosBigS n c ^ 7 := by ring
    rw [hR]
    generalize c * (2 * K * scosBigS n c ^ 7) = Z at *
    generalize c * (10000 * scosBigS n c ^ 7) = Y at *
    omega

end Prog

end GI.Impl
