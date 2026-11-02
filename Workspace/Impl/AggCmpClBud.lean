import Workspace.Impl.AggCmpClProg

/-!
# The call of a stage: the kernel and the increment

Two pieces of the call (`AggCmpClProg.lean`), each within the module budget `cpG`.

* `cm_cl_ker`: from stage `j` of a log, `cmKerF` computes the stage kernel
  `N_j = ker(φ_T|_{A_j})`. The kernel is the stabilizer of the label points of `T` in `A_j`
  (`pairGens_kernelIn`), so one **PointwiseStab** call gives it in graph form, and the reduction
  `kr_spec` keeps the first parts with at most `k²` generators (`groupValC_of_kr`).
* `cm_cl_dv`: the indicator of the positions of the increment `V_j` (`cm_ind_spec`,
  `cp_count_pos`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv
  Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

section Bud

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {W : ℕ} {Pg : Program}
  {b jp : ℕ} (hsa : CmStAt Pg b jp) (hca : CmClAt Pg b)
  {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}

include hsa hca in
/-- **The stage kernel.** From stage `j` of the log of `T` and the string `z`, `cmKerF` returns
the canonical value of the group of the lift of `N_j = ker(φ_T|_{A_j})`. -/
theorem cm_cl_ker (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) {T : Finset (Fin L.q)} {z : Ω → C}
    {j : ℕ} {d : CmStage k L.q} (hd : CmStg e πd T z j d)
    (hw : 10 * (Val.list [.list [.nat k, .nat L.q], cmStgV d, tsV k T]).wt + 100 ≤ W)
    (hW : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W) :
    CpFB Pg (b + 13) (.list [.list [.nat k, .nat L.q], cmStgV d, tsV k T]) W
      (2 * cpG hst hpre hm W + 40 * W + 200)
      (fun w => GroupValC k w (groupFin e (S.liftGroup
        (kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (dstr S z) j))))) := by
  obtain ⟨hps, hpl, -⟩ := hd
  set X := labPts k (tlist T) with hX
  have hXl : X.length ≤ L.q := by
    rw [hX, labPts, List.length_map, tlist, Finset.length_sort]
    exact (Finset.card_le_univ T).trans (by simp)
  set V := Val.list [.list [.nat k, .nat L.q], cmStgV d, tsV k T] with hV
  have hVW : 10 * V.wt + 100 ≤ W := hw
  have eV : (Val.list [.list [.nat k, .nat L.q], cmStgV d, tsV k T]).wt = V.wt := rfl
  have eS : (Val.list [gpV d.1, encPts d.2]).wt = (cmStgV d).wt := rfl
  have eT : (Val.list [indT T, natList (ptsKey X)]).wt = (tsV k T).wt := rfl
  have h0 : (Val.list [.nat k, .nat L.q]).wt < V.wt := cm_wt_lt_of_mem (by simp)
  have h1 : (cmStgV d).wt < V.wt := cm_wt_lt_of_mem (by simp)
  have h2 : (tsV k T).wt < V.wt := cm_wt_lt_of_mem (by simp)
  have h1' : (gpV d.1).wt < (cmStgV d).wt := cm_wt_lt_of_mem (by simp)
  have h2' : (natList (ptsKey X)).wt < (tsV k T).wt := cm_wt_lt_of_mem (by simp [hX])
  have dA : Det Pg [V] (mk3 (arg 0) (.get (arg 1) (.nat 0)) (.get (arg 2) (.nat 1)))
      (.list [.list [.nat k, .nat L.q], gpV d.1, natList (ptsKey X)]) (20 * W + 50) := by
    refine (Det.mk3 (Det.arg' (rest := []) (j := 0) (v := .list [.nat k, .nat L.q]) rfl)
      (Det.get' (Det.arg' (rest := []) (j := 1) (v := cmStgV d) rfl) (Det.nat 0)
        (vs := [gpV d.1, encPts d.2]) rfl)
      (Det.get' (Det.arg' (rest := []) (j := 2) (v := tsV k T) rfl) (Det.nat 1)
        (vs := [indT T, natList (ptsKey X)]) rfl)).mono ?_
    have := wt_list3_le (.list [.nat k, .nat L.q]) (gpV d.1) (natList (ptsKey X))
    omega
  have hAw : (Val.list [.list [.nat k, .nat L.q], gpV d.1, natList (ptsKey X)]).wt ≤ W := by
    have := wt_list3_le (.list [.nat k, .nat L.q]) (gpV d.1) (natList (ptsKey X))
    have : 10 ^ 10 ≤ W := by
      have := Nat.one_le_pow 12 (k + L.q + 1) (by omega)
      omega
    omega
  have hS := cm_bud_stab hst hpre hm hsa hjp hpl hXl hW
  refine CpFB.intro hca.ker ?_
  unfold cmKerF
  refine (CpEB.letE (Cb := cpG hst hpre hm W + 12 * W + 60) (CpEB.call (CpEB.det dA le_rfl hAw (Q := fun v => v =
    .list [.list [.nat k, .nat L.q], gpV d.1, natList (ptsKey X)]) rfl)
    (fun v hv _ => by subst hv; exact hS)) (fun v hv hvW => ?_)).mono (by omega) (fun _ h => h)
  obtain ⟨qs, rfl, hql, hcl⟩ := hv
  obtain ⟨f1, f2, -, f24, f46, -, -, -, f9, -⟩ := cp_pow_facts k L.q
  have w4 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hqw := cp_wt_gp (k := k) (q := L.q) hql
  have hkW : k + 2 ≤ W := by have := Nat.le_self_pow (n := 12) (by omega) (k + L.q + 1); omega
  have dK : Det Pg [V, gpV qs] (mk2 (.get (arg 0) (.nat 0)) (.var 1)) (.list [.nat k, gpV qs])
      (10 * W + 50) := by
    refine (Det.mk2 (Det.get' (Det.arg' (rest := [gpV qs]) (j := 0)
        (v := .list [.nat k, .nat L.q]) rfl) (Det.nat 0) (vs := [.nat k, .nat L.q]) rfl)
      (Det.var' (i := 1) (v := gpV qs) rfl)).mono ?_
    have := wt_list2_le (.nat k) (gpV qs)
    have := wt_nat_le k
    omega
  have hKw : (Val.list [.nat k, gpV qs]).wt ≤ W := by
    have := wt_list2_le (.nat k) (gpV qs)
    have := wt_nat_le k
    omega
  refine (CpEB.call (CpEB.det dK le_rfl hKw (Q := fun v => v = .list [.nat k, gpV qs]) rfl)
    (fun v hv _ => by subst hv; exact cp_bud_kr hst hpre hm hsa.kr hjp hql hW)).mono
    (by omega) ?_
  rintro w ⟨hs, rfl, hg, hl⟩
  have hA : grp (cpPhi S πd T) (dstr S z) j ≤ Pgrp S.domGroup πd T := grp_le _ _ _
  exact groupValC_of_kr (S.liftGroup_le _) (pairGens_kernelIn πd hπ hA hps hcl) hg hl

include hsa hca in
open Classical in
/-- **The increment.** From stage `j` of the log of `T` and the string `z`, the indicator returns
the domain indicator of the increment `V_j`. -/
theorem cm_cl_dv {T : Finset (Fin L.q)} {z : Ω → C} {j : ℕ} {d : CmStage k L.q}
    (hd : CmStg e πd T z j d) (hW : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W) :
    CpFB Pg (b + 11) (.list [.nat k, encPts d.2]) W (cpG hst hpre hm W)
      (fun w => DomVal e w (Subtype.val ''
        (inc (cpPhi S πd T) (dstr S z) j : Set S.dom))) := by
  obtain ⟨-, -, incl, hnd, hmem, hd2⟩ := hd
  rw [hd2, encPts_posN]
  set P := cpPosN e L.q incl with hP
  have hl : incl.length ≤ k := by
    have := hnd.length_le_card
    have : Fintype.card S.dom ≤ k := by
      have := Fintype.card_le_of_injective (fun v : S.dom => e v.1)
        (fun a b h => Subtype.ext (e.injective h))
      simpa using this
    omega
  have hPl : P.length ≤ k + L.q := by rw [hP, cp_posN_length]; omega
  have hI := cm_ind_spec hca.ind hsa.rng hca.imap hca.istep hca.cnt k P (B := k + L.q)
    cp_posN_le (by omega) hPl
  have hset : (Subtype.val '' (inc (cpPhi S πd T) (dstr S z) j : Set S.dom)) =
      Subtype.val '' {v | v ∈ incl} := by
    congr 1
    ext v
    exact (hmem v).symm
  have hout : natList ((List.range k).map P.count) =
      encFun fun i => if e.symm i ∈ Subtype.val '' {v | v ∈ incl} then 1 else 0 := by
    rw [encFun_eq_natList, ← List.map_coe_finRange_eq_range, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, hP]
    exact cp_count_pos hnd i
  rw [hout] at hI
  refine CpFB.det hI ?_ ?_ (by rw [hset]; rfl)
  · obtain ⟨f1, -, -, -, -, -, -, -, -, -⟩ := cp_pow_facts k L.q
    have h4 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have := cpG_poly hst hpre hm (W := W)
    have hW1 : 1 ≤ W := by have := Nat.one_le_pow 12 (k + L.q + 1) (by omega); omega
    have hp := cp_poly_le (W := W) (K := cmIndK) (d := 4) (by simp [cmIndK]) (by norm_num) hW1
    have : (k + L.q + 1) ^ 4 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_left (by
      have := Nat.le_self_pow (n := 12) (by omega) (k + L.q + 1); omega) 4
    have := Nat.mul_le_mul_left cmIndK this
    omega
  · have := wt_encFun_le (fun i => if e.symm i ∈ Subtype.val '' {v | v ∈ incl} then 1 else 0)
      (B := 1) (fun i => by
        by_cases h : e.symm i ∈ Subtype.val '' {v | v ∈ incl} <;> simp [h])
    have e7 : k * (2 * 1 + 5) = 7 * k := by ring
    have := Nat.le_self_pow (n := 12) (by omega) (k + L.q + 1)
    omega

end Bud

end GI.Impl
