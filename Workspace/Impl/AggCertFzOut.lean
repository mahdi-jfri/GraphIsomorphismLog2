module

public import Workspace.Impl.AggCertFz

@[expose] public section

/-!
# The graph forms of the certificate groups: the points outside the final window

The first part of one step of `cpFzFuns`: the `foldl` of the filter `cpFzFiltE` over the stages
of a log. Each step removes the points of one increment (`cp_bud_filt`), so after all stages the
list holds the points outside the final window (`cpOutF`, `cp_mem_outF_win`).

* `cp_fz_filt`: one stage, within the budget `cpG W + 20 (W + 20)`;
* `cp_fz_out`: all stages, within `cpFzOutB W`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- The budget of the loop over the stages of one log. -/
noncomputable def cpFzOutB (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W : ℕ) :
    ℕ :=
  W * (cpG hst hpre hm W + 20 * (W + 20)) + 3000 * (W + 1) ^ 2

section Out

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {q : ℕ}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

theorem cp_outF_sublist (os : List S.dom) (incls : List (List S.dom)) :
    (cpOutF e q os incls).Sublist os := by
  induction incls generalizing os with
  | nil => exact List.Sublist.refl _
  | cons i is ih =>
    exact (ih _).trans List.filter_sublist

theorem cp_outF_snoc (os : List S.dom) (incls : List (List S.dom)) (i : List S.dom) :
    cpOutF e q os (incls ++ [i]) = (cpOutF e q os incls).filter fun v =>
      decide ((cpPosN e q i).count (domPos e q v : ℕ) = 0) := by
  unfold cpOutF
  rw [List.foldl_append]
  rfl

/-- **One stage**: the filter of the move program, on the increment of the stage. -/
theorem cp_fz_filt {Pg : Program} {f b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hfz : CpFzAt Pg f b) {c : Val} {o : List S.dom} {d : CpStgD k q} {incl : List S.dom}
    (hd : d.2 = incl.map (domPos e q)) (hl : incl.length ≤ k) (ho : o.length ≤ k) {W : ℕ}
    (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W)
    (hw : (Val.list [c, encPts (o.map (domPos e q)), cpSgV d]).wt ≤ W) :
    CpFB Pg (f + 8) (.list [c, encPts (o.map (domPos e q)), cpSgV d]) W
      (cpG hst hpre hm W + 20 * (W + 20))
      (fun w => w = encPts ((o.filter fun v =>
        decide ((cpPosN e q incl).count (domPos e q v : ℕ) = 0)).map (domPos e q))) := by
  refine CpFB.intro hfz.filt ?_
  unfold cpFzFiltE
  set A := Val.list [c, encPts (o.map (domPos e q)), cpSgV d] with hA
  have g2 := Det.arg' (P := Pg) (vs := [c, encPts (o.map (domPos e q)), cpSgV d]) (rest := [])
    (j := 2) (v := .list [gpV d.1, encPts d.2]) rfl
  have d1 := Det.get' g2 (Det.nat 1) (v := natList (cpPosN e q incl))
    (by rw [hd, encPts_posN]; rfl)
  have d2 := Det.arg' (P := Pg) (vs := [c, encPts (o.map (domPos e q)), cpSgV d]) (rest := [])
    (j := 1) (v := encPts (o.map (domPos e q))) rfl
  have w1 : (natList (cpPosN e q incl)).wt ≤ 10 * (k + q + 1) ^ 2 := by
    rw [← encPts_posN]; exact cp_wt_pts (by rw [List.length_map]; exact hl)
  have w2 : (encPts (o.map (domPos e q))).wt ≤ 10 * (k + q + 1) ^ 2 :=
    cp_wt_pts (by rw [List.length_map]; exact ho)
  have w3 := wt_list2_le (natList (cpPosN e q incl)) (encPts (o.map (domPos e q)))
  have w4 : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w5 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have eA : (Val.list [c, encPts (o.map (domPos e q)), cpSgV d]).wt = A.wt := rfl
  refine (CpEB.call (CpEB.det (Det.mk2 d1 d2) le_rfl (by omega)
    (Q := fun v => v = .list [natList (cpPosN e q incl), encPts (o.map (domPos e q))]) rfl)
    fun v hv _ => hv ▸ cp_bud_filt hst hpre hm hat hl ho hW).mono ?_ fun _ h => h
  have := wt_nat_le 1
  omega

set_option maxRecDepth 20000 in
/-- **All stages of a log**: from the points `o0`, the points not in any increment. -/
theorem cp_fz_out {Pg : Program} {f b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hfz : CpFzAt Pg f b) {o0 : List S.dom} (ho0 : o0.length ≤ k) {l : List (CpStgD k q)}
    (hl : CpLgLen l) {incls : List (List S.dom)} (hlen : incls.length = l.length)
    (hinc : ∀ j (h1 : j < incls.length) (h2 : j < l.length),
      l[j].2 = incls[j].map (domPos e q) ∧ incls[j].length ≤ k) {W : ℕ}
    (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W)
    (hw : (Val.list [.nat 0, .list (l.map cpSgV), encPts (o0.map (domPos e q))]).wt ≤ W) :
    CpFB Pg (f + 5) (.list [.nat 0, .list (l.map cpSgV), encPts (o0.map (domPos e q))]) W
      (cpFzOutB hst hpre hm W)
      (fun w => w = encPts ((cpOutF e q o0 incls).map (domPos e q))) := by
  have w4 : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w6 : (k + q + 1) ^ 4 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w7 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hwo : ∀ n, ((cpOutF e q o0 (incls.take n)).map (domPos e q)).length ≤ k := fun n => by
    rw [List.length_map]; exact (cp_outF_sublist o0 _).length_le.trans ho0
  have hWo : ∀ n, (encPts ((cpOutF e q o0 (incls.take n)).map (domPos e q))).wt ≤
      10 * (k + q + 1) ^ 2 := fun n => cp_wt_pts (hwo n)
  have hF := foldl_spec hfz.fold (c := .nat 0) (xs := l.map cpSgV)
    (acc0 := encPts (o0.map (domPos e q)))
    (Inv := fun i acc => acc = encPts ((cpOutF e q o0 (incls.take i)).map (domPos e q)))
    (M := 10 * (k + q + 1) ^ 2) (B := fun _ => cpG hst hpre hm W + 20 * (W + 20))
    (by simp [cpOutF])
    (fun i acc _ h => h ▸ hWo i) (fun i acc hi hacc => ?_)
  · refine FunAll.mono hF fun w cost h => ⟨?_, ?_, ?_⟩
    · rw [h.1, List.length_map, ← hlen, List.take_length]
    · rw [h.1]; have := hWo (l.map cpSgV).length; omega
    · have h2 := h.2
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
      have hlk : (l.map cpSgV).length ≤ W := by
        rw [List.length_map]; have := hl.1
        have : k ≤ (k + q + 1) ^ 12 := (Nat.le_self_pow (by omega) _).trans' (by omega)
        omega
      have a1 : (l.map cpSgV).length * (cpG hst hpre hm W + 20 * (W + 20)) ≤
          W * (cpG hst hpre hm W + 20 * (W + 20)) := Nat.mul_le_mul_right _ hlk
      have a2 : loopModK * ((l.map cpSgV).length + 1) *
          ((Val.list [.nat 0, .list (l.map cpSgV), encPts (o0.map (domPos e q))]).wt +
            (l.map cpSgV).length + 10 * (k + q + 1) ^ 2 + 1) ≤
          1000 * (W + 1) * (3 * (W + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have a3 : 1000 * (W + 1) * (3 * (W + 1)) = 3000 * (W + 1) ^ 2 := by ring
      have e1 : loopModK = 1000 := rfl
      unfold cpFzOutB
      clear hwo hWo hinc hF
      omega
  · subst hacc
    have hil : i < l.length := by rw [List.length_map] at hi; exact hi
    have hii : i < incls.length := by rw [hlen]; exact hil
    obtain ⟨hd, hik⟩ := hinc i hii hil
    have hxi : (l.map cpSgV)[i] = cpSgV l[i] := List.getElem_map _
    rw [hxi]
    have hsg := cp_wt_sg (hl.2 _ (List.getElem_mem hil))
    have w3 := wt_list3_le (.nat 0) (encPts ((cpOutF e q o0 (incls.take i)).map (domPos e q)))
      (cpSgV l[i])
    have := wt_nat_le 0
    have := hWo i
    refine FunAll.mono (cp_fz_filt hst hpre hm hat hfz hd hik
      ((cp_outF_sublist o0 _).length_le.trans ho0) hW (by omega)) fun w cost h => ⟨?_, h.2.2⟩
    beta_reduce
    rw [h.1, List.take_add_one, List.getElem?_eq_getElem hii, Option.toList_some, cp_outF_snoc]

end Out

end GI.Impl
