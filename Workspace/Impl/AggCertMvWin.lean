module

public import Workspace.Impl.AggCertMvNext

@[expose] public section

/-!
# The move program: after a window answer

`cpWinF` (at `b + 5`) runs when a window call of the round has been answered. It adds the
generators of the answer (`ansGens_spec`) to those of the round (`append`), then makes the next
window call (`cp_next_spec`) or closes the round (`cp_close_spec`). `cp_win_spec` is the result
used later.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

section Bud

variable {k : ℕ} (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- **The generators of one answer, within the budget.** -/
theorem cp_bud_ansG {Pg : Program} {b : ℕ} (hb : Pg.HasAt b (ansGensFuns b)) (a : Perm (Fin k))
    {u : Val} {o : Option (Perm (Fin k) × List (Perm (Fin k)))} (hu : AnsOV u o) {W : ℕ}
    (hW : 10 ^ 10 * (k + 1) ^ 12 ≤ W) :
    CpFB Pg b (.list [encPerm a, u]) W (cpG hst hpre hm W)
      (fun w => w = .list ((ansGens a o).map encPerm)) := by
  have hl := cp_ansGens_length (a := a) hu
  have hw := cp_wt_perms (q := 0) hl
  have e0 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  have e1 : (k + 1) ^ 2 * (k + 1) ^ 2 = (k + 1) ^ 4 := by ring
  have e2 : (k + 1) ^ 4 ≤ (k + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (k ^ 2 + 1) * (k + 1) ^ 2 ≤ (k + 1) ^ 12 :=
    (Nat.mul_le_mul_right _ (by omega)).trans (e1 ▸ e2)
  have e3 : 9 * (k ^ 2 + 1) * (k + 0 + 1) ^ 2 = 9 * ((k ^ 2 + 1) * (k + 1) ^ 2) := by ring
  have e4 : 1 ≤ (k + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  refine CpFB.det (ansGens_spec hb a hu) ?_ (by omega) rfl
  have a1 : ansGK * (k + 1) ^ 8 ≤ ansGK * (W + 1) ^ 8 := by
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 8)
    have : k + 1 ≤ (k + 1) ^ 12 := Nat.le_self_pow (by omega) _
    omega
  have a2 := cp_poly_le (W := W) (K := ansGK) (d := 8) (by simp [ansGK]) (by norm_num)
    (by have : 1 ≤ (k + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
        omega)
  have := cpG_poly hst hpre hm (W := W)
  omega

/-- **Append, within the budget.** -/
theorem cp_bud_app {Pg : Program} {b : ℕ} (hb : Pg.HasAt b (appendFuns b)) (xs ys : List Val)
    {W : ℕ} (hW : 1 ≤ W) (hw : 4 * (Val.list [.list xs, .list ys]).wt + 10 ≤ W) :
    CpFB Pg b (.list [.list xs, .list ys]) W (cpG hst hpre hm W) (fun w => w = .list (xs ++ ys)) := by
  have hxs : (Val.list xs).wt < (Val.list [.list xs, .list ys]).wt := wt_le_wt_list (by simp)
  have hys : (Val.list ys).wt < (Val.list [.list xs, .list ys]).wt := wt_le_wt_list (by simp)
  have hyl := length_lt_wt_list ys
  have hap := wt_list_append_le xs ys
  have hsum : (Val.list xs).wt + (Val.list ys).wt ≤ (Val.list [.list xs, .list ys]).wt := by
    rw [wt_list_eq [.list xs, .list ys]]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  refine FunAll.mono (append_spec hb xs ys) ?_
  rintro w c ⟨rfl, hc⟩
  refine ⟨rfl, by omega, ?_⟩
  have h1 : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (Val.list (xs ++ ys)).wt + 1) ≤ 1000 * (W + 1) * (W + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e3 : 1000 * (W + 1) * (W + 1) = 1000 * (W + 1) ^ 2 := by ring
  have hp := cp_poly_le (W := W) (K := 1000) (d := 2) (by norm_num) (by norm_num) hW
  have := cpG_poly hst hpre hm (W := W)
  omega

end Bud

section Win

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **After a window answer.** -/
theorem cp_win_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {m f : ℕ} {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    {inner u : Val} {τs : List (Perm S.dom)} {acc' : List (Set (Perm S.dom))}
    (hm' : m = cpMeas (Fintype.card S.dom) D (.win acc T σ.Ts σ.s σ.t τs acc')) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hlen : CpLen D σ) (hT : T = σ.T) (hWI : CpWinInv e πd σ acc T rec inner u τs acc')
    (hin : CpInLen k L.q D inner)
    (hst' : (Val.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
      inner, u]).wt ≤ Bw) :
    CpFB Pg (b + 5) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        inner, u]) W (6 * cpG hst hpre hm W + 6200 * (W + 20))
      (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀
        NT m ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R
          (.win acc T σ.Ts σ.s σ.t τs acc')) '' Cands rec) f) := by
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  have hWI0 := hWI
  obtain ⟨hR, ht, hne, dn, a, as, hs, dv, incl, rfl, hl, hG, rfl, ho, hacc, hu, hgv', hdv, hnd,
    hinc⟩ := hWI
  obtain ⟨o, huo, hao⟩ := hu.ansOV
  obtain ⟨hglen, hhs, ⟨fd, hfd, hfd1⟩, hincl⟩ := cp_inLen_unpack hin
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := cp_W_facts hBw hW
  have hk12 : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
  set inner := cpInnerV as (stageGens dn) hs dv (incl.map (domPos e L.q)) a with hinner
  set ks := σ.vals par inner with hks
  have hsv : σ.val par inner = .list ks := rfl
  have hwB : (Val.list [.list ks, u]).wt ≤ Bw := by rw [← hsv]; exact hst'
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by omega
  have hi0 : ks[10]? = some (.list [.list (as.map encPerm), .list ((stageGens dn).map encPerm),
    encGroup hs, dv, encPts (incl.map (domPos e L.q)), encPerm a]) := rfl
  have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? =
      some (.list [.list ks, u]) := fun _ => rfl
  have hkW : (Val.list ks).wt < (Val.list [.list ks, u]).wt := cp_wt_get (vs := [.list ks, u])
    (j := 0) rfl
  have huW : u.wt < (Val.list [.list ks, u]).wt := cp_wt_get (vs := [.list ks, u]) (j := 1) rfl
  have hinK : inner.wt < (Val.list ks).wt := cp_wt_get (vs := ks) (j := 10) rfl
  have hgsI : (Val.list ((stageGens dn).map encPerm)).wt < inner.wt :=
    cp_wt_get (vs := [.list (as.map encPerm), .list ((stageGens dn).map encPerm),
      encGroup hs, dv, encPts (incl.map (domPos e L.q)), encPerm a]) (j := 1) rfl
  have haI : (encPerm a).wt < inner.wt :=
    cp_wt_get (vs := [.list (as.map encPerm), .list ((stageGens dn).map encPerm),
      encGroup hs, dv, encPts (incl.map (domPos e L.q)), encPerm a]) (j := 5) rfl
  have hasI : (Val.list (as.map encPerm)).wt < inner.wt :=
    cp_wt_get (vs := [.list (as.map encPerm), .list ((stageGens dn).map encPerm),
      encGroup hs, dv, encPts (incl.map (domPos e L.q)), encPerm a]) (j := 0) rfl
  -- the new generators
  set gs' := stageGens (dn ++ [(a, o)]) with hgs'
  have hgl : (ansGens a o).length ≤ k ^ 2 + 1 := cp_ansGens_length huo
  have hgs'l : gs'.length + (as.length) * (k ^ 2 + 1) ≤ D * (k ^ 2 + 1) := by
    rw [hgs', cp_stageGens_snoc, List.length_append]
    have : (as.length + 1) * (k ^ 2 + 1) = as.length * (k ^ 2 + 1) + (k ^ 2 + 1) := by ring
    omega
  have hk2 : k ^ 2 + 1 ≤ (k + L.q + 1) ^ 2 := by nlinarith
  have hDk : D * (k ^ 2 + 1) ≤ (D + 1) * (k + L.q + 1) ^ 2 :=
    Nat.mul_le_mul (by omega) hk2
  have hw6 : (D + 1) * (k + L.q + 1) ^ 2 * (k + L.q + 1) ^ 2 ≤ (D + 1) * (k + L.q + 1) ^ 6 := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have : (k + L.q + 1) ^ 2 * (k + L.q + 1) ^ 2 = (k + L.q + 1) ^ 4 := by ring
    rw [this]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hgsV := cp_wt_perms (q := L.q) (as := gs') (n := D * (k ^ 2 + 1)) (by omega)
  have hgsVB : (Val.list (gs'.map encPerm)).wt ≤ Bw / 2 := by
    have e1 : 9 * (D * (k ^ 2 + 1)) * (k + L.q + 1) ^ 2 ≤ 9 * ((D + 1) * (k + L.q + 1) ^ 2 *
        (k + L.q + 1) ^ 2) := by
      rw [Nat.mul_assoc 9]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDk)
    have e2 : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + L.q + 1) ^ 6) := by
      ring
    have e3 : 1 ≤ (D + 1) * (k + L.q + 1) ^ 6 :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    omega
  have hargB : (Val.list [σ.val par inner, .list (gs'.map encPerm)]).wt ≤ 4 * Bw := by
    have := wt_list2_le (σ.val par inner) (.list (gs'.map encPerm))
    rw [hsv] at this ⊢
    omega
  refine CpFB.intro hat.win ?_
  rw [hsv]
  unfold cpWinF
  -- the generators of the answer
  have huB : u.wt < Bw := lt_of_lt_of_le huW hwB
  have haW : (encPerm a).wt < Bw := by omega
  have dA := Det.mk2 (cp_rdI (P := Pg) (h0 []) hwW hi0 (j := 5) rfl (by omega))
    (Det.rd (a := 1) (Det.rv (P := Pg) (env := [.list [.list ks, u]]) (i := 0) rfl hwW) le_rfl
      (show [Val.list ks, u][1]? = some u from rfl) (huW.trans_le hwW).le (by omega))
  have hAw : (Val.list [encPerm a, u]).wt ≤ W := by
    have := wt_list2_le (encPerm a) u; omega
  have hk1 : 10 ^ 10 * (k + 1) ^ 12 ≤ W :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 12)) hW2
  have hbA := cp_bud_ansG hst hpre hm hat.ansG a huo hk1
  refine (CpEB.letE (CpEB.call (CpEB.det dA le_rfl hAw
      (Q := fun v => v = .list [encPerm a, u]) rfl) fun v hv _ => hv ▸ hbA)
    (Cb := 5 * cpG hst hpre hm W + 6020 * (W + 20)) fun gv hgv hgW => ?_).mono
    (by omega) fun _ h => h
  subst hgv
  -- the generators of the round so far
  have h1 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? =
      some (.list [.list ks, u]) := fun _ => rfl
  have hgsW : (Val.list ((stageGens dn).map encPerm)).wt < Bw := by omega
  set gv := Val.list ((ansGens a o).map encPerm) with hgv
  have dB := Det.mk2 (cp_rdI (P := Pg) (h1 [gv]) hwW hi0 (j := 1) rfl (by omega))
    (Det.rv (P := Pg) (env := [.list [.list ks, u], gv]) (i := 1) rfl hgW)
  have hansW : gv.wt ≤ Bw / 2 := by
    rw [hgv]
    have := cp_wt_perms (q := L.q) (as := ansGens a o) hgl
    have e5 : (k ^ 2 + 1) * (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 2 * (k + L.q + 1) ^ 2 :=
      Nat.mul_le_mul_right _ hk2
    have e6 : (k + L.q + 1) ^ 2 * (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have e7 : 9 * (k ^ 2 + 1) * (k + L.q + 1) ^ 2 = 9 * ((k ^ 2 + 1) * (k + L.q + 1) ^ 2) := by
      ring
    have e8 : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + L.q + 1) ^ 6) := by
      ring
    have e9 : (k + L.q + 1) ^ 6 ≤ (D + 1) * (k + L.q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
    have e10 : 1 ≤ (k + L.q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have hBw' : (Val.list [.list ((stageGens dn).map encPerm), gv]).wt ≤ 4 * Bw := by
    have := wt_list2_le (.list ((stageGens dn).map encPerm)) gv; omega
  have hbB := cp_bud_app hst hpre hm hat.app ((stageGens dn).map encPerm)
    ((ansGens a o).map encPerm) hW5 (by rw [← hgv]; omega)
  have hgs'e : (stageGens dn).map encPerm ++ (ansGens a o).map encPerm = gs'.map encPerm := by
    rw [hgs', cp_stageGens_snoc, List.map_append]
  rw [hgs'e] at hbB
  refine (CpEB.letE (CpEB.call (CpEB.det dB le_rfl (by omega)
      (Q := fun v => v = .list [.list ((stageGens dn).map encPerm), gv]) rfl)
    fun v hv _ => hv ▸ hbB)
    (Cb := 4 * cpG hst hpre hm W + 6000 * (W + 20)) fun nv hnv hnW => ?_).mono
    (by omega) fun _ h => h
  subst hnv
  set nv := Val.list (gs'.map encPerm) with hnv
  have h2 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? =
      some (.list [.list ks, u]) := fun _ => rfl
  have dC := Det.length (cp_rdI (P := Pg) (h2 [gv, nv]) hwW hi0 (j := 0) rfl (by omega))
  have dK := Det.mk2 (cp_rdKs (P := Pg) (h2 [gv, nv]) hwW)
    (Det.rv (P := Pg) (env := [.list [.list ks, u], gv, nv]) (i := 2) rfl hnW)
  have hasl : as.length < W := by
    have := length_lt_wt_list (as.map encPerm); rw [List.length_map] at this; omega
  have hKW : (Val.list [.list ks, nv]).wt ≤ 4 * Bw := by rw [← hsv]; exact hargB
  have hmapl : (as.map encPerm).length = as.length := List.length_map _
  refine (CpEB.ite dC (Ct := 2 * cpG hst hpre hm W + 5010 * (W + 20))
    (Ce := 2 * cpG hst hpre hm W + 810 * (W + 20)) ?_ ?_).mono (by omega) fun _ h => h
  · intro hne0
    rcases as with _ | ⟨a', as'⟩
    · exact absurd rfl hne0
    have hin' : CpInLen k L.q D (cpInnerV as' (stageGens (dn ++ [(a, o)])) hs dv
        (incl.map (domPos e L.q)) a') := by
      refine ⟨as', _, hs, fd, _, a', by rw [hfd], ?_, hhs, hfd1, by simpa using hincl⟩
      rw [cp_stageGens_snoc, List.length_append]
      simp only [List.length_cons] at hglen
      have : (as'.length + 1 + 1) * (k ^ 2 + 1) = (as'.length + 1) * (k ^ 2 + 1) + (k ^ 2 + 1) := by
        ring
      omega
    have hN := cp_next_spec hst hpre hm hat ctx hBw hW hm' hmf hM hNT hR ht hne hl hG ho hacc hgv'
      hdv hnd hinc hao hT hlen hin' hargB
    exact CpEB.call (CpEB.det dK le_rfl (by omega) (Q := fun v => v = .list [.list ks, nv]) rfl)
      (fun v hv _ => hv ▸ hN) |>.mono (by omega) fun _ h => h
  · intro h0'
    have has : as = [] := List.eq_nil_of_length_eq_zero (by rw [← hmapl]; exact h0')
    subst has
    have hC := cp_close_spec hst hpre hm hat hjpre ctx hBw hW hm' hmf hM hNT hlen hT hWI0 hl hG ho
      hacc hnd hinc hao hargB
    exact CpEB.call (CpEB.det dK le_rfl (by omega) (Q := fun v => v = .list [.list ks, nv]) rfl)
      (fun v hv _ => hv ▸ hC) |>.mono (by omega) fun _ h => h

end Win

end GI.Impl
