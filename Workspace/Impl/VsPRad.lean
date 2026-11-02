import Workspace.Impl.VsPDesc
import Workspace.Impl.VsWProgImg

/-!
# The radical stage

On `[pc, rc, r]`: the Gram rows `us` are the keys of the generators `g_i` (row `i` holds
`dl(g_i, g_j)`); `K = vsWKer r us` are the relations among the rows; the program looks for a
relation `t` whose word `∏ g_i^{t_i}` is outside `L`. It returns `[1, z]` with that word `z`,
or `[0, 1]` if there is none (`vsPRad_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- The test on values: is the word of the relation outside `L`. -/
noncomputable def vsPRQV (ib : Perm (Fin I.n) → Bool) (gs : List (Perm (Fin I.n))) (v : Val) : Bool := by
  classical exact decide (∃ a : List ℕ, v = natList a ∧ vsPQN ib (encPerm (vsPW gs a)) = true)

theorem vsPRQV_enc (ib : Perm (Fin I.n) → Bool) (gs : List (Perm (Fin I.n))) (a : List ℕ) :
    vsPRQV ib gs (natList a) = vsPQN ib (encPerm (vsPW gs a)) := by
  unfold vsPRQV
  cases h : vsPQN ib (encPerm (vsPW gs a))
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro a' e h'
    rw [← vsQ_natList_injective e, h] at h'; exact Bool.false_ne_true h'
  · simp only [decide_eq_true_eq]; exact ⟨a, rfl, h⟩

/-- The Gram rows. -/
noncomputable def vsPGram (I : VecStabInst) (ws' cs : List (List ℕ)) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) : List (List ℕ) :=
  gs.map (vsPKey I ws' cs Zp gs)

/-- The index of the first relation whose word is outside `L`. -/
noncomputable def vsPRadJ (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (Zp : List (List (List ℕ))) (gs : List (Perm (Fin I.n))) (r : ℕ) : ℕ :=
  (vsWKer r (vsPGram I ws' cs Zp gs)).findIdx fun a => !vsPInLB I ws' cs rows (vsPW gs a)

/-- The value of the radical stage. -/
noncomputable def vsPRadV (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (Zp : List (List (List ℕ))) (gs : List (Perm (Fin I.n))) (r : ℕ) : Val :=
  if h : vsPRadJ I ws' cs rows Zp gs r < (vsWKer r (vsPGram I ws' cs Zp gs)).length then
    .list [.nat 1, encPerm (vsPW gs (vsWKer r (vsPGram I ws' cs Zp gs))[vsPRadJ I ws' cs rows Zp gs r])]
  else .list [.nat 0, encPerm (1 : Perm (Fin I.n))]

/-- On `[pc, rc, r]`: the radical stage. -/
def vsPRadE (gmp ker fnd word : ℕ) : Expr :=
  .letE (.call gmp (mk2 (arg 0) (.get (arg 0) (.nat 1))))
    (.letE (.call ker (mk2 (arg 2) (.var 1)))
      (.letE (.call fnd (mk2 (arg 1) (.var 2)))
        (.ite (.arith .lt (.var 3) (.length (.var 2)))
          (mk2 (.nat 1) (.call word (mk3 (mk3 (.get (arg 1) (.nat 1)) (.get (.var 2) (.var 3))
            (.get (arg 1) (.nat 2))) (.get (arg 1) (.nat 3)) (.get (arg 1) (.nat 2)))))
          (mk2 (.nat 0) (.get (arg 1) (.nat 2))))))

/-- The cost of the radical stage. -/
def vsPRadCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) * vsPKeyCost Cφ N W + 4 * 10 ^ 7 * (N + 1) ^ 5 + (N + 1) * vsPRadPredCost Cφ N W +
    vsPWordCost I.n N + 10 ^ 5 * (N + 1) * (W + 100 * (N + 1) ^ 3)

set_option maxHeartbeats 4000000 in
theorem vsPRad_spec {P : Program} {f gmp ker fnd rp word pow : ℕ} {x : VsPDX}
    (hf : P.funs[f]? = some (vsPRadE gmp ker fnd word)) (L : VsPDLay P x)
    (hgmp : P.HasAt gmp (mapFuns gmp x.o.key)) (hker : P.HasAt ker (vsWKerFuns ker))
    (hfnd : P.HasAt fnd (findFuns fnd rp)) (hrp : P.funs[rp]? = some (vsPRadPredE word x.nt))
    (hword : P.HasAt word (vsPWordFuns word x.o.comp pow)) (hpow : P.HasAt pow (vsPPowFuns pow))
    {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    (D : VsPOD I N W ws' cs rows hs gs Zp cap hs1 F r) (hr1 : 1 < r)
    (hrc : (vsPRc I ws' cs rows hs gs).wt ≤ W)
    (hfit : ∀ g ∈ gs, (∀ a ∈ vsPKey I ws' cs Zp gs g, a < r) ∧
      (vsPKey I ws' cs Zp gs g).length = gs.length) :
    FunDet P f (.list [vsPPc I ws' cs rows hs gs Zp, vsPRc I ws' cs rows hs gs, .nat r])
      (vsPRadV I ws' cs rows Zp gs r) (vsPRadCost (I := I) Cφ N W) := by
  have hn := D.H.n
  set pc := vsPPc I ws' cs rows hs gs Zp
  set rc := vsPRc I ws' cs rows hs gs
  set C := vsPCtx I ws' cs rows hs
  set ib := vsPInLB I ws' cs rows
  set us := vsPGram I ws' cs Zp gs with hus
  set K := vsWKer r us with hK
  have hfitU : VsWFit r gs.length us := by
    intro u hu
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hu
    exact hfit g hg
  have hul : us.length ≤ N := by rw [hus, vsPGram, List.length_map]; exact D.hgl
  have hKfit : VsWFit r us.length K := vsWKer_fit hr1 hfitU
  have hKl : K.length ≤ N := (vsWKer_length_le hr1 D.hrN D.hgl hfitU hul).trans hul
  have hlen : us.length = gs.length := by rw [hus, vsPGram, List.length_map]
  set vs := [pc, rc, Val.nat r]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  -- the Gram rows
  have dgs : Det P [Val.list vs] (.get (arg 0) (.nat 1)) (.list (gs.map encPerm)) _ :=
    Det.get' a0 (Det.nat 1) rfl
  have hmap := vsQ_map hgmp (c := pc) gs encPerm (fun g => natList (vsPKey I ws' cs Zp gs g))
    encPerm_injective (B := vsPKeyCost Cφ N W) fun g hg =>
      vsPKey_spec L.L.hkey L.L.hmp L.L.hit L.L.hcomm L.L.hcomp L.L.hinv L.L.hloc L.L.hwl L.L.hfd'
        L.L.heq hphi D.H D.hZ D.hZl D.hpc D.hgs D.hgl (D.hgs g hg)
  have eG : Val.list (gs.map fun g => natList (vsPKey I ws' cs Zp gs g)) = vsWVs us := by
    rw [hus, vsPGram, vsWVs, List.map_map]; rfl
  rw [eG] at hmap
  have dG := Det.call (Det.mk2 a0 dgs) hmap
  -- the relations
  have b2 := Det.arg' (P := P) (vs := vs) (rest := [vsWVs us]) (j := 2) rfl
  have bv := Det.var' (P := P) (env := [Val.list vs, vsWVs us]) (i := 1) rfl
  have dK := Det.call (Det.mk2 b2 bv) (vsWKer_spec hker hr1 D.hrN D.hgl hfitU hul)
  -- the search
  have c1 := Det.arg' (P := P) (vs := vs) (rest := [vsWVs us, vsWVs K]) (j := 1) rfl
  have cv := Det.var' (P := P) (env := [Val.list vs, vsWVs us, vsWVs K]) (i := 2) rfl
  have hpred : ∀ v ∈ K.map natList, FunDet P rp (.list [rc, v]) (boolVal (vsPRQV ib gs v))
      (vsPRadPredCost Cφ N W) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    rw [vsPRQV_enc]
    have haf := hKfit a ha
    exact vsPRadPred_spec hrp hword L.L.hcomp hpow L.hnt L.hinl hphi D.H D.hgs D.hgl hrc
      (by rw [haf.2, hlen]) (fun y hy => (haf.1 y hy).le.trans D.hrN)
  set X := N * vsPRadPredCost Cφ N W + loopModK * (N + 1) *
    ((Val.list [rc, Val.list (K.map natList)]).wt + 2 * N + 3)
  have hF' : FunAll P fnd (.list [rc, Val.list (K.map natList)]) (fun w c =>
      w = .nat ((K.map natList).findIdx (vsPRQV ib gs)) ∧ c ≤ X) := by
    refine (find_spec hfnd hpred).mono fun w c h => ⟨h.1, ?_⟩
    have h2 := h.2
    have e1 : ((K.map natList).map (fun _ => vsPRadPredCost Cφ N W)).sum =
        K.length * vsPRadPredCost Cφ N W := by
      rw [List.map_map]
      have : ((fun _ => vsPRadPredCost Cφ N W) ∘ natList : List ℕ → ℕ) =
        fun _ => vsPRadPredCost Cφ N W := rfl
      rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
    rw [e1] at h2
    simp only [List.length_map] at h2
    have h4 := Nat.mul_le_mul_right (vsPRadPredCost Cφ N W) hKl
    have h3 : loopModK * (K.length + 1) * ((Val.list [rc, Val.list (K.map natList)]).wt +
        2 * K.length + 3) ≤ loopModK * (N + 1) *
        ((Val.list [rc, Val.list (K.map natList)]).wt + 2 * N + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega
  have eKV : vsWVs K = Val.list (K.map natList) := rfl
  rw [eKV] at cv dK
  have dF := Det.call (Det.mk2 c1 cv) hF'
  have hj : (K.map natList).findIdx (vsPRQV ib gs) = vsPRadJ I ws' cs rows Zp gs r := by
    rw [vsP_findIdx_map]; unfold vsPRadJ; congr 1; funext a
    simp only [Function.comp, vsPRQV_enc, vsPQN_enc]
    rfl
  rw [hj] at dF
  set j := vsPRadJ I ws' cs rows Zp gs r
  set E3 := [Val.list vs, vsWVs us, Val.list (K.map natList), Val.nat j]
  have t3 := Det.var' (P := P) (env := E3) (i := 3) rfl
  have t2 := Det.var' (P := P) (env := E3) (i := 2) rfl
  have tt := Det.arith' (op := .lt) t3 (Det.length t2) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := [vsWVs us, Val.list (K.map natList), Val.nat j])
    (j := 1) rfl
  have g1 : Det P E3 (.get (arg 1) (.nat 1)) (.list (gs.map encPerm)) _ := Det.get' d1 (Det.nat 1) rfl
  have g2 : Det P E3 (.get (arg 1) (.nat 2)) (encPerm (1 : Perm (Fin I.n))) _ :=
    Det.get' d1 (Det.nat 2) rfl
  have g3 : Det P E3 (.get (arg 1) (.nat 3)) (.nat gs.length) _ := Det.get' d1 (Det.nat 3) rfl
  -- weights
  have wrc : rc.wt ≤ W := hrc
  have wvsl := wt_list3_le pc rc (Val.nat r)
  have evs : (Val.list vs).wt = (Val.list [pc, rc, Val.nat r]).wt := rfl
  have wpc : pc.wt ≤ W := D.hpc
  have wr := wt_nat_le r
  have hrN := D.hrN
  have hKB : VsWBnd N K := fun u hu => ⟨fun y hy => ((hKfit u hu).1 y hy).le.trans hrN,
    by rw [(hKfit u hu).2]; exact hul⟩
  have wK : (vsWVs K).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsWVs_le hKB (by omega)
  have wK' : (Val.list (K.map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 := wK
  have hUB : VsWBnd N us := fun u hu => ⟨fun y hy => ((hfitU u hu).1 y hy).le.trans hrN,
    by rw [(hfitU u hu).2]; exact D.hgl⟩
  have wU : (vsWVs us).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsWVs_le hUB (by omega)
  have wj := wt_nat_le j
  have hjK : j ≤ K.length := List.findIdx_le_length
  have wenc : ∀ g : Perm (Fin I.n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le g).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have wgs : (Val.list (gs.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := vsP_wt_perms hn gs (by have := D.hgl; omega)
  have wgl := wt_nat_le gs.length
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hgl := D.hgl
  set B0 := vsPWordCost I.n N + 100 * W + 10 ^ 4 * (N + 1) ^ 3
  have dI := Det.ite (v := vsPRadV I ws' cs rows Zp gs r) tt (ct := B0) (ce := B0)
    (fun hx => by
      have hlt : j < K.length := by
        simp only [BinOp.eval, List.length_map] at hx; split_ifs at hx with h <;> omega
      have hKj := hKfit K[j] (List.getElem_mem hlt)
      have dKa : Det P E3 (.get (.var 2) (.var 3)) (natList K[j]) _ :=
        Det.get' t2 t3 (by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl)
      have dw := Det.call (Det.mk3 (Det.mk3 g1 dKa g2) g3 g2)
        (vsPWord_spec hword L.L.hcomp hpow hn (by rw [hKj.2, hlen]) D.hgl
          (fun y hy => (hKj.1 y hy).le.trans hrN))
      have dm := Det.mk2 (Det.nat (P := P) (env := E3) 1) dw
      have hV : vsPRadV I ws' cs rows Zp gs r =
          .list [.nat 1, encPerm (vsPW gs K[j])] := by
        unfold vsPRadV; rw [dif_pos hlt]
      rw [hV]
      refine dm.mono ?_
      have wKj : (natList K[j]).wt ≤ (Val.list (K.map natList)).wt :=
        (wt_le_wt_list (List.mem_map.2 ⟨K[j], List.getElem_mem hlt, rfl⟩)).le
      have := wenc (vsPW gs K[j])
      have := wt_list2_le (Val.nat 1) (encPerm (vsPW gs K[j]))
      have := wt_list3_le (Val.list (gs.map encPerm)) (natList K[j]) (encPerm (1 : Perm (Fin I.n)))
      have := wt_list3_le (Val.list [Val.list (gs.map encPerm), natList K[j],
        encPerm (1 : Perm (Fin I.n))]) (Val.nat gs.length) (encPerm (1 : Perm (Fin I.n)))
      have := wenc 1
      have := wt_nat_le 1
      omega)
    (fun hx => by
      have hge : ¬ j < K.length := by
        simp only [BinOp.eval, List.length_map] at hx; split_ifs at hx with h <;> omega
      have hV : vsPRadV I ws' cs rows Zp gs r = .list [.nat 0, encPerm (1 : Perm (Fin I.n))] := by
        unfold vsPRadV; rw [dif_neg hge]
      rw [hV]
      refine (Det.mk2 (Det.nat (P := P) (env := E3) 0) g2).mono ?_
      have := wenc 1
      have := wt_list2_le (Val.nat 0) (encPerm (1 : Perm (Fin I.n)))
      have := wt_nat_le 0
      omega)
  rw [max_self] at dI
  have dAll := Det.letE dG (Det.letE dK (Det.letE dF dI))
  refine FunDet.intro hf (dAll.mono ?_)
  have wV : (vsPRadV I ws' cs rows Zp gs r).wt ≤ 20 * (N + 1) ^ 2 := by
    have wl : ∀ (b : ℕ) (z : Perm (Fin I.n)), b ≤ 1 →
        (Val.list [Val.nat b, encPerm z]).wt ≤ 20 * (N + 1) ^ 2 := by
      intro b z hb
      have := wt_list2_le (Val.nat b) (encPerm z); have := wenc z; have := wt_nat_le b; omega
    unfold vsPRadV
    split_ifs
    · exact wl 1 _ le_rfl
    · exact wl 0 _ (Nat.zero_le 1)
  have wpg := wt_list2_le pc (Val.list (gs.map encPerm))
  have wb := wt_list2_le (Val.nat r) (vsWVs us)
  have wc := wt_list2_le rc (Val.list (K.map natList))
  have hlt1 : BinOp.eval .lt j (K.map natList).length ≤ 1 := by
    simp only [BinOp.eval]; split_ifs <;> omega
  have wlt := wt_nat_le (BinOp.eval .lt j (K.map natList).length)
  have hKl' : (K.map natList).length ≤ N := by rw [List.length_map]; exact hKl
  set Y := (N + 1) * (W + 100 * (N + 1) ^ 3)
  have hY1 : W + 100 * (N + 1) ^ 3 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hM : mapK * (gs.length + 1) * ((Val.list [pc, Val.list (gs.map encPerm)]).wt +
      (vsWVs us).wt + 1) ≤ 1000 * (2 * Y) := by
    have hA : (Val.list [pc, Val.list (gs.map encPerm)]).wt + (vsWVs us).wt + 1 ≤
        2 * (W + 100 * (N + 1) ^ 3) := by omega
    have e1 : (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) = 2 * Y := by simp only [Y]; ring
    calc mapK * (gs.length + 1) * ((Val.list [pc, Val.list (gs.map encPerm)]).wt +
          (vsWVs us).wt + 1) ≤ mapK * (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hA
      _ = 1000 * (2 * Y) := by rw [mul_assoc, e1]; rfl
  have hX : loopModK * (N + 1) * ((Val.list [rc, Val.list (K.map natList)]).wt + 2 * N + 3) ≤
      1000 * (2 * Y) := by
    have hA : (Val.list [rc, Val.list (K.map natList)]).wt + 2 * N + 3 ≤
        2 * (W + 100 * (N + 1) ^ 3) := by omega
    have e1 : (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) = 2 * Y := by simp only [Y]; ring
    calc loopModK * (N + 1) * ((Val.list [rc, Val.list (K.map natList)]).wt + 2 * N + 3)
        ≤ loopModK * (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) := Nat.mul_le_mul_left _ hA
      _ = 1000 * (2 * Y) := by rw [mul_assoc, e1]; rfl
  have hGK : gs.length * vsPKeyCost Cφ N W ≤ (N + 1) * vsPKeyCost Cφ N W :=
    Nat.mul_le_mul_right _ (by omega)
  have hNP : N * vsPRadPredCost Cφ N W ≤ (N + 1) * vsPRadPredCost Cφ N W :=
    Nat.mul_le_mul_right _ (by omega)
  have eY : 10 ^ 5 * (N + 1) * (W + 100 * (N + 1) ^ 3) = 10 ^ 5 * Y := by rw [mul_assoc]
  unfold vsPRadCost
  rw [eY]
  omega

end GI.Impl
