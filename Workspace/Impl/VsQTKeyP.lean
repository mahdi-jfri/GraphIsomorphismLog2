module

public import Workspace.Impl.VsQTLows

@[expose] public section

/-!
# The key of a tuple given by local bases

On `[[p, D], P]` the item returns `1 :: key(span P)` flattened (the marked key `vsQTKeyM`).

* `vsQTKeyItemE`, `vsQTKeyItem_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved

variable {I : VecStabInst}

/-- The marked key of the span of `P`, on `[[p, D], P]`. -/
def vsQTKeyItemE (key cat appd : ℕ) : Expr :=
  .call appd (mk2 (mk1 (.nat 1)) (.call cat (.call key (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (arg 1)))))

/-- The layout of the key item. -/
structure VsQTKeyItemAt (P : Program) (f key cat appd : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQTKeyItemE key cat appd)
  hkey : P.HasAt key (vsWKeyFuns key)
  hcat : P.HasAt cat (vsWFlatFuns cat)
  happd : P.HasAt appd (appendFuns appd)

theorem vsWKey_span_eq {s : VsQSt I} {P' : List (List ℕ)} (hP : VsWFit I.p (vsQD s) P') :
    vsWKey I.p (vsQD s) P' = vsQTKeyU (vsWSp I.p (vsQD s) P') :=
  (vsWKey_eq_iff I.prime hP (vsQTBas_fit _)).2 (by rw [vsQTBas_span])

set_option maxHeartbeats 8000000 in
theorem vsQTKeyItem_spec {P : Program} {f key cat appd : ℕ} (H : VsQTKeyItemAt P f key cat appd)
    {s : VsQSt I} {N : ℕ} (hpN : I.p ≤ N) (hDN : vsQD s * vsQD s + 1 ≤ N) {P' : List (List ℕ)}
    (hP : VsWFit I.p (vsQD s) P') (hl : P'.length ≤ N) :
    FunDet P f (.list [.list [.nat I.p, .nat (vsQD s)], vsWVs P'])
      (natList (vsQTKeyM (vsWSp I.p (vsQD s) P'))) (10 ^ 9 * (N + 1) ^ 6) := by
  have hp1 := I.prime.one_lt
  have hDN' : vsQD s ≤ N := by nlinarith
  set c := Val.list [.nat I.p, .nat (vsQD s)]
  set X := Val.list [c, vsWVs P']
  have rc : ∀ k v, [Val.nat I.p, .nat (vsQD s)][k]? = some v → Det P [X] (.get (arg 0) (.nat k)) v _ :=
    fun k v hv => Det.get' (Det.arg' (P := P) (rest := []) (vs := [c, vsWVs P']) (j := 0) rfl) (Det.nat k) hv
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, vsWVs P']) (j := 1) rfl
  have dkey := Det.call (Det.mk3 (rc 0 _ rfl) (rc 1 _ rfl) g1) (vsWKey_spec H.hkey hp1 hpN hDN' hP hl)
  rw [vsWKey_span_eq hP] at dkey
  set K := vsQTKeyU (vsWSp I.p (vsQD s) P')
  have hK : VsWFit I.p (vsQD s) K := vsWKey_fit hp1 _
  have hKl : K.length = vsQD s := vsWKey_length _ _
  have hKf : K.flatten.length = vsQD s * vsQD s := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => vsQD s) fun r hr => (hK r hr).2]
    simp [hKl]
  have e1 : Val.list ((K.map fun r => r.map Val.nat).map Val.list) = vsWVs K := by
    simp [vsWVs, natList, List.map_map, Function.comp_def]
  rw [← e1] at dkey
  have wKf : (natList K.flatten).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      exact ((hK r hr).1 y hy).le.trans hpN) (by omega)
  have wK := wt_vsWVs_le (VsWFit.bnd hK hpN hDN') (by omega)
  have q24 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q04 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have dcat := Det.call dkey (vsWConcat_spec H.hcat (N := N) (K.map fun r => r.map Val.nat) (by simp; omega)
      (fun xs hxs => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hxs
        simp [(hK r hr).2]; omega)
      (by rw [vsQT_flatten_natList]; omega) (by rw [e1]; omega))
  rw [vsQT_flatten_natList] at dcat
  have kap : FunDet P appd (.list [.list [.nat 1], natList K.flatten]) (natList (1 :: K.flatten))
      (10 ^ 6 * (N + 1) ^ 3) := by
    refine (append_spec H.happd [.nat 1] (K.flatten.map Val.nat)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have w2 := wt_list2_le (.list [.nat 1]) (natList K.flatten)
    have w1 : (Val.list [.nat 1]).wt ≤ 10 := by decide
    have wo : (natList (1 :: K.flatten)).wt ≤ 5 * (N + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
          exact ((hK r hr).1 y hy).le.trans hpN) (by rw [List.length_cons, hKf]; omega)
    have e2' : (Val.list ([Val.nat 1] ++ K.flatten.map Val.nat)).wt = (natList (1 :: K.flatten)).wt := rfl
    have e3 : (Val.list [Val.list [Val.nat 1], Val.list (K.flatten.map Val.nat)]).wt =
      (Val.list [.list [.nat 1], natList K.flatten]).wt := rfl
    have hll : (K.flatten.map Val.nat).length = vsQD s * vsQD s := by rw [List.length_map, hKf]
    have h4 : ((K.flatten.map Val.nat).length + 1) *
        ((Val.list [Val.list [Val.nat 1], Val.list (K.flatten.map Val.nat)]).wt +
          (K.flatten.map Val.nat).length + (Val.list ([Val.nat 1] ++ K.flatten.map Val.nat)).wt + 1) ≤
        (N + 1) * (100 * (N + 1) ^ 2) := Nat.mul_le_mul (by omega) (by
          have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
          omega)
    have e : (N + 1) * (100 * (N + 1) ^ 2) = 100 * (N + 1) ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * ((K.flatten.map Val.nat).length + 1) * _ = 1000 * (((K.flatten.map Val.nat).length + 1) *
          ((Val.list [Val.list [Val.nat 1], Val.list (K.flatten.map Val.nat)]).wt +
          (K.flatten.map Val.nat).length + (Val.list ([Val.nat 1] ++ K.flatten.map Val.nat)).wt + 1)) := by
            ring
      _ ≤ _ := by omega
  have dap := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := [X]) 1)) dcat) kap
  refine FunDet.intro H.hf (dap.mono ?_)
  have wP := wt_vsWVs_le (VsWFit.bnd hP hpN hDN') (by omega)
  have wc := wt_list2_le (.nat I.p) (.nat (vsQD s))
  have wX := wt_list2_le c (vsWVs P')
  have w3 := wt_list3_le (.nat I.p) (.nat (vsQD s)) (vsWVs P')
  have := wt_nat_le I.p; have := wt_nat_le (vsQD s); have := wt_nat_le 0; have := wt_nat_le 1
  have w2 := wt_list2_le (.list [.nat 1]) (natList K.flatten)
  have w1 : (Val.list [.nat 1]).wt ≤ 10 := by decide
  have wo : (natList (1 :: K.flatten)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
        exact ((hK r hr).1 y hy).le.trans hpN) (by rw [List.length_cons, hKf]; omega)
  have eo : (natList (vsQTKeyM (vsWSp I.p (vsQD s) P'))).wt = (natList (1 :: K.flatten)).wt := rfl
  have eK : (Val.list ((K.map fun r => r.map Val.nat).map Val.list)).wt = (vsWVs K).wt := by rw [e1]
  have q56 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q46 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q36 : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q26 : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have ec : c.wt = (Val.list [.nat I.p, .nat (vsQD s)]).wt := rfl
  have eX : X.wt = (Val.list [c, vsWVs P']).wt := rfl
  clear_value c X K
  omega

end GI.Impl
