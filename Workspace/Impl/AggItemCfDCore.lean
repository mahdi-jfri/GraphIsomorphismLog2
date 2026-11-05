module

public import Workspace.Impl.AggItemCfDAtSpec

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

private theorem itCfD_core_k {P : Program} {dl tl : List ℕ} {q κ B : ℕ}
    (hA : (stDA dl tl q κ).wt ≤ B) (hk : κ ≤ B) (rest : List Val) :
    StDC P (stDA dl tl q κ :: rest) (.get (.var 0) (.nat 3))
      (.nat κ) 3 0 (100 * (B + 1)) := by
  have wk := wt_nat_le κ
  have gv := Det.var' (P := P) (env := stDA dl tl q κ :: rest) (i := 0) (v := stDA dl tl q κ) rfl
  have gg := Det.get' gv (Det.nat 3) (vs := [natList dl, natList tl, .nat q, .nat κ])
    (v := .nat κ) rfl
  exact gg.mono (by omega)

theorem itCfD_core_calls {P : Program} {f fh rb atf B : ℕ}
    (hf : P.funs[f]? = some (itCfDCoreF fh rb atf)) (dl tl : List ℕ) (q κ : ℕ)
    (hkl : κ < tl.length) (hA : (stDA dl tl q κ).wt ≤ B) (hk : κ ≤ B)
    (hrb : FunDet P rb (.nat κ) (natList (List.range κ)) B)
    (hfind : FunDet P fh (.list [stDA dl tl q κ, natList (List.range κ)])
      (.nat ((List.range κ).findIdx (stDHit dl tl q κ))) B)
    (hat : ∀ m < κ, FunDet P atf (.list [stDA dl tl q κ, .nat m])
      (itCfDAt dl tl q κ m) B) :
    FunDet P f (stDA dl tl q κ) (itCfDOut dl tl q κ) (10 ^ 5 * (B + 1)) := by
  set A := stDA dl tl q κ
  set m := (List.range κ).findIdx (stDHit dl tl q κ)
  have hm : m ≤ κ := by simpa [m] using (List.findIdx_le_length (p := stDHit dl tl q κ)
    (xs := List.range κ))
  set W := 100 * (B + 1)
  have wk := wt_nat_le κ
  have wm := wt_nat_le m
  have wr := hrb.wt_lt
  have wa := wt_list2_le A (natList (List.range κ))
  have wai := wt_list2_le A (.nat m)
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have g0 (rest : List Val) : StDC P (A :: rest) (.var 0) A 1 0 W :=
    StDC.var' rfl (by dsimp [W]; change A.wt ≤ B at hA; omega)
  have gk (rest : List Val) : StDC P (A :: rest) (.get (.var 0) (.nat 3)) (.nat κ) 3 0 W :=
    itCfD_core_k hA hk rest
  have gf := StDC.call (StDC.mk2 (g0 []) (StDC.call (gk []) hrb (by dsimp [W]; omega))
    (by dsimp [W]; omega) (by omega)) hfind (by dsimp [W]; omega)
  have gm : StDC P [A, .nat m] (.var 1) (.nat m) 1 0 W :=
    StDC.var' rfl (by dsimp [W]; omega)
  have gc := StDC.arith' gm (gk [.nat m]) (op := .lt) (z := BinOp.eval .lt m κ) rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  unfold itCfDOut
  rw [if_pos hkl]
  change FunDet P f A (if m < κ then _ else _) _
  by_cases hmk : m < κ
  · rw [if_pos hmk]
    have ha := hat m hmk
    have wo := ha.wt_lt
    have ga := StDC.call (StDC.mk2 (g0 [.nat m]) gm (by dsimp [W]; change A.wt ≤ B at hA; omega)
      (by omega)) ha (by dsimp [W]; omega)
    have hx : BinOp.eval .lt m κ ≠ 0 := by simp [BinOp.eval, hmk]
    have gi := StDC.ite (e := .snoc .nil (.nat 0)) (ne := 0) (Ee := 0) gc
      (fun _ => ga) (fun h => absurd h hx) (by dsimp [W]; omega)
    exact StDC.funDet hf (StDC.letE gf gi (by show (itCfDAt dl tl q κ m).wt ≤ W; dsimp [W]; omega)) (by dsimp [W]; omega)
  · rw [if_neg hmk]
    have gn : StDC P [A, .nat m] (.snoc .nil (.nat 0)) (.list [.nat 0]) 3 0 W :=
      StDC.snoc (StDC.nil (by omega)) (StDC.nat 0 (by omega))
        (by
          have hw : (Val.list [Val.nat 0]).wt = 9 := by decide
          change (Val.list [Val.nat 0]).wt ≤ W
          dsimp [W]
          omega)
    have wo : (Val.list [Val.nat 0]).wt ≤ W := by
      have hw : (Val.list [Val.nat 0]).wt = 9 := by decide
      dsimp [W]; omega
    have hx : BinOp.eval .lt m κ = 0 := by simp [BinOp.eval, hmk]
    have gi := StDC.ite (t := .call atf (mk2 (.var 0) (.var 1))) (nt := 0) (Et := 0) gc
      (fun h => absurd hx h) (fun _ => gn) wo
    exact StDC.funDet hf (StDC.letE gf gi wo) (by dsimp [W]; omega)

/-- The scan budget includes all prefix tests and the one object readout. -/
def itCfDCoreBudget (N : ℕ) : ℕ := 10 ^ 70 * (N + 1) ^ 17

theorem itCfD_core_find_budget {N κ : ℕ} (hk : κ ≤ N) :
    κ * (stDHitK * (4 * N + 10 + 1) ^ 16) +
      loopModK * (20 * (N + 1) ^ 2 + 1) * (3 * (20 * (N + 1) ^ 2) + 3) ≤
      itCfDCoreBudget N := by
  have hp2 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hh := Nat.mul_le_mul (show κ ≤ N + 1 by omega)
    (Nat.mul_le_mul_left stDHitK (Nat.pow_le_pow_left
      (show 4 * N + 10 + 1 ≤ 11 * (N + 1) by omega) 16))
  have he : (N + 1) * (stDHitK * (11 * (N + 1)) ^ 16) =
      (stDHitK * 11 ^ 16) * (N + 1) ^ 17 := by ring
  have h1 := hh.trans_eq he
  have h2 := st_mul3 (le_refl loopModK)
    (show 20 * (N + 1) ^ 2 + 1 ≤ 21 * (N + 1) ^ 2 by omega)
    (show 3 * (20 * (N + 1) ^ 2) + 3 ≤ 63 * (N + 1) ^ 2 by omega)
  have he2 : loopModK * (21 * (N + 1) ^ 2) * (63 * (N + 1) ^ 2) =
      (loopModK * 21 * 63) * (N + 1) ^ 4 := by ring
  have h2' := (h2.trans_eq he2).trans (itCfD_cost_mono N (a := loopModK * 21 * 63)
    (b := loopModK * 21 * 63) le_rfl (show 4 ≤ (17 : ℕ) by norm_num))
  calc _ ≤ (stDHitK * 11 ^ 16 + loopModK * 21 * 63) * (N + 1) ^ 17 := by
        simpa only [Nat.add_mul] using Nat.add_le_add h1 h2'
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num [stDHitK, loopModK, itCfDCoreBudget])

theorem itCfD_core_at_budget (N : ℕ) :
    10 ^ 50 * (4 * N + 10 + 1) ^ 8 ≤ itCfDCoreBudget N := by
  have hh := Nat.mul_le_mul_left (10 ^ 50) (Nat.pow_le_pow_left
    (show 4 * N + 10 + 1 ≤ 11 * (N + 1) by omega) 8)
  have he : 10 ^ 50 * (11 * (N + 1)) ^ 8 = (10 ^ 50 * 11 ^ 8) * (N + 1) ^ 8 := by ring
  exact (hh.trans_eq he).trans (itCfD_cost_mono N (b := 10 ^ 70) (by norm_num [itCfDCoreBudget]) (by norm_num : 8 ≤ (17 : ℕ)))

/-- The prefix scan runs the paper's hit test and returns its first object's value. -/
theorem itCfD_core_spec {P : Program} {I : ItCfDIdx} (h : ItCfDOk P I)
    {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) {N : ℕ}
    (hN : (stDA dl tl q κ).wt ≤ N) :
    FunDet P I.core (stDA dl tl q κ) (itCfDOut dl tl q κ) (10 ^ 80 * (N + 1) ^ 17) := by
  have hk : κ ≤ N := by have := hc.le_wt.2.1; omega
  have hAi : ∀ i ≤ κ, (Val.list [stDA dl tl q κ, .nat i]).wt ≤ 4 * N + 10 := by
    intro i hi
    have := wt_list2_le (stDA dl tl q κ) (.nat i)
    have := wt_nat_le i
    omega
  have hh : ItCfDHitOK P I.hit := itCfD_hit_ok h.hit h.hit2 h.ad h.dv h.dvv h.cb h.rb
    (itCfD_split_ok h.sp h.fd h.dv h.dvv h.cb h.fr h.rf h.adr h.df h.rb h.cf h.hor)
    h.vm h.vmap h.vf h.cf h.hor
  have hp2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have wrange : (natList (List.range κ)).wt ≤ 5 * (N + 1) ^ 2 := by
    have hw := wt_natList_le_sq (xs := List.range κ) (B := κ)
      (fun x hx => (List.mem_range.1 hx).le) (by simp)
    exact hw.trans (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (by omega) 2))
  have wsearch : (Val.list [stDA dl tl q κ, natList (List.range κ)]).wt ≤
      20 * (N + 1) ^ 2 := by
    have := wt_list2_le (stDA dl tl q κ) (natList (List.range κ)); omega
  have hfind := st_find_det h.fh (c := stDA dl tl q κ) (n := κ) (t := stDHit dl tl q κ)
    (fun i hi => hh hc hi.le (hAi i hi.le)) wsearch (by omega)
  have hfindB := hfind.mono (itCfD_core_find_budget hk)
  have hrangeB := (st_range_det h.rb κ).mono
    ((Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left (show κ + 1 ≤ N + 1 by omega) 3)).trans
      (itCfD_cost_mono N (b := 10 ^ 70) (by norm_num [itCfDCoreBudget]) (by norm_num : 3 ≤ (17 : ℕ))))
  have hatB : ∀ m < κ, FunDet P I.atf (.list [stDA dl tl q κ, .nat m])
      (itCfDAt dl tl q κ m) (itCfDCoreBudget N) := fun m hm =>
    (itCfD_at_spec h hc m (hAi m hm.le)).mono (itCfD_core_at_budget N)
  have hp : N + 1 ≤ (N + 1) ^ 17 := Nat.le_self_pow (by norm_num) _
  have hp0 : 1 ≤ (N + 1) ^ 17 := Nat.one_le_pow _ _ (by omega)
  have hNB : N ≤ itCfDCoreBudget N := by unfold itCfDCoreBudget; omega
  have hs := itCfD_core_calls h.core dl tl q κ hc.len_tl (hN.trans hNB) (hk.trans hNB)
    hrangeB hfindB hatB
  exact hs.mono (by unfold itCfDCoreBudget; omega)

end GI.Impl
