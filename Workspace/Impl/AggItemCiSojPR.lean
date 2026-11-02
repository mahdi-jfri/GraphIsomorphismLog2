import Workspace.Impl.AggItemCiSojGW

/-!
# Processing a physical query answer

An empty answer remains empty. For a nonempty answer, project the representative
and the full source generators through the stored homomorphism, then multiply
the representative by the target twist. The projected source group stays fixed.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

/-- Nonempty-answer processing after the length guard. -/
def itcsProjectBody (pi gm cmp : ℕ) : Expr :=
  .letE (.call pi (mk2 (arg 0) (.get (arg 1) (.nat 0))))
    (.letE (.call gm (mk3 (arg 0) (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 0))))
      (.letE (.call cmp (mk2 (arg 2) (.var 1))) (mk2 (.var 3) (.var 2))))

/-- On `[swapped lift context, canonical answer, target twist]`, return the
projected answer representative and encoded group, or `[]`. -/
def itcsProjectF (pi gm cmp : ℕ) : Expr :=
  .ite (.length (arg 1)) (itcsProjectBody pi gm cmp) .nil

/-- A budget for all intermediate answer encodings. -/
def itcsProjectW (k q : ℕ) (ctx gv out : Val) : ℕ :=
  1000 * (ctx.wt + gv.wt + out.wt + (k + q + 1) ^ 2 + 10)

set_option maxHeartbeats 400000 in
/-- The actual nonempty-answer projector, with all wrapper weights discharged. -/
theorem itcs_project_spec {Pg : Program} {f pi gm cmp k q Cpi Cgm : ℕ}
    (hf : Pg.funs[f]? = some (itcsProjectF pi gm cmp))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (vs : List Val) (hq : vs[0]? = some (.nat q))
    (x : Perm (Fin k)) (y t : Perm (Fin q)) (gs : List (Perm (Fin k))) (ts : List (Perm (Fin q)))
    (hp : FunDet Pg pi (.list [.list vs, encPerm x]) (encPerm y) Cpi)
    (hg : FunDet Pg gm (.list [.list vs, encGroup gs, .nat q]) (encGroup ts) Cgm) :
    FunDet Pg f (.list [.list vs, .list [encPerm x, encGroup gs], encPerm t])
      (.list [encPerm (t * y), encGroup ts])
      (100 * (itcsProjectW k q (.list vs) (encGroup gs) (encGroup ts) + 1) +
        Cpi + Cgm + permK * (q + 1) ^ 3) := by
  let ctx : Val := .list vs
  let u : Val := .list [encPerm x, encGroup gs]
  let inp : Val := .list [ctx, u, encPerm t]
  let Bw := itcsProjectW k q ctx (encGroup gs) (encGroup ts)
  have budget : 50 * ctx.wt + 50 * (encGroup gs).wt + 50 * (encGroup ts).wt +
      500 * (k + q + 1) ^ 2 + 1000 ≤ Bw := by dsimp only [Bw]; unfold itcsProjectW; omega
  have hpow : (k + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hpowq : (q + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hlin : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h1 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have wx := (wt_encPerm_le x).trans (Nat.mul_le_mul_left 4 hpow)
  have wy := (wt_encPerm_le y).trans (Nat.mul_le_mul_left 4 hpowq)
  have wt := (wt_encPerm_le t).trans (Nat.mul_le_mul_left 4 hpowq)
  have wty := (wt_encPerm_le (t * y)).trans (Nat.mul_le_mul_left 4 hpowq)
  have wu := wt_list2_le (encPerm x) (encGroup gs)
  have wi : inp.wt ≤ Bw := by have h := wt_list3_le ctx u (encPerm t); dsimp only [inp,u] at h ⊢; omega
  have wpi : (Val.list [ctx, encPerm x]).wt ≤ Bw := by have h := wt_list2_le ctx (encPerm x); omega
  have wgi : (Val.list [ctx, encGroup gs, .nat q]).wt ≤ Bw := by
    have h := wt_list3_le ctx (encGroup gs) (.nat q)
    have qn := wt_nat_le q
    omega
  have wci : (Val.list [encPerm t, encPerm y]).wt ≤ Bw := by have h := wt_list2_le (encPerm t) (encPerm y); omega
  have wo : (Val.list [encPerm (t*y), encGroup ts]).wt ≤ Bw := by
    have h := wt_list2_le (encPerm (t*y)) (encGroup ts)
    omega
  have get {rest : List Val} {i : ℕ} {v : Val} (hh : [ctx,u,encPerm t][i]? = some v)
      (hii : i + 2 ≤ Bw) : StDC Pg (inp :: rest) (arg i) v 3 0 Bw :=
    StDC.arg hh wi hii ((st_wt_mem (List.mem_of_getElem? hh)).trans wi)
  have wctx : ctx.wt ≤ Bw := by omega
  have wuv : u.wt ≤ Bw := by dsimp only [u]; omega
  have wlgs : (encGroup gs).wt ≤ Bw := by omega
  have ul0 (rest : List Val) := StDC.get (get (rest := rest) (i := 1) rfl (by omega))
    (StDC.nat 0 (by omega)) rfl (wx.trans (by omega))
  have ul1 (rest : List Val) := StDC.get (get (rest := rest) (i := 1) rfl (by omega))
    (StDC.nat 1 (by omega)) rfl wlgs
  have pc := StDC.call (StDC.mk2 (get (rest := []) (i := 0) rfl (by omega)) (ul0 []) wpi (by omega))
    hp (wy.trans (by omega))
  have qv := StDC.get (get (rest := [encPerm y]) (i := 0) rfl (by omega))
    (StDC.nat 0 (by omega)) hq ((wt_nat_le q).trans (by omega))
  have gc := StDC.call (StDC.mk3 (get (rest := [encPerm y]) (i := 0) rfl (by omega))
    (ul1 [encPerm y]) qv wgi (by omega)) hg (by omega)
  have yi : StDC Pg [inp, encPerm y, encGroup ts] (.var 1) (encPerm y) 1 0 Bw :=
    StDC.var' rfl (wy.trans (by omega))
  have tc := StDC.call (StDC.mk2 (get (rest := [encPerm y, encGroup ts]) (i := 2) rfl (by omega)) yi wci (by omega))
    (compose_spec hc t y) (wty.trans (by omega))
  have ty3 : StDC Pg [inp, encPerm y, encGroup ts, encPerm (t*y)] (.var 3) (encPerm (t*y)) 1 0 Bw :=
    StDC.var' rfl (wty.trans (by omega))
  have gs2 : StDC Pg [inp, encPerm y, encGroup ts, encPerm (t*y)] (.var 2) (encGroup ts) 1 0 Bw :=
    StDC.var' rfl (by omega)
  have result := StDC.mk2 ty3 gs2 wo (by omega)
  have nonempty := StDC.letE pc (StDC.letE gc (StDC.letE tc result wo) wo) wo
  have cond : StDC Pg [inp] (.length (arg 1)) (.nat 2) 4 0 Bw := StDC.length
    (get (rest := []) (i := 1) rfl (by omega)) (by simp only [List.length_cons,List.length_nil]; omega)
  have body := StDC.ite (e := .nil) (nt := 80) (ne := 1)
    (Et := Cpi + Cgm + permK * (q + 1) ^ 3) (Ee := 0) cond
    (fun _ => nonempty.mono (by omega) (by omega)) (fun h => by omega) wo
  clear budget hpow hpowq hlin h1 wx wy wt wty wu wi wpi wgi wci wo get wctx wuv wlgs ul0 ul1 pc qv gc yi tc ty3 gs2 result nonempty cond
  exact StDC.funDet hf body (by dsimp only [Bw, ctx] at *; omega)

/-- Empty canonical answers are processed without any group routine. -/
theorem itcs_project_empty {Pg : Program} {f pi gm cmp : ℕ} (ctx t : Val)
    (hf : Pg.funs[f]? = some (itcsProjectF pi gm cmp)) :
    FunDet Pg f (.list [ctx, .list [], t]) (.list [])
      (20 * ((Val.list [ctx, .list [], t]).wt + 10)) := by
  let Bw := (Val.list [ctx, .list [], t]).wt + 10
  have hin : (Val.list [ctx, .list [], t]).wt ≤ Bw := by omega
  have ga : StDC Pg [.list [ctx, .list [], t]] (arg 1) (.list []) 3 0 Bw :=
    StDC.arg rfl hin (by dsimp only [Bw]; omega)
      ((st_wt_mem (by simp)).trans hin)
  have gl : StDC Pg [.list [ctx, .list [], t]] (.length (arg 1)) (.nat 0) 4 0 Bw :=
    StDC.length ga (by change 0 + 2 ≤ Bw; dsimp only [Bw]; omega)
  have body := StDC.ite (t := itcsProjectBody pi gm cmp) (nt := 1) (ne := 1) (Et := 0) (Ee := 0) gl (fun h => by omega)
    (fun _ => StDC.nil (by dsimp only [Bw]; omega)) (by simp only [wt_list_nil]; dsimp only [Bw]; omega)
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

end GI.Impl
