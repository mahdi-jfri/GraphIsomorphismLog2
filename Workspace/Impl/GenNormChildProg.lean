import Workspace.Impl.GenEnum
import Workspace.Impl.GenNormModeCall

/-! # The recursive call on one normalization coset -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup)

/-- Compute the translated target, call the selected procedure, and retain its coset tag. -/
def normChildF (F : Funs) (bg : ℕ) : Expr :=
  .letE (.call bg (mk2 (ctxV 4) (arg 1)))
    (mk2 (arg 1) (normModeCall F (Expr.mkList
      [ctxV 0, .get (arg 0) (.nat 1), ctxV 2, ctxV 3, .var 1, .get (arg 0) (.nat 2), ctxV 6,
        ctxV 7, ctxV 8, ctxV 9]) (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 4))))

/-- Polynomial own cost of a normalization child call. -/
def normChildB (Z : ℕ) : ℕ := 10 ^ 12 * (Z + 1) ^ 4

set_option maxHeartbeats 2000000 in
/-- The recursive child is canonical, has `SmallInv`, and receives its exact supplied labels. -/
theorem normChild_spec (R : Rest) {Pg : Program} {F : Funs} {f bg : ℕ}
    (hf : Pg.funs[f]? = some (normChildF F bg)) (hga : Pg.HasAt bg (gatherFuns bg))
    {Ω C : Type} [Finite Ω] {k : ℕ} {e : Ω ≃ Fin k} {cc : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e cc (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (Q : PrimitiveQuotient S) (nc : Q.NormChoice) (htr : S.Transitive)
    (hq : P₀.q₀ < (Q.normalizationOf nc).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (j : Fin (Q.normAboveOf nc htr hq hkc hkl).I.k) (t : Perm (Fin k))
    (ht : nc.τ j = (toFin e).symm t) {Kv hv' lv : Val} (b : Bool)
    (hK : GroupValC k Kv (groupFin e (Q.normGroup nc.e nc.hS)))
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post))
    (hL : LabValStd e ((Q.normAboveOf nc htr hq hkc hkl).child j) lv
      ((Q.normAboveOf nc htr hq hkc hkl).childLabels j))
    (hcall : ∀ val, Canon e cc val ((Q.normAboveOf nc htr hq hkc hkl).child j) →
      FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
        (R.iface.Post (normMode b) ((Q.normAboveOf nc htr hq hkc hkl).child j) e
          (if b then .list [val, lv] else val))) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
        Kv, hv', lv, boolVal b], encPerm t])
      (fun w cost => (∃ u, w = .list [encPerm t, u] ∧
        AnsC e u ((Q.normAboveOf nc htr hq hkc hkl).child j).answer) ∧
        ∃ cb : ℕ, (∃ (A : Set (Perm Ω))
          (r : Run P₀ (normMode b) ((Q.normAboveOf nc htr hq hkc hkl).child j)
            ((normMode b).labels ((Q.normAboveOf nc htr hq hkc hkl).childLabels j)) A),
          (cb : ℝ) ≤ r.total R.iface.work) ∧
        cost ≤ normChildB (5 * (Val.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv,
          hh, .nat N], Kv, hv', lv, boolVal b], encPerm t]).wt + ansW k + 20 * (k + 1) ^ 2 + 10) + cb) := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, -, -, hyv, -, -, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -, -⟩ := heq
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set ctx := Val.list [v, Kv, hv', lv, boolVal b] with hctx
  set x := encPerm t with hx
  set a := Val.list [ctx, x] with ha
  let NN := Q.normAboveOf nc htr hq hkc hkl
  let T := NN.child j
  -- the target coloring after `t`
  set τ := (toFin e).symm t with hτ
  have htτ : toFin e τ = t := MulEquiv.apply_symm_apply _ _
  set yv' := encFun fun i => cc ((S.y ∘ τ) (e.symm i)) with hyv'
  have hyv0 : yv = .list ((List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i)))) := hyv
  have hg := gather_spec hga (L := (List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i))))
    (is := (List.finRange k).map fun i => (t i : ℕ)) (by simp)
  have hgy : (((List.finRange k).map fun i => (t i : ℕ)).map fun j =>
      ((List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i)))).getD j (.nat 0)) =
      (List.finRange k).map fun i => Val.nat (cc ((S.y ∘ τ) (e.symm i))) := by
    rw [← htτ]; exact gather_colors e cc S.y τ
  rw [hgy] at hg
  have hy' : ColorVal e cc yv' (S.y ∘ τ) := rfl
  have hyc : ∀ b, cc ((S.y ∘ τ) b) < 2 * k := fun b => (hcan.colors (τ b)).2
  have hcanT := normCanon_child hcan Q nc htr hq hkc hkl j hK
    (by rw [ht]; exact hy') hH
  have hcallT := hcall _ hcanT
  -- weights
  have wv : v.wt < ctx.wt := wt_le_wt_list (by simp)
  have wK : Kv.wt < ctx.wt := wt_le_wt_list (by simp)
  have wH : hv'.wt < ctx.wt := wt_le_wt_list (by simp)
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp)
  have wx : x.wt < a.wt := wt_le_wt_list (by simp)
  have wt : (encPerm t).wt = x.wt := rfl
  have wlv : lv.wt < ctx.wt := wt_le_wt_list (by simp)
  have wy : yv.wt < v.wt := wt_le_wt_list (by simp)
  have wyv' : yv'.wt ≤ 4 * (2 * k + 1) ^ 2 := by
    have := wt_encFun_le (fun i => cc ((S.y ∘ τ) (e.symm i))) (B := 2 * k)
      fun i => (hyc _).le
    nlinarith
  have ea : (Val.list [ctx, x]).wt = a.wt := rfl
  have ev : (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt = v.wt := rfl
  have ec : (Val.list [v, Kv, hv', lv, boolVal b]).wt = ctx.wt := rfl
  have ex : (encPerm t).wt = x.wt := rfl
  -- the entries of the state value
  have dctx : ∀ rest, Det Pg (a :: rest) (.get (arg 0) (.nat 0)) v (3 * a.wt + 10) := fun rest =>
    (Det.get' (Det.arg' (vs := [ctx, x]) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [v, Kv, hv', lv, boolVal b][0]? = some v from rfl)).mono (by omega)
  have dent : ∀ rest j (hj : j < 10), Det Pg (a :: rest) (ctxV j)
      [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j] (5 * a.wt + 30) := fun rest j hj => by
    have := wt_getElem_lt [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] j (by simpa using hj)
    exact (Det.get' (dctx rest) (Det.nat j) (List.getElem?_eq_getElem (by simpa using hj))).mono
      (by omega)
  have dt : ∀ rest, Det Pg (a :: rest) (arg 1) (encPerm t) (3 * a.wt + 10) :=
    fun rest => (Det.arg' (vs := [ctx, x]) (rest := rest) (j := 1) rfl).mono (by omega)
  -- gather
  have hgath := Det.call (Det.mk2 (dent [] 4 (by omega)) (dt [])) (by
    rw [hyv0, encPerm_eq_natList]; exact hg)
  refine FunAll.intro hf (EvalAll.letE hgath fun yw cy hyw => ?_)
  obtain ⟨rfl, hcy⟩ := hyw
  have hyw : Val.list ((List.finRange k).map fun i => Val.nat (cc ((S.y ∘ τ) (e.symm i)))) = yv' :=
    rfl
  rw [hyw] at hcy ⊢
  -- the child value
  have hval := Det.mkList (P := Pg) (env := [a, yv']) (c := 5 * a.wt + 30 + 5 * (k + 1) ^ 2 * 4)
    [(ctxV 0, .nat k), (.get (arg 0) (.nat 1), Kv), (ctxV 2, dv), (ctxV 3, xv), (.var 1, yv'),
      (.get (arg 0) (.nat 2), hv'), (ctxV 6, rv), (ctxV 7, fv), (ctxV 8, hh), (ctxV 9, .nat N)]
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dent [yv'] 0 (by omega)).mono (by omega)
      · exact (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 1)
          (show [v, Kv, hv', lv, boolVal b][1]? = some Kv from rfl)).mono (by omega)
      · exact (dent [yv'] 2 (by omega)).mono (by omega)
      · exact (dent [yv'] 3 (by omega)).mono (by omega)
      · exact (Det.var' (i := 1) rfl).mono (by nlinarith)
      · exact (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 2)
          (show [v, Kv, hv', lv, boolVal b][2]? = some hv' from rfl)).mono (by omega)
      · exact (dent [yv'] 6 (by omega)).mono (by omega)
      · exact (dent [yv'] 7 (by omega)).mono (by omega)
      · exact (dent [yv'] 8 (by omega)).mono (by omega)
      · exact (dent [yv'] 9 (by omega)).mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hval
  have dl : Det Pg [a, yv'] (.get (arg 0) (.nat 3)) lv (4 * a.wt + 30) :=
    (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 3)
      (show [v, Kv, hv', lv, boolVal b][3]? = some lv from rfl)).mono (by omega)
  have db : Det Pg [a, yv'] (.get (arg 0) (.nat 4)) (boolVal b) (4 * a.wt + 30) := by
    have wb : (boolVal b).wt < ctx.wt := wt_le_wt_list (by simp)
    exact (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 4)
      (show [v, Kv, hv', lv, boolVal b][4]? = some (boolVal b) from rfl)).mono (by omega)
  have hcl := normModeCall_spec R hval dl db hL hcallT
  refine (EvalAll.snoc_det (Det.mk1 (dt [yv'])) hcl).mono ?_
  rintro w cw ⟨u, cu, ⟨A, r, cb, hA, hcb, hcu⟩, rfl, hcw⟩
  have hAT := r.exact
  subst hAT
  refine ⟨⟨u, rfl, hA⟩, cb, ⟨_, r, hcb⟩, ?_⟩
  have wu := hA.wt_le
  set Z := 5 * a.wt + ansW k + 20 * (k + 1) ^ 2 + 10 with hZ
  have hZ1 : Z + 1 ≤ (Z + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hX : (Val.list [Val.list ((List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i)))),
      natList ((List.finRange k).map fun i => (t i : ℕ))]).wt + 1 ≤ Z + 1 := by
    rw [← hyv0, ← encPerm_eq_natList]
    have := wt_list2_le yv (encPerm t)
    omega
  have hX3 := Nat.pow_le_pow_left hX 3
  have hg3 := Nat.mul_le_mul_left gatherK hX3
  have w10 := wt_list_le [.nat k, Kv, dv, xv, yv', hv', rv, fv, hh, .nat N]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w10
  have w10' := sum_wt_lt_wt_list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at w10'
  have hk2 : (2 * k + 1) ^ 2 ≤ 4 * (k + 1) ^ 2 :=
    calc (2 * k + 1) ^ 2 ≤ (2 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (k + 1) ^ 2 := by ring
  have wtu := wt_list2_le (encPerm t) u
  have etu : (Val.list ([encPerm t] ++ [u])).wt = (Val.list [encPerm t, u]).wt := rfl
  have w1 := wt_list_le [encPerm t]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w1
  have ev' : v.wt = (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt := rfl
  have hZ34 : (Z + 1) ^ 3 ≤ (Z + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hZ14 : Z + 1 ≤ (Z + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold normChildB
  have hgK : gatherK * (Z + 1) ^ 3 ≤ 100000 * (Z + 1) ^ 3 := by simp [gatherK]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hcy
  clear hval hcl hgath hcallT hcanT hcall
  have hq := wt_list2_le yv (encPerm t)
  have hfin : cy + cw + (Val.list ([encPerm t] ++ [u])).wt + 1 ≤
      10000 * (Z + 1) + gatherK * (Z + 1) ^ 3 + cb := by omega
  omega

end GI.Impl
