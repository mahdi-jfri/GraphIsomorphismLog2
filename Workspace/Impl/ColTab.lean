import Workspace.Impl.ColSpec

/-!
# Tables of the column program, with costs in one bound

The column program builds its tables by `map` over `[0, …, k - 1]` (`tab_det`) with the entry
functions of `Workspace/Impl/ColElem.lean`. This file packs each table into one lemma whose cost
is `K (X + 1)^d`, where `X` bounds every number in the tables and every length. The program
then only adds such bounds.

* `colTabPick_det`: `a (x i) + s`;
* `colTabEq_det`: the indicator `colEqv a₁ a₂`;
* `colTabKey_det`: the mixed radix key `colKeyv`;
* `colTabMin_det`: the running minimum `colMinv`;
* `colCount_det`, `colLabs_det`: the count of classes and the first-point labels of the class
  numbering.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {P : Program}

theorem colWt_fin_le {k p X : ℕ} (x : Fin k → Fin p) (hp : p ≤ X) (hk : k ≤ X) :
    (encFun fun j => (x j : ℕ)).wt ≤ 5 * (X + 1) ^ 2 :=
  wt_encFun_le' _ (fun j => by have := (x j).2; omega) hk

theorem colSq_ge (X : ℕ) : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _

/-- **The table `a (x i) + s`.** -/
theorem colTabPick_det {b f : ℕ} (hm : P.HasAt b (mapFuns b f)) (hf : P.funs[f]? = some colPickF)
    {p k : ℕ} (a : Fin p → ℕ) (x : Fin k → Fin p) (s : ℕ) {X : ℕ} (ha : ∀ j, a j + s ≤ X)
    (hs : s ≤ X) (hp : p ≤ X) (hk : k ≤ X) :
    FunDet P b (.list [.list [encFun a, encFun fun j => (x j : ℕ), .nat s],
        natList (List.range k)]) (encFun fun i => a (x i) + s) (10 ^ 7 * (X + 1) ^ 3) := by
  generalize hc : (Val.list [encFun a, encFun fun j => (x j : ℕ), .nat s]) = c
  have wa : (encFun a).wt ≤ 5 * (X + 1) ^ 2 := wt_encFun_le' _ (fun j => by have := ha j; omega) hp
  have wx := colWt_fin_le x hp hk
  have ws := wt_nat_le s
  have hX := colSq_ge X
  have wc : c.wt ≤ 40 * (X + 1) ^ 2 := by
    have := wt_list3_le (encFun a) (encFun fun j => (x j : ℕ)) (.nat s); rw [hc] at this; omega
  have hB : ∀ i : Fin k, FunDet P f (.list [c, .nat i]) (.nat (a (x i) + s))
      (2000 * (X + 1) ^ 2) := by
    intro i
    have hd := colPick_det hf a x s i
    rw [hc] at hd
    refine hd.mono ?_
    have := wt_list2_le c (.nat (i : ℕ))
    have := wt_nat_le (i : ℕ)
    have := ha (x i)
    have := i.2
    omega
  refine (tab_det hm hB (fun i => ha (x i)) (by omega) hk).mono ?_
  have : k * (2000 * (X + 1) ^ 2) ≤ 2000 * (X + 1) ^ 3 := mul_le_pow_succ 2000 2 hk
  omega

/-- **The table of `colEqv a₁ a₂`.** -/
theorem colTabEq_det {b f : ℕ} (hm : P.HasAt b (mapFuns b f)) (hf : P.funs[f]? = some colEqF)
    {k : ℕ} (a₁ a₂ : Fin k → ℕ) (h0 : 0 < k) {X : ℕ} (h1 : ∀ j, a₁ j ≤ X) (h2 : ∀ j, a₂ j ≤ X)
    (hk : k ≤ X) :
    FunDet P b (.list [.list [encFun a₁, encFun a₂], natList (List.range k)])
      (encFun (colEqv a₁ a₂ h0)) (10 ^ 7 * (X + 1) ^ 3) := by
  generalize hc : (Val.list [encFun a₁, encFun a₂]) = c
  have w1 := wt_encFun_le' _ h1 hk
  have w2 := wt_encFun_le' _ h2 hk
  have hX := colSq_ge X
  have wc : c.wt ≤ 40 * (X + 1) ^ 2 := by
    have := wt_list2_le (encFun a₁) (encFun a₂); rw [hc] at this; omega
  have hB : ∀ i : Fin k, FunDet P f (.list [c, .nat i]) (.nat (colEqv a₁ a₂ h0 i))
      (5000 * (X + 1) ^ 2) := by
    intro i
    have hd := colEq_det hf a₁ a₂ h0 i
    rw [hc] at hd
    refine hd.mono ?_
    have := wt_list2_le c (.nat (i : ℕ))
    have := wt_nat_le (i : ℕ)
    have := i.2
    omega
  refine (tab_det hm hB (fun i => (colEqv_le a₁ a₂ h0 i).trans (by omega)) (by omega) hk).mono ?_
  have : k * (5000 * (X + 1) ^ 2) ≤ 5000 * (X + 1) ^ 3 := mul_le_pow_succ 5000 2 hk
  omega

/-- **The table of the mixed radix keys.** -/
theorem colTabKey_det {b f : ℕ} (hm : P.HasAt b (mapFuns b f)) (hf : P.funs[f]? = some colKeyF)
    {k : ℕ} (rl hl oc : Fin k → ℕ) {N1 X : ℕ} (hN : 1 ≤ N1) (hrl : ∀ j, rl j ≤ X)
    (hhl : ∀ j, hl j ≤ X) (hoc : ∀ j, oc j ≤ X) (hN1 : N1 ≤ X)
    (hkey : ∀ j, colKeyv rl hl oc N1 j ≤ X) (hk : k ≤ X) :
    FunDet P b (.list [.list [encFun rl, encFun hl, encFun oc, .nat N1], natList (List.range k)])
      (encFun (colKeyv rl hl oc N1)) (10 ^ 7 * (X + 1) ^ 3) := by
  generalize hc : (Val.list [encFun rl, encFun hl, encFun oc, .nat N1]) = c
  have w1 := wt_encFun_le' _ hrl hk
  have w2 := wt_encFun_le' _ hhl hk
  have w3 := wt_encFun_le' _ hoc hk
  have w4 := wt_nat_le N1
  have hX := colSq_ge X
  have wc : c.wt ≤ 50 * (X + 1) ^ 2 := by
    have := wt_list4_le (encFun rl) (encFun hl) (encFun oc) (.nat N1); rw [hc] at this; omega
  have hB : ∀ i : Fin k, FunDet P f (.list [c, .nat i]) (.nat (colKeyv rl hl oc N1 i))
      (20000 * (X + 1) ^ 2) := by
    intro i
    have hd := colKey_det hf rl hl oc hN i
    rw [hc] at hd
    refine hd.mono ?_
    have := wt_list2_le c (.nat (i : ℕ))
    have := wt_nat_le (i : ℕ)
    have := hkey i
    have := i.2
    omega
  refine (tab_det hm hB hkey (by omega) hk).mono ?_
  have : k * (20000 * (X + 1) ^ 2) ≤ 20000 * (X + 1) ^ 3 := mul_le_pow_succ 20000 2 hk
  omega

/-- **The table of the running minima.** -/
theorem colTabMin_det {b f it g : ℕ} (hm : P.HasAt b (mapFuns b f))
    (hf : P.funs[f]? = some (colMinF it)) (hit : P.HasAt it (iterFuns it g))
    (hg : P.funs[g]? = some colMinStepF) {k : ℕ} (bk orb : Fin k → ℕ) {X : ℕ}
    (hbk : ∀ j, bk j ≤ X) (horb : ∀ j, orb j ≤ X) (hk : k ≤ X) :
    FunDet P b (.list [.list [encFun bk, encFun orb], natList (List.range k)])
      (encFun (colMinv bk orb)) (10 ^ 9 * (X + 1) ^ 4) := by
  generalize hc : (Val.list [encFun bk, encFun orb]) = c
  have w1 := wt_encFun_le' _ hbk hk
  have w2 := wt_encFun_le' _ horb hk
  have hX := colSq_ge X
  have wc : c.wt ≤ 40 * (X + 1) ^ 2 := by
    have := wt_list2_le (encFun bk) (encFun orb); rw [hc] at this; omega
  have hv : ∀ i, colMinv bk orb i ≤ X := fun i => (colMinAcc_le bk orb i k).trans (hbk i)
  have hB : ∀ i : Fin k, FunDet P f (.list [c, .nat i]) (.nat (colMinv bk orb i))
      (2 * 10 ^ 8 * (X + 1) ^ 3) := by
    intro i
    have hd := colMin_det hf hit hg bk orb i
    rw [hc] at hd
    refine hd.mono ?_
    have h1 : (Val.list [c, .nat (i : ℕ)]).wt + k + 1 ≤ 200 * (X + 1) ^ 2 := by
      have := wt_list2_le c (.nat (i : ℕ))
      have := wt_nat_le (i : ℕ)
      have := i.2
      omega
    have h2 := Nat.mul_le_mul (show colMinK * (k + 1) ≤ colMinK * (X + 1) by
      exact Nat.mul_le_mul_left _ (by omega)) h1
    have e : colMinK * (X + 1) * (200 * (X + 1) ^ 2) = 2 * 10 ^ 8 * (X + 1) ^ 3 := by
      simp only [colMinK]; ring
    omega
  refine (tab_det hm hB hv (by omega) hk).mono ?_
  have : k * (2 * 10 ^ 8 * (X + 1) ^ 3) ≤ 2 * 10 ^ 8 * (X + 1) ^ 4 := mul_le_pow_succ (2 * 10 ^ 8) 3 hk
  have : (X + 1) ^ 3 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **A class count**: the number of class representatives of `lab` on the support of `dm`. -/
theorem colCount_det {b : ℕ} (h : P.HasAt b (clsFuns b)) {env : List Val} {e : Expr} {k X ce : ℕ}
    (lab dm : Fin k → ℕ) (he : Det P env e (.list [encFun lab, encFun dm]) ce)
    (hlab : ∀ i, lab i ≤ X) (hdm : ∀ i, dm i ≤ 1) (hkX : k ≤ X) :
    Det P env (.length (.get (.call b e) (.nat 1)))
      (.nat (Cls.repsOf dm (Cls.keyOf lab dm)).length) (ce + 10 ^ 10 * (X + 1) ^ 4) := by
  have hc := Det.call he (cls_spec h lab dm hlab hdm hkX)
  have hg := Det.get' hc (Det.nat 1) (v := natList (Cls.repsOf dm (Cls.keyOf lab dm))) rfl
  have hl := Det.length hg
  rw [List.length_map] at hl
  refine hl.mono ?_
  have w := (cls_spec h lab dm hlab hdm hkX).wt_lt
  have w1 : (natList (Cls.repsOf dm (Cls.keyOf lab dm))).wt < (clsVal lab dm).wt :=
    wt_le_wt_list (by simp)
  have w2 : ((Cls.repsOf dm (Cls.keyOf lab dm)).map Val.nat).length ≤
      (natList (Cls.repsOf dm (Cls.keyOf lab dm))).wt := by
    have := length_lt_wt_list ((Cls.repsOf dm (Cls.keyOf lab dm)).map Val.nat)
    exact this.le
  simp only [List.length_map] at w2
  have : (Val.list ((Cls.repsOf dm (Cls.keyOf lab dm)).map Val.nat)).wt =
    (natList (Cls.repsOf dm (Cls.keyOf lab dm))).wt := rfl
  simp only [clsK] at *
  omega

/-- **First-point labels** of the class numbering. -/
theorem colLabs_det {b : ℕ} (h : P.HasAt b (clsFuns b)) {env : List Val} {e : Expr} {k X ce : ℕ}
    (lab dm : Fin k → ℕ) (he : Det P env e (.list [encFun lab, encFun dm]) ce)
    (hlab : ∀ i, lab i ≤ X) (hdm : ∀ i, dm i ≤ 1) (hkX : k ≤ X) :
    Det P env (.get (.call b e) (.nat 2)) (encFun (Cls.repOf (Cls.keyOf lab dm)))
      (ce + 10 ^ 10 * (X + 1) ^ 4) := by
  have hc := Det.call he (cls_spec h lab dm hlab hdm hkX)
  have hg := Det.get' hc (Det.nat 2) (v := encFun (Cls.repOf (Cls.keyOf lab dm))) rfl
  refine hg.mono ?_
  have w := (cls_spec h lab dm hlab hdm hkX).wt_lt
  have w1 : (encFun (Cls.repOf (Cls.keyOf lab dm))).wt < (clsVal lab dm).wt :=
    wt_le_wt_list (by simp)
  simp only [clsK] at *
  omega

/-! ### Costs that add up

The weight of a value is below its cost bound (`Det.wt_lt`). So each combinator of `Det` costs
at most a fixed multiple of the costs of its parts, and long programs are costed by adding. -/

section Lin

variable {env : List Val}

theorem colMk2 {a b : Expr} {va vb : Val} {ca cb : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) : Det P env (mk2 a b) (.list [va, vb]) (5 * (ca + cb) + 20) := by
  have := ha.wt_lt; have := hb.wt_lt; have := wt_list2_le va vb
  exact (Det.mk2 ha hb).mono (by omega)

theorem colMk3 {a b c : Expr} {va vb vc : Val} {ca cb cc : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) (hc : Det P env c vc cc) :
    Det P env (mk3 a b c) (.list [va, vb, vc]) (7 * (ca + cb + cc) + 30) := by
  have := ha.wt_lt; have := hb.wt_lt; have := hc.wt_lt; have := wt_list3_le va vb vc
  exact (Det.mk3 ha hb hc).mono (by omega)

theorem colMk4 {a b c d : Expr} {va vb vc vd : Val} {ca cb cc cd : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) (hc : Det P env c vc cc) (hd : Det P env d vd cd) :
    Det P env (mk4 a b c d) (.list [va, vb, vc, vd]) (9 * (ca + cb + cc + cd) + 50) := by
  have := ha.wt_lt; have := hb.wt_lt; have := hc.wt_lt; have := hd.wt_lt
  have := wt_list4_le va vb vc vd
  exact (Det.mk4 ha hb hc hd).mono (by omega)

theorem colLet {e body : Expr} {v w : Val} {ca cb : ℕ} (ha : Det P env e v ca)
    (hb : Det P (env ++ [v]) body w cb) : Det P env (.letE e body) w (ca + 2 * cb + 1) := by
  have := hb.wt_lt
  exact (Det.letE ha hb).mono (by omega)

theorem colCall {f : ℕ} {a : Expr} {v w : Val} {ca cb : ℕ} (ha : Det P env a v ca)
    (hf : FunDet P f v w cb) : Det P env (.call f a) w (ca + 2 * cb + 1) := by
  have := hf.wt_lt
  exact (Det.call ha hf).mono (by omega)

theorem colGet {l i : Expr} {vs : List Val} {x ca cb : ℕ} {v : Val}
    (ha : Det P env l (.list vs) ca) (hb : Det P env i (.nat x) cb) (hv : vs[x]? = some v) :
    Det P env (.get l i) v (2 * ca + cb + 1) := by
  have := ha.wt_lt
  have : v.wt < (Val.list vs).wt := by
    obtain ⟨hx, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    exact wt_getElem_lt _ _ hx
  exact (Det.get' ha hb hv).mono (by omega)

theorem colLength {l : Expr} {vs : List Val} {ca : ℕ} (ha : Det P env l (.list vs) ca) :
    Det P env (.length l) (.nat vs.length) (2 * ca + 3) := by
  have := ha.wt_lt
  have := length_lt_wt_list vs
  exact (Det.length ha).mono (by omega)

theorem colVar {i : ℕ} {v : Val} (h : env[i]? = some v) {c : ℕ} (hc : v.wt + 1 ≤ c) :
    Det P env (.var i) v c :=
  (Det.var' h).mono hc

end Lin

end GI.Impl
