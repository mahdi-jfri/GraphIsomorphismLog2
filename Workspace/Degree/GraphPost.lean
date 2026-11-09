module

public import Workspace.Degree.GraphDec
public import Workspace.Lang.Prims.Reduce

/-!
# After a string query

`postE`: on `[[bv, FX, FY], U, ans]`, the next pair of the loop of Lemma 9.4, or `[]` if the answer
is empty. Its specs are `post_nil` and `post_some`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The body. -/
def postE (pr dc ma cp rd : ℕ) : Expr :=
  let c := arg 0
  let B := Expr.get c (.nat 0)
  let FX := Expr.get c (.nat 1)
  let FY := Expr.get c (.nat 2)
  let U := arg 1
  let ans := arg 2
  .ite (.length ans)
    (.letE (.call pr (mk2 (mk2 B FX) (.get B (.nat 5))))
      (mk2 (.call cp (mk2 U (.call dc (mk2 (mk3 B FY (.var 1)) (.get ans (.nat 0))))))
        (.call rd (mk2 (.get B (.nat 0))
          (.call ma (mk2 (mk3 B FX (.var 1)) (.get (.get ans (.nat 1)) (.nat 1))))))))
    .nil

/-- The cost of the case of an empty answer, and a bound on the small weights. -/
def postNilT (n : ℕ) : ℕ := 1000 * VB n

/-- A bound on lists of `k ^ 2 + 1` permutations. -/
def LB (n : ℕ) : ℕ := (kB n ^ 2 + 2) * (2 * WB n + 1) + 4

/-- A bound on the weights of the arguments. -/
def postW (n : ℕ) : ℕ := 1000 * LB n + 10000 * VB n

/-- The cost of the map of `dec`. -/
def postMapC (n : ℕ) : ℕ := (kB n ^ 2 + 1) * decC n + mapK * (kB n ^ 2 + 2) * postW n

/-- The cost of the reduction. -/
noncomputable def postRdC (h : Membership) (n : ℕ) : ℕ := reduceCost h n (kB n ^ 2)

/-- The budget of the body. -/
noncomputable def postT (h : Membership) (n : ℕ) : ℕ :=
  parC n + decC n + postMapC n + permK * (n + 1) ^ 3 + postRdC h n + postW n

/-- The bound of the body. -/
noncomputable def postC (h : Membership) (n : ℕ) : ℕ := 100000 * postT h n

theorem postC_poly (h : Membership) : PolyB (postC h) := by
  have := VB_poly
  have := WB_poly
  have := parC_poly
  have := decC_poly
  unfold postC postT postRdC reduceCost memCost postMapC postW LB kB
  poly

theorem reduceCost_mono (h : Membership) (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    reduceCost h n a ≤ reduceCost h n b := by
  unfold reduceCost
  refine Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_left _ ?_)
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) _

/-- **The case of an empty answer.** -/
theorem post_nil {P : Program} {f pr dc ma cp rd : ℕ} (hf : P.funs[f]? = some (postE pr dc ma cp rd))
    {b U : Val} (hb : 2 * (Val.list [b, U, .list []]).wt + 10 ≤ postNilT n) :
    FunDet P f (.list [b, U, .list []]) (.list []) (100 * postNilT n) := by
  have a2 : Lv P [.list [b, U, .list []]] (postNilT n) (arg 2) (.list []) 1 :=
    Lv.arg rfl (by omega)
  have hl := Lv.length a2 (by omega)
  have n1 : Lv P [.list [b, U, .list []]] (postNilT n) .nil (.list []) 1 := Lv.nil (by omega)
  exact funDet_of_lv hf (T := postNilT n) (m := 100) (Lv.mono (e := postE pr dc ma cp rd)
    (Lv.ite_zero (t := _) hl n1) (by norm_num))

set_option maxHeartbeats 2000000 in
/-- **The case of a nonempty answer.** -/
theorem post_some {P : Program} {f pr dc ma cp rd j : ℕ} (h : Membership)
    (hf : P.funs[f]? = some (postE pr dc ma cp rd))
    (hP : P.HasAt pr (parFuns pr)) (hDc : P.HasAt dc (decFuns dc))
    (hM : P.HasAt ma (mapFuns ma dc)) (hC : P.HasAt cp (composeFuns cp))
    (hR : P.HasAt rd (reduceFuns rd j)) (hj : P.prims[j]? = some (membershipPrim h))
    (hS : Sz n D) (hD : 0 < D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n)
    {X Z : SimpleGraph (Fin n)} {par : Fin n → Fin n × Fin D}
    (hpar : ∀ w, ℓ w = r + 1 → (slotE n D (par w) : ℕ) = parNum D ℓ r (fwd ℓ X) w)
    (z : Fin n × Fin D) {U e : Perm (Fin n)} {g₀ : Perm (Fin n × Fin D)}
    (he : ∀ u, e u = decMap ℓ r (fwd ℓ Z) par (z0 hD) g₀ u)
    {hs' : List (Perm (Fin n × Fin D))} (hlen : hs'.length ≤ kB n ^ 2)
    (decP : Perm (Fin n × Fin D) → Perm (Fin n))
    (hdec : ∀ f ∈ (1 :: hs'), ∀ u, decP f u = decMap ℓ r (fwd ℓ X) par (z0 hD) f u)
    (hdec1 : decP 1 = 1) :
    FunDet P f (.list [.list [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z], encPerm U,
        .list [encPerm (diag n D g₀), encGroup (hs'.map (diag n D))]])
      (.list [encPerm (U * e), encGroup (keepList (hs'.map decP))]) (postC h n) := by
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have w0 := bv_wt hS hℓ hr
  have wFX := fwdV_le_VB ℓ X
  have wFZ := fwdV_le_VB ℓ Z
  have wU : (encPerm U).wt ≤ WB n := perm_wt (by omega) U
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wt0 : (encPerm (diag n D g₀)).wt ≤ WB n := perm_wt (by omega) _
  have wpn : (encFun (parNum D ℓ r (fwd ℓ X))).wt ≤ WB n :=
    table_wt' (B := n * D) (by omega) (by omega) fun w => parNum_le ℓ r _ w
  set L : List (Perm (Fin n × Fin D)) := 1 :: hs' with hL
  set enc : Perm (Fin n × Fin D) → Val := fun f => encPerm (diag n D f) with henc
  set res : Perm (Fin n × Fin D) → Val := fun f => encPerm (decP f) with hres
  have hLl : L.length ≤ kB n ^ 2 + 1 := by simp [hL]; omega
  have hLB : ∀ (v : Perm (Fin n × Fin D) → Val), (∀ f, (v f).wt ≤ WB n) →
      (Val.list (L.map v)).wt ≤ LB n := by
    intro v hv
    have := wt_lit (L.map v) (c := WB n) (by
      intro x hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      exact hv g)
    simp only [List.length_map] at this
    refine this.trans ?_
    simp only [LB]
    have := Nat.mul_le_mul_right (2 * WB n + 1) (show L.length ≤ kB n ^ 2 + 2 by omega)
    omega
  have wenc := hLB enc fun f => perm_wt (by omega) _
  have wres := hLB res fun f => perm_wt (by omega) _
  have heL : encGroup (hs'.map (diag n D)) = .list [.nat (n * D * (n * D)), .list (L.map enc)] := by
    have e1 : enc 1 = encPerm (1 : Perm (Fin (n * D * (n * D)))) := by simp only [henc, map_one]
    have e2 : L.map enc = (1 :: hs'.map (diag n D)).map encPerm := by
      simp only [hL, List.map_cons, List.map_map, e1]
      rfl
    rw [e2]
    rfl
  have heR : encGroup (hs'.map decP) = .list [.nat n, .list (L.map res)] := by
    have e1 : res 1 = encPerm (1 : Perm (Fin n)) := by simp only [hres, hdec1]
    have e2 : L.map res = (1 :: hs'.map decP).map encPerm := by
      simp only [hL, List.map_cons, List.map_map, e1]
      rfl
    rw [e2]
    rfl
  rw [heL]
  set ans : Val := .list [encPerm (diag n D g₀), .list [.nat (n * D * (n * D)), .list (L.map enc)]]
    with hans
  set b : Val := .list [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z] with hb
  set A : List Val := [b, encPerm U, ans] with hA
  have wn : (Val.nat (n * D * (n * D))).wt ≤ WB n := nat_wt (by omega)
  have w1 : (Val.list [Val.nat (n * D * (n * D)), .list (L.map enc)]).wt ≤
      2 * (2 * (LB n + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w2 : ans.wt ≤ 2 * (2 * (2 * (2 * (LB n + WB n) + 1) + 4 + WB n) + 1) + 4 :=
    wt_lit _ (by simp [hans]; omega)
  have w3 : b.wt ≤ 3 * (2 * VB n + 1) + 4 := wt_lit _ (by simp; omega)
  have hb1 : WB n ≤ VB n := by omega
  have w4 : (Val.list A).wt ≤ 3 * (2 * (ans.wt + b.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp [hA]; omega)
  have hLW : 1 ≤ WB n := by omega
  have hW : 2 * (Val.list A).wt + 10 ≤ postW n := by
    simp only [postW]
    omega
  have hTW : postW n ≤ postT h n := by simp only [postT]; omega
  have hW100 : 100 + WB n ≤ postW n := by simp only [postW]; omega
  have hT1 : parC n ≤ postT h n := by simp only [postT]; omega
  have hT2 : decC n ≤ postT h n := by simp only [postT]; omega
  have hT3 : postMapC n ≤ postT h n := by simp only [postT]; omega
  have hT4 : permK * (n + 1) ^ 3 ≤ postT h n := by simp only [postT]; omega
  have hT5 : postRdC h n ≤ postT h n := by simp only [postT]; omega
  -- the program, in the environment of the `let`
  set pv := encFun (parNum D ℓ r (fwd ℓ X)) with hpv
  have wAll : ∀ (rest : List Val) {i : ℕ} {v : Val}, [b, encPerm U, ans][i]? = some v → i ≤ 2 →
      Lv P (.list A :: rest) (postT h n) (arg i) v 1 := fun rest i v hv hi =>
    Lv.arg hv (by omega)
  have n0 : ∀ (env : List Val) (k : ℕ), k ≤ 8 → Lv P env (postT h n) (.nat k) (.nat k) 1 :=
    fun env k hk => Lv.nat k (by omega)
  have getB : ∀ rest : List Val, Lv P (.list A :: rest) (postT h n) (.get (arg 0) (.nat 0))
      (bv D ℓ r) _ := fun rest =>
    Lv.get (vs := [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z]) (wAll rest (i := 0) rfl (by omega)) (n0 _ 0 (by omega)) rfl
  have getX : ∀ rest : List Val, Lv P (.list A :: rest) (postT h n) (.get (arg 0) (.nat 1))
      (fwdV ℓ X) _ := fun rest =>
    Lv.get (vs := [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z]) (wAll rest (i := 0) rfl (by omega)) (n0 _ 1 (by omega)) rfl
  have getZ : ∀ rest : List Val, Lv P (.list A :: rest) (postT h n) (.get (arg 0) (.nat 2))
      (fwdV ℓ Z) _ := fun rest =>
    Lv.get (vs := [bv D ℓ r, fwdV ℓ X, fwdV ℓ Z]) (wAll rest (i := 0) rfl (by omega)) (n0 _ 2 (by omega)) rfl
  have hparC : FunDet P pr (.list [.list [bv D ℓ r, fwdV ℓ X], ids n]) pv (parC n) :=
    par_spec hP hS hℓ hr (fwd ℓ X) (length_fwd_le ℓ X)
  have c1 := Lv.call (Lv.mk2 (Lv.mk2 (getB []) (getX []) (by omega))
    (Lv.bvGet (getB []) (j := 5) (by omega) rfl (by omega)) (by omega)) hparC hT1
  have hpn : ∀ u, parNum D ℓ r (fwd ℓ X) u ≤ n * D := fun u => parNum_le ℓ r _ u
  have hdc := dec_spec hDc hS hD hℓ hr (F := fwd ℓ Z) (length_fwd_le ℓ Z) hpn hpar g₀ he
  have hdm : FunDet P ma (.list [decCtx D ℓ r (fwd ℓ X) (parNum D ℓ r (fwd ℓ X)),
      .list (L.map enc)]) (.list (L.map res)) (postMapC n) := by
    have hinj : Function.Injective enc := fun a b hab =>
      diag_injective z (encPerm_injective hab)
    have w8 : (decCtx D ℓ r (fwd ℓ X) (parNum D ℓ r (fwd ℓ X))).wt ≤ 3 * (2 * VB n + 1) + 4 :=
      decCtx_wt hS hℓ hr (length_fwd_le ℓ X) hpn
    have w9 : (Val.list [decCtx D ℓ r (fwd ℓ X) (parNum D ℓ r (fwd ℓ X)), .list (L.map enc)]).wt ≤
        2 * (2 * (3 * (2 * VB n + 1) + 4 + LB n) + 1) + 4 := wt_lit _ (by simp; omega)
    refine (mapInj_spec (W := postW n) hM L enc res hinj (B := decC n) (fun a ha =>
      dec_spec hDc hS hD hℓ hr (F := fwd ℓ X) (length_fwd_le ℓ X) hpn hpar a (hdec a ha))
      (by simp only [postW]; omega)).mono ?_
    have e1 := Nat.mul_le_mul_right (decC n) hLl
    have e2 : mapK * (L.length + 1) * postW n ≤ mapK * (kB n ^ 2 + 2) * postW n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    simp only [postMapC]
    omega
  -- the environment of the `let`
  set A' : List Val := [.list A, pv] with hA'
  have wp : pv.wt ≤ WB n := wpn
  have v1 : Lv P A' (postT h n) (.var 1) pv 1 := Lv.var rfl (by omega)
  have bB := getB [pv]
  have bX := getX [pv]
  have bZ := getZ [pv]
  have wAns : Lv P A' (postT h n) (arg 2) ans 1 := wAll [pv] (i := 2) rfl (by omega)
  have wUa : Lv P A' (postT h n) (arg 1) (encPerm U) 1 := wAll [pv] (i := 1) rfl (by omega)
  have a0 := Lv.get (vs := [encPerm (diag n D g₀), .list [.nat (n * D * (n * D)), .list (L.map enc)]])
    wAns (n0 A' 0 (by omega)) rfl
  have a1 := Lv.get (vs := [encPerm (diag n D g₀), .list [.nat (n * D * (n * D)), .list (L.map enc)]])
    wAns (n0 A' 1 (by omega)) rfl
  have a2 := Lv.get (vs := [.nat (n * D * (n * D)), .list (L.map enc)]) a1 (n0 A' 1 (by omega)) rfl
  have ctxZ := Lv.mk3 bB bZ v1 (by omega)
  have ctxX := Lv.mk3 bB bX v1 (by omega)
  have d1 := Lv.call (Lv.mk2 ctxZ a0 (by omega)) hdc hT2
  have d2 := Lv.call (Lv.mk2 ctxX a2 (by omega)) hdm hT3
  have d3 := Lv.call (Lv.mk2 wUa d1 (by omega)) (compose_spec hC U e) hT4
  have grp := Lv.mk2 (Lv.bvGet bB (j := 0) (by omega) rfl (by omega)) d2 (by omega)
  rw [← heR] at grp
  have hrd : FunDet P rd (encGroup (hs'.map decP)) (encGroup (keepList (hs'.map decP)))
      (postRdC h n) := by
    refine (reduce_spec h hR hj (hs'.map decP)).mono ?_
    simp only [postRdC]
    exact reduceCost_mono h n (by simpa using hlen)
  have d4 := Lv.call grp hrd hT5
  have o1 := Lv.mk2 d3 d4 (by omega)
  have l1 := Lv.letE (Lv.call (Lv.mk2 (Lv.mk2 (getB []) (getX []) (by omega))
    (Lv.bvGet (getB []) (j := 5) (by omega) rfl (by omega)) (by omega)) hparC hT1) o1
  have c0 : Lv P [.list A] (postT h n) (.length (arg 2)) (.nat 2) _ :=
    Lv.length (vs := [encPerm (diag n D g₀), .list [.nat (n * D * (n * D)), .list (L.map enc)]])
      (wAll [] (i := 2) rfl (by omega)) (by omega)
  have i1 := Lv.ite_pos (e := .nil) c0 (by omega) l1
  have hC' : postC h n = 100000 * postT h n := rfl
  rw [hC']
  exact funDet_of_lv hf (T := postT h n) (m := 100000) (Lv.mono (e := postE pr dc ma cp rd) i1
    (by norm_num))

end GI.Degree
