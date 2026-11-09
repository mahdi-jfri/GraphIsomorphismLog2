module

public import Workspace.Degree.ResetVal
public import Workspace.Impl.GenProdHier

@[expose] public section

/-!
# The reset program

`resetBody` runs a reset: it computes the canonical value of the reset state `R` of `T`, calls the
function `trans` on it, and lifts the answer. It uses `prepF` and the lift of a fresh phase of
the general algorithm, and replaces the hierarchy of the value.

`resetIntBody` handles one interval on `[[P, s], [labels, ratio, cap, origin]]`, where `P` lists the
positions of the domain. See `Workspace/Degree/ResetVal.lean`.

`reset_spec`: every evaluation returns a canonical answer of `T`, at the cost of the call of `trans`
and a polynomial in the weight of the input.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens PointwiseStab Preimage NormalizedFactor)

variable {Ω C : Type} {k : ℕ}

/-- The body of the step on one interval. -/
def resetIntBody (ga mp : ℕ) : Expr :=
  .letE (.call ga (mk2 (.get (arg 1) (.nat 0)) (.get (arg 0) (.nat 0))))
  (.letE (minE (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 1)))
  (mk4 (.call mp (mk2 (.var 1) (.var 1))) (.var 2)
    (minE (.get (arg 1) (.nat 2)) (.var 2))
    (minE (.get (arg 1) (.nat 3)) (.get (arg 0) (.nat 1)))))

/-- The cost of the step on one interval, when all weights are at most `Y`. -/
def intC (Y : ℕ) : ℕ := gatherK * (4 * Y + 7) ^ 3 + 10 ^ 7 * (2 * Y + 1) ^ 3 + 10 ^ 4 * (Y + 10)

theorem resetInt_spec {P : Program} {f d : ℕ}
    (hf : P.funs[f]? = some (resetIntBody (d + 18) (d + 9))) (hd : DomAt P d) {Ps : List ℕ} {s : ℕ}
    (a : IvData) (hi : ∀ i ∈ Ps, i < a.1.length) {Y : ℕ}
    (hc : (Val.list [natList Ps, .nat s]).wt ≤ Y) (ha : (ivEnc a).wt ≤ Y)
    (hL : (natList (domLabs Ps a.1)).wt ≤ Y) (hw : (ivReset Ps s a).wt ≤ Y) :
    FunDet P f (.list [.list [natList Ps, .nat s], ivEnc a]) (ivReset Ps s a) (intC Y) := by
  obtain ⟨labs, r, cp, o⟩ := a
  simp only at hi hL
  set c := Val.list [natList Ps, .nat s] with hcdef
  set x := Val.list [c, ivEnc (labs, r, cp, o)] with hx
  have hxw : x.wt ≤ 4 * Y + 6 := by
    have := wt_list2_le c (ivEnc (labs, r, cp, o))
    rw [hx]
    omega
  have g0 : ∀ rest, Det P (x :: rest) (arg 0) c _ := fun rest =>
    Det.arg' (vs := [c, ivEnc (labs, r, cp, o)]) (rest := rest) (j := 0) rfl
  have g1 : ∀ rest, Det P (x :: rest) (arg 1) (ivEnc (labs, r, cp, o)) _ := fun rest =>
    Det.arg' (vs := [c, ivEnc (labs, r, cp, o)]) (rest := rest) (j := 1) rfl
  have gl : ∀ rest, Det P (x :: rest) (.get (arg 1) (.nat 0)) (natList labs) _ := fun rest =>
    Det.get' (g1 rest) (Det.nat 0) (vs := [_, _, _, _]) rfl
  have gr : ∀ rest, Det P (x :: rest) (.get (arg 1) (.nat 1)) (.nat r) _ := fun rest =>
    Det.get' (g1 rest) (Det.nat 1) (vs := [_, _, _, _]) rfl
  have gc : ∀ rest, Det P (x :: rest) (.get (arg 1) (.nat 2)) (.nat cp) _ := fun rest =>
    Det.get' (g1 rest) (Det.nat 2) (vs := [_, _, _, _]) rfl
  have go : ∀ rest, Det P (x :: rest) (.get (arg 1) (.nat 3)) (.nat o) _ := fun rest =>
    Det.get' (g1 rest) (Det.nat 3) (vs := [_, _, _, _]) rfl
  have gP : ∀ rest, Det P (x :: rest) (.get (arg 0) (.nat 0)) (natList Ps) _ := fun rest =>
    Det.get' (g0 rest) (Det.nat 0) (vs := [_, _]) rfl
  have gs : ∀ rest, Det P (x :: rest) (.get (arg 0) (.nat 1)) (.nat s) _ := fun rest =>
    Det.get' (g0 rest) (Det.nat 1) (vs := [_, _]) rfl
  set Lv := natList (domLabs Ps labs) with hLv
  have hgather : FunDet P (d + 18) (.list [natList labs, natList Ps]) Lv
      (gatherK * ((Val.list [natList labs, natList Ps]).wt + 1) ^ 3) := by
    have hg := gather_spec hd.gather (L := labs.map Val.nat) (is := Ps)
      (fun i hi' => by simpa using hi i hi')
    have e1 : Val.list (Ps.map fun i => (labs.map Val.nat).getD i (.nat 0)) = Lv := by
      simp only [hLv, natList, domLabs, List.map_map]
      congr 1
      refine List.map_congr_left fun i hi' => ?_
      have hlen := hi i hi'
      simp [List.getD_eq_getElem?_getD, hlen]
    rw [e1] at hg
    exact hg
  have hmp : FunDet P (d + 9) (.list [Lv, Lv]) (natList (relab Ps labs)) (10 ^ 7 * (2 * Y + 1) ^ 3) :=
    mapPos_spec hd (domLabs Ps labs) (domLabs Ps labs) (by change Lv.wt + Lv.wt ≤ _; omega)
  have d1 := Det.call (Det.mk2 (gl []) (gP [])) hgather
  have d2 := Det.minE (gr [Lv]) (gs [Lv])
  set rr := min r s with hrr
  have d3 := Det.call (Det.mk2 (Det.var' (P := P) (env := [x, Lv, .nat rr]) (i := 1) rfl)
    (Det.var' (P := P) (env := [x, Lv, .nat rr]) (i := 1) rfl)) hmp
  have d4 := Det.var' (P := P) (env := [x, Lv, .nat rr]) (i := 2) rfl
  have d5 := Det.minE (gc [Lv, .nat rr]) (Det.var' (P := P) (env := [x, Lv, .nat rr]) (i := 2) rfl)
  have d6 := Det.minE (go [Lv, .nat rr]) (gs [Lv, .nat rr])
  have d7 := Det.mk4 d3 d4 d5 d6
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 d7)).mono ?_)
  have hlw : (natList labs).wt < (ivEnc (labs, r, cp, o)).wt := wt_le_wt_list (by simp [ivEnc])
  have hrw : (Val.nat r).wt < (ivEnc (labs, r, cp, o)).wt := wt_le_wt_list (by simp [ivEnc])
  have hcw : (Val.nat cp).wt < (ivEnc (labs, r, cp, o)).wt := wt_le_wt_list (by simp [ivEnc])
  have how : (Val.nat o).wt < (ivEnc (labs, r, cp, o)).wt := wt_le_wt_list (by simp [ivEnc])
  have hPw : (natList Ps).wt < c.wt := wt_le_wt_list (by simp [hcdef])
  have hsw : (Val.nat s).wt < c.wt := wt_le_wt_list (by simp [hcdef])
  have hrrw : (Val.nat rr).wt < (ivReset Ps s (labs, r, cp, o)).wt :=
    wt_le_wt_list (by simp [ivReset, hrr])
  have hmw : (natList (relab Ps labs)).wt < (ivReset Ps s (labs, r, cp, o)).wt :=
    wt_le_wt_list (by simp [ivReset])
  have h1 := wt_list2_le (natList labs) (natList Ps)
  have h2 := wt_list2_le Lv Lv
  have hG : gatherK * ((Val.list [natList labs, natList Ps]).wt + 1) ^ 3 ≤
      gatherK * (4 * Y + 7) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e1 : (Val.list [natList (relab Ps labs), .nat rr, .nat (min cp rr), .nat (min o s)]).wt =
      (ivReset Ps s (labs, r, cp, o)).wt := rfl
  have e2 := wt_nat_le r
  have e3 := wt_nat_le cp
  have e4 := wt_nat_le o
  have e5 := wt_nat_le s
  have e8 : (Val.nat (min cp rr)).wt < (ivReset Ps s (labs, r, cp, o)).wt :=
    wt_le_wt_list (by simp [ivReset, hrr])
  have e9 : (Val.nat (min o s)).wt < (ivReset Ps s (labs, r, cp, o)).wt :=
    wt_le_wt_list (by simp [ivReset])
  have e6 : (Val.list [Lv, Lv]).wt ≤ 4 * Y + 6 := by omega
  have e7 : x.wt ≤ 4 * Y + 6 := hxw
  unfold intC
  have hY3 := Nat.le_self_pow (n := 3) (by norm_num) (2 * Y + 1)
  have ex : (Val.list [c, ivEnc (labs, r, cp, o)]).wt = x.wt := rfl
  omega

/-- The step on the whole hierarchy. -/
theorem resetMap_spec {P : Program} {mh f d : ℕ} (hm : P.HasAt mh (mapFuns mh f))
    (hf : P.funs[f]? = some (resetIntBody (d + 18) (d + 9))) (hd : DomAt P d) {Ps : List ℕ} {s : ℕ}
    (xs : List IvData) (hi : ∀ a ∈ xs, ∀ i ∈ Ps, i < a.1.length) {Y : ℕ}
    (hc : (Val.list [natList Ps, .nat s]).wt ≤ Y) (ha : (Val.list (xs.map ivEnc)).wt ≤ Y)
    (hL : ∀ a ∈ xs, (natList (domLabs Ps a.1)).wt ≤ Y)
    (hw : (Val.list (xs.map (ivReset Ps s))).wt ≤ Y) :
    FunDet P mh (.list [.list [natList Ps, .nat s], .list (xs.map ivEnc)])
      (.list (xs.map (ivReset Ps s)))
      (Y * intC Y + mapK * (Y + 1) * (5 * Y + 7)) := by
  have h := mapList_spec hm xs ivEnc (ivReset Ps s) (c := .list [natList Ps, .nat s]) (B := intC Y)
    (fun a _ a' _ he => by rw [ivEnc_injective he])
    (fun a ha' => resetInt_spec hf hd a (hi a ha') hc
      (((wt_le_wt_list (List.mem_map_of_mem ha')).le).trans ha) (hL a ha')
      (((wt_le_wt_list (List.mem_map_of_mem ha')).le).trans hw))
  refine h.mono ?_
  have hlen : xs.length ≤ Y := by
    have := length_lt_wt_list (xs.map ivEnc)
    simp only [List.length_map] at this
    omega
  have h1 := wt_list2_le (Val.list [natList Ps, .nat s]) (Val.list (xs.map ivEnc))
  have h2 : xs.length * intC Y ≤ Y * intC Y := Nat.mul_le_mul_right _ hlen
  have h3 : mapK * (xs.length + 1) * ((Val.list [Val.list [natList Ps, .nat s],
      .list (xs.map ivEnc)]).wt + (Val.list (xs.map (ivReset Ps s))).wt + 1) ≤
      mapK * (Y + 1) * (5 * Y + 7) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  omega

/-- The body of a reset on a state value `v`. -/
def resetBody (prep mh trans lift : ℕ) : Expr :=
  .letE (.call prep (.var 0))
  (.letE (.call mh (mk2 (mk2 (.get (.get (.var 1) (.nat 1)) (.nat 0)) (.get (.var 1) (.nat 2)))
    (arg 5)))
  (.letE (Expr.mkList [.get (.get (.var 1) (.nat 3)) (.nat 0), .get (.get (.var 1) (.nat 3)) (.nat 1),
      .get (.get (.var 1) (.nat 3)) (.nat 2), .get (.get (.var 1) (.nat 3)) (.nat 3),
      .get (.get (.var 1) (.nat 3)) (.nat 4), .var 2, .get (.get (.var 1) (.nat 3)) (.nat 6),
      .get (.get (.var 1) (.nat 3)) (.nat 7), .get (.get (.var 1) (.nat 3)) (.nat 8),
      .get (.get (.var 1) (.nat 3)) (.nat 9)])
  (.letE (.call trans (.var 3))
    (.call lift (mk2 (mk4 (arg 0) (.get (.var 1) (.nat 2)) (.get (.var 1) (.nat 1))
      (.get (.var 1) (.nat 0))) (.var 4))))))

/-- The weight bound in a reset, in `X = wt v + 1`. -/
def resetY (X : ℕ) : ℕ := 10 ^ 6 * (X + 2) ^ 6

/-- The cost of a reset besides the call of `trans`. -/
def resetOwn (pst pp pf : Prim) (X : ℕ) : ℕ :=
  prepCost pst X + liftCost pp pf X + resetY X * intC (resetY X) +
    mapK * (resetY X + 1) * (5 * resetY X + 7) + 10 ^ 4 * (resetY X + 10)

theorem reset_forall₂_left {α β : Type} {R : α → β → Prop} {xs : List α} {l : List β}
    (h : List.Forall₂ R xs l) : ∀ a ∈ xs, ∃ b, R a b := by
  induction h with
  | nil => simp
  | @cons a b xs l hab _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, hab⟩
    · exact ih x hx

/-- **A reset.** -/
theorem reset_spec (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor) {P : Program}
    {f prep mh mi red dom col hier ap rep lo cnt ob jst lift jpre jfac trans : ℕ}
    (hb : P.funs[f]? = some (resetBody prep mh trans lift))
    (hp : PrepAt P prep red dom col hier ap rep lo cnt ob jst)
    (hjs : P.prims[jst]? = some (pointwiseStabPrim hst))
    (hm : P.HasAt mh (mapFuns mh mi))
    (hi : P.funs[mi]? = some (resetIntBody (dom + 18) (dom + 9)))
    (hl : LiftAt P lift dom jpre jfac) (hjp : P.prims[jpre]? = some (preimagePrim hpre))
    (hjf : P.prims[jfac]? = some (normalizedFactorPrim hfac))
    (e : Ω ≃ Fin k) (c : C → ℕ) (T : State Ω C) {v : Val} (hcan : Canon e c v T)
    (h2 : 2 ≤ T.size) (hρ : rhoNat T.hier ≤ T.size) {b : ℝ}
    (htr : ∀ val, Canon (domEquiv e T.dom) (freshCode e c T) val (resetState T) →
      FunAll P trans val (fun u cu => AnsC (domEquiv e T.dom) u (resetState T).answer ∧
        (cu : ℝ) ≤ b)) :
    FunAll P f v (fun w cost => AnsC e w T.answer ∧ (cost : ℝ) ≤
      b + resetOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)
        (v.wt + 1)) := by
  have hsv : StateVal e c v T := hcan.stateVal
  have hkv := StateVal.k_le_wt hsv
  obtain ⟨gv, dv, xv, yv, hv0, rv, -, -, -, -, ⟨vs, rfl, hvs⟩, -, hveq⟩ := id hcan.val
  obtain ⟨xs, rfl, hxs⟩ := exists_ivData e hvs
  set s := (domFin e T.dom).length with hsd
  have hsT : T.size = s := card_dom_eq e T.dom
  have hsk : s ≤ k := length_domFin_le
  set X := v.wt + 1 with hX
  set Y := resetY X with hY
  have hkX : k + 1 ≤ X := by omega
  have hYX : 10 ^ 6 * (X + 2) ^ 6 = Y := rfl
  refine FunAll.intro hb ?_
  have d0 := Det.var' (P := P) (env := [v]) (i := 0) rfl
  refine EvalAll.letE (EvalAll.call_spec d0 (prep_spec hst hp hjs e c T (by omega) hsv)) ?_
  rintro w1 c1 ⟨cb1, ⟨⟨gs₀, hsF, labF, a, hgs₀, hl₀, -, hcan0, rfl, hw1⟩, hcb1⟩, hc1⟩
  set cx := natList (cmpCodes e c T T.x)
  set cy := natList (cmpCodes e c T T.y)
  set gF := encGroup hsF
  set hF := fhierVal (encFun labF) (Nat.card (orb T.domGroup a))
  set Ps := domNat e T.dom with hPs
  have hhv : HierValC (domEquiv e T.dom) (.list (xs.map (ivReset Ps T.size))) (resetHier T) :=
    hierValC_reset e T hxs
  have hcanR := canon_reset T hcan0 hhv hcan.small h2 hρ
  rw [hsT] at hhv hcanR
  set hsV := Val.list (xs.map (ivReset Ps s)) with hhsV
  set v' := freshVal s gF cx cy hsV with hv'
  set v0 := freshVal s gF cx cy hF with hv0
  set w1 := Val.list [encGroup gs₀, domCtx e T.dom, .nat s, v0] with hw1d
  have hP6 : X + 2 ≤ (X + 2) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hk6 : (k + 1) ^ 6 ≤ (X + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hs6 : (s + 2) ^ 6 ≤ (X + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hkk : k * (2 * k + 5) + 4 ≤ 10 * (X + 2) ^ 6 := by
    have h1 : (X + 2) ^ 2 ≤ (X + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : k * (2 * k + 5) ≤ (X + 2) * (3 * (X + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hv'w : v'.wt ≤ 10 ^ 4 * (s + 2) ^ 6 := by
    have := hcanR.wt_le_poly
    have hN : (resetState T).N = s := hsT
    rwa [hN] at this
  have hhw : hsV.wt < v'.wt := wt_le_wt_list (by simp [hv', freshVal])
  have hctx1 : (domCtx e T.dom).wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have hsw1 : (Val.nat s).wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have hPw : (natList Ps).wt < (domCtx e T.dom).wt := wt_le_wt_list (by simp [domCtx, hPs])
  have h0w1 : v0.wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have hcw : (Val.list [natList Ps, .nat s]).wt ≤ Y := by
    have := wt_list2_le (natList Ps) (.nat s)
    omega
  have hlist := wt_le_wt_list (v := .list (xs.map ivEnc))
    (vs := [.nat k, gv, dv, xv, yv, .list (xs.map ivEnc), rv, boolVal T.floor, .nat T.h, .nat T.N])
    (by simp)
  rw [← hveq] at hlist
  have hmap := resetMap_spec hm hi hp.domAt (Ps := Ps) (s := s) xs (fun a ha i hi' => by
      obtain ⟨I, ⟨lab, h1, -, -⟩, -⟩ := reset_forall₂_left hxs a ha
      rw [h1]
      simpa using domNat_lt hi') (Y := Y) hcw (by omega) (fun a ha => by
      obtain ⟨I, ⟨lab, h1, h3, -⟩, -⟩ := reset_forall₂_left hxs a ha
      rw [h1, hPs, domLabs_encFun]
      have h4 := wt_natList_le (xs := (domFin e T.dom).map lab) (B := k) (fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact (h3 i).le)
      have h5 : ((domFin e T.dom).map lab).length ≤ k := by simpa using hsk
      have h6 := Nat.mul_le_mul_right (2 * k + 5) h5
      omega) (by change hsV.wt ≤ Y; omega)
  have ga : Det P [v, w1] (arg 5) (.list (xs.map ivEnc)) (2 * v.wt + 5 + 5) := by
    have := Det.arg' (P := P) (vs := [.nat k, gv, dv, xv, yv, .list (xs.map ivEnc), rv,
      boolVal T.floor, .nat T.h, .nat T.N]) (rest := [w1]) (j := 5) rfl
    rw [← hveq] at this
    exact this
  have g1 := Det.var' (P := P) (env := [v, w1]) (i := 1) rfl
  have gP := Det.get' (Det.get' g1 (Det.nat 1) (v := domCtx e T.dom)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl) (Det.nat 0) (v := natList Ps)
    (vs := [natList Ps, posVal e T.dom]) rfl
  have gs := Det.get' g1 (Det.nat 2) (v := .nat s)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have d2 := Det.call (Det.mk2 (Det.mk2 gP gs) ga) hmap
  refine EvalAll.letE d2 ?_
  rintro _ c2 ⟨rfl, hc2⟩
  have g1' := Det.var' (P := P) (env := [v, w1, hsV]) (i := 1) rfl
  have gv0 := Det.get' g1' (Det.nat 3) (v := v0)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have gf : ∀ (i : ℕ) (u : Val), [Val.nat s, gF, .list (List.replicate s (.nat 1)), cx, cy, hF,
      .list [], .nat 0, .nat 2, .nat s][i]? = some u →
      Det P [v, w1, hsV] (.get (.get (.var 1) (.nat 3)) (.nat i)) u (3 * Y + 40) := by
    intro i u h
    have hi10 : i < 10 := by
      by_contra hc
      rw [List.getElem?_eq_none (by simpa using hc)] at h
      cases h
    have hu : u.wt < v0.wt := wt_le_wt_list (List.mem_of_getElem? h)
    refine (Det.get' gv0 (Det.nat i) (vs := [Val.nat s, gF, .list (List.replicate s (.nat 1)), cx,
      cy, hF, .list [], .nat 0, .nat 2, .nat s]) h).mono ?_
    omega
  have gh : Det P [v, w1, hsV] (.var 2) hsV (3 * Y + 40) :=
    (Det.var' (P := P) (env := [v, w1, hsV]) (i := 2) rfl).mono (by omega)
  have d3 : Det P [v, w1, hsV] (Expr.mkList [.get (.get (.var 1) (.nat 3)) (.nat 0),
      .get (.get (.var 1) (.nat 3)) (.nat 1), .get (.get (.var 1) (.nat 3)) (.nat 2),
      .get (.get (.var 1) (.nat 3)) (.nat 3), .get (.get (.var 1) (.nat 3)) (.nat 4), .var 2,
      .get (.get (.var 1) (.nat 3)) (.nat 6), .get (.get (.var 1) (.nat 3)) (.nat 7),
      .get (.get (.var 1) (.nat 3)) (.nat 8), .get (.get (.var 1) (.nat 3)) (.nat 9)]) v'
      (10 * (3 * Y + 40 + v'.wt + 1) + 5) :=
    Det.mkList (c := 3 * Y + 40) [(.get (.get (.var 1) (.nat 3)) (.nat 0), .nat s),
      (.get (.get (.var 1) (.nat 3)) (.nat 1), gF),
      (.get (.get (.var 1) (.nat 3)) (.nat 2), .list (List.replicate s (.nat 1))),
      (.get (.get (.var 1) (.nat 3)) (.nat 3), cx), (.get (.get (.var 1) (.nat 3)) (.nat 4), cy),
      (.var 2, hsV), (.get (.get (.var 1) (.nat 3)) (.nat 6), .list []),
      (.get (.get (.var 1) (.nat 3)) (.nat 7), .nat 0),
      (.get (.get (.var 1) (.nat 3)) (.nat 8), .nat 2),
      (.get (.get (.var 1) (.nat 3)) (.nat 9), .nat s)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact gf 0 _ rfl
      · exact gf 1 _ rfl
      · exact gf 2 _ rfl
      · exact gf 3 _ rfl
      · exact gf 4 _ rfl
      · exact gh
      · exact gf 6 _ rfl
      · exact gf 7 _ rfl
      · exact gf 8 _ rfl
      · exact gf 9 _ rfl)
  refine EvalAll.letE d3 ?_
  rintro _ c3 ⟨rfl, hc3⟩
  refine EvalAll.letE (EvalAll.call_spec
    (Det.var' (P := P) (env := [v, w1, hsV, v']) (i := 3) rfl) (htr v' hcanR)) ?_
  rintro u' c4 ⟨cb4, ⟨hA', hcb4⟩, hc4⟩
  have hsub : (resetState T).answer ⊆ (restrictHom T.G T.dom T.dom_inv).range := by
    intro g hg
    exact hg.1
  have hlift := lift_spec hpre hfac hl hp.domAt hjp hjf e T hgs₀ hl₀ hA' hsub
  have q1 := Det.arg' (P := P) (vs := [.nat k, gv, dv, xv, yv, .list (xs.map ivEnc), rv,
      boolVal T.floor, .nat T.h, .nat T.N]) (rest := [w1, hsV, v', u']) (j := 0) rfl
  rw [← hveq] at q1
  have g1'' := Det.var' (P := P) (env := [v, w1, hsV, v', u']) (i := 1) rfl
  have q2 := Det.get' g1'' (Det.nat 2) (v := .nat s)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have q3 := Det.get' g1'' (Det.nat 1) (v := domCtx e T.dom)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have q4 := Det.get' g1'' (Det.nat 0) (v := encGroup gs₀)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have q5 := Det.var' (P := P) (env := [v, w1, hsV, v', u']) (i := 4) rfl
  refine (EvalAll.call_spec (Det.mk2 (Det.mk4 q1 q2 q3 q4) q5) hlift).mono ?_
  rintro w c5 ⟨cb5, ⟨hAns, hcb5⟩, hc5⟩
  rw [liftAnswer_reset] at hAns
  refine ⟨hAns, ?_⟩
  have wu := hA'.wt_le
  have wu' : ansW s ≤ 400 * (k + 1) ^ 6 :=
    (ansW_le_pow _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))
  have ww := hAns.wt_le
  have ww' := ansW_le_pow k
  have wctx := wt_liftCtx_le e T.dom hl₀
  have wl2 := wt_list2_le (liftCtx e T.dom gs₀) u'
  have hlc := liftCost_mono (preimagePrim hpre) (normalizedFactorPrim hfac) (show k ≤ X by omega)
  have eL : (Val.list [Val.nat k, Val.nat s, domCtx e T.dom, encGroup gs₀]).wt =
      (liftCtx e T.dom gs₀).wt := rfl
  have eL2 : (Val.list [Val.list [Val.nat k, Val.nat s, domCtx e T.dom, encGroup gs₀], u']).wt =
      (Val.list [liftCtx e T.dom gs₀, u']).wt := rfl
  have hg0 : (encGroup gs₀).wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have e3 : (Val.list [natList Ps, .nat s]).wt ≤ Y := hcw
  have e4 := wt_list2_le (Val.list [natList Ps, .nat s]) (Val.list (xs.map ivEnc))
  have hnat : c1 + (c2 + (c3 + (c4 + c5 + w.wt + 1) + w.wt + 1) + w.wt + 1) + w.wt + 1 ≤
      resetOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) X + cb4 := by
    unfold resetOwn
    rw [← hY]
    have a1 : (Val.list (xs.map (ivReset Ps s))).wt = hsV.wt := rfl
    have a2 : ansW (domFin e T.dom).length = ansW s := rfl
    have a3 : prepCost (pointwiseStabPrim hst) (v.wt + 1) = prepCost (pointwiseStabPrim hst) X := rfl
    omega
  have hnat' : ((c1 + (c2 + (c3 + (c4 + c5 + w.wt + 1) + w.wt + 1) + w.wt + 1) + w.wt + 1 : ℕ) : ℝ) ≤
      ((resetOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) X : ℕ) : ℝ)
        + (cb4 : ℝ) := by exact_mod_cast hnat
  linarith

end GI.Degree
