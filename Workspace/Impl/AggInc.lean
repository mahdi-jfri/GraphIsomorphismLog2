module

public import Workspace.Impl.AggIncMath

@[expose] public section

/-!
# The window increment as a program

`incFuns` computes the increment `V_t` of rules 1 to 4 of Algorithm 2 (`inc_spec`). Its input is
`[[k, q], pairs, x₀, B, a, outside]`: a graph-form generating list of the lift of `A`, the label
points `x₀` of `T`, a bound `B ≥ |Alt(T)|` on orbit sizes, the order `a = |Alt(T)|`, and the
positions of the points outside the window. It follows `incList` (`AggIncMath.lean`): each
test computes the order `|φ_T(A_{(U)})|` with `imgCardFuns` and compares it with `a` or with `1`.
For rule 4 the orbit `v^A` is read off the orbit labels of the encoded pairs on `Fin (k + q)`
(`mem_genOrbit_pairs`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.LocalGroups GI.Endpoint
open GI.Cited (Val encPerm encPerms encGroup encPts gens PointwiseStab)

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- The cost of one order computation, for size parameter `M`. -/
noncomputable def cardCost (h : PointwiseStab) (M : ℕ) : ℕ :=
  (pointwiseStabPrim h).boundSize (200 * M ^ 4) + imgCardK * M ^ 24

theorem boundSize_mono (p : Prim) {B B' : ℕ} (hB : B ≤ B') : p.boundSize B ≤ p.boundSize B' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem cardCost_mono (h : PointwiseStab) {M M' : ℕ} (hM : M ≤ M') :
    cardCost h M ≤ cardCost h M' :=
  Nat.add_le_add (boundSize_mono _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 4)))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 24))

variable (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **The order of `φ_T(A_{(U)})`, deterministically.** -/
theorem imgCardDet (h : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (imgCardFuns b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim h))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps)
    {U : Set S.dom} {X : List (Fin (k + L.q))}
    (hX : ∀ j, j ∈ X ↔ ∃ u ∈ U, Fin.castAdd L.q (e (u : Ω)) = j)
    {B : ℕ} (hB : Nat.card (alternatingGroup T) ≤ B) {M : ℕ}
    (hM : imgM k L.q ps X B T.card ≤ M) :
    FunDet P b (.list [.list [.nat k, .nat L.q], .list (ps.map pairV), encPts X,
      natList (ptsKey (labPts k (tlist T))), .nat B])
      (.nat (cardFix (phiT S.domGroup πd T) A U)) (cardCost h M) := by
  have hl : (labPts k (tlist T)).length = T.card := by
    rw [labPts, List.length_map, length_tlist]
  have hfA : fix A U ≤ Pgrp S.domGroup πd T := (inf_le_left : fix A U ≤ A).trans hA
  refine (imgCard_spec h hb hj ps X (labPts k (tlist T)) (B := B) fun qs hqs => ?_).mono ?_
  · rw [ncard_eq_card_img_fix πd hπ hA hps hX hqs]
    exact (card_img_le πd _).trans hB
  · rintro w c ⟨qs, hqs, rfl, hc⟩
    refine ⟨by rw [ncard_eq_card_img_fix πd hπ hA hps hX hqs]; rfl, ?_⟩
    have h1 := stabBound_le h ps X B (labPts k (tlist T)).length
    rw [hl] at h1 hc
    have h2 := cardCost_mono h hM
    unfold cardCost at h2
    unfold cardCost
    have h3 : imgCardK * imgM k L.q ps X B T.card ^ 24 ≤ imgCardK * M ^ 24 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 24)
    have h4 := boundSize_mono (pointwiseStabPrim h)
      (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hM 4))
    omega

/-! ### The tests -/

/-- A list of five values. -/
def mk5 (a b c d f : Expr) : Expr := .snoc (mk4 a b c d) f

theorem Det.mk5 {P : Program} {env : List Val} {a b c d f : Expr} {va vb vc vd vf : Val}
    {ca cb cc cd cf : ℕ} (ha : Det P env a va ca) (hb : Det P env b vb cb)
    (hc : Det P env c vc cc) (hd : Det P env d vd cd) (hf : Det P env f vf cf) :
    Det P env (mk5 a b c d f) (.list [va, vb, vc, vd, vf])
      (ca + cb + cc + cd + cf + 5 * (Val.list [va, vb, vc, vd, vf]).wt + 10) := by
  have h1 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, vf] from ⟨[vf], rfl⟩)
  exact (Det.snoc (Det.mk4 ha hb hc hd) hf).mono
    (by simp only [List.cons_append, List.nil_append]; omega)

/-- `sameTest`, on `[[lab, i], j]`: whether `lab[j] = lab[i]`. -/
def sameTest : Expr :=
  .arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))

theorem sameTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some sameTest) {n : ℕ}
    (lab : Fin n → ℕ) (i j : Fin n) :
    FunDet P f (.list [.list [encFun lab, .nat i], .nat j]) (boolVal (decide (lab j = lab i)))
      (20 * (Val.list [.list [encFun lab, .nat i], .nat j]).wt + 50) := by
  set v : Val := .list [.list [encFun lab, .nat i], .nat j] with hv
  have a0 := Det.arg' (P := P) (vs := [.list [encFun lab, .nat i], .nat j]) (rest := []) (j := 0)
    rfl
  have a1 := Det.arg' (P := P) (vs := [.list [encFun lab, .nat i], .nat j]) (rest := []) (j := 1)
    rfl
  have l0 := Det.get' a0 (Det.nat 0) (v := encFun lab) rfl
  have i0 := Det.get' a0 (Det.nat 1) (v := .nat i) rfl
  have gj := Det.get' l0 a1 (v := .nat (lab j)) (encFun_getElem? lab j)
  have gi := Det.get' l0 i0 (v := .nat (lab i)) (encFun_getElem? lab i)
  have d := Det.arith' (op := .eq) gj gi (z := (decide (lab j = lab i)).toNat)
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp_all)
  refine FunDet.intro hf (d.mono ?_)
  have w1 : (Val.list [encFun lab, .nat i]).wt < v.wt := wt_le_wt_list (by simp)
  have w2 : (Val.nat j).wt < v.wt := wt_le_wt_list (by simp)
  have ev : (Val.list [Val.list [encFun lab, Val.nat i], Val.nat j]).wt = v.wt := rfl
  have w3 : (encFun lab).wt < (Val.list [encFun lab, .nat i]).wt := wt_le_wt_list (by simp)
  have w4 : (Val.nat i).wt < (Val.list [encFun lab, .nat i]).wt := wt_le_wt_list (by simp)
  have w5 : (Val.nat (lab j)).wt < (encFun lab).wt := wt_le_wt_list (by
    simp only [List.mem_map, List.mem_finRange, true_and]; exact ⟨j, rfl⟩)
  have w6 : (Val.nat (lab i)).wt < (encFun lab).wt := wt_le_wt_list (by
    simp only [List.mem_map, List.mem_finRange, true_and]; exact ⟨i, rfl⟩)
  have : (decide (lab j = lab i)).toNat ≤ 1 := Bool.toNat_le _
  omega

theorem encPts_eq_natList {n : ℕ} (X : List (Fin n)) : encPts X = natList (X.map Fin.val) := by
  rw [encPts_eq, natList, List.map_map]; rfl

theorem wt_encPts_le_sq {n : ℕ} {X : List (Fin n)} {B : ℕ} (hn : n ≤ B) (hl : X.length ≤ B) :
    (encPts X).wt ≤ 5 * (B + 1) ^ 2 := by
  rw [encPts_eq_natList]
  refine wt_natList_le_sq (fun x hx => ?_) (by rw [List.length_map]; exact hl)
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  have := j.isLt; omega

/-- The test of `sameTest` on values. -/
def sameQ {n : ℕ} (lab : Fin n → ℕ) (i : Fin n) : Val → Bool
  | .nat m => if h : m < n then decide (lab ⟨m, h⟩ = lab i) else false
  | _ => false

/-- **The positions in the orbit of `i`**: the filter of `range n` by `sameTest`. -/
theorem sameX_spec {P : Program} {f p : ℕ} (hfl : P.HasAt f (filterFuns f p))
    (hp : P.funs[p]? = some sameTest) {n : ℕ} (lab : Fin n → ℕ) (i : Fin n) {Wc : ℕ}
    (hW : (Val.list [encFun lab, .nat i]).wt ≤ Wc) (hn : n ≤ Wc) :
    FunDet P f (.list [.list [encFun lab, .nat i], natList (List.range n)])
      (encPts ((List.finRange n).filter (fun j => lab j = lab i)))
      (10 ^ 5 * (Wc + 1) ^ 3) := by
  have hxs : natList (List.range n) = .list ((List.range n).map Val.nat) := rfl
  rw [hxs]
  have hval : ((List.range n).map Val.nat).filter (sameQ lab i) =
      ((List.finRange n).filter (fun j => lab j = lab i)).map fun j => Val.nat j.val := by
    rw [← List.map_coe_finRange_eq_range, List.map_map, List.filter_map]
    rw [show (Val.nat ∘ fun x : Fin n => (x : ℕ)) = fun j => Val.nat j.val from rfl]
    congr 1
    apply List.filter_congr
    intro j _
    simp [sameQ, j.isLt]
  refine (filter_spec hfl (q := sameQ lab i)
    (B := fun _ => 20 * (2 * (Wc + n + 2) + 6) + 50) fun x hx => ?_).mono ?_
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    have hm' : m < n := List.mem_range.1 hm
    refine FunAll.mono (sameTest_spec hp lab i ⟨m, hm'⟩) fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
    · rw [hw]; simp [sameQ, hm']
    · have h1 := wt_list2_le (.list [encFun lab, .nat i]) (.nat m)
      have h2 := wt_nat_le m
      have e1 : (Val.list [Val.list [encFun lab, .nat i], Val.nat ((⟨m, hm'⟩ : Fin n) : ℕ)]).wt =
        (Val.list [Val.list [encFun lab, .nat i], .nat m]).wt := rfl
      show c ≤ 20 * (2 * (Wc + n + 2) + 6) + 50
      omega
  · rintro w c ⟨rfl, hc⟩
    refine ⟨by rw [hval, encPts_eq], ?_⟩
    rw [List.map_const', List.sum_replicate, List.length_map, List.length_range,
      smul_eq_mul] at hc
    rw [hval] at hc
    have hw1 : (Val.list ((List.range n).map Val.nat)).wt ≤ 5 * (Wc + 1) ^ 2 := by
      rw [← hxs]
      exact wt_natList_le_sq (fun x hx => by have := List.mem_range.1 hx; omega)
        (by rw [List.length_range]; exact hn)
    have hw2 : (Val.list (((List.finRange n).filter (fun j => lab j = lab i)).map
        fun j => Val.nat j.val)).wt ≤ 5 * (Wc + 1) ^ 2 := by
      rw [← encPts_eq]
      exact wt_encPts_le_sq hn ((List.length_filter_le _ _).trans (by simp [hn]))
    have h3 := wt_list2_le (.list [encFun lab, .nat i]) (.list ((List.range n).map Val.nat))
    have h4 : n * (20 * (2 * (Wc + n + 2) + 6) + 50) ≤ 330 * (Wc + 1) ^ 2 := by
      have : n * (20 * (2 * (Wc + n + 2) + 6) + 50) ≤ (Wc + 1) * (330 * (Wc + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    have h5 : loopModK * (n + 1) * ((Val.list [Val.list [encFun lab, .nat i],
        Val.list ((List.range n).map Val.nat)]).wt + n + (Val.list (((List.finRange n).filter
          (fun j => lab j = lab i)).map fun j => Val.nat j.val)).wt + 1) ≤
        loopModK * (Wc + 1) * (40 * (Wc + 1) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
        have : Wc + 1 ≤ (Wc + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
        omega)
    have e5 : loopModK * (Wc + 1) * (40 * (Wc + 1) ^ 2) = 40000 * (Wc + 1) ^ 3 := by
      simp only [loopModK]; ring
    have : (Wc + 1) ^ 2 ≤ (Wc + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    clear hval
    omega

/-- Entry `j` of entry `0` of the argument. -/
def arg0 (j : ℕ) : Expr := .get (arg 0) (.nat j)

theorem Det.arg0 {P : Program} {us vs rest : List Val} {j : ℕ} {v : Val}
    (hj : us[j]? = some v) :
    Det P (.list (.list us :: vs) :: rest) (GI.Impl.arg0 j) v
      (3 * (Val.list (.list us :: vs)).wt + j + 9) := by
  have h0 := Det.arg' (P := P) (vs := .list us :: vs) (rest := rest) (j := 0) rfl
  have hw : v.wt < (Val.list us).wt := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact wt_getElem_lt us j h
  have hu : (Val.list us).wt < (Val.list (.list us :: vs)).wt := wt_le_wt_list (by simp)
  exact (Det.get' h0 (Det.nat j) hj).mono (by omega)

/-- `affTest`, on `[input, i]`: whether `|φ_T(A_{({i})})| ≠ a`. The input is
`[[k, q], pairs, x₀, B, a, outside]`; the order is computed by `imgCardFuns` at `bI`. -/
def affTest (bI : ℕ) : Expr :=
  .arith .eq (.arith .eq (.call bI (mk5 (arg0 0) (arg0 1) (mk1 (arg 1)) (arg0 2) (arg0 3)))
    (arg0 4)) (.nat 0)

theorem affTest_spec {P : Program} {f bI : ℕ} (hf : P.funs[f]? = some (affTest bI))
    (kqV psV x0V BV outV : Val) (a i r cI : ℕ)
    (hI : FunDet P bI (.list [kqV, psV, .list [.nat i], x0V, BV]) (.nat r) cI) :
    FunDet P f (.list [.list [kqV, psV, x0V, BV, .nat a, outV], .nat i])
      (boolVal (decide (r ≠ a)))
      (cI + 100 * (Val.list [.list [kqV, psV, x0V, BV, .nat a, outV], .nat i]).wt + r + 100) := by
  set W := (Val.list [.list [kqV, psV, x0V, BV, .nat a, outV], .nat i]).wt with hW
  have f0 := Det.arg0 (P := P) (us := [kqV, psV, x0V, BV, .nat a, outV]) (vs := [.nat i])
    (rest := []) (j := 0) rfl
  have f1 := Det.arg0 (P := P) (us := [kqV, psV, x0V, BV, .nat a, outV]) (vs := [.nat i])
    (rest := []) (j := 1) rfl
  have f2 := Det.arg0 (P := P) (us := [kqV, psV, x0V, BV, .nat a, outV]) (vs := [.nat i])
    (rest := []) (j := 2) rfl
  have f3 := Det.arg0 (P := P) (us := [kqV, psV, x0V, BV, .nat a, outV]) (vs := [.nat i])
    (rest := []) (j := 3) rfl
  have f4 := Det.arg0 (P := P) (us := [kqV, psV, x0V, BV, .nat a, outV]) (vs := [.nat i])
    (rest := []) (j := 4) rfl
  have a1 := Det.arg' (P := P) (vs := [.list [kqV, psV, x0V, BV, .nat a, outV], .nat i])
    (rest := []) (j := 1) rfl
  have dI := Det.call (Det.mk5 f0 f1 (Det.mk1 a1) f2 f3) hI
  have d1 := Det.arith' (op := .eq) dI f4 (z := (decide (r = a)).toNat)
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp_all)
  have d2 := Det.arith' (op := .eq) d1 (Det.nat 0) (z := (decide (r ≠ a)).toNat)
    (by simp only [GI.Machine.BinOp.eval]; by_cases h : r = a <;> simp [h])
  refine FunDet.intro hf (d2.mono ?_)
  have hu : (Val.list [kqV, psV, x0V, BV, .nat a, outV]).wt < W := wt_le_wt_list (by simp)
  have hk : kqV.wt < (Val.list [kqV, psV, x0V, BV, .nat a, outV]).wt := wt_le_wt_list (by simp)
  have hp : psV.wt < (Val.list [kqV, psV, x0V, BV, .nat a, outV]).wt := wt_le_wt_list (by simp)
  have hx : x0V.wt < (Val.list [kqV, psV, x0V, BV, .nat a, outV]).wt := wt_le_wt_list (by simp)
  have hB : BV.wt < (Val.list [kqV, psV, x0V, BV, .nat a, outV]).wt := wt_le_wt_list (by simp)
  have hi : (Val.nat i).wt < W := wt_le_wt_list (by simp)
  have h1 := wt_list_le [kqV, psV, .list [.nat i], x0V, BV]
  have h2 := wt_list_le [Val.nat i]
  simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at h1 h2
  have h3 := wt_nat_le r
  have h4 : (decide (r = a)).toNat ≤ 1 := Bool.toNat_le _
  have h5 : (decide (r ≠ a)).toNat ≤ 1 := Bool.toNat_le _
  omega

/-- The cost bound of `range n`. -/
def rangeCost (n : ℕ) : ℕ :=
  loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)

/-- Entry `j` of the input inside the context `[input, labels]` of `visTest`. -/
def inpF (j : ℕ) : Expr := .get (.get (arg 0) (.nat 0)) (.nat j)

theorem Det.inpF {P : Program} {us : List Val} {lab : Val} {rest rest' : List Val} {j : ℕ}
    {v : Val} (hj : us[j]? = some v) :
    Det P (.list (.list [.list us, lab] :: rest) :: rest') (GI.Impl.inpF j) v
      (4 * (Val.list (.list [.list us, lab] :: rest)).wt + j + 20) := by
  have h0 := Det.arg0 (P := P) (us := [.list us, lab]) (vs := rest) (rest := rest') (j := 0) rfl
  have hw : v.wt < (Val.list us).wt := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact wt_getElem_lt us j h
  have hu : (Val.list us).wt < (Val.list [.list us, lab]).wt := wt_le_wt_list (by simp)
  have hu' : (Val.list [.list us, lab]).wt < (Val.list (.list [.list us, lab] :: rest)).wt :=
    wt_le_wt_list (by simp)
  exact (Det.get' h0 (Det.nat j) hj).mono (by omega)

/-- `visTest`, on `[[input, labels], i]`: whether `|φ_T(A_{(Δ)})| = 1` for the orbit `Δ` of
`i`. The positions of `Δ` are the `j < k + q` with the label of `i`, found by the filter at `bS`
of `range (k + q)` (at `bR`). -/
def visTest (bI bS bR : ℕ) : Expr :=
  .letE (.call bS (mk2 (mk2 (.get (arg 0) (.nat 1)) (arg 1))
      (.call bR (.arith .add (.get (inpF 0) (.nat 0)) (.get (inpF 0) (.nat 1))))))
    (.arith .eq (.call bI (mk5 (inpF 0) (inpF 1) (.var 1) (inpF 2) (inpF 3))) (.nat 1))

theorem visTest_spec {P : Program} {f bI bS bR : ℕ} (hf : P.funs[f]? = some (visTest bI bS bR))
    (hR : P.HasAt bR (rangeFuns bR))
    (k q : ℕ) (psV x0V BV aV outV labV XV : Val) (i r cI cS : ℕ)
    (hS : FunDet P bS (.list [.list [labV, .nat i], natList (List.range (k + q))]) XV cS)
    (hI : FunDet P bI (.list [.list [.nat k, .nat q], psV, XV, x0V, BV]) (.nat r) cI) :
    FunDet P f (.list [.list [.list [.list [.nat k, .nat q], psV, x0V, BV, aV, outV], labV],
        .nat i])
      (boolVal (decide (r = 1)))
      (cI + cS + 2 * rangeCost (k + q) + 200 * (Val.list [.list [.list [.list [.nat k, .nat q], psV,
        x0V, BV, aV, outV], labV], .nat i]).wt + 20 * XV.wt + r + 10 * (k + q) + 300) := by
  set us : List Val := [.list [.nat k, .nat q], psV, x0V, BV, aV, outV] with hus
  set W := (Val.list [.list [.list us, labV], .nat i]).wt with hW
  have f0 := Det.inpF (P := P) (us := us) (lab := labV) (rest := [.nat i]) (rest' := []) (j := 0)
    (v := .list [.nat k, .nat q]) rfl
  have gk := Det.get' f0 (Det.nat 0) (v := .nat k) rfl
  have gq := Det.get' f0 (Det.nat 1) (v := .nat q) rfl
  have dn := Det.arith' (op := .add) gk gq (z := k + q) rfl
  have dR := Det.call dn ((range_spec hR (k + q)).mono fun w c ⟨hw, hc⟩ => ⟨hw, by
    rw [hw] at hc; exact hc⟩)
  have dl := Det.arg0 (P := P) (us := [.list us, labV]) (vs := [.nat i]) (rest := []) (j := 1)
    rfl
  have a1 := Det.arg' (P := P) (vs := [.list [.list us, labV], .nat i]) (rest := []) (j := 1) rfl
  have dX := Det.call (Det.mk2 (Det.mk2 dl a1) dR) hS
  -- the body after the `let`
  have g0 := Det.inpF (P := P) (us := us) (lab := labV) (rest := [.nat i]) (rest' := [XV]) (j := 0)
    (v := .list [.nat k, .nat q]) rfl
  have g1 := Det.inpF (P := P) (us := us) (lab := labV) (rest := [.nat i]) (rest' := [XV]) (j := 1)
    (v := psV) rfl
  have g2 := Det.inpF (P := P) (us := us) (lab := labV) (rest := [.nat i]) (rest' := [XV]) (j := 2)
    (v := x0V) rfl
  have g3 := Det.inpF (P := P) (us := us) (lab := labV) (rest := [.nat i]) (rest' := [XV]) (j := 3)
    (v := BV) rfl
  have gX := Det.var' (P := P) (env := [Val.list [.list [.list us, labV], .nat i], XV]) (i := 1) rfl
  have dI := Det.call (Det.mk5 g0 g1 gX g2 g3) hI
  have d1 := Det.arith' (op := .eq) dI (Det.nat 1) (z := (decide (r = 1)).toNat)
    (by simp only [GI.Machine.BinOp.eval]; by_cases h : r = 1 <;> simp [h])
  refine FunDet.intro hf ((Det.letE dX d1).mono ?_)
  -- the cost
  have hl : (Val.list [.list us, labV]).wt < W := wt_le_wt_list (by simp)
  have hu : (Val.list us).wt < (Val.list [.list us, labV]).wt := wt_le_wt_list (by simp)
  have hlab : labV.wt < (Val.list [.list us, labV]).wt := wt_le_wt_list (by simp)
  have hk : (Val.list [.nat k, .nat q]).wt < (Val.list us).wt := wt_le_wt_list (by simp [hus])
  have hp : psV.wt < (Val.list us).wt := wt_le_wt_list (by simp [hus])
  have hx : x0V.wt < (Val.list us).wt := wt_le_wt_list (by simp [hus])
  have hB : BV.wt < (Val.list us).wt := wt_le_wt_list (by simp [hus])
  have hi : (Val.nat i).wt < W := wt_le_wt_list (by simp)
  have wk : (Val.nat k).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have wq : (Val.nat q).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have h1 := wt_list_le [Val.list [.nat k, .nat q], psV, XV, x0V, BV]
  have h2 := wt_list2_le (.list [labV, .nat i]) (natList (List.range (k + q)))
  have h3 := wt_list2_le labV (.nat i)
  have h5 : (Val.list [Val.list [.list us, labV], .nat i]).wt = W := rfl
  simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at h1
  have h6 := wt_nat_le r
  have h7 : (decide (r = 1)).toNat ≤ 1 := Bool.toNat_le _
  have er : rangeCost (k + q) = loopModK * (k + q + 1) *
      ((Val.nat (k + q)).wt + (k + q) + (natList (List.range (k + q))).wt + 1) := rfl
  have h8 : 1000 * ((natList (List.range (k + q))).wt + 1) ≤ rangeCost (k + q) := by
    rw [er]
    exact Nat.mul_le_mul (by simp only [loopModK]; omega) (by omega)
  have h9 : (Val.list [Val.list [.list us, labV], .nat i, XV]).wt ≤ W + 2 * XV.wt + 2 :=
    wt_list_snoc_le [Val.list [.list us, labV], .nat i] XV
  have h10 := wt_list_le [Val.list [.list us, labV], Val.nat i, XV]
  have h11 : (Val.list [.nat k, .nat q]).wt ≤ 2 * ((Val.nat k).wt + (Val.nat q).wt) + 6 :=
    wt_list2_le _ _
  simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at h10
  have h12 : (Val.nat (decide (r = 1)).toNat).wt ≤ 3 := wt_boolVal_le _
  have h13 := wt_nat_le (k + q)
  have h14 := sum_wt_lt_wt_list us
  rw [hus] at h14
  simp only [List.map, List.sum_cons, List.sum_nil] at h14
  have hc : (Val.list us).wt =
    (Val.list [.list [.nat k, .nat q], psV, x0V, BV, aV, outV]).wt := rfl
  clear dX d1 dR dn gk gq f0 g0 g1 g2 g3 gX dI dl a1
  rw [← er] at *
  omega

/-! ### The increment program -/

/-- The body of the increment program at base `b`. On `[[k, q], pairs, x₀, B, a, outside]`:
rule 1 compares `|φ_T(A)|` with `a`; rule 2 filters `outside` by `affTest`; rule 3 compares
`|φ_T(A_{(outside)})|` with `a`; rule 4 computes the orbit labels of the encoded pairs and
filters `outside` by `visTest`. -/
def incEntry (b : ℕ) : Expr :=
  .ite (.arith .eq (.call (b + 1) (mk5 (arg 0) (arg 1) .nil (arg 2) (arg 3))) (arg 4))
    (.letE (.call (b + 73) (mk2 (.var 0) (arg 5)))
      (.ite (.length (.var 1)) (.var 1) (rule3E b)))
    .nil
where
  /-- Rules 3 and 4, in the environment `[input, affected]`. -/
  rule3E (b : ℕ) : Expr :=
    .ite (.arith .eq (.call (b + 1) (mk5 (arg 0) (arg 1) (arg 5) (arg 2) (arg 3))) (arg 4))
      .nil (rule4E b)
  /-- Rule 4, in the environment `[input, affected]`. -/
  rule4E (b : ℕ) : Expr :=
    .letE (.call (b + 100) (mk2 (.arith .add (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))
        (.call (b + 87) (mk2 (.get (arg 0) (.nat 0)) (arg 1)))))
      (.call (b + 77) (mk2 (mk2 (.var 0) (.var 2)) (arg 5)))

/-- The increment program at base `b` (132 functions), with the stabilizer primitive at `jp`. -/
def incFuns (b jp : ℕ) : List Expr :=
  [incEntry b] ++ imgCardFuns (b + 1) jp ++ [affTest (b + 1)] ++ filterFuns (b + 73) (b + 72) ++
    [visTest (b + 1) (b + 81) (b + 84)] ++ filterFuns (b + 77) (b + 76) ++ [sameTest] ++
    filterFuns (b + 81) (b + 80) ++ rangeFuns (b + 84) ++ pEncMapFuns (b + 87) ++
    orbitFuns (b + 100)

/-- The size parameter of the increment program. -/
def incM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) (B t o : ℕ) : ℕ :=
  k + q + ps.length + B + t + o + 20

/-- The position of a point of the domain in `Fin (k + q)`. -/
def domPos (e : Ω ≃ Fin k) (q : ℕ) (u : S.dom) : Fin (k + q) := Fin.castAdd q (e (u : Ω))

theorem posOf_injective (e : Ω ≃ Fin k) (q : ℕ) : Function.Injective (domPos (S := S) e q) :=
  fun u v h => Subtype.ext (e.injective (Fin.castAdd_injective _ _ h))

/-- A test on points, read on the values of their positions. -/
noncomputable def qOf (e : Ω ≃ Fin k) (q : ℕ) (t : S.dom → Bool) : Val → Bool := by
  classical
  exact fun x => decide (∃ v : S.dom, x = .nat (domPos e q v : ℕ) ∧ t v = true)

theorem qOf_pos (e : Ω ≃ Fin k) (q : ℕ) (t : S.dom → Bool) (v : S.dom) :
    qOf e q t (.nat (domPos e q v : ℕ)) = t v := by
  unfold qOf
  by_cases hv : t v = true
  · simp only [hv, decide_eq_true_eq]
    exact ⟨v, rfl, hv⟩
  · simp only [Bool.not_eq_true] at hv
    rw [hv]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro u hu
    have : domPos e q u = domPos e q v := Fin.ext (by simpa using hu.symm)
    rw [posOf_injective e q this, hv]
    simp

theorem filter_qOf (e : Ω ≃ Fin k) (q : ℕ) (t : S.dom → Bool) (os : List S.dom) :
    (os.map fun v => Val.nat (domPos e q v : ℕ)).filter (qOf e q t) =
      (os.filter t).map fun v => Val.nat (domPos e q v : ℕ) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro v _
  exact qOf_pos e q t v

theorem encPts_map_posOf (e : Ω ≃ Fin k) (q : ℕ) (os : List S.dom) :
    encPts (os.map (domPos e q)) = .list (os.map fun v => Val.nat (domPos e q v : ℕ)) := by
  rw [encPts_eq, List.map_map]; rfl

theorem _root_.GI.Lang.Program.HasAt.right' {P : Program} {b n : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B))
    (hl : A.length = n) : P.HasAt (b + n) B := hl ▸ h.right

theorem length_imgCardFuns (b jp : ℕ) : (imgCardFuns b jp).length = 71 := rfl
theorem length_filterFuns (b p : ℕ) : (filterFuns b p).length = 3 := rfl
theorem length_rangeFuns (b : ℕ) : (rangeFuns b).length = 3 := rfl
theorem length_pEncMapFuns (b : ℕ) : (pEncMapFuns b).length = 13 := rfl

/-- Where the pieces of the increment program sit. -/
theorem incFuns_parts {P : Program} {b jp : ℕ} (hb : P.HasAt b (incFuns b jp)) :
    P.funs[b]? = some (incEntry b) ∧ P.HasAt (b + 1) (imgCardFuns (b + 1) jp) ∧
    P.funs[b + 72]? = some (affTest (b + 1)) ∧
    P.HasAt (b + 73) (filterFuns (b + 73) (b + 72)) ∧
    P.funs[b + 76]? = some (visTest (b + 1) (b + 81) (b + 84)) ∧
    P.HasAt (b + 77) (filterFuns (b + 77) (b + 76)) ∧
    P.funs[b + 80]? = some sameTest ∧
    P.HasAt (b + 81) (filterFuns (b + 81) (b + 80)) ∧
    P.HasAt (b + 84) (rangeFuns (b + 84)) ∧
    P.HasAt (b + 87) (pEncMapFuns (b + 87)) ∧
    P.HasAt (b + 100) (orbitFuns (b + 100)) := by
  unfold incFuns at hb
  have l1 := length_imgCardFuns (b + 1) jp
  have l2 := length_filterFuns (b + 73) (b + 72)
  have l3 := length_filterFuns (b + 77) (b + 76)
  have l4 := length_filterFuns (b + 81) (b + 80)
  have l5 := length_rangeFuns (b + 84)
  have l6 := length_pEncMapFuns (b + 87)
  refine ⟨hb.left.left.left.left.left.left.left.left.left.left.single,
    hb.left.left.left.left.left.left.left.left.left.right,
    (hb.left.left.left.left.left.left.left.left.right' ?_).single,
    hb.left.left.left.left.left.left.left.right' ?_,
    (hb.left.left.left.left.left.left.right' ?_).single,
    hb.left.left.left.left.left.right' ?_,
    (hb.left.left.left.left.right' ?_).single,
    hb.left.left.left.right' ?_, hb.left.left.right' ?_, hb.left.right' ?_, hb.right' ?_⟩ <;>
  simp only [List.length_append, List.length_singleton, l1, l2, l3, l4, l5, l6]

/-- The cost constant of the increment program. -/
def incK : ℕ := 10 ^ 14

set_option maxHeartbeats 2000000 in
/-- **The increment program computes the increment** `V_t` of rules 1 to 4, as the positions of
the points of `incList` (`incList_toFinset`). Its cost is at most `2|outside| + 2` order
computations and a polynomial in the size parameter `M`. -/
theorem inc_spec (h : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (incFuns b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim h))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps)
    (W : Set S.dom) {os : List S.dom} (hos : ∀ v, v ∈ os ↔ v ∉ W)
    {B : ℕ} (hB : Nat.card (alternatingGroup T) ≤ B) :
    FunDet P b (.list [.list [.nat k, .nat L.q], .list (ps.map pairV),
        natList (ptsKey (labPts k (tlist T))), .nat B, .nat (Nat.card (alternatingGroup T)),
        encPts (os.map (domPos e L.q))])
      (encPts ((incList (phiT S.domGroup πd T) A W os (Nat.card (alternatingGroup T))).map
        (domPos e L.q)))
      ((2 * os.length + 2) * cardCost h (2 * incM k L.q ps B T.card os.length) +
        incK * incM k L.q ps B T.card os.length ^ 12) := by
  classical
  set φ := phiT S.domGroup πd T with hφ
  set a := Nat.card (alternatingGroup T) with ha
  set M := incM k L.q ps B T.card os.length with hM
  set kqV : Val := .list [.nat k, .nat L.q] with hkqV
  set psV : Val := .list (ps.map pairV) with hpsV
  set x0V : Val := natList (ptsKey (labPts k (tlist T))) with hx0V
  set outV : Val := encPts (os.map (domPos e L.q)) with houtV
  set inp : Val := .list [kqV, psV, x0V, .nat B, .nat a, outV] with hinp
  set posV : S.dom → Val := fun v => .nat (domPos e L.q v : ℕ) with hposV
  have hout : outV = .list (os.map posV) := encPts_map_posOf e L.q os
  -- where the pieces sit
  obtain ⟨hentry, hI, hAff, hFA, hVis, hFV, hSame, hFS, hR, hPE, hO⟩ := incFuns_parts hb
  -- the size parameter
  have hMd : k + L.q + ps.length + B + T.card + os.length + 20 = M := rfl
  have hcard : ∀ (U : Set S.dom) (X : List (Fin (k + L.q))),
      (∀ j, j ∈ X ↔ ∃ u ∈ U, Fin.castAdd L.q (e (u : Ω)) = j) → X.length ≤ k + L.q + os.length →
      FunDet P (b + 1) (.list [kqV, psV, encPts X, x0V, .nat B]) (.nat (cardFix φ A U))
        (cardCost h (2 * M)) := fun U X hX hl =>
    imgCardDet πd h hI hj hπ hA hps hX hB (by unfold imgM; omega)
  have hle : ∀ U, cardFix φ A U ≤ a := fun U => card_img_le πd _
  -- reading the input
  have ar : ∀ (rest : List Val) (j : ℕ) (v : Val),
      [kqV, psV, x0V, .nat B, .nat a, outV][j]? = some v →
      Det P (inp :: rest) (arg j) v (2 * inp.wt + j + 5) := fun rest j v hv =>
    Det.arg' (vs := [kqV, psV, x0V, .nat B, .nat a, outV]) (rest := rest) hv
  -- rule 1
  have e0 : encPts ([] : List (Fin (k + L.q))) = .list [] := by simp [encPts_eq]
  have d0 := Det.call (Det.mk5 (ar [] 0 kqV rfl) (ar [] 1 psV rfl) Det.nil (ar [] 2 x0V rfl)
    (ar [] 3 (.nat B) rfl)) (e0 ▸ hcard ∅ [] (by simp) (by simp))
  set Wi := inp.wt with hWi
  -- weights in terms of `M`
  have hM20 : 20 ≤ M := by omega
  have pw : ∀ i j : ℕ, i ≤ j → M ^ i ≤ M ^ j := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have hM2 : M * M = M ^ 2 := by ring
  have hM3 : M * M ^ 2 = M ^ 3 := by ring
  have hM1 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have hMM : 20 * M ≤ M ^ 2 := by rw [← hM2]; exact Nat.mul_le_mul_right _ hM20
  have hMM3 : 20 * M ^ 2 ≤ M ^ 3 := by rw [← hM3]; exact Nat.mul_le_mul_right _ hM20
  have wOut : outV.wt ≤ 5 * (M + 1) ^ 2 :=
    wt_encPts_le_sq (by omega) (by rw [List.length_map]; omega)
  have e1 : (M + 1) ^ 2 = M ^ 2 + 2 * M + 1 := by ring
  have wPs : psV.wt ≤ 50 * M ^ 3 := by
    have h1 := wt_pairList_le ps
    have h2 := Nat.pow_le_pow_left (show pM k L.q ps ≤ M by unfold pM; omega) 3
    have h3 : psV.wt = (Val.list (ps.map pairV)).wt := rfl
    omega
  have wX0 : x0V.wt ≤ 3 * M ^ 2 + 4 := by
    have h1 := wt_ptsKey_le (labPts k (tlist T))
    rw [labPts, List.length_map, length_tlist] at h1
    have : T.card * (2 * (k + L.q) + 5) ≤ M * (3 * M) := Nat.mul_le_mul (by omega) (by omega)
    rw [hx0V, labPts]
    nlinarith
  have wKq := wt_list2_le (.nat k) (.nat L.q)
  have wk := wt_nat_le k
  have wq := wt_nat_le L.q
  have wB := wt_nat_le B
  have wa := wt_nat_le a
  have hWb : Wi ≤ 400 * M ^ 3 := by
    have h1 := wt_list_le [kqV, psV, x0V, .nat B, .nat a, outV]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at h1
    have h2 : Wi = (Val.list [kqV, psV, x0V, .nat B, .nat a, outV]).wt := rfl
    have h3 : kqV.wt = (Val.list [.nat k, .nat L.q]).wt := rfl
    omega
  -- the per-point costs
  set KA := cardCost h (2 * M) + 200 * Wi + 300 * M + a + 2000 with hKA
  set tA : S.dom → Bool := fun v => decide (cardFix φ A {v} ≠ a) with htA
  set tV : S.dom → Bool := fun v => decide (cardFix φ A (Endpoint.orb A v) = 1) with htV
  have hdp : ∀ v : S.dom, (domPos e L.q v : ℕ) < k + L.q := fun v => (domPos e L.q v).isLt
  -- rule 2: the affected points
  have fA : FunDet P (b + 73) (.list [inp, outV]) (.list ((os.filter tA).map posV))
      (os.length * KA + loopModK * (os.length + 1) * ((Val.list [inp, outV]).wt + os.length +
        (Val.list ((os.filter tA).map posV)).wt + 1)) := by
    rw [hout]
    refine (filter_spec hFA (q := qOf e L.q tA) (B := fun _ => KA) fun x hx => ?_).mono ?_
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
      have hIv := hcard {v} [domPos e L.q v] (by simp [domPos, eq_comm])
        (by have := (e (v : Ω)).isLt; simp; omega)
      rw [show encPts [domPos e L.q v] = .list [.nat (domPos e L.q v : ℕ)] by simp [encPts_eq]]
        at hIv
      refine FunAll.mono (affTest_spec hAff kqV psV x0V (.nat B) outV a _ _ _ hIv)
        fun w c ⟨hw, hc⟩ => ⟨by rw [hw, hposV, qOf_pos], ?_⟩
      have h1 := wt_list2_le inp (.nat (domPos e L.q v : ℕ))
      have h2 := wt_nat_le (domPos e L.q v : ℕ)
      have h3 := hdp v
      have h4 := hle {v}
      have h5 : (Val.list [.list [kqV, psV, x0V, .nat B, .nat a, outV],
        .nat (domPos e L.q v : ℕ)]).wt = (Val.list [inp, .nat (domPos e L.q v : ℕ)]).wt := rfl
      show c ≤ KA
      omega
    · rintro w c ⟨rfl, hc⟩
      refine ⟨by rw [hposV, filter_qOf], ?_⟩
      rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
      rw [hposV, filter_qOf] at hc
      exact hc
  -- rule 4: the visible orbits
  set lab := orbitLabels (ps.map encPair) with hlab
  have wLab : (encFun lab).wt ≤ 3 * M ^ 2 + 4 := by
    have h1 := wt_encFun_le lab (B := k + L.q) fun x =>
      ((orbitLabels_spec (ps.map encPair)).2 x).1.le
    have : (k + L.q) * (2 * (k + L.q) + 5) ≤ M * (3 * M) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have wLi : ∀ v : S.dom, (Val.list [encFun lab, .nat (domPos e L.q v : ℕ)]).wt ≤ 10 * M ^ 2 := by
    intro v
    have h1 := wt_list2_le (encFun lab) (.nat (domPos e L.q v : ℕ))
    have h2 := wt_nat_le (domPos e L.q v : ℕ)
    have h3 := hdp v
    omega
  have hRC : rangeCost (k + L.q) ≤ 8000 * M ^ 3 := by
    unfold rangeCost
    have h1 := wt_natList_le_sq (xs := List.range (k + L.q)) (B := k + L.q)
      (fun x hx => (List.mem_range.1 hx).le) (by simp)
    have h2 := wt_nat_le (k + L.q)
    have h3 : (k + L.q + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : loopModK * (k + L.q + 1) * ((Val.nat (k + L.q)).wt + (k + L.q) +
        (natList (List.range (k + L.q))).wt + 1) ≤ loopModK * M * (8 * M ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h5 : loopModK * M * (8 * M ^ 2) = 8000 * M ^ 3 := by simp only [loopModK]; ring
    omega
  set KV : ℕ := cardCost h (2 * M) + 10 ^ 9 * M ^ 6 with hKV
  have fV : FunDet P (b + 77) (.list [.list [inp, encFun lab], outV])
      (.list ((os.filter tV).map posV))
      (os.length * KV + loopModK * (os.length + 1) * ((Val.list [.list [inp, encFun lab],
        outV]).wt + os.length + (Val.list ((os.filter tV).map posV)).wt + 1)) := by
    rw [hout]
    refine (filter_spec hFV (q := qOf e L.q tV) (B := fun _ => KV) fun x hx => ?_).mono ?_
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
      set Xv := (List.finRange (k + L.q)).filter (fun j => lab j = lab (domPos e L.q v))
        with hXv
      have hS := sameX_spec hFS hSame lab (domPos e L.q v) (Wc := 10 * M ^ 2) (wLi v) (by omega)
      have hIv := hcard (Endpoint.orb A v) Xv (fun j => by
          rw [hXv, List.mem_filter, decide_eq_true_iff, eq_comm,
            (orbitLabels_spec (ps.map encPair)).1]
          exact ⟨fun h => (mem_genOrbit_pairs (fun x hx => Pgrp_le (G := S.domGroup) (hA hx))
            hps v j).1 h.2, fun h => ⟨List.mem_finRange j,
            (mem_genOrbit_pairs (fun x hx => Pgrp_le (G := S.domGroup) (hA hx)) hps v j).2 h⟩⟩)
        ((List.length_filter_le _ _).trans (by simp))
      refine FunAll.mono (visTest_spec hVis hR k L.q psV x0V (.nat B) (.nat a) outV (encFun lab)
          (encPts Xv) _ _ _ _ hS hIv)
        fun w c ⟨hw, hc⟩ => ⟨by rw [hw, hposV, qOf_pos], ?_⟩
      have h1 : (10 * M ^ 2 + 1) ^ 3 ≤ 1331 * M ^ 6 := by
        have : 10 * M ^ 2 + 1 ≤ 11 * M ^ 2 := by omega
        calc (10 * M ^ 2 + 1) ^ 3 ≤ (11 * M ^ 2) ^ 3 := Nat.pow_le_pow_left this 3
          _ = 1331 * M ^ 6 := by ring
      have h2 := wt_list2_le (.list [inp, encFun lab]) (.nat (domPos e L.q v : ℕ))
      have h3 := wt_list2_le inp (encFun lab)
      have h4 := wt_nat_le (domPos e L.q v : ℕ)
      have h5 := hdp v
      have h6 := hle (Endpoint.orb A v)
      have h7 : (encPts Xv).wt ≤ 5 * (M + 1) ^ 2 :=
        wt_encPts_le_sq (by omega) ((List.length_filter_le _ _).trans (by simp; omega))
      have h8 : (Val.list [.list [.list [.list [.nat k, .nat L.q], psV, x0V, .nat B, .nat a, outV],
        encFun lab], .nat (domPos e L.q v : ℕ)]).wt =
          (Val.list [.list [inp, encFun lab], .nat (domPos e L.q v : ℕ)]).wt := rfl
      have m3 := pw 3 6 (by omega)
      have m2 := pw 2 6 (by omega)
      show c ≤ KV
      omega
    · rintro w c ⟨rfl, hc⟩
      refine ⟨by rw [hposV, filter_qOf], ?_⟩
      rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
      rw [hposV, filter_qOf] at hc
      exact hc
  -- the orbit labels
  have hOrb : FunDet P (b + 100) (.list [.nat (k + L.q), .list (ps.map fun p => encPerm (encPair p))])
      (encFun lab) (orbitK * (((ps.map encPair).length + 1) * (k + L.q + 1)) ^ 5) := by
    have := orbitFuns_spec hO (ps.map encPair)
    rwa [encPerms, List.map_map] at this
  -- the cost facts shared by the cases
  set C := cardCost h (2 * M) with hC
  have hlen : os.length ≤ M := by omega
  have eKA : os.length * KA = os.length * C + os.length * (200 * Wi + 300 * M + a + 2000) := by
    rw [hKA]; ring
  have bKA : os.length * (200 * Wi + 300 * M + a + 2000) ≤ 10 ^ 6 * M ^ 4 := by
    have : os.length * (200 * Wi + 300 * M + a + 2000) ≤ M * (10 ^ 5 * M ^ 3) :=
      Nat.mul_le_mul hlen (by have := pw 1 3 (by omega); simp at this; omega)
    have e : M * (10 ^ 5 * M ^ 3) = 10 ^ 5 * M ^ 4 := by ring
    omega
  have eKV : os.length * KV = os.length * C + os.length * (10 ^ 9 * M ^ 6) := by
    rw [hKV]; ring
  have bKV : os.length * (10 ^ 9 * M ^ 6) ≤ 10 ^ 9 * M ^ 7 := by
    have : os.length * (10 ^ 9 * M ^ 6) ≤ M * (10 ^ 9 * M ^ 6) := Nat.mul_le_mul_right _ hlen
    have e : M * (10 ^ 9 * M ^ 6) = 10 ^ 9 * M ^ 7 := by ring
    omega
  have eT : (2 * os.length + 2) * C = 2 * (os.length * C) + 2 * C := by ring
  have hsum := sum_wt_lt_wt_list [kqV, psV, x0V, .nat B, .nat a, outV]
  simp only [List.map, List.sum_cons, List.sum_nil] at hsum
  have eWi : Wi = (Val.list [kqV, psV, x0V, .nat B, .nat a, outV]).wt := rfl
  -- assembling the cases
  have ePos : ∀ l : List S.dom, encPts (l.map (domPos e L.q)) = .list (l.map posV) :=
    fun l => encPts_map_posOf e L.q l
  rw [ePos]
  unfold incList
  have t0 := fun z (hz : GI.Machine.BinOp.eval .eq (cardFix φ A ∅) a = z) =>
    Det.arith' (op := .eq) d0 (ar [] 4 (.nat a) rfl) hz
  by_cases h1 : cardFix φ A ∅ = a
  swap
  · -- rule 1 stops
    rw [if_pos h1]
    have t1 := t0 0 (by simp [GI.Machine.BinOp.eval, h1])
    refine FunDet.intro hentry ((Det.ite_zero t1 Det.nil).mono ?_)
    have w5 := wt_list_le [kqV, psV, .list [], x0V, .nat B]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w5
    have w0 : (Val.list []).wt = 4 := wt_list_nil
    have wc := wt_nat_le (cardFix φ A ∅)
    have hc0 := hle ∅
    have m3 := pw 3 12 (by omega)
    simp only [incK]
    omega
  rw [if_neg (not_not.2 h1)]
  have t1 := t0 1 (by simp [GI.Machine.BinOp.eval, h1])
  set affV : Val := .list ((os.filter tA).map posV) with haffV
  have wAff : affV.wt ≤ 5 * (M + 1) ^ 2 := by
    rw [haffV, ← ePos]
    exact wt_encPts_le_sq (by omega) (by simp; exact (List.length_filter_le _ _).trans hlen)
  have bLA : loopModK * (os.length + 1) * ((Val.list [inp, outV]).wt + os.length + affV.wt + 1) ≤
      2 * 10 ^ 6 * M ^ 4 := by
    have h1 := wt_list2_le inp outV
    have h2 : loopModK * (os.length + 1) * ((Val.list [inp, outV]).wt + os.length + affV.wt + 1) ≤
        loopModK * M * (2000 * M ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h3 : loopModK * M * (2000 * M ^ 3) = 2 * 10 ^ 6 * M ^ 4 := by
      simp only [loopModK]; ring
    omega
  have m4 := pw 4 12 (by omega)
  have m3 := pw 3 12 (by omega)
  have eAff : (Val.list ((os.filter tA).map posV)).wt = affV.wt := rfl
  have eInp : inp.wt = Wi := rfl
  have dA := Det.call (Det.mk2 (Det.var' (P := P) (env := [inp]) (i := 0) rfl)
    (ar [] 5 outV rfl)) fA
  by_cases h2 : os.filter tA ≠ []
  · -- rule 2
    rw [if_pos h2]
    have hl : ((os.filter tA).map posV).length ≠ 0 := by
      rw [List.length_map]; exact fun h => h2 (List.eq_nil_of_length_eq_zero h)
    have body := Det.ite_pos (e := incEntry.rule3E b)
      (Det.length (Det.var' (P := P) (env := [inp, affV]) (i := 1) rfl)) hl
      (Det.var' (P := P) (env := [inp, affV]) (i := 1) rfl)
    refine FunDet.intro hentry ((Det.ite_pos t1 one_ne_zero (Det.letE dA body)).mono ?_)
    have w5 := wt_list_le [kqV, psV, .list [], x0V, .nat B]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w5
    have w0 : (Val.list []).wt = 4 := wt_list_nil
    have wc := wt_nat_le (cardFix φ A ∅)
    have hc0 := hle ∅
    have wl := wt_nat_le ((os.filter tA).map posV).length
    have hl' : ((os.filter tA).map posV).length ≤ M := by
      rw [List.length_map]; exact (List.length_filter_le _ _).trans hlen
    have w2 := wt_list2_le inp outV
    have w3 := wt_list2_le inp affV
    have w4 : (Val.list [inp, affV]).wt ≤ (Val.list [inp]).wt + 2 * affV.wt + 2 :=
      wt_list_snoc_le [inp] affV
    have w6 := wt_list_le [inp]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w6
    simp only [incK]
    omega
  rw [if_neg h2]
  have hl0 : ((os.filter tA).map posV).length = 0 := by
    rw [List.length_map]; simpa using h2
  have dl0 := hl0 ▸ Det.length (Det.var' (P := P) (env := [inp, affV]) (i := 1) rfl)
  have d3 := Det.call (Det.mk5 (ar [affV] 0 kqV rfl) (ar [affV] 1 psV rfl) (ar [affV] 5 outV rfl)
    (ar [affV] 2 x0V rfl) (ar [affV] 3 (.nat B) rfl))
    (hcard {v | v ∉ W} (os.map (domPos e L.q)) (fun j => by simp [domPos, hos]) (by simp))
  have t3 := fun z (hz : GI.Machine.BinOp.eval .eq (cardFix φ A {v | v ∉ W}) a = z) =>
    Det.arith' (op := .eq) d3 (ar [affV] 4 (.nat a) rfl) hz
  by_cases h3 : cardFix φ A {v | v ∉ W} = a
  · -- rule 3 stops
    rw [if_pos h3]
    have t3' := t3 1 (by simp [GI.Machine.BinOp.eval, h3])
    have body := Det.ite_zero (t := .var 1) dl0 (Det.ite_pos t3' one_ne_zero (Det.nil (P := P)) (e := incEntry.rule4E b))
    refine FunDet.intro hentry ((Det.ite_pos t1 one_ne_zero (Det.letE dA body)).mono ?_)
    have w5 := wt_list_le [kqV, psV, .list [], x0V, .nat B]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w5
    have w5' := wt_list_le [kqV, psV, outV, x0V, .nat B]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w5'
    have w0 : (Val.list []).wt = 4 := wt_list_nil
    have wc := wt_nat_le (cardFix φ A ∅)
    have hc0 := hle ∅
    have wc3 := wt_nat_le (cardFix φ A {v | v ∉ W})
    have hc3 := hle {v | v ∉ W}
    have w2 := wt_list2_le inp outV
    have w4 : (Val.list [inp, affV]).wt ≤ (Val.list [inp]).wt + 2 * affV.wt + 2 :=
      wt_list_snoc_le [inp] affV
    have w6 := wt_list_le [inp]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w6
    simp only [incK]
    omega
  · -- rule 4
    rw [if_neg h3]
    have t3' := t3 0 (by simp [GI.Machine.BinOp.eval, h3])
    have gk := Det.get' (ar [affV] 0 kqV rfl) (Det.nat 0) (v := .nat k) rfl
    have gq := Det.get' (ar [affV] 0 kqV rfl) (Det.nat 1) (v := .nat L.q) rfl
    have dPE := Det.call (Det.mk2 gk (ar [affV] 1 psV rfl)) (pEncMap_spec hPE ps)
    have dOrb := Det.call (Det.mk2 (Det.arith' (op := .add) gk gq rfl) dPE) hOrb
    have dV := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := P) (env := [inp, affV, encFun lab])
      (i := 0) rfl) (Det.var' (P := P) (env := [inp, affV, encFun lab]) (i := 2) rfl))
      (ar [affV, encFun lab] 5 outV rfl)) fV
    have w5 := wt_list_le [kqV, psV, .list [], x0V, .nat B]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w5
    have w5' := wt_list_le [kqV, psV, outV, x0V, .nat B]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w5'
    have w0 : (Val.list []).wt = 4 := wt_list_nil
    have wc := wt_nat_le (cardFix φ A ∅)
    have hc0 := hle ∅
    have wc3 := wt_nat_le (cardFix φ A {v | v ∉ W})
    have hc3 := hle {v | v ∉ W}
    have w2 := wt_list2_le inp outV
    have w4 : (Val.list [inp, affV]).wt ≤ (Val.list [inp]).wt + 2 * affV.wt + 2 :=
      wt_list_snoc_le [inp] affV
    have w6 := wt_list_le [inp]
    simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at w6
    -- rule 4 pieces
    have ePs : psV.wt = (Val.list (ps.map pairV)).wt := rfl
    have eKq : kqV.wt = (Val.list [.nat k, .nat L.q]).wt := rfl
    have hkW : (Val.nat k).wt < kqV.wt := wt_le_wt_list (by simp)
    have hqW : (Val.nat L.q).wt < kqV.wt := wt_le_wt_list (by simp)
    have wV : (Val.list ((os.filter tV).map posV)).wt ≤ 5 * (M + 1) ^ 2 := by
      rw [← ePos]
      exact wt_encPts_le_sq (by omega) (by simp; exact (List.length_filter_le _ _).trans hlen)
    have wIL := wt_list2_le inp (encFun lab)
    have wILo := wt_list2_le (.list [inp, encFun lab]) outV
    have w7 : (Val.list [inp, affV, encFun lab]).wt ≤ (Val.list [inp, affV]).wt +
        2 * (encFun lab).wt + 2 := wt_list_snoc_le [inp, affV] (encFun lab)
    have bLV : loopModK * (os.length + 1) * ((Val.list [.list [inp, encFun lab], outV]).wt +
        os.length + (Val.list ((os.filter tV).map posV)).wt + 1) ≤ 4 * 10 ^ 6 * M ^ 4 := by
      have h2 : loopModK * (os.length + 1) * ((Val.list [.list [inp, encFun lab], outV]).wt +
          os.length + (Val.list ((os.filter tV).map posV)).wt + 1) ≤
          loopModK * M * (4000 * M ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have h3 : loopModK * M * (4000 * M ^ 3) = 4 * 10 ^ 6 * M ^ 4 := by
        simp only [loopModK]; ring
      omega
    have bE : (Val.list (ps.map fun p => encPerm (encPair p))).wt ≤ 9 * M ^ 3 + 4 := by
      have h1 := wt_list_map_le ps (fun p => encPerm (encPair p))
        (W := 4 * (k + L.q + 1) ^ 2) fun p _ => wt_encPerm_le _
      have h2 : ps.length * (2 * (4 * (k + L.q + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
        Nat.mul_le_mul (by omega) (by
          have := Nat.pow_le_pow_left (show k + L.q + 1 ≤ M by omega) 2
          have := Nat.one_le_pow 2 M (by omega); omega)
      have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
      omega
    have wkP := wt_list2_le (.nat k) (.list (ps.map pairV))
    have eKP : (Val.list [.nat k, psV]).wt = (Val.list [.nat k, .list (ps.map pairV)]).wt := rfl
    have cE : ps.length * pEncCost k L.q ≤ natStepK * M ^ 4 := by
      have h2 : ps.length * pEncCost k L.q ≤ M * (natStepK * M ^ 3) :=
        Nat.mul_le_mul (by omega) (by
          show natStepK * (k + L.q + 1) ^ 3 ≤ _
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
      have e2 : M * (natStepK * M ^ 3) = natStepK * M ^ 4 := by ring
      omega
    have cE2 : mapK * (ps.length + 1) * ((Val.list [.nat k, .list (ps.map pairV)]).wt +
        (Val.list (ps.map fun p => encPerm (encPair p))).wt + 1) ≤ mapK * M * (1000 * M ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e3 : mapK * M * (1000 * M ^ 3) = 10 ^ 6 * M ^ 4 := by simp only [mapK]; ring
    have cO : orbitK * (((ps.map encPair).length + 1) * (k + L.q + 1)) ^ 5 ≤ 10 ^ 6 * M ^ 10 := by
      rw [List.length_map]
      have h1 : ((ps.length + 1) * (k + L.q + 1)) ^ 5 ≤ (M * M) ^ 5 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 5
      have h2 : (M * M) ^ 5 = M ^ 10 := by ring
      simp only [orbitK]; omega
    have wpE : (Val.list [.nat (k + L.q), .list (ps.map fun p => encPerm (encPair p))]).wt ≤
        2 * ((Val.nat (k + L.q)).wt + (Val.list (ps.map fun p => encPerm (encPair p))).wt) + 6 :=
      wt_list2_le _ _
    have wkq := wt_nat_le (k + L.q)
    have m10 := pw 10 12 (by omega)
    have m7 := pw 7 12 (by omega)
    have m2 := pw 2 12 (by omega)
    have eadd : GI.Machine.BinOp.eval .add k L.q = k + L.q := rfl
    have hkwi : (Val.nat k).wt < Wi := by omega
    have dPE' := dPE.mono (c' := 40 * Wi + 3 * 10 ^ 9 * M ^ 4 + 200) (by
      have m34 := pw 3 4 (by omega)
      clear_value KA KV C Wi affV inp outV x0V psV kqV posV lab M a tA tV φ
      simp only [natStepK] at cE; omega)
    have dOrb' := (Det.call (Det.mk2 (Det.arith' (op := .add) (z := k + L.q) gk gq rfl) dPE')
      hOrb).mono (c' := 10 ^ 10 * M ^ 10) (by
        have m410 := pw 4 10 (by omega)
        have m310 := pw 3 10 (by omega)
        have m210 := pw 2 10 (by omega)
        have hqwi : (Val.nat L.q).wt < Wi := by omega
        have hkqM : k + L.q ≤ M ^ 10 := by
          have := pw 1 10 (by omega); rw [pow_one] at this; omega
        clear * - m410 m310 m210 hqwi hkwi hkqM hWb wkq wpE bE cO wLab
        omega)
    have dV' := dV.mono (c' := os.length * C + 2 * 10 ^ 9 * M ^ 7) (by
      rw [eKV]
      have m47 := pw 4 7 (by omega)
      have m37 := pw 3 7 (by omega)
      have m27 := pw 2 7 (by omega)
      have m17 : M ≤ M ^ 7 := by have := pw 1 7 (by omega); rwa [pow_one] at this
      clear * - m47 m37 m27 m17 bKV bLV wIL wILo wV wOut wLab hWb e1 eInp hM20
      omega)
    have body := Det.ite_zero (t := .var 1) dl0 (Det.ite_zero (t := .nil) t3' (Det.letE dOrb' dV'))
    refine FunDet.intro hentry ((Det.ite_pos t1 one_ne_zero (Det.letE dA body)).mono ?_)
    rw [eKA, eT]
    have m1012 := pw 10 12 (by omega)
    have m712 := pw 7 12 (by omega)
    have m112 : M ≤ M ^ 12 := by have := pw 1 12 (by omega); rwa [pow_one] at this
    have haB : a ≤ M := by omega
    clear * - m1012 m712 m112 m4 m3 m2 haB hM20 bKA bLA w5 w5' w0 wc hc0 wc3 hc3 w2 w4 w6 wAff eAff
      eInp hWb hsum eWi wV w7 wLab wOut e1 hlen
    simp only [incK]
    omega
