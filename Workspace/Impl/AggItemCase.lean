module

public import Workspace.Impl.AggItemCol
public import Workspace.Impl.AggCaseProg

@[expose] public section

/-!
# The case of the round, from the items' start state

The item of every branch depends on the case of the ideal certificate group `π(F_x)` of the
source string (Section A.3: Case 1, 2a, 2b, 3; `plan`). The items' start state holds graph pairs
`fx` of the lift of `F_x` (`ItHand`). Their second parts generate `π(F_x)`:
* `it_snd_gens` (mathematics): for graph pairs of the lift `S.liftGroup F` of any `F`, the second
  parts generate `π_d(F ∩ G|_dom)`, when `π_d` agrees with `π` on `G` (`πd_spec`). The lift is the
  full preimage of `F` in `G`, and `G → G|_dom` is onto, so the label images agree;
* `it_grp_spec` (program `itGrpF`): on `[q, ⟨fx⟩]` it returns `encGroup (fx.map Prod.snd)`, by a
  `map` that takes the second entry of each pair and an `append` that puts the identity first;
* `it_case_spec` (program `itCaseF`): on the start state it returns the code of
  `aggCase π(F_x)` (`acp_case_spec`, one **PointwiseStab** call and two **GroupOrder** calls).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens PointwiseStab GroupOrder)

variable {Ω C : Type} {k : ℕ}

/-! ### The second parts generate the ideal certificate group -/

/-- **The second parts of graph pairs of a lift generate the ideal image.** -/
theorem it_snd_gens (e : Ω ≃ Fin k) {S : State Ω C} (L : GiantLabels S)
    (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (F : Subgroup (Perm S.dom))
    {fz : List (Perm (Fin k) × Perm (Fin L.q))} (h : PairGens e L (S.liftGroup F) fz) :
    gens (fz.map Prod.snd) =
      ((F.subgroupOf S.domGroup).map πd).map (alternatingGroup (Fin L.q)).subtype := by
  rw [gens_snd, h]
  unfold graphOf State.liftGroup
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _),
    Subgroup.map_map]
  have e1 : (MonoidHom.snd _ _).comp (gpair e L) = (alternatingGroup (Fin L.q)).subtype.comp L.π := by
    ext g : 1; rfl
  have e2 : L.π = πd.comp S.domHom.rangeRestrict := by
    ext g : 1; exact (hπ g).symm
  have e3 : F.comap S.domHom = (F.subgroupOf S.domGroup).comap S.domHom.rangeRestrict := by
    ext g; simp [Subgroup.mem_subgroupOf, State.domGroup]
  rw [e1, ← Subgroup.map_map]
  congr 1
  rw [e2, e3]
  refine (Subgroup.map_map _ _ _).symm.trans (congrArg (Subgroup.map πd) ?_)
  exact Subgroup.map_comap_eq_self_of_surjective S.domHom.rangeRestrict_surjective _

/-- **For a round**: the second parts of graph pairs of the lift of `F_x` generate the group of
the source structure, `(Ag.strX t).grp = π(F_x)`, for every individualized tuple `t`. -/
theorem it_gens_strX (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (Ag : Aggregation P₀ S L) {fx : List (Perm (Fin k) × Perm (Fin L.q))}
    (h : PairGens e L (itCertLift Ag.fin S Ag.πd P₀.κ S.x) fx) (t : Fin Ag.ℓ → Fin L.q) :
    gens (fx.map Prod.snd) = (Ag.strX t).grp :=
  it_snd_gens e L Ag.πd Ag.πd_spec _ h

/-! ### The group of the second parts, as a program -/

/-- On `[c, pairV p]`: `encPerm p.2`. -/
def itSndF : Expr := .get (arg 1) (.nat 1)

/-- On `[q, ⟨fx⟩]`: `encGroup (fx.map Prod.snd) = [q, [1, p₁.2, …]]`. The identity `1` of
`Sym(q)` is `range q`. -/
def itGrpF (rb mp app : ℕ) : Expr :=
  mk2 (arg 0) (.call app (mk2 (mk1 (.call rb (arg 0))) (.call mp (mk2 (arg 0) (arg 1)))))

theorem it_snd_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itSndF) {q : ℕ} (c : Val)
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P f (.list [c, pairV p]) (encPerm p.2) (10 * ((Val.list [c, pairV p]).wt + 1)) := by
  have hp : (pairV p).wt < (Val.list [c, pairV p]).wt := wt_le_wt_list (by simp)
  have h2 : (encPerm p.2).wt < (pairV p).wt := wt_le_wt_list (by simp)
  refine FunDet.intro hf ((Det.get' (Det.arg' (P := P) (rest := []) (vs := [c, pairV p]) (j := 1)
    rfl) (Det.nat 1) (v := encPerm p.2) rfl).mono ?_)
  have := wt_nat_le 1
  omega

/-- The weight of the group value of the second parts, for a state weight bound `W ≥ q`. -/
theorem it_grp_wt {q : ℕ} (fx : List (Perm (Fin k) × Perm (Fin q))) {W : ℕ}
    (hW : (Val.list (fx.map pairV)).wt ≤ W) (hq : q ≤ W) :
    (encGroup (fx.map Prod.snd)).wt ≤ 100 * (W + 1) ^ 3 := by
  have h1 : ∀ v ∈ (fx.map Prod.snd).map encPerm, v.wt ≤ W := by
    intro v hv
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    have h2 : (encPerm p.2).wt < (pairV p).wt := wt_le_wt_list (by simp)
    have h3 : (pairV p).wt < (Val.list (fx.map pairV)).wt :=
      wt_le_wt_list (List.mem_map_of_mem hp)
    omega
  have h1' : (encPerm (1 : Perm (Fin q))).wt ≤ 5 * (W + 1) ^ 2 := by
    rw [encPerm_one_eq]
    exact wt_natList_le_sq (fun x hx => by
      simp only [List.mem_map] at hx; obtain ⟨i, -, rfl⟩ := hx; have := i.2; omega) (by simp; omega)
  have hl : fx.length < (Val.list (fx.map pairV)).wt := by
    have := length_lt_wt_list (fx.map pairV); simpa using this
  have h4 := wt_list_le_of ((1 :: fx.map Prod.snd).map encPerm) (c := 5 * (W + 1) ^ 2) (by
    intro v hv
    simp only [List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h1'
    · have := h1 v hv; nlinarith)
  have h5 : ((1 :: fx.map Prod.snd).map encPerm).length = fx.length + 1 := by simp
  rw [h5] at h4
  have h6 := wt_list2_le (.nat q) (.list ((1 :: fx.map Prod.snd).map encPerm))
  have h7 := wt_nat_le q
  have h8 : (fx.length + 1) * (2 * (5 * (W + 1) ^ 2) + 1) ≤ (W + 1) * (11 * (W + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by nlinarith)
  have h9 : (W + 1) * (11 * (W + 1) ^ 2) = 11 * (W + 1) ^ 3 := by ring
  have h10 : W + 1 ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold encGroup encPerms
  omega

/-- The value of `itSndF` on a pair value. -/
def itSndVal : Val → Val
  | .list [_, b] => b
  | _ => .nat 0

/-- The cost bound of `itGrpF`, for a weight bound `W` of the pairs and of `q`. -/
def itGrpC (W : ℕ) : ℕ := 10 ^ 8 * (W + 1) ^ 5

/-- **The group of the second parts.** On `[q, ⟨fx⟩]` the entry `itGrpF` returns
`encGroup (fx.map Prod.snd)`. -/
theorem it_grp_spec {P : Program} {f rb mp sf app : ℕ} (hf : P.funs[f]? = some (itGrpF rb mp app))
    (hrb : P.HasAt rb (rangeFuns rb)) (hmp : P.HasAt mp (mapFuns mp sf))
    (hsf : P.funs[sf]? = some itSndF) (happ : P.HasAt app (appendFuns app)) {q : ℕ}
    (fx : List (Perm (Fin k) × Perm (Fin q))) {W : ℕ} (hW : (Val.list (fx.map pairV)).wt ≤ W)
    (hq : q ≤ W) :
    FunDet P f (.list [.nat q, .list (fx.map pairV)]) (encGroup (fx.map Prod.snd)) (itGrpC W) := by
  set xs := fx.map pairV with hxs
  set ys := (fx.map Prod.snd).map encPerm with hys
  have hW1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW2 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW3 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW4 : (W + 1) ^ 4 ≤ (W + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have wq := wt_nat_le q
  have hin := wt_list2_le (.nat q) (.list xs)
  have hl : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have hlx : xs.length = fx.length := by simp [hxs]
  -- the map
  have hmap := map_det hmp (c := .nat q) (xs := xs) (F := itSndVal)
    (B := 10 * (2 * (q + 2 + W) + 7)) fun x hx => by
      have hp : x.wt ≤ W := (wt_le_wt_list hx).le.trans hW
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      refine (it_snd_spec hsf (.nat q) p).mono ?_
      have := wt_list2_le (.nat q) (pairV p)
      omega
  have hys' : xs.map itSndVal = ys := by
    rw [hxs, hys, List.map_map, List.map_map]; rfl
  rw [hys'] at hmap
  have hyl : ys.length = fx.length := by simp [hys]
  have hyw : ∀ v ∈ ys, v.wt ≤ W := by
    intro v hv
    simp only [hys, List.map_map, List.mem_map, Function.comp_apply] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    have h2 : (encPerm p.2).wt < (pairV p).wt := wt_le_wt_list (by simp)
    have h3 : (pairV p).wt < (Val.list xs).wt :=
      wt_le_wt_list (by rw [hxs]; exact List.mem_map_of_mem hp)
    omega
  have hysw := wt_list_le_of ys hyw
  rw [hyl] at hysw
  -- the identity
  have hone : natList (List.range q) = encPerm (1 : Perm (Fin q)) := by
    rw [encPerm_one_eq, List.map_coe_finRange_eq_range]
  have hrng := st_range_det hrb q
  rw [hone] at hrng
  have h1w : (encPerm (1 : Perm (Fin q))).wt ≤ 5 * (W + 1) ^ 2 := by
    rw [← hone]
    exact wt_natList_le_sq (fun x hx => by have := List.mem_range.1 hx; omega) (by simp; omega)
  -- the append
  have happ' : FunDet P app (.list [.list [encPerm (1 : Perm (Fin q))], .list ys])
      (.list (encPerm (1 : Perm (Fin q)) :: ys))
      (loopModK * (ys.length + 1) * ((Val.list [.list [encPerm (1 : Perm (Fin q))], .list ys]).wt +
        ys.length + (Val.list (encPerm (1 : Perm (Fin q)) :: ys)).wt + 1)) :=
    (append_spec happ [encPerm 1] ys).mono fun w c ⟨h1, h2⟩ => by
      subst h1; exact ⟨rfl, h2⟩
  set env : List Val := [.list [.nat q, .list xs]]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [.nat q, .list xs]) (j := 0) (v := .nat q) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.nat q, .list xs]) (j := 1) (v := .list xs) rfl
  have d := Det.mk2 g0 (Det.call (Det.mk2 (Det.mk1 (Det.call g0 hrng)) (Det.call (Det.mk2 g0 g1) hmap))
    happ')
  refine FunDet.intro hf (d.mono ?_)
  -- the weights
  have hone1 : (Val.list [encPerm (1 : Perm (Fin q))]).wt ≤ 2 * (5 * (W + 1) ^ 2) + 5 := by
    have := wt_list_le [encPerm (1 : Perm (Fin q))]; simp at this; omega
  have hall := wt_list_le_of (encPerm (1 : Perm (Fin q)) :: ys) (c := 5 * (W + 1) ^ 2) (by
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h1w
    · have := hyw v hv; omega)
  simp only [List.length_cons, hyl] at hall
  have hpq := wt_list2_le (.nat q) (.list (encPerm (1 : Perm (Fin q)) :: ys))
  have hap := wt_list2_le (.list [encPerm (1 : Perm (Fin q))]) (.list ys)
  have hm1 := wt_list2_le (.nat q) (.list xs)
  have hfx : fx.length ≤ W := by omega
  have b1 : (fx.length + 1) * (2 * (5 * (W + 1) ^ 2) + 1) ≤ 11 * (W + 1) ^ 3 := by
    have := Nat.mul_le_mul (show fx.length + 1 ≤ W + 1 by omega)
      (show 2 * (5 * (W + 1) ^ 2) + 1 ≤ 11 * (W + 1) ^ 2 by omega)
    have e : (W + 1) * (11 * (W + 1) ^ 2) = 11 * (W + 1) ^ 3 := by ring
    omega
  have b2 : fx.length * (2 * W + 1) ≤ 3 * (W + 1) ^ 2 := by
    have := Nat.mul_le_mul (show fx.length ≤ W + 1 by omega) (show 2 * W + 1 ≤ 3 * (W + 1) by omega)
    have e : (W + 1) * (3 * (W + 1)) = 3 * (W + 1) ^ 2 := by ring
    omega
  have b3 : fx.length * (10 * (2 * (q + 2 + W) + 7)) ≤ 110 * (W + 1) ^ 2 := by
    have := Nat.mul_le_mul (show fx.length ≤ W + 1 by omega)
      (show 10 * (2 * (q + 2 + W) + 7) ≤ 110 * (W + 1) by omega)
    have e : (W + 1) * (110 * (W + 1)) = 110 * (W + 1) ^ 2 := by ring
    omega
  have b4 : mapK * (fx.length + 1) * ((Val.list [.nat q, .list xs]).wt + (Val.list ys).wt + 1) ≤
      mapK * (W + 1) * (20 * (W + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have b5 : loopModK * (fx.length + 1) *
      ((Val.list [.list [encPerm (1 : Perm (Fin q))], .list ys]).wt + fx.length +
        (Val.list (encPerm (1 : Perm (Fin q)) :: ys)).wt + 1) ≤
      loopModK * (W + 1) * (100 * (W + 1) ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e4 : mapK * (W + 1) * (20 * (W + 1) ^ 2) = 20 * mapK * (W + 1) ^ 3 := by ring
  have e5 : loopModK * (W + 1) * (100 * (W + 1) ^ 3) = 100 * loopModK * (W + 1) ^ 4 := by ring
  have hr : 10000 * (q + 1) ^ 3 ≤ 10000 * (W + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  simp only [hlx, hyl] at *
  have hg : (encGroup (fx.map Prod.snd)).wt =
      (Val.list [.nat q, .list (encPerm (1 : Perm (Fin q)) :: ys)]).wt := rfl
  unfold itGrpC
  unfold mapK loopModK at *
  omega

/-! ### The case code -/

/-- **The case program meets its contract** at `acp` (the conclusion of `acp_case_spec`, for every
degree): on `encGroup gs` it returns the code of `aggCase (gens gs)`. -/
def ItCaseOK (P : Program) (acp : ℕ) (hst : PointwiseStab) (hO : GroupOrder) : Prop :=
  ∀ (n : ℕ) (gs : List (Perm (Fin n))), FunDet P acp (encGroup gs)
    (.nat (AggCase.code (aggCase (gens gs))))
    (acpCC (pointwiseStabPrim hst) (groupOrderPrim hO) (encGroup gs).wt)

/-- `acp_case_spec` meets `ItCaseOK`. -/
theorem itCaseOK_of (hst : PointwiseStab) (hO : GroupOrder) {P : Program}
    {b orb rng fd pd fs ps cnt g pst fac jp jo : ℕ}
    (hb : P.funs[b]? = some (acpCaseF orb rng fd fs g)) (horb : P.HasAt orb (orbitFuns orb))
    (hrng : P.HasAt rng (rangeFuns rng)) (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hfs : P.HasAt fs (filterFuns fs ps))
    (hps : P.funs[ps]? = some (acpSuppF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hg : P.funs[g]? = some (acpGiantF pst fac jo)) (hpst : P.HasAt pst (pstabFuns pst jp))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst)) (hfac : P.HasAt fac (factFuns fac))
    (hjo : P.prims[jo]? = some (groupOrderPrim hO)) : ItCaseOK P b hst hO :=
  fun _ gs => acp_case_spec hst hO hb horb hrng hfd hpd hfs hps hcnt hg hpst hjp hfac hjo gs

theorem acpCC_mono' (p o : Prim) {a b : ℕ} (h : a ≤ b) : acpCC p o a ≤ acpCC p o b := by
  unfold acpCC
  have h1 : 40 * (a + 1) ^ 2 ≤ 40 * (b + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h2 := acpGC_mono p o h1
  have h3 : 10 ^ 15 * (a + 1) ^ 6 ≤ 10 ^ 15 * (b + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
  omega

/-- On the items' start state: the case code of the group of the second parts of `fx`. -/
def itCaseF (acp grp : ℕ) : Expr :=
  .call acp (.call grp (mk2 (.get (.get (.var 0) (.nat 1)) (.nat 1)) (.get (.var 0) (.nat 3))))

/-- The cost bound of `itCaseF`, for a weight bound `W` of the state. -/
noncomputable def itCaseC (hst : PointwiseStab) (hO : GroupOrder) (W : ℕ) : ℕ :=
  acpCC (pointwiseStabPrim hst) (groupOrderPrim hO) (100 * (W + 1) ^ 3) + itGrpC W +
    1000 * (W + 1) ^ 3

/-- **The case of the round.** On the items' start state, `itCaseF` returns the code of
`aggCase` of the group generated by the second parts of `fx`. -/
theorem it_case_spec (hst : PointwiseStab) (hO : GroupOrder) {P : Program}
    {f acp grp rb mp sf app : ℕ} (hf : P.funs[f]? = some (itCaseF acp grp))
    (hacp : ItCaseOK P acp hst hO) (hgrp : P.funs[grp]? = some (itGrpF rb mp app))
    (hrb : P.HasAt rb (rangeFuns rb)) (hmp : P.HasAt mp (mapFuns mp sf))
    (hsf : P.funs[sf]? = some itSndF) (happ : P.HasAt app (appendFuns app))
    (sv : Val) {q : ℕ} (ps fx fy : List (Perm (Fin k) × Perm (Fin q)))
    (tt : List (TestTuple q P₀.κ)) (cr : TestTuple q P₀.κ → TestTuple q P₀.κ → Bool) {W : ℕ}
    (hW : (itSt sv k q ps fx fy tt cr).wt ≤ W) (hqW : q ≤ W) :
    FunDet P f (itSt sv k q ps fx fy tt cr)
      (.nat (AggCase.code (aggCase (gens (fx.map Prod.snd))))) (itCaseC hst hO W) := by
  have hstl : itSt sv k q ps fx fy tt cr = .list [sv, .list [.nat k, .nat q],
      .list (ps.map pairV), .list (fx.map pairV), .list (fy.map pairV), stCv tt cr] := rfl
  have hkq : (Val.list [.nat k, .nat q]).wt < (itSt sv k q ps fx fy tt cr).wt := by
    rw [hstl]; exact wt_le_wt_list (by simp)
  have hfxw : (Val.list (fx.map pairV)).wt < (itSt sv k q ps fx fy tt cr).wt := by
    rw [hstl]; exact wt_le_wt_list (by simp)
  have hqw : (Val.nat q).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have hgr := it_grp_spec hgrp hrb hmp hsf happ fx (W := W) (by omega) (by omega)
  have hgw := it_grp_wt fx (W := W) (by omega) (by omega)
  have hac := (hacp q (fx.map Prod.snd)).mono (acpCC_mono' _ _ hgw)
  have d := Det.call (Det.call (Det.mk2 (Det.get' (Det.get' (Det.var' (P := P)
    (env := [itSt sv k q ps fx fy tt cr]) (i := 0) rfl) (Det.nat 1) rfl)
    (Det.nat 1) (v := .nat q) rfl) (Det.get' (Det.var' (i := 0) rfl) (Det.nat 3)
    (v := .list (fx.map pairV)) rfl)) hgr) hac
  refine FunDet.intro hf (d.mono ?_)
  have h1 := wt_list2_le (.nat q) (.list (fx.map pairV))
  have h2 : (Val.nat (AggCase.code (aggCase (gens (fx.map Prod.snd))))).wt ≤ 10 := by
    have := wt_nat_le (AggCase.code (aggCase (gens (fx.map Prod.snd))))
    have : AggCase.code (aggCase (gens (fx.map Prod.snd))) ≤ 3 := by
      cases aggCase (gens (fx.map Prod.snd)) <;> simp [AggCase.code]
    omega
  have hW1 : W + 1 ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have est : (Val.list [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
      .list (fy.map pairV), stCv tt cr]).wt = (itSt sv k q ps fx fy tt cr).wt := rfl
  unfold itCaseC
  omega

end GI.Impl
