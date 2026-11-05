module

public import Workspace.Impl.Lift

@[expose] public section

/-!
# The specification of the lift

`lift_spec`: on `[liftCtx e S.dom gs, u']`, where `gs` generates `G` (as permutations of
`Fin k`) and `u'` is a canonical answer value of a set `A'` of permutations of the domain inside
`G|_dom`, the lifting module returns a canonical answer value of `S.liftAnswer A'`, at cost at
most `liftCost`. It uses the cited tasks **Preimage** and **NormalizedFactor**.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encGroup gens sumToFin Preimage NormalizedFactor PreimageInst
  preimageSet)
open scoped Pointwise

variable {Ω : Type} {k : ℕ}

/-- The context of the lift: `[k, s, domCtx, encGroup gs]`. -/
noncomputable def liftCtx (e : Ω ≃ Fin k) (D : Set Ω) (gs : List (Perm (Fin k))) : Val :=
  .list [.nat k, .nat (domFin e D).length, domCtx e D, encGroup gs]

/-- The cost constant of the lift. -/
def liftK : ℕ := 10 ^ 20

/-- The cost of the lift: a polynomial in `k`, and one call of each cited primitive on an
input of weight at most `10⁶ (k + 1)⁶`. -/
def liftCost (pp pf : Prim) (k : ℕ) : ℕ :=
  liftK * (k + 1) ^ 21 + pp.c * (10 ^ 6 * (k + 1) ^ 6 + 2) ^ pp.k +
    pf.c * (10 ^ 6 * (k + 1) ^ 6 + 2) ^ pf.k

theorem wt_list4_le (a b c d : Val) :
    (Val.list [a, b, c, d]).wt ≤ 2 * (a.wt + b.wt + c.wt + d.wt) + 8 := by
  have := wt_list_le [a, b, c, d]; simp at this; omega

theorem wt_liftCtx_le (e : Ω ≃ Fin k) (D : Set Ω) {gs : List (Perm (Fin k))}
    (hgl : gs.length ≤ k ^ 2) : (liftCtx e D gs).wt ≤ 1000 * (k + 1) ^ 6 := by
  have h1 := wt_list4_le (.nat k) (.nat (domFin e D).length) (domCtx e D) (encGroup gs)
  have h2 := wt_nat_le k
  have h3 := wt_nat_le (domFin e D).length
  have h4 : (domFin e D).length ≤ k := length_domFin_le
  have h5 := wt_domCtx_le e D
  have h6 := wt_encGroup_le_sq hgl
  have p12 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [liftCtx]; omega

/-- A prim bound on an input of weight at most `W`. -/
theorem Prim.bound_le (p : Prim) {v : Val} {W : ℕ} (h : v.wt ≤ W) :
    p.bound v ≤ p.c * (W + 2) ^ p.k :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := v.size_le_wt; omega) _)

/-- **The lift.** -/
theorem lift_spec (hpre : Preimage) (hfac : NormalizedFactor) {P : Program} {b d jpre jfac : ℕ}
    (h : LiftAt P b d jpre jfac) (hd : DomAt P d)
    (hjp : P.prims[jpre]? = some (preimagePrim hpre))
    (hjf : P.prims[jfac]? = some (normalizedFactorPrim hfac))
    {C : Type} (e : Ω ≃ Fin k) (S : State Ω C) {gs : List (Perm (Fin k))}
    (hgs : gens gs = groupFin e S.G) (hgl : gs.length ≤ k ^ 2)
    {u' : Val} {A' : Set (Perm S.dom)} (hu : AnsC (domEquiv e S.dom) u' A')
    (hA' : A' ⊆ (restrictHom S.G S.dom S.dom_inv).range) :
    FunAll P b (.list [liftCtx e S.dom gs, u']) (fun w c => AnsC e w (S.liftAnswer A') ∧
      c ≤ liftCost (preimagePrim hpre) (normalizedFactorPrim hfac) k) := by
  refine FunAll.intro h.entry ?_
  unfold liftEntry
  set s := (domFin e S.dom).length with hsdef
  have hs : s ≤ k := length_domFin_le
  have wctx := wt_liftCtx_le e S.dom hgl
  set X := k + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have p12 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p36 : X ^ 3 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p69 : X ^ 6 ≤ X ^ 9 := Nat.pow_le_pow_right hX1 (by omega)
  have p921 : X ^ 9 ≤ X ^ 21 := Nat.pow_le_pow_right hX1 (by omega)
  rcases hu with ⟨rfl, rfl⟩ | ⟨x', gs', rfl, hgl', hA⟩
  · -- the empty answer lifts to the empty answer
    have hc := Det.length (P := P) (Det.arg' (vs := [liftCtx e S.dom gs, .list []]) (rest := [])
      (j := 1) rfl)
    refine (Det.ite (ct := 0) hc (fun h0 => absurd rfl h0) (fun _ => Det.nil)).post ?_
    intro c hc'
    refine ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · ext g; simp [State.liftAnswer]
    · have w1 := wt_list2_le (liftCtx e S.dom gs) (.list [])
      have w2 : (Val.list []).wt ≤ 5 := by decide
      simp only [List.length_nil] at hc'
      simp only [liftCost, liftK, ← hX]
      have : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX1
      omega
  · obtain ⟨hx', hms⟩ := lift_hyps e S hA' hA
    set I := liftInst e S.G S.dom S.dom_inv hgs gs' hms with hI
    set ctx := liftCtx e S.dom gs with hctx
    set u := Val.list [encPerm x', encGroup gs'] with hu
    set inp := Val.list [ctx, u] with hinp
    set L1 := Val.list ((1 :: gs).map fun g =>
      encPerm (sumToFin (Perm.sumCongr g (restrP e S.G S.dom S.dom_inv g)))) with hL1
    set L2 := Val.list ((1 :: gs).map fun g =>
      encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin s))))) with hL2
    set GG := Val.list [.nat (k + s), L1] with hGG
    set NN := Val.list [.nat (k + s), L2] with hNN
    -- weights
    have hsX : s + 1 ≤ X := by omega
    have wx' : (encPerm x').wt ≤ 4 * X ^ 2 :=
      (wt_encPerm_le x').trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsX 2))
    have wg' : (encGroup gs').wt ≤ 320 * X ^ 6 :=
      (wt_encGroup_le_sq hgl').trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsX 6))
    have hX6 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX1
    have wu : u.wt ≤ 700 * X ^ 6 := by
      have : u.wt ≤ 2 * ((encPerm x').wt + (encGroup gs').wt) + 6 := wt_list2_le _ _
      omega
    have wI : inp.wt ≤ 4000 * X ^ 6 := by
      have : inp.wt ≤ 2 * (ctx.wt + u.wt) + 6 := wt_list2_le _ _
      omega
    have hm3 : (gs.length + 2) * X ≤ 2 * X ^ 3 := measure_le_of_sq hgl
    have hm6 : ((gs.length + 2) * X) ^ 2 ≤ 4 * X ^ 6 := by
      calc ((gs.length + 2) * X) ^ 2 ≤ (2 * X ^ 3) ^ 2 := Nat.pow_le_pow_left hm3 2
        _ = 4 * X ^ 6 := by ring
    have hm21 : ((gs.length + 2) * X) ^ 7 ≤ 128 * X ^ 21 := by
      calc ((gs.length + 2) * X) ^ 7 ≤ (2 * X ^ 3) ^ 7 := Nat.pow_le_pow_left hm3 7
        _ = 128 * X ^ 21 := by ring
    have wL1 : L1.wt ≤ 160 * X ^ 6 := by
      have : L1.wt ≤ 40 * ((gs.length + 2) * X) ^ 2 :=
        wt_gensList_le (n := k + s) (by omega) (1 :: gs) (fun g => sumToFin (Perm.sumCongr g (restrP e S.G S.dom S.dom_inv g)))
      omega
    have wL2 : L2.wt ≤ 160 * X ^ 6 := by
      have : L2.wt ≤ 40 * ((gs.length + 2) * X) ^ 2 :=
        wt_gensList_le (n := k + s) (by omega) (1 :: gs) (fun g => sumToFin (Perm.sumCongr g (1 : Perm (Fin s))))
      omega
    have wks := wt_nat_le (k + s)
    have wGG : GG.wt ≤ 400 * X ^ 6 := by
      have : GG.wt ≤ 2 * ((Val.nat (k + s)).wt + L1.wt) + 6 := wt_list2_le _ _
      omega
    have wNN : NN.wt ≤ 400 * X ^ 6 := by
      have : NN.wt ≤ 2 * ((Val.nat (k + s)).wt + L2.wt) + 6 := wt_list2_le _ _
      omega
    -- reads of the input
    have rk : ∀ rest, Det P (inp :: rest) (.get (arg 0) (.nat 0)) (.nat k) (3 * inp.wt + 10) :=
      fun rest => Det.read2 (vs := [ctx, u]) (ws := [.nat k, .nat s, domCtx e S.dom, encGroup gs])
        rfl rfl
    have rs : ∀ rest, Det P (inp :: rest) (.get (arg 0) (.nat 1)) (.nat s) (3 * inp.wt + 11) :=
      fun rest => Det.read2 (vs := [ctx, u]) (ws := [.nat k, .nat s, domCtx e S.dom, encGroup gs])
        rfl rfl
    have rdc : ∀ rest, Det P (inp :: rest) (.get (arg 0) (.nat 2)) (domCtx e S.dom)
        (3 * inp.wt + 12) :=
      fun rest => Det.read2 (vs := [ctx, u]) (ws := [.nat k, .nat s, domCtx e S.dom, encGroup gs])
        rfl rfl
    have rgv : ∀ rest, Det P (inp :: rest) (.get (.get (arg 0) (.nat 3)) (.nat 1))
        (.list ((1 :: gs).map encPerm)) (4 * inp.wt + 24) :=
      fun rest => Det.read3 (vs := [ctx, u]) (ws := [.nat k, .nat s, domCtx e S.dom, encGroup gs])
        (us := [.nat k, .list ((1 :: gs).map encPerm)]) rfl rfl rfl
    have rx : ∀ rest, Det P (inp :: rest) (.get (arg 1) (.nat 0)) (encPerm x') (3 * inp.wt + 11) :=
      fun rest => Det.read2 (vs := [ctx, u]) (ws := [encPerm x', encGroup gs']) rfl rfl
    have rg : ∀ rest, Det P (inp :: rest) (.get (arg 1) (.nat 1)) (encGroup gs') (3 * inp.wt + 12) :=
      fun rest => Det.read2 (vs := [ctx, u]) (ws := [encPerm x', encGroup gs']) rfl rfl
    -- the graph generators
    have d1 := Det.call (Det.mk2 (Det.mk2 (rdc []) (rk [])) (rgv []))
      (graphList_spec e S.G S.dom S.dom_inv h hd hgs)
    have d2 := Det.call (Det.mk2 (Det.mk2 (Det.call (rs [L1]) (range_det h.range s)) (rk [L1]))
      (rgv [L1])) (leftList_spec e S.dom h gs)
    have d3 := Det.mk2 (Det.arith' (op := .add) (rk [L1, L2]) (rs [L1, L2]) (z := k + s) rfl)
      (Det.var' (P := P) (env := [inp, L1, L2]) (i := 1) rfl)
    have hpe : preimageEnc I = .list [.nat k, GG, encGroup gs'] := by
      change Val.list [.nat k, encGroup (graphGensF e S.G S.dom S.dom_inv gs), encGroup gs'] = _
      rw [encGroup_graphGensF]
    have d4 := Det.mk3 (rk [L1, L2, GG]) (Det.var' (P := P) (env := [inp, L1, L2, GG]) (i := 3) rfl)
      (rg [L1, L2, GG])
    rw [← hpe] at d4
    have pre := preimage_call hpre I hjp d4
    -- the program
    have dl := Det.length (P := P) (Det.arg' (vs := [ctx, u]) (rest := []) (j := 1) rfl)
    refine EvalAll.ite dl (fun _ _ hv => ⟨_, hv.1⟩) ?_
    rintro x cc ⟨hx2, hcc⟩
    simp only [Val.nat.injEq, List.length_cons, List.length_nil] at hx2
    subst hx2
    rw [if_neg (by decide)]
    refine EvalAll.letE d1 ?_
    rintro _ ca1 ⟨rfl, hca1⟩
    refine EvalAll.letE d2 ?_
    rintro _ ca2 ⟨rfl, hca2⟩
    refine EvalAll.letE d3 ?_
    rintro _ ca3 ⟨rfl, hca3⟩
    refine EvalAll.letE pre ?_
    rintro w4 ca4 ⟨hw4, hca4⟩
    obtain ⟨hs4, rfl, hl4, hgen⟩ := hw4
    have d5 := Det.call (Det.mk2 (rk [L1, L2, GG, Val.list (hs4.map encPerm)])
      (Det.var' (P := P) (env := [inp, L1, L2, GG, Val.list (hs4.map encPerm)]) (i := 4) rfl))
      ((mkGroup_spec (n := k) h.mkGroup hs4).mono (c' := mkGroupK * (8 * X ^ 9))
        (le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (measure_le_of_sq (n := k) hl4) 3))
          (le_of_eq (by rw [hX]; ring))))
    refine EvalAll.letE d5 ?_
    rintro _ ca5 ⟨rfl, hca5⟩
    have d6 := Det.mk3
      (Det.var' (P := P) (env := [inp, L1, L2, GG, Val.list (hs4.map encPerm), encGroup hs4])
        (i := 3) rfl)
      (Det.mk2 (Det.arith' (op := .add) (rk _) (rs _) (z := k + s) rfl)
        (Det.var' (P := P) (env := [inp, L1, L2, GG, Val.list (hs4.map encPerm), encGroup hs4])
          (i := 2) rfl))
      (Det.call (Det.mk3 (Det.call (rk _) (range_det h.range k)) (rx _) (rk _))
        (h.shift_spec (1 : Perm (Fin k)) x'))
    have hGG : GroupVal (k + s) GG (gens (graphGensF e S.G S.dom S.dom_inv gs)) :=
      ⟨_, (encGroup_graphGensF e S.G S.dom S.dom_inv gs).symm, rfl⟩
    have hNN : GroupVal (k + s) NN (gens (leftGensF e S.dom gs)) :=
      ⟨_, (encGroup_leftGensF e S.dom gs).symm, rfl⟩
    have fac := normalizedFactor_call hfac hjf d6 hGG hNN
      (normalizes_graph e S.G S.dom S.dom_inv hgs) (mem_graph_mul_left e S.G S.dom S.dom_inv hgs hx')
    refine EvalAll.letE fac ?_
    rintro w6 ca6 ⟨⟨g, hg, m, hm, hxgm, rfl⟩, hca6⟩
    obtain ⟨a, ha, rfl⟩ := factor_lift e S.G S.dom S.dom_inv hgs hg hm hxgm
    have d7 := Det.mk2 (Det.call (Det.mk2 (Det.get' (Det.var' (P := P)
        (env := [inp, L1, L2, GG, Val.list (hs4.map encPerm), encGroup hs4,
          .list [encPerm (graphHomF e S.G S.dom S.dom_inv a), encPerm m]]) (i := 6) rfl)
        (Det.nat 0) rfl) (Det.call (rk _) (range_det h.range k)))
        (gatherLeft_spec h.gather (a : Perm (Fin k)) (restrK e S.G S.dom S.dom_inv a)))
      (Det.var' (P := P) (env := [inp, L1, L2, GG, Val.list (hs4.map encPerm), encGroup hs4,
          .list [encPerm (graphHomF e S.G S.dom S.dom_inv a), encPerm m]]) (i := 5) rfl)
    refine d7.post ?_
    intro c7 hc7
    refine ⟨Or.inr ⟨a, hs4, rfl, hl4, ?_⟩, ?_⟩
    · rw [image_liftAnswer_coset e S A' hA a ha]
      congr 1
      ext b
      exact (Set.ext_iff.1 (preimageSet_liftInst e S.G S.dom S.dom_inv hgs gs' hms) b).symm.trans
        (SetLike.ext_iff.1 hgen b).symm
    · clear d1 d2 d3 d4 d5 d6 d7 pre fac dl rk rs rdc rgv rx rg
      change hs4.length ≤ k ^ 2 at hl4
      have hn : (I.n + 1) ^ 6 = X ^ 6 := rfl
      simp only [List.length_cons, List.length_nil] at hcc
      simp only [← hX, ← hsdef, hn] at hca1 hca2 hca3 hca4 hca5 hca6 hc7
      simp only [liftCost, liftK, ← hX]
      have hksX : k + s + 1 ≤ 2 * X := by omega
      -- small weights
      have wdc : (domCtx e S.dom).wt ≤ 30 * X ^ 2 := wt_domCtx_le e S.dom
      have wk := wt_nat_le k
      have wgl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
        wt_le_wt_list (vs := [.nat k, .list ((1 :: gs).map encPerm)]) (by simp)
      have wgs : (encGroup gs).wt ≤ 320 * X ^ 6 := wt_encGroup_le_sq hgl
      have w1s : (encPerm (1 : Perm (Fin s))).wt ≤ 4 * X ^ 2 :=
        (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsX 2))
      have w1k : (encPerm (1 : Perm (Fin k))).wt ≤ 4 * X ^ 2 := wt_encPerm_le _
      have h22 : (k + s + 1) ^ 2 ≤ 4 * X ^ 2 := by
        calc (k + s + 1) ^ 2 ≤ (2 * X) ^ 2 := Nat.pow_le_pow_left hksX 2
          _ = 4 * X ^ 2 := by ring
      have wsq : ∀ σ : Perm (Fin (k + s)), (encPerm σ).wt ≤ 16 * X ^ 2 := by
        intro σ
        have := wt_encPerm_le σ
        omega
      have wa : (encPerm (a : Perm (Fin k))).wt ≤ 4 * X ^ 2 := wt_encPerm_le _
      have a1 := wt_list2_le (domCtx e S.dom) (.nat k)
      have a2 := wt_list2_le (.list [domCtx e S.dom, .nat k]) (.list ((1 :: gs).map encPerm))
      have a3 := wt_list2_le (encPerm (1 : Perm (Fin s))) (.nat k)
      have a4 := wt_list2_le (.list [encPerm (1 : Perm (Fin s)), .nat k])
        (.list ((1 :: gs).map encPerm))
      have a5 : (Val.list [Val.nat (k + s), L1]).wt ≤ 400 * X ^ 6 := wGG
      have a6 : (Val.list [Val.nat (k + s), L2]).wt ≤ 400 * X ^ 6 := wNN
      have wpe : (preimageEnc I).wt ≤ 10 ^ 6 * X ^ 6 := by
        rw [hpe]
        have := wt_list3_le (.nat k) GG (encGroup gs')
        omega
      have bpre := Prim.bound_le (preimagePrim hpre) wpe
      have whs := wt_list_encPerms_le_sq hl4
      have whs' := wt_encGroup_le_sq hl4
      have a7 := wt_list2_le (.nat k) (.list (hs4.map encPerm))
      have eqG : (encGroup (n := k) hs4).wt = (encGroup (n := I.n) hs4).wt := rfl
      have eqL : (Val.list (List.map (encPerm (n := k)) hs4)).wt =
        (Val.list (List.map (encPerm (n := I.n)) hs4)).wt := rfl
      have a8 := wt_list3_le (encPerm (1 : Perm (Fin k))) (encPerm x') (.nat k)
      have wxx := wsq (sumToFin (Perm.sumCongr (1 : Perm (Fin k)) x'))
      have a9 := wt_list3_le GG (.list [.nat (k + s), L2]) (encPerm (sumToFin (Perm.sumCongr (1 : Perm (Fin k)) x')))
      have wfe : (Val.list [GG, .list [.nat (k + s), L2],
          encPerm (sumToFin (Perm.sumCongr (1 : Perm (Fin k)) x'))]).wt ≤ 10 ^ 6 * X ^ 6 := by omega
      have bfac := Prim.bound_le (normalizedFactorPrim hfac) wfe
      have hsh : shiftK * (k + s + 1) ^ 3 ≤ shiftK * (8 * X ^ 3) := by
        refine Nat.mul_le_mul_left _ ?_
        calc (k + s + 1) ^ 3 ≤ (2 * X) ^ 3 := Nat.pow_le_pow_left hksX 3
          _ = 8 * X ^ 3 := by ring
      have hs3 : (s + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hsX 3
      have wg := wsq (graphHomF e S.G S.dom S.dom_inv a)
      have wm := wsq m
      have b1 := wt_list2_le (encPerm (graphHomF e S.G S.dom S.dom_inv a)) (encPerm m)
      have b2 := wt_list2_le (encPerm (graphHomF e S.G S.dom S.dom_inv a))
        (encPerm (1 : Perm (Fin k)))
      have b3 := wt_list2_le (encPerm (a : Perm (Fin k))) (encGroup hs4)
      have hga : gatherK * (40 * (k + s + 1) ^ 2) ^ 3 ≤ gatherK * (64000 * 64 * X ^ 6) := by
        refine Nat.mul_le_mul_left _ ?_
        calc (40 * (k + s + 1) ^ 2) ^ 3 ≤ (40 * (4 * X ^ 2)) ^ 3 :=
              Nat.pow_le_pow_left (by omega) 3
          _ = 64000 * 64 * X ^ 6 := by ring
      have hinp : (Val.list [ctx, u]).wt = inp.wt := rfl
      rw [← hL1] at hca1
      rw [← hL2] at hca2
      simp only [gensMapK, mkGroupK, shiftK, gatherK] at *
      have hb0 : cc ≤ 10 ^ 5 * X ^ 6 := by omega
      have hb1 : ca1 ≤ 10 ^ 16 * X ^ 21 := by omega
      have hb2 : ca2 ≤ 10 ^ 16 * X ^ 21 := by omega
      have hb3 : ca3 ≤ 10 ^ 5 * X ^ 6 := by omega
      have hb4 : ca4 ≤ 10 ^ 7 * X ^ 6 + (preimagePrim hpre).c * (10 ^ 6 * X ^ 6 + 2) ^ (preimagePrim hpre).k := by
        omega
      have hb5 : ca5 ≤ 10 ^ 7 * X ^ 9 := by omega
      have hb6 : ca6 ≤ 10 ^ 10 * X ^ 6 + (normalizedFactorPrim hfac).c *
        (10 ^ 6 * X ^ 6 + 2) ^ (normalizedFactorPrim hfac).k := by omega
      have hb7 : c7 ≤ 10 ^ 12 * X ^ 6 := by omega
      have hbw : (Val.list [encPerm (a : Perm (Fin k)), encGroup hs4]).wt ≤ 10 ^ 4 * X ^ 6 := by omega
      omega

end GI.Impl
