module

public import Workspace.Impl.TermGlueLabPLift

@[expose] public section

/-!
# The lifts `k(s)` of the label step: the specifications of the two entry points

`tmGLPLc_spec`: the context program returns `liftLabCtx n m ps'` for pairs `ps'`
generating the image of `g ↦ (g, g|_{row i0})` on the label kernel. `tmGLPL1_spec`: with that
context, the one-lift program returns, for `s ∈ H`, the encoding of a tuple `y` with
`cleanRowPerm E y ∈ G|_dom` and `y i0 = s`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens PointwiseStab NormalizedFactor)
open GI.Lang (Prim)

/-- A map result related entrywise through an injective encoding. -/
theorem tmGLP_forall₂_map {α : Type*} {g F : α → Val} (hg : Function.Injective g) :
    ∀ {l : List α} {ws : List Val},
      List.Forall₂ (fun x w => ∃ p, x = g p ∧ w = F p) (l.map g) ws → ws = l.map F
  | [], ws, h => by cases h; rfl
  | a :: l, ws, h => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨p, hp, rfl⟩ := h1
      rw [hg hp, tmGLP_forall₂_map hg h2]
      rfl

theorem tmGLP_natList_injective : Function.Injective natList := by
  intro a b h
  have : a.map Val.nat = b.map Val.nat := by
    simpa [natList] using h
  exact List.map_injective_iff.2 (fun x y hxy => by injection hxy) this

theorem tmGLP_sum_const {α : Type*} (l : List α) (B : ℕ) : (l.map fun _ => B).sum = l.length * B := by
  simp

variable {Ω C : Type} {n : ℕ} {e : Ω ≃ Fin n} {S : State Ω C} {L : GiantLabels S}
  {label : Ω → Fin L.q} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom)

/-- The cost bound of the context program. -/
noncomputable def tmGLPLcC (hst : PointwiseStab) (M : ℕ) : ℕ :=
  rowKerCost hst M + 10 ^ 20 * M ^ 12

/-- **The context of the lifts.** -/
theorem tmGLPLc_spec (hst : PointwiseStab) {P : Program} {b jp jf : ℕ} (h : TmGLPLiftAt P b jp jf)
    (hj : P.prims[jp]? = some (pointwiseStabPrim hst)) (hnat : NaturalRows S L label)
    (hE : ∀ b i, label (E (b, i)) = i) (i0 : Fin L.q)
    {ps : List (Perm (Fin n) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) :
    FunAll P b (.list [.list [.nat n, .nat L.q], .list (ps.map pairV),
        natList ((rowList e E i0).map Fin.val)])
      (fun w c => ∃ ps' : List (Perm (Fin n) × Perm (Fin m)), w = liftLabCtx n m ps' ∧
        Subgroup.closure {p | p ∈ ps'} = (tmGLPχ e E hnat hE i0).range ∧
        ps'.length ≤ (n + L.q) ^ 2 ∧ c ≤ tmGLPLcC hst (pM n L.q ps)) := by
  set zs := (rowList e E i0).map Fin.val with hzs
  set A : Val := .list [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs] with hA
  have hz : ZsOK n zs := zsOK_row E i0
  have hzl : zs.length = m := by rw [hzs, List.length_map, rowList_length]
  have hmn : m ≤ n := m_le_n e E i0
  set M := pM n L.q ps with hM
  have hM2 : n + L.q + 2 ≤ M := by rw [hM]; unfold pM; omega
  have hM1 : 1 ≤ M := by omega
  -- weights of the input
  have wps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := wt_pairs_le_of_len le_rfl
  have wzs : (natList zs).wt ≤ 7 * (n + 1) ^ 2 := wt_zs_le hz
  have wnq := wt_list2_le (.nat n) (.nat L.q)
  have wn := wt_nat_le n
  have wq := wt_nat_le L.q
  have wA := wt_list3_le (.list [.nat n, .nat L.q]) (.list (ps.map pairV)) (natList zs)
  have p2 : (n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have p23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have p36 : M ^ 3 ≤ M ^ 6 := Nat.pow_le_pow_right hM1 (by omega)
  have p68 : M ^ 6 ≤ M ^ 8 := Nat.pow_le_pow_right hM1 (by omega)
  have p812 : M ^ 8 ≤ M ^ 12 := Nat.pow_le_pow_right hM1 (by omega)
  have pM3 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) _
  have pM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have h2M : 2 * M ≤ M ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_right M (by omega)
  have hAw : A.wt ≤ 200 * M ^ 3 := by
    have e1 : A.wt = (Val.list [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs]).wt :=
      rfl
    have : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  refine FunAll.intro h.lc ?_
  -- step 1: the label kernel
  have g0 := Det.arg' (P := P) (vs := [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs])
    (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs])
    (rest := []) (j := 1) rfl
  have e1 : EvalAll P [A] (.call (b + 69) (mk2 (arg 0) (arg 1))) (fun w c =>
      ∃ ks : List (Perm (Fin n) × Perm (Fin L.q)), w = .list (ks.map pairV) ∧
        ks.length ≤ (n + L.q) ^ 2 ∧ PairGens e L (kerG S L) ks ∧
        c ≤ rowKerCost hst M + 3000 * M ^ 6) := by
    refine EvalAll.call_funAll (Det.mk2 g0 g1) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (rowKer_spec hst h.ker hj ps).mono fun w c hw => ?_
    obtain ⟨ks, rfl, hkl, hks, hc⟩ := hw
    refine ⟨ks, rfl, hkl, pairGens_of_pre hps hks, ?_⟩
    have hkM : ks.length ≤ M ^ 2 := hkl.trans (Nat.pow_le_pow_left (by omega) 2)
    have wks : (Val.list (ks.map pairV)).wt ≤ 50 * (2 * M ^ 2) ^ 3 := by
      refine wt_pairs_le_of_len ?_
      unfold pM
      have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    have e23 : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
    rw [e23] at wks
    have w2 := wt_list2_le (.list [.nat n, .nat L.q]) (.list (ps.map pairV))
    have e1 : A.wt = (Val.list [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs]).wt :=
      rfl
    rw [← hM] at hc
    clear_value A zs M
    omega
  refine EvalAll.letE e1 fun v1 c1 h1 => ?_
  obtain ⟨ks, rfl, hkl, hks, hc1⟩ := h1
  -- the pairs `(a, a|_{row i0})`
  obtain ⟨ps', hps'e, hps'l, hps'c⟩ := tmGLP_pairs E hnat hE i0 hks
  have hkM : ks.length ≤ M ^ 2 := hkl.trans (Nat.pow_le_pow_left (by omega) 2)
  have wks : (Val.list (ks.map pairV)).wt ≤ 50 * (2 * M ^ 2) ^ 3 := by
    refine wt_pairs_le_of_len ?_
    unfold pM
    have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have wps' : (Val.list (ps'.map pairV)).wt ≤ 50 * (2 * M ^ 2) ^ 3 := by
    refine wt_pairs_le_of_len ?_
    unfold pM
    have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have e23 : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
  rw [e23] at wks wps'
  -- step 2: the map
  have h0 := Det.arg' (P := P) (vs := [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs])
    (rest := [Val.list (ks.map pairV)]) (j := 2) rfl
  have hv1 := Det.var' (P := P) (env := [A, Val.list (ks.map pairV)]) (i := 1)
    (v := Val.list (ks.map pairV)) rfl
  have hmap := map_spec h.pairMap (c := natList zs) (xs := ks.map pairV)
    (R := fun x w => ∃ p, x = pairV p ∧ w = .list [encPerm p.1, natList (partNat zs p.1)])
    (B := fun _ => tmGLPStepC n L.q) (fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact FunAll.mono (tmGLPPairStep_spec h.pairStep h.part hz p) fun w c hw =>
        ⟨⟨p, rfl, hw.1⟩, hw.2⟩)
  have hstep : ks.length * tmGLPStepC n L.q ≤ 1000 * 10 ^ 10 * M ^ 8 := by
    unfold tmGLPStepC
    have h6 : (n + L.q + 1) ^ 6 ≤ M ^ 6 := Nat.pow_le_pow_left (by omega) 6
    calc ks.length * (1000 * (partK * (n + L.q + 1) ^ 6)) ≤ M ^ 2 * (1000 * (partK * M ^ 6)) :=
          Nat.mul_le_mul hkM (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6))
      _ = 1000 * 10 ^ 10 * M ^ 8 := by unfold partK; ring
  have e2 : EvalAll P [A, Val.list (ks.map pairV)] (.call (b + 3) (mk2 (arg 2) (.var 1)))
      (fun w c => w = .list (ps'.map pairV) ∧ c ≤ 10 ^ 14 * M ^ 8) := by
    refine EvalAll.call_funAll (Det.mk2 h0 hv1) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hmap.mono fun w c hw => ?_
    obtain ⟨ws, rfl, hR, hc⟩ := hw
    have hws := tmGLP_forall₂_map pairV_injective hR
    rw [hws, hps'e] at hc ⊢
    refine ⟨rfl, ?_⟩
    rw [tmGLP_sum_const, List.length_map] at hc
    have w2 := wt_list2_le (natList zs) (.list (ks.map pairV))
    have hl : ks.length + 1 ≤ 2 * M ^ 2 := by
      have : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ hM1; omega
    have hw : (Val.list [natList zs, .list (ks.map pairV)]).wt + (Val.list (ps'.map pairV)).wt + 1
        ≤ 2000 * M ^ 6 := by omega
    have hmapc : mapK * (ks.length + 1) *
        ((Val.list [natList zs, .list (ks.map pairV)]).wt + (Val.list (ps'.map pairV)).wt + 1) ≤
        4000 * 1000 * M ^ 8 := by
      calc mapK * (ks.length + 1) * _ ≤ mapK * (2 * M ^ 2) * (2000 * M ^ 6) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hl) hw
        _ = 4000 * 1000 * M ^ 8 := by unfold mapK; ring
    have wl2 := wt_list2_le A (.list (ks.map pairV))
    have e1 : (Val.list [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs]).wt = A.wt :=
      rfl
    have wl2' := wt_list2_le (natList zs) (Val.list (ks.map pairV))
    have e3 : (Val.list [Val.list [Val.nat n, Val.nat L.q], Val.list (List.map pairV ps), natList zs]
      :: [Val.list (List.map pairV ks)]) = [A, Val.list (ks.map pairV)] := rfl
    clear_value A zs M
    try simp only [List.length_cons, List.length_nil] at *
    omega
  refine EvalAll.letE e2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- step 3: the context
  have k0 := Det.get' (Det.arg' (P := P)
    (vs := [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs])
    (rest := [Val.list (ks.map pairV), Val.list (ps'.map pairV)]) (j := 0) rfl) (Det.nat 0)
    (vs := [.nat n, .nat L.q]) (v := .nat n) rfl
  have k1 := Det.length (Det.arg' (P := P)
    (vs := [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs])
    (rest := [Val.list (ks.map pairV), Val.list (ps'.map pairV)]) (j := 2) (v := .list (zs.map Val.nat))
    rfl)
  have k2 := Det.var' (P := P) (env := [A, Val.list (ks.map pairV), Val.list (ps'.map pairV)]) (i := 2)
    (v := Val.list (ps'.map pairV)) rfl
  have hlen : (zs.map Val.nat).length = m := by rw [List.length_map, hzl]
  rw [hlen] at k1
  have d3 := Det.call (Det.mk2 (Det.mk2 k0 k1) k2)
    (it_hvLc_spec h.hvLc h.range h.grp h.enc h.mkG h.fstM ps')
  refine d3.post fun c3 hc3 => ⟨ps', rfl, hps'c, by omega, ?_⟩
  -- the cost
  have wctx := wt_liftLabCtx_le ps'
  have hpM' : pM n m ps' ≤ 2 * M ^ 2 := by
    unfold pM
    have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hlc : itHvLcC (pM n m ps') ≤ 10 ^ 14 * 64 * M ^ 12 := by
    unfold itHvLcC
    have := Nat.pow_le_pow_left hpM' 6
    have e6 : (2 * M ^ 2) ^ 6 = 64 * M ^ 12 := by ring
    rw [e6] at this
    calc 10 ^ 14 * pM n m ps' ^ 6 ≤ 10 ^ 14 * (64 * M ^ 12) := Nat.mul_le_mul_left _ this
      _ = 10 ^ 14 * 64 * M ^ 12 := by ring
  have hctx4 : (ps'.length + n + m + 2) ^ 4 ≤ 16 * M ^ 8 := by
    have h1 : ps'.length + n + m + 2 ≤ 2 * M ^ 2 := by
      have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    have := Nat.pow_le_pow_left h1 4
    have e4 : (2 * M ^ 2) ^ 4 = 16 * M ^ 8 := by ring
    omega
  have wl2 := wt_list2_le (.list [.nat n, .nat m]) (.list (ps'.map pairV))
  have wnm := wt_list2_le (.nat n) (.nat m)
  have wm := wt_nat_le m
  have wl3 := wt_list3_le A (.list (ks.map pairV)) (.list (ps'.map pairV))
  have e1 : (Val.list [.list [.nat n, .nat L.q], .list (ps.map pairV), natList zs]).wt = A.wt := rfl
  have wzl : (Val.list (zs.map Val.nat)).wt = (natList zs).wt := rfl
  unfold tmGLPLcC
  clear_value A zs M
  try simp only [List.length_cons, List.length_nil] at *
  omega

/-- The cost bound of one lift. -/
def tmGLPL1C (pf : Prim) (M : ℕ) : ℕ := liftLabCost pf M + 10 ^ 20 * M ^ 8

/-- **One lift.** With the context of `tmGLPLc_spec` (row `i0`) and `s ∈ H` (some blockwise
element of `G|_dom` has coordinate `s` at row `i0`), the program returns the encoding of a tuple
`y` with `cleanRowPerm E y ∈ G|_dom` and `y i0 = s`. It calls **NormalizedFactor** once. -/
theorem tmGLPL1_spec (hfac : NormalizedFactor) {P : Program} {b jp jf : ℕ}
    (h : TmGLPLiftAt P b jp jf) (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    (hnat : NaturalRows S L label) (hE : ∀ b i, label (E (b, i)) = i) (i0 : Fin L.q)
    {ps' : List (Perm (Fin n) × Perm (Fin m))}
    (hps' : Subgroup.closure {p | p ∈ ps'} = (tmGLPχ e E hnat hE i0).range)
    {s : Perm (Fin m)} (hs : ∃ y : Fin L.q → Perm (Fin m), cleanRowPerm E y ∈ S.domGroup ∧ y i0 = s) :
    FunAll P (b + 1) (.list [.list [liftLabCtx n m ps', coordsVal e S E], encPerm s])
      (fun w c => ∃ y : Fin L.q → Perm (Fin m),
        w = .list ((List.finRange L.q).map fun i => encPerm (y i)) ∧
        cleanRowPerm E y ∈ S.domGroup ∧ y i0 = s ∧
        c ≤ tmGLPL1C (normalizedFactorPrim hfac) (ps'.length + n + n + L.q + 2)) := by
  set X := ps'.length + n + n + L.q + 2 with hX
  have hmn : m ≤ n := m_le_n e E i0
  have hX1 : 1 ≤ X := by omega
  set ctx := liftLabCtx n m ps' with hctx
  set rows := coordsVal e S E with hrows
  have wctx : ctx.wt ≤ 400 * X ^ 4 := by
    have := wt_liftLabCtx_le ps'
    have ectx : ctx.wt = (liftLabCtx n m ps').wt := rfl
    have := Nat.pow_le_pow_left (show ps'.length + n + m + 2 ≤ X by omega) 4
    omega
  have wrows : rows.wt ≤ 15 * X ^ 3 + 4 := by
    have := wt_coordsVal_le (e := e) E
    have erows : rows.wt = (coordsVal e S E).wt := rfl
    have := Nat.pow_le_pow_left (show n + L.q + 2 ≤ X by omega) 3
    omega
  have ws := wt_encPerm_le s
  have ps2 : (m + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have p23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p34 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by omega)
  have p48 : X ^ 4 ≤ X ^ 8 := Nat.pow_le_pow_right hX1 (by omega)
  have p14 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX1
  refine FunAll.intro h.l1 ?_
  -- step 1: the lift `(a, s)`
  have g0 := Det.arg' (P := P) (vs := [.list [ctx, rows], encPerm s]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.list [ctx, rows], encPerm s]) (rest := []) (j := 1) rfl
  have gc := Det.get' g0 (Det.nat 0) (vs := [ctx, rows]) (v := ctx) rfl
  have hσ : ∃ a, (a, s) ∈ Subgroup.closure {p | p ∈ ps'} := by
    rw [hps']; exact tmGLP_pairs_exists E hnat hE i0 hs
  have e1 : EvalAll P [.list [.list [ctx, rows], encPerm s]]
      (.call (b + 51) (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (fun w c =>
        ∃ a, w = encPerm a ∧ (a, s) ∈ Subgroup.closure {p | p ∈ ps'} ∧
          c ≤ liftLabCost (normalizedFactorPrim hfac) X + 20000 * X ^ 4) := by
    refine EvalAll.call_funAll (Det.mk2 gc g1) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (liftLab_spec hfac h.liftLab h.shift h.split hjf ps' hσ).mono fun w c hw => ?_
    obtain ⟨a, rfl, ha, hc⟩ := hw
    refine ⟨a, rfl, ha, ?_⟩
    have hmono := lc_liftLabCost_mono (normalizedFactorPrim hfac)
      (show ps'.length + n + m + 2 ≤ X by omega)
    have wa := wt_encPerm_le a
    have pn2 : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have w2 := wt_list2_le ctx rows
    have w2' := wt_list2_le (.list [ctx, rows]) (encPerm s)
    have w3 := wt_list2_le ctx (encPerm s)
    clear_value ctx rows X
    omega
  refine EvalAll.letE e1 fun v1 c1 h1 => ?_
  obtain ⟨a, rfl, ha, hc1⟩ := h1
  -- step 2: the parts of `a` on all rows
  obtain ⟨y, hy, hyG, hy0⟩ := tmGLP_lift_of_pair E hnat hE i0 (hps' ▸ ha)
  set zsOf : Fin L.q → List ℕ := fun j => (rowList e E j).map Fin.val with hzsOf
  have hrowsE : rows = .list (((List.finRange L.q).map zsOf).map natList) := by
    rw [hrows, coordsVal_eq, List.map_map]; rfl
  have hv := Det.var' (P := P) (env := [.list [.list [ctx, rows], encPerm s], encPerm a]) (i := 1)
    (v := encPerm a) rfl
  have g0' := Det.arg' (P := P) (vs := [.list [ctx, rows], encPerm s]) (rest := [encPerm a])
    (j := 0) rfl
  have gr := Det.get' g0' (Det.nat 1) (vs := [ctx, rows]) (v := rows) rfl
  have hmap := map_spec h.rowMap (c := pairV (a, a)) (xs := ((List.finRange L.q).map zsOf).map natList)
    (R := fun x w => ∃ zs, x = natList zs ∧ w = natList (partNat zs a))
    (B := fun _ => tmGLPStepC n n) (fun x hx => by
      obtain ⟨zs, hzs, rfl⟩ := List.mem_map.1 hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hzs
      exact FunAll.mono (tmGLPRowStep_spec h.rowStep h.part (zsOK_row E j) a) fun w c hw =>
        ⟨⟨_, rfl, hw.1⟩, hw.2⟩)
  rw [← hrowsE] at hmap
  refine EvalAll.call_funAll (Det.mk2 (Det.mk2 hv hv) gr) fun v ca hv' => ?_
  obtain ⟨rfl, hca⟩ := hv'
  refine hmap.mono fun w c hw => ?_
  obtain ⟨ws', rfl, hR, hc⟩ := hw
  have hws := tmGLP_forall₂_map (F := fun zs => natList (partNat zs a)) tmGLP_natList_injective hR
  rw [List.map_map] at hws
  have hws' : ws' = (List.finRange L.q).map fun i => encPerm (y i) := by
    rw [hws, ← hy]; rfl
  refine ⟨y, by rw [hws'], hyG, hy0, ?_⟩
  -- the cost
  rw [tmGLP_sum_const, List.length_map, List.length_map, List.length_finRange] at hc
  have wout : (Val.list ((List.finRange L.q).map fun i => encPerm (y i))).wt ≤
      L.q * (2 * (4 * (m + 1) ^ 2) + 1) + 4 := by
    have := wt_list_map_le (List.finRange L.q) (fun i => encPerm (y i)) (W := 4 * (m + 1) ^ 2)
      (fun i _ => wt_encPerm_le (y i))
    rw [List.length_finRange] at this
    omega
  rw [← hws'] at wout
  have hstep : L.q * tmGLPStepC n n ≤ 64 * (1000 * 10 ^ 10 * X ^ 7) := by
    unfold tmGLPStepC
    have h6 : (n + n + 1) ^ 6 ≤ (2 * X) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have e6 : (2 * X) ^ 6 = 64 * X ^ 6 := by ring
    rw [e6] at h6
    calc L.q * (1000 * (partK * (n + n + 1) ^ 6)) ≤ X * (1000 * (partK * (64 * X ^ 6))) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6))
      _ = 64 * (1000 * 10 ^ 10 * X ^ 7) := by unfold partK; ring
  have wpa := wt_pairV_le (a, a)
  have pnn : (n + n + 1) ^ 2 ≤ 4 * X ^ 2 := by
    have := Nat.pow_le_pow_left (show n + n + 1 ≤ 2 * X by omega) 2
    have e2 : (2 * X) ^ 2 = 4 * X ^ 2 := by ring
    omega
  have wa := wt_encPerm_le a
  have pn2 : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wl1 := wt_list2_le (pairV (a, a)) rows
  have wl0 := wt_list2_le (.list [ctx, rows]) (encPerm s)
  have wl00 := wt_list2_le ctx rows
  have hmapc : mapK * (L.q + 1) * ((Val.list [pairV (a, a), rows]).wt + (Val.list ws').wt + 1) ≤
      1000 * X * (400 * X ^ 3) := by
    have hw : (Val.list [pairV (a, a), rows]).wt + (Val.list ws').wt + 1 ≤ 400 * X ^ 3 := by
      have : L.q * (2 * (4 * (m + 1) ^ 2) + 1) ≤ X * (8 * X ^ 2 + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e3 : X * (8 * X ^ 2 + 1) = 8 * X ^ 3 + X := by ring
      have : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) _
      omega
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hw
  have e4 : 1000 * X * (400 * X ^ 3) = 400000 * X ^ 4 := by ring
  rw [e4] at hmapc
  have hmK : mapK = 1000 := rfl
  have p78 : X ^ 7 ≤ X ^ 8 := Nat.pow_le_pow_right hX1 (by omega)
  have hf1 : L.q * (2 * (4 * (m + 1) ^ 2) + 1) ≤ X * (8 * X ^ 2 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e3 : X * (8 * X ^ 2 + 1) = 8 * X ^ 3 + X := by ring
  have pX3 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) _
  have ea1 : (pairV (a, a)).wt = (Val.list [encPerm a, encPerm a]).wt := rfl
  have ea2 : (Val.list [pairV (a, a), rows]).wt =
      (Val.list [Val.list [encPerm a, encPerm a], rows]).wt := rfl
  have wa2 := wt_list2_le (encPerm a) (encPerm a)
  unfold tmGLPL1C
  clear_value ctx rows X zsOf
  rw [hmK] at hmapc hc
  try simp only [List.length_cons, List.length_nil] at *
  omega

end GI.Impl
