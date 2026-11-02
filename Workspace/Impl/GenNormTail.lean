import Workspace.Impl.GenNormChildProg

/-! # The normalization children and their exact combination -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm Membership)
open scoped Pointwise

theorem normChildB_mono {Z Z' : ℕ} (h : Z ≤ Z') : normChildB Z ≤ normChildB Z' := by
  unfold normChildB
  gcongr

/-- Polynomial work of the child map, answer combination and canonical normal form. -/
noncomputable def normTailCost (hm : Membership) (k W : ℕ) : ℕ :=
  W * normChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40) +
    mapQK * (W + 1) * (W + piecesW k W + 1) + combCost k (combInW k W) +
    cosetNFCost hm k (combOutW k W) + 6 * combInW k W + 2 * combOutW k W + 2 * ansW k + 100

set_option maxHeartbeats 3000000 in
/-- The tail returns the canonical answer of `Run.normalize`, charging each recursive call
only to that run's children. -/
theorem normTail_spec (R : Rest) (hm : Membership) {Pg : Program} {F : Funs}
    {f bm fch bg bc g comp inv app bn jm : ℕ}
    (hf : Pg.funs[f]? = some (tailF bm bc bn))
    (hbm : Pg.HasAt bm (mapFuns bm fch)) (hch : Pg.funs[fch]? = some (normChildF F bg))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbc : Pg.HasAt bc (foldlFuns bc g)) (hg : Pg.funs[g]? = some (combStep comp inv app))
    (hcomp : Pg.HasAt comp (composeFuns comp)) (hinv : Pg.HasAt inv (invFuns inv))
    (happ : Pg.HasAt app (appendFuns app))
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {Ω C : Type} [Finite Ω] {k : ℕ} {e : Ω ≃ Fin k} {cc : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {sz : ℕ} {S : State Ω C}
    (hcan : Canon e cc (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S)
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive) (hfl : ¬ S.FloorEntered)
    (Q : PrimitiveQuotient S) (hsm : ¬ Q.SmallZ P₀.smallExp)
    (nc : Q.NormChoice) (hq : P₀.q₀ < (Q.normalizationOf nc).q)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) (b : Bool)
    (hmode : ∀ j, (normMode b = .cont ∧ ¬ ((Q.normAboveOf nc htr hq hkc hkl).child j).Transitive) ∨
      (normMode b = .giant ∧ ((Q.normAboveOf nc htr hq hkc hkl).child j).Transitive))
    {Kv hv' lv : Val} (hK : GroupValC k Kv (groupFin e (Q.normGroup nc.e nc.hS)))
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post))
    (hL : ∀ j, LabValStd e ((Q.normAboveOf nc htr hq hkc hkl).child j) lv
      ((Q.normAboveOf nc htr hq hkc hkl).childLabels j))
    (ts : List (Perm (Fin k))) (hlen : ts.length = (Q.normAboveOf nc htr hq hkc hkl).I.k)
    (hτ : ∀ j : Fin (Q.normAboveOf nc htr hq hkc hkl).I.k, nc.τ j = (toFin e).symm (ts.getD j 1))
    (hcall : ∀ j val, Canon e cc val ((Q.normAboveOf nc htr hq hkc hkl).child j) →
      FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
        (R.iface.Post (normMode b) ((Q.normAboveOf nc htr hq hkc hkl).child j) e
          (if b then .list [val, lv] else val))) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz],
        Kv, hv', lv, boolVal b], .list (ts.map encPerm)])
      (fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont S none A), r.kind = .normalize ∧
        AnsC e u A ∧ (cost : ℝ) ≤ normTailCost hm k (Val.list [.list
          [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], Kv, hv', lv, boolVal b],
          .list (ts.map encPerm)]).wt + R.iface.childCost r) := by
  let xs := ts.map encPerm
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz] with hvdef
  set ctx := Val.list [v, Kv, hv', lv, boolVal b] with hctx
  set a := Val.list [ctx, .list xs] with ha
  set W := a.wt with hW
  set n := xs.length with hn
  let NN := Q.normAboveOf nc htr hq hkc hkl
  have hnD : n = NN.I.k := by simpa only [n, xs, List.length_map] using hlen
  have hsumW := sum_wt_lt_wt_list [ctx, .list xs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsumW
  have ea : (Val.list [ctx, .list xs]).wt = W := rfl
  have hnW : n < W := (length_lt_wt_list xs).trans (by omega)
  -- the calls on the cosets
  have hmap := mapQ_spec hbm (c := ctx) (xs := xs)
    (R := fun i w => ∀ hi : i < NN.I.k, ∃ u,
      w = .list [encPerm (ts.getD i 1), u] ∧ AnsC e u (NN.child ⟨i, hi⟩).answer)
    (Q := fun i cb => ∀ hi : i < NN.I.k, ∃ (A : Set (Perm Ω))
      (r : Run P₀ (normMode b) (NN.child ⟨i, hi⟩)
        ((normMode b).labels (NN.childLabels ⟨i, hi⟩)) A), (cb : ℝ) ≤ r.total R.iface.work)
    (B := fun _ => normChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40)) (fun i hi => by
      have hiN : i < NN.I.k := by change i < n at hi; omega
      have hiT : i < ts.length := by simpa only [xs, List.length_map] using hi
      have hxi : xs[i] = encPerm (ts.getD i 1) := by
        simp only [xs, List.getElem_map, List.getD_eq_getElem _ _ hiT]
      have hxiW := wt_getElem_lt xs i hi
      rw [hxi] at hxiW ⊢
      refine (normChild_spec R hch hga hcan Q nc htr hq hkc hkl ⟨i, hiN⟩
        (ts.getD i 1) (hτ ⟨i, hiN⟩) b hK hH (hL ⟨i, hiN⟩) (hcall ⟨i, hiN⟩)).mono ?_
      rintro w cost ⟨hR, cb, hQ, hcost⟩
      refine ⟨fun _ => hR, cb, fun _ => hQ, ?_⟩
      change cost ≤ normChildB (5 * (Val.list [ctx, encPerm (ts.getD i 1)]).wt +
        ansW k + 20 * (k + 1) ^ 2 + 10) + cb at hcost
      have h2 := wt_list2_le ctx (encPerm (ts.getD i 1))
      exact hcost.trans (Nat.add_le_add_right (normChildB_mono (by omega)) _))
  set Bc := normChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40) with hBc
  have hcm : EvalAll Pg [a] (.call bm (.var 0)) (fun w cm => ∃ ws, w = .list ws ∧
      ws.length = n ∧ (∀ i (hi : i < ws.length), ∀ hiN : i < NN.I.k, ∃ u,
        ws[i] = .list [encPerm (ts.getD i 1), u] ∧ AnsC e u (NN.child ⟨i, hiN⟩).answer) ∧
      ∃ cs : ℕ → ℕ, (∀ i, i < n → ∀ hiN : i < NN.I.k, ∃ (A : Set (Perm Ω))
        (r : Run P₀ (normMode b) (NN.child ⟨i, hiN⟩)
          ((normMode b).labels (NN.childLabels ⟨i, hiN⟩)) A),
          (cs i : ℝ) ≤ r.total R.iface.work) ∧
        cm ≤ ∑ i ∈ Finset.range n, (Bc + cs i) + mapQK * (n + 1) * (W + w.wt + 1) + W + w.wt + 2) :=
    EvalAll.call_funAll (Det.var' (i := 0) (v := a) rfl) fun v0 ca h0 => by
      obtain ⟨rfl, hca⟩ := h0
      exact hmap.mono fun w cost hw => by
        obtain ⟨ws, rfl, hwl, hR, cs, hQ, hc⟩ := hw
        have hc' : cost ≤ ∑ i ∈ Finset.range n, (Bc + cs i) +
            mapQK * (n + 1) * (W + (Val.list ws).wt + 1) := by rw [ea] at hc; exact hc
        exact ⟨ws, rfl, hwl, hR, cs, hQ, by omega⟩
  refine FunAll.intro hf (EvalAll.letE hcm fun wsv cm hwsv => ?_)
  obtain ⟨ws, rfl, hwl, hR, cs, hQ, hcmb⟩ := hwsv
  -- the pieces
  have hpc : ∀ i : Fin ws.length, ∃ q : Acc k, ws[i] = encPiece (ts.getD i 1, q) ∧
      accSet q = toFin e '' (NN.child ⟨i, by omega⟩).answer := fun i => by
    obtain ⟨u, hu, hA⟩ := hR i i.2 (by omega)
    obtain ⟨q, rfl, hq⟩ := hA.acc
    exact ⟨q, hu, hq⟩
  choose qs hqs using hpc
  set ps : List (Perm (Fin k) × Acc k) := List.ofFn fun i : Fin ws.length => (ts.getD i 1, qs i)
    with hps
  have hws : ws = ps.map encPiece := List.ext_getElem (by simp [hps]) fun i h1 h2 => by
    simp only [hps, List.getElem_map, List.getElem_ofFn]
    exact (hqs ⟨i, h1⟩).1
  -- The calls made by the map are exactly the children of this normalization run.
  choose A' r' hr' using fun j : Fin NN.I.k => hQ j (by omega) j.2
  let r := Run.normalize hs htr hfl Q hsm nc hq hkc hkl NN rfl
    (normMode b) hmode A' r'
  have hτNN : ∀ j : Fin NN.I.k, NN.I.τ j = (toFin e).symm (ts.getD j 1) := hτ
  -- the answer
  have hU : unionSet ps = toFin e '' ⋃ j, NN.I.τ j • A' j := by
    ext g
    rw [Set.image_iUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, hg⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      refine ⟨⟨i, by omega⟩, ?_⟩
      rw [image_toFin_smul, hτNN, MulEquiv.apply_symm_apply, (r' _).exact]
      have := (hqs i).2
      simp only at hg this ⊢
      rw [← this]; exact hg
    · rintro ⟨j, hg⟩
      refine ⟨(ts.getD j 1, qs ⟨j, by omega⟩), List.mem_ofFn.mpr ⟨⟨j, by omega⟩, rfl⟩, ?_⟩
      rw [image_toFin_smul, hτNN, MulEquiv.apply_symm_apply, (r' _).exact] at hg
      have := (hqs ⟨j, by omega⟩).2
      simp only at hg this ⊢
      rw [this]; exact hg
  have hCE := combine_cosetOrEmpty ps (by rw [hU, r.exact]; exact image_answer_cases e S)
  -- the combination and the normal form
  have hmk := Det.mk3 (P := Pg) (env := [a, .list ws]) (Det.nat 0) (Det.var' (i := 1) rfl) Det.nil
  have hcomb := Det.call hmk (by
    rw [hws]; exact comb_spec hbc hg hcomp hinv happ (.nat 0) ps)
  refine EvalAll.call_funAll hcomb fun w0 ca h0 => ?_
  obtain ⟨rfl, hca⟩ := h0
  refine (cosetNF_spec hm hbn hjm hCE).mono fun u cb hu => ?_
  obtain ⟨hC, hcb⟩ := hu
  rw [hU] at hC
  refine ⟨_, r, rfl, CosetC.ansC hC, ?_⟩
  have hmne : normMode b ≠ .solve := by cases b <;> simp [normMode]
  have hch : R.iface.childCost r = ∑ j : Fin NN.I.k, (r' j).total R.iface.work := by
    simp only [r, Iface.childCost, Run.children, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      Iface.charge, hmne, if_false, add_zero]
  -- weights
  have hwu := (CosetC.ansC hC).wt_le
  have hpw : ∀ x ∈ ws, x.wt ≤ pieceW k := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨u', hu', hA'⟩ := hR i hi (by omega)
    rw [hu']
    have := wt_list2_le (encPerm (ts.getD i 1)) u'
    have := wt_encPerm_le (ts.getD i 1)
    have := hA'.wt_le
    unfold pieceW; omega
  have hWS : (Val.list ws).wt ≤ piecesW k W := by
    have := wt_list_le_of ws hpw
    have : ws.length * (2 * pieceW k + 1) ≤ W * (2 * pieceW k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    unfold piecesW; omega
  have hwc : (Val.list [.nat 0, .list ws, .list []]).wt ≤ combInW k W := by
    have h1 := wt_list3_le (.nat 0) (.list ws) (.list [])
    have := wt_nat_le 0
    rw [wt_list_nil] at h1
    unfold combInW; omega
  rw [← hws] at hca
  have hcc := combCost_mono k hwc
  have hL : ∀ c0 gs, combine ps = some (c0, gs) → gs.length ≤ combInW k W := by
    intro c0 gs h
    have h1 := length_combine ps c0 gs h
    have h2 := sum_accLen_le ps
    have h3 := sum_wt_lt_wt_list (ps.map encPiece)
    rw [← hws] at h2 h3
    have : (Val.list ws).wt < (Val.list [.nat 0, .list ws, .list []]).wt := wt_le_wt_list (by simp)
    omega
  have hacc : (encAcc (combine ps)).wt ≤ combOutW k W := wt_encAcc_le (combine ps) hL
  have hnf := cosetNFCost_mono hm k hacc
  have hmapb : mapQK * (n + 1) * (W + (Val.list ws).wt + 1) ≤
      mapQK * (W + 1) * (W + piecesW k W + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hsum : ∑ i ∈ Finset.range n, (Bc + cs i) = n * Bc + ∑ i ∈ Finset.range n, cs i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hnB : n * Bc ≤ W * Bc := Nat.mul_le_mul_right _ hnW.le
  have hpieces : W ≤ piecesW k W := by
    unfold piecesW
    have : W ≤ W * (2 * pieceW k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have key : cm + (ca + cb + u.wt + 1) + u.wt + 1 ≤
      normTailCost hm k W + ∑ i ∈ Finset.range n, cs i := by
    unfold normTailCost
    rw [← hBc]
    have hci : combInW k W = 2 * piecesW k W + 30 := rfl
    omega
  have hcs : (∑ i ∈ Finset.range n, (cs i : ℝ)) ≤ ∑ j : Fin NN.I.k, (r' j).total R.iface.work := by
    rw [hnD, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum fun j _ => hr' j
  rw [hch]
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this ⊢
  linarith

end GI.Impl
