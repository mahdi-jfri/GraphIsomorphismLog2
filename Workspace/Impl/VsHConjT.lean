import Workspace.Impl.VsHConj

/-!
# Conjugation of a tuple of local matrices

The `Q₈` branch needs the centralizer of `Ȳ` in `C`, the stabilizer of the tuple
`(T(b))_{b ∈ B}` under conjugation. Points are lists of matrices with keys
`m :: [0, key M₁] ++ … ++ [0, key M_m]`; `vsHConjTE` cuts the key into pieces, conjugates each
piece with `vsHConjE` and joins them (`vsHConjT_spec`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- The action on tuples. -/
noncomputable def vsHAlT (s : VsQSt I) (g : Perm (Fin I.n))
    (ys : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p))) :
    List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :=
  ys.map (vsHAl s g)

theorem vsH_conjT_act (hs : VsQStOK s) : VsQPAct (gens s.hs) (vsHAlT s) := by
  have h := vsH_conj_act hs
  refine ⟨fun ys => ?_, fun g hg h' hh ys => ?_⟩
  · have e : vsHAl s 1 = id := funext h.one
    simp [vsHAlT, e]
  · simp [vsHAlT, h.mul g hg h' hh, List.map_map, Function.comp_def]

/-- The piece of one matrix. -/
noncomputable def vsHPc (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) : List ℕ :=
  0 :: vsHKey M

/-- The key of a tuple. -/
noncomputable def vsHKeyT (ys : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p))) : List ℕ :=
  ys.length :: (ys.map vsHPc).flatten

theorem vsHPc_length (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :
    (vsHPc M).length = vsQD s * vsQD s + 1 := by
  rw [vsHPc, List.length_cons, vsHKey_length]

/-- Cutting the joined pieces gives back the pieces. -/
theorem vsHKeyT_chunk (ys : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p))) :
    vsQChunk (Val.nat 0) (vsQD s * vsQD s + 1) ys.length ((ys.map vsHPc).flatten.map Val.nat) =
      ys.map fun M => (vsHPc M).map Val.nat := by
  have hc := vsQChunk_flatten (Val.nat 0) (vsQD s * vsQD s + 1) (ys.map fun M => (vsHPc M).map Val.nat)
    (fun x hx => by
      obtain ⟨M, -, rfl⟩ := List.mem_map.1 hx
      rw [List.length_map, vsHPc_length])
  rw [List.length_map] at hc
  rw [List.map_flatten, List.map_map]
  exact hc

theorem vsHKeyT_injective : Function.Injective (vsHKeyT (s := s)) := by
  intro ys ys' h
  have hl : ys.length = ys'.length := (List.cons.inj h).1
  have hf := (List.cons.inj h).2
  have := vsHKeyT_chunk ys
  rw [hf, hl, vsHKeyT_chunk] at this
  have hinj : Function.Injective fun M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p) =>
      (vsHPc M).map Val.nat := by
    intro M M' e
    have e1 := List.map_injective_iff.2 (fun a b hab => Val.nat.inj hab) e
    exact vsHKey_injective (List.cons.inj e1).2
  exact List.map_injective_iff.2 hinj this.symm

/-- The item of the map, on `[[ac, g], piece]`. -/
def vsHConjItE (conj : ℕ) : Expr := .call conj (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))

/-- The tuple program, on `[ac, g, [0, keyT ys]]`. -/
def vsHConjTE (tl ch mp cat app : ℕ) : Expr :=
  .letE (.call tl (.call tl (arg 2)))
  (.letE (.call ch (mk3 (.arith .add (.arith .mul (vsHAc 3) (vsHAc 3)) (.nat 1)) (.get (arg 2) (.nat 1))
      (.var 1)))
  (.letE (.call mp (mk2 (mk2 (arg 0) (arg 1)) (.var 2)))
    (.call app (mk2 (mk2 (.nat 0) (.get (arg 2) (.nat 1))) (.call cat (.var 3))))))

/-- The indices of the tuple program. -/
structure VsHTX where
  (c : VsHCX) (conjT mp it cat : ℕ)

/-- The layout of the tuple program. -/
structure VsHTLay (P : Program) (x : VsHTX) : Prop where
  c : VsHCLay P x.c
  hconjT : P.funs[x.conjT]? = some (vsHConjTE x.c.tl x.c.ch x.mp x.cat x.c.app)
  hmp : P.HasAt x.mp (mapFuns x.mp x.it)
  hit : P.funs[x.it]? = some (vsHConjItE x.c.conj)
  hcat : P.HasAt x.cat (vsWFlatFuns x.cat)

/-- The cost of the tuple program. -/
def vsHConjTCost (Cφ N : ℕ) : ℕ := (N + 1) * vsHConjCost Cφ N + 10 ^ 12 * (N + 1) ^ 8

set_option maxHeartbeats 8000000 in
/-- **The tuple program.** -/
theorem vsHConjT_spec {P : Program} {x : VsHTX} (L : VsHTLay P x) {Cφ N : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.c.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hΓ : (vsQGam I).wt ≤ N) (hn : I.n ≤ N)
    (hfr : VsWFrOK I.p N I.d s.ws' (vsQCs s)) (hDD1 : vsQD s * vsQD s + 1 ≤ N)
    (hac : (vsHAcV s).wt ≤ 1000 * (N + 1) ^ 3)
    {g : Perm (Fin I.n)} (hg : g ∈ gens I.gs)
    (ys : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p))) (hm : ys.length ≤ N) :
    FunDet P x.conjT (.list [vsHAcV s, encPerm g, natList (0 :: vsHKeyT ys)])
      (natList (0 :: vsHKeyT (vsHAlT s g ys))) (vsHConjTCost Cφ N) := by
  have hpN := hsz.pN
  set m := ys.length
  set DD := vsQD s * vsQD s
  set flat := (ys.map vsHPc).flatten
  have hfl : flat.length = m * (DD + 1) := by
    simp only [flat, List.length_flatten, List.map_map, Function.comp_def, vsHPc_length]
    simp [m]
    exact Or.inl rfl
  set vs := [vsHAcV s, encPerm g, natList (0 :: vsHKeyT ys)]
  have ekey : natList (0 :: vsHKeyT ys) = .list (Val.nat 0 :: Val.nat m :: flat.map Val.nat) := rfl
  -- the two tails
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  rw [ekey] at a2
  have t1 := Det.call a2 (GI.Lang.tail_spec L.c.htl (Val.nat 0) (Val.nat m :: flat.map Val.nat))
  have t2 := Det.call t1 (GI.Lang.tail_spec L.c.htl (Val.nat m) (flat.map Val.nat))
  -- the pieces
  set E1 := [Val.list vs, Val.list (flat.map Val.nat)]
  have rac : ∀ rest : List Val, ∀ j (v : Val), [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      .nat (vsQD s), natList (vsWZ (vsQD s))][j]? = some v →
      Det P (Val.list vs :: rest) (vsHAc j) v _ :=
    fun rest j v h => Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl) (Det.nat j) h
  have r3 := rac [Val.list (flat.map Val.nat)] 3 (.nat (vsQD s)) rfl
  have dDD := Det.arith (op := .add) (Det.arith (op := .mul) r3 r3) (Det.nat (P := P) (env := E1) 1)
  have eDD : GI.Machine.BinOp.eval .add (GI.Machine.BinOp.eval .mul (vsQD s) (vsQD s)) 1 = DD + 1 := rfl
  rw [eDD] at dDD
  have a2' := Det.arg' (P := P) (vs := vs) (rest := [Val.list (flat.map Val.nat)]) (j := 2) rfl
  rw [ekey] at a2'
  have dm := Det.get' a2' (Det.nat 1)
    (show (Val.nat 0 :: Val.nat m :: flat.map Val.nat)[1]? = some (.nat m) from rfl)
  have hmDD : m * (DD + 1) ≤ N * N := Nat.mul_le_mul hm (by omega)
  have q2 : N * N + 1 ≤ (N + 1) ^ 2 := by nlinarith
  have hflatW : ∀ zs : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)), zs.length = m →
      (Val.list ((zs.map vsHPc).flatten.map Val.nat)).wt ≤ 20 * (N + 1) ^ 4 := by
    intro zs hzs
    have hl : (zs.map vsHPc).flatten.length = m * (DD + 1) := by
      simp only [List.length_flatten, List.map_map, Function.comp_def, vsHPc_length]
      simp [hzs]
      exact Or.inl rfl
    have hz : ∀ y ∈ (zs.map vsHPc).flatten, y ≤ N := by
      intro y hy
      obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 hy
      obtain ⟨M, -, rfl⟩ := List.mem_map.1 hl
      rcases List.mem_cons.1 hyl with rfl | hy'
      · omega
      · exact (vsHKey_lt M y hy').le.trans hpN
    have := wt_natList_le_sq (xs := (zs.map vsHPc).flatten) (B := (N + 1) ^ 2)
      (fun y hy => (hz y hy).trans (by nlinarith)) (by rw [hl]; omega)
    have e : 5 * ((N + 1) ^ 2 + 1) ^ 2 ≤ 20 * (N + 1) ^ 4 := by nlinarith
    exact this.trans e
  have hfw : (Val.list (flat.map Val.nat)).wt ≤ 20 * (N + 1) ^ 4 := hflatW ys rfl
  have d2 := Det.call (Det.mk3 dDD dm (Det.var' (P := P) (env := E1) (i := 1) rfl))
    (vsQChunk_spec L.c.hch (k := DD + 1) (m := m) (N := N) (W := 20 * (N + 1) ^ 4)
      (by rw [List.length_map, hfl, Nat.mul_comm]) (by omega) hm hfw)
  rw [vsHKeyT_chunk ys] at d2
  have ePc : (ys.map fun M => (vsHPc M).map Val.nat).map Val.list = ys.map fun M => natList (vsHPc M) := by
    simp [List.map_map, Function.comp_def, natList]
  rw [ePc] at d2
  -- the map
  set ys' := vsHAlT s g ys
  set E2 := [Val.list vs, Val.list (flat.map Val.nat), Val.list (ys.map fun M => natList (vsHPc M))]
  have b0 := Det.arg' (P := P) (vs := vs) (rest := [Val.list (flat.map Val.nat),
    Val.list (ys.map fun M => natList (vsHPc M))]) (j := 0) rfl
  have b1 := Det.arg' (P := P) (vs := vs) (rest := [Val.list (flat.map Val.nat),
    Val.list (ys.map fun M => natList (vsHPc M))]) (j := 1) rfl
  have hit : ∀ M ∈ ys, FunDet P x.it (.list [.list [vsHAcV s, encPerm g], natList (vsHPc M)])
      (natList (vsHPc (vsHAl s g M))) (vsHConjCost Cφ N + 10 ^ 5 * (N + 1) ^ 3) := by
    intro M _
    set A := Val.list [.list [vsHAcV s, encPerm g], natList (vsHPc M)]
    have c0 := Det.arg' (P := P) (vs := [.list [vsHAcV s, encPerm g], natList (vsHPc M)]) (rest := [])
      (j := 0) rfl
    have c1 := Det.arg' (P := P) (vs := [.list [vsHAcV s, encPerm g], natList (vsHPc M)]) (rest := [])
      (j := 1) rfl
    have cac := Det.get' c0 (Det.nat 0) (show [vsHAcV s, encPerm g][0]? = some (vsHAcV s) from rfl)
    have cg := Det.get' c0 (Det.nat 1) (show [vsHAcV s, encPerm g][1]? = some (encPerm g) from rfl)
    have dc := Det.call (Det.mk3 cac cg c1) (vsHConj_spec L.c hphi hsz hΓ hn hfr hDD1 hac hg M)
    refine FunDet.intro L.hit (dc.mono ?_)
    have wpc : ∀ M' : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p),
        (natList (vsHPc M')).wt ≤ 5 * (N + 1) ^ 2 := fun M' =>
      wt_natList_le_sq (B := N) (fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · exact (vsHKey_lt M' y hy).le.trans hpN) (by rw [vsHPc_length]; omega)
    have w1 := wpc M
    have w2 := wpc (vsHAl s g M)
    have wg := wt_encPerm_le g
    have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have l1 := wt_list2_le (vsHAcV s) (encPerm g)
    have l2 := wt_list2_le (Val.list [vsHAcV s, encPerm g]) (natList (vsHPc M))
    have l3 := wt_list3_le (vsHAcV s) (encPerm g) (natList (vsHPc M))
    have eA : A.wt = (Val.list [.list [vsHAcV s, encPerm g], natList (vsHPc M)]).wt := rfl
    have e1 : natList (0 :: vsHKey (vsHT s g⁻¹ * M * vsHT s g)) = natList (vsHPc (vsHAl s g M)) := rfl
    have e2 : natList (0 :: vsHKey M) = natList (vsHPc M) := rfl
    rw [e1] at *
    have := wt_nat_le 0; have := wt_nat_le 1
    omega
  have dmap := Det.call (Det.mk2 (Det.mk2 b0 b1) (Det.var' (P := P) (env := E2) (i := 2) rfl))
    (vsQ_map L.hmp ys (fun M => natList (vsHPc M)) (fun M => natList (vsHPc (vsHAl s g M)))
      (fun M M' h => by
        have := vsFMat_natList_inj h
        exact vsHKey_injective (List.cons.inj this).2) hit)
  -- the join
  set xss := ys.map fun M => (vsHPc (vsHAl s g M)).map Val.nat
  have exs : Val.list (ys.map fun M => natList (vsHPc (vsHAl s g M))) = Val.list (xss.map Val.list) := by
    simp [xss, List.map_map, Function.comp_def, natList]
  rw [exs] at dmap
  have ef : xss.flatten = (ys'.map vsHPc).flatten.map Val.nat := by
    simp [xss, ys', vsHAlT, List.map_flatten, List.map_map, Function.comp_def]
  have hys' : ys'.length = m := by simp [ys', vsHAlT, m]
  have wpc : ∀ M' : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p),
      (natList (vsHPc M')).wt ≤ 5 * (N + 1) ^ 2 := fun M' =>
    wt_natList_le_sq (B := N) (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact (vsHKey_lt M' y hy).le.trans hpN) (by rw [vsHPc_length]; omega)
  have hWi : (Val.list (xss.map Val.list)).wt ≤ 1000 * (N + 1) ^ 4 := by
    have := vs_wt_list_le_of (xss.map Val.list) (c := 5 * (N + 1) ^ 2) (by
      intro v hv
      simp only [xss, List.map_map, List.mem_map, Function.comp_def] at hv
      obtain ⟨M, -, rfl⟩ := hv
      exact wpc _)
    have hlen : (xss.map Val.list).length = m := by simp [xss, m]
    rw [hlen] at this
    have : m * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
    have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    have : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  set E3 := [Val.list vs, Val.list (flat.map Val.nat), Val.list (ys.map fun M => natList (vsHPc M)),
    Val.list (xss.map Val.list)]
  have dcat := Det.call (Det.var' (P := P) (env := E3) (i := 3) rfl)
    (vsWConcat_spec L.hcat xss (N := N) (by simp [xss]; omega)
      (fun xs hxs => by
        simp only [xss, List.mem_map] at hxs
        obtain ⟨M, -, rfl⟩ := hxs
        rw [List.length_map, vsHPc_length]; omega)
      (by rw [ef]; exact (hflatW ys' hys').trans (by nlinarith)) hWi)
  rw [ef] at dcat
  -- prepend `[0, m]`
  have a2'' := Det.arg' (P := P) (vs := vs) (rest := [Val.list (flat.map Val.nat),
    Val.list (ys.map fun M => natList (vsHPc M)), Val.list (xss.map Val.list)]) (j := 2) rfl
  rw [ekey] at a2''
  have dm' := Det.get' a2'' (Det.nat 1)
    (show (Val.nat 0 :: Val.nat m :: flat.map Val.nat)[1]? = some (.nat m) from rfl)
  set fl' := (ys'.map vsHPc).flatten
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P E3 (mk2 (mk2 (.nat 0) (.get (arg 2) (.nat 1)))
      (.call x.cat (.var 3))) (.list [.list [Val.nat 0, Val.nat m], .list (fl'.map Val.nat)]) KA :=
    ⟨_, rfl, Det.mk2 (Det.mk2 (Det.nat 0) dm') dcat⟩
  have hfl' : fl'.length = m * (DD + 1) := by
    simp only [fl', List.length_flatten, List.map_map, Function.comp_def, vsHPc_length]
    simp [hys']
    exact Or.inl rfl
  have wout := hflatW ys' hys'
  set KP := loopModK * (m * (DD + 1) + 1) *
    ((Val.list [.list [Val.nat 0, Val.nat m], .list (fl'.map Val.nat)]).wt + m * (DD + 1) +
      (natList (0 :: vsHKeyT ys')).wt + 1)
  have dap : Det P E3 (.call x.c.app (mk2 (mk2 (.nat 0) (.get (arg 2) (.nat 1))) (.call x.cat (.var 3))))
      (natList (0 :: vsHKeyT ys')) (KA + KP + (natList (0 :: vsHKeyT ys')).wt + 1) := by
    refine EvalAll.call_funAll dA fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (append_spec L.c.happ [Val.nat 0, Val.nat m] (fl'.map Val.nat)).mono fun w c hw => ⟨?_, ?_⟩
    · rw [hw.1]; simp [vsHKeyT, hys', natList, fl']
    · have h2 := hw.2
      have hw' : w = natList (0 :: vsHKeyT ys') := by rw [hw.1]; simp [vsHKeyT, hys', natList, fl']
      rw [hw'] at h2 ⊢
      have hc : c ≤ KP := by
        simp only [KP]
        rw [List.length_map, hfl'] at h2
        exact h2
      clear_value KP
      omega
  refine FunDet.intro L.hconjT ((Det.letE t2 (Det.letE d2 (Det.letE dmap dap))).mono ?_)
  -- weights
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q46 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q68 : (N + 1) ^ 6 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hkey : ∀ zs : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)), zs.length = m →
      (natList (0 :: vsHKeyT zs)).wt ≤ 20 * (N + 1) ^ 4 := by
    intro zs hzs
    have hl : (zs.map vsHPc).flatten.length = m * (DD + 1) := by
      simp only [List.length_flatten, List.map_map, Function.comp_def, vsHPc_length]
      simp [hzs]
      exact Or.inl rfl
    have hz : ∀ y ∈ 0 :: vsHKeyT zs, y ≤ (N + 1) ^ 2 := by
      intro y hy
      simp only [vsHKeyT, List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · omega
      · omega
      · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 hy
        obtain ⟨M, -, rfl⟩ := List.mem_map.1 hl
        rcases List.mem_cons.1 hyl with rfl | hy'
        · omega
        · have := (vsHKey_lt M y hy').le.trans hpN; omega
    have := wt_natList_le_sq (xs := 0 :: vsHKeyT zs) (B := (N + 1) ^ 2) hz (by
      simp only [vsHKeyT, List.length_cons, hl]; nlinarith)
    have e : 5 * ((N + 1) ^ 2 + 1) ^ 2 ≤ 20 * (N + 1) ^ 4 := by nlinarith
    exact this.trans e
  have wk := hkey ys rfl
  have wk' := hkey ys' hys'
  have ek : natList (0 :: vsHKeyT ys) = Val.list (Val.nat 0 :: Val.nat m :: flat.map Val.nat) := ekey
  have wm1 : (Val.list (Val.nat m :: flat.map Val.nat)).wt ≤ 20 * (N + 1) ^ 4 :=
    (wt_list_sublist (List.sublist_cons_self _ _)).trans (ek ▸ wk)
  have wg := wt_encPerm_le g
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wvs := wt_list3_le (vsHAcV s) (encPerm g) (natList (0 :: vsHKeyT ys))
  have evs : (Val.list vs).wt = (Val.list [vsHAcV s, encPerm g, natList (0 :: vsHKeyT ys)]).wt := rfl
  have wP : (Val.list (ys.map fun M => natList (vsHPc M))).wt ≤ 1000 * (N + 1) ^ 4 := by
    have := vs_wt_list_le_of (ys.map fun M => natList (vsHPc M)) (c := 5 * (N + 1) ^ 2) (by
      intro v hv
      obtain ⟨M, -, rfl⟩ := List.mem_map.1 hv
      exact wpc M)
    have hlen : (ys.map fun M => natList (vsHPc M)).length = m := by simp [m]
    rw [hlen] at this
    have : m * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have l1 := wt_list2_le (vsHAcV s) (encPerm g)
  have l2 := wt_list2_le (Val.list [vsHAcV s, encPerm g]) (Val.list (ys.map fun M => natList (vsHPc M)))
  have l3 := wt_list3_le (Val.nat (DD + 1)) (Val.nat m) (Val.list (flat.map Val.nat))
  have wD := wt_nat_le (vsQD s)
  have wDD := wt_nat_le (DD + 1)
  have wDD' := wt_nat_le (GI.Machine.BinOp.eval .mul (vsQD s) (vsQD s))
  have eDD' : GI.Machine.BinOp.eval .mul (vsQD s) (vsQD s) = DD := rfl
  have wmm := wt_nat_le m
  have hDN : vsQD s ≤ N := (Nat.le_mul_self _).trans (by omega)
  have lfl : flat.length ≤ N * N := by omega
  -- the loop costs
  have hT1 : loopModK * ((Val.nat m :: flat.map Val.nat).length + 1) *
      (3 * (Val.list (Val.nat 0 :: Val.nat m :: flat.map Val.nat)).wt + 1) ≤
      1000 * (N + 1) ^ 2 * (61 * (N + 1) ^ 4) := by
    rw [← ek]
    refine Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) ?_) (by omega)
    simp only [List.length_cons, List.length_map]; nlinarith
  have hT2 : loopModK * ((flat.map Val.nat).length + 1) *
      (3 * (Val.list (Val.nat m :: flat.map Val.nat)).wt + 1) ≤ 1000 * (N + 1) ^ 2 * (61 * (N + 1) ^ 4) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) ?_) (by omega)
    simp only [List.length_map]; nlinarith
  have e6 : 1000 * (N + 1) ^ 2 * (61 * (N + 1) ^ 4) = 61000 * (N + 1) ^ 6 := by ring
  have hCh : 10 ^ 8 * (N + 1) ^ 4 * (20 * (N + 1) ^ 4 + (N + 1) ^ 2) ≤ 21 * 10 ^ 8 * (N + 1) ^ 8 := by
    have : 10 ^ 8 * (N + 1) ^ 4 * (20 * (N + 1) ^ 4 + (N + 1) ^ 2) ≤ 10 ^ 8 * (N + 1) ^ 4 * (21 * (N + 1) ^ 4) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : 10 ^ 8 * (N + 1) ^ 4 * (21 * (N + 1) ^ 4) = 21 * 10 ^ 8 * (N + 1) ^ 8 := by ring
    omega
  have hM1 : ys.length * (vsHConjCost Cφ N + 10 ^ 5 * (N + 1) ^ 3) ≤
      (N + 1) * vsHConjCost Cφ N + 10 ^ 5 * (N + 1) ^ 4 := by
    have := Nat.mul_le_mul_right (vsHConjCost Cφ N + 10 ^ 5 * (N + 1) ^ 3) (show ys.length ≤ N + 1 by omega)
    have e : (N + 1) * (vsHConjCost Cφ N + 10 ^ 5 * (N + 1) ^ 3) =
        (N + 1) * vsHConjCost Cφ N + 10 ^ 5 * (N + 1) ^ 4 := by ring
    omega
  have hM2 : mapK * (ys.length + 1) * ((Val.list [Val.list [vsHAcV s, encPerm g],
      Val.list (List.map (fun M => natList (vsHPc M)) ys)]).wt + (Val.list (List.map Val.list xss)).wt + 1) ≤
      1000 * (N + 1) * (10 ^ 4 * (N + 1) ^ 4) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have e5 : 1000 * (N + 1) * (10 ^ 4 * (N + 1) ^ 4) = 10 ^ 7 * (N + 1) ^ 5 := by ring
  have q58 : (N + 1) ^ 5 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have wfl' := hflatW ys' hys'
  have kp1 := wt_list2_le (Val.list [Val.nat 0, Val.nat m]) (Val.list (fl'.map Val.nat))
  have kp2 := wt_list2_le (Val.nat 0) (Val.nat m)
  have w0 := wt_nat_le 0
  have hmDD' : m * (DD + 1) ≤ (N + 1) ^ 2 := by omega
  have hKPa : (Val.list [.list [Val.nat 0, Val.nat m], .list (fl'.map Val.nat)]).wt + m * (DD + 1) +
      (natList (0 :: vsHKeyT ys')).wt + 1 ≤ 200 * (N + 1) ^ 4 := by
    have p4 : N + 1 ≤ (N + 1) ^ 4 := by omega
    have hr : (Val.list (fl'.map Val.nat)).wt ≤ 20 * (N + 1) ^ 4 := wfl'
    have hz : (natList (0 :: vsHKeyT ys')).wt ≤ 20 * (N + 1) ^ 4 := wk'
    have hmD : m * (DD + 1) ≤ (N + 1) ^ 2 := hmDD'
    clear_value fl'
    omega
  have hKP : KP ≤ 1000 * (N + 1) ^ 2 * (200 * (N + 1) ^ 4) := by
    simp only [KP]
    exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) hKPa
  have e6' : 1000 * (N + 1) ^ 2 * (200 * (N + 1) ^ 4) = 2 * 10 ^ 5 * (N + 1) ^ 6 := by ring
  clear_value KP
  unfold vsHConjTCost
  have lk : loopModK = 1000 := rfl
  have mk : mapK = 1000 := rfl
  linarith

end GI.Impl
