import Workspace.Impl.AggPre

/-!
# The pointwise stabilizer on a list of label pairs, in `GI.Lang`

`graphStabL` works on the same format as `graphPre`: a list of label pairs `[a, b]`. It encodes
the pairs, makes their group value, calls the cited task **PointwiseStab** on the positions
`X` of the first part, and splits the output back into pairs. The output pairs generate the
pairs of the input group whose first part fixes every point of `X` (`graphStabL_spec`).
`pairGens_of_pre` and `pairGens_of_stab` turn the results of `graphPre_spec` and
`graphStabL_spec` into statements about graph forms.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens sumToFin pointwiseStab PointwiseStab)

variable {k q : ℕ}

/-- The pairs whose first part fixes every point of `X`. -/
def fixFst (k q : ℕ) (X : List (Fin k)) : Subgroup (Perm (Fin k) × Perm (Fin q)) where
  carrier := {p | ∀ i ∈ X, p.1 i = i}
  one_mem' := fun i _ => rfl
  mul_mem' := fun {a b} ha hb i hi => by
    show a.1 (b.1 i) = i
    rw [hb i hi, ha i hi]
  inv_mem' := fun {a} ha i hi => by
    show a.1⁻¹ i = i
    rw [Perm.inv_eq_iff_eq, ha i hi]

theorem encPts_eq (X : List (Fin k)) : encPts X = .list (X.map fun i : Fin k => Val.nat i.val) := by
  unfold encPts
  congr 1
  induction X with
  | nil => rfl
  | cons x X ih => simp_all

theorem encPts_leftPts (X : List (Fin k)) : encPts (leftPts (q := q) X) = encPts X := by
  unfold encPts leftPts
  congr 1
  induction X with
  | nil => rfl
  | cons x X ih => simp_all

/-- On `[[k, q], pairs, X]`; the environment after the `let`s is `[input, encoded list,
group value, output generators]`. -/
def graphStabEntry (b jp : ℕ) : Expr :=
  let kE := Expr.get (arg 0) (.nat 0)
  let qE := Expr.get (arg 0) (.nat 1)
  .letE (.call (b + 1) (mk2 kE (arg 1)))
  (.letE (.call (b + 14) (mk2 (.arith .add kE qE) (.var 1)))
  (.letE (.prim jp (mk2 (.var 2) (arg 2)))
  (.call (b + 21) (mk2 (mk2 kE (mk2 (.call (b + 15) kE) (.call (b + 15) qE))) (.var 3)))))

/-- The stabilizer module at base `b`, with the cited primitive at `jp`. -/
def graphStabFuns (b jp : ℕ) : List Expr :=
  [graphStabEntry b jp] ++ pEncMapFuns (b + 1) ++ mkGroupFuns (b + 14) ++ pSplitMapFuns (b + 21)

/-- The size parameter of a stabilizer call. -/
def stabM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) (X : List (Fin k)) : ℕ :=
  k + q + ps.length + X.length + 2

/-- The cost constant of the stabilizer module. -/
def graphStabK : ℕ := 10 ^ 14

/-- **The pointwise stabilizer on a list of pairs.** -/
theorem graphStabL_spec (h : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (graphStabFuns b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim h))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (X : List (Fin k)) :
    FunAll P b (.list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X])
      (fun w c => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixFst k q X ∧
        c ≤ (pointwiseStabPrim h).bound (.list [encGroup (ps.map encPair), encPts X]) +
          graphStabK * stabM k q ps X ^ 8) := by
  have hentry : P.funs[b]? = some (graphStabEntry b jp) := by
    simpa using (hb.block 0 (gs := [graphStabEntry b jp]) (by rfl)).single
  have hen : P.HasAt (b + 1) (pEncMapFuns (b + 1)) := hb.block 1 (by rfl)
  have hmk : P.HasAt (b + 14) (mkGroupFuns (b + 14)) := hb.block 14 (by rfl)
  have hrg : P.HasAt (b + 15) (rangeFuns (b + 15)) := hmk.block 1 (by rfl)
  have hsp : P.HasAt (b + 21) (pSplitMapFuns (b + 21)) := hb.block 21 (by rfl)
  set A : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X] with hA
  set E : Val := .list (ps.map fun p => encPerm (encPair p)) with hE
  set GD : Val := encGroup (ps.map encPair) with hGD
  have gk : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 0)) (.nat k) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      encPts X]) (rest := rest) (j := 0) rfl) (Det.nat 0) (v := .nat k) rfl
  have gq : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 1)) (.nat q) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      encPts X]) (rest := rest) (j := 0) rfl) (Det.nat 1) (v := .nat q) rfl
  have d1 := Det.call (Det.mk2 (gk []) (Det.arg' (P := P) (vs := [.list [.nat k, .nat q],
    .list (ps.map pairV), encPts X]) (rest := []) (j := 1) rfl)) (pEncMap_spec hen ps)
  have hG2 := mkGroup_spec hmk (ps.map encPair)
  have eE : Val.list ((ps.map encPair).map encPerm) = E := by simp [hE]
  rw [eE] at hG2
  have d2 := Det.call (Det.mk2 (Det.arith' (op := .add) (gk [E]) (gq [E]) (z := k + q) rfl)
    (Det.var' (P := P) (env := [A, E]) (i := 1) rfl)) hG2
  have dI := Det.mk2 (Det.var' (P := P) (env := [A, E, GD]) (i := 2) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), encPts X])
      (rest := [E, GD]) (j := 2) rfl)
  have hGv : GroupVal (k + q) GD (gens (ps.map encPair)) := ⟨ps.map encPair, rfl, rfl⟩
  have hspec := pointwiseStabPrim_spec h hGv (leftPts X)
  rw [encPts_leftPts] at hspec
  have hP := EvalAll.prim_spec_le hj dI hspec
    fun w hw => GensVal.wt_le hw
  refine FunAll.intro hentry (EvalAll.letE d1 fun _ _ h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun _ _ h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine EvalAll.letE hP fun w3 c3 h3 => ?_
  obtain ⟨⟨hs, rfl, hl, hgen⟩, hc3⟩ := h3
  have hsub : pointwiseStab (gens (ps.map encPair)) (leftPts X) =
      (Subgroup.closure {p | p ∈ ps} ⊓ fixFst k q X).map (encPairHom k q) := by
    ext x
    rw [mem_pointwiseStab_pairs]
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨p, hp, hX, rfl⟩
      exact ⟨p, ⟨hp, hX⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hX⟩, rfl⟩
      exact ⟨p, hp, hX, rfl⟩
  obtain ⟨qs, rfl, hqs⟩ := exists_pairs_of_gens (hgen.trans hsub)
  set H : Val := .list ((qs.map encPair).map encPerm) with hH
  have hsplit := pSplitMap_spec hsp qs
  have eH : Val.list (qs.map fun p => encPerm (encPair p)) = H := by simp [hH]
  rw [eH] at hsplit
  have dr1 := Det.call (gk [E, GD, H]) (range_det hrg k)
  have dr2 := Det.call (gq [E, GD, H]) (range_det hrg q)
  have dctx := Det.mk2 (gk [E, GD, H]) (Det.mk2 dr1 dr2)
  have ectx : Val.list [.nat k, .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]] =
      pSplitCtx k q := rfl
  rw [ectx] at dctx
  have d4 := Det.call (Det.mk2 dctx (Det.var' (P := P) (env := [A, E, GD, H]) (i := 3) rfl))
    hsplit
  have hlq : qs.length ≤ (k + q) ^ 2 := by
    have e : (qs.map (encPair (k := k) (q := q))).length = qs.length := List.length_map _
    have hl' : (qs.map (encPair (k := k) (q := q))).length ≤ (k + q) ^ 2 := hl
    omega
  refine d4.post fun c hc => ⟨qs, rfl, hlq, hqs, ?_⟩
  -- the cost
  set M := stabM k q ps X with hM
  have hMd : k + q + ps.length + X.length + 2 = M := rfl
  have m2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have m3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have m4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have m6 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have m8 : M ^ 6 ≤ M ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have sq : ∀ x, x ≤ M → x ^ 2 ≤ M ^ 2 := fun x hx => Nat.pow_le_pow_left hx 2
  have pw : ∀ x n, x ≤ M → x ^ n ≤ M ^ n := fun x n hx => Nat.pow_le_pow_left hx n
  have bps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
    have := wt_pairList_le ps
    have h3 := pw (pM k q ps) 3 (by unfold pM; omega)
    omega
  have bX : (encPts X).wt ≤ 3 * M ^ 2 + 4 := by
    have h1 := wt_list_map_le X (fun i : Fin k => Val.nat i.val) (W := k + 2) fun i _ => by
      show (Val.nat (i : ℕ)).wt ≤ k + 2; have := wt_nat_le (i : ℕ); have := i.isLt; omega
    have h2 : X.length * (2 * (k + 2) + 1) ≤ M * (3 * M) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : M * (3 * M) = 3 * M ^ 2 := by ring
    rw [encPts_eq]
    omega
  have bkq := wt_list2_le (.nat k) (.nat q)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wkq := wt_nat_le (k + q)
  have bA := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (encPts X)
  have bA1 := wt_list2_le (.nat k) (.list (ps.map pairV))
  have bE : E.wt ≤ 9 * M ^ 3 + 4 := by
    have h1 := wt_list_map_le ps (fun p => encPerm (encPair p))
      (W := 4 * (k + q + 1) ^ 2) fun p _ => wt_encPerm_le _
    have h2 : ps.length * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := sq (k + q + 1) (by omega); omega)
    have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
    rw [hE]; omega
  have bE1 := wt_list2_le (.nat (k + q)) E
  have cE : ps.length * pEncCost k q ≤ natStepK * M ^ 4 := by
    have h2 : ps.length * pEncCost k q ≤ M * (natStepK * M ^ 3) :=
      Nat.mul_le_mul (by omega) (by
        show natStepK * (k + q + 1) ^ 3 ≤ _; exact Nat.mul_le_mul_left _ (pw _ 3 (by omega)))
    have e2 : M * (natStepK * M ^ 3) = natStepK * M ^ 4 := by ring
    omega
  have cE2 : mapK * (ps.length + 1) * ((Val.list [.nat k, .list (ps.map pairV)]).wt + E.wt + 1)
      ≤ mapK * M * (1000 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have sGD2 : ((ps.map encPair).length + 2) * (k + q + 1) ≤ M ^ 2 := by
    have := Nat.mul_le_mul (show (ps.map encPair).length + 2 ≤ M by simp; omega)
      (show k + q + 1 ≤ M by omega)
    have e : M * M = M ^ 2 := by ring
    omega
  have bGD : GD.wt ≤ 40 * M ^ 4 := by
    have h1 := wt_encGroup_le (ps.map encPair)
    have h2 := Nat.pow_le_pow_left sGD2 2
    have e : (M ^ 2) ^ 2 = M ^ 4 := by ring
    rw [hGD]; omega
  have cGD : mkGroupK * (((ps.map encPair).length + 2) * (k + q + 1)) ^ 3 ≤ mkGroupK * M ^ 6 := by
    have h2 := Nat.pow_le_pow_left sGD2 3
    have e : (M ^ 2) ^ 3 = M ^ 6 := by ring
    exact Nat.mul_le_mul_left _ (e ▸ h2)
  have bI := wt_list2_le GD (encPts X)
  have bIn : 13 * (k + q + 1) ^ 6 ≤ 13 * M ^ 6 := Nat.mul_le_mul_left _ (pw _ 6 (by omega))
  have hq2 : qs.length ≤ M ^ 2 := le_trans hlq (sq _ (by omega))
  have bH : H.wt ≤ 9 * M ^ 4 + 4 := by
    have h1 := wt_list_map_le (qs.map encPair) encPerm (W := 4 * (k + q + 1) ^ 2)
      fun p _ => wt_encPerm_le p
    have h2 : (qs.map encPair).length * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ M ^ 2 * (9 * M ^ 2) :=
      Nat.mul_le_mul (by simp; omega) (by have := sq (k + q + 1) (by omega); omega)
    have h3 : M ^ 2 * (9 * M ^ 2) = 9 * M ^ 4 := by ring
    rw [hH]; omega
  have bQ : (Val.list (qs.map pairV)).wt ≤ 400 * M ^ 6 := by
    have h1 := wt_pairList_le qs
    have h2 : pM k q qs ≤ 2 * M ^ 2 := by unfold pM; omega
    have h3 := Nat.pow_le_pow_left h2 3
    have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
    omega
  have b1k := wt_encPerm_le (1 : Perm (Fin k))
  have b1q := wt_encPerm_le (1 : Perm (Fin q))
  have b11 := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin q)))
  have bC := wt_list2_le (.nat k) (.list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))])
  have eC : (pSplitCtx k q).wt =
      (Val.list [.nat k, .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]]).wt := rfl
  have bCH := wt_list2_le (pSplitCtx k q) H
  have sk := sq (k + 1) (by omega)
  have sq' := sq (q + 1) (by omega)
  have ck : 8000 * (k + 1) ^ 3 ≤ 8000 * M ^ 3 := Nat.mul_le_mul_left _ (pw _ 3 (by omega))
  have cq : 8000 * (q + 1) ^ 3 ≤ 8000 * M ^ 3 := Nat.mul_le_mul_left _ (pw _ 3 (by omega))
  have cS : qs.length * pSplitCost k q ≤ 10 ^ 11 * M ^ 8 := by
    have h1 : pSplitCost k q ≤ 10 ^ 11 * M ^ 6 :=
      Nat.mul_le_mul_left _ (pw _ 6 (by omega))
    have h2 := Nat.mul_le_mul hq2 h1
    have e : M ^ 2 * (10 ^ 11 * M ^ 6) = 10 ^ 11 * M ^ 8 := by ring
    omega
  have cS2 : mapK * (qs.length + 1) * ((Val.list [pSplitCtx k q, H]).wt +
      (Val.list (qs.map pairV)).wt + 1) ≤ mapK * (2 * M ^ 2) * (1000 * M ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : mapK * M * (1000 * M ^ 3) = 10 ^ 6 * M ^ 4 := by simp only [mapK]; ring
  have e2 : mapK * (2 * M ^ 2) * (1000 * M ^ 6) = 2 * 10 ^ 6 * M ^ 8 := by simp only [mapK]; ring
  rw [← hE] at hc1
  rw [← hGD] at hc2
  simp only [graphStabK, natStepK, mkGroupK] at *
  omega

/-! ### Back to graph forms -/

section Graph

variable {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

theorem pairGens_of_pre {A : Subgroup (Perm Ω)} {ps qs : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L A ps) {ms : List (Perm (Fin L.q))}
    (h : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ (gens ms).comap (MonoidHom.snd _ _)) :
    PairGens e L (A ⊓ labPre (L := L) (gens ms)) qs := by
  unfold PairGens at *
  rw [h, hps, graphOf_inf_labPre]

theorem pairGens_of_stab {A : Subgroup (Perm Ω)} {ps qs : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L A ps) {X : List (Fin k)}
    (h : Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixFst k L.q X) :
    PairGens e L (A ⊓ fixPos (e := e) X) qs := by
  unfold PairGens at *
  rw [h, hps, graphOf_inf_fixPos]
  congr 1

end Graph

end GI.Impl
