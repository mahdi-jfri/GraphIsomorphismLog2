module

public import Workspace.Impl.VsPDim
public import Workspace.Impl.VsPDer

@[expose] public section

/-!
# The descent to a least spin

Start from `y := x₂`. In each round, list the words of the kept basis of the spin of `y`
(`vsPEnum`), and look for a word `z` outside `L` whose spin has a smaller dimension. If there is
one, set `y := z`. After enough rounds `y` is stable: no listed word outside `L` has a smaller
spin dimension. This is the input of `vsP_min`.

* `vsPDPredE`: on `[[Q, d], z]`, is `z ∉ L` with `dim z < d` (`vsPDPred_spec`);
* `vsPDsStepE`: one round (`vsPDsStep_spec`); `vsPDescE`: `k` rounds (`vsPDesc_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- The context inside the orbit data `Q`. -/
def vsPQCtx : Expr := .get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0)

/-- On `[[Q, d], z]`: `1` if `z ∉ L` and the spin of `z` has dimension below `d`. -/
def vsPDPredE (nt dim : ℕ) : Expr :=
  .ite (.call nt (mk2 vsPQCtx (arg 1)))
    (.arith .lt (.length (.get (.call dim (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.nat 1)))
      (.get (arg 0) (.nat 1)))
    (.nat 0)

/-- The function indices of the dimension program and its parts. -/
structure VsPDX where
  (o : VsPOX) (dim bas g ins nt inl : ℕ)

/-- The layout of the dimension program and the membership test. -/
structure VsPDLay (P : Program) (x : VsPDX) : Prop where
  L : VsPOLay P x.o
  hdim : P.funs[x.dim]? = some (vsPDimE x.o.orb x.bas)
  hb : P.HasAt x.bas (foldlFuns x.bas x.g)
  hg : P.funs[x.g]? = some (vsPGStepE x.ins)
  hins : P.HasAt x.ins (vsInsertFuns x.ins)
  hnt : P.funs[x.nt]? = some (vsPNotInE x.inl)
  hinl : P.HasAt x.inl (vsPInLPFuns x.inl x.o.phi)

/-- The cost of the test. -/
def vsPDPredCost (Cφ N W : ℕ) : ℕ :=
  vsPInLPCost Cφ N W + vsPDimCost Cφ N W + 100 * W + 10 ^ 4 * (N + 1) ^ 3

/-- The value of the test. -/
noncomputable def vsPDQ (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (Zp : List (List (List ℕ))) (gs : List (Perm (Fin I.n))) (cap : ℕ)
    (hs1 : List (Perm (Fin I.n))) (F r d : ℕ) (z : Perm (Fin I.n)) : Bool :=
  !vsPInLB I ws' cs rows z && decide ((vsPDim I ws' cs Zp gs cap hs1 F r z).length < d)

set_option maxHeartbeats 1000000 in
theorem vsPDPred_spec {P : Program} {f : ℕ} {x : VsPDX} (hf : P.funs[f]? = some (vsPDPredE x.nt x.dim))
    (L : VsPDLay P x) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    (D : VsPOD I N W ws' cs rows hs gs Zp cap hs1 F r) {d : ℕ} (hd : d ≤ N)
    {z : Perm (Fin I.n)} (hz : z ∈ gens I.gs)
    (hfit : ∀ p ∈ vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z,
      (∀ a ∈ p.2, a < r) ∧ p.2.length = gs.length) :
    FunDet P f (.list [.list [vsPQ I ws' cs rows hs gs Zp cap hs1 F r, .nat d], encPerm z])
      (boolVal (vsPDQ I ws' cs rows Zp gs cap hs1 F r d z)) (vsPDPredCost Cφ N W) := by
  have hn := D.H.n
  set Q := vsPQ I ws' cs rows hs gs Zp cap hs1 F r
  set pc := vsPPc I ws' cs rows hs gs Zp
  set C := vsPCtx I ws' cs rows hs
  set vs := [Val.list [Q, .nat d], encPerm z]
  have a0 : Det P [Val.list vs] (arg 0) (.list [Q, .nat d]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dQ : Det P [Val.list vs] (.get (arg 0) (.nat 0))
      (.list [pc, .nat cap, .list (hs1.map encPerm), .nat F, .nat r]) _ :=
    Det.get' a0 (Det.nat 0) rfl
  have dpc : Det P [Val.list vs] (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.list [C, .list (gs.map encPerm), .list (Zp.map vsWVs)]) _ :=
    Det.get' dQ (Det.nat 0) rfl
  have dC : Det P [Val.list vs] vsPQCtx C _ := Det.get' dpc (Det.nat 0) rfl
  have dnt := Det.call (Det.mk2 dC a1) (vsPNotIn_spec L.hnt L.hinl hphi D.H hz)
  rw [vsPQN_enc] at dnt
  have ddim := Det.call (Det.mk2 (Det.get' a0 (Det.nat 0) rfl) a1)
    (vsPDim_spec L.hdim L.L L.hb L.hg L.hins hphi D hz hfit)
  have dlen := Det.length (Det.get' ddim (Det.nat 1) rfl)
  rw [List.length_map] at dlen
  have dlt := Det.arith' (op := .lt) dlen (Det.get' a0 (Det.nat 1) rfl) rfl
  have hOl : (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z).length ≤ N :=
    ((vsPOrbit_ok D.hcap1 D.hh hz F).2).trans D.hcap
  have wG := vsPGV_wt_le hn D.hr D.hrN D.hgl hfit hOl
  have hBl : (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.length ≤ N := by
    have := (vsPBasis_take_inv D.hr D.hrN D.hgl hfit
      (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z).length).2.2
    rw [List.take_length] at this; unfold vsPBasis; omega
  have wQ : Q.wt ≤ W := D.hQ
  have wpc : pc.wt ≤ W := D.hpc
  have wC : C.wt ≤ W := D.H.cw
  have wz := (wt_encPerm_le z).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have wd := wt_nat_le d
  have w2 := wt_list2_le Q (.nat d)
  have wvs := wt_list2_le (Val.list [Q, .nat d]) (encPerm z)
  have evs : (Val.list vs).wt = (Val.list [Val.list [Q, .nat d], encPerm z]).wt := rfl
  have eQ : (Val.list [pc, Val.nat cap, Val.list (List.map encPerm hs1), Val.nat F, Val.nat r]).wt =
    Q.wt := rfl
  have epc : (Val.list [C, Val.list (List.map encPerm gs), Val.list (List.map vsWVs Zp)]).wt =
    pc.wt := rfl
  have wb1 := wt_boolVal_le (!vsPInLB I ws' cs rows z)
  have wb2 := wt_boolVal_le (vsPDQ I ws' cs rows Zp gs cap hs1 F r d z)
  have wCz := wt_list2_le C (encPerm z)
  have wQz := wt_list2_le Q (encPerm z)
  have wlt := wt_nat_le (BinOp.eval .lt (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.length d)
  have hlt1 : BinOp.eval .lt (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.length d ≤ 1 := by
    simp only [BinOp.eval]; split_ifs <;> omega
  have wBP := wt_le_wt_list (vs := [.list ((vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).1.map VsRow.val),
      .list ((vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.map encPerm)])
    (v := .list ((vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.map encPerm)) (by simp)
  have eGV : (vsPGV (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z))).wt =
    (Val.list [.list ((vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).1.map VsRow.val),
      .list ((vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.map encPerm)]).wt := rfl
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hv : (if (!vsPInLB I ws' cs rows z).toNat = 0 then Val.nat 0 else
      Val.nat (BinOp.eval .lt (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.length d)) =
      boolVal (vsPDQ I ws' cs rows Zp gs cap hs1 F r d z) := by
    unfold vsPDQ vsPDim
    cases vsPInLB I ws' cs rows z
    · simp only [Bool.not_false, Bool.true_and, Bool.toNat_true, one_ne_zero, if_false, BinOp.eval]
      by_cases h : (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F z)).2.length < d <;>
        simp [h]
    · rfl
  set B := vsPDimCost Cφ N W + 50 * W + 2000 * (N + 1) ^ 3
  have dlt' := dlt.mono (c' := B) (by omega)
  have d0 := (Det.nat (P := P) (env := [Val.list vs]) 0).mono (c' := B) (by
    have := wt_nat_le 0; omega)
  have dite := Det.ite' dnt dlt' d0
  rw [max_self, hv] at dite
  refine FunDet.intro hf (dite.mono ?_)
  have w0 := wt_nat_le 0
  unfold vsPDPredCost
  omega

/-! ### One round -/

/-- The function indices of the enumeration. -/
structure VsPEX where
  (en fo st mpM mid mpI it pow comp cat rng : ℕ)

/-- The layout of the enumeration. -/
structure VsPELay (P : Program) (x : VsPEX) : Prop where
  hf : P.funs[x.en]? = some (vsPEnumE x.fo x.rng)
  hfo : P.HasAt x.fo (foldlFuns x.fo x.st)
  hst : P.funs[x.st]? = some (vsPEStepE x.mpM x.cat)
  hmpM : P.HasAt x.mpM (mapFuns x.mpM x.mid)
  hmid : P.funs[x.mid]? = some (vsPEMidE x.mpI)
  hmp : P.HasAt x.mpI (mapFuns x.mpI x.it)
  hit : P.funs[x.it]? = some (vsPEItemE x.pow x.comp)
  hpow : P.HasAt x.pow (vsPPowFuns x.pow)
  hcomp : P.HasAt x.comp (composeFuns x.comp)
  hcat : P.HasAt x.cat (vsWFlatFuns x.cat)
  hrng : P.HasAt x.rng (rangeFuns x.rng)

/-- The test on values. -/
noncomputable def vsPDQV (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (Zp : List (List (List ℕ))) (gs : List (Perm (Fin I.n))) (cap : ℕ)
    (hs1 : List (Perm (Fin I.n))) (F r d : ℕ) (v : Val) : Bool := by
  classical exact decide (∃ z : Perm (Fin I.n), v = encPerm z ∧
    vsPDQ I ws' cs rows Zp gs cap hs1 F r d z = true)

theorem vsPDQV_enc (ws' cs : List (List ℕ)) (rows : List VsRow)
    (Zp : List (List (List ℕ))) (gs : List (Perm (Fin I.n))) (cap : ℕ)
    (hs1 : List (Perm (Fin I.n))) (F r d : ℕ) (z : Perm (Fin I.n)) :
    vsPDQV I ws' cs rows Zp gs cap hs1 F r d (encPerm z) = vsPDQ I ws' cs rows Zp gs cap hs1 F r d z := by
  unfold vsPDQV
  cases h : vsPDQ I ws' cs rows Zp gs cap hs1 F r d z
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro z' e h'
    rw [← encPerm_injective e, h] at h'; exact Bool.false_ne_true h'
  · simp only [decide_eq_true_eq]; exact ⟨z, rfl, h⟩

/-- One round of the descent. -/
noncomputable def vsPDsStepF (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (Zp : List (List (List ℕ))) (gs : List (Perm (Fin I.n))) (cap : ℕ)
    (hs1 : List (Perm (Fin I.n))) (F r : ℕ) (y : Perm (Fin I.n)) : Perm (Fin I.n) :=
  let E := vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)
  let q := vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length
  if h : E.findIdx q < E.length then E[E.findIdx q] else y

/-- On `[Q, i, y]`: one round. -/
def vsPDsStepE (dim en fnd : ℕ) : Expr :=
  .letE (.call dim (mk2 (arg 0) (arg 2)))
    (.letE (.call en (mk3 (.get (arg 0) (.nat 4))
        (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 6)) (.get (.var 1) (.nat 1))))
      (.letE (.call fnd (mk2 (mk2 (arg 0) (.length (.get (.var 1) (.nat 1)))) (.var 2)))
        (.ite (.arith .lt (.var 3) (.length (.var 2))) (.get (.var 2) (.var 3)) (arg 2))))

/-- What a round needs at `y`: `y` and the listed words are in `⟨I.gs⟩` with fitting orbit keys,
and the list is short. -/
def VsPDOK (I : VecStabInst) (ws' cs : List (List ℕ)) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (cap : ℕ) (hs1 : List (Perm (Fin I.n))) (F r N : ℕ)
    (y : Perm (Fin I.n)) : Prop :=
  y ∈ gens I.gs ∧ (∀ p ∈ vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y,
      (∀ a ∈ p.2, a < r) ∧ p.2.length = gs.length) ∧
    r ^ (vsPDim I ws' cs Zp gs cap hs1 F r y).length ≤ N

/-- The cost of a round. -/
def vsPDsStepCost (Cφ N W : ℕ) : ℕ :=
  vsPDimCost Cφ N W + vsPEnumCost N + (N + 1) * vsPDPredCost Cφ N W +
    10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3)

theorem vsP_findIdx_map {α β : Type*} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).findIdx p = l.findIdx (p ∘ f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.findIdx_cons, ih]

set_option maxHeartbeats 4000000 in
theorem vsPDsStep_spec {P : Program} {f fnd pr : ℕ} {x : VsPDX} {e : VsPEX}
    (hf : P.funs[f]? = some (vsPDsStepE x.dim e.en fnd)) (L : VsPDLay P x) (LE : VsPELay P e)
    (hfnd : P.HasAt fnd (findFuns fnd pr)) (hpr : P.funs[pr]? = some (vsPDPredE x.nt x.dim))
    {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    (D : VsPOD I N W ws' cs rows hs gs Zp cap hs1 F r) {y : Perm (Fin I.n)}
    (hy : VsPDOK I ws' cs Zp gs cap hs1 F r N y)
    (hE : ∀ z ∈ vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y), VsPDOK I ws' cs Zp gs cap hs1 F r N z)
    {i : ℕ} (hi : i ≤ N) :
    FunDet P f (.list [vsPQ I ws' cs rows hs gs Zp cap hs1 F r, .nat i, encPerm y])
      (encPerm (vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y)) (vsPDsStepCost Cφ N W) := by
  have hn := D.H.n
  obtain ⟨hyg, hfy, hry⟩ := hy
  set O := vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y
  set B := vsPDim I ws' cs Zp gs cap hs1 F r y with hB
  set E := vsPEnum r B with hEdef
  set Q := vsPQ I ws' cs rows hs gs Zp cap hs1 F r
  set pc := vsPPc I ws' cs rows hs gs Zp
  set C := vsPCtx I ws' cs rows hs
  set GV := vsPGV (vsPBasis r O)
  set vs := [Q, Val.nat i, encPerm y]
  have hOl : O.length ≤ N := ((vsPOrbit_ok D.hcap1 D.hh hyg F).2).trans D.hcap
  have hBl : B.length ≤ N := by
    have := (vsPBasis_take_inv D.hr D.hrN D.hgl hfy O.length).2.2
    rw [List.take_length] at this; exact this.trans hOl
  have hEl : E.length ≤ N := by rw [hEdef, vsPEnum_length]; exact hry
  -- the dimension
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dD := Det.call (Det.mk2 a0 a2) (vsPDim_spec L.hdim L.L L.hb L.hg L.hins hphi D hyg hfy)
  -- the enumeration
  have b0 : Det P [Val.list vs, GV] (arg 0) Q _ :=
    Det.arg' (P := P) (vs := vs) (rest := [GV]) (j := 0) rfl
  have bv := Det.var' (P := P) (env := [Val.list vs, GV]) (i := 1) rfl
  have bB : Det P [Val.list vs, GV] (.get (.var 1) (.nat 1)) (.list (B.map encPerm)) _ :=
    Det.get' bv (Det.nat 1) rfl
  have br : Det P [Val.list vs, GV] (.get (arg 0) (.nat 4)) (.nat r) _ :=
    Det.get' b0 (Det.nat 4) rfl
  have bn : Det P [Val.list vs, GV] (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 6))
      (.nat I.n) _ :=
    Det.get' (Det.get' (Det.get' b0 (Det.nat 0) (v := pc) rfl) (Det.nat 0) (v := C) rfl)
      (Det.nat 6) rfl
  have dE := Det.call (Det.mk3 br bn bB) (vsPEnum_spec LE.hf LE.hfo LE.hst LE.hmpM LE.hmid LE.hmp
    LE.hit LE.hpow LE.hcomp LE.hcat LE.hrng hn D.hr D.hrN hry hBl)
  -- the search
  have c0 : Det P [Val.list vs, GV, (Val.list (E.map encPerm))] (arg 0) Q _ :=
    Det.arg' (P := P) (vs := vs) (rest := [GV, (Val.list (E.map encPerm))]) (j := 0) rfl
  have cv := Det.var' (P := P) (env := [Val.list vs, GV, (Val.list (E.map encPerm))]) (i := 1) rfl
  have cB : Det P [Val.list vs, GV, (Val.list (E.map encPerm))] (.get (.var 1) (.nat 1)) (.list (B.map encPerm)) _ :=
    Det.get' cv (Det.nat 1) rfl
  have cl := Det.length cB
  rw [List.length_map] at cl
  have c2 := Det.var' (P := P) (env := [Val.list vs, GV, (Val.list (E.map encPerm))]) (i := 2) rfl
  have hpred : ∀ v ∈ E.map encPerm, FunDet P pr (.list [.list [Q, .nat B.length], v])
      (boolVal (vsPDQV I ws' cs rows Zp gs cap hs1 F r B.length v)) (vsPDPredCost Cφ N W) := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
    obtain ⟨hzg, hzf, -⟩ := hE z hz
    rw [vsPDQV_enc]
    exact vsPDPred_spec hpr L hphi D hBl hzg hzf
  have hfind := find_spec hfnd hpred
  set X := N * vsPDPredCost Cφ N W + loopModK * (N + 1) *
    ((Val.list [.list [Q, .nat B.length], (Val.list (E.map encPerm))]).wt + 2 * N + 3)
  have hF' : FunAll P fnd (.list [.list [Q, .nat B.length], (Val.list (E.map encPerm))]) (fun w c =>
      w = .nat ((E.map encPerm).findIdx (vsPDQV I ws' cs rows Zp gs cap hs1 F r B.length)) ∧
      c ≤ X) := by
    refine hfind.mono fun w c h => ⟨h.1, ?_⟩
    have h2 := h.2
    have e1 : ((E.map encPerm).map (fun _ => vsPDPredCost Cφ N W)).sum =
        E.length * vsPDPredCost Cφ N W := by
      rw [List.map_map]
      have : ((fun _ => vsPDPredCost Cφ N W) ∘ encPerm : Perm (Fin I.n) → ℕ) =
        fun _ => vsPDPredCost Cφ N W := rfl
      rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
    rw [e1] at h2
    simp only [List.length_map] at h2
    have h4 := Nat.mul_le_mul_right (vsPDPredCost Cφ N W) hEl
    have h3 : loopModK * (E.length + 1) * ((Val.list [.list [Q, .nat B.length], (Val.list (E.map encPerm))]).wt +
        2 * E.length + 3) ≤ loopModK * (N + 1) *
        ((Val.list [.list [Q, .nat B.length], (Val.list (E.map encPerm))]).wt + 2 * N + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega
  have dF := Det.call (Det.mk2 (Det.mk2 c0 cl) c2) hF'
  have hj : (E.map encPerm).findIdx (vsPDQV I ws' cs rows Zp gs cap hs1 F r B.length) =
      E.findIdx (vsPDQ I ws' cs rows Zp gs cap hs1 F r B.length) := by
    rw [vsP_findIdx_map]; congr 1; funext z; exact vsPDQV_enc ws' cs rows Zp gs cap hs1 F r _ z
  rw [hj] at dF
  set j := E.findIdx (vsPDQ I ws' cs rows Zp gs cap hs1 F r B.length) with hjdef
  have hjE : j ≤ E.length := List.findIdx_le_length
  set E3 := [Val.list vs, GV, Val.list (E.map encPerm), Val.nat j]
  have t3 := Det.var' (P := P) (env := E3) (i := 3) rfl
  have t2 := Det.var' (P := P) (env := E3) (i := 2) rfl
  have tl := Det.length t2
  have tt := Det.arith' (op := .lt) t3 tl rfl
  set V := encPerm (vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y)
  have hval : vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y =
      if h : j < E.length then E[j] else y := rfl
  have wy := (wt_encPerm_le y).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have wV := (wt_encPerm_le (vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have wV' : V.wt ≤ 4 * (N + 1) ^ 2 := wV
  have wEl := vsP_wt_perms hn E (by omega)
  have wj := wt_nat_le j
  set B0 := 2 * (Val.list vs).wt + 20 * (N + 1) ^ 3 + 8 * (N + 1) ^ 2 + 2 * N + 20
  have dI := Det.ite (v := V) tt (ct := B0) (ce := B0)
    (fun hx => by
      have hlt : j < E.length := by
        simp only [BinOp.eval, List.length_map] at hx; split_ifs at hx with h <;> omega
      have hV : V = encPerm E[j] := by
        show encPerm (vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y) = _; rw [hval, dif_pos hlt]
      have dg := Det.get' t2 t3 (show (E.map encPerm)[j]? = some V by
        rw [hV, List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl)
      refine dg.mono ?_
      have := wt_nat_le j
      omega)
    (fun hx => by
      have hge : ¬ j < E.length := by
        simp only [BinOp.eval, List.length_map] at hx; split_ifs at hx with h <;> omega
      have hV : V = encPerm y := by
        show encPerm (vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y) = _; rw [hval, dif_neg hge]
      rw [hV]
      exact (Det.arg' (P := P) (vs := vs) (rest := [GV, Val.list (E.map encPerm), Val.nat j])
        (j := 2) rfl).mono (by omega))
  rw [max_self] at dI
  have dAll := Det.letE dD (Det.letE dE (Det.letE dF dI))
  refine FunDet.intro hf (dAll.mono ?_)
  -- weights
  have wQ : Q.wt ≤ W := D.hQ
  have wpc : pc.wt ≤ W := D.hpc
  have wC : C.wt ≤ W := D.H.cw
  have eQ : (Val.list [pc, Val.nat cap, Val.list (List.map encPerm hs1), Val.nat F, Val.nat r]).wt =
    Q.wt := rfl
  have epc : (Val.list [C, Val.list (List.map encPerm gs), Val.list (List.map vsWVs Zp)]).wt =
    pc.wt := rfl
  have wGV : GV.wt ≤ 300 * (N + 1) ^ 3 := vsPGV_wt_le hn D.hr D.hrN D.hgl hfy hOl
  have wBl : (Val.list (B.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := vsP_wt_perms hn B (by omega)
  have wi := wt_nat_le i
  have wvs := wt_list3_le Q (Val.nat i) (encPerm y)
  have evs : (Val.list vs).wt = (Val.list [Q, Val.nat i, encPerm y]).wt := rfl
  have wQy := wt_list2_le Q (encPerm y)
  have wrn := wt_list3_le (Val.nat r) (Val.nat I.n) (Val.list (B.map encPerm))
  have wr := wt_nat_le r
  have wnn := wt_nat_le I.n
  have wd := wt_nat_le B.length
  have wQd := wt_list2_le Q (Val.nat B.length)
  have wF2 := wt_list2_le (Val.list [Q, Val.nat B.length]) (Val.list (E.map encPerm))
  have wlt := wt_nat_le (BinOp.eval .lt j (E.map encPerm).length)
  have hlt1 : BinOp.eval .lt j (E.map encPerm).length ≤ 1 := by
    simp only [BinOp.eval]; split_ifs <;> omega
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  set Y := (N + 1) * (W + 100 * (N + 1) ^ 3)
  have hY1 : W + 100 * (N + 1) ^ 3 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hA : (Val.list [Val.list [Q, Val.nat B.length], Val.list (E.map encPerm)]).wt + 2 * N + 3 ≤
      4 * (W + 100 * (N + 1) ^ 3) := by omega
  have hX2 : loopModK * (N + 1) *
      ((Val.list [Val.list [Q, Val.nat B.length], Val.list (E.map encPerm)]).wt + 2 * N + 3) ≤
      4000 * Y := by
    have := Nat.mul_le_mul_left (N + 1) hA
    have e : (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) = 4 * Y := by simp only [Y]; ring
    rw [mul_assoc]
    calc loopModK * ((N + 1) * ((Val.list [Val.list [Q, Val.nat B.length],
          Val.list (E.map encPerm)]).wt + 2 * N + 3)) ≤ loopModK * (4 * Y) :=
          Nat.mul_le_mul_left _ (e ▸ this)
      _ = 4000 * Y := by unfold loopModK; ring
  have hNP : N * vsPDPredCost Cφ N W ≤ (N + 1) * vsPDPredCost Cφ N W :=
    Nat.mul_le_mul_right _ (by omega)
  have wGV' : (vsPGV (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y))).wt ≤
    300 * (N + 1) ^ 3 := wGV
  have wEl' : (Val.list (List.map encPerm (vsPEnum r B))).wt ≤ 20 * (N + 1) ^ 3 := wEl
  have hEl' : (List.map encPerm E).length ≤ N := by rw [List.length_map]; exact hEl
  have eY : 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) = 10 ^ 4 * Y := by rw [mul_assoc]
  have hrN := D.hrN
  unfold vsPDsStepCost
  rw [eY]
  omega

/-! ### The rounds -/

/-- A round that changes `y` lowers a measure, so after more rounds than the measure the value is
stable. -/
theorem vsP_iter_fix {α : Type*} (step : α → α) (D : α → ℕ) (hD : ∀ y, step y ≠ y → D (step y) < D y)
    (y0 : α) : ∀ k, D y0 < k → step (step^[k] y0) = step^[k] y0 := by
  have key : ∀ i, step (step^[i] y0) = step^[i] y0 ∨ D (step^[i] y0) + i ≤ D y0 := by
    intro i
    induction i with
    | zero => right; simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · left; rw [h, h]
      · by_cases hfix : step (step (step^[i] y0)) = step (step^[i] y0)
        · exact Or.inl hfix
        · right
          by_cases h0 : step (step^[i] y0) = step^[i] y0
          · exact absurd (by rw [h0, h0]) hfix
          · have := hD _ h0; omega
  intro k hk
  rcases key k with h | h
  · exact h
  · omega

/-- **A round lowers the dimension** when it changes `y`. -/
theorem vsPDsStepF_lt (ws' cs : List (List ℕ)) (rows : List VsRow) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (cap : ℕ) (hs1 : List (Perm (Fin I.n))) (F r : ℕ)
    (y : Perm (Fin I.n)) (h : vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y ≠ y) :
    (vsPDim I ws' cs Zp gs cap hs1 F r (vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y)).length <
      (vsPDim I ws' cs Zp gs cap hs1 F r y).length := by
  have hval : vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y =
      if h : (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)).findIdx
        (vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length) <
        (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)).length then
        (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y))[_]'h else y := rfl
  by_cases hj : (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)).findIdx
      (vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length) <
      (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)).length
  · rw [hval, dif_pos hj]
    have := List.findIdx_getElem (w := hj)
    unfold vsPDQ at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · rw [hval, dif_neg hj] at h; exact absurd rfl h

/-- **The stable value.** When a round does not change `y`, no listed word outside `L` has a
spin of smaller dimension. -/
theorem vsPDsStepF_fix {ws' cs : List (List ℕ)} {rows : List VsRow} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    {y : Perm (Fin I.n)} (h : vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y = y) :
    ∀ z ∈ vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y), vsPInLB I ws' cs rows z = false →
      (vsPDim I ws' cs Zp gs cap hs1 F r y).length ≤ (vsPDim I ws' cs Zp gs cap hs1 F r z).length := by
  intro z hz hzL
  by_contra hlt
  push Not at hlt
  have hq : vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length z =
      true := by
    unfold vsPDQ; simp [hzL, hlt]
  have hj : (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)).findIdx
      (vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length) <
      (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)).length :=
    List.findIdx_lt_length_of_exists ⟨z, hz, hq⟩
  set E := vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)
  set qq := vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length
  have hval : vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y =
      if h : E.findIdx qq < E.length then E[E.findIdx qq] else y := rfl
  rw [hval, dif_pos hj] at h
  have := List.findIdx_getElem (w := hj)
  rw [h] at this
  unfold qq vsPDQ at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact absurd this.2 (lt_irrefl _)

/-- On `[Q, y0, k]`: `k` rounds from `y0`. -/
def vsPDescE (it : ℕ) : Expr := .call it (mk3 (arg 0) (arg 2) (arg 1))

/-- The cost of the descent. -/
def vsPDescCost (Cφ N W : ℕ) : ℕ := (N + 2) * vsPDsStepCost Cφ N W + 10 ^ 4 * (N + 2) * (W + 100 * (N + 1) ^ 2)

set_option maxHeartbeats 2000000 in
theorem vsPDesc_spec {P : Program} {f it st fnd pr : ℕ} {x : VsPDX} {e : VsPEX}
    (hf : P.funs[f]? = some (vsPDescE it)) (hit : P.HasAt it (iterFuns it st))
    (hst : P.funs[st]? = some (vsPDsStepE x.dim e.en fnd)) (L : VsPDLay P x) (LE : VsPELay P e)
    (hfnd : P.HasAt fnd (findFuns fnd pr)) (hpr : P.funs[pr]? = some (vsPDPredE x.nt x.dim))
    {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    (D : VsPOD I N W ws' cs rows hs gs Zp cap hs1 F r) {Y : Set (Perm (Fin I.n))}
    (hY : ∀ y ∈ Y, VsPDOK I ws' cs Zp gs cap hs1 F r N y ∧
      ∀ z ∈ vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y), z ∈ Y)
    {y0 : Perm (Fin I.n)} (hy0 : y0 ∈ Y) {k : ℕ} (hk : k ≤ N + 1) :
    FunDet P f (.list [vsPQ I ws' cs rows hs gs Zp cap hs1 F r, encPerm y0, .nat k])
      (encPerm ((vsPDsStepF I ws' cs rows Zp gs cap hs1 F r)^[k] y0)) (vsPDescCost Cφ N W) := by
  set step := vsPDsStepF I ws' cs rows Zp gs cap hs1 F r
  set Q := vsPQ I ws' cs rows hs gs Zp cap hs1 F r
  have hmem : ∀ i, step^[i] y0 ∈ Y := by
    intro i
    induction i with
    | zero => exact hy0
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hval : step (step^[i] y0) = if h : (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r
          (step^[i] y0))).findIdx (vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs
          cap hs1 F r (step^[i] y0)).length) < (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r
          (step^[i] y0))).length then (vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r
          (step^[i] y0)))[_]'h else step^[i] y0 := rfl
      rw [hval]
      split_ifs with h
      · exact (hY _ ih).2 _ (List.getElem_mem h)
      · exact ih
  have hn := D.H.n
  have wenc : ∀ g : Perm (Fin I.n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le g).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have hiter := iter_spec hit (c := Q) (k := k) (acc0 := encPerm y0)
    (Inv := fun i acc => acc = encPerm (step^[i] y0)) (M := 4 * (N + 1) ^ 2)
    (B := fun _ => vsPDsStepCost Cφ N W) rfl (fun i acc _ h => h ▸ wenc _)
    (fun i acc hi h => by
      subst h
      have hy := hY _ (hmem i)
      refine FunAll.mono (vsPDsStep_spec hst L LE hfnd hpr hphi D hy.1
        (fun z hz => (hY z (hy.2 z hz)).1) (i := i) (by omega)) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, Function.iterate_succ_apply'])
  set vs := [Q, encPerm y0, Val.nat k]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dc := Det.call (Det.mk3 a0 a2 a1) (hiter.mono fun w c hw => ⟨hw.1, hw.2⟩)
  refine FunDet.intro hf (dc.mono ?_)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have wQ : Q.wt ≤ W := D.hQ
  have wy0 := wenc y0
  have wyk := wenc (step^[k] y0)
  have wk := wt_nat_le k
  have w3 := wt_list3_le Q (encPerm y0) (Val.nat k)
  have evs : (Val.list vs).wt = (Val.list [Q, encPerm y0, Val.nat k]).wt := rfl
  have w3' := wt_list3_le Q (Val.nat k) (encPerm y0)
  have h1 : k * vsPDsStepCost Cφ N W ≤ (N + 2) * vsPDsStepCost Cφ N W :=
    Nat.mul_le_mul_right _ (by omega)
  set Z := (N + 2) * (W + 100 * (N + 1) ^ 2)
  have hZ : W + 100 * (N + 1) ^ 2 ≤ Z := Nat.le_mul_of_pos_left _ (by omega)
  have hL : loopModK * (k + 1) * ((Val.list [Q, Val.nat k, encPerm y0]).wt + k + 4 * (N + 1) ^ 2 + 1)
      ≤ 1000 * (4 * Z) := by
    have hA : (Val.list [Q, Val.nat k, encPerm y0]).wt + k + 4 * (N + 1) ^ 2 + 1 ≤
        4 * (W + 100 * (N + 1) ^ 2) := by
      have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
      omega
    have e1 : (N + 2) * (4 * (W + 100 * (N + 1) ^ 2)) = 4 * Z := by simp only [Z]; ring
    calc loopModK * (k + 1) * ((Val.list [Q, Val.nat k, encPerm y0]).wt + k + 4 * (N + 1) ^ 2 + 1)
        ≤ loopModK * (N + 2) * (4 * (W + 100 * (N + 1) ^ 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hA
      _ = 1000 * (4 * Z) := by rw [mul_assoc, e1]; rfl
  have eZ : 10 ^ 4 * (N + 2) * (W + 100 * (N + 1) ^ 2) = 10 ^ 4 * Z := by simp only [Z]; ring
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  unfold vsPDescCost
  rw [eZ]
  omega

end GI.Impl
