import Workspace.Impl.VsPRad
import Workspace.Impl.VsPAb
import Workspace.Proved.VsPBasMath

/-!
# The final stage

On `[Q, x₀]`: the kept basis `B` of the spin of `x₀` (`vsPDim`), the group value `⟨B⟩`, and the
isotropy test: do the local matrices of `1 :: B` commute (`vsPAb`). The value is
`[test, ⟨B⟩]` (`vsPFin_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- The kept elements come from the list. -/
theorem vsPBasis_sub {n r : ℕ} (O : List (Perm (Fin n) × List ℕ)) :
    ∀ c ∈ (vsPBasis r O).2, ∃ p ∈ O, p.1 = c := by
  have key : ∀ (M : List (Perm (Fin n) × List ℕ)) (acc : List VsRow × List (Perm (Fin n))),
      ∀ c ∈ (M.foldl (vsPGStep r) acc).2, c ∈ acc.2 ∨ ∃ p ∈ M, p.1 = c := by
    intro M
    induction M with
    | nil => intro acc c hc; exact Or.inl hc
    | cons q M ih =>
      intro acc c hc
      rcases ih _ c hc with h | ⟨p, hp, e⟩
      · unfold vsPGStep at h
        split_ifs at h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl h
          · simp at h; exact Or.inr ⟨q, by simp, h.symm⟩
        · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, e⟩
  intro c hc
  rcases key O ([], []) c hc with h | h
  · simp at h
  · exact h

/-- On `[Q, x₀]`: `[isotropy test, ⟨B⟩]`. -/
def vsPFinE (dim mkg ab : ℕ) : Expr :=
  .letE (.call dim (mk2 (arg 0) (arg 1)))
    (.letE (.call mkg (mk2 (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 6))
        (.get (.var 1) (.nat 1))))
      (mk2 (.call ab (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 2))) (.var 2)))

/-- The isotropy test on the kept basis. -/
noncomputable def vsPIso (I : VecStabInst) (ws' cs : List (List ℕ)) (B : List (Perm (Fin I.n))) :
    Bool :=
  decide (∀ g ∈ 1 :: B, ∀ h ∈ 1 :: B, vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g))

/-- The cost of the final stage. -/
def vsPFinCost (Cφ N W : ℕ) : ℕ :=
  vsPDimCost Cφ N W + mkGroupK * ((N + 2) * (N + 1)) ^ 3 + vsPAbCost Cφ N W + 100 * W +
    10 ^ 4 * (N + 1) ^ 6

set_option maxHeartbeats 4000000 in
theorem vsPFin_spec {r : ℕ} [Fact r.Prime] {P : Program} {f mkg ab fo no fi nc : ℕ} {x : VsPDX}
    (hf : P.funs[f]? = some (vsPFinE x.dim mkg ab)) (L : VsPDLay P x)
    (hmkg : P.HasAt mkg (mkGroupFuns mkg)) (hab : P.funs[ab]? = some (vsPAbE fo))
    (hfo : P.HasAt fo (findFuns fo no)) (hno : P.funs[no]? = some (vsPNoE fi))
    (hfi : P.HasAt fi (findFuns fi nc)) (hnc : P.funs[nc]? = some (vsPNcE x.o.comp x.o.loc x.o.eqb))
    {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F : ℕ}
    (D : VsPOD I N W ws' cs rows hs gs Zp cap hs1 F r) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs)
    (hfit : ∀ p ∈ vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y,
      (∀ a ∈ p.2, a < r) ∧ p.2.length = gs.length) (hgn : gs.length ≤ I.n ^ 2) :
    FunDet P f (.list [vsPQ I ws' cs rows hs gs Zp cap hs1 F r, encPerm y])
      (.list [boolVal (vsPIso I ws' cs (vsPDim I ws' cs Zp gs cap hs1 F r y)),
        encGroup (vsPDim I ws' cs Zp gs cap hs1 F r y)]) (vsPFinCost Cφ N W) := by
  have hn := D.H.n
  set O := vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y
  set B := vsPDim I ws' cs Zp gs cap hs1 F r y
  set Q := vsPQ I ws' cs rows hs gs Zp cap hs1 F r
  set pc := vsPPc I ws' cs rows hs gs Zp
  set C := vsPCtx I ws' cs rows hs
  set GV := vsPGV (vsPBasis r O)
  have hBk : B.length ≤ gs.length :=
    vsPBasis_length_le (kf := vsPKey I ws' cs Zp gs) (fun p hp =>
      ⟨((vsPOrbit_ok (ws' := ws') (cs := cs) (Zp := Zp) (gs := gs) D.hcap1 D.hh hy F).1 p hp).1,
        hfit p hp⟩)
  have hBn : B.length ≤ I.n ^ 2 := hBk.trans hgn
  have hok := vsPOrbit_ok (ws' := ws') (cs := cs) (Zp := Zp) (gs := gs) D.hcap1 D.hh hy F
  have hBg : ∀ b ∈ B, b ∈ gens I.gs := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := vsPBasis_sub O b hb
    exact (hok.1 p hp).2
  have hOl : O.length ≤ N := hok.2.trans D.hcap
  set vs := [Q, encPerm y]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dD := Det.call (Det.mk2 a0 a1) (vsPDim_spec L.hdim L.L L.hb L.hg L.hins hphi D hy hfit)
  -- the group value
  have b0 : Det P [Val.list vs, GV] (arg 0)
      (.list [pc, .nat cap, .list (hs1.map encPerm), .nat F, .nat r]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [GV]) (j := 0) rfl
  have bpc : Det P [Val.list vs, GV] (.get (arg 0) (.nat 0))
      (.list [C, .list (gs.map encPerm), .list (Zp.map vsWVs)]) _ := Det.get' b0 (Det.nat 0) rfl
  have bC : Det P [Val.list vs, GV] (.get (.get (arg 0) (.nat 0)) (.nat 0)) C _ :=
    Det.get' bpc (Det.nat 0) rfl
  have bn : Det P [Val.list vs, GV] (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 6))
      (.nat I.n) _ := Det.get' bC (Det.nat 6) rfl
  have bB : Det P [Val.list vs, GV] (.get (.var 1) (.nat 1)) (.list (B.map encPerm)) _ :=
    Det.get' (Det.var' (i := 1) rfl) (Det.nat 1) rfl
  have dG := Det.call (Det.mk2 bn bB) (mkGroup_spec hmkg B)
  -- the test
  have c0 : Det P [Val.list vs, GV, encGroup B] (arg 0)
      (.list [pc, .nat cap, .list (hs1.map encPerm), .nat F, .nat r]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [GV, encGroup B]) (j := 0) rfl
  have cpc : Det P [Val.list vs, GV, encGroup B] (.get (arg 0) (.nat 0))
      (.list [C, .list (gs.map encPerm), .list (Zp.map vsWVs)]) _ := Det.get' c0 (Det.nat 0) rfl
  have cC : Det P [Val.list vs, GV, encGroup B] (.get (.get (arg 0) (.nat 0)) (.nat 0))
      C _ := Det.get' cpc (Det.nat 0) rfl
  have cv := Det.var' (P := P) (env := [Val.list vs, GV, encGroup B]) (i := 2) rfl
  have dA := Det.call (Det.mk2 cC cv) (vsPAb_spec hab hfo hno hfi hnc L.L.hcomp L.L.hloc L.L.hwl
    L.L.heq hphi D.H hBg hBn)
  have dAll := Det.letE dD (Det.letE dG (Det.mk2 dA cv))
  refine FunDet.intro hf (dAll.mono ?_)
  have hBN : B.length ≤ N := by
    have := (vsPBasis_take_inv D.hr D.hrN D.hgl hfit O.length).2.2
    rw [List.take_length] at this; exact this.trans hOl
  have hmk : mkGroupK * ((B.length + 2) * (I.n + 1)) ^ 3 ≤ mkGroupK * ((N + 2) * (N + 1)) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 3)
  have wEG : (encGroup B).wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hBn
  have wEG' : 320 * (I.n + 1) ^ 6 ≤ 320 * (N + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
  have wGV : GV.wt ≤ 300 * (N + 1) ^ 3 := vsPGV_wt_le hn D.hr D.hrN D.hgl hfit hOl
  have wBl : (Val.list (B.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := vsP_wt_perms hn B (by omega)
  have wQ : Q.wt ≤ W := D.hQ
  have wC : C.wt ≤ W := D.H.cw
  have eQ : (Val.list [pc, Val.nat cap, Val.list (List.map encPerm hs1), Val.nat F, Val.nat r]).wt =
    Q.wt := rfl
  have wpc : pc.wt ≤ W := D.hpc
  have epc : (Val.list [C, Val.list (List.map encPerm gs), Val.list (List.map vsWVs Zp)]).wt =
    pc.wt := rfl
  have wy := (wt_encPerm_le y).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have wvs := wt_list2_le Q (encPerm y)
  have evs : (Val.list vs).wt = (Val.list [Q, encPerm y]).wt := rfl
  have wnn := wt_nat_le I.n
  have w2 := wt_list2_le (Val.nat I.n) (Val.list (B.map encPerm))
  have w3 := wt_list2_le C (encGroup B)
  have wb := wt_boolVal_le (vsPIso I ws' cs B)
  have w4 := wt_list2_le (boolVal (vsPIso I ws' cs B)) (encGroup B)
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hrN := D.hrN
  have eAb : vsPIso I ws' cs B = decide (∀ g ∈ 1 :: B, ∀ h ∈ 1 :: B,
      vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)) := rfl
  have wGV' : (vsPGV (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y))).wt ≤
    300 * (N + 1) ^ 3 := wGV
  have wGV'' : (Val.list [Val.list ((vsPBasis r O).1.map VsRow.val),
    Val.list ((vsPBasis r O).2.map encPerm)]).wt ≤ 300 * (N + 1) ^ 3 := wGV
  have wb' := wt_boolVal_le (decide (∀ g ∈ 1 :: B, ∀ h ∈ 1 :: B,
      vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)))
  have w4' := wt_list2_le (boolVal (decide (∀ g ∈ 1 :: B, ∀ h ∈ 1 :: B,
      vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)))) (encGroup B)
  unfold vsPFinCost
  omega

end GI.Impl
