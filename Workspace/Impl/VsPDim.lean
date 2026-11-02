import Workspace.Impl.VsPOrb
import Workspace.Impl.VsPBas
import Workspace.Impl.VsPEnum

/-!
# The dimension of a spin

For an element `y`, the program runs the orbit (`vsPOrbit`) and the greedy basis of the orbit
keys (`vsPBasis`). The kept elements `vsPDim … y` span the keys of the spin; their number is the
dimension (`Proved/VsPBasMath.lean`).

The orbit data `Q = [pc, cap, hs1, F, r]` is packed in one value (`vsPQ`); its hypotheses are
bundled in `VsPOD`, and the function indices of the orbit program in `VsPOLay`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- A list of five values. -/
def vsPMk5 (a b c d f : Expr) : Expr := .snoc (mk4 a b c d) f

theorem Det.vsPMk5 {P : Program} {env : List Val} {a b c d f : Expr} {va vb vc vd vf : Val}
    {ca cb cc cd cf : ℕ} (ha : Det P env a va ca) (hb : Det P env b vb cb)
    (hc : Det P env c vc cc) (hd : Det P env d vd cd) (hf : Det P env f vf cf) :
    Det P env (vsPMk5 a b c d f) (.list [va, vb, vc, vd, vf])
      (ca + cb + cc + cd + cf + 5 * (Val.list [va, vb, vc, vd, vf]).wt + 10) := by
  have h1 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, vf] from ⟨[vf], rfl⟩)
  exact (Det.snoc (Det.mk4 ha hb hc hd) hf).mono
    (by simp only [List.cons_append, List.nil_append]; omega)

/-- The orbit data value `[pc, cap, hs1, F, r]`. -/
def vsPQ (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (hs gs : List (Perm (Fin I.n))) (Zp : List (List (List ℕ))) (cap : ℕ)
    (hs1 : List (Perm (Fin I.n))) (F r : ℕ) : Val :=
  .list [vsPPc I ws' cs rows hs gs Zp, .nat cap, .list (hs1.map encPerm), .nat F, .nat r]

/-- The kept elements of the greedy basis of the orbit keys of `y`. -/
noncomputable def vsPDim (I : VecStabInst) (ws' cs : List (List ℕ)) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (cap : ℕ) (hs1 : List (Perm (Fin I.n))) (F r : ℕ)
    (y : Perm (Fin I.n)) : List (Perm (Fin I.n)) :=
  (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y)).2

/-- The hypotheses on the orbit data. -/
structure VsPOD (I : VecStabInst) (N W : ℕ) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (hs gs : List (Perm (Fin I.n))) (Zp : List (List (List ℕ))) (cap : ℕ)
    (hs1 : List (Perm (Fin I.n))) (F r : ℕ) : Prop where
  H : VsPCtxOK I N W ws' cs rows hs
  hZ : ∀ A ∈ Zp, VsWSq I.p cs.length A
  hZl : Zp.length ≤ N
  hpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W
  hgs : ∀ g ∈ gs, g ∈ gens I.gs
  hgl : gs.length ≤ N
  hh : ∀ h ∈ hs1, h ∈ gens I.gs
  hhl : hs1.length ≤ (N + 1) ^ 2
  hhw : (Val.list (hs1.map encPerm)).wt ≤ W
  hcap1 : 1 ≤ cap
  hcap : cap ≤ N
  hF : F ≤ N
  hr : 0 < r
  hrN : r ≤ N
  hQ : (vsPQ I ws' cs rows hs gs Zp cap hs1 F r).wt ≤ W

/-- The function indices of the orbit program. -/
structure VsPOX where
  (orb itb st fo out fi ins conj comp inv key mp it comm loc fd fd' pk eq eqb phi : ℕ)

/-- The layout of the orbit program in `P`. -/
structure VsPOLay (P : Program) (x : VsPOX) : Prop where
  hf : P.funs[x.orb]? = some (vsPOrbE x.key x.itb)
  hitb : P.HasAt x.itb (iterFuns x.itb x.st)
  hst : P.funs[x.st]? = some (vsPOItE x.fo)
  hfo : P.HasAt x.fo (foldlFuns x.fo x.out)
  hout : P.funs[x.out]? = some (vsPOOutE x.fi)
  hfi : P.HasAt x.fi (foldlFuns x.fi x.ins)
  hins : P.funs[x.ins]? = some (vsPOInsE x.conj x.key x.fd)
  hconj : P.funs[x.conj]? = some (vsPConjE x.comp x.inv)
  hfd : P.HasAt x.fd (findFuns x.fd x.pk)
  hpk : P.funs[x.pk]? = some (vsPPkE x.eq)
  heqn : P.HasAt x.eq (eqNatsFuns x.eq)
  hkey : P.funs[x.key]? = some (vsPKeyE x.mp)
  hmp : P.HasAt x.mp (mapFuns x.mp x.it)
  hit : P.funs[x.it]? = some (vsPKeyItemE x.comm x.loc x.fd')
  hcomm : P.funs[x.comm]? = some (vsPCommE x.comp x.inv)
  hcomp : P.HasAt x.comp (composeFuns x.comp)
  hinv : P.HasAt x.inv (invFuns x.inv)
  hloc : P.funs[x.loc]? = some (vsPLocE x.phi (x.loc + 1))
  hwl : P.HasAt (x.loc + 1) (vsWLocFuns (x.loc + 1))
  hfd' : P.HasAt x.fd' (findFuns x.fd' x.eqb)
  heq : P.HasAt x.eqb (vsPEqFuns x.eqb)

theorem VsPOLay.orb_spec {P : Program} {x : VsPOX} (L : VsPOLay P x) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    (D : VsPOD I N W ws' cs rows hs gs Zp cap hs1 F r) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    FunDet P x.orb (.list [vsPPc I ws' cs rows hs gs Zp, encPerm y, .nat cap,
        .list (hs1.map encPerm), .nat F])
      (.list ((vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y).map vsPPV)) (vsPOrbCost Cφ N W) :=
  vsPOrb_spec L.hf L.hitb L.hst L.hfo L.hout L.hfi L.hins L.hconj L.hfd L.hpk L.heqn L.hkey L.hmp
    L.hit L.hcomm L.hcomp L.hinv L.hloc L.hwl L.hfd' L.heq hphi D.H D.hZ D.hZl D.hpc D.hgs D.hgl
    D.hh D.hhl D.hhw D.hcap1 D.hcap D.hF hy

/-- The weight of a greedy basis. -/
theorem vsPGV_wt_le {n r N k : ℕ} (hn : n ≤ N) (hr : 0 < r) (hrN : r ≤ N) (hk : k ≤ N)
    {O : List (Perm (Fin n) × List ℕ)} (hO : ∀ p ∈ O, (∀ x ∈ p.2, x < r) ∧ p.2.length = k)
    (hOl : O.length ≤ N) : (vsPGV (vsPBasis r O)).wt ≤ 300 * (N + 1) ^ 3 := by
  obtain ⟨h1, h2, h3⟩ := vsPBasis_take_inv hr hrN hk hO O.length
  rw [List.take_length] at h1 h2 h3
  have wR := wt_vsRows_le h1 (by omega)
  have eB : vsPBasis r O = O.foldl (vsPGStep r) ([], []) := rfl
  rw [eB]
  have wB := vsP_wt_perms hn (O.foldl (vsPGStep r) ([], [])).2 (by omega)
  have := wt_list2_le (.list ((O.foldl (vsPGStep r) ([], [])).1.map VsRow.val))
    (.list ((O.foldl (vsPGStep r) ([], [])).2.map encPerm))
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  show (Val.list [.list ((O.foldl (vsPGStep r) ([], [])).1.map VsRow.val),
    .list ((O.foldl (vsPGStep r) ([], [])).2.map encPerm)]).wt ≤ _
  omega

/-- On `[Q, y]`: the greedy basis of the orbit keys of `y`. -/
def vsPDimE (orb bas : ℕ) : Expr :=
  .letE (.call orb (vsPMk5 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1))
      (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 3))))
    (.call bas (mk3 (.get (arg 0) (.nat 4)) (.var 1) (mk2 .nil .nil)))

/-- The cost of the dimension program. -/
def vsPDimCost (Cφ N W : ℕ) : ℕ := vsPOrbCost Cφ N W + vsPBasisCost N + 100 * W + 10 ^ 4 * (N + 1) ^ 3

/-- **The dimension program.** It needs the orbit keys to have entries below `r` and length
`|gs|` (true on the conjugates of an element of `N̄₂`). -/
theorem vsPDim_spec {P : Program} {f bas g ins : ℕ} {x : VsPOX} (hf : P.funs[f]? = some (vsPDimE x.orb bas))
    (L : VsPOLay P x) (hb : P.HasAt bas (foldlFuns bas g))
    (hg : P.funs[g]? = some (vsPGStepE ins)) (hins : P.HasAt ins (vsInsertFuns ins)) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    (D : VsPOD I N W ws' cs rows hs gs Zp cap hs1 F r) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs)
    (hfit : ∀ p ∈ vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y,
      (∀ a ∈ p.2, a < r) ∧ p.2.length = gs.length) :
    FunDet P f (.list [vsPQ I ws' cs rows hs gs Zp cap hs1 F r, encPerm y])
      (vsPGV (vsPBasis r (vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y))) (vsPDimCost Cφ N W) := by
  have hn := D.H.n
  set O := vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y
  set pc := vsPPc I ws' cs rows hs gs Zp
  set qv := [pc, Val.nat cap, .list (hs1.map encPerm), .nat F, .nat r]
  set vs := [vsPQ I ws' cs rows hs gs Zp cap hs1 F r, encPerm y]
  have hOl : O.length ≤ N := ((vsPOrbit_ok D.hcap1 D.hh hy F).2).trans D.hcap
  have a0 : Det P [Val.list vs] (arg 0) (.list qv) _ := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have q k {v : Val} (hv : qv[k]? = some v) := Det.get' a0 (Det.nat k) hv
  have dO := Det.call (Det.vsPMk5 (q 0 rfl) a1 (q 1 rfl) (q 2 rfl) (q 3 rfl)) (L.orb_spec hphi D hy)
  set E := [Val.list vs, Val.list (O.map vsPPV)]
  have b0 : Det P E (arg 0) (.list qv) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [Val.list (O.map vsPPV)]) (j := 0) rfl
  have v1 := Det.var' (P := P) (env := E) (i := 1) rfl
  have r4 := Det.get' b0 (Det.nat 4) (show qv[4]? = some (.nat r) from rfl)
  have dB := Det.call (Det.mk3 r4 v1 (Det.mk2 (Det.nil (P := P) (env := E)) (Det.nil (P := P) (env := E))))
    (vsPBasis_spec hb hg hins hn D.hr D.hrN D.hgl hfit hOl)
  refine FunDet.intro hf ((Det.letE dO dB).mono ?_)
  -- weights
  have wO := vsP_wt_pairs hn hOl (fun p hp => ⟨by rw [(hfit p hp).2]; exact D.hgl,
    fun a ha => ((hfit p hp).1 a ha).le.trans D.hrN⟩)
  have wG := vsPGV_wt_le hn D.hr D.hrN D.hgl hfit hOl
  have wQ : (Val.list qv).wt ≤ W := D.hQ
  have wy := (wt_encPerm_le y).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show I.n + 1 ≤ N + 1 by omega) 2))
  have wvs := wt_list2_le (Val.list qv) (encPerm y)
  have eQ : (vsPQ I ws' cs rows hs gs Zp cap hs1 F r).wt = (Val.list qv).wt := rfl
  have wE := wt_list2_le (Val.list vs) (Val.list (O.map vsPPV))
  have evs : (Val.list vs).wt = (Val.list [Val.list qv, encPerm y]).wt := rfl
  have w5 := wt_list_le [pc, encPerm y, Val.nat cap, .list (hs1.map encPerm), .nat F]
  have wq5 := wt_list_le qv
  simp only [qv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w5 wq5
  have w3 := wt_list3_le (Val.nat r) (Val.list (O.map vsPPV)) (Val.list [.list [], .list []])
  have w00 : (Val.list [Val.list [], Val.list []]).wt ≤ 20 := by decide
  have wr := wt_nat_le r
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have eO : (Val.list ((vsPOrbit (vsPKey I ws' cs Zp gs) cap hs1 F y).map vsPPV)).wt ≤
      70 * (N + 1) ^ 3 := wO
  have eq5 : (Val.list qv).wt = (Val.list [pc, Val.nat cap, .list (hs1.map encPerm), .nat F,
      .nat r]).wt := rfl
  have wpc : pc.wt ≤ W := D.hpc
  have whs := D.hhw
  have wcap := wt_nat_le cap
  have wF := wt_nat_le F
  have hc1 := D.hcap
  have hF1 := D.hF
  have q3 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have hrN := D.hrN
  unfold vsPDimCost
  omega

end GI.Impl
