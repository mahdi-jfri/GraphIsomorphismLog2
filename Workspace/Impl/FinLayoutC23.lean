module

public import Workspace.Impl.AggItemCfCase
public import Workspace.Impl.AggItemCiSpec
public import Workspace.Impl.AggItemHvInitFit

@[expose] public section

/-! # Fixed functions of Cases 2b and 3

Offsets from `c`: 0 init, 1 step, 2–15 object dispatch and cache,
16–31 item dispatch and colored partitions. Case 1 helpers are shared at `d`.
The object entries are at 1000, 1001, 1002 and the pair entries at
100000, 100001, 100002. The binary refinement uses primitive 20.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (KaryRefinement)

/-- The fixed functions, without padding. -/
noncomputable def fc23Conc (c d : ℕ) : List Expr :=
  [itCfIF (d + 10) (c + 1000) (c + 100000)] ++ (
  [itCfBF (c + 2) (c + 3)] ++ (
  [itCfStF (c + 4) (c + 16) (c + 5)] ++ (
  [itCfCtF (c + 100002) (c + 5)] ++ (
  [itCfObF (c + 6) (c + 7)] ++ (
  [itCfWrF] ++ (
  [itCfO2F (c + 1000) (c + 9) (c + 8) (c + 1001)] ++ (
  [itCfO3F (c + 1002) P₀.κ] ++ (
  [stRefF (d + 112) 20] ++ (
  findFuns (c + 9) (c + 12) ++ (
  [itCfKeyF (c + 13)] ++ (
  eqNatsFuns (c + 13) ++ (
  [itciDF (c + 17) (c + 100001)] ++ (
  [itciF (d + 74) (c + 18) (c + 19) (c + 23) (d + 55) (d + 241)] ++ (
  [itciAF (d + 74) (d + 202) (d + 208) (d + 241)] ++ (
  allFuns (c + 19) (c + 22) ++ (
  [itciChkT] ++ (
  [itciGF (c + 24) (d + 223) (d + 229) (d + 226) (d + 53)] ++ (
  mapFuns (c + 24) (c + 27) ++ (
  [itciCB (c + 28)] ++ (
  findFuns (c + 28) (c + 31) ++ (
  [itciEqT])))))))))))))))))))))

theorem fc23_length (c d : ℕ) : (fc23Conc c d).length = 32 := rfl

structure fc23At (P : Program) (c d : ℕ) : Prop where
  init : P.funs[c + 0]? = some (itCfIF (d + 10) (c + 1000) (c + 100000))
  step : P.funs[c + 1]? = some (itCfBF (c + 2) (c + 3))
  start : P.funs[c + 2]? = some (itCfStF (c + 4) (c + 16) (c + 5))
  cont : P.funs[c + 3]? = some (itCfCtF (c + 100002) (c + 5))
  ob : P.funs[c + 4]? = some (itCfObF (c + 6) (c + 7))
  wr : P.funs[c + 5]? = some (itCfWrF)
  o2 : P.funs[c + 6]? = some (itCfO2F (c + 1000) (c + 9) (c + 8) (c + 1001))
  o3 : P.funs[c + 7]? = some (itCfO3F (c + 1002) P₀.κ)
  ref : P.funs[c + 8]? = some (stRefF (d + 112) 20)
  fd : P.HasAt (c + 9) (findFuns (c + 9) (c + 12))
  key : P.funs[c + 12]? = some (itCfKeyF (c + 13))
  eqn : P.HasAt (c + 13) (eqNatsFuns (c + 13))
  disp : P.funs[c + 16]? = some (itciDF (c + 17) (c + 100001))
  part : P.funs[c + 17]? = some (itciF (d + 74) (c + 18) (c + 19) (c + 23) (d + 55) (d + 241))
  al : P.funs[c + 18]? = some (itciAF (d + 74) (d + 202) (d + 208) (d + 241))
  all : P.HasAt (c + 19) (allFuns (c + 19) (c + 22))
  chk : P.funs[c + 22]? = some (itciChkT)
  gen : P.funs[c + 23]? = some (itciGF (c + 24) (d + 223) (d + 229) (d + 226) (d + 53))
  mp : P.HasAt (c + 24) (mapFuns (c + 24) (c + 27))
  cb : P.funs[c + 27]? = some (itciCB (c + 28))
  fnd : P.HasAt (c + 28) (findFuns (c + 28) (c + 31))
  t : P.funs[c + 31]? = some (itciEqT)

/-- Read the fixed table from its installed list. -/
theorem fc23_at {P : Program} {c d : ℕ} (h : P.HasAt c (fc23Conc c d)) :
    fc23At P c d := by
  have h : P.HasAt (c + 0) (fc23Conc c d) := h
  unfold fc23Conc at h
  obtain ⟨h_init, h⟩ := fit_peel (N' := 1) h rfl rfl
  obtain ⟨h_step, h⟩ := fit_peel (N' := 2) h rfl rfl
  obtain ⟨h_start, h⟩ := fit_peel (N' := 3) h rfl rfl
  obtain ⟨h_cont, h⟩ := fit_peel (N' := 4) h rfl rfl
  obtain ⟨h_ob, h⟩ := fit_peel (N' := 5) h rfl rfl
  obtain ⟨h_wr, h⟩ := fit_peel (N' := 6) h rfl rfl
  obtain ⟨h_o2, h⟩ := fit_peel (N' := 7) h rfl rfl
  obtain ⟨h_o3, h⟩ := fit_peel (N' := 8) h rfl rfl
  obtain ⟨h_ref, h⟩ := fit_peel (N' := 9) h rfl rfl
  obtain ⟨h_fd, h⟩ := fit_peel (N' := 12) h rfl rfl
  obtain ⟨h_key, h⟩ := fit_peel (N' := 13) h rfl rfl
  obtain ⟨h_eqn, h⟩ := fit_peel (N' := 16) h rfl rfl
  obtain ⟨h_disp, h⟩ := fit_peel (N' := 17) h rfl rfl
  obtain ⟨h_part, h⟩ := fit_peel (N' := 18) h rfl rfl
  obtain ⟨h_al, h⟩ := fit_peel (N' := 19) h rfl rfl
  obtain ⟨h_all, h⟩ := fit_peel (N' := 22) h rfl rfl
  obtain ⟨h_chk, h⟩ := fit_peel (N' := 23) h rfl rfl
  obtain ⟨h_gen, h⟩ := fit_peel (N' := 24) h rfl rfl
  obtain ⟨h_mp, h⟩ := fit_peel (N' := 27) h rfl rfl
  obtain ⟨h_cb, h⟩ := fit_peel (N' := 28) h rfl rfl
  obtain ⟨h_fnd, h⟩ := fit_peel (N' := 31) h rfl rfl
  exact ⟨h_init.single, h_step.single, h_start.single, h_cont.single, h_ob.single, h_wr.single, h_o2.single, h_o3.single, h_ref.single, h_fd, h_key.single, h_eqn, h_disp.single, h_part.single, h_al.single, h_all, h_chk.single, h_gen.single, h_mp, h_cb.single, h_fnd, h.single⟩

/-- The partition indices share the existing Case 1 helpers. -/
def fc23Ii (c d : ℕ) : ItciIdx where
  c1 := fitC1Idx d
  f := c + 17
  fa := c + 18
  all := c + 19
  chk := c + 22
  fg := c + 23
  mpC := c + 24
  cb := c + 27
  fnd := c + 28
  t := c + 31

/-- All partition callees are installed. -/
theorem fc23_itciOk {P : Program} {c d : ℕ} (h : fc23At P c d) (hA : FitAt P d) :
    ItciOk P (fc23Ii c d) :=
  ⟨fit_c1Ok hA, h.part, h.al, h.all, h.chk, h.gen, h.mp, h.cb, h.fnd, h.t⟩

/-- The explicit case bound. -/
noncomputable def fc23X (h2 : KaryRefinement 2) (Co Do : ℕ) (Xp : ℕ → ℕ) : ℕ → ℕ :=
  itCfX Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k (itciXt Xp)

theorem fc23_X_pbu (h2 : KaryRefinement 2) (Co Do : ℕ) {Xp : ℕ → ℕ}
    (h : PBU fun _ W _ => Xp W) : PBU fun _ W _ => fc23X h2 Co Do Xp W :=
  itCfX_pbu _ _ _ _ (itciXt_pbu h)

/-- The case contract holds for every interface from the two program contracts. -/
theorem fc23_caseOK (I : Iface) {P : Program} {c d : ℕ} {F : Funs}
    (h : fc23At P c d) (hA : FitAt P d) (h2 : KaryRefinement 2)
    (hj : P.prims[20]? = some (karyRefinementPrim h2)) {Co Do : ℕ} {Xp : ℕ → ℕ}
    (hobj : ItCfObjSpec P (c + 1000) (c + 1001) (c + 1002) Co Do)
    (hpair : ItciPairSpec I P F (c + 100000) (c + 100001) (c + 100002) Xp) :
    ItSCaseOK I P F (fun a => a = .twoB ∨ a = .three) (c + 0) (c + 1)
      (fc23X h2 Co Do Xp) := by
  have hi := itci_itemSpec I P hpair (fc23_itciOk h hA) h.disp
  exact itS_c23_caseOK I P hobj hi h2 hj h.init h.step h.start h.cont h.wr h.ob h.o2 h.o3
    hA.grp hA.rb hA.mpsf hA.sf hA.app h.fd h.key h.eqn h.ref hA.brep

end GI.Impl
