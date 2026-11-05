module

public import Workspace.Impl.VsQAnaBase
public import Workspace.Impl.VsFAlgSpanProg
public import Workspace.Impl.VsWProgId
public import Workspace.Impl.VsWProgNil
public import Workspace.Impl.VsWProgAnn
public import Workspace.Impl.VsWProgEig
public import Workspace.Proved.VsQAlg
public import Workspace.Proved.VsWEigCount

@[expose] public section

/-!
# The abelian branch of the analysis

On a valid state `s` whose group acts on `W/W'` as an abelian group, with `D = dim W/W' ≥ 2`,
the program `vsQAbFuns` computes the algebra `B = 𝔽_p[Λ(H)]` (a basis `Bm`) and returns:

1. if `dim B < D`: the chain split by the first columns `B e₀` (`vsQ_rows`);
2. else, if the common kernel of the nilpotent elements is not everything: the chain split by
   it (`vsQ_ann`);
3. else, if the first piece is not everything: the chain split by it (`vsQ_piece`);
4. else `B` is a field (`vsQ_field`) and the field-line base `fld` gives the answer.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {S Tm : ℕ}

/-! ### Lengths -/

theorem vsFAnnL_length {p N D : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hDN : D ≤ N) :
    ∀ (Ys : List (List (List ℕ))) (us : List (List ℕ)), (∀ y ∈ Ys, VsWSq p D y) →
      VsWFit p D us → us.length ≤ N → (Ys.foldl (vsWCut p D) us).length ≤ us.length
  | [], _, _, _, _ => le_rfl
  | y :: Ys, us, hY, hu, hl => by
    have h1 := vsWCut_length_le hp1 hpN hDN (hY y (by simp)) (us := us) hl
    have h2 := vsFAnnL_length hp1 hpN hDN Ys (vsWCut p D us y) (fun y' hy' => hY y' (by simp [hy']))
      (vsWCut_fit (by omega)) (by omega)
    simp only [List.foldl_cons]
    omega

theorem vsFNilL_length {p N D : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hDN : D * D ≤ N)
    {Bm : List (List (List ℕ))} (hB : ∀ M ∈ Bm, VsWSq p D M) (hl : Bm.length ≤ N) :
    (vsFNilL p D Bm).length ≤ Bm.length := by
  have := vsWKer_length_le hp1 hpN hDN (vsWPowFlat_fit (by omega) hB) (by simpa using hl)
  simpa [vsFNilL] using this

theorem vsFFixL_length {p N D : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hDN : D * D ≤ N)
    {Bm : List (List (List ℕ))} (hB : ∀ M ∈ Bm, VsWSq p D M) (hl : Bm.length ≤ N) :
    (vsFFixL p D Bm).length ≤ Bm.length := by
  have := vsWKer_length_le hp1 hpN hDN (vsWFixFlat_fit (by omega) hB) (by simpa using hl)
  simpa [vsFFixL] using this

theorem vsFNilL_sq {p D : ℕ} (hp : 0 < p) (Bm : List (List (List ℕ))) :
    ∀ M ∈ vsFNilL p D Bm, VsWSq p D M := by
  intro M hM
  simp only [vsFNilL, List.mem_map] at hM
  obtain ⟨a, -, rfl⟩ := hM
  exact vsWMC_sq hp _ a

theorem vsQ_mats_inj : Function.Injective fun M : List (List ℕ) => Val.list (M.map natList) := by
  intro M M' h
  simp only [Val.list.injEq] at h
  exact List.map_injective_iff.mpr (fun a a' e => vsFMat_natList_inj e) h

/-- `(2 S⁴ + 1)^k ≤ 3^8 S^32` for `k ≤ 8`. -/
theorem vsQ_powN {S k : ℕ} (hS : 1 ≤ S) (hk : k ≤ 8) : (2 * S ^ 4 + 1) ^ k ≤ 6561 * S ^ 32 := by
  have h1 : 2 * S ^ 4 + 1 ≤ 3 * S ^ 4 := by have := Nat.one_le_pow 4 S hS; omega
  calc (2 * S ^ 4 + 1) ^ k ≤ (3 * S ^ 4) ^ k := Nat.pow_le_pow_left h1 k
    _ ≤ (3 * S ^ 4) ^ 8 := Nat.pow_le_pow_right (by have := Nat.one_le_pow 4 S hS; omega) hk
    _ = 6561 * S ^ 32 := by ring

/-! ### The program -/

/-- `p`, from the frame. -/
def vsQAbP : Expr := .get (.get (arg 1) (.nat 0)) (.nat 0)

/-- The zero vector of length `D`, from the frame. -/
def vsQAbZ : Expr := .get (.get (arg 1) (.nat 0)) (.nat 3)

/-- Is the length of the list `e` below `D`? -/
def vsQLtD (e : Expr) : Expr := .arith .lt (.length e) (arg 2)

/-- On `[c, M]`: the first row of `M`. -/
def vsQRow0E : Expr := .get (arg 1) (.nat 0)

/-- The abelian branch, on the local context. -/
def vsQAbE (idf alg mp spl nil ann bas fix eig fld : ℕ) : Expr :=
  .letE (.call alg (mk4 vsQAbP (arg 3) vsQAbZ (.call idf (arg 2))))
  (.letE (.get (.var 1) (.nat 1))
  (.ite (vsQLtD (.var 2))
    (.call spl (mk2 (.var 0) (.call mp (mk2 (.nat 0) (.var 2)))))
    (.letE (.call bas (mk2 vsQAbP (.call ann (mk3 vsQAbP (arg 2)
        (.call nil (mk3 vsQAbP (arg 2) (.var 2)))))))
    (.ite (vsQLtD (.var 3))
      (.call spl (mk2 (.var 0) (.var 3)))
      (.letE (.call bas (mk2 vsQAbP (.get (.call eig (mk3 vsQAbP (arg 2)
          (.call fix (mk3 vsQAbP (arg 2) (.var 2))))) (.nat 0))))
      (.ite (vsQLtD (.var 4))
        (.call spl (mk2 (.var 0) (.var 4)))
        (.letE (.call bas (mk2 vsQAbP (.call mp (mk2 (.nat 0) (.var 2)))))
        (.ite (vsQLtD (.var 5))
          (.call spl (mk2 (.var 0) (.var 5)))
          (.call fld (mk2 (.var 0) (.var 2)))))))))))

/-- The abelian branch at base `b` (629 functions); `fld` is the field-line base. -/
def vsQAbFuns (b fld : ℕ) : List Expr :=
  [vsQAbE (b + 1) (b + 11) (b + 69) (b + 73) (b + 133) (b + 249) (b + 321) (b + 360) (b + 476) fld] ++
    (vsWIdFuns (b + 1) ++ (vsFAlgSpanFuns (b + 11) ++ (mapFuns (b + 69) (b + 72) ++ ([vsQRow0E] ++
    (vsQSplFuns (b + 73) ++ (vsFNilFuns (b + 133) ++ (vsFAnnFuns (b + 249) ++ (vsWBasFuns (b + 321) ++
    (vsFFixFuns (b + 360) ++ vsFEigFuns (b + 476))))))))))

/-! ### Weights of the outputs -/

theorem FunDet.wt_lt' {P : Program} {f : ℕ} {v w : Val} {c : ℕ} (h : FunDet P f v w c) :
    w.wt < c := by
  obtain ⟨body, -, he⟩ := FunAll.wt_lt h
  obtain ⟨w', c', -, ⟨rfl, hc⟩, hw⟩ := he.exists_eval
  omega

theorem Det.wt_lt' {P : Program} {env : List Val} {e : Expr} {v : Val} {c : ℕ}
    (h : Det P env e v c) : v.wt < c := Det.wt_lt h

theorem Det.mk2c {P : Program} {env : List Val} {a b : Expr} {va vb : Val} {ca cb : ℕ}
    (ha : Det P env a va ca) (hb : Det P env b vb cb) :
    Det P env (mk2 a b) (.list [va, vb]) (5 * (ca + cb) + 20) :=
  (Det.mk2 ha hb).mono (by
    have := wt_list2_le va vb; have := Det.wt_lt ha; have := Det.wt_lt hb; omega)

theorem Det.mk3c {P : Program} {env : List Val} {a b c : Expr} {va vb vc : Val} {ca cb cc : ℕ}
    (ha : Det P env a va ca) (hb : Det P env b vb cb) (hc : Det P env c vc cc) :
    Det P env (mk3 a b c) (.list [va, vb, vc]) (7 * (ca + cb + cc) + 30) :=
  (Det.mk3 ha hb hc).mono (by
    have := wt_list3_le va vb vc; have := Det.wt_lt ha; have := Det.wt_lt hb
    have := Det.wt_lt hc; omega)

theorem Det.mk4c {P : Program} {env : List Val} {a b c d : Expr} {va vb vc vd : Val}
    {ca cb cc cd : ℕ} (ha : Det P env a va ca) (hb : Det P env b vb cb) (hc : Det P env c vc cc)
    (hd : Det P env d vd cd) :
    Det P env (mk4 a b c d) (.list [va, vb, vc, vd]) (9 * (ca + cb + cc + cd) + 50) :=
  (Det.mk4 ha hb hc hd).mono (by
    have := wt_list4_le va vb vc vd; have := Det.wt_lt ha; have := Det.wt_lt hb
    have := Det.wt_lt hc; have := Det.wt_lt hd; omega)

theorem Det.getc {P : Program} {env : List Val} {l i : Expr} {vs : List Val} {x ca cb : ℕ}
    {v : Val} (ha : Det P env l (.list vs) ca) (hb : Det P env i (.nat x) cb)
    (hv : vs[x]? = some v) : Det P env (.get l i) v (2 * ca + cb + 1) :=
  (Det.get' ha hb hv).mono (by
    have h1 := Det.wt_lt ha
    obtain ⟨hx, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    have := wt_getElem_lt vs x hx; omega)

/-- A call whose cost no longer counts the result twice. -/
theorem Det.call'' {P : Program} {env : List Val} {f : ℕ} {a : Expr} {v w : Val} {ca cb : ℕ}
    (ha : Det P env a v ca) (hf : FunDet P f v w cb) : Det P env (.call f a) w (ca + 2 * cb) :=
  (Det.call ha hf).mono (by have := FunDet.wt_lt' hf; omega)

theorem vsQSpl_wt (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hd : 2 ≤ I.d)
    (us : List (List ℕ)) :
    (vsQSplitV [1] s.hs (vsQSplLows s us)).wt ≤ 10 ^ 4 * S ^ 6 := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hlf : VsWFit I.p I.d (vsWLift I.p I.d s.ws' (vsQCs s) us) :=
    vsWLift_fit I.prime.pos hs.fit' _ _
  have hbl : (vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us)).length ≤ I.d := by
    rw [vsWBas_length I.prime hlf]
    exact (Submodule.finrank_le _).trans (by simp)
  have hl : (vsQLowsV (vsQSplLows s us)).wt ≤ 300 * S ^ 4 := hS.wt_lows (by
    intro u hu
    simp only [vsQSplLows, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact ⟨vsWBas_fit I.prime.pos hlf, hbl⟩
    · exact ⟨hs.fit', hs.wl'⟩) (by simp [vsQSplLows]; omega)
  have h4 := wt_list4_le (.nat 1) (.list [encPerm (1 : Perm (Fin I.n))]) (encGroup s.hs)
    (vsQLowsV (vsQSplLows s us))
  have h1 := wt_list1_le (encPerm (1 : Perm (Fin I.n)))
  have := hS.wt_perm 1
  have := hS.wt_group hs.hsl
  have := wt_nat_le 1
  have := hS.pow_le (show 4 ≤ 6 by omega)
  have := hS.pow_le (show 2 ≤ 6 by omega)
  have := hS.pow_le (show 0 ≤ 6 by omega)
  simp only [pow_zero] at *
  have e : (vsQSplitV [1] s.hs (vsQSplLows s us)).wt = (Val.list [.nat 1,
    .list [encPerm (1 : Perm (Fin I.n))], encGroup s.hs, vsQLowsV (vsQSplLows s us)]).wt := rfl
  omega

theorem vsQLeaf_wt (hS : VsQDSz I S Tm) {a : Option (Perm (Fin I.n) × List (Perm (Fin I.n)))}
    (ha : ∀ r ∈ a, r.2.length ≤ I.n ^ 2) : (vsQLeafV a).wt ≤ 10 ^ 4 * S ^ 6 := by
  have h1 := hS.wt_ans ha
  have h2 := wt_list2_le (.nat 0) (vsQAnsV a)
  have := wt_nat_le 0
  have := hS.pow_le (show 0 ≤ 6 by omega)
  simp at this
  have e : (vsQLeafV a).wt = (Val.list [.nat 0, vsQAnsV a]).wt := rfl
  omega

/-! ### The specification -/

/-- What the field-line base must do on a state (hypothesis of `vsQAb_spec`). -/
def VsQFldHyp (P : Program) (fld CF : ℕ) {s : VsQSt I} (hs : VsQStOK s) : Prop :=
  ∀ Lb : List (List (List ℕ)),
    (∀ X, X ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X} ↔
      X ∈ Algebra.adjoin (ZMod I.p) {X | ∃ g ∈ s.hs, vsQLam s g = X}) →
    (∀ X ∈ Algebra.adjoin (ZMod I.p) {X | ∃ g ∈ s.hs, vsQLam s g = X},
      X = 0 ∨ ∀ v, X *ᵥ v = 0 → v = 0) →
    vsWSp I.p (vsQD s) (vsQRows0 Lb) = ⊤ → Lb.length ≤ vsQD s * vsQD s →
    (∀ M ∈ Lb, VsWSq I.p (vsQD s) M) →
    FunAll P fld (.list [vsQLCV s, vsFMatsVal Lb])
      (fun w c => (∃ a, w = vsQLeafV a ∧ VsQAnsOK hs.prob a) ∧ c ≤ CF)

set_option maxHeartbeats 8000000 in
/-- **The abelian branch.** -/
theorem vsQAb_spec {P : Program} {b fld E CF : ℕ} (h : P.HasAt b (vsQAbFuns b fld))
    (hS : VsQDSz I S Tm) (hTm : 1 ≤ Tm) {s : VsQSt I} (hs : VsQStOK s) (hab : s.Ab)
    (hD : 2 ≤ vsQD s) (hfld : VsQFldHyp P fld CF hs) :
    FunAll P b (vsQLCV s) (fun w c => VsQAnaOut hs E Tm w ∧ c ≤ CF + 10 ^ 25 * S ^ 32) := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  -- the blocks
  obtain ⟨h0', h1⟩ := h.split (k := 1) rfl
  obtain ⟨hidf, h2⟩ := h1.split (vsWIdFuns_length _)
  obtain ⟨halg, h3⟩ := h2.split (vsFAlgSpanFuns_length _)
  obtain ⟨hmp, h4⟩ := h3.split (k := 3) rfl
  obtain ⟨hit, h5⟩ := h4.split (k := 1) rfl
  obtain ⟨hspl, h6⟩ := h5.split (vsQSplFuns_length _)
  obtain ⟨hnil, h7⟩ := h6.split (vsWRelFuns_length _ _)
  obtain ⟨hann, h8⟩ := h7.split (vsFAnnFuns_length _)
  obtain ⟨hbas, h9⟩ := h8.split (vsWBasFuns_length _)
  obtain ⟨hfix, heig⟩ := h9.split (vsWRelFuns_length _ _)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hidf halg hmp hit hspl hnil hann hbas hfix heig
  have h0 : P.funs[b]? = some (vsQAbE (b + 1) (b + 11) (b + 69) (b + 73) (b + 133) (b + 249)
      (b + 321) (b + 360) (b + 476) fld) := h0'.get (j := 0) (by simp)
  have hit0 : P.funs[b + 72]? = some vsQRow0E := hit.get (j := 0) (by simp)
  -- sizes
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hp1 := I.prime.one_lt
  set D := vsQD s with hDdef
  set N := 2 * S ^ 4 with hN
  have hS4 : S ≤ S ^ 4 := by have := hS.pow_le (show 1 ≤ 4 by omega); simpa using this
  have hDS : D ≤ S := by omega
  have hDD : D * D ≤ S ^ 2 := by rw [sq]; exact Nat.mul_le_mul hDS hDS
  have hS22 : S ^ 2 * S ^ 2 = S ^ 4 := by ring
  have hMsl : (vsQMs s).length ≤ S ^ 2 := by
    simp only [vsQMs, List.length_map]; exact vsQ_hsl hS hs
  have hDDM : D * D * (vsQMs s).length ≤ S ^ 4 := by
    rw [← hS22]; exact Nat.mul_le_mul hDD hMsl
  have hS24 : S ^ 2 ≤ S ^ 4 := hS.pow_le (by omega)
  have hpN : I.p ≤ N := by omega
  have hDN : D ≤ N := by omega
  have hDDN : D * D ≤ N := by omega
  have hBl := vsQBm_length s
  have hBsq := vsQBm_sq s
  -- the values
  set st := vsQStV I s with hst
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s) with hfrV
  set MsV := vsFMatsVal (vsQMs s) with hMsV
  set lc := vsQLCV s with hlc
  set fr0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ D)] with hfr0
  have wLC := vsQ_wt_LC hS hs
  have elc : lc.wt = (vsQLCV s).wt := rfl
  have wfr : frV.wt < lc.wt := wt_le_wt_list (show frV ∈ [st, frV, .nat D, MsV] by simp)
  have wMs : MsV.wt < lc.wt := wt_le_wt_list (show MsV ∈ [st, frV, .nat D, MsV] by simp)
  have wDv : (Val.nat D).wt < lc.wt := wt_le_wt_list (show Val.nat D ∈ [st, frV, .nat D, MsV] by simp)
  have wfr0 : fr0.wt < frV.wt := wt_le_wt_list (show fr0 ∈ [fr0, vsWVs s.ws', vsWVs (vsQCs s),
    .list ((vsWFrRows I.p s.ws' (vsQCs s)).map VsRow.val)] by simp)
  have wpv : (Val.nat I.p).wt < fr0.wt := wt_le_wt_list (by simp)
  have wzv : (natList (vsWZ D)).wt < fr0.wt := wt_le_wt_list (by simp)
  have efr0 : (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d),
      natList (vsWZ (vsQCs s).length)]).wt = fr0.wt := rfl
  -- access to the context, in any environment that starts with it
  have dA : ∀ (rest : List Val) (j : ℕ) (v : Val), [st, frV, .nat D, MsV][j]? = some v →
      Det P (lc :: rest) (arg j) v (2 * lc.wt + j + 5) := fun rest j v hj =>
    Det.arg' (vs := [st, frV, .nat D, MsV]) (rest := rest) hj
  have dF0 : ∀ rest, Det P (lc :: rest) (.get (arg 1) (.nat 0)) fr0 (4 * lc.wt + 20) :=
    fun rest => (Det.get' (dA rest 1 frV rfl) (Det.nat 0) rfl).mono (by omega)
  have dP : ∀ rest, Det P (lc :: rest) vsQAbP (.nat I.p) (6 * lc.wt + 40) :=
    fun rest => (Det.get' (dF0 rest) (Det.nat 0) rfl).mono (by omega)
  have dZ : ∀ rest, Det P (lc :: rest) vsQAbZ (natList (vsWZ D)) (6 * lc.wt + 40) :=
    fun rest => (Det.get' (dF0 rest) (Det.nat 3) rfl).mono (by omega)
  have dD : ∀ rest, Det P (lc :: rest) (arg 2) (.nat D) (2 * lc.wt + 7) :=
    fun rest => dA rest 2 _ rfl
  have dL0 : ∀ rest, Det P (lc :: rest) (.var 0) lc (lc.wt + 1) := fun rest => Det.var' rfl
  -- powers
  have pw : ∀ k ≤ 8, (N + 1) ^ k ≤ 6561 * S ^ 32 := fun k hk => vsQ_powN hS1 hk
  have pw4 := pw 4 (by omega)
  have pw5 := pw 5 (by omega)
  have pw6 := pw 6 (by omega)
  have pw7 := pw 7 (by omega)
  have pw8 := pw 8 (by omega)
  have q6 : S ^ 6 ≤ S ^ 32 := hS.pow_le (by omega)
  have wLC' : lc.wt ≤ 10 ^ 6 * S ^ 32 := by omega
  have hU1 : 1 ≤ S ^ 32 := Nat.one_le_pow _ _ hS1
  have q2U : S ^ 2 ≤ S ^ 32 := hS.pow_le (by omega)
  have q3U : S ^ 3 ≤ S ^ 32 := hS.pow_le (by omega)
  -- the algebra basis
  have didf := Det.call'' (dD []) (vsWId_spec hidf (N := N) hDN)
  have hzb : ∀ y ∈ vsWZ D, y < I.p := fun y hy => by simp [vsWZ] at hy; omega
  have dalg := Det.call'' (Det.mk4c (dP []) (dA [] 3 MsV rfl) (dZ []) didf)
    (vsFAlgSpan_spec halg I.prime.pos hpN hDDN (gs := vsQMs s)
      (fun g hg => vsFSq_of_wSq (vsQMs_sq s g hg)) (by omega) (by omega) hzb (by simp [vsWZ])
      (vsWId_sq hp1 D))
  set stA := vsFAlgSpanL I.p (vsWZ D) (vsWId D) (vsQMs s) (D * D) with hstA
  have dalg' : Det P [lc] _ (vsFAVal stA) (10 ^ 15 * S ^ 32) := dalg.mono (by omega)
  refine FunAll.intro h0 (EvalAll.letE dalg' fun Av cA hA => ?_)
  obtain ⟨rfl, hcA⟩ := hA
  have wA := Det.wt_lt dalg'
  set BmV := vsFMatsVal (vsQBm s) with hBmV
  have eAv : (vsFAVal stA).wt = (Val.list [vsAccVal stA.1, vsFMatsVal stA.2]).wt := rfl
  have dBm : Det P ([lc] ++ [vsFAVal stA]) (.get (.var 1) (.nat 1)) BmV (10 ^ 16 * S ^ 32) :=
    (Det.getc (Det.var' (show ([lc] ++ [vsFAVal stA])[1]? = some (vsFAVal stA) from rfl))
      (Det.nat 1) (show [vsAccVal stA.1, vsFMatsVal stA.2][1]? = some BmV from rfl)).mono
      (by omega)
  refine EvalAll.letE dBm fun Bv cB hB => ?_
  obtain ⟨rfl, hcB⟩ := hB
  have wB := Det.wt_lt dBm
  set E2 := [lc] ++ [vsFAVal stA] ++ [BmV] with hE2
  have dvB : Det P E2 (.var 2) BmV (BmV.wt + 1) := Det.var' rfl
  have eBl : ((vsQBm s).map fun M => Val.list (M.map natList)).length = (vsQBm s).length := by simp
  have dltB := Det.arith' (op := .lt) (Det.length dvB) (dD _) rfl
  rw [eBl] at dltB
  -- small weights
  have hBl2 : (vsQBm s).length ≤ S ^ 2 := le_trans hBl (by omega)
  have wBm : BmV.wt ≤ 1000 * S ^ 5 := vsQ_wt_mats hS hs hBsq hBl2
  have q56 : S ^ 5 ≤ S ^ 6 := hS.pow_le (by omega)
  have hd2 : 2 ≤ I.d := by omega
  have hD' : 1 ≤ vsQD s := by omega
  -- the chain split, from any local list in any environment starting with the context
  have dSpl : ∀ (rest : List Val) (e : Expr) (us : List (List ℕ)) (c : ℕ),
      Det P (lc :: rest) e (vsWVs us) c → VsWFit I.p D us → us.length ≤ I.d →
      Det P (lc :: rest) (.call (b + 73) (mk2 (.var 0) e)) (vsQSplitV [1] s.hs (vsQSplLows s us))
        (5 * (lc.wt + 1 + c) + 20 + 2 * (10 ^ 13 * S ^ 6)) :=
    fun rest e us c de hus hul => Det.call'' (Det.mk2c (dL0 rest) de) (vsQSpl_spec hspl hS hs hus hul)
  -- the output of a chain split
  have hOut : ∀ us : List (List ℕ), VsWFit I.p D us →
      vsWSp I.p D us ≠ ⊥ → vsWSp I.p D us ≠ ⊤ →
      (∀ g ∈ s.hs, ∀ a ∈ vsWSp I.p D us, vsQLam s g *ᵥ a ∈ vsWSp I.p D us) →
      VsQAnaOut hs E Tm (vsQSplitV [1] s.hs (vsQSplLows s us)) := fun us _ hbot htop hU =>
    Or.inr ⟨[1], s.hs, vsQSplLows s us, rfl, vsQ_split1 hs hTm hbot htop hU⟩
  by_cases hlt : (vsQBm s).length < D
  · -- 1. the first columns
    obtain ⟨hfit, hbot, htop, hU⟩ := vsQ_rows hD' hlt
    have hitem : ∀ M ∈ vsQBm s, FunDet P (b + 72) (.list [.nat 0, .list (M.map natList)])
        (natList (M.getD 0 [])) (10 ^ 4 * S ^ 3) := by
      intro M hM
      have hsq := hBsq M hM
      have h0M : (M.map natList)[0]? = some (natList (M.getD 0 [])) := by
        cases M with
        | nil => have := hsq.2; simp at this; omega
        | cons m M => rfl
      have wM := vsQ_wt_loc hS hs hsq.1 (by rw [hsq.2]; exact hDd)
      have w2 := wt_list2_le (.nat 0) (.list (M.map natList))
      have := wt_nat_le 0
      have eM : (vsWVs M).wt = (Val.list (M.map natList)).wt := rfl
      have := Nat.one_le_pow 3 S hS1
      exact FunDet.intro hit0 ((Det.getc (Det.arg' (vs := [.nat 0, .list (M.map natList)])
        (rest := []) (j := 1) rfl) (Det.nat 0) h0M).mono (by omega))
    have dmap := vsQ_map hmp (vsQBm s) (fun M => Val.list (M.map natList))
      (fun M => natList (M.getD 0 [])) vsQ_mats_inj (c := .nat 0) hitem
    have eus : Val.list ((vsQBm s).map fun M => natList (M.getD 0 [])) =
        vsWVs (vsQRows0 (vsQBm s)) := by simp [vsWVs, vsQRows0, List.map_map]
    rw [eus] at dmap
    have dus := Det.call'' (Det.mk2c (Det.nat 0) dvB) dmap
    have hul : (vsQRows0 (vsQBm s)).length ≤ I.d := by simp [vsQRows0]; omega
    have dT := dSpl _ _ _ _ dus hfit hul
    refine Det.post (Det.ite_pos dltB (by simp [GI.Machine.BinOp.eval, hlt]) dT)
      fun c hc => ⟨hOut _ hfit hbot htop hU, ?_⟩
    have wO := vsQSpl_wt hS hs hd2 (vsQRows0 (vsQBm s))
    have wR := vsQ_wt_loc hS hs hfit hul
    have w2 := wt_list2_le (.nat 0) (Val.list (List.map (fun M => Val.list (List.map natList M))
      (vsQBm s)))
    have := wt_nat_le 0
    have eBV : (Val.list (List.map (fun M => Val.list (List.map natList M)) (vsQBm s))).wt =
      BmV.wt := rfl
    have hm1 : (vsQBm s).length * (10 ^ 4 * S ^ 3) ≤ S ^ 2 * (10 ^ 4 * S ^ 3) :=
      Nat.mul_le_mul_right _ hBl2
    have e1 : S ^ 2 * (10 ^ 4 * S ^ 3) = 10 ^ 4 * S ^ 5 := by ring
    have q35 : S ^ 3 ≤ S ^ 5 := hS.pow_le (by omega)
    have hm2 : mapK * ((vsQBm s).length + 1) *
        ((Val.list [Val.nat 0, Val.list (List.map (fun M => Val.list (List.map natList M))
          (vsQBm s))]).wt + (vsWVs (vsQRows0 (vsQBm s))).wt + 1) ≤
        1000 * (2 * S ^ 2) * (10 ^ 4 * S ^ 5) := by
      rw [show mapK = 1000 from rfl]
      have := Nat.one_le_pow 2 S hS1
      have := Nat.one_le_pow 3 S hS1
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : 1000 * (2 * S ^ 2) * (10 ^ 4 * S ^ 5) = 2 * 10 ^ 7 * S ^ 7 := by ring
    have q7 : S ^ 7 ≤ S ^ 32 := hS.pow_le (by omega)
    have ev : GI.Machine.BinOp.lt.eval (vsQBm s).length D = 1 := by
      simp [GI.Machine.BinOp.eval, hlt]
    have t1 : (vsQBm s).length * (10 ^ 4 * S ^ 3) ≤ 10 ^ 4 * S ^ 32 := by omega
    have t2 : mapK * ((vsQBm s).length + 1) *
        ((Val.list [Val.nat 0, Val.list (List.map (fun M => Val.list (List.map natList M))
          (vsQBm s))]).wt + (vsWVs (vsQRows0 (vsQBm s))).wt + 1) ≤ 2 * 10 ^ 7 * S ^ 32 := by omega
    have t3 : c ≤ 10 ^ 19 * S ^ 32 := by omega
    omega
  · -- 2. the kernel of the nilpotent part
    have ev0 : GI.Machine.BinOp.lt.eval (vsQBm s).length D = 0 := by
      simp [GI.Machine.BinOp.eval, hlt]
    rw [ev0] at dltB
    refine (EvalAll.vsQ_ite_zero' (R := fun w c => VsQAnaOut hs E Tm w ∧
      c ≤ CF + 4 * 10 ^ 24 * S ^ 32 ∧ w.wt ≤ 10 ^ 4 * S ^ 6) dltB ?_).mono fun w c hw => ?_
    swap
    · obtain ⟨ce, ⟨hout, hce, hw⟩, hc⟩ := hw
      exact ⟨hout, by omega⟩
    have hBlN : (vsQBm s).length ≤ N := by omega
    have dnil := Det.call'' (Det.mk3c (dP _) (dD _) dvB)
      (vsFNil_spec hnil hp1 hpN hDDN hBsq hBlN)
    have hNl := vsFNilL_length hp1 hpN hDDN hBsq hBlN
    have dann := Det.call'' (Det.mk3c (dP _) (dD _) dnil)
      (vsFAnn_spec hann hp1 hpN hDN (vsFNilL_sq I.prime.pos _) (by omega))
    have hAl : (vsQAnnL s).length ≤ D := by
      have := vsFAnnL_length hp1 hpN hDN (vsFNilL I.p D (vsQBm s)) (vsWId D)
        (vsFNilL_sq I.prime.pos _) (vsWId_fit hp1 D) (by simp [vsWId]; omega)
      simpa [vsQAnnL, vsFAnnL, vsWId] using this
    have hAfit := vsQAnnL_fit (s := s)
    have hAl' : (vsFAnnL I.p D (vsFNilL I.p D (vsQBm s))).length ≤ D := hAl
    have dbasA := Det.call'' (Det.mk2c (dP _) dann)
      (vsWBas_spec hbas I.prime.pos hpN hDN hAfit (by omega))
    set AnnB := vsWBas I.p (vsQAnnL s) with hAnnB
    have dbasA' : Det P E2 _ (vsWVs AnnB) (10 ^ 21 * S ^ 32) := dbasA.mono (by
      have := Det.wt_lt dvB
      omega)
    refine EvalAll.letE dbasA' fun Av2 cA2 hA2 => ?_
    obtain ⟨rfl, hcA2⟩ := hA2
    set E3 := E2 ++ [vsWVs AnnB] with hE3
    have dv3 : Det P E3 (.var 3) (vsWVs AnnB) ((vsWVs AnnB).wt + 1) := Det.var' rfl
    have eAl : (AnnB.map natList).length = AnnB.length := by simp
    have dlt2 := Det.arith' (op := .lt) (Det.length dv3) (dD _) rfl
    rw [eAl] at dlt2
    have hAbf : VsWFit I.p D AnnB := vsWBas_fit I.prime.pos hAfit
    have eAsp : vsWSp I.p D AnnB = vsWSp I.p D (vsQAnnL s) := vsWBas_span I.prime hAfit
    have hABl : AnnB.length ≤ D := by
      rw [hAnnB, vsWBas_length I.prime hAfit]
      exact (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
    have wAnnB := vsQ_wt_loc hS hs hAbf (by omega)
    obtain ⟨hAbot, hAinv⟩ := vsQ_ann hs hab hD'
    by_cases hlt2 : AnnB.length < D
    · have ev : GI.Machine.BinOp.lt.eval AnnB.length D = 1 := by
        simp [GI.Machine.BinOp.eval, hlt2]
      rw [ev] at dlt2
      have dT := dSpl _ _ _ _ dv3 hAbf (by omega)
      refine Det.post (Det.ite_pos dlt2 one_ne_zero dT) fun c hc => ?_
      refine ⟨hOut _ hAbf (by rw [eAsp]; exact hAbot)
        (vsWSp_ne_top_of_bas I.prime hAfit hlt2 |> fun h => by rw [eAsp]; exact h)
        (by rw [eAsp]; exact hAinv), ?_, ?_⟩
      · have wO := vsQSpl_wt hS hs hd2 AnnB
        omega
      · have wO := vsQSpl_wt hS hs hd2 AnnB
        omega
    · have ev : GI.Machine.BinOp.lt.eval AnnB.length D = 0 := by
        simp [GI.Machine.BinOp.eval, hlt2]
      rw [ev] at dlt2
      have hAtop : vsWSp I.p D (vsQAnnL s) = ⊤ := vsWSp_top_of_bas I.prime hAfit (by
        have : D ≤ AnnB.length := by omega
        exact this)
      refine (EvalAll.vsQ_ite_zero' (R := fun w c => VsQAnaOut hs E Tm w ∧
        c ≤ CF + 3 * 10 ^ 24 * S ^ 32 ∧ w.wt ≤ 10 ^ 4 * S ^ 6) dlt2 ?_).mono fun w c hw => ?_
      swap
      · obtain ⟨ce, ⟨hout, hce, hw⟩, hc⟩ := hw
        exact ⟨hout, by omega, hw⟩
      -- 3. the first piece
      have dvB3 : Det P E3 (.var 2) BmV (BmV.wt + 1) := Det.var' rfl
      have dfix := Det.call'' (Det.mk3c (dP _) (dD _) dvB3)
        (vsFFix_spec hfix hp1 hpN hDDN hBsq hBlN)
      have hFl := vsFFixL_length hp1 hpN hDDN hBsq hBlN
      have deig := Det.call'' (Det.mk3c (dP _) (dD _) dfix)
        (vsFEig_spec heig I.prime hpN hDN (vsQFix_sq (s := s)) (by omega))
      have hPne := vsQPcs_ne hs hab hD'
      obtain ⟨Q0, Qs, hPQ⟩ := List.exists_cons_of_ne_nil hPne
      have hQ0 : Q0 ∈ vsQPcs s := by rw [hPQ]; exact List.mem_cons_self
      obtain ⟨hQfit, hQbot, hQinv⟩ := vsQ_piece hs hab hQ0
      have hQl : Q0.length ≤ D := ((vsFEigL_count I.prime _ (vsQFix_sq (s := s))).2 Q0 hQ0).2
      have eP : vsFMatsVal (vsFEigL I.p D (vsFFixL I.p D (vsQBm s))) =
          .list (vsWVs Q0 :: Qs.map fun M => Val.list (M.map natList)) := by
        change vsFMatsVal (vsQPcs s) = _
        rw [hPQ]; rfl
      rw [eP] at deig
      have dget := Det.getc deig (Det.nat 0) (show (vsWVs Q0 ::
        Qs.map fun M => Val.list (M.map natList))[0]? = some (vsWVs Q0) from rfl)
      have dbasQ := Det.call'' (Det.mk2c (dP _) dget)
        (vsWBas_spec hbas I.prime.pos hpN hDN hQfit (by omega))
      set QB := vsWBas I.p Q0 with hQB
      have dbasQ' : Det P E3 _ (vsWVs QB) (10 ^ 23 * S ^ 32) := dbasQ.mono (by
        have := Det.wt_lt dvB3
        omega)
      refine EvalAll.letE dbasQ' fun Qv cQ hQv => ?_
      obtain ⟨rfl, hcQ⟩ := hQv
      set E4 := E3 ++ [vsWVs QB] with hE4
      have dv4 : Det P E4 (.var 4) (vsWVs QB) ((vsWVs QB).wt + 1) := Det.var' rfl
      have eQl : (QB.map natList).length = QB.length := by simp
      have dlt3 := Det.arith' (op := .lt) (Det.length dv4) (dD _) rfl
      rw [eQl] at dlt3
      have hQbf : VsWFit I.p D QB := vsWBas_fit I.prime.pos hQfit
      have eQsp : vsWSp I.p D QB = vsWSp I.p D Q0 := vsWBas_span I.prime hQfit
      have hQBl : QB.length ≤ D := by
        rw [hQB, vsWBas_length I.prime hQfit]
        exact (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
      have wQB := vsQ_wt_loc hS hs hQbf (by omega)
      by_cases hlt3 : QB.length < D
      · have ev : GI.Machine.BinOp.lt.eval QB.length D = 1 := by
          simp [GI.Machine.BinOp.eval, hlt3]
        rw [ev] at dlt3
        have dT := dSpl _ _ _ _ dv4 hQbf (by omega)
        refine Det.post (Det.ite_pos dlt3 one_ne_zero dT) fun c hc => ?_
        have wO := vsQSpl_wt hS hs hd2 QB
        refine ⟨hOut _ hQbf (by rw [eQsp]; exact hQbot)
          (by rw [eQsp]; exact vsWSp_ne_top_of_bas I.prime hQfit hlt3)
          (by rw [eQsp]; exact hQinv), by omega, by omega⟩
      · have ev : GI.Machine.BinOp.lt.eval QB.length D = 0 := by
          simp [GI.Machine.BinOp.eval, hlt3]
        rw [ev] at dlt3
        have hQtop : vsWSp I.p D Q0 = ⊤ := vsWSp_top_of_bas I.prime hQfit (by
          have : D ≤ QB.length := by omega
          exact this)
        refine (EvalAll.vsQ_ite_zero' (R := fun w c => VsQAnaOut hs E Tm w ∧
          c ≤ CF + 2 * 10 ^ 24 * S ^ 32 ∧ w.wt ≤ 10 ^ 4 * S ^ 6) dlt3 ?_).mono fun w c hw => ?_
        swap
        · obtain ⟨ce, ⟨hout, hce, hw⟩, hc⟩ := hw
          exact ⟨hout, by omega, hw⟩
        -- 4. the first columns again, then the field line
        have hitem : ∀ M ∈ vsQBm s, FunDet P (b + 72) (.list [.nat 0, .list (M.map natList)])
            (natList (M.getD 0 [])) (10 ^ 4 * S ^ 3) := by
          intro M hM
          have hsq := hBsq M hM
          have h0M : (M.map natList)[0]? = some (natList (M.getD 0 [])) := by
            cases M with
            | nil => have := hsq.2; simp at this; omega
            | cons m M => rfl
          have wM := vsQ_wt_loc hS hs hsq.1 (by rw [hsq.2]; exact hDd)
          have w2 := wt_list2_le (.nat 0) (.list (M.map natList))
          have := wt_nat_le 0
          have eM : (vsWVs M).wt = (Val.list (M.map natList)).wt := rfl
          have := Nat.one_le_pow 3 S hS1
          exact FunDet.intro hit0 ((Det.getc (Det.arg' (vs := [.nat 0, .list (M.map natList)])
            (rest := []) (j := 1) rfl) (Det.nat 0) h0M).mono (by omega))
        have dmap := vsQ_map hmp (vsQBm s) (fun M => Val.list (M.map natList))
          (fun M => natList (M.getD 0 [])) vsQ_mats_inj (c := .nat 0) hitem
        have eus : Val.list ((vsQBm s).map fun M => natList (M.getD 0 [])) =
            vsWVs (vsQRows0 (vsQBm s)) := by simp [vsWVs, vsQRows0, List.map_map]
        rw [eus] at dmap
        have dvB4 : Det P E4 (.var 2) BmV (BmV.wt + 1) := Det.var' rfl
        have dus := Det.call'' (Det.mk2c (Det.nat 0) dvB4) dmap
        obtain ⟨hRfit, hRbot, hRinv⟩ := vsQ_rows' hD'
        have hRl : (vsQRows0 (vsQBm s)).length ≤ N := by simp [vsQRows0]; omega
        have dbasR := Det.call'' (Det.mk2c (dP _) dus)
          (vsWBas_spec hbas I.prime.pos hpN hDN hRfit hRl)
        set RB := vsWBas I.p (vsQRows0 (vsQBm s)) with hRB
        have hm1 : (vsQBm s).length * (10 ^ 4 * S ^ 3) ≤ S ^ 2 * (10 ^ 4 * S ^ 3) :=
          Nat.mul_le_mul_right _ hBl2
        have e1 : S ^ 2 * (10 ^ 4 * S ^ 3) = 10 ^ 4 * S ^ 5 := by ring
        have q35 : S ^ 3 ≤ S ^ 5 := hS.pow_le (by omega)
        have wR : (vsWVs (vsQRows0 (vsQBm s))).wt ≤ 50 * S ^ 4 := by
          have h1 := GI.Lang.wt_list_le_of ((vsQRows0 (vsQBm s)).map natList) (c := 20 * S ^ 2) (by
            intro v hv
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
            have hu' := hRfit u hu
            have := wt_natList_le_sq (B := S) (xs := u) (fun y hy => (hu'.1 y hy).le.trans hS.p)
              (by rw [hu'.2]; omega)
            have : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
              have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
              have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
              omega
            omega)
          have hl : ((vsQRows0 (vsQBm s)).map natList).length ≤ S ^ 2 := by simp [vsQRows0]; omega
          have h2 := Nat.mul_le_mul_right (2 * (20 * S ^ 2) + 1) hl
          have e : S ^ 2 * (2 * (20 * S ^ 2) + 1) = 40 * S ^ 4 + S ^ 2 := by ring
          have : S ^ 2 ≤ S ^ 4 := hS.pow_le (by omega)
          have : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS1
          show (Val.list ((vsQRows0 (vsQBm s)).map natList)).wt ≤ _
          omega
        have hm2 : mapK * ((vsQBm s).length + 1) *
            ((Val.list [Val.nat 0, Val.list (List.map (fun M => Val.list (List.map natList M))
              (vsQBm s))]).wt + (vsWVs (vsQRows0 (vsQBm s))).wt + 1) ≤
            1000 * (2 * S ^ 2) * (10 ^ 4 * S ^ 5) := by
          rw [show mapK = 1000 from rfl]
          have := Nat.one_le_pow 2 S hS1
          have := Nat.one_le_pow 3 S hS1
          have w2 := wt_list2_le (.nat 0) (Val.list (List.map (fun M => Val.list (List.map natList M))
            (vsQBm s)))
          have := wt_nat_le 0
          have eBV : (Val.list (List.map (fun M => Val.list (List.map natList M)) (vsQBm s))).wt =
            BmV.wt := rfl
          have q45 : S ^ 4 ≤ S ^ 5 := hS.pow_le (by omega)
          have h15 : 1 ≤ S ^ 5 := Nat.one_le_pow _ _ hS1
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
        have e2 : 1000 * (2 * S ^ 2) * (10 ^ 4 * S ^ 5) = 2 * 10 ^ 7 * S ^ 7 := by ring
        have q7 : S ^ 7 ≤ S ^ 32 := hS.pow_le (by omega)
        have dbasR' : Det P E4 _ (vsWVs RB) (10 ^ 23 * S ^ 32) := dbasR.mono (by
          have := Det.wt_lt dvB4
          have := wt_nat_le 0
          omega)
        refine EvalAll.letE dbasR' fun Rv cR hRv => ?_
        obtain ⟨rfl, hcR⟩ := hRv
        set E5 := E4 ++ [vsWVs RB] with hE5
        have dv5 : Det P E5 (.var 5) (vsWVs RB) ((vsWVs RB).wt + 1) := Det.var' rfl
        have eRl : (RB.map natList).length = RB.length := by simp
        have dlt4 := Det.arith' (op := .lt) (Det.length dv5) (dD _) rfl
        rw [eRl] at dlt4
        have hRbf : VsWFit I.p D RB := vsWBas_fit I.prime.pos hRfit
        have eRsp : vsWSp I.p D RB = vsWSp I.p D (vsQRows0 (vsQBm s)) := vsWBas_span I.prime hRfit
        have hRBl : RB.length ≤ D := by
          rw [hRB, vsWBas_length I.prime hRfit]
          exact (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
        have wRB := vsQ_wt_loc hS hs hRbf (by omega)
        by_cases hlt4 : RB.length < D
        · have ev : GI.Machine.BinOp.lt.eval RB.length D = 1 := by
            simp [GI.Machine.BinOp.eval, hlt4]
          rw [ev] at dlt4
          have dT := dSpl _ _ _ _ dv5 hRbf (by omega)
          refine Det.post (Det.ite_pos dlt4 one_ne_zero dT) fun c hc => ?_
          have wO := vsQSpl_wt hS hs hd2 RB
          refine ⟨hOut _ hRbf (by rw [eRsp]; exact hRbot)
            (by rw [eRsp]; exact vsWSp_ne_top_of_bas I.prime hRfit hlt4)
            (by rw [eRsp]; exact hRinv), by omega, by omega⟩
        · have ev : GI.Machine.BinOp.lt.eval RB.length D = 0 := by
            simp [GI.Machine.BinOp.eval, hlt4]
          rw [ev] at dlt4
          have hRtop : vsWSp I.p D (vsQRows0 (vsQBm s)) = ⊤ := vsWSp_top_of_bas I.prime hRfit (by
            have : D ≤ RB.length := by omega
            exact this)
          have hLb := hfld (vsQBm s) (fun X => (vsQBm_mem s X).trans (by rw [vsQBl_eq s hs]))
            (vsQ_field hs hab hAtop hQ0 hQtop) hRtop hBl hBsq
          have darg := Det.mk2c (P := P) (Det.var' (show E5[0]? = some lc from rfl))
            (Det.var' (show E5[2]? = some BmV from rfl))
          have dF := EvalAll.call_funAll (f := fld) (Q := fun w c =>
              (∃ a, w = vsQLeafV a ∧ VsQAnsOK hs.prob a) ∧
                c ≤ 5 * (lc.wt + 1 + (BmV.wt + 1)) + 20 + CF + 10 ^ 4 * S ^ 6 + 1) darg
            fun v ca hv => by
            obtain ⟨rfl, hca⟩ := hv
            refine hLb.mono fun w cb hw => ⟨hw.1, ?_⟩
            obtain ⟨⟨a, rfl, ha⟩, hcb⟩ := hw
            have := vsQLeaf_wt hS (VsQAnsOK.len ha)
            omega
          refine (EvalAll.vsQ_ite_zero' dlt4 dF).mono fun w c hw => ?_
          obtain ⟨ce, ⟨⟨a, rfl, ha⟩, hce⟩, hc⟩ := hw
          have wO := vsQLeaf_wt hS (VsQAnsOK.len ha)
          refine ⟨Or.inl ⟨a, rfl, ha⟩, by omega, by omega⟩

end GI.Impl
