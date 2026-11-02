import Workspace.Impl.VsWProgNil
import Workspace.Proved.VsWEigCount

/-!
# The joint eigenspace pieces as a program

* `vsFEigFuns b` (153 functions), `vsFEig_spec`: on `[p, D, vsFMatsVal Ss]` the value
  `vsFMatsVal (vsFEigL p D Ss)`. Meaning: `GI.Proved.vsFEigL_pieces`.

The program follows `vsFEigL`: a fold over `Ss`, whose step maps each piece to its split and
then joins the results. The split of a piece `P` by `s` maps `c < p` to the basis of
`span P ∩ ker (s - c)`, and keeps the nonempty ones. The cost bound rests on
`GI.Proved.vsFEigL_count`: there are at most `D` pieces, each with at most `D` vectors.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-! ### Navigating nested blocks -/

theorem _root_.GI.Lang.Program.HasAt.vsWAppL {P : Program} {b : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B)) :
    P.HasAt b A := fun j hj => by
  have := h j (by simp; omega)
  rwa [List.getElem_append_left hj] at this

theorem _root_.GI.Lang.Program.HasAt.vsWAppR {P : Program} {b : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B)) :
    P.HasAt (b + A.length) B := fun j hj => by
  have := h (A.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

theorem _root_.GI.Lang.Program.HasAt.vsWOne {P : Program} {b : ℕ} {e : Expr} (h : P.HasAt b [e]) :
    P.funs[b]? = some e := h.get (j := 0) (by simp)

/-! ### Joining a list of lists -/

theorem vsW_flatten_take_prefix {α : Type} (xss : List (List α)) (i : ℕ) :
    (xss.take i).flatten <+: xss.flatten := by
  conv_rhs => rw [← List.take_append_drop i xss]
  rw [List.flatten_append]
  exact List.prefix_append _ _

/-- **Joining.** `vsWFlatFuns` joins any list of lists, not only the rows of a matrix. -/
theorem vsWConcat_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWFlatFuns b)) {N : ℕ}
    (xss : List (List Val)) (hl : xss.length ≤ N) (hx : ∀ xs ∈ xss, xs.length ≤ N)
    (hW : (Val.list xss.flatten).wt ≤ 1000 * (N + 1) ^ 4)
    (hWi : (Val.list (xss.map .list)).wt ≤ 1000 * (N + 1) ^ 4) :
    FunDet P b (.list (xss.map .list)) (.list xss.flatten) (10 ^ 8 * (N + 1) ^ 6) := by
  have h0 : P.funs[b]? = some (vsWFlatF (b + 1)) := h.get (j := 0) (by simp [vsWFlatFuns])
  have hfo : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hst : P.funs[b + 4]? = some (vsWFlatStepF (b + 5)) :=
    h.get (j := 4) (by rw [vsWFlatFuns_length]; omega)
  have hap : P.HasAt (b + 5) (appendFuns (b + 5)) := h.block 5 rfl
  have hK : loopModK = 1000 := rfl
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have wF : ∀ i, (Val.list (xss.take i).flatten).wt ≤ 1000 * (N + 1) ^ 4 := fun i =>
    (wt_list_mono (vsW_flatten_take_prefix xss i)).trans hW
  have hfold := foldl_spec hfo (c := .list []) (xs := xss.map .list) (acc0 := .list [])
    (Inv := fun i acc => acc = .list (xss.take i).flatten)
    (M := 1000 * (N + 1) ^ 4) (B := fun _ => 2 * 10 ^ 7 * (N + 1) ^ 5) (by simp)
    (fun i acc _ hacc => by subst hacc; exact wF i)
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < xss.length := by simpa using hi
      have hxe : (xss.map Val.list)[i] = .list xss[i] := by simp
      rw [hxe]
      have hxl := hx xss[i] (List.getElem_mem hi')
      have wxi : (Val.list xss[i]).wt ≤ 1000 * (N + 1) ^ 4 :=
        (wt_le_wt_list (List.mem_map_of_mem (f := Val.list) (List.getElem_mem hi'))).le.trans hWi
      set F := (xss.take i).flatten
      have wFi : (Val.list F).wt ≤ 1000 * (N + 1) ^ 4 := wF i
      have a1 := Det.arg' (P := P) (rest := []) (vs := [Val.list [], .list F, .list xss[i]])
        (j := 1) rfl
      have a2 := Det.arg' (P := P) (rest := []) (vs := [Val.list [], .list F, .list xss[i]])
        (j := 2) rfl
      have hF1 : F ++ xss[i] = (xss.take (i + 1)).flatten := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
          List.flatten_append, List.flatten_singleton]
      have wF1 := wF (i + 1)
      rw [← hF1] at wF1
      have kapp : loopModK * (xss[i].length + 1) *
          ((Val.list [.list F, .list xss[i]]).wt + xss[i].length + (Val.list (F ++ xss[i])).wt + 1) ≤
          1000 * (N + 1) * (10000 * (N + 1) ^ 4) := by
        have w2 := wt_list2_le (.list F) (.list xss[i])
        rw [hK]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have dap := Det.call (Det.mk2 a1 a2) ((append_spec hap F xss[i]).mono
        fun w c hw => ⟨hw.1, hw.2.trans (hw.1 ▸ kapp)⟩)
      refine FunAll.mono (FunDet.intro hst (dap.mono le_rfl)) fun w c hw => ⟨?_, ?_⟩
      · beta_reduce; rw [hw.1, hF1]
      · beta_reduce
        refine hw.2.trans ?_
        have w3 := wt_list3_le (.list []) (.list F) (.list xss[i])
        have w2 := wt_list2_le (.list F) (.list xss[i])
        have wn : (Val.list []).wt ≤ 4 := by decide
        have e3 : 1000 * (N + 1) * (10000 * (N + 1) ^ 4) = 10 ^ 7 * (N + 1) ^ 5 := by ring
        omega)
  refine FunDet.intro h0 ((Det.call (Det.mk3 Det.nil (Det.var' (P := P)
    (env := [.list (xss.map .list)]) (i := 0) rfl) Det.nil)
    (hfold.mono fun w c hw => ⟨by rw [hw.1, List.length_map, List.take_length], hw.2⟩)).mono ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map]
  have w3 := wt_list3_le (.list []) (.list (xss.map .list)) (.list [])
  have wn : (Val.list []).wt ≤ 4 := by decide
  have k1 : xss.length * (2 * 10 ^ 7 * (N + 1) ^ 5) ≤ (N + 1) * (2 * 10 ^ 7 * (N + 1) ^ 5) :=
    Nat.mul_le_mul_right _ (by omega)
  have k2 : loopModK * (xss.length + 1) * ((Val.list [.list [], .list (xss.map .list), .list []]).wt +
      xss.length + 1000 * (N + 1) ^ 4 + 1) ≤ 1000 * (N + 1) * (10000 * (N + 1) ^ 4) := by
    rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : (N + 1) * (2 * 10 ^ 7 * (N + 1) ^ 5) = 2 * 10 ^ 7 * (N + 1) ^ 6 := by ring
  have e2 : 1000 * (N + 1) * (10000 * (N + 1) ^ 4) = 10 ^ 7 * (N + 1) ^ 5 := by ring
  have w1 := wt_list3_le (.list []) (.list (xss.map .list)) (.list [])
  have e4 : (Val.list [.list [], .list (xss.map .list), .list []]).wt =
    (Val.list [Val.list [], Val.list (List.map Val.list xss), Val.list []]).wt := rfl
  omega

/-! ### The split of one piece -/

/-- Whether a value is a nonempty list. -/
def vsWNe : Val → Bool
  | .list l => !l.isEmpty
  | _ => true

/-- The test "nonempty", on `[c, x]`. -/
def vsWNeF : Expr := .ite (.length (arg 1)) (.nat 1) (.nat 0)

theorem vsWNe_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsWNeF) (c : Val) (l : List Val) :
    FunDet P f (.list [c, .list l]) (boolVal (vsWNe (.list l)))
      (3 * (Val.list [c, .list l]).wt + 50) := by
  have a1 := Det.arg' (P := P) (rest := []) (vs := [c, .list l]) (j := 1) rfl
  have d := Det.ite' (Det.length a1) (Det.nat (P := P) (env := [.list [c, .list l]]) 1)
    (Det.nat (P := P) (env := [.list [c, .list l]]) 0)
  have e : (if l.length = 0 then Val.nat 0 else Val.nat 1) = boolVal (vsWNe (.list l)) := by
    cases l <;> simp [vsWNe]
  rw [e] at d
  refine FunDet.intro hf (d.mono ?_)
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have wb := wt_boolVal_le (vsWNe (.list l))
  have hl := length_lt_wt_list l
  have hl2 : (Val.list l).wt < (Val.list [c, .list l]).wt := wt_le_wt_list (by simp)
  have : max (Val.nat 1).wt (Val.nat 0).wt ≤ 3 := by
    have := wt_nat_le 1; have := wt_nat_le 0; omega
  omega

theorem vsWNe_filter (l : List (List (List ℕ))) :
    (l.map vsWVs).filter vsWNe = (l.filter fun Q => !Q.isEmpty).map vsWVs := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro Q _
  cases Q <;> rfl

/-- One value `c`, on `[[p, D, s, P], c]`: the basis of `span P ∩ ker (s - c)`. -/
def vsWEigCF (bas cut subC : ℕ) : Expr :=
  .call bas (mk2 (.get (arg 0) (.nat 0)) (.call cut (mk4 (.get (arg 0) (.nat 0))
    (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 3))
    (.call subC (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 2)))))))

theorem vsWEigC_spec {P : Program} {f bas cut subC : ℕ} (hf : P.funs[f]? = some (vsWEigCF bas cut subC))
    (hb : P.HasAt bas (vsWBasFuns bas)) (hc : P.HasAt cut (vsWCutFuns cut))
    (hs : P.HasAt subC (vsWSubCFuns subC)) {p N D c : ℕ} (hp : 1 < p) (hpN : p ≤ N) (hDN : D ≤ N)
    (hcp : c < p) {s Pc : List (List ℕ)} (hsq : GI.Proved.VsWSq p D s)
    (hP : GI.Proved.VsWFit p D Pc) (hPl : Pc.length ≤ N) :
    FunDet P f (.list [.list [.nat p, .nat D, vsWVs s, vsWVs Pc], .nat c])
      (vsWVs (vsWBas p (vsWCut p D Pc (vsWSubC p c s)))) (2 * 10 ^ 10 * (N + 1) ^ 5) := by
  have a0 := Det.arg' (P := P) (rest := [])
    (vs := [.list [.nat p, .nat D, vsWVs s, vsWVs Pc], .nat c]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := [])
    (vs := [.list [.nat p, .nat D, vsWVs s, vsWVs Pc], .nat c]) (j := 1) rfl
  have g k {v : Val} (hv : [Val.nat p, .nat D, vsWVs s, vsWVs Pc][k]? = some v) :=
    Det.get' a0 (Det.nat k) hv
  have hSq := GI.Proved.vsWSubC_fit (c := c) (by omega) hsq
  have dsub := Det.call (Det.mk3 (g 0 rfl) a1 (g 2 rfl)) (vsWSubC_spec hs (by omega) hpN hDN hcp.le hsq)
  have dcut := Det.call (Det.mk4 (g 0 rfl) (g 1 rfl) (g 3 rfl) dsub) (vsWCut_spec hc hp hpN hDN hP hPl hSq)
  have hcf : GI.Proved.VsWFit p D (vsWCut p D Pc (vsWSubC p c s)) := GI.Proved.vsWCut_fit (by omega)
  have hcl := vsWCut_length_le hp hpN hDN hSq hPl
  have dbas := Det.call (Det.mk2 (g 0 rfl) dcut) (vsWBas_spec hb (by omega) hpN hDN hcf (by omega))
  refine FunDet.intro hf (dbas.mono ?_)
  have wS := wt_vsWVs_le (VsWFit.bnd hsq.1 hpN hDN) (show s.length ≤ N + 1 by have := hsq.2; omega)
  have wSq := wt_vsWVs_le (VsWFit.bnd hSq.1 hpN hDN) (show (vsWSubC p c s).length ≤ N + 1 by
    have := hSq.2; omega)
  have wP := wt_vsWVs_le (VsWFit.bnd hP hpN hDN) (show Pc.length ≤ N + 1 by omega)
  have wC := wt_vsWVs_le (VsWFit.bnd hcf hpN hDN) (show (vsWCut p D Pc (vsWSubC p c s)).length ≤ N + 1 by
    omega)
  have hbl : (vsWBas p (vsWCut p D Pc (vsWSubC p c s))).length ≤ N + 1 := by
    have := vsWRows_length_le (by omega) hpN hDN hcf
    simp only [vsWBas, List.length_map]; omega
  have wO := wt_vsWVs_le (VsWFit.bnd (GI.Proved.vsWBas_fit (by omega) hcf) hpN hDN) hbl
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have wc := wt_nat_le c
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have w3 := wt_nat_le 3
  have wA := wt_list4_le (.nat p) (.nat D) (vsWVs s) (vsWVs Pc)
  have wA2 := wt_list2_le (.list [.nat p, .nat D, vsWVs s, vsWVs Pc]) (.nat c)
  have wS3 := wt_list3_le (.nat p) (.nat c) (vsWVs s)
  have wC4 := wt_list4_le (.nat p) (.nat D) (vsWVs Pc) (vsWVs (vsWSubC p c s))
  have wB2 := wt_list2_le (.nat p) (vsWVs (vsWCut p D Pc (vsWSubC p c s)))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The program for one value `c` at base `b` (116 functions). -/
def vsWEigCFuns (b : ℕ) : List Expr :=
  [vsWEigCF (b + 1) (b + 40) (b + 97)] ++ vsWBasFuns (b + 1) ++ vsWCutFuns (b + 40) ++
    vsWSubCFuns (b + 97)

theorem vsWEigCFuns_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWEigCFuns b)) {p N D c : ℕ}
    (hp : 1 < p) (hpN : p ≤ N) (hDN : D ≤ N)
    (hcp : c < p) {s Pc : List (List ℕ)} (hsq : GI.Proved.VsWSq p D s)
    (hP : GI.Proved.VsWFit p D Pc) (hPl : Pc.length ≤ N) :
    FunDet P b (.list [.list [.nat p, .nat D, vsWVs s, vsWVs Pc], .nat c])
      (vsWVs (vsWBas p (vsWCut p D Pc (vsWSubC p c s)))) (2 * 10 ^ 10 * (N + 1) ^ 5) :=
  vsWEigC_spec (h.vsWAppL.vsWAppL.vsWAppL.vsWOne) (h.vsWAppL.vsWAppL.vsWAppR : P.HasAt (b + 1) _)
    (h.vsWAppL.vsWAppR : P.HasAt (b + 40) _) (h.vsWAppR : P.HasAt (b + 97) _) hp hpN hDN hcp hsq hP hPl

/-- The split of one piece, on `[[p, D, s], P]`. -/
def vsWEigSplitF (filt mapC rng : ℕ) : Expr :=
  .call filt (mk2 (.nat 0) (.call mapC (mk2 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (.get (arg 0) (.nat 2)) (arg 1)) (.call rng (.get (arg 0) (.nat 0))))))

/-- The weight of a list of at most `N + 1` pieces, each of at most `N + 1` vectors that fit. -/
theorem wt_vsWPieces_le {p N D : ℕ} (hpN : p ≤ N) (hDN : D ≤ N) {L : List (List (List ℕ))}
    (hL : ∀ Q ∈ L, GI.Proved.VsWFit p D Q ∧ Q.length ≤ N + 1) (hl : L.length ≤ N + 1) :
    (Val.list (L.map vsWVs)).wt ≤ 40 * (N + 1) ^ 4 := by
  have h := vs_wt_list_le_of (L.map vsWVs) (c := 11 * (N + 1) ^ 3 + 4) (by
    intro v hv
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hv
    exact wt_vsWVs_le (VsWFit.bnd (hL Q hQ).1 hpN hDN) (hL Q hQ).2)
  rw [List.length_map] at h
  have k : L.length * (2 * (11 * (N + 1) ^ 3 + 4) + 1) ≤ (N + 1) * (2 * (11 * (N + 1) ^ 3 + 4) + 1) :=
    Nat.mul_le_mul_right _ hl
  have e : (N + 1) * (2 * (11 * (N + 1) ^ 3 + 4) + 1) = 22 * (N + 1) ^ 4 + 9 * (N + 1) := by ring
  have q1 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
  omega

theorem vsWEigSplit_spec {P : Program} {f filt mapC rng ne ci : ℕ}
    (hf : P.funs[f]? = some (vsWEigSplitF filt mapC rng)) (hfi : P.HasAt filt (filterFuns filt ne))
    (hne : P.funs[ne]? = some vsWNeF) (hm : P.HasAt mapC (mapFuns mapC ci))
    (hci : P.HasAt ci (vsWEigCFuns ci)) (hrg : P.HasAt rng (rangeFuns rng)) {p N D : ℕ} (hp : 1 < p) (hpN : p ≤ N)
    (hDN : D ≤ N) {s Pc : List (List ℕ)} (hsq : GI.Proved.VsWSq p D s)
    (hP : GI.Proved.VsWFit p D Pc) (hPl : Pc.length ≤ N) :
    FunDet P f (.list [.list [.nat p, .nat D, vsWVs s], vsWVs Pc]) (vsFMatsVal (vsFEigSplit p D s Pc))
      (3 * 10 ^ 13 * (N + 1) ^ 6) := by
  have a0 := Det.arg' (P := P) (rest := []) (vs := [(Val.list [.nat p, .nat D, vsWVs s]), vsWVs Pc]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [(Val.list [.nat p, .nat D, vsWVs s]), vsWVs Pc]) (j := 1) rfl
  have g k {v : Val} (hv : [Val.nat p, .nat D, vsWVs s][k]? = some v) := Det.get' a0 (Det.nat k) hv
  have drg := Det.call (g 0 rfl) (vsWRange_det hrg hpN)
  set F := fun c => vsWBas p (vsWCut p D Pc (vsWSubC p c s)) with hF
  have dmap := vsQ_map hm (List.range p) Val.nat (fun c => vsWVs (F c)) valNat_injective
    (c := .list [.nat p, .nat D, vsWVs s, vsWVs Pc]) fun c hcm =>
      vsWEigCFuns_spec hci hp hpN hDN (List.mem_range.mp hcm) hsq hP hPl
  have dmc := Det.call (Det.mk2 (Det.mk4 (g 0 rfl) (g 1 rfl) (g 2 rfl) a1) drg) dmap
  have hFf : ∀ c, GI.Proved.VsWFit p D (F c) ∧ (F c).length ≤ N + 1 := fun c => by
    have hcf : GI.Proved.VsWFit p D (vsWCut p D Pc (vsWSubC p c s)) := GI.Proved.vsWCut_fit (by omega)
    refine ⟨GI.Proved.vsWBas_fit (by omega) hcf, ?_⟩
    have := vsWRows_length_le (by omega) hpN hDN hcf
    have := vsWCut_length_le hp hpN hDN (GI.Proved.vsWSubC_fit (c := c) (by omega) hsq) hPl
    simp only [hF, vsWBas, List.length_map]; omega
  have hxs : ∀ x ∈ (List.range p).map (fun c => vsWVs (F c)), x.wt ≤ 11 * (N + 1) ^ 3 + 4 := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    exact wt_vsWVs_le (VsWFit.bnd (hFf c).1 hpN hDN) (hFf c).2
  have hfil := filter_spec hfi (c := .nat 0) (xs := (List.range p).map (fun c => vsWVs (F c)))
    (q := vsWNe) (B := fun x => 3 * (Val.list [.nat 0, x]).wt + 50) fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
      exact vsWNe_spec hne (.nat 0) ((F c).map natList)
  have e1 : ((List.range p).map fun c => vsWVs (F c)).filter vsWNe =
      (vsFEigSplit p D s Pc).map vsWVs := by
    have : (List.range p).map (fun c => vsWVs (F c)) = ((List.range p).map F).map vsWVs := by
      rw [List.map_map]; rfl
    rw [this, vsWNe_filter]
    rfl
  have hK : loopModK = 1000 := rfl
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have w0 := wt_nat_le 0
  have exs : Val.list ((List.range p).map fun c => vsWVs (F c)) =
      Val.list (((List.range p).map F).map vsWVs) := by rw [List.map_map]; rfl
  have wxs : (Val.list ((List.range p).map fun c => vsWVs (F c))).wt ≤ 40 * (N + 1) ^ 4 := by
    rw [exs]
    refine wt_vsWPieces_le hpN hDN (fun Q hQ => ?_) (by simp; omega)
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hQ
    exact hFf c
  have hsp : ∀ Q ∈ vsFEigSplit p D s Pc, GI.Proved.VsWFit p D Q ∧ Q.length ≤ N + 1 := by
    intro Q hQ
    rw [vsFEigSplit, List.mem_filter, List.mem_map] at hQ
    obtain ⟨⟨c, -, rfl⟩, -⟩ := hQ
    exact hFf c
  have hspl : (vsFEigSplit p D s Pc).length ≤ N + 1 := by
    simp only [vsFEigSplit]
    refine (List.length_filter_le _ _).trans ?_
    simp; omega
  have wout := wt_vsWPieces_le hpN hDN hsp hspl
  have hsum : (((List.range p).map fun c => vsWVs (F c)).map
      fun x => 3 * (Val.list [.nat 0, x]).wt + 50).sum ≤ p * (200 * (N + 1) ^ 3) := by
    have := List.sum_le_card_nsmul (((List.range p).map fun c => vsWVs (F c)).map
      fun x => 3 * (Val.list [.nat 0, x]).wt + 50) (200 * (N + 1) ^ 3) (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        have := hxs x hx
        have := wt_list2_le (.nat 0) x
        omega)
    simpa using this
  have hfd : FunDet P filt (.list [.nat 0, .list ((List.range p).map fun c => vsWVs (F c))])
      (vsFMatsVal (vsFEigSplit p D s Pc)) (3 * 10 ^ 5 * (N + 1) ^ 5) :=
    FunAll.mono hfil fun w c hw => by
      have hw1 : w = vsFMatsVal (vsFEigSplit p D s Pc) := by rw [hw.1, e1]; rfl
      refine ⟨hw1, hw.2.trans ?_⟩
      have ew : w.wt = (Val.list ((vsFEigSplit p D s Pc).map vsWVs)).wt := by rw [hw1]; rfl
      have w2 := wt_list2_le (.nat 0) (.list ((List.range p).map fun c => vsWVs (F c)))
      have k1 : p * (200 * (N + 1) ^ 3) ≤ (N + 1) * (200 * (N + 1) ^ 3) :=
        Nat.mul_le_mul_right _ (by omega)
      have k2 : loopModK * (((List.range p).map fun c => vsWVs (F c)).length + 1) *
          ((Val.list [.nat 0, .list ((List.range p).map fun c => vsWVs (F c))]).wt +
            ((List.range p).map fun c => vsWVs (F c)).length + w.wt + 1) ≤
          1000 * (N + 1) * (200 * (N + 1) ^ 4) := by
        rw [hK]
        simp only [List.length_map, List.length_range]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have e2 : (N + 1) * (200 * (N + 1) ^ 3) = 200 * (N + 1) ^ 4 := by ring
      have e3 : 1000 * (N + 1) * (200 * (N + 1) ^ 4) = 2 * 10 ^ 5 * (N + 1) ^ 5 := by ring
      omega
  have dfi := Det.call (Det.mk2 (Det.nat (P := P) (env := [.list [(Val.list [.nat p, .nat D, vsWVs s]), vsWVs Pc]]) 0) dmc) hfd
  refine FunDet.intro hf (dfi.mono ?_)
  have wS := wt_vsWVs_le (VsWFit.bnd hsq.1 hpN hDN) (show s.length ≤ N + 1 by have := hsq.2; omega)
  have wP := wt_vsWVs_le (VsWFit.bnd hP hpN hDN) (show Pc.length ≤ N + 1 by omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have wX := wt_list3_le (.nat p) (.nat D) (vsWVs s)
  have eO : (vsFMatsVal (vsFEigSplit p D s Pc)).wt =
    (Val.list ((vsFEigSplit p D s Pc).map vsWVs)).wt := rfl
  have wX2 := wt_list2_le (Val.list [.nat p, .nat D, vsWVs s]) (vsWVs Pc)
  have wC4 := wt_list4_le (.nat p) (.nat D) (vsWVs s) (vsWVs Pc)
  have wrg := wt_natList_le_sq (B := N) (xs := List.range p) (fun y hy => by simp at hy; omega)
    (by simp; omega)
  have eN : natList (List.range p) = .list ((List.range p).map Val.nat) := rfl
  rw [eN] at wrg
  have wM2 := wt_list2_le (.list [.nat p, .nat D, vsWVs s, vsWVs Pc]) (.list ((List.range p).map Val.nat))
  have wF2 := wt_list2_le (.nat 0) (.list ((List.range p).map fun c => vsWVs (F c)))
  have kmap := vsW_mapCost (N := N) (n := (List.range p).length) (B := 2 * 10 ^ 10 * (N + 1) ^ 5)
    (c := 2 * 10 ^ 10) (k := 5)
    (W := (Val.list [.list [.nat p, .nat D, vsWVs s, vsWVs Pc],
      .list ((List.range p).map Val.nat)]).wt + (Val.list ((List.range p).map fun c => vsWVs (F c))).wt)
    (by simp; omega) le_rfl (by omega)
  have e6 : (N + 1) ^ (5 + 1) = (N + 1) ^ 6 := rfl
  omega

/-! ### One step: split every piece, then join -/

/-- A list of lists weighs at most a constant times the joined list, plus its length. -/
theorem wt_nested_le (xss : List (List Val)) :
    (Val.list (xss.map .list)).wt ≤ 6 * (Val.list xss.flatten).wt + 9 * xss.length + 4 := by
  have h3 : (xss.map fun xs => 2 * (xs.map Val.wt).sum + xs.length + 4).sum =
      2 * (xss.flatten.map Val.wt).sum + xss.flatten.length + 4 * xss.length := by
    induction xss with
    | nil => simp
    | cons xs xss ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.flatten_cons, List.map_append,
        List.sum_append, List.length_append, List.length_cons]
      ring
  have h1 := wt_list_le (xss.map .list)
  have h2 : ((xss.map Val.list).map Val.wt).sum ≤
      (xss.map fun xs => 2 * (xs.map Val.wt).sum + xs.length + 4).sum := by
    rw [List.map_map]
    exact List.sum_le_sum fun xs _ => wt_list_le xs
  have h4 := sum_wt_lt_wt_list xss.flatten
  have h5 := length_lt_wt_list xss.flatten
  simp only [List.length_map] at h1
  omega

/-- One step, on `[[p, D], L, s]`. -/
def vsWEigStepF (concat mapS : ℕ) : Expr :=
  .call concat (.call mapS (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 2)) (arg 1)))

/-- The main function, on `[p, D, Ss]`. -/
def vsFEigF (fo filt id : ℕ) : Expr :=
  .call fo (mk3 (mk2 (arg 0) (arg 1)) (arg 2)
    (.call filt (mk2 (.nat 0) (.snoc .nil (.call id (arg 1))))))

/-- The split program at base `b` (127 functions). -/
def vsWEigSplitFuns (b : ℕ) : List Expr :=
  [vsWEigSplitF (b + 1) (b + 4) (b + 7)] ++ filterFuns (b + 1) (b + 10) ++ mapFuns (b + 4) (b + 11) ++
    rangeFuns (b + 7) ++ [vsWNeF] ++ vsWEigCFuns (b + 11)

theorem vsWEigSplitFuns_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWEigSplitFuns b)) {p N D : ℕ}
    (hp : 1 < p) (hpN : p ≤ N) (hDN : D ≤ N) {s Pc : List (List ℕ)} (hsq : GI.Proved.VsWSq p D s)
    (hP : GI.Proved.VsWFit p D Pc) (hPl : Pc.length ≤ N) :
    FunDet P b (.list [.list [.nat p, .nat D, vsWVs s], vsWVs Pc]) (vsFMatsVal (vsFEigSplit p D s Pc))
      (3 * 10 ^ 13 * (N + 1) ^ 6) :=
  vsWEigSplit_spec h.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWOne (h.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppR : P.HasAt (b + 1) _)
    (h.vsWAppL.vsWAppR.vsWOne : P.funs[b + 10]? = _) (h.vsWAppL.vsWAppL.vsWAppL.vsWAppR : P.HasAt (b + 4) _)
    (h.vsWAppR : P.HasAt (b + 11) _) (h.vsWAppL.vsWAppL.vsWAppR : P.HasAt (b + 7) _) hp hpN hDN hsq hP hPl

/-- The joint eigenspace program at base `b` (153 functions). -/
def vsFEigFuns (b : ℕ) : List Expr :=
  [vsFEigF (b + 1) (b + 17) (b + 143)] ++ foldlFuns (b + 1) (b + 4) ++ [vsWEigStepF (b + 5) (b + 13)] ++
    vsWFlatFuns (b + 5) ++ mapFuns (b + 13) (b + 16) ++ vsWEigSplitFuns (b + 16) ++ vsWIdFuns (b + 143)

theorem vsFEigSplit_length_le (p D : ℕ) (s P : List (List ℕ)) : (vsFEigSplit p D s P).length ≤ p := by
  simp only [vsFEigSplit]
  refine (List.length_filter_le _ _).trans ?_
  simp

theorem vsWEigStep_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFEigFuns b)) {p N D : ℕ}
    (hp : 1 < p) (hpN : p ≤ N) (hDN : D ≤ N) {s : List (List ℕ)} (hsq : GI.Proved.VsWSq p D s)
    {L : List (List (List ℕ))} (hL : ∀ Q ∈ L, GI.Proved.VsWFit p D Q ∧ Q.length ≤ N)
    (hLl : L.length ≤ N)
    (hL' : ∀ Q ∈ L.flatMap (vsFEigSplit p D s), GI.Proved.VsWFit p D Q ∧ Q.length ≤ N + 1)
    (hLl' : (L.flatMap (vsFEigSplit p D s)).length ≤ N + 1) :
    FunDet P (b + 4) (.list [.list [.nat p, .nat D], vsFMatsVal L, vsWVs s])
      (vsFMatsVal (L.flatMap (vsFEigSplit p D s))) (4 * 10 ^ 16 * (N + 1) ^ 7) := by
  have hst : P.funs[b + 4]? = some (vsWEigStepF (b + 5) (b + 13)) :=
    (h.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppR.vsWOne : P.funs[b + 4]? = _)
  have hcat : P.HasAt (b + 5) (vsWFlatFuns (b + 5)) := h.vsWAppL.vsWAppL.vsWAppL.vsWAppR
  have hm : P.HasAt (b + 13) (mapFuns (b + 13) (b + 16)) := h.vsWAppL.vsWAppL.vsWAppR
  have hsp : P.HasAt (b + 16) (vsWEigSplitFuns (b + 16)) := h.vsWAppL.vsWAppR
  have a0 := Det.arg' (P := P) (rest := [])
    (vs := [.list [.nat p, .nat D], vsFMatsVal L, vsWVs s]) (j := 0) rfl
  have a1 : Det P [.list [.list [.nat p, .nat D], vsFMatsVal L, vsWVs s]] (arg 1)
      (.list (L.map vsWVs)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [.list [.nat p, .nat D], vsFMatsVal L, vsWVs s]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := [])
    (vs := [.list [.nat p, .nat D], vsFMatsVal L, vsWVs s]) (j := 2) rfl
  have g0 := Det.get' a0 (Det.nat 0) (show [Val.nat p, .nat D][0]? = some (.nat p) from rfl)
  have g1 := Det.get' a0 (Det.nat 1) (show [Val.nat p, .nat D][1]? = some (.nat D) from rfl)
  have dmap := vsQ_map hm L vsWVs (fun Pc => vsFMatsVal (vsFEigSplit p D s Pc)) vsWVs_injective
    (c := .list [.nat p, .nat D, vsWVs s]) fun Pc hPc =>
      vsWEigSplitFuns_spec hsp hp hpN hDN hsq (hL Pc hPc).1 (hL Pc hPc).2
  have dm := Det.call (Det.mk2 (Det.mk3 g0 g1 a2) a1) dmap
  set xss := L.map fun Pc => (vsFEigSplit p D s Pc).map vsWVs with hxss
  have e1 : Val.list (L.map fun Pc => vsFMatsVal (vsFEigSplit p D s Pc)) = .list (xss.map .list) := by
    simp only [hxss, List.map_map]; rfl
  have e2 : Val.list xss.flatten = vsFMatsVal (L.flatMap (vsFEigSplit p D s)) := by
    rw [hxss, vsFMatsVal, List.flatMap_def, List.map_flatten, List.map_map]
    rfl
  rw [e1] at dm
  have wout := wt_vsWPieces_le hpN hDN hL' hLl'
  have eO : (vsFMatsVal (L.flatMap (vsFEigSplit p D s))).wt =
    (Val.list ((L.flatMap (vsFEigSplit p D s)).map vsWVs)).wt := rfl
  have wfl : (Val.list xss.flatten).wt ≤ 40 * (N + 1) ^ 4 := by rw [e2, eO]; exact wout
  have wnest := wt_nested_le xss
  have hxl : xss.length ≤ N := by simp [hxss]; omega
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q6 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have dcat := Det.call dm (vsWConcat_spec hcat xss hxl (fun xs hxs => by
      obtain ⟨Pc, -, rfl⟩ := List.mem_map.mp hxs
      have := vsFEigSplit_length_le p D s Pc
      simp only [List.length_map]; omega)
    (by omega) (by omega))
  rw [e2] at dcat
  refine FunDet.intro hst (dcat.mono ?_)
  have wL := wt_vsWPieces_le hpN hDN (fun Q hQ => ⟨(hL Q hQ).1, by have := (hL Q hQ).2; omega⟩)
    (by omega)
  have eL : (vsFMatsVal L).wt = (Val.list (L.map vsWVs)).wt := rfl
  have wS := wt_vsWVs_le (VsWFit.bnd hsq.1 hpN hDN) (show s.length ≤ N + 1 by have := hsq.2; omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have wC := wt_list2_le (.nat p) (.nat D)
  have wA := wt_list3_le (.list [.nat p, .nat D]) (vsFMatsVal L) (vsWVs s)
  have wX := wt_list3_le (.nat p) (.nat D) (vsWVs s)
  have wM := wt_list2_le (.list [.nat p, .nat D, vsWVs s]) (.list (L.map vsWVs))
  have kmap := vsW_mapCost (N := N) (n := L.length) (B := 3 * 10 ^ 13 * (N + 1) ^ 6)
    (c := 3 * 10 ^ 13) (k := 6)
    (W := (Val.list [.list [.nat p, .nat D, vsWVs s], .list (L.map vsWVs)]).wt +
      (Val.list (L.map fun Pc => vsFMatsVal (vsFEigSplit p D s Pc))).wt) hLl le_rfl
    (by rw [e1]; omega)
  rw [e1] at kmap
  have e7 : (N + 1) ^ (6 + 1) = (N + 1) ^ 7 := rfl
  omega

theorem vsFEigL_take_succ (p D : ℕ) (Ss : List (List (List ℕ))) {i : ℕ} (hi : i < Ss.length) :
    vsFEigL p D (Ss.take (i + 1)) = (vsFEigL p D (Ss.take i)).flatMap (vsFEigSplit p D Ss[i]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, vsFEigL, vsFEigL,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The pieces after a prefix of `Ss`: few, and each fits with at most `N + 1` vectors. -/
theorem vsFEigL_take_ok {p N D : ℕ} (hp : p.Prime) (hDN : D ≤ N) {Ss : List (List (List ℕ))}
    (hS : ∀ s ∈ Ss, GI.Proved.VsWSq p D s) (i : ℕ) :
    (vsFEigL p D (Ss.take i)).length ≤ N ∧
      ∀ Q ∈ vsFEigL p D (Ss.take i), GI.Proved.VsWFit p D Q ∧ Q.length ≤ N := by
  obtain ⟨h1, h2⟩ := GI.Proved.vsFEigL_count hp (Ss.take i)
    (fun s hs => hS s (List.mem_of_mem_take hs))
  exact ⟨h1.trans hDN, fun Q hQ => ⟨(h2 Q hQ).1, (h2 Q hQ).2.trans hDN⟩⟩

/-- **The joint eigenspace program.** -/
theorem vsFEig_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFEigFuns b)) {p N D : ℕ}
    (hp : p.Prime) (hpN : p ≤ N) (hDN : D ≤ N) {Ss : List (List (List ℕ))}
    (hS : ∀ s ∈ Ss, GI.Proved.VsWSq p D s) (hSl : Ss.length ≤ N) :
    FunDet P b (.list [.nat p, .nat D, vsFMatsVal Ss]) (vsFMatsVal (vsFEigL p D Ss))
      (10 ^ 17 * (N + 1) ^ 8) := by
  have hp1 := hp.one_lt
  have h0 : P.funs[b]? = some (vsFEigF (b + 1) (b + 17) (b + 143)) :=
    (h.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWOne : P.funs[b]? = _)
  have hfo : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := h.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppR
  have hsp : P.HasAt (b + 16) (vsWEigSplitFuns (b + 16)) := h.vsWAppL.vsWAppR
  have hfi : P.HasAt (b + 17) (filterFuns (b + 17) (b + 26)) :=
    hsp.vsWAppL.vsWAppL.vsWAppL.vsWAppL.vsWAppR
  have hne : P.funs[b + 26]? = some vsWNeF := (hsp.vsWAppL.vsWAppR.vsWOne : P.funs[b + 26]? = _)
  have hid : P.HasAt (b + 143) (vsWIdFuns (b + 143)) := h.vsWAppR
  have ar k {v : Val} (hv : [Val.nat p, .nat D, vsFMatsVal Ss][k]? = some v) :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat D, vsFMatsVal Ss]) (j := k) hv
  have a2 : Det P [.list [.nat p, .nat D, vsFMatsVal Ss]] (arg 2) (.list (Ss.map vsWVs)) _ := ar 2 rfl
  -- the start
  have did := Det.call (ar 1 rfl) (vsWId_spec hid hDN)
  have dsn : Det P [.list [.nat p, .nat D, vsFMatsVal Ss]] (.snoc .nil (.call (b + 143) (arg 1)))
      (.list [vsWVs (vsWId D)]) _ := Det.snoc Det.nil did
  have hId : GI.Proved.VsWFit p D (vsWId D) := GI.Proved.vsWId_fit hp1 D
  have wId := wt_vsWVs_le (VsWFit.bnd hId hpN hDN) (show (vsWId D).length ≤ N + 1 by
    simp [vsWId]; omega)
  have hK : loopModK = 1000 := rfl
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q6 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have q7 : (N + 1) ^ 7 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have w0 := wt_nat_le 0
  have hok0 := vsFEigL_take_ok hp hDN hS 0
  have e0 : vsFEigL p D (Ss.take 0) = vsFEig0 D := by simp [vsFEigL]
  rw [e0] at hok0
  have wE0 := wt_vsWPieces_le hpN hDN (fun Q hQ => ⟨(hok0.2 Q hQ).1, by have := (hok0.2 Q hQ).2; omega⟩)
    (by have := hok0.1; omega)
  have hfd : FunDet P (b + 17) (.list [.nat 0, .list [vsWVs (vsWId D)]]) (vsFMatsVal (vsFEig0 D))
      (10 ^ 6 * (N + 1) ^ 4) :=
    FunAll.mono (filter_spec hfi (c := .nat 0) (xs := [vsWVs (vsWId D)]) (q := vsWNe)
      (B := fun x => 3 * (Val.list [.nat 0, x]).wt + 50) fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact vsWNe_spec hne (.nat 0) ((vsWId D).map natList)) fun w c hw => by
      have hw1 : w = vsFMatsVal (vsFEig0 D) := by
        rw [hw.1]
        have := vsWNe_filter [vsWId D]
        simp only [List.map_cons, List.map_nil] at this
        rw [this]; rfl
      refine ⟨hw1, hw.2.trans ?_⟩
      have ew : w.wt = (Val.list ((vsFEig0 D).map vsWVs)).wt := by rw [hw1]; rfl
      have w1 := wt_list2_le (.nat 0) (vsWVs (vsWId D))
      have w2 := wt_list2_le (.nat 0) (.list [vsWVs (vsWId D)])
      have w3 : (Val.list [vsWVs (vsWId D)]).wt ≤ 2 * (vsWVs (vsWId D)).wt + 10 := by
        have := wt_list_le [vsWVs (vsWId D)]; simp at this; omega
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil, hK]
      omega
  have dinit := Det.call (Det.mk2 (Det.nat (P := P) (env := [.list [.nat p, .nat D, vsFMatsVal Ss]]) 0)
    dsn) hfd
  -- the fold
  have hfold := foldl_spec hfo (c := .list [.nat p, .nat D]) (xs := Ss.map vsWVs)
    (acc0 := vsFMatsVal (vsFEig0 D)) (Inv := fun i acc => acc = vsFMatsVal (vsFEigL p D (Ss.take i)))
    (M := 40 * (N + 1) ^ 4) (B := fun _ => 4 * 10 ^ 16 * (N + 1) ^ 7) (by beta_reduce; rw [e0])
    (fun i acc _ hacc => by
      subst hacc
      have hok := vsFEigL_take_ok hp hDN hS i
      have := wt_vsWPieces_le hpN hDN (fun Q hQ => ⟨(hok.2 Q hQ).1, by have := (hok.2 Q hQ).2; omega⟩)
        (by have := hok.1; omega)
      exact this)
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < Ss.length := by simpa using hi
      have hx : (Ss.map vsWVs)[i] = vsWVs Ss[i] := by simp
      rw [hx]
      have hok := vsFEigL_take_ok hp hDN hS i
      have hok' := vsFEigL_take_ok hp hDN hS (i + 1)
      beta_reduce
      rw [vsFEigL_take_succ p D Ss hi'] at hok' ⊢
      exact vsWEigStep_spec h hp1 hpN hDN (hS _ (List.getElem_mem hi')) hok.2 hok.1
        (fun Q hQ => ⟨(hok'.2 Q hQ).1, by have := (hok'.2 Q hQ).2; omega⟩) (by have := hok'.1; omega))
  refine FunDet.intro h0 ((Det.call (Det.mk3 (Det.mk2 (ar 0 rfl) (ar 1 rfl)) a2 dinit)
    (hfold.mono fun w c hw => ⟨by rw [hw.1, List.length_map, List.take_length], hw.2⟩)).mono ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map]
  have wSs := wt_vsWMats_le hpN hDN hS (by omega)
  have hokN := vsFEigL_take_ok hp hDN hS Ss.length
  rw [List.take_length] at hokN
  have wout := wt_vsWPieces_le hpN hDN (fun Q hQ => ⟨(hokN.2 Q hQ).1, by
    have := (hokN.2 Q hQ).2; omega⟩) (by have := hokN.1; omega)
  have eout : (vsFMatsVal (vsFEigL p D Ss)).wt = (Val.list ((vsFEigL p D Ss).map vsWVs)).wt := rfl
  have eSs : (vsFMatsVal Ss).wt = (Val.list (Ss.map vsWVs)).wt := rfl
  have eE0 : (vsFMatsVal (vsFEig0 D)).wt = (Val.list ((vsFEig0 D).map vsWVs)).wt := rfl
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have wA := wt_list3_le (.nat p) (.nat D) (vsFMatsVal Ss)
  have wC := wt_list2_le (.nat p) (.nat D)
  have wF := wt_list3_le (.list [.nat p, .nat D]) (.list (Ss.map vsWVs)) (vsFMatsVal (vsFEig0 D))
  have wI1 : (Val.list [vsWVs (vsWId D)]).wt ≤ 2 * (vsWVs (vsWId D)).wt + 10 := by
    have := wt_list_le [vsWVs (vsWId D)]; simp at this; omega
  have wI2 := wt_list2_le (.nat 0) (.list [vsWVs (vsWId D)])
  have eI : (Val.list ([] ++ [vsWVs (vsWId D)])).wt = (Val.list [vsWVs (vsWId D)]).wt := rfl
  have wn : (Val.list []).wt ≤ 4 := by decide
  have k1 : Ss.length * (4 * 10 ^ 16 * (N + 1) ^ 7) ≤ (N + 1) * (4 * 10 ^ 16 * (N + 1) ^ 7) :=
    Nat.mul_le_mul_right _ (by omega)
  have k2 : loopModK * (Ss.length + 1) * ((Val.list [.list [.nat p, .nat D], .list (Ss.map vsWVs),
      vsFMatsVal (vsFEig0 D)]).wt + Ss.length + 40 * (N + 1) ^ 4 + 1) ≤
      1000 * (N + 1) * (1000 * (N + 1) ^ 4) := by
    rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : (N + 1) * (4 * 10 ^ 16 * (N + 1) ^ 7) = 4 * 10 ^ 16 * (N + 1) ^ 8 := by ring
  have e2 : 1000 * (N + 1) * (1000 * (N + 1) ^ 4) = 10 ^ 6 * (N + 1) ^ 5 := by ring
  omega

end GI.Impl
