module

public import Workspace.Impl.TermGlueLabSVMath
public import Workspace.Impl.TermGlueLabPXs

@[expose] public section

/-!
# The two label vectors of step 6: the programs

Proof of Theorem A.23. The affine call of step 6 needs the vectors of the label
points of `y'` and of `x` in the coordinates `E` (`tmGLS_call`, `tmGLS_call'`). Both are
computed by the same program from the pairs `[J_k, a_k]` of the string (`TmGLSEnt`), which the
label program already holds: for `x` the output of `tmGLPXLab_spec`, for `y'` the output of
`tmGLPYLab_spec`.

* `tmGLSVecFuns b cs vec` (6 functions), on `[[gens N, ctx], l]` with `ctx = [t, U, V, d]` the
  context of step 5: read the elements `a_k` (a `map`), then the offset-vector program
  `tmGLPOVecF` (coordinate sums, then `(Σ z) V mod d`). Spec `tmGLSVec_spec`, cost
  `tmGLSVecC`. With `tmGLS_lab_vec`, the result is the vector of `E(s(z))`
  (`tmGLSVec_lab`): the vector of `tmGLS_call'` (some type repeats).
* `tmGLSPtFuns b cs vec` (31 functions): the same vector, then the parity of `k ↦ J_k` with the
  orientation program `tmGLPOrFuns` (`tmGLS_or_spec`: it reads only the first entries), then
  the bit put in front as an integer (`append`). Spec `tmGLSPt_spec`, cost `tmGLSPtC`. With
  `tmGLS_pt_vec`, the result is the vector of `Ev(s(z), o(z))` (`tmGLSPt_lab`): the vector of
  `tmGLS_call` (every type distinct).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens encInt)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}

/-! ### The label vector -/

/-- On `[[gens N, ctx], l]`: the elements `a_k` of the pairs, then the offset-vector program. -/
def tmGLSVecF (mp ov : ℕ) : Expr :=
  .letE (.call mp (mk2 .nil (arg 1))) (.call ov (mk2 (arg 0) (.var 1)))

/-- **The label vector program** (6 functions; the coordinate sums at `cs`, the vector program
at `vec`). -/
def tmGLSVecFuns (b cs vec : ℕ) : List Expr :=
  [tmGLSVecF (b + 1) (b + 5)] ++ mapFuns (b + 1) (b + 4) ++ [tmGLPGet1F] ++ [tmGLPOVecF cs vec]

theorem length_tmGLSVecFuns (b cs vec : ℕ) : (tmGLSVecFuns b cs vec).length = 6 := rfl

/-- The cost bound of the label vector, for an input of weight `W`. -/
def tmGLSVecC (Cs Ds Cv Dv W : ℕ) : ℕ :=
  10 ^ 7 * (W + 1) ^ 4 + 3 * tmGLPMPairC Cs Ds Cv Dv (50 * (W + 1) ^ 3)

theorem tmGLS_mpair_mono (Cs Ds Cv Dv : ℕ) {W V : ℕ} (h : W ≤ V) :
    tmGLPMPairC Cs Ds Cv Dv W ≤ tmGLPMPairC Cs Ds Cv Dv V := by
  have hX : tmGLPMPX Cs Ds W ≤ tmGLPMPX Cs Ds V := by
    unfold tmGLPMPX; gcongr
  have hZ : tmGLPMPZ Cs Ds Cv Dv W ≤ tmGLPMPZ Cs Ds Cv Dv V := by
    unfold tmGLPMPZ; gcongr
  unfold tmGLPMPairC
  omega

/-- The entry `a` of a pair `[j, a]`. -/
private theorem tmGLS_get1 {P : Program} {g : ℕ} (hg : P.funs[g]? = some tmGLPGet1F) {W : ℕ}
    (j : ℕ) (s : Perm (Fin n)) (hW : (Val.list [.nat j, encPerm s]).wt < W) :
    FunAll P g (.list [.list [], .list [.nat j, encPerm s]])
      (fun w c => w = encPerm s ∧ c ≤ 10 * W + 50) := by
  have d1 := Det.arg' (P := P) (vs := [.list [], .list [.nat j, encPerm s]]) (rest := [])
    (j := 1) rfl
  have d2 := Det.get' d1 (Det.nat 1) (vs := [.nat j, encPerm s]) (v := encPerm s) rfl
  refine FunAll.intro hg (d2.post fun c hc => ⟨rfl, ?_⟩)
  have w2 := wt_list2_le (.list []) (.list [.nat j, encPerm s])
  have w0 : (Val.list []).wt ≤ 5 := by decide
  have ws : (encPerm s).wt < (Val.list [.nat j, encPerm s]).wt := wt_le_wt_list (by simp)
  omega

private theorem tmGLS_pw_ar {q n W : ℕ} (hq : q ≤ W) (hn : n ≤ W) :
    2 * (q * (4 * (n + 1) ^ 2)) + q + 4 ≤ 20 * (W + 1) ^ 3 := by
  have h1 : q * (4 * (n + 1) ^ 2) ≤ (W + 1) * (4 * (W + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have e : (W + 1) * (4 * (W + 1) ^ 2) = 4 * (W + 1) ^ 3 := by ring
  have h3 : W + 1 ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

/-- The weight of a list of encoded permutations. -/
theorem tmGLS_wt_perms (xs : List (Perm (Fin n))) {W : ℕ} (hq : xs.length ≤ W) (hn : n ≤ W) :
    (Val.list (xs.map encPerm)).wt ≤ 20 * (W + 1) ^ 3 := by
  have h1 := wt_list_le (xs.map encPerm)
  have h2 : ((xs.map encPerm).map Val.wt).sum ≤ xs.length * (4 * (n + 1) ^ 2) := by
    have := List.sum_le_card_nsmul ((xs.map encPerm).map Val.wt) (4 * (n + 1) ^ 2) (by
      simp only [List.map_map, List.mem_map, forall_exists_index, and_imp]
      rintro _ s _ rfl
      exact wt_encPerm_le s)
    simpa using this
  simp only [List.length_map] at h1
  have := tmGLS_pw_ar hq hn
  omega

private theorem tmGLS_map_ar {c q W A B : ℕ}
    (hc : c ≤ q * (10 * W + 50) + 1000 * (q + 1) * (A + B + 1)) (hq : q ≤ W)
    (hA : A ≤ 2 * W + 16) (hB : B ≤ 20 * (W + 1) ^ 3) : c ≤ 10 ^ 6 * (W + 1) ^ 4 := by
  have h3 : W + 1 ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h1 : q * (10 * W + 50) ≤ (W + 1) * (50 * (W + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 1000 * (q + 1) * (A + B + 1) ≤ 1000 * ((W + 1) * (40 * (W + 1) ^ 3)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e1 : (W + 1) * (50 * (W + 1)) = 50 * (W + 1) ^ 2 := by ring
  have e2 : (W + 1) * (40 * (W + 1) ^ 3) = 40 * (W + 1) ^ 4 := by ring
  have h4 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

private theorem tmGLS_vec_ar {c1 cb ww W P3 P4 X C2 : ℕ} (h1 : c1 ≤ 10 * W + 50 + 2 * (10 ^ 6 * P4) + 1)
    (hb : cb ≤ X + 2 * C2 + 1) (hX : X ≤ 200 * P3 + 10 * W + 100) (hw : ww < C2)
    (hP : P3 ≤ P4) (hW : W + 1 ≤ P3) : c1 + cb + ww + 1 ≤ 10 ^ 7 * P4 + 3 * C2 := by
  omega

set_option maxHeartbeats 2000000 in
/-- **The label vector program.** On `[[gens N, ctx], l]` with `l` the pairs of `z`, the
result is `(Σ zs) V mod d` for coordinate vectors `zs` of `1, a_0, …, a_{q-1}`, where
`x_{J_k}^{a_k} = z_k` and `J_k` is the first row of the type of `z_k`. -/
theorem tmGLSVec_spec (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {b cs vec ec add ib jm mul tr red : ℕ} (h : P.HasAt b (tmGLSVecFuns b cs vec))
    (hcs : P.HasAt cs (tmGLPCSumFuns cs ec add)) (hec : linElementCoordinatesAt P ec jm hm)
    (hib : linIntSpec P ib) (hadd : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hvec : P.funs[vec]? = some (tmGLPVecF mul tr red))
    (hmul : linDenseMulAt P mul) (htr : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red))
    {Ce De Cs Ds Cv Dv : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv)
    (σN : List (Perm (Fin n))) (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ)
    (d : Fin σN.length → ℤ) {X Z : Fin q → Ω} {l : List Val} (hl : TmGLSEnt (gens σN) X Z l) :
    FunAll P b (.list [.list [encGroup σN, tmGLPMCtx U V d], .list l]) (fun w c =>
      ∃ J : Fin q → Fin q, ∃ a : Fin q → Perm (Fin n), (∀ k, a k ∈ gens σN) ∧
        (∀ k, TmGLPFirst (gens σN) X (Z k) (J k)) ∧ (∀ k, X (J k) ↼ a k = Z k) ∧
        ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs ∧
          w = linVecVal (fun i => Matrix.vecMul zs.sum V i % d i) ∧
          c ≤ tmGLSVecC Cs Ds Cv Dv
            (Val.list [.list [encGroup σN, tmGLPMCtx U V d], .list l]).wt) := by
  obtain ⟨J, a, ha, hla, hJ, haz⟩ := tmGLS_ent_choose hl
  have hlen : l.length = q := hl.1
  have hf : P.funs[b]? = some (tmGLSVecF (b + 1) (b + 5)) := by
    simpa using (h.block (gs := [tmGLSVecF (b + 1) (b + 5)]) 0 rfl).single
  have hmp : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hg1 : P.funs[b + 4]? = some tmGLPGet1F := (h.block (gs := [tmGLPGet1F]) 4 rfl).single
  have hov : P.funs[b + 5]? = some (tmGLPOVecF cs vec) :=
    (h.block (gs := [tmGLPOVecF cs vec]) 5 rfl).single
  set c0 : Val := .list [encGroup σN, tmGLPMCtx U V d] with hc0
  set inp : Val := .list [c0, .list l] with hinp
  set W := inp.wt with hW
  have wl : (Val.list l).wt < W := wt_le_wt_list (by simp)
  have wc0 : c0.wt < W := wt_le_wt_list (by simp)
  have hn : n < W :=
    (tmGLP_n_lt_encGroup σN).trans ((wt_le_wt_list (by simp)).trans wc0)
  have hq : q < W := hlen ▸ (length_lt_wt_list l).trans wl
  set xs := List.ofFn a with hxs
  have hx : ∀ y ∈ xs, y ∈ gens σN := by
    intro y hy
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
    exact ha k
  -- the map reads the elements `a_k`
  have hget : ∀ x ∈ l, FunAll P (b + 4) (.list [.list [], x]) (fun w c =>
      (∀ (j : ℕ) (s : Perm (Fin n)), x = .list [.nat j, encPerm s] → w = encPerm s) ∧
        c ≤ 10 * W + 50) := by
    intro x hx
    have hxW : x.wt < W := (wt_le_wt_list hx).trans wl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiq : i < q := hlen ▸ hi
    have hxe : l[i] = .list [.nat (J ⟨i, hiq⟩), encPerm (a ⟨i, hiq⟩)] :=
      Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans (hla ⟨i, hiq⟩))
    rw [hxe] at hxW ⊢
    refine (tmGLS_get1 hg1 _ _ hxW).mono fun w c ⟨hw, hc⟩ => ⟨fun j s he => ?_, hc⟩
    simp only [Val.list.injEq, List.cons.injEq] at he
    rw [hw, he.2.1]
  have hmap := map_spec hmp hget
  have hws : ∀ ws : List Val, List.Forall₂ (fun x w => ∀ (j : ℕ) (s : Perm (Fin n)),
      x = .list [.nat j, encPerm s] → w = encPerm s) l ws → ws = xs.map encPerm := by
    intro ws hF
    have hlw := hF.length_eq
    refine List.ext_getElem (by simp [hxs, ← hlw, hlen]) fun i h1 h2 => ?_
    have hiq : i < q := by simpa [hxs] using h2
    have hil : i < l.length := by omega
    have hR := hF.get hil h1
    simp only [List.get_eq_getElem] at hR
    have hxe : l[i] = .list [.nat (J ⟨i, hiq⟩), encPerm (a ⟨i, hiq⟩)] :=
      Option.some.inj ((List.getElem?_eq_getElem hil).symm.trans (hla ⟨i, hiq⟩))
    rw [hR _ _ hxe]
    simp [hxs]
  have wxs : (Val.list (xs.map encPerm)).wt ≤ 20 * (W + 1) ^ 3 :=
    tmGLS_wt_perms xs (by simp [hxs]; omega) hn.le
  have hM : FunAll P (b + 1) (.list [.list [], .list l]) (fun w c =>
      w = .list (xs.map encPerm) ∧ c ≤ 10 ^ 6 * (W + 1) ^ 4) := by
    refine hmap.mono fun w c ⟨ws, hw, hF, hc⟩ => ?_
    have e := hws ws hF
    subst e
    refine ⟨hw, ?_⟩
    rw [hw] at hc
    have hsum : (l.map fun _ => 10 * W + 50).sum = l.length * (10 * W + 50) := by simp
    rw [hsum, hlen] at hc
    have w2 := wt_list2_le (.list []) (.list l)
    have w0 : (Val.list []).wt ≤ 5 := by decide
    exact tmGLS_map_ar hc hq.le (by omega) wxs
  apply FunAll.intro hf
  have d0 := Det.mk2 (Det.nil (P := P) (env := [inp]))
    (Det.arg' (P := P) (vs := [c0, .list l]) (rest := []) (j := 1) rfl)
  have w2 := wt_list2_le (.list []) (.list l)
  have w0 : (Val.list []).wt ≤ 5 := by decide
  have c1 := tmGLP_callAll_le d0 (A := 10 * W + 50) (by rw [← hinp, ← hW]; omega) hM
  refine EvalAll.letE c1 fun v1 c1' h1 => ?_
  obtain ⟨rfl, hc1, -⟩ := h1
  -- the offset-vector program on `[[gens N, ctx], [a_k]]`
  have g0 := Det.arg' (P := P) (vs := [c0, .list l]) (rest := [.list (xs.map encPerm)])
    (j := 0) (v := c0) rfl
  have dv1 := Det.var' (P := P) (env := [inp, .list (xs.map encPerm)]) (i := 1) rfl
  have hP3 : W + 1 ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hP4 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have j1 := tmGLP_mk2_le g0 (A := 2 * W + 5) (by rw [← hinp, ← hW]) dv1
    (B := 20 * (W + 1) ^ 3 + 1) (by omega) (X := W) (Y := 20 * (W + 1) ^ 3) wc0.le wxs
  have hov' : FunAll P (b + 5) (.list [c0, .list (xs.map encPerm)]) (fun w c =>
      (∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: xs) zs ∧
        w = linVecVal (fun i => Matrix.vecMul zs.sum V i % d i)) ∧
      c ≤ tmGLPMPairC Cs Ds Cv Dv (50 * (W + 1) ^ 3)) := by
    refine (tmGLPOVec_spec hm hov hcs hec hib hadd hvec hmul htr hred hEB hCS hVC σN U V d xs
      hx).mono fun w c ⟨zs, hz, hw, hc⟩ => ⟨⟨zs, hz, hw⟩, hc.trans ?_⟩
    exact tmGLS_mpair_mono _ _ _ _ (j1.2.trans (by omega))
  have c2 := tmGLP_callAll_le j1.1 le_rfl hov'
  refine c2.mono fun w cb ⟨⟨zs, hz, hw⟩, hcb, hww⟩ => ⟨J, a, ha, hJ, haz, zs, hz, hw, ?_⟩
  unfold tmGLSVecC
  exact tmGLS_vec_ar hc1 hcb (by omega) hww hP4 hP3

/-! ### The orientation of a list of pairs -/

set_option maxHeartbeats 2000000 in
/-- **The orientation program on any list of pairs.** If entry `i` of `l` is `[ρ i, s_i]` for a
permutation `ρ`, the program `tmGLPOrFuns` returns `itpNInv ρ % 2`. (It reads only the first
entries; `tmGLPOr_spec` is the case of the transporters.) -/
theorem tmGLS_or_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPOrFuns b)) {q : ℕ}
    (ρ : Perm (Fin q)) {l : List Val} (hlen : l.length = q)
    (hlρ : ∀ i : Fin q, ∃ s : Perm (Fin n), l[i.1]? = some (.list [.nat (ρ i), encPerm s])) :
    FunAll P b (.list l) (fun w c => w = .nat (itpNInv ρ % 2) ∧
      c ≤ tmGLPOrC q (Val.list l).wt) := by
  have hf : P.funs[b]? = some (tmGLPOrF (b + 1) (b + 5)) := by
    simpa using (h.block (gs := [tmGLPOrF (b + 1) (b + 5)]) 0 rfl).single
  have hmp : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hg0 : P.funs[b + 4]? = some tmGLPGet0F := (h.block (gs := [tmGLPGet0F]) 4 rfl).single
  have hpar : P.HasAt (b + 5) (tmGLPParFuns (b + 5)) := h.block 5 rfl
  set W := (Val.list l).wt with hW
  have hget : ∀ x ∈ l, FunAll P (b + 4) (.list [.list [], x]) (fun w c =>
      (∀ (j : ℕ) (s : Perm (Fin n)), x = .list [.nat j, encPerm s] → w = .nat j) ∧
        c ≤ 10 * W + 50) := by
    intro x hx
    have hxW : x.wt < W := wt_le_wt_list hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiq : i < q := hlen ▸ hi
    obtain ⟨s, hs⟩ := hlρ ⟨i, hiq⟩
    have hxe : l[i] = .list [.nat (ρ ⟨i, hiq⟩), encPerm s] :=
      Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hs)
    rw [hxe] at hxW ⊢
    have d1 := Det.arg' (P := P) (vs := [.list [], .list [.nat (ρ ⟨i, hiq⟩), encPerm s]])
      (rest := []) (j := 1) rfl
    have d2 := Det.get' d1 (Det.nat 0) (vs := [.nat (ρ ⟨i, hiq⟩), encPerm s])
      (v := .nat (ρ ⟨i, hiq⟩)) rfl
    refine FunAll.intro hg0 (d2.post fun c hc => ⟨fun j s' he => ?_, ?_⟩)
    · simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq] at he
      rw [he.1]
    · have w2 := wt_list2_le (.list []) (.list [.nat (ρ ⟨i, hiq⟩), encPerm s])
      have w0 : (Val.list []).wt ≤ 5 := by decide
      have wj : (Val.nat (ρ ⟨i, hiq⟩)).wt <
          (Val.list [.nat (ρ ⟨i, hiq⟩), encPerm s]).wt := wt_le_wt_list (by simp)
      omega
  have hm := map_spec hmp hget
  have hws : ∀ ws : List Val, List.Forall₂ (fun x w => ∀ (j : ℕ) (s : Perm (Fin n)),
      x = .list [.nat j, encPerm s] → w = .nat j) l ws → Val.list ws = encPerm ρ := by
    intro ws hF
    have hlw := hF.length_eq
    unfold encPerm
    congr 1
    refine List.ext_getElem (by simp [← hlw, hlen]) fun i h1 h2 => ?_
    have hiq : i < q := by simpa using h2
    obtain ⟨s, hs⟩ := hlρ ⟨i, hiq⟩
    have hil : i < l.length := by omega
    have hR := hF.get hil h1
    simp only [List.get_eq_getElem] at hR
    have hxe : l[i] = .list [.nat (ρ ⟨i, hiq⟩), encPerm s] :=
      Option.some.inj ((List.getElem?_eq_getElem hil).symm.trans hs)
    rw [hR _ _ hxe]
    simp
  have wl := length_lt_wt_list l
  have hpw := wt_encPerm_le ρ
  apply FunAll.intro hf
  have dinner : EvalAll P [.list l] (.call (b + 1) (mk2 .nil (.var 0))) (fun w c =>
      w = encPerm ρ ∧ c ≤ 10 ^ 5 * (W + 1) ^ 3) := by
    refine EvalAll.call_funAll (Det.mk2 Det.nil (Det.var' (P := P) (env := [.list l]) (i := 0)
      (v := .list l) rfl)) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hm.mono fun w c ⟨ws, hw, hF, hc⟩ => ⟨hw.trans (hws ws hF), ?_⟩
    subst hw
    have hwt : (Val.list ws).wt = (encPerm ρ).wt := congrArg Val.wt (hws ws hF)
    have hsum : (l.map fun _ => 10 * W + 50).sum = l.length * (10 * W + 50) := by simp
    rw [hsum] at hc
    have w2 := wt_list2_le (.list []) (.list l)
    have w0 : (Val.list []).wt ≤ 5 := by decide
    have hq2 : (q + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hS3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : l.length * (10 * W + 50) ≤ (W + 1) * (50 * (W + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : mapK * (l.length + 1) *
        ((Val.list [.list [], .list l]).wt + (Val.list ws).wt + 1) ≤
        1000 * ((W + 1) * (30 * (W + 1) ^ 2)) := by
      rw [Nat.mul_assoc]; unfold mapK
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e1 : (W + 1) * (50 * (W + 1)) = 50 * (W + 1) ^ 2 := by ring
    have e2 : (W + 1) * (30 * (W + 1) ^ 2) = 30 * (W + 1) ^ 3 := by ring
    have hfin := hc.trans (Nat.add_le_add h1 h2)
    rw [e1, e2] at hfin
    clear hc h1 h2
    omega
  refine EvalAll.call_funAll dinner fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine FunAll.mono (tmGLP_par_spec hpar ρ) fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  subst hw
  have : (Val.nat (itpNInv ρ % 2)).wt ≤ 3 := by
    have := wt_nat_le (itpNInv ρ % 2)
    have := Nat.mod_lt (itpNInv ρ) (show 2 > 0 by omega)
    omega
  have : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold tmGLPOrC
  omega

theorem tmGLS_orC_mono {q q' W W' : ℕ} (hq : q ≤ q') (hW : W ≤ W') :
    tmGLPOrC q W ≤ tmGLPOrC q' W' := by
  unfold tmGLPOrC itParC
  gcongr

/-! ### The label point vector (orientation coordinate in front) -/

/-- The bit `b` as the integer `encInt b`: `[0, []]` or `[0, [1]]`. -/
def tmGLSBitE : Expr := Expr.mkList [mk2 (.nat 0) (.ite (.var 2) (Expr.mkList [.nat 1]) .nil)]

/-- On `[[gens N, ctx], l]`: the label vector (at `vf`), the parity (at `orf`), and the bit put
in front (append at `app`). -/
def tmGLSPtF (vf orf app : ℕ) : Expr :=
  .letE (.call vf (.var 0)) (.letE (.call orf (arg 1)) (.call app (mk2 tmGLSBitE (.var 1))))

/-- **The label point vector program** (31 functions). -/
def tmGLSPtFuns (b cs vec : ℕ) : List Expr :=
  [tmGLSPtF (b + 1) (b + 7) (b + 28)] ++ tmGLSVecFuns (b + 1) cs vec ++ tmGLPOrFuns (b + 7) ++
    appendFuns (b + 28)

theorem length_tmGLSPtFuns (b cs vec : ℕ) : (tmGLSPtFuns b cs vec).length = 31 := rfl

/-- The bit, as a deterministic expression of constant cost. -/
theorem tmGLS_bit_det {P : Program} {env : List Val} {b : ℕ} (hb : b < 2)
    (he : env[2]? = some (.nat b)) :
    Det P env tmGLSBitE (.list [encInt (b : ℤ)]) 500 ∧ (Val.list [encInt (b : ℤ)]).wt ≤ 100 := by
  have dv := Det.var' (P := P) he
  have d1 : Det P env (Expr.mkList [.nat 1]) (.list ([] ++ [.nat 1])) _ :=
    Det.snoc Det.nil (Det.nat 1)
  have di := Det.ite' dv d1 Det.nil
  have dm := Det.mk2 (Det.nat 0) di
  have dl : Det P env tmGLSBitE (.list ([] ++ [Val.list [.nat 0,
      if b = 0 then .list [] else .list ([] ++ [.nat 1])]])) _ := Det.snoc Det.nil dm
  have e : Val.list ([] ++ [Val.list [.nat 0, if b = 0 then .list [] else .list ([] ++ [.nat 1])]])
      = .list [encInt (b : ℤ)] := by
    rw [List.nil_append, List.nil_append, tmGLS_bit_enc hb]
  rw [e] at dl
  refine ⟨dl.mono ?_, ?_⟩ <;> interval_cases b <;> decide

/-! ### The exact values -/

variable {A : Type*} [CommGroup A]

/-- **The vector of `tmGLS_call'`** (some type repeats). With `E(class of w) = w V mod D`,
`d i = D i i` and `z` of the type multiset of `x`, the label vector program returns
`linVecVal (tmGLVecZ (E (s(z))))`, the label of `z` with the first-row representatives. -/
theorem tmGLSVec_lab (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {b cs vec ec add ib jm mul tr red : ℕ} (h : P.HasAt b (tmGLSVecFuns b cs vec))
    (hcs : P.HasAt cs (tmGLPCSumFuns cs ec add)) (hec : linElementCoordinatesAt P ec jm hm)
    (hib : linIntSpec P ib) (hadd : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hvec : P.funs[vec]? = some (tmGLPVecF mul tr red))
    (hmul : linDenseMulAt P mul) (htr : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red))
    {Ce De Cs Ds Cv Dv : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv)
    {N : Subgroup (Perm (Fin n))} {φ : N →* A} {X Z : Fin q → Ω} (j0 : Fin q)
    {σN : List (Perm (Fin n))} (hN : gens σN = N)
    (U : Matrix (Fin σN.length) (Fin σN.length) ℤ)
    {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (E : Additive (tmGLV N φ X) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ w, E (tmGLPg N φ X (fun i => σN[i.val]) w) = tmGLQMap V D w)
    (hz : types N Z = types N X) {l : List Val} (hl : TmGLSEnt N X Z l) :
    FunAll P b (.list [.list [encGroup σN, tmGLPMCtx U V (fun i => D i i)], .list l]) (fun w c =>
      w = linVecVal (tmGLVecZ (E (Additive.ofMul (tmGLLab N φ X (tmGLPRep N X j0) Z)))) ∧
      c ≤ tmGLSVecC Cs Ds Cv Dv
        (Val.list [.list [encGroup σN, tmGLPMCtx U V (fun i => D i i)], .list l]).wt) := by
  subst hN
  refine (tmGLSVec_spec hm h hcs hec hib hadd hvec hmul htr hred hEB hCS hVC σN U V
    (fun i => D i i) hl).mono fun w c ⟨J, a, ha, hJ, haz, zs, hzs, hw, hc⟩ => ⟨?_, hc⟩
  rw [hw, tmGLS_lab_vec j0 rfl hpos E hE hz ha hJ haz hzs]

end GI.Impl
