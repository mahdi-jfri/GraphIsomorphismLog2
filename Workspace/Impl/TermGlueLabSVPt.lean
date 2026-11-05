module

public import Workspace.Impl.TermGlueLabSVProg

@[expose] public section

/-!
# The label point vector of step 6 (orientation coordinate in front)

Proof of Theorem A.23, the case where every type is distinct. The program
`tmGLSPtFuns` (defined in `Impl/TermGlueLabSVProg.lean`) returns the label vector of
`tmGLSVecFuns` with the parity of `k ↦ J_k` put in front as an integer (`tmGLSPt_spec`, cost
`tmGLSPtC`). With `tmGLS_pt_vec` this is the vector of `Ev(s(z), o(z))` that `tmGLS_call`
needs (`tmGLSPt_lab`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens encInt)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}

/-- The cost bound of the label point vector, for an input of weight `W`. -/
def tmGLSPtC (Cs Ds Cv Dv W : ℕ) : ℕ :=
  10 ^ 7 * (tmGLSVecC Cs Ds Cv Dv W + tmGLPOrC W W + W + 1) ^ 2

private theorem tmGLS_app_ar {c L Y A B : ℕ}
    (hc : c ≤ 1000 * (L + 1) * (A + L + B + 1)) (hL : L < Y) (hA : A ≤ 2 * (100 + Y) + 6)
    (hB : B ≤ 2 * (100 + Y) + Y + 4) : c ≤ 10 ^ 6 * (Y + 1) ^ 2 := by
  have h1 : 1000 * (L + 1) * (A + L + B + 1) ≤ 1000 * ((Y + 1) * (500 * (Y + 1))) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e : (Y + 1) * (500 * (Y + 1)) = 500 * (Y + 1) ^ 2 := by ring
  omega

private theorem tmGLS_pt_ar {c1 c2 c3 w W Y O Ca S : ℕ} (h1 : c1 ≤ W + 1 + 2 * Y + 1)
    (h2 : c2 ≤ 2 * W + 1 + 5 + 2 * O + 1) (h3 : c3 ≤ 500 + (Y + 1) + 4 * (100 + Y) + 19 + 2 * Ca + 1)
    (hw : w < Ca) (hCa : Ca = 10 ^ 6 * (Y + 1) ^ 2) (hS : S = Y + O + W + 1)
    (hYS : (Y + 1) ^ 2 ≤ S ^ 2) (hS1 : S ≤ S ^ 2) :
    c1 + (c2 + c3 + w + 1) + w + 1 ≤ 10 ^ 7 * S ^ 2 := by
  subst hCa hS
  omega

set_option maxHeartbeats 4000000 in
/-- **The label point vector program.** With distinct types and `z` of the type multiset of
`x`, on `[[gens N, ctx], l]` with `l` the pairs of `z`, the result is the list
`encInt (itpNInv ρ % 2) :: (Σ zs) V mod d`, for `ρ` the permutation `k ↦ J_k`. -/
theorem tmGLSPt_spec (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {b cs vec ec add ib jm mul tr red : ℕ} (h : P.HasAt b (tmGLSPtFuns b cs vec))
    (hcs : P.HasAt cs (tmGLPCSumFuns cs ec add)) (hec : linElementCoordinatesAt P ec jm hm)
    (hib : linIntSpec P ib) (hadd : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hvec : P.funs[vec]? = some (tmGLPVecF mul tr red))
    (hmul : linDenseMulAt P mul) (htr : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red))
    {Ce De Cs Ds Cv Dv : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv)
    (σN : List (Perm (Fin n))) (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ)
    (d : Fin σN.length → ℤ) {X Z : Fin q → Ω} (hT : (types (gens σN) X).Nodup)
    (hz : types (gens σN) Z = types (gens σN) X) {l : List Val}
    (hl : TmGLSEnt (gens σN) X Z l) :
    FunAll P b (.list [.list [encGroup σN, tmGLPMCtx U V d], .list l]) (fun w c =>
      ∃ J : Fin q → Fin q, ∃ a : Fin q → Perm (Fin n), (∀ k, a k ∈ gens σN) ∧
        (∀ k, TmGLPFirst (gens σN) X (Z k) (J k)) ∧ (∀ k, X (J k) ↼ a k = Z k) ∧
        ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs ∧
        ∃ ρ : Perm (Fin q), (∀ k, ρ k = J k) ∧
          w = .list (encInt ((itpNInv ρ % 2 : ℕ) : ℤ) ::
            (List.finRange σN.length).map fun i => encInt (Matrix.vecMul zs.sum V i % d i)) ∧
          c ≤ tmGLSPtC Cs Ds Cv Dv
            (Val.list [.list [encGroup σN, tmGLPMCtx U V d], .list l]).wt) := by
  obtain ⟨J0, a0, -, hla, hJ0, -⟩ := tmGLS_ent_choose hl
  obtain ⟨ρ, hρ, -⟩ := tmGLS_or_perm hT hz hJ0
  have hlen : l.length = q := hl.1
  have hf : P.funs[b]? = some (tmGLSPtF (b + 1) (b + 7) (b + 28)) := by
    simpa using (h.block (gs := [tmGLSPtF (b + 1) (b + 7) (b + 28)]) 0 rfl).single
  have hvf : P.HasAt (b + 1) (tmGLSVecFuns (b + 1) cs vec) := h.block 1 rfl
  have hor : P.HasAt (b + 7) (tmGLPOrFuns (b + 7)) := h.block 7 rfl
  have happ : P.HasAt (b + 28) (appendFuns (b + 28)) := h.block 28 rfl
  set c0 : Val := .list [encGroup σN, tmGLPMCtx U V d] with hc0
  set inp : Val := .list [c0, .list l] with hinp
  set W := inp.wt with hW
  set Y := tmGLSVecC Cs Ds Cv Dv W with hY
  set O := tmGLPOrC W W with hO
  have wl : (Val.list l).wt < W := wt_le_wt_list (by simp)
  have hq : q < W := hlen ▸ (length_lt_wt_list l).trans wl
  have hor' := tmGLS_or_spec hor ρ hlen fun i => ⟨a0 i, by rw [hρ]; exact hla i⟩
  have hvec' : FunAll P (b + 1) inp (fun w c => (∃ J : Fin q → Fin q, ∃ a : Fin q → Perm (Fin n),
      (∀ k, a k ∈ gens σN) ∧ (∀ k, TmGLPFirst (gens σN) X (Z k) (J k)) ∧
      (∀ k, X (J k) ↼ a k = Z k) ∧
      ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs ∧
        w = linVecVal (fun i => Matrix.vecMul zs.sum V i % d i)) ∧ c ≤ Y) :=
    (tmGLSVec_spec hm hvf hcs hec hib hadd hvec hmul htr hred hEB hCS hVC σN U V d hl).mono
      fun w c ⟨J, a, ha, hJ, haz, zs, hz, hw, hc⟩ => ⟨⟨J, a, ha, hJ, haz, zs, hz, hw⟩, hc⟩
  have hor'' : FunAll P (b + 7) (.list l) (fun w c => w = .nat (itpNInv ρ % 2) ∧ c ≤ O) :=
    hor'.mono fun w c ⟨hw, hc⟩ => ⟨hw, hc.trans (tmGLS_orC_mono hq.le wl.le)⟩
  clear_value Y O
  apply FunAll.intro hf
  -- the label vector
  have c1 := tmGLP_callAll_le (Det.var' (P := P) (env := [inp]) (i := 0) (v := inp) rfl)
    (A := W + 1) le_rfl hvec'
  refine EvalAll.letE c1 fun v1 c1' h1 => ?_
  obtain ⟨⟨J, a, ha, hJ, haz, zs, hzs, rfl⟩, hc1, hv1⟩ := h1
  obtain ⟨ys, hys⟩ : ∃ ys : List Val,
      ys = (List.finRange σN.length).map fun i => encInt (Matrix.vecMul zs.sum V i % d i) :=
    ⟨_, rfl⟩
  have hv1e : linVecVal (fun i => Matrix.vecMul zs.sum V i % d i) = .list ys := by
    rw [hys]; rfl
  rw [hv1e] at hv1 ⊢
  -- the parity
  have g1 : Det P ([inp] ++ [.list ys]) (arg 1) (.list l) (2 * W + 1 + 5) :=
    Det.arg' (P := P) (vs := [c0, .list l]) (rest := [.list ys]) (j := 1) (v := .list l) rfl
  have c2 := tmGLP_callAll_le g1 (A := 2 * W + 1 + 5) le_rfl hor''
  refine EvalAll.letE c2 fun v2 c2' h2 => ?_
  obtain ⟨rfl, hc2, -⟩ := h2
  -- the bit in front
  have hb2 : itpNInv ρ % 2 < 2 := Nat.mod_lt _ (by omega)
  obtain ⟨dB, wB⟩ := tmGLS_bit_det (P := P)
    (env := [inp, .list ys, .nat (itpNInv ρ % 2)]) hb2 rfl
  have dv1 := Det.var' (P := P) (env := [inp, .list ys, .nat (itpNInv ρ % 2)]) (i := 1) rfl
  have j3 := tmGLP_mk2_le dB le_rfl dv1 (B := Y + 1) (by omega) (X := 100) (Y := Y) wB hv1.le
  have hysl : ys.length < Y := (length_lt_wt_list ys).trans hv1
  have happ : FunAll P (b + 28) (.list [.list [encInt ((itpNInv ρ % 2 : ℕ) : ℤ)], .list ys])
      (fun w c => w = .list (encInt ((itpNInv ρ % 2 : ℕ) : ℤ) :: ys) ∧
        c ≤ 10 ^ 6 * (Y + 1) ^ 2) := by
    refine (append_spec happ _ ys).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
    have hwe := wt_list_le ([encInt ((itpNInv ρ % 2 : ℕ) : ℤ)] ++ ys)
    have hs := sum_wt_lt_wt_list ys
    have he : (encInt ((itpNInv ρ % 2 : ℕ) : ℤ)).wt < 100 :=
      (wt_le_wt_list (by simp)).trans_le wB
    simp only [List.map_append, List.sum_append, List.length_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.length_singleton] at hwe
    rw [hw] at hc
    unfold loopModK at hc
    exact tmGLS_app_ar hc hysl (j3.2.trans (by omega)) (hwe.trans (by omega))
  have c3 := tmGLP_callAll_le j3.1 le_rfl happ
  refine c3.mono fun w c3' ⟨hw, hc3, hww⟩ => ⟨J, a, ha, hJ, haz, zs, hzs, ρ, fun k => ?_, by rw [hw, hys], ?_⟩
  · rw [hρ]; exact tmGLP_first_unique (hJ0 k) (hJ k)
  · unfold tmGLSPtC
    rw [← hY, ← hO]
    have hYS : (Y + 1) ^ 2 ≤ (Y + O + W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hS1 : Y + O + W + 1 ≤ (Y + O + W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact tmGLS_pt_ar hc1 hc2 hc3 hww rfl rfl hYS hS1

variable {A : Type*} [CommGroup A]

/-- **The vector of `tmGLS_call`** (every type distinct). With `Ev` putting the orientation
coordinate in front of `E` (`hEv`, as for `tmGLPEo` by `tmGLS_Eo_apply`), the label point
vector program returns `linVecVal (tmGLVecZ (Ev (s(z), o(z))))`. -/
theorem tmGLSPt_lab (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {b cs vec ec add ib jm mul tr red : ℕ} (h : P.HasAt b (tmGLSPtFuns b cs vec))
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
    (Ev : Additive (tmGLV N φ X × ℤˣ) ≃+
      tmGLVec (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ))
    (hEv : ∀ p : tmGLV N φ X × ℤˣ, Ev (Additive.ofMul p) =
      tmGLPCons 2 (tmGLQMod D) (tmGLPUnits (Additive.ofMul p.2), E (Additive.ofMul p.1)))
    (hT : (types N X).Nodup) (hz : types N Z = types N X) {l : List Val}
    (hl : TmGLSEnt N X Z l) :
    FunAll P b (.list [.list [encGroup σN, tmGLPMCtx U V (fun i => D i i)], .list l]) (fun w c =>
      w = linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLPt N φ X (tmGLPRep N X j0) Z)))) ∧
      c ≤ tmGLSPtC Cs Ds Cv Dv
        (Val.list [.list [encGroup σN, tmGLPMCtx U V (fun i => D i i)], .list l]).wt) := by
  subst hN
  refine (tmGLSPt_spec hm h hcs hec hib hadd hvec hmul htr hred hEB hCS hVC σN U V
    (fun i => D i i) hT hz hl).mono
    fun w c ⟨J, a, ha, hJ, haz, zs, hzs, ρ, hρ, hw, hc⟩ => ⟨?_, hc⟩
  rw [hw, tmGLS_pt_vec j0 rfl hpos E hE Ev hEv hT hz ha hJ haz hzs hρ]

end GI.Impl
