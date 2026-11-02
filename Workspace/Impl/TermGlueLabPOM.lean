import Workspace.Impl.TermGlueLabPGenM
import Workspace.Impl.TermGlueLabPE
import Workspace.CitedChecks.AlgoTerminalChecks

/-!
# The orientation coordinate in the items (step 5, all types distinct)

Step 5 of the label program (proof of Theorem A.23). When all types of `x` are
distinct, the affine procedure acts on `A/B(x) × C₂`: the extra coordinate is the orientation
`ε`. With coordinates `E` of `A/B(x)`, the coordinates of `A/B(x) × C₂` are
`E_o = (ℤˣ ≅ ℤ/2) × E` with the orientation in front (`tmGLPEoOf E`, moduli `(2, d)`). Here:

* `tmGLP_ρO_cons`: the linear part fixes the orientation coordinate, so in `E_o`-coordinates the
  matrix of `ρ(g)` is the block matrix `[[1, 0], [0, M]]` with `M` the matrix in
  `E`-coordinates (`tmGLP_mat_blk`, `tmGLPBlk`);
* `tmGLP_cO_vec`: the offset of `g` is `(ε(g⁻¹), c(g))`, with `ε(g⁻¹)` read in `ℤ/2`
  (`tmGLPEc`);
* `tmGLP_genO_item`: the item computed by the orientation program (`TmGLPGenOOut`) is the
  contract's item `tmGLAffItem` for `E_o`, `tmGLlamO` and `tmGLoO`.
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Algorithm (State)
open GI.Cited (Val encInt encPerm encGroup encIntMatrix gens)
open GI.Lang (linVecVal encPerm_injective)

/-! ### Coordinates with the orientation in front -/

/-- `E_o`: the orientation coordinate `ℤˣ ≅ ℤ/2` in front of `E`. -/
noncomputable def tmGLPEoOf {Y : Type*} [CommGroup Y] {t : ℕ} {m : Fin t → ℕ}
    (E : Additive Y ≃+ tmGLVec m) :
    Additive (Y × ℤˣ) ≃+ tmGLVec (Fin.cons 2 m : Fin (t + 1) → ℕ) :=
  (tmGLPAddProd _ _).trans (AddEquiv.prodComm.trans ((AddEquiv.prodCongr tmGLPUnits E).trans
    (tmGLPCons 2 m)))

theorem tmGLP_rce_val {a b : ℕ} (h : a = b) (z : ZMod a) : (ZMod.ringEquivCongr h z).val = z.val := by
  subst h; rw [ZMod.ringEquivCongr_refl_apply]

theorem tmGLP_cons_val0 {t : ℕ} (k : ℕ) (m : Fin t → ℕ) (p : ZMod k × tmGLVec m) :
    (tmGLPCons k m p 0).val = p.1.val := by
  simp only [tmGLPCons, AddEquiv.coe_mk, Equiv.coe_fn_mk, Fin.cases_zero]
  exact tmGLP_rce_val _ _

theorem tmGLP_cons_valS {t : ℕ} (k : ℕ) (m : Fin t → ℕ) (p : ZMod k × tmGLVec m) (j : Fin t) :
    (tmGLPCons k m p j.succ).val = (p.2 j).val := by
  simp only [tmGLPCons, AddEquiv.coe_mk, Equiv.coe_fn_mk, Fin.cases_succ]
  exact tmGLP_rce_val _ _

/-- The reduced coordinates of `(a, v)` are `a` followed by those of `v`. -/
theorem tmGLP_vecZ_cons {t : ℕ} (k : ℕ) (m : Fin t → ℕ) (p : ZMod k × tmGLVec m) :
    tmGLVecZ (tmGLPCons k m p) = Fin.cons ((p.1.val : ℕ) : ℤ) (tmGLVecZ p.2) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [tmGLVecZ, Fin.cons_zero, tmGLP_cons_val0]
  · simp only [tmGLVecZ, Fin.cons_succ, tmGLP_cons_valS]

theorem tmGLP_EoOf_apply {Y : Type*} [CommGroup Y] {t : ℕ} {m : Fin t → ℕ}
    (E : Additive Y ≃+ tmGLVec m) (y : Y) (u : ℤˣ) :
    tmGLPEoOf E (Additive.ofMul (y, u)) =
      tmGLPCons 2 m (tmGLPUnits (Additive.ofMul u), E (Additive.ofMul y)) := rfl

theorem tmGLP_EoOf_symm {Y : Type*} [CommGroup Y] {t : ℕ} {m : Fin t → ℕ}
    (E : Additive Y ≃+ tmGLVec m) (p : ZMod 2 × tmGLVec m) :
    (tmGLPEoOf E).symm (tmGLPCons 2 m p) =
      Additive.ofMul (Additive.toMul (E.symm p.2), Additive.toMul (tmGLPUnits.symm p.1)) := by
  rw [AddEquiv.symm_apply_eq, tmGLP_EoOf_apply]
  simp

/-! ### The block matrix -/

/-- The block matrix `[[1, 0], [0, B]]`. -/
def tmGLPBlk {t : ℕ} (B : Matrix (Fin t) (Fin t) ℤ) : Matrix (Fin (t + 1)) (Fin (t + 1)) ℤ :=
  Fin.cons (Fin.cons 1 0) fun i => Fin.cons 0 (B i)

section Kappa

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}
  {x : Fin q → Ω}
variable {hn : Normalizes H N} {hker : TmGLKer N H φ} {hNH : N ≤ H}
variable {gs : List (Perm (Fin n))} {hgs : gens gs ≤ Aut H (types N x)}

/-- **The linear part fixes the orientation coordinate.** -/
theorem tmGLP_ρO_cons {t : ℕ} {m : Fin t → ℕ} (E : Additive (tmGLV N φ x) ≃+ tmGLVec m)
    (h : gens gs) (p : ZMod 2 × tmGLVec m) :
    tmGLρE (tmGLPEoOf E) (tmGLlamO hn hker hgs hNH) h (tmGLPCons 2 m p) =
      tmGLPCons 2 m (p.1, tmGLρE E (tmGLlam hn hker hgs hNH) h p.2) := by
  change tmGLPEoOf E (MulEquiv.toAdditive (tmGLlamO hn hker hgs hNH h)
    ((tmGLPEoOf E).symm (tmGLPCons 2 m p))) = _
  rw [tmGLP_EoOf_symm]
  change tmGLPEoOf E (Additive.ofMul (tmGLlam hn hker hgs hNH h (Additive.toMul (E.symm p.2)),
    Additive.toMul (tmGLPUnits.symm p.1))) = _
  rw [tmGLP_EoOf_apply]
  simp only [ofMul_toMul, AddEquiv.apply_symm_apply]
  rfl

/-- The basis vectors of `ℤ/2 × ∏ ℤ/m_i` in the `Fin.cons` coordinates. -/
theorem tmGLP_single_zero {t : ℕ} (m : Fin t → ℕ) :
    (Pi.single 0 1 : tmGLVec (Fin.cons 2 m : Fin (t + 1) → ℕ)) = tmGLPCons 2 m (1, 0) := by
  rw [← (tmGLPCons 2 m).apply_symm_apply (Pi.single 0 1)]
  congr 1
  refine Prod.ext ?_ ?_
  · change ZMod.ringEquivCongr _ ((Pi.single 0 1 : tmGLVec (Fin.cons 2 m : Fin (t + 1) → ℕ)) 0) = 1
    rw [Pi.single_eq_same, map_one]
  · funext j
    change ZMod.ringEquivCongr _ ((Pi.single 0 1 : tmGLVec (Fin.cons 2 m : Fin (t + 1) → ℕ)) j.succ) = 0
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero j), map_zero]

theorem tmGLP_single_succ {t : ℕ} (m : Fin t → ℕ) (j : Fin t) :
    (Pi.single j.succ 1 : tmGLVec (Fin.cons 2 m : Fin (t + 1) → ℕ)) =
      tmGLPCons 2 m (0, Pi.single j 1) := by
  rw [← (tmGLPCons 2 m).apply_symm_apply (Pi.single j.succ 1)]
  congr 1
  refine Prod.ext ?_ ?_
  · change ZMod.ringEquivCongr _
      ((Pi.single j.succ 1 : tmGLVec (Fin.cons 2 m : Fin (t + 1) → ℕ)) 0) = 0
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero j).symm, map_zero]
  · funext j'
    change ZMod.ringEquivCongr _
      ((Pi.single j.succ 1 : tmGLVec (Fin.cons 2 m : Fin (t + 1) → ℕ)) j'.succ) = _
    by_cases hj : j' = j
    · subst hj
      rw [Pi.single_eq_same, map_one]
      simp
    · rw [Pi.single_eq_of_ne ((Fin.succ_injective _).ne hj), map_zero]
      simp [Pi.single_eq_of_ne hj]

/-- **The matrix with the orientation coordinate is the block matrix.** -/
theorem tmGLP_mat_blk {t : ℕ} {m : Fin t → ℕ} (E : Additive (tmGLV N φ x) ≃+ tmGLVec m)
    (h : gens gs) :
    tmGLMat (Fin.cons 2 m : Fin (t + 1) → ℕ)
        (tmGLρE (tmGLPEoOf E) (tmGLlamO hn hker hgs hNH) h).toAddMonoidHom =
      tmGLPBlk (tmGLMat m (tmGLρE E (tmGLlam hn hker hgs hNH) h).toAddMonoidHom) := by
  funext i j
  simp only [tmGLMat, AddEquiv.coe_toAddMonoidHom]
  refine Fin.cases ?_ (fun j' => ?_) j
  · rw [tmGLP_single_zero, tmGLP_ρO_cons]
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [tmGLP_cons_val0]; simp [tmGLPBlk]; rfl
    · rw [tmGLP_cons_valS]; simp [tmGLPBlk]
  · rw [tmGLP_single_succ, tmGLP_ρO_cons]
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [tmGLP_cons_val0]; simp [tmGLPBlk]
    · rw [tmGLP_cons_valS]; simp [tmGLPBlk]; rfl

/-- The orientation of `h` read in `ℤ/2`, as a number. -/
noncomputable def tmGLPEc (N : Subgroup (Perm (Fin n))) (x : Fin q → Ω) (h : Perm (Fin n)) : ℕ :=
  (tmGLPUnits (Additive.ofMul (tmGLε N x h))).val

/-- **The offset with the orientation coordinate**: `(ε(g⁻¹), c(g))`. -/
theorem tmGLP_cO_vec {t : ℕ} {m : Fin t → ℕ} (E : Additive (tmGLV N φ x) ≃+ tmGLVec m)
    (rep : Set Ω → Ω) (k : Perm (Fin n) → Fin q → Perm (Fin n)) (h : gens gs) :
    tmGLVecZ (tmGLcE (tmGLPEoOf E) (tmGLoO (N := N) (φ := φ) (x := x) (gs := gs) rep k) h) =
      Fin.cons ((tmGLPEc N x (h : Perm (Fin n))⁻¹ : ℕ) : ℤ)
        (tmGLVecZ (tmGLcE E (tmGLo (N := N) (φ := φ) (x := x) (gs := gs) rep k) h)) := by
  simp only [tmGLcE]
  rw [tmGLoO, tmGLo, tmGLP_EoOf_apply, tmGLP_vecZ_cons]
  rfl

end Kappa

/-! ### Encodings with the extra coordinate -/

/-- Put `v` in front of a list value. -/
def tmGLPConsV (v : Val) : Val → Val
  | .list l => .list (v :: l)
  | w => w

theorem tmGLP_linVec_cons {t : ℕ} (a : ℤ) (v : Fin t → ℤ) :
    linVecVal (Fin.cons a v : Fin (t + 1) → ℤ) = tmGLPConsV (encInt a) (linVecVal v) := by
  simp [linVecVal, tmGLPConsV, List.finRange_succ, List.map_map, Function.comp_def]

theorem tmGLP_enc_blk {t : ℕ} (B : Matrix (Fin t) (Fin t) ℤ) :
    encIntMatrix (tmGLPBlk B) = .list (.list (encInt 1 :: List.replicate t (encInt 0)) ::
      (List.finRange t).map fun i => .list (encInt 0 :: (List.finRange t).map fun j => encInt (B i j))) := by
  simp [encIntMatrix, tmGLPBlk, List.finRange_succ, List.map_map, Function.comp_def,
    List.map_const']

/-! ### The item with the orientation coordinate -/

theorem tmGLP_encIntMatrix_inj {r c : ℕ} {A B : Matrix (Fin r) (Fin c) ℤ}
    (h : encIntMatrix A = encIntMatrix B) : A = B :=
  GI.CitedChecks.terminal_encIntMatrix_injective h

variable {n : ℕ}

/-- **The facts of the item of `g` with the orientation coordinate**: the facts `TmGLPGenOut`
for the inner item `[M₁, c₁, M₂, c₂]`, and the item
`[[[1,0],[0,M₁]], (ε(g⁻¹), c₁), [[1,0],[0,M₂]], (ε(g), c₂)]`. -/
def TmGLPGenOOut {Ω C : Type} {S : State Ω C} {L : GI.Algorithm.GiantLabels S} {m : ℕ}
    (E : Fin m × Fin L.q ≃ S.dom) (i0 : Fin L.q) {Ω' : Type}
    [GI.Multicoset.RAct (Perm (Fin m)) Ω'] (σN : List (Perm (Fin m))) (X : Fin L.q → Ω')
    (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ) (g : Perm (Fin m))
    (w : Val) : Prop :=
  ∃ (C₁ C₂ : Matrix (Fin σN.length) (Fin σN.length) ℤ) (v₁ v₂ : Val),
    TmGLPGenOut E i0 σN X U V d g (.list [encIntMatrix (fun i j => (U * C₁ * V) j i % d i), v₁,
      encIntMatrix (fun i j => (U * C₂ * V) j i % d i), v₂]) ∧
    w = .list [encIntMatrix (tmGLPBlk (fun i j => (U * C₁ * V) j i % d i)),
      tmGLPConsV (encInt (tmGLPEc (gens σN) X g⁻¹)) v₁,
      encIntMatrix (tmGLPBlk (fun i j => (U * C₂ * V) j i % d i)),
      tmGLPConsV (encInt (tmGLPEc (gens σN) X g)) v₂]

variable {Ω : Type} [RAct (Perm (Fin n)) Ω]
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}
variable {Ω₀ C₀ : Type} {S : State Ω₀ C₀} {L : GI.Algorithm.GiantLabels S}

/-- **The orientation item of one generator is the contract's item** for `E_o = tmGLPEoOf E'`,
`tmGLlamO` and `tmGLoO`, with moduli `(2, D)`. -/
theorem tmGLP_genO_item (hn : Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H)
    {k : Perm (Fin n) → Fin L.q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    (E : Fin n × Fin L.q ≃ S.dom) (i0 j0 : Fin L.q) {x : Fin L.q → Ω}
    (hyk : ∀ h ∈ H, ∀ y : Fin L.q → Perm (Fin n), GI.Paper.cleanRowPerm E y ∈ S.domGroup →
      y i0 = h → ∃ ν, TmGLZero N φ ν ∧ ∀ i, y i = k h i * ν i)
    {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (hUV : U * V = 1) (E' : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D))
    (hE' : ∀ z, E' (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z)
    {gs : List (Perm (Fin n))} (hgs : gens gs ≤ Aut H (types N x)) (g : gens gs) {w : Val}
    (hw : TmGLPGenOOut E i0 σN x U V (fun i => D i i) (g : Perm (Fin n)) w) :
    w = tmGLAffItem gs (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ)
      (tmGLρE (tmGLPEoOf E') (tmGLlamO hn hker hgs hNH))
      (tmGLcE (tmGLPEoOf E') (tmGLoO (tmGLPRep N x j0) k)) g := by
  obtain ⟨C₁, C₂, v₁, v₂, hg, rfl⟩ := hw
  have h := tmGLP_gen_item hn hker hNH hk E i0 j0 hyk hN hpos hUV E' hE' hgs g hg
  simp only [tmGLAffItem, Val.list.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hb1 := tmGLP_mat_blk (hn := hn) (hker := hker) (hNH := hNH) (hgs := hgs) E' g
  have hb2 := tmGLP_mat_blk (hn := hn) (hker := hker) (hNH := hNH) (hgs := hgs) E' g⁻¹
  have hc1 := tmGLP_cO_vec E' (tmGLPRep N x j0) k g
  have hc2 := tmGLP_cO_vec E' (tmGLPRep N x j0) k g⁻¹
  have hm1 := tmGLP_encIntMatrix_inj h1
  have hm2 := tmGLP_encIntMatrix_inj h3
  rw [tmGLAffItem, hb1, hb2, hc1, hc2, tmGLP_linVec_cons, tmGLP_linVec_cons, ← hm1, ← hm2, ← h2,
    ← h4, hN]
  simp only [InvMemClass.coe_inv, inv_inv]

end GI.Impl
