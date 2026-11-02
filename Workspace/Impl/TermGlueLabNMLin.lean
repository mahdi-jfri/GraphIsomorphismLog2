import Workspace.Impl.TermGlueLabNVecOK
import Workspace.Impl.TermGlueLabPPoly

/-!
# The label driver: the linear library module and the vector module

Proof of Theorem A.23, steps 5 and 6, at a fixed layout. The vector wrapper and
the step-5 items use the same integer linear algebra: coordinates of group elements
(ConstructiveMembership), sums of coordinate vectors, dense matrix products, transposes and
reductions mod `D`. `tmGLNLinFuns b jm` holds these blocks once (`TmGLNLinAt`); the vector
module `tmGLNVecMFuns` is the wrapper of `TermGlueLabNVecP.lean` pointed at them.

The cost envelopes of these blocks are polynomial (`linElementBudget_poly`,
`tmGLPCSumC_poly`, `tmGLPVecC_poly`, `tmGLPCMatC_poly`, `tmGLPMatC_poly`). Their constants are
fixed here by choice (`tmGLNCe` …).

Layout of the library (offsets from `b`): `0` dense product (32, integers at `14`), `32` sums
(4), `36` element coordinates (42), `78` vector addition (3), `81` the vector map, `82`
transpose (12), `94` reduction (25), `119` the coordinate matrix, `120` conjugation, `121` the
matrix map, `122` map (3), `125` compose (4), `129` tail (3), `132` map (3).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val ConstructiveMembership)

set_option maxRecDepth 100000

/-- The three single functions at offsets `119`–`121`. -/
def tmGLNLinMid (b : ℕ) : List Expr :=
  [tmGLPCMatF (b + 122) (b + 129) (b + 132), supConjF (b + 125), tmGLPMatF b (b + 82) (b + 94)]

/-- **The linear library module** at `b`, with ConstructiveMembership at `jm`. -/
def tmGLNLinFuns (b jm : ℕ) : List Expr :=
  linDenseMulFuns b ++ (tmGLPCSumFuns (b + 32) (b + 36) (b + 78) ++
    (linElementCoordinatesFuns (b + 36) jm ++ (linVectorBinaryFuns (b + 78) (b + 14 + 11) ++
    ([tmGLPVecF b (b + 82) (b + 94)] ++ (tmGLPTrFuns (b + 82) ++
    (linFiniteMatrixReduceFuns (b + 94) ++ (tmGLNLinMid b ++ (mapFuns (b + 122) (b + 120) ++
    (composeFuns (b + 125) ++ (linTailFuns (b + 129) ++ mapFuns (b + 132) (b + 36)))))))))))

theorem length_tmGLNLinFuns (b jm : ℕ) : (tmGLNLinFuns b jm).length = 135 := rfl

/-- The blocks of the library at `b`. -/
structure TmGLNLinAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  mul : linDenseMulAt P b
  cs : P.HasAt (b + 32) (tmGLPCSumFuns (b + 32) (b + 36) (b + 78))
  ec : linElementCoordinatesAt P (b + 36) jm hm
  add : P.HasAt (b + 78) (linVectorBinaryFuns (b + 78) (b + 14 + 11))
  vec : P.funs[b + 81]? = some (tmGLPVecF b (b + 82) (b + 94))
  tr : P.HasAt (b + 82) (tmGLPTrFuns (b + 82))
  red : P.HasAt (b + 94) (linFiniteMatrixReduceFuns (b + 94))
  cm : P.funs[b + 119]? = some (tmGLPCMatF (b + 122) (b + 129) (b + 132))
  cj : P.funs[b + 120]? = some (supConjF (b + 125))
  mat : P.funs[b + 121]? = some (tmGLPMatF b (b + 82) (b + 94))
  mcj : P.HasAt (b + 122) (mapFuns (b + 122) (b + 120))
  cp : P.HasAt (b + 125) (composeFuns (b + 125))
  tl : P.HasAt (b + 129) (linTailFuns (b + 129))
  mec : P.HasAt (b + 132) (mapFuns (b + 132) (b + 36))

private theorem tmGLN_ml_right {P : Program} {b b' : ℕ} {A B : List Expr}
    (h : P.HasAt b (A ++ B)) (hb : b + A.length = b') : P.HasAt b' B := hb ▸ h.right

theorem tmGLNLinAt_of {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (tmGLNLinFuns b jm)) (hj : P.prims[jm]? = some (linMembershipPrim hm)) :
    TmGLNLinAt P b jm hm := by
  have h1 := tmGLN_ml_right h (b' := b + 32) rfl
  have h2 := tmGLN_ml_right h1 (b' := b + 36) rfl
  have h3 := tmGLN_ml_right h2 (b' := b + 78) rfl
  have h4 := tmGLN_ml_right h3 (b' := b + 81) rfl
  have h5 := tmGLN_ml_right h4 (b' := b + 82) rfl
  have h6 := tmGLN_ml_right h5 (b' := b + 94) rfl
  have h7 := tmGLN_ml_right h6 (b' := b + 119) rfl
  have h8 := tmGLN_ml_right h7 (b' := b + 122) rfl
  have h9 := tmGLN_ml_right h8 (b' := b + 125) rfl
  have h10 := tmGLN_ml_right h9 (b' := b + 129) rfl
  have h11 := tmGLN_ml_right h10 (b' := b + 132) rfl
  have hs := h7.left
  exact { mul := linDenseMulAt_of h.left, cs := h1.left,
          ec := linElementCoordinatesAt_of h2.left hj, add := h3.left, vec := h4.left.single,
          tr := h5.left, red := h6.left,
          cm := (hs.block (gs := [tmGLPCMatF (b + 122) (b + 129) (b + 132)]) 0 rfl).single,
          cj := by simpa using (hs.block (gs := [supConjF (b + 125)]) 1 rfl).single,
          mat := by simpa using (hs.block (gs := [tmGLPMatF b (b + 82) (b + 94)]) 2 rfl).single,
          mcj := h8.left, cp := h9.left, tl := h10.left, mec := h11 }

theorem TmGLNLinAt.ovec {P : Program} {b jm ov : ℕ} {hm : ConstructiveMembership}
    (h : TmGLNLinAt P b jm hm) (hov : P.funs[ov]? = some (tmGLPOVecF (b + 32) (b + 81))) :
    TmGLPOVecAt P ov hm :=
  ⟨_, _, _, _, _, _, _, _, _, hov, h.cs, h.ec, h.mul.ints, h.add, h.vec, h.mul, h.tr, h.red⟩

theorem TmGLNLinAt.mpair {P : Program} {b jm mp : ℕ} {hm : ConstructiveMembership}
    (h : TmGLNLinAt P b jm hm) (hmp : P.funs[mp]? = some (tmGLPMPairF (b + 119) (b + 121))) :
    TmGLPMPairAt P mp hm :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, hmp, h.cm, h.cp, h.cj, h.mcj, h.tl, h.mec, h.ec, h.mat,
    h.mul, h.tr, h.red⟩

/-! ### The constants of the cost envelopes -/

theorem tmGLN_pbu_W {f : ℕ → ℕ} (h : PBU fun _ W _ => f W) :
    ∃ C D : ℕ, ∀ W, f W ≤ C * (W + 2) ^ D := by
  obtain ⟨C, D, hC⟩ := h
  exact ⟨C, D, fun W => by simpa [PB] using hC 0 W 0⟩

theorem tmGLN_pbu_Wt {f : ℕ → ℕ → ℕ} (h : PBU fun t W _ => f W t) :
    ∃ C D : ℕ, ∀ W t, f W t ≤ C * (W + 0 + t + 2) ^ D := by
  obtain ⟨C, D, hC⟩ := h
  exact ⟨C, D, fun W t => hC t W 0⟩

/-- `Ce`, `De`: the element-coordinates budget. -/
noncomputable def tmGLNCe (hm : ConstructiveMembership) : ℕ :=
  (tmGLN_pbu_W (linElementBudget_poly hm)).choose
noncomputable def tmGLNDe (hm : ConstructiveMembership) : ℕ :=
  (tmGLN_pbu_W (linElementBudget_poly hm)).choose_spec.choose
theorem tmGLN_hEB (hm : ConstructiveMembership) :
    ∀ W, linElementBudget hm W ≤ tmGLNCe hm * (W + 2) ^ tmGLNDe hm :=
  (tmGLN_pbu_W (linElementBudget_poly hm)).choose_spec.choose_spec

/-- `Cs`, `Ds`: the coordinate sums. -/
noncomputable def tmGLNCs (hm : ConstructiveMembership) : ℕ :=
  (tmGLN_pbu_W (tmGLPCSumC_poly (tmGLNCe hm) (tmGLNDe hm))).choose
noncomputable def tmGLNDs (hm : ConstructiveMembership) : ℕ :=
  (tmGLN_pbu_W (tmGLPCSumC_poly (tmGLNCe hm) (tmGLNDe hm))).choose_spec.choose
theorem tmGLN_hCS (hm : ConstructiveMembership) :
    ∀ W, tmGLPCSumC (tmGLNCe hm) (tmGLNDe hm) W ≤ tmGLNCs hm * (W + 2) ^ tmGLNDs hm :=
  (tmGLN_pbu_W (tmGLPCSumC_poly (tmGLNCe hm) (tmGLNDe hm))).choose_spec.choose_spec

/-- `Cc`, `Dc`: the coordinate matrices. -/
noncomputable def tmGLNCc (hm : ConstructiveMembership) : ℕ :=
  (tmGLN_pbu_W (tmGLPCMatC_poly (tmGLNCe hm) (tmGLNDe hm))).choose
noncomputable def tmGLNDc (hm : ConstructiveMembership) : ℕ :=
  (tmGLN_pbu_W (tmGLPCMatC_poly (tmGLNCe hm) (tmGLNDe hm))).choose_spec.choose
theorem tmGLN_hCM (hm : ConstructiveMembership) :
    ∀ W, tmGLPCMatC (tmGLNCe hm) (tmGLNDe hm) W ≤ tmGLNCc hm * (W + 2) ^ tmGLNDc hm :=
  (tmGLN_pbu_W (tmGLPCMatC_poly (tmGLNCe hm) (tmGLNDe hm))).choose_spec.choose_spec

/-- `Cv`, `Dv`: the vector maps. -/
noncomputable def tmGLNCv : ℕ := (tmGLN_pbu_Wt tmGLPVecC_poly).choose
noncomputable def tmGLNDv : ℕ := (tmGLN_pbu_Wt tmGLPVecC_poly).choose_spec.choose
theorem tmGLN_hVC : ∀ W t, tmGLPVecC W t ≤ tmGLNCv * (W + 0 + t + 2) ^ tmGLNDv :=
  (tmGLN_pbu_Wt tmGLPVecC_poly).choose_spec.choose_spec

/-- `Cm`, `Dm`: the matrix maps. -/
noncomputable def tmGLNCm : ℕ := (tmGLN_pbu_Wt tmGLPMatC_poly).choose
noncomputable def tmGLNDm : ℕ := (tmGLN_pbu_Wt tmGLPMatC_poly).choose_spec.choose
theorem tmGLN_hMC : ∀ W t, tmGLPMatC W t ≤ tmGLNCm * (W + 0 + t + 2) ^ tmGLNDm :=
  (tmGLN_pbu_Wt tmGLPMatC_poly).choose_spec.choose_spec

/-! ### The vector module -/

/-- **The vector module** at `v`, with the library at `b`. -/
def tmGLNVecMFuns (v b : ℕ) : List Expr := tmGLNVecFuns v (b + 32) (b + 81)

theorem tmGLN_vecm_ok (hm : ConstructiveMembership) {P : Program} {v b jm : ℕ}
    (h : P.HasAt v (tmGLNVecMFuns v b)) (hL : TmGLNLinAt P b jm hm) :
    Iface.TmGLNVecOK P v (tmGLNVecC (tmGLNCs hm) (tmGLNDs hm) tmGLNCv tmGLNDv) :=
  tmGLN_vec_ok hm h hL.cs hL.ec hL.mul.ints hL.add hL.vec hL.mul hL.tr hL.red (tmGLN_hEB hm)
    (tmGLN_hCS hm) tmGLN_hVC

end GI.Impl
