module

public import Workspace.Impl.TermGlueLabNS5OK
public import Workspace.Impl.TermGlueLabNMF
public import Workspace.Impl.TermGlueLabNMLin

@[expose] public section

/-!
# The label driver: the step-5 module

Proof of Theorem A.23, step 5, at a fixed layout. `tmGLNS5Funs s f l abel quo
minv` holds the step-5 function of the driver (the test "all types distinct", then the plain or
the orientation step 5) with its items, the matrix pairs, the offsets and the orientation
blocks. It uses the lift module, the row transporter and the relation of the front module at
`f`, and the linear library at `l`. The setup of step 5 calls three outside programs: the
abelian coordinates at `abel`, the quotient coordinates at `quo` and the matrix inverse at
`minv`.

`tmGLN_m5_ok`: with these in place and the contracts `hab`, `hquo`, `hminv` of the three
outside programs, the module meets `TmGLNS5OK`.

Layout (offsets from `s`): `0` the step-5 function, `1` plain step 5, `2` plain step 5 for the
orientation items, `3` orientation step 5, `4` cons, `5` orientation generator item, `6` the
signs, `7` the generator item, `8` the offsets, `9` offset vectors, `10` matrix pairs, `11` the
setup with `D`, `12` the setup, `13` the test (3), `16` items map (3), `19` orientation items map
(3), `22` append (3), `25` inverse (12), `37` blocks (12), `49` offsets loop (5), `54` signs loop
(21), `75` offset lists, `76` first entries, `77` map (3), `80` map (3), `83` composed lists.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val PointwiseStab Membership NormalizedFactor ConstructiveMembership encGroup
  encIntMatrix gens FullRankInst fullRankInput)

set_option maxRecDepth 100000

/-- The single functions at offsets `0`–`12`. -/
def tmGLNS5Singles (s f l abel quo minv : ℕ) : List Expr :=
  [tmGLNS5F (s + 13) (s + 3) (s + 1), tmGLPStep5F (s + 11) (s + 16),
    tmGLPStep5F (s + 11) (s + 19), tmGLPStep5OF (s + 2) (s + 4), tmGLPConsF (s + 22),
    tmGLPGenOF (s + 25) (s + 6) (s + 7) (s + 4) (s + 37), tmGLPEpsF (s + 49) (s + 54),
    tmGLPGenF (s + 25) (s + 8) (s + 10), tmGLPHalfF (s + 49) (f + 7 + 1) (s + 75) (s + 9),
    tmGLPOVecF (l + 32) (l + 81), tmGLPMPairF (l + 119) (l + 121), tmGLPSetDF (s + 12),
    tmGLPSetF abel (l + 132) (s + 22) quo minv]

/-- The single functions at offsets `75`, `76`. -/
def tmGLNS5Xs (s : ℕ) : List Expr := [tmGLPXsF (s + 22) (s + 77) (s + 80), tmGLPGet1F]

/-- **The step-5 module** at `s`. -/
def tmGLNS5Funs (s f l abel quo minv : ℕ) : List Expr :=
  tmGLNS5Singles s f l abel quo minv ++ (tmGLNDistFuns (s + 13) ++ (mapFuns (s + 16) (s + 7) ++
    (mapFuns (s + 19) (s + 5) ++ (appendFuns (s + 22) ++ (invFuns (s + 25) ++
    (tmGLPBlkFuns (s + 37) ++ (tmGLPOffFuns (s + 49) (f + 124) (f + 128) ++
    (tmGLPOrFuns (s + 54) ++ (tmGLNS5Xs s ++ (mapFuns (s + 77) (s + 76) ++
    (mapFuns (s + 80) (s + 83) ++ [tmGLPLCmpF (l + 125)])))))))))))

theorem length_tmGLNS5Funs (s f l abel quo minv : ℕ) :
    (tmGLNS5Funs s f l abel quo minv).length = 84 := rfl

private theorem tmGLN_m5_right {P : Program} {b b' : ℕ} {A B : List Expr}
    (h : P.HasAt b (A ++ B)) (hb : b + A.length = b') : P.HasAt b' B := hb ▸ h.right

/-- The cost of the step-5 module. -/
noncomputable def tmGLNM5C (hm : Membership) (hfac : NormalizedFactor)
    (hcm : ConstructiveMembership) (FA FQ FI : ℕ → ℕ) : ℕ → ℕ :=
  tmGLNS5Cost (membershipPrim hm) (normalizedFactorPrim hfac) FA FQ FI (tmGLNCe hcm)
    (tmGLNDe hcm) (tmGLNCs hcm) (tmGLNDs hcm) tmGLNCv tmGLNDv (tmGLNCc hcm) (tmGLNDc hcm)
    tmGLNCm tmGLNDm

/-- **The step-5 module meets the step-5 contract**, given the contracts of the abelian
coordinates, the quotient coordinates and the matrix inverse. -/
theorem tmGLN_m5_ok (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (hcm : ConstructiveMembership) {P : Program} {s f l abel quo minv jp jm jf jc sup : ℕ}
    (h : P.HasAt s (tmGLNS5Funs s f l abel quo minv))
    (hF : P.HasAt f (tmGLNFrontFuns f jp jm jf sup)) (hL : TmGLNLinAt P l jc hcm)
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {FA FQ FI : ℕ → ℕ} (hFA : Monotone FA) (hFQ : Monotone FQ) (hFI : Monotone FI)
    (hab : ∀ {n : ℕ} (ns as : List (Equiv.Perm (Fin n))), gens ns ≤ gens as →
      (∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) →
      FunAll P abel (.list [encGroup ns, encGroup as]) (fun out c =>
        (∃ M : Matrix (Fin as.length) (Fin as.length) ℤ, out = encIntMatrix M ∧
          linPermPresentation ns as M) ∧ c ≤ FA (Val.list [encGroup ns, encGroup as]).wt))
    (hquo : ∀ I : FullRankInst, FunAll P quo (fullRankInput I) (fun out c =>
      TmGLQOut I.A out ∧ c ≤ FQ (fullRankInput I).wt))
    (hminv : ∀ {t : ℕ} (ht : 0 < t) (V : Matrix (Fin t) (Fin t) ℤ) (hV : IsUnit V.det),
      FunAll P minv (fullRankInput (tmGLPInst ht V hV)) (fun w c =>
        ∃ U : Matrix (Fin t) (Fin t) ℤ, w = encIntMatrix U ∧ U * V = 1 ∧ V * U = 1 ∧
          c ≤ FI (fullRankInput (tmGLPInst ht V hV)).wt)) :
    Iface.TmGLNS5OK P s (tmGLNM5C hm hfac hcm FA FQ FI) := by
  obtain ⟨-, hl, -, -, hfd, hr, -⟩ := tmGLN_front_parts hF
  have h1 := tmGLN_m5_right h (b' := s + 13) rfl
  have h2 := tmGLN_m5_right h1 (b' := s + 16) rfl
  have h3 := tmGLN_m5_right h2 (b' := s + 19) rfl
  have h4 := tmGLN_m5_right h3 (b' := s + 22) rfl
  have h5 := tmGLN_m5_right h4 (b' := s + 25) rfl
  have h6 := tmGLN_m5_right h5 (b' := s + 37) rfl
  have h7 := tmGLN_m5_right h6 (b' := s + 49) rfl
  have h8 := tmGLN_m5_right h7 (b' := s + 54) rfl
  have h9 := tmGLN_m5_right h8 (b' := s + 75) rfl
  have h10 := tmGLN_m5_right h9 (b' := s + 77) rfl
  have h11 := tmGLN_m5_right h10 (b' := s + 80) rfl
  have h12 := tmGLN_m5_right h11 (b' := s + 83) rfl
  have hS := h.left
  have hX := h9.left
  have g0 : P.funs[s]? = some (tmGLNS5F (s + 13) (s + 3) (s + 1)) := by
    simpa using (hS.block (gs := [tmGLNS5F (s + 13) (s + 3) (s + 1)]) 0 rfl).single
  have g1 : P.funs[s + 1]? = some (tmGLPStep5F (s + 11) (s + 16)) :=
    (hS.block (gs := [tmGLPStep5F (s + 11) (s + 16)]) 1 rfl).single
  have g2 : P.funs[s + 2]? = some (tmGLPStep5F (s + 11) (s + 19)) :=
    (hS.block (gs := [tmGLPStep5F (s + 11) (s + 19)]) 2 rfl).single
  have g3 : P.funs[s + 3]? = some (tmGLPStep5OF (s + 2) (s + 4)) :=
    (hS.block (gs := [tmGLPStep5OF (s + 2) (s + 4)]) 3 rfl).single
  have g4 : P.funs[s + 4]? = some (tmGLPConsF (s + 22)) :=
    (hS.block (gs := [tmGLPConsF (s + 22)]) 4 rfl).single
  have g5 : P.funs[s + 5]? = some (tmGLPGenOF (s + 25) (s + 6) (s + 7) (s + 4) (s + 37)) :=
    (hS.block (gs := [tmGLPGenOF (s + 25) (s + 6) (s + 7) (s + 4) (s + 37)]) 5 rfl).single
  have g6 : P.funs[s + 6]? = some (tmGLPEpsF (s + 49) (s + 54)) :=
    (hS.block (gs := [tmGLPEpsF (s + 49) (s + 54)]) 6 rfl).single
  have g7 : P.funs[s + 7]? = some (tmGLPGenF (s + 25) (s + 8) (s + 10)) :=
    (hS.block (gs := [tmGLPGenF (s + 25) (s + 8) (s + 10)]) 7 rfl).single
  have g8 : P.funs[s + 8]? = some (tmGLPHalfF (s + 49) (f + 7 + 1) (s + 75) (s + 9)) :=
    (hS.block (gs := [tmGLPHalfF (s + 49) (f + 7 + 1) (s + 75) (s + 9)]) 8 rfl).single
  have g9 : P.funs[s + 9]? = some (tmGLPOVecF (l + 32) (l + 81)) :=
    (hS.block (gs := [tmGLPOVecF (l + 32) (l + 81)]) 9 rfl).single
  have g10 : P.funs[s + 10]? = some (tmGLPMPairF (l + 119) (l + 121)) :=
    (hS.block (gs := [tmGLPMPairF (l + 119) (l + 121)]) 10 rfl).single
  have g11 : P.funs[s + 11]? = some (tmGLPSetDF (s + 12)) :=
    (hS.block (gs := [tmGLPSetDF (s + 12)]) 11 rfl).single
  have g12 : P.funs[s + 12]? = some (tmGLPSetF abel (l + 132) (s + 22) quo minv) :=
    (hS.block (gs := [tmGLPSetF abel (l + 132) (s + 22) quo minv]) 12 rfl).single
  have x0 : P.funs[s + 75]? = some (tmGLPXsF (s + 22) (s + 77) (s + 80)) := by
    simpa using (hX.block (gs := [tmGLPXsF (s + 22) (s + 77) (s + 80)]) 0 rfl).single
  have x1 : P.funs[s + 76]? = some tmGLPGet1F := by
    simpa using (hX.block (gs := [tmGLPGet1F]) 1 rfl).single
  have hoff : TmGLPOffAt P (s + 49) hm hfac :=
    ⟨f + 124, f + 128, jm, jf, h7.left, hfd, tmGLPRelAt_of hr, hjm, hjf⟩
  have hlb : TmGLPL1At P (f + 7) hst hfac := ⟨jp, jf, tmGLPLiftAt_of hl, hjp, hjf⟩
  have hxs : TmGLPXsAt P (s + 75) :=
    ⟨s + 22, s + 77, s + 76, s + 80, s + 83, l + 125, x0, h4.left, h10.left, x1, h11.left,
      h12.single, hL.cp⟩
  exact @tmGLN_s5_ok hm hfac hcm hst P s (s + 13) (s + 3) (s + 1) (s + 2) (s + 11) (s + 12)
    (s + 16) (s + 19) (s + 7) (s + 5) (s + 6) (s + 4) (s + 22) (s + 37) (s + 25) (s + 8)
    (s + 10) (s + 49) (f + 7) (s + 75) (s + 9) (s + 54) abel (l + 132) (l + 36) jc quo minv
    g0 h1.left g1 h2.left g2 h3.left g3 g4 h4.left g5 h6.left g6 h8.left g7 h5.left g8 hoff hlb
    hxs (hL.ovec g9) (hL.mpair g10) (tmGLNCe hcm) (tmGLNDe hcm) (tmGLNCs hcm) (tmGLNDs hcm)
    tmGLNCv tmGLNDv (tmGLNCc hcm) (tmGLNDc hcm) tmGLNCm tmGLNDm (tmGLN_hEB hcm) (tmGLN_hCS hcm)
    tmGLN_hVC (tmGLN_hCM hcm) tmGLN_hMC g11 g12 FA FQ FI hFA hFQ hFI hab hL.mec hL.ec hquo hminv

end GI.Impl
