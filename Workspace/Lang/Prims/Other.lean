/-
**The other cited algorithms as primitives**: Smith normal form and vector stabilizers
(`Workspace.Cited.AlgoLinear`), joint `k`-ary refinement (`Workspace.Cited.AlgoRefinement`), the
Design Lemma witnesses (`Workspace.Cited.AlgoDesign`) and constructive Cameron–Maróti recognition
(`Workspace.Cited.AlgoCameron`).

The pattern is that of `Workspace.Lang.Prims.PermGroups`: `xPrim h` is the primitive of the
hypothesis `h : GI.Cited.X`, `xPrim_spec` says what every result encodes, and `x_call` is the
call in `EvalAll` form. The work is the injectivity of the encodings: of integers in binary
(`encInt_injective`, from `Nat.eq_of_testBit_eq`), of matrices, of vectors over `𝔽_p`
(`ZMod.val_injective`), of colorings (through `finFunctionFinEquiv`), and, for vector
stabilizers, that a homomorphism is determined by its values on generators (`hom_eq_of_gens`).
-/
module

public import Workspace.Lang.Prims.Basic
public import Workspace.Cited.AlgoLinear
public import Workspace.Cited.AlgoDesign
public import Workspace.Cited.AlgoCameron
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace GI.Lang

open GI.Cited
open Equiv

/-! ### Injectivity of the encodings -/

theorem nat_bits_injective : Function.Injective Nat.bits := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

theorem encInt_injective : Function.Injective encInt := by
  intro a b h
  simp only [encInt, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
  obtain ⟨hs, hb⟩ := h
  have hb' : a.natAbs.bits = b.natAbs.bits := by
    refine (List.map_injective_iff.mpr (fun x y hxy => ?_)) hb
    simp only [Val.nat.injEq] at hxy
    cases x <;> cases y <;> simp_all
  have habs := nat_bits_injective hb'
  rcases Int.natAbs_eq_natAbs_iff.mp habs with e | e
  · exact e
  · by_cases ha : a < 0
    · by_cases hb0 : b < 0
      · omega
      · simp [ha, hb0] at hs
    · by_cases hb0 : b < 0
      · simp [ha, hb0] at hs
      · omega

theorem encIntMatrix_injective {r c : ℕ} :
    Function.Injective (encIntMatrix (r := r) (c := c)) := by
  intro A B h
  simp only [encIntMatrix, Val.list.injEq] at h
  rw [List.map_inj_left] at h
  funext i j
  have hi := h i (List.mem_finRange i)
  simp only [Val.list.injEq] at hi
  rw [List.map_inj_left] at hi
  exact encInt_injective (hi j (List.mem_finRange j))

theorem encVec_injective {p d : ℕ} [NeZero p] :
    Function.Injective (encVec (p := p) (d := d)) := by
  intro v w h
  simp only [encVec, Val.list.injEq] at h
  rw [List.map_inj_left] at h
  funext i
  have := h i (List.mem_finRange i)
  simp only [Val.nat.injEq] at this
  exact ZMod.val_injective p this

theorem encModMatrix_injective {p d : ℕ} [NeZero p] :
    Function.Injective (encModMatrix (p := p) (d := d)) := by
  intro M N h
  simp only [encModMatrix, Val.list.injEq] at h
  rw [List.map_inj_left] at h
  funext i
  exact encVec_injective (h i (List.mem_finRange i))

theorem encVec_length {p d d' : ℕ} {v : Fin d → ZMod p} {v' : Fin d' → ZMod p}
    (h : encVec v = encVec v') : d = d' := by
  simp only [encVec, Val.list.injEq] at h
  simpa using congrArg List.length h

theorem encKColoring_injective {n k : ℕ} :
    Function.Injective (encKColoring (n := n) (k := k)) := by
  intro c c' h
  simp only [encKColoring, Val.list.injEq] at h
  rw [List.map_inj_left] at h
  funext x
  have := h (finFunctionFinEquiv x) (List.mem_finRange _)
  simpa using this

theorem replicate_zero_length {n n' : ℕ}
    (h : Val.list (List.replicate n (.nat 0)) = .list (List.replicate n' (.nat 0))) : n = n' := by
  simp only [Val.list.injEq] at h
  simpa using congrArg List.length h

/-! ### Smith normal form -/

/-- **Smith normal form** as a primitive. -/
noncomputable def smithNormalFormPrim (h : SmithNormalForm) : Prim := Prim.ofHyp _ _ h

/-- The value of an integer matrix instance. -/
def smithEnc {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℤ) : Val :=
  .list [.nat r, .nat c, encIntMatrix A]

/-- The result: `[U, D, V]` with `U, V` unimodular, `U A V = D` and `D` in Smith form, every entry
of at most `s³` bits, `s` the number of cells of the input. -/
def SmithOut {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℤ) (w : Val) : Prop :=
  ∃ (U : Matrix (Fin r) (Fin r) ℤ) (V : Matrix (Fin c) (Fin c) ℤ) (D : Matrix (Fin r) (Fin c) ℤ),
    w = .list [encIntMatrix U, encIntMatrix D, encIntMatrix V] ∧
    IsUnit U.det ∧ IsUnit V.det ∧ U * A * V = D ∧ IsSmithForm D ∧
    EntriesBelow (smithEnc A).cells.length U ∧ EntriesBelow (smithEnc A).cells.length D ∧
    EntriesBelow (smithEnc A).cells.length V

theorem smithNormalFormPrim_spec (h : SmithNormalForm) {r c : ℕ} (hr : 0 < r) (hc : 0 < c)
    (A : Matrix (Fin r) (Fin c) ℤ) :
    PrimSpec (smithNormalFormPrim h) (smithEnc A) (SmithOut A) :=
  Prim.ofHyp_spec h (⟨r, c, hr, hc, A⟩ : IntMatrixInst) (by
    rintro ⟨r', c', _, _, A'⟩ hy
    simp only [smithInput, smithEnc, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at hy
    obtain ⟨rfl, rfl, hA⟩ := hy
    obtain rfl := encIntMatrix_injective hA
    rfl)

theorem smithNormalForm_call (h : SmithNormalForm) {P : Program} {env : List Val} {j : ℕ}
    {a : Expr} {ca : ℕ} {r c : ℕ} (hr : 0 < r) (hc : 0 < c) {A : Matrix (Fin r) (Fin c) ℤ}
    (hj : P.prims[j]? = some (smithNormalFormPrim h)) (ha : Det P env a (smithEnc A) ca) :
    EvalAll P env (.prim j a) (fun w cost => SmithOut A w ∧
      cost ≤ ca + (smithNormalFormPrim h).bound (smithEnc A) + w.wt + 1) :=
  EvalAll.prim_spec hj ha (smithNormalFormPrim_spec h hr hc A)

/-! ### Vector stabilizers -/

/-- **Vector stabilizer** as a primitive. -/
noncomputable def vectorStabilizerPrim (h : VectorStabilizer) : Prim := Prim.ofHyp _ _ h

/-- The value of a vector-stabilizer instance: the group, `p`, the matrices of the generators
and the vector. -/
def vecStabEnc (I : VecStabInst) : Val :=
  .list [encGroup I.gs, .nat I.p,
    .list (I.gs.attach.map fun g => encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val),
    encVec I.v]

/-- Two vector-stabilizer instances with the same value are equal. -/
theorem vecStabEnc_injective {I J : VecStabInst} (h : vecStabEnc J = vecStabEnc I) : J = I := by
  obtain ⟨n, gs, p, hp, hpn, d, φ, sol, v⟩ := I
  obtain ⟨n', gs', p', hp', hpn', d', φ', sol', v'⟩ := J
  simp only [vecStabEnc, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
  obtain ⟨h1, rfl, h3, h4⟩ := h
  obtain rfl := encGroup_deg h1
  obtain rfl := encGroup_injective h1
  obtain rfl := encVec_length h4
  haveI : NeZero p' := ⟨hp.ne_zero⟩
  obtain rfl := encVec_injective h4
  have hφ : φ' = φ := by
    refine hom_eq_of_gens (gs := gs') rfl fun g hg hgs => ?_
    rw [List.map_inj_left] at h3
    have := h3 ⟨g, hgs⟩ (List.mem_attach _ _)
    exact Units.ext (encModMatrix_injective this)
  subst hφ
  rfl

/-- The stabilizer of `v`, as a subgroup of `Sym(n)`. -/
def vecStabSub (I : VecStabInst) : Subgroup (Perm (Fin I.n)) :=
  (vecStab I).map (gens I.gs).subtype

theorem vectorStabilizerPrim_spec (h : VectorStabilizer) (I : VecStabInst) :
    PrimSpec (vectorStabilizerPrim h) (vecStabEnc I) (fun w => GensVal I.n w (vecStabSub I)) :=
  Prim.ofHyp_spec h I fun _ hy => vecStabEnc_injective hy

theorem vectorStabilizer_call (h : VectorStabilizer) {P : Program} {env : List Val} {j : ℕ}
    {a : Expr} {ca : ℕ} (I : VecStabInst) (hj : P.prims[j]? = some (vectorStabilizerPrim h))
    (ha : Det P env a (vecStabEnc I) ca) :
    EvalAll P env (.prim j a) (fun w c => GensVal I.n w (vecStabSub I) ∧
      c ≤ ca + (vectorStabilizerPrim h).bound (vecStabEnc I) + 13 * (I.n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (vectorStabilizerPrim_spec h I) fun _ hw => GensVal.wt_le hw

/-! ### Joint `k`-ary refinement -/

/-- **Joint `k`-ary coherent refinement** as a primitive. -/
noncomputable def karyRefinementPrim {k : ℕ} (h : KaryRefinement k) : Prim := Prim.ofHyp _ _ h

/-- The value of two `k`-ary colorings of `Fin n`: `n` padding cells and the two colorings. -/
def karyEnc {n k : ℕ} (c c' : (Fin k → Fin n) → ℕ) : Val :=
  .list [.list (List.replicate n (.nat 0)), encKColoring c, encKColoring c']

/-- The result: `[d, d']`, a joint coherent refinement of `c, c'`, with colors below `2 n^k`. -/
def KaryOut {n k : ℕ} (c c' : (Fin k → Fin n) → ℕ) (w : Val) : Prop :=
  ∃ d d' : (Fin k → Fin n) → ℕ, w = .list [encKColoring d, encKColoring d'] ∧
    (∀ x, d x < 2 * n ^ k) ∧ (∀ x, d' x < 2 * n ^ k) ∧ JointRefinement c c' d d'

/-- A `k`-ary coloring with colors below `2 n^k` weighs at most `5 (n^k + 1)²`. -/
theorem wt_encKColoring_le {n k : ℕ} {d : (Fin k → Fin n) → ℕ} (hd : ∀ x, d x < 2 * n ^ k) :
    (encKColoring d).wt ≤ 5 * (n ^ k + 1) ^ 2 := by
  have := wt_encFun_le (n := n ^ k) (fun j => d (finFunctionFinEquiv.symm j)) (B := 2 * n ^ k)
    fun j => (hd _).le
  have e : (encKColoring d) = encFun (n := n ^ k) (fun j => d (finFunctionFinEquiv.symm j)) := rfl
  rw [e]
  have h2 : n ^ k * (2 * (2 * n ^ k) + 5) + 4 ≤ 5 * (n ^ k + 1) ^ 2 := by
    generalize n ^ k = N
    nlinarith
  omega

/-- **The weight of a refinement result**: at most `30 (n^k + 1)²`. -/
theorem KaryOut.wt_le {n k : ℕ} {c c' : (Fin k → Fin n) → ℕ} {w : Val} (h : KaryOut c c' w) :
    w.wt ≤ 30 * (n ^ k + 1) ^ 2 := by
  obtain ⟨d, d', rfl, hd, hd', -⟩ := h
  have := wt_list2_le (encKColoring d) (encKColoring d')
  have := wt_encKColoring_le hd
  have := wt_encKColoring_le hd'
  have : 1 ≤ (n ^ k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem karyRefinementPrim_spec {k : ℕ} (h : KaryRefinement k) {n : ℕ}
    (c c' : (Fin k → Fin n) → ℕ) (hc : ∀ x, c x ≤ n ^ k) (hc' : ∀ x, c' x ≤ n ^ k) :
    PrimSpec (karyRefinementPrim h) (karyEnc c c') (KaryOut c c') :=
  Prim.ofHyp_spec h (⟨n, c, c', hc, hc'⟩ : TwoColoringsInst k) (by
    rintro ⟨n', e, e', _, _⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
    obtain rfl := replicate_zero_length (congrArg Val.list hy.1)
    obtain rfl := encKColoring_injective hy.2.1
    obtain rfl := encKColoring_injective hy.2.2
    rfl)

theorem karyRefinement_call {k : ℕ} (h : KaryRefinement k) {P : Program} {env : List Val}
    {j : ℕ} {a : Expr} {ca n : ℕ} {c c' : (Fin k → Fin n) → ℕ} (hc : ∀ x, c x ≤ n ^ k)
    (hc' : ∀ x, c' x ≤ n ^ k) (hj : P.prims[j]? = some (karyRefinementPrim h))
    (ha : Det P env a (karyEnc c c') ca) :
    EvalAll P env (.prim j a) (fun w cost => KaryOut c c' w ∧
      cost ≤ ca + (karyRefinementPrim h).bound (karyEnc c c') + 30 * (n ^ k + 1) ^ 2 + 1) :=
  EvalAll.prim_spec_le hj ha (karyRefinementPrim_spec h c c' hc hc') fun _ hw => KaryOut.wt_le hw

/-! ### Design Lemma witnesses -/

/-- **The Design Lemma witnesses** as a primitive. -/
noncomputable def designWitnessesPrim {k : ℕ} {α : ℚ} (h : DesignWitnesses k α) : Prim :=
  Prim.ofHyp _ _ h

/-- The value of a `k`-ary coloring of `Fin n`: `n` padding cells and the coloring. -/
def designEnc {n k : ℕ} (c : (Fin k → Fin n) → ℕ) : Val :=
  .list [.list (List.replicate n (.nat 0)), encKColoring c]

theorem designWitnessesPrim_spec {k : ℕ} {α : ℚ} (h : DesignWitnesses k α) {n : ℕ}
    (c : (Fin k → Fin n) → ℕ) (hc : ∀ x, c x ≤ n ^ k) :
    PrimSpec (designWitnessesPrim h) (designEnc c) (DesignWitnessLists α c) :=
  Prim.ofHyp_spec h (⟨n, c, hc⟩ : KColoringInst k) (by
    rintro ⟨n', e, _⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
    obtain rfl := replicate_zero_length (congrArg Val.list hy.1)
    obtain rfl := encKColoring_injective hy.2
    rfl)

theorem designWitnesses_call {k : ℕ} {α : ℚ} (h : DesignWitnesses k α) {P : Program}
    {env : List Val} {j : ℕ} {a : Expr} {ca n : ℕ} {c : (Fin k → Fin n) → ℕ}
    (hc : ∀ x, c x ≤ n ^ k) (hj : P.prims[j]? = some (designWitnessesPrim h))
    (ha : Det P env a (designEnc c) ca) :
    EvalAll P env (.prim j a) (fun w cost => DesignWitnessLists α c w ∧
      cost ≤ ca + (designWitnessesPrim h).bound (designEnc c) + w.wt + 1) :=
  EvalAll.prim_spec hj ha (designWitnessesPrim_spec h c hc)

/-! ### Constructive Cameron–Maróti recognition -/

/-- **Constructive Cameron–Maróti recognition** as a primitive. -/
noncomputable def cameronRecognitionPrim (h : CameronRecognition) : Prim := Prim.ofHyp _ _ h

/-- The result of the recognition for `G ≤ Sym(n)`: `[0]` (small order), `[1, m, k, r, E]`
(the Johnson structure with `m > (k'+1)² - 2`, and its identification), or `[2]` (a structure
with `m ≤ (k'+1)² - 2`), where `k' = min(k, m - k)`. -/
def CameronOut {n : ℕ} (G : Subgroup (Perm (Fin n))) (w : Val) : Prop :=
  (w = .list [.nat 0] ∧ Nat.card G < n ^ (1 + Nat.log 2 n)) ∨
  (∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
    (min k (m - k) + 1) ^ 2 < m + 2 ∧ MarotiStructure G e ∧
    w = .list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e]) ∨
  (w = .list [.nat 2] ∧ ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
    m + 2 ≤ (min k (m - k) + 1) ^ 2 ∧ MarotiStructure G e)

theorem cameronRecognitionPrim_spec (h : CameronRecognition) {n : ℕ} {gv : Val}
    {G : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) (hn : 25 ≤ n)
    (hprim : MulAction.IsPreprimitive G (Fin n)) :
    PrimSpec (cameronRecognitionPrim h) gv (CameronOut G) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec h (⟨n, hn, gs, hprim⟩ : PrimitiveInst) (by
    rintro ⟨n', _, gs', _⟩ hy
    obtain rfl := encGroup_deg hy
    obtain rfl := encGroup_injective hy
    rfl)

theorem cameronRecognition_call (h : CameronRecognition) {P : Program} {env : List Val}
    {j : ℕ} {a : Expr} {ca n : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (cameronRecognitionPrim h)) (ha : Det P env a gv ca)
    (hG : GroupVal n gv G) (hn : 25 ≤ n) (hprim : MulAction.IsPreprimitive G (Fin n)) :
    EvalAll P env (.prim j a) (fun w c => CameronOut G w ∧
      c ≤ ca + (cameronRecognitionPrim h).bound gv + w.wt + 1) :=
  EvalAll.prim_spec hj ha (cameronRecognitionPrim_spec h hG hn hprim)

end GI.Lang
