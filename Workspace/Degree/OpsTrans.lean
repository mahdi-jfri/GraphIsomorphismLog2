module

public import Workspace.Degree.TransD
public import Workspace.Degree.OpsCont
public import Workspace.Degree.Enum
public import Workspace.Degree.Prod
public import Workspace.Degree.Norm
public import Workspace.Degree.CaseData
public import Workspace.Degree.QuotChild

@[expose] public section

/-!
# The operation of `transD`

`ops_trans` proves the field `trans` of `Ops` (`Degree/Spine.lean`). The specifications of the three
branches stay as named statements (`EnumAt`, `ProdAt`, `NormAt`), so that this file does not depend on
where the program holds their functions. The polynomial bounds are the fields of `TransBudget`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership GroupOrder MinimalBlocks
  encKSetTuples MarotiStructure)

/-- **The statement of `enum_spec`** at the function `f`. -/
def EnumAt (Pg : Program) (F : Funs) (hp : Preimage) (hm : Membership) (f : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (Bc : State Ω C → ℝ) {e : Ω ≃ Fin k} {c : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C},
    Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S →
    ∀ (Q : PrimitiveQuotient S), CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post) →
    ∀ {lv hv' : Val}, ReprVal k lv (fun i j => Q.labFin e i = Q.labFin e j) →
    HierValC e hv' (Q.pre ++ Q.top :: Q.post) → ∀ {B : ℕ}, Nat.card Q.ρ.range ≤ B →
    (∀ (t : Perm (Fin k)) (val : Val), Canon e c val (enumChild S Q e t) →
      FunAll Pg F.cont val (ChildPost Bc (enumChild S Q e t) e)) →
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], lv, hv', .nat B])
      (fun u cost => AnsC e u S.answer ∧ ∃ L : List (Perm (Fin k)), L.length ≤ B ∧
        (cost : ℝ) ≤ enumCost hp hm k (Val.list [.list [.nat k, gv, dv, xv, yv, hv,
          rv, fv, hh, .nat N], lv, hv', .nat B]).wt B +
          (L.map fun t => Bc (enumChild S Q e t)).sum)

/-- **The statement of `prod_specD`** at the function `f`. -/
def ProdAt (Pg : Program) (F : Funs) (hO : GroupOrder) (hp : Preimage) (hm : Membership) (f : ℕ) :
    Prop :=
  ∀ {Ω C : Type} (Bc : State Ω C → ℝ) {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C},
    Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S →
    ∀ (Q : PrimitiveQuotient S) {m l r : ℕ} (E : Fin Q.d ≃ (Fin r → Product.KSet m l))
    (hS : Q.ProductStructure m l r E), 2 ≤ r →
    CarrierOK (Q.coordinateGroup E hS (Q.two_le_choose E)) S.dom S.rows
      (Q.pre ++ Q.coordHier E ++ Q.post) →
    ∀ {gv' rep hv' : Val}, HierValC e hv' (Q.pre ++ Q.top :: Q.post) →
    (∀ (I : DispatchStep P₀ S), I.kind = .product r →
      I.K = Q.coordinateGroup E hS (Q.two_le_choose E) →
      I.hier' = Q.pre ++ Q.coordHier E ++ Q.post → ∀ (t : Perm (Fin k)) (val : Val),
      Canon e c val (tailChild S I.toData e t) →
      FunAll Pg F.cont val (ChildPost Bc (tailChild S I.toData e t) e)) →
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
        .list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
        .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E]])
      (fun u cost => AnsC e u S.answer ∧ ∃ (I : DispatchStep P₀ S) (Kv : Val)
        (L : List (Perm (Fin k))),
        I.kind = .product r ∧ I.K = Q.coordinateGroup E hS (Q.two_le_choose E) ∧
        I.hier' = Q.pre ++ Q.coordHier E ++ Q.post ∧
        I.n = ((Q.coordinateGroup E hS (Q.two_le_choose E)).subgroupOf S.G).index ∧
        GroupValC k Kv (groupFin e I.K) ∧ L.length ≤ I.n ∧
        (cost : ℝ) ≤ prodCostD hO hp hm k (Val.list
          [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
          .list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
          .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E]]).wt I.n gv Kv +
          (L.map fun t => Bc (tailChild S I.toData e t)).sum)

/-- **The statement of `normStep_specD`** at the function `f`. -/
def NormAt (Pg : Program) (F : Funs) (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    (f : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] {n m k sz : ℕ} (en : Ω ≃ Fin n) (cc : C → ℕ) {S : State Ω C}
    (Bg : Bool → State Ω C → ℝ) {gv dv xv yv hv rv fv hh rep hv' : Val},
    Canon en cc (.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S →
    S.dom.Nonempty → ∀ (htr : S.Transitive) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (hq : P₀.q₀ < m) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels),
    normNumbered en Q rep → HierValC en hv' (Q.pre ++ Q.top :: Q.post) →
    (∀ (D : normCosetData Q e hS) (b : Bool),
      (∀ j, (normMode b = .cont ∧ ¬ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive) ∨
        (normMode b = .giant ∧ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive)) →
      ∀ (lv : Val), (∀ j, LabValStd en ((Q.normAboveOf D.choice htr hq hkc hkl).child j) lv
        ((Q.normAboveOf D.choice htr hq hkc hkl).childLabels j)) →
      ∀ j val, Canon en cc val ((Q.normAboveOf D.choice htr hq hkc hkl).child j) →
        FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
          (ChildPost (Bg b) ((Q.normAboveOf D.choice htr hq hkc hkl).child j) en)) →
    FunAll Pg f (.list [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
      .nat m, .nat k, encKSetTuples e]) (fun u cost =>
      AnsC en u S.answer ∧ ∃ (D : normCosetData Q e hS) (b : Bool),
        (∀ j, (normMode b = .cont ∧ ¬ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive) ∨
          (normMode b = .giant ∧ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive)) ∧
        (cost : ℝ) ≤ normStepCost hp hst hm n m (Val.list
          [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
            .nat m, .nat k, encKSetTuples e]).wt +
          ∑ j : Fin (Q.normAboveOf D.choice htr hq hkc hkl).I.k,
            Bg b ((Q.normAboveOf D.choice htr hq hkc hkl).child j))

/-- The inner statement of `PrimitiveAlternatives`. -/
def AltAt (c₁ c₂ : ℝ) (q₀ : ℕ) : Prop :=
  ∀ (D b : ℕ), 6 ≤ D → 2 ≤ b → ∀ P : Subgroup (Perm (Fin b)),
    MulAction.IsPreprimitive P (Fin b) → GammaHat D P →
      Real.log (Nat.card P) ≤ (c₁ * Real.log D + c₂) * Real.log b ∨
      ∃ (q h r : ℕ) (e : Fin b ≃ JohnsonTuple q h r), q₀ < q ∧ JohnsonProduct D P e

/-- The code of `transD`. -/
structure TransCode (X : Ctx) (F : Funs) (hmb : MinimalBlocks) (hO : GroupOrder)
    (h : JohnsonRecognition) (hp : Preimage) (hst : PointwiseStab) (hm : Membership) where
  hcont : F.cont = X.contD
  hgiant : F.giant = X.giantD
  fexp : ℕ
  jo : ℕ
  fcase : ℕ
  tst : ℕ
  jr : ℕ
  fbr : ℕ
  fen : ℕ
  fpr : ℕ
  fno : ℕ
  fs : ℕ
  fad : ℕ
  fn : ℕ
  E : ℕ
  hf : X.Pg.funs[X.transD]? = some (transE fexp jo fcase fbr)
  hexp : ExposeAt hmb X.Pg fexp
  hjo : X.Pg.prims[jo]? = some (groupOrderPrim hO)
  hc : X.Pg.funs[fcase]? = some (caseDE tst jr X.D)
  htst : X.Pg.HasAt tst (degTestFuns tst E)
  hjr : X.Pg.prims[jr]? = some (recognitionPrim h)
  hbr : X.Pg.funs[fbr]? = some (branchE fen fpr fno)
  hgate : X.Pg.funs[fno]? = some (normGateE fs fad)
  had : X.Pg.funs[fad]? = some (gsNormE fn)
  en : EnumAt X.Pg F hp hm fen
  pr : ProdAt X.Pg F hO hp hm fpr
  no : NormAt X.Pg F hp hst hm fn

/-- The bound on the weight of an input of a branch. -/
noncomputable def Ctx.WB (X : Ctx) (hmb : MinimalBlocks) : ℕ :=
  30 * (X.W₀ + gsX hmb X.W₀ + gsWc X.Nm + X.Nm ^ 2 + 10) + 100

/-- **The polynomial bounds of a step of `transD`.** -/
structure TransBudget (X : Ctx) (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition)
    (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (E Kg dg p : ℕ) (K₂ : ℝ) : Prop where
  K_nn : 0 ≤ K₂
  one_le_p : 1 ≤ p
  enum : ∀ k W B, k ≤ X.Nm → W ≤ X.WB hmb →
    (enumCost hp hm k W B : ℝ) ≤ K₂ * ((B : ℝ) + 1) ^ p
  prod : ∀ k W B (gv Kv : Val), k ≤ X.Nm → W ≤ X.WB hmb → gv.wt ≤ X.W₀ → Kv.wt ≤ groupW k →
    (prodCostD hO hp hm k W B gv Kv : ℝ) ≤ K₂ * ((B : ℝ) + 1) ^ p
  norm : ∀ n m W, n ≤ X.Nm → m ≤ X.D → W ≤ X.WB hmb → (normStepCost hp hst hm n m W : ℝ) ≤ K₂
  solver : ∀ W, W ≤ X.W₀ → (Kg : ℝ) * ((W : ℝ) + 1) ^ dg ≤ K₂
  gate : ∀ k W N m, k ≤ X.Nm → W ≤ X.WB hmb → N ≤ X.Nm → m ≤ X.D →
    ((gateOwn W N m + 3 * (ansW k + 1) : ℕ) : ℝ) ≤ K₂
  adapter : ∀ k W, k ≤ X.Nm → W ≤ X.WB hmb → ((100 * W + 100 + ansW k : ℕ) : ℝ) ≤ K₂
  own : ∀ k W, k ≤ X.Nm → W ≤ X.W₀ →
    ((transOwn hmb hO h E X.D k W + 8 * (ansW k + 2) : ℕ) : ℝ) ≤ K₂

variable {Ω C : Type} {X : Ctx} {ks : Cst}

/-- **Own work added to a step.** -/
theorem Ctx.TransOut.add {K K' : ℝ} {R : State Ω C} {B : Child → ℝ} {c c' n : ℕ}
    (h : X.TransOut ks K R B c) (hle : c' ≤ c + n) (hn : (n : ℝ) ≤ K') :
    X.TransOut ks (K + K') R B c' := by
  have hc : (c' : ℝ) ≤ c + n := by exact_mod_cast hle
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases h with ⟨b, I, cs, a1, a2, a3, a4, a5, a6⟩ | ⟨r, I, cs, a1, a2, a3, a4, a5, a6⟩ |
    ⟨a1, a2⟩ | ⟨cs, a1, a2⟩
  · refine Or.inl ⟨b, I, cs, a1, a2, a3, a4, a5, ?_⟩
    nlinarith
  · refine Or.inr (Or.inl ⟨r, I, cs, a1, a2, a3, a4, a5, ?_⟩)
    nlinarith
  · exact Or.inr (Or.inr (Or.inl ⟨a1, by linarith⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨cs, a1, by linarith⟩))

theorem two_le_logD (D : ℕ) : 2 ≤ logD D := by
  have : 0 ≤ Real.log ((D : ℝ) + 2) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ D := Nat.cast_nonneg D; linarith)
  unfold logD
  linarith

theorem log2_le_logD (D : ℕ) : (Nat.log 2 D : ℝ) ≤ 2 * logD D := by
  have hL := two_le_logD D
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp only [Nat.log_zero_right, Nat.cast_zero]
    linarith
  have h1 : 2 ^ Nat.log 2 D ≤ D := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ) ^ Nat.log 2 D) ≤ D := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 : Real.log D ≤ Real.log ((D : ℝ) + 2) :=
    Real.log_le_log (by exact_mod_cast hD) (by linarith)
  have h5 := Real.log_two_gt_d9
  have h6 : (0 : ℝ) ≤ Nat.log 2 D := Nat.cast_nonneg _
  unfold logD at hL ⊢
  nlinarith

theorem le_add_one_pow {p : ℕ} (hp : 1 ≤ p) (n : ℕ) : (n : ℝ) ≤ ((n : ℝ) + 1) ^ p := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    _ = ((n : ℝ) + 1) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hp

/-- The bound on the branches of an enumeration. -/
theorem enum_I_le {E p b B D : ℕ} (hb : 2 ≤ b) (hB : B ≤ b ^ degExp E D) :
    ((B : ℝ) + 1) ^ p ≤ exp ((3 * (p : ℝ) * ((E : ℝ) + 1)) * logD D * Real.log b) := by
  set T := degExp E D with hT
  have hpos : 1 ≤ b ^ T := Nat.one_le_pow _ _ (by omega)
  have h1 : B + 1 ≤ b ^ (T + 1) := by
    rw [pow_succ]
    nlinarith
  have hbr : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have h2 : ((B : ℝ) + 1) ≤ (b : ℝ) ^ (T + 1) := by exact_mod_cast h1
  have h3 : (b : ℝ) ^ (T + 1) = exp (((T + 1 : ℕ) : ℝ) * Real.log b) := by
    rw [Real.exp_nat_mul, Real.exp_log hbr]
  have h4 : ((T + 1 : ℕ) : ℝ) ≤ 3 * ((E : ℝ) + 1) * logD D := by
    have hl := log2_le_logD D
    have hL := two_le_logD D
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
    have e : ((T + 1 : ℕ) : ℝ) = (E : ℝ) * ((Nat.log 2 D : ℝ) + 1) + 1 := by
      simp [hT, degExp]
    rw [e]
    nlinarith
  calc ((B : ℝ) + 1) ^ p ≤ (exp (((T + 1 : ℕ) : ℝ) * Real.log b)) ^ p := by
        rw [← h3]
        exact pow_le_pow_left₀ (by positivity) h2 p
    _ = exp ((p : ℝ) * (((T + 1 : ℕ) : ℝ) * Real.log b)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
        refine Real.exp_le_exp.2 ?_
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        have := mul_le_mul_of_nonneg_right h4 (mul_nonneg hp0 hlb)
        nlinarith

/-- The bound on the branches of a product. -/
theorem prod_I_le {p n D r₁ : ℕ} (hD : 2 ≤ D) (hr : 1 ≤ r₁) (hn : n ≤ D ^ r₁) :
    ((n : ℝ) + 1) ^ p ≤ exp ((2 * (p : ℝ)) * r₁ * logD D) := by
  have h0 : D ≤ D ^ r₁ := Nat.le_self_pow (by omega) D
  have h1 : n + 1 ≤ D ^ (2 * r₁) := by
    rw [two_mul, pow_add]
    nlinarith
  have hbr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have h2 : ((n : ℝ) + 1) ≤ (D : ℝ) ^ (2 * r₁) := by exact_mod_cast h1
  have h3 : (D : ℝ) ^ (2 * r₁) = exp (((2 * r₁ : ℕ) : ℝ) * Real.log D) := by
    rw [Real.exp_nat_mul, Real.exp_log hbr]
  have hlD : Real.log D ≤ logD D := by
    have : Real.log D ≤ Real.log ((D : ℝ) + 2) := Real.log_le_log hbr (by linarith)
    unfold logD
    linarith
  calc ((n : ℝ) + 1) ^ p ≤ (exp (((2 * r₁ : ℕ) : ℝ) * Real.log D)) ^ p := by
        rw [← h3]
        exact pow_le_pow_left₀ (by positivity) h2 p
    _ = exp ((p : ℝ) * (((2 * r₁ : ℕ) : ℝ) * Real.log D)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
        refine Real.exp_le_exp.2 ?_
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        have hr0 : (0 : ℝ) ≤ r₁ := Nat.cast_nonneg r₁
        push_cast
        have := mul_le_mul_of_nonneg_left hlD (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0) hr0)
        nlinarith

theorem not_univOn_bot {S : State Ω C} (h2 : 2 ≤ S.size) : ¬ UnivOn S.dom ⊥ := by
  intro hu
  have hle : Nat.card S.dom ≤ 1 := by
    have hfin : Finite S.dom := by
      by_contra hni
      have : Infinite S.dom := not_finite_iff_infinite.1 hni
      have e : S.size = 0 := Nat.card_eq_zero_of_infinite
      omega
    have : Subsingleton S.dom := ⟨fun a b => Subtype.ext (hu a a.2 b b.2)⟩
    exact Finite.card_le_one_iff_subsingleton.2 this
  have e : S.size = Nat.card S.dom := rfl
  omega

/-- The caps of the coordinate intervals. -/
theorem caps_product {D : ℕ} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
    (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) (hc : ∀ I ∈ S.hier, I.cap ≤ D) :
    ∀ I ∈ Q.pre ++ Q.coordHier E ++ Q.post, I.cap ≤ D := by
  have h := caps_exposed Q hc
  intro I hI
  simp only [List.mem_append] at hI
  rcases hI with (hI | hI) | hI
  · exact h I (by simp [hI])
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hI
    exact (min_le_left _ _).trans (h Q.top (by simp))
  · exact h I (by simp [hI])

/-- A larger constant in `TransOut`. -/
theorem TransOut_le {K₄ K₅ : ℝ} {R : State Ω C} {B : Child → ℝ} {c : ℕ} (hle : K₄ ≤ K₅)
    (h : X.TransOut ks K₄ R B c) : X.TransOut ks K₅ R B c := by
  have hn : ((0 : ℕ) : ℝ) ≤ K₅ - K₄ := by simpa using hle
  have := h.add (c' := c) (n := 0) (by omega) hn
  rwa [add_sub_cancel] at this

theorem dres_rho_nonneg (T : State Ω C) : 0 ≤ T.dres.rho :=
  Nat.cast_nonneg (rhoNat T.hier)

section Branches

variable {F : Funs} {hmb : MinimalBlocks} {hO : GroupOrder} {h : JohnsonRecognition}
  {hp : Preimage} {hst : PointwiseStab} {hm : Membership}
  (ht : TransCode X F hmb hO h hp hst hm) {Kg dg p : ℕ} {K₂ : ℝ}
  (hb : TransBudget X hmb hO h hp hst hm ht.E Kg dg p K₂)
  {R : State Ω C} (hd : DGood X.D X.Nm R) (htr : R.Transitive) (h2 : 2 ≤ R.size)
  {B : Child → ℝ} (hB : X.Below (measure P₀ .cont R) B)
  {k : ℕ} {e : Ω ≃ Fin k} {cc : C → ℕ} (hcc : Function.Injective cc) {v gv₀ dv xv yv hv₀ rv : Val}
  (hcan : Canon e cc v R)
  (hvv : v = .list [.nat k, gv₀, dv, xv, yv, hv₀, rv, boolVal R.floor, .nat R.h, .nat R.N])

include hb hd htr h2 hB hcc hcan hvv

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000 in
/-- The enumeration branch. -/
theorem branch_enum (hcE : ks.cE = 3 * (p : ℝ) * ((ht.E : ℝ) + 1)) (Q : PrimitiveQuotient R)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) {gv rep hv' : Val}
    (hxw : (Val.list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt < gsX hmb v.wt)
    (hrep : ReprVal k rep fun i j => Q.labFin e i = Q.labFin e j)
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post))
    (hs : Nat.card Q.ρ.range ≤ Q.d ^ degExp ht.E X.D) :
    FunAll X.Pg ht.fen (.list [v, rep, hv', .nat (Nat.card Q.ρ.range)]) fun u c =>
      AnsC e u R.answer ∧ X.TransOut ks (K₂ + K₂ + K₂) R B c := by
  have hfin : Finite Ω := hd.finite
  have hK0 := hb.K_nn
  have hcanL : Canon e cc (.list [.nat k, gv₀, dv, xv, yv, hv₀, rv, boolVal R.floor, .nat R.h,
      .nat R.N]) R := hvv ▸ hcan
  have hkN : k ≤ X.Nm := Ctx.k_le_Nm hd hcan
  have wv : v.wt ≤ X.W₀ := Ctx.wt_le_W₀ hd hcan
  have wgX := gsX_mono hmb wv
  have wk2 : k ^ 2 ≤ X.Nm ^ 2 := Nat.pow_le_pow_left hkN 2
  have wrep : rep.wt < (Val.list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt :=
    wt_le_wt_list (by simp)
  have whv : hv'.wt < (Val.list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt :=
    wt_le_wt_list (by simp)
  set B' := Nat.card Q.ρ.range with hB'
  have wB' : (Val.nat B').wt ≤ Q.d ^ 2 + 3 := wt_card_le _
  have hd2 : Q.d ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (Q.d_le_card e) 2
  have w4 := Lang.wt_list4_le v rep hv' (.nat B')
  have wW : (Val.list [v, rep, hv', .nat B']).wt ≤ X.WB hmb := by
    unfold Ctx.WB
    omega
  have hcall : ∀ (t : Perm (Fin k)) (val : Val), Canon e cc val (enumChild R Q e t) →
      FunAll X.Pg F.cont val (ChildPost (fun T => B ⟨Ω, C, T, false⟩) (enumChild R Q e t) e) :=
    fun t val hval => by
      obtain ⟨f1, f2, f3, -⟩ := enumChild_facts Q hd htr h2 R.x (R.y ∘ (toFin e).symm t)
      rw [ht.hcont]
      exact Ctx.below_call hB hcc f1 f2 f3 hval
  have s := ht.en (fun T => B ⟨Ω, C, T, false⟩) hcanL Q (Q.kernel_keeps hkc hkl) hrep hH
    (le_refl _) hcall
  rw [← hvv] at s
  refine s.mono ?_
  rintro u cost ⟨ha, L, hL, hc⟩
  have hbudget := hb.enum k _ B' hkN wW
  have h1I : (1 : ℝ) ≤ ((B' : ℝ) + 1) ^ p :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ B' := Nat.cast_nonneg B'; linarith)
  have hsum : (L.map fun t => B ⟨Ω, C, enumChild R Q e t, false⟩).sum =
      ((L.map fun t => (⟨Ω, C, enumChild R Q e t, false⟩ : Child)).map B).sum := by
    rw [List.map_map]
    rfl
  refine ⟨ha, TransOut_le (K₄ := K₂) (by linarith)
    (Or.inl ⟨Q.d, ((B' : ℝ) + 1) ^ p, L.map fun t => ⟨Ω, C, enumChild R Q e t, false⟩, Q.two_le,
      Q.d_le_size, h1I, ?_, ⟨?_, ?_⟩, ?_⟩)⟩
  · rw [hcE]
    exact enum_I_le Q.two_le hs
  · rw [List.length_map]
    have e1 : (L.length : ℝ) ≤ B' := by exact_mod_cast hL
    exact e1.trans (le_add_one_pow hb.one_le_p B')
  · intro c hc'
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨-, -, -, f4, f5, f6, f7⟩ :=
      enumChild_facts Q hd htr h2 R.x (R.y ∘ (toFin e).symm t)
    exact ⟨rfl, f4, f5, f6, f7⟩
  · rw [← hsum]
    have e2 : K₂ * (1 + ((B' : ℝ) + 1) ^ p) = K₂ + K₂ * ((B' : ℝ) + 1) ^ p := by ring
    rw [e2]
    linarith

set_option maxHeartbeats 2000000 in
/-- The product branch. -/
theorem branch_prod (hcP : ks.cP = 2 * (p : ℝ)) (hD6 : 6 ≤ X.D) (Q : PrimitiveQuotient R)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) {gv rep hv' : Val}
    (hxw : (Val.list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt < gsX hmb v.wt)
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post)) {m l r : ℕ}
    (E' : Fin Q.d ≃ (Fin r → {A : Finset (Fin m) // A.card = l})) (hR : RecogRange m l)
    (hM : MarotiStructure Q.ρ.range E') (h2r : 2 ≤ r)
    (wz : (Val.list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E']).wt ≤ gsWc k) :
    FunAll X.Pg ht.fpr (.list [v, .list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
      .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E']]) fun u c =>
      AnsC e u R.answer ∧ X.TransOut ks (K₂ + K₂ + K₂) R B c := by
  have hfin : Finite Ω := hd.finite
  have hK0 := hb.K_nn
  have hcanL : Canon e cc (.list [.nat k, gv₀, dv, xv, yv, hv₀, rv, boolVal R.floor, .nat R.h,
      .nat R.N]) R := hvv ▸ hcan
  have hkN : k ≤ X.Nm := Ctx.k_le_Nm hd hcan
  have wv : v.wt ≤ X.W₀ := Ctx.wt_le_W₀ hd hcan
  have wgX := gsX_mono hmb wv
  have wWc : gsWc k ≤ gsWc X.Nm := by
    unfold gsWc
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have wk2 : k ^ 2 ≤ X.Nm ^ 2 := Nat.pow_le_pow_left hkN 2
  have hgam : GammaHat X.D Q.ρ.range :=
    GammaHat.of_surjective Q.ρ.rangeRestrict Q.ρ.rangeRestrict_surjective hd.gamma
  have wg₀ : gv₀.wt ≤ X.W₀ := by
    have : gv₀.wt < v.wt := by
      rw [hvv]
      exact wt_le_wt_list (by simp)
    omega
  have hS := Q.productStructure_of_maroti hM
  have hkeep : CarrierOK (Q.coordinateGroup E' hS (Q.two_le_choose E')) R.dom R.rows
      (Q.pre ++ Q.coordHier E' ++ Q.post) := Q.productRed_keeps P₀ hkc hkl ⟨m, l, r, E', hS, h2r⟩
  have w3 := Lang.wt_list3_le v
    (Val.list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length])
    (Val.list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E'])
  have wW : (Val.list [v, .list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
      .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E']]).wt ≤ X.WB hmb := by
    unfold Ctx.WB
    omega
  have hcaps : ∀ I : DispatchStep P₀ R, I.hier' = Q.pre ++ Q.coordHier E' ++ Q.post →
      ∀ J ∈ I.hier', J.cap ≤ X.D := fun I hH' => by
    rw [hH']
    exact caps_product Q E' hd.caps
  have hcall : ∀ (I : DispatchStep P₀ R), I.kind = .product r →
      I.K = Q.coordinateGroup E' hS (Q.two_le_choose E') →
      I.hier' = Q.pre ++ Q.coordHier E' ++ Q.post → ∀ (t : Perm (Fin k)) (val : Val),
      Canon e cc val (tailChild R I.toData e t) →
      FunAll X.Pg F.cont val (ChildPost (fun T => B ⟨Ω, C, T, false⟩)
        (tailChild R I.toData e t) e) := fun I hk _ hH' t val hval => by
    obtain ⟨f1, f2, f3, -⟩ := prodChild_facts hd htr I (hcaps I hH') hk R.x
      (R.y ∘ (toFin e).symm t)
    rw [ht.hcont]
    exact Ctx.below_call hB hcc f1 f2 f3 hval
  have s := ht.pr (fun T => B ⟨Ω, C, T, false⟩) hcanL Q E' hS h2r hkeep (gv' := gv) (rep := rep)
    hH hcall
  rw [← hvv] at s
  refine s.mono ?_
  rintro u cost ⟨ha, I, Kv, L, hk, hK, hH', hn, hKv, hL, hc⟩
  have hbudget := hb.prod k _ I.n gv₀ Kv hkN wW wg₀ hKv.wt_le
  have hidx : I.n ≤ X.D ^ (r - 1) := by
    rw [hn]
    exact index_coordinate_le_pow Q hS hR (by omega) hD6 hM hgam _
  have hr1 : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have h1I : (1 : ℝ) ≤ ((I.n : ℝ) + 1) ^ p :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ I.n := Nat.cast_nonneg _; linarith)
  have hsum : (L.map fun t => B ⟨Ω, C, tailChild R I.toData e t, false⟩).sum =
      ((L.map fun t => (⟨Ω, C, tailChild R I.toData e t, false⟩ : Child)).map B).sum := by
    rw [List.map_map]
    rfl
  refine ⟨ha, TransOut_le (K₄ := K₂) (by linarith)
    (Or.inr (Or.inl ⟨r - 1, ((I.n : ℝ) + 1) ^ p,
      L.map fun t => ⟨Ω, C, tailChild R I.toData e t, false⟩, by omega, ?_, h1I, ?_, ⟨?_, ?_⟩,
      ?_⟩))⟩
  · obtain ⟨-, -, -, -, -, f6, -⟩ := prodChild_facts hd htr I (hcaps I hH') hk R.x R.y
    have h0 : 0 ≤ (R.restrict I.K I.K_le R.x R.y I.hier').dres.rho := by
      exact dres_rho_nonneg _
    rw [hr1]
    linarith
  · rw [hcP]
    exact prod_I_le (by omega) (by omega) hidx
  · rw [List.length_map]
    have e1 : (L.length : ℝ) ≤ I.n := by exact_mod_cast hL
    exact e1.trans (le_add_one_pow hb.one_le_p _)
  · intro c hc'
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨-, -, -, f4, f5, f6, f7⟩ := prodChild_facts hd htr I (hcaps I hH') hk R.x
      (R.y ∘ (toFin e).symm t)
    refine ⟨rfl, f4, f5, ?_, f7⟩
    rw [hr1]
    exact f6
  · rw [← hsum]
    have e2 : K₂ * (1 + ((I.n : ℝ) + 1) ^ p) = K₂ + K₂ * ((I.n : ℝ) + 1) ^ p := by ring
    rw [e2]
    linarith

omit h2 in
/-- The calls of a normalization. -/
theorem norm_calls (hNs : Ctx.Ready R) (hcont : F.cont = X.contD) (hgiant : F.giant = X.giantD)
    (hlab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
      (L : SuppliedLabels S), LabValStd e S lv L → X.I.LabVal e S lv L)
    (hlabW : ∀ k N, labWStd k N ≤ X.I.labW k N) (h2 : 2 ≤ R.size) (N : NormAbove P₀ R)
    (hlt : N.I.q ^ 5 < R.N ^ 2) (hc : ∀ J ∈ N.I.hier', J.cap ≤ X.D) (b : Bool)
    (hbm : ∀ j, (normMode b = .cont ∧ ¬ (N.child j).Transitive) ∨
      (normMode b = .giant ∧ (N.child j).Transitive)) (lv : Val)
    (hlv : ∀ j, LabValStd e (N.child j) lv (N.childLabels j)) (j : Fin N.I.k) (val : Val)
    (hval : Canon e cc val (N.child j)) :
    FunAll X.Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
      (ChildPost (fun T => B ⟨Ω, C, T, b⟩) (N.child j) e) := by
  have hfin : Finite Ω := hd.finite
  cases b with
  | false =>
    have hnt : ¬ (N.child j).Transitive :=
      ((hbm j).resolve_right fun h' => by simpa [normMode] using h'.1).2
    obtain ⟨f1, f2, f3, -⟩ := normChild_cont N hd htr h2 hc (fun h' => hnt h') j
    show FunAll X.Pg F.cont val _
    rw [hcont]
    exact Ctx.below_call hB hcc f1 f2 f3 hval
  | true =>
    have ht' : (N.child j).Transitive :=
      ((hbm j).resolve_left fun h' => by simpa [normMode] using h'.1).2
    obtain ⟨f1, f2, f3, -⟩ := normChild_giant N hd htr hNs h2 hc (fun v hv w hw => ht' v hv w hw) j
    have hL := hlab e _ lv _ (hlv j)
    have hIn : X.In .giant e cc (.list [val, lv]) (N.child j) :=
      ⟨⟨val, lv, N.childLabels j, rfl, hval, hL, N.q_large,
        ((hlv j).wt_le hval.small'.1).trans (hlabW _ _)⟩,
        fun _ => ⟨val, lv, N.childLabels j, rfl, hval, hL, N.q_large,
          ((hlv j).wt_le hval.small'.1).trans (hlabW _ _), hlt⟩⟩
    have s := hB ⟨Ω, C, N.child j, true⟩ ⟨f1, f2⟩ f3 k e cc hcc (.list [val, lv]) hIn
    show FunAll X.Pg F.giant _ _
    rw [hgiant]
    exact s

set_option maxHeartbeats 2000000 in
/-- The single-factor branch. -/
theorem branch_norm (hNs : Ctx.Ready R) (hc₀ : ks.c₀ ≤ cZero) {c₁ c₂ : ℝ}
    (hE : ht.E = caseE c₁ c₂ P₀.q₀)
    (hgs : ∀ v : Val, StateVal e cc v R → FunAll X.Pg ht.fs v fun u cost =>
      AnsC e u R.answer ∧
        (cost : ℝ) ≤ exp (ks.a * Real.log ((R.size : ℝ) + 2) ^ 2) + Kg * ((v.wt : ℝ) + 1) ^ dg)
    (hlab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
      (L : SuppliedLabels S), LabValStd e S lv L → X.I.LabVal e S lv L)
    (hlabW : ∀ k N, labWStd k N ≤ X.I.labW k N) (Q : PrimitiveQuotient R)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) {gv rep hv' : Val}
    (hxw : (Val.list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt < gsX hmb v.wt)
    (hnum : normNumbered e Q rep) (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post))
    (hns : ¬ Nat.card Q.ρ.range ≤ Q.d ^ degExp ht.E X.D) {m l : ℕ}
    (E' : Fin Q.d ≃ (Fin 1 → {A : Finset (Fin m) // A.card = l})) (hR : RecogRange m l)
    (hM : MarotiStructure Q.ρ.range E')
    (wz : (Val.list [.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E']).wt ≤ gsWc k) :
    FunAll X.Pg ht.fno (.list [v, .list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
      .list [.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E']]) fun u c =>
      AnsC e u R.answer ∧ X.TransOut ks (K₂ + K₂ + K₂) R B c := by
  have hfin : Finite Ω := hd.finite
  have hK0 := hb.K_nn
  have hcanL : Canon e cc (.list [.nat k, gv₀, dv, xv, yv, hv₀, rv, boolVal R.floor, .nat R.h,
      .nat R.N]) R := hvv ▸ hcan
  have hkN : k ≤ X.Nm := Ctx.k_le_Nm hd hcan
  have wv : v.wt ≤ X.W₀ := Ctx.wt_le_W₀ hd hcan
  have wgX := gsX_mono hmb wv
  have wWc : gsWc k ≤ gsWc X.Nm := by
    unfold gsWc
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have wk2 : k ^ 2 ≤ X.Nm ^ 2 := Nat.pow_le_pow_left hkN 2
  have hNle : R.N ≤ X.Nm := hd.N_le
  have hS := Q.productStructure_of_maroti hM
  have hgam : GammaHat X.D Q.ρ.range :=
    GammaHat.of_surjective Q.ρ.rangeRestrict Q.ρ.rangeRestrict_surjective hd.gamma
  have hmD : m ≤ X.D := recog_le_D hR le_rfl hM hgam
  have hT : P₀.q₀.factorial ≤ degExp ht.E X.D := by
    have := le_degExp c₁ c₂ P₀.q₀ X.D
    rw [hE]
    omega
  have hq : P₀.q₀ < m := recog_q₀_lt hR hM Q.two_le hT hns
  have hne : R.dom.Nonempty := by
    obtain ⟨⟨x⟩, -⟩ := Nat.card_pos_iff.1 (show 0 < Nat.card R.dom by change 0 < R.size; omega)
    exact ⟨x.1, x.2⟩
  set x := Val.list [gv, rep, hv', encFun (Q.labFin e), .nat Q.pre.length] with hx
  set z := Val.list [.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E'] with hz
  have w3 := Lang.wt_list3_le v x z
  have wW : (Val.list [v, x, z]).wt ≤ X.WB hmb := by
    unfold Ctx.WB
    omega
  have wrep : rep.wt < x.wt := wt_le_wt_list (by simp)
  have whv : hv'.wt < x.wt := wt_le_wt_list (by simp)
  have wm : (Val.nat m).wt < z.wt := wt_le_wt_list (by simp)
  have wl : (Val.nat l).wt < z.wt := wt_le_wt_list (by simp)
  have wE : (encKSetTuples E').wt < z.wt := wt_le_wt_list (by simp)
  have w6 : (Val.list [v, rep, hv', .nat m, .nat l, encKSetTuples E']).wt ≤ X.WB hmb := by
    have := wt_list_le [v, rep, hv', .nat m, .nat l, encKSetTuples E']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    unfold Ctx.WB
    omega
  have hgate := normGate_spec (Post := fun u c => AnsC e u R.answer ∧
    X.TransOut ks (K₂ + K₂) R B c) (k := k) (N := R.N) (m := m) (l := l) (r := 1) (gv := gv₀)
    (dv := dv) (xv := xv) (yv := yv) (hv := hv₀) (rv := rv) (fv := boolVal R.floor) (hh := .nat R.h)
    (x := x) (E' := encKSetTuples E') ht.hgate ?_ ?_
  · rw [← hvv] at hgate
    refine hgate.mono ?_
    rintro u cost ⟨c₀, ⟨ha, hout⟩, hle⟩
    have hle' : cost ≤ c₀ + gateOwn (Val.list [v, x, z]).wt R.N m + 3 * (u.wt + 1) := hle
    have hu := ha.wt_le
    have hg := hb.gate k _ R.N m hkN wW hNle hmD
    exact ⟨ha, hout.add (by omega) hg⟩
  · intro hlt
    rw [← hvv]
    have hstep := ht.no (Ω := Ω) (C := C) e cc (fun b T => B ⟨Ω, C, T, b⟩) hcanL hne htr Q E' hS hq
      hkc hkl hnum hH fun Dc b hbm lv hlv j val hval =>
        norm_calls ht hb hd htr hB hcc hcan hvv hNs ht.hcont ht.hgiant hlab hlabW h2
          (Q.normAboveOf Dc.choice htr hq hkc hkl) hlt
          (caps_exposed Q hd.caps) b hbm lv hlv j val hval
    rw [← hvv] at hstep
    have hstep' : FunAll X.Pg ht.fn (.list [v, rep, hv', .nat m, .nat l, encKSetTuples E'])
        fun u c => AnsC e u R.answer ∧ X.TransOut ks K₂ R B c := by
      refine hstep.mono ?_
      rintro u cost ⟨ha, Dc, b, hbm, hcost⟩
      set N := Q.normAboveOf Dc.choice htr hq hkc hkl with hN
      have hbudget := hb.norm k m _ hkN hmD w6
      have hsum : ∑ j : Fin N.I.k, B ⟨Ω, C, N.child j, b⟩ =
          (((List.finRange N.I.k).map fun j => (⟨Ω, C, N.child j, b⟩ : Child)).map B).sum := by
        rw [List.map_map, Fin.sum_univ_def]
        rfl
      refine ⟨ha, Or.inr (Or.inr (Or.inr ⟨(List.finRange N.I.k).map fun j => ⟨Ω, C, N.child j, b⟩,
        ⟨by simpa using N.I.k_le, fun c hc' => ?_⟩, ?_⟩))⟩
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc'
        cases b with
        | false =>
          have hnt : ¬ (N.child j).Transitive :=
            ((hbm j).resolve_right fun h' => by simpa [normMode] using h'.1).2
          obtain ⟨-, -, -, f4, f5, f6, f7⟩ :=
            normChild_cont N hd htr h2 (caps_exposed Q hd.caps) (fun h' => hnt h') j
          refine ⟨f4, f5, f6, ?_⟩
          show (N.child j).dres.psi + ks.c₀ ≤ R.dres.psi
          linarith
        | true =>
          have ht' : (N.child j).Transitive :=
            ((hbm j).resolve_left fun h' => by simpa [normMode] using h'.1).2
          obtain ⟨-, -, -, f4⟩ := normChild_giant N hd htr hNs h2 (caps_exposed Q hd.caps)
            (fun v hv w hw => ht' v hv w hw) j
          exact ⟨f4.s, f4.rho, f4.Q, f4.psi⟩
      · rw [← hsum]
        linarith
    refine (normAd_spec ht.had hstep').mono ?_
    rintro u cost ⟨c₀, ⟨ha, hout⟩, hle⟩
    have hle' : cost ≤ c₀ + 100 * (Val.list [v, x, z]).wt + 100 + u.wt := hle
    have hu := ha.wt_le
    exact ⟨ha, hout.add (n := 100 * (Val.list [v, x, z]).wt + 100 + ansW k) (by omega)
      (hb.adapter k _ hkN wW)⟩
  · intro hnlt
    rw [← hvv]
    have hsz : R.size ^ 2 ≤ X.D ^ 5 := by
      have h5 : m ^ 5 ≤ X.D ^ 5 := Nat.pow_le_pow_left hmD 5
      have e1 : R.N = R.size := hNs
      rw [← e1]
      omega
    refine (hgs v hcan.stateVal).mono fun u c hq' => ⟨hq'.1, Or.inr (Or.inr (Or.inl ⟨hsz, ?_⟩))⟩
    have := hb.solver v.wt wv
    linarith [hq'.2]

end Branches

set_option maxHeartbeats 4000000 in
/-- **The field `trans` of `Ops`.** -/
theorem ops_trans {F : Funs} {hmb : MinimalBlocks} {hO : GroupOrder} {h : JohnsonRecognition}
    {hp : Preimage} {hst : PointwiseStab} {hm : Membership}
    (ht : TransCode X F hmb hO h hp hst hm) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hA : AltAt c₁ c₂ P₀.q₀) (hE : ht.E = caseE c₁ c₂ P₀.q₀) (hD6 : 6 ≤ X.D)
    {Kg dg p : ℕ} {K₂ : ℝ} (hb : TransBudget X hmb hO h hp hst hm ht.E Kg dg p K₂)
    (hgs : ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
      Function.Injective c → ∀ v : Val, StateVal e c v S →
        FunAll X.Pg ht.fs v fun u cost => AnsC e u S.answer ∧
          (cost : ℝ) ≤ exp (ks.a * Real.log ((S.size : ℝ) + 2) ^ 2) + Kg * ((v.wt : ℝ) + 1) ^ dg)
    (hcE : ks.cE = 3 * (p : ℝ) * ((ht.E : ℝ) + 1)) (hcP : ks.cP = 2 * (p : ℝ))
    (hc₀ : ks.c₀ ≤ cZero)
    (hlab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
      (L : SuppliedLabels S), LabValStd e S lv L → X.I.LabVal e S lv L)
    (hlabW : ∀ k N, labWStd k N ≤ X.I.labW k N)
    (R : State Ω C) (hd : DGood X.D X.Nm R) (htr : R.Transitive) (h2 : 2 ≤ R.size)
    (hNs : Ctx.Ready R) (B : Child → ℝ) (hB : X.Below (measure P₀ .cont R) B)
    (k : ℕ) (e : Ω ≃ Fin k) (cc : C → ℕ) (hcc : Function.Injective cc) (v : Val)
    (hv : X.In .cont e cc v R) :
    FunAll X.Pg X.transD v fun u cost =>
      AnsC e u R.answer ∧ X.TransOut ks (K₂ + K₂ + K₂ + K₂) R B cost := by
  have hcan : Canon e cc v R := hv.1
  have hfin : Finite Ω := hd.finite
  have hK0 := hb.K_nn
  obtain ⟨gv₀, dv, xv, yv, hv₀, rv, -, -, -, -, -, -, hvv⟩ := hcan.val
  have hkN : k ≤ X.Nm := Ctx.k_le_Nm hd hcan
  have wv : v.wt ≤ X.W₀ := Ctx.wt_le_W₀ hd hcan
  have wgX := gsX_mono hmb wv
  have wWc : gsWc k ≤ gsWc X.Nm := by
    unfold gsWc
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have wk2 : k ^ 2 ≤ X.Nm ^ 2 := Nat.pow_le_pow_left hkN 2
  have hgam : ∀ Q : PrimitiveQuotient R, GammaHat X.D Q.ρ.range := fun Q =>
    GammaHat.of_surjective Q.ρ.rangeRestrict Q.ρ.rangeRestrict_surjective hd.gamma
  have hq₀ : 8 ≤ P₀.q₀ := by norm_num [P₀]
  have hne : R.dom.Nonempty := by
    obtain ⟨⟨x⟩, -⟩ := Nat.card_pos_iff.1 (show 0 < Nat.card R.dom by change 0 < R.size; omega)
    exact ⟨x.1, x.2⟩
  have hcanL : Canon e cc (.list [.nat k, gv₀, dv, xv, yv, hv₀, rv, boolVal R.floor, .nat R.h,
      .nat R.N]) R := hvv ▸ hcan
  have wg₀ : gv₀.wt ≤ X.W₀ := by
    have : gv₀.wt < v.wt := by
      rw [hvv]
      exact wt_le_wt_list (by simp)
    omega
  refine (trans_spec hmb hO h ht.hf ht.hexp ht.hjo ht.hc ht.htst ht.hjr ht.hbr hcan htr hd.hier
    (not_univOn_bot h2) (fun Q hc => recog_promise hc₁ hc₂ hq₀ hA hD6 Q.two_le Q.primitive (hgam Q)
      (hE ▸ hc)) (Post := fun u c => AnsC e u R.answer ∧ X.TransOut ks (K₂ + K₂ + K₂) R B c)
    ?_ ?_ ?_).mono ?_
  · intro Q hkc hkl gv rep hv' hxw hrep hH hs
    exact branch_enum ht hb hd htr h2 hB hcc hcan hvv hcE Q hkc hkl hxw hrep hH hs
  · intro Q hkc hkl gv rep hv' hxw hgv' hnum hrep hH hns m l r E' hR hM h2r wz
    exact branch_prod ht hb hd htr h2 hB hcc hcan hvv hcP hD6 Q hkc hkl hxw hH E' hR hM h2r wz
  · intro Q hkc hkl gv rep hv' hxw hgv' hnum hH hns m l r E' hR hM hr1 hr2 wz
    obtain rfl : r = 1 := by omega
    exact branch_norm ht hb hd htr h2 hB hcc hcan hvv hNs hc₀ hE
      (fun v hv' => hgs R k e cc hcc v hv') hlab hlabW Q hkc hkl hxw hnum hH hns E' hR hM wz
  · rintro u cost ⟨c₀, ⟨ha, hout⟩, hle⟩
    refine ⟨ha, hout.add (n := transOwn hmb hO h ht.E X.D k v.wt + 8 * (ansW k + 2)) ?_ ?_⟩
    · have := ha.wt_le
      omega
    · exact hb.own k v.wt hkN wv

end GI.Degree
