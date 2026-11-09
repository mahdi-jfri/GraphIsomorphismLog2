module

public import Workspace.Degree.Class
public import Workspace.Degree.Potential
public import Workspace.Impl.Weights
public import Workspace.Impl.Skeleton

@[expose] public section

/-!
# The spine of the proof

This file proves the main bound of Sections 8.5 and 8.6 of the paper for the new program, by one
induction on the termination measure, with each operation of the program as a named hypothesis
(`Ops`). The hypotheses are facts about the program text and about states. Their proofs come later.
This file shows that they give the bound.

**The functions.** `contD` handles a state of `Continue`, and `giantD` a state of `GiantStep`.
`transD` handles a transitive state after the reset. The program never reads `D`. It is a
parameter of the analysis, and any bound on the degree serves.

**What the program does at a call**, as `contD` runs on `T`:

1. `T` is small (`IsSmall`): call the general solver. The operation is `Ops.base`.
2. `T` is not transitive: the orbit chain, `Ops.orbit`.
3. Otherwise reset to a state `R` of the same size, with `N = s` (`Ops.reset`), and run `transD`.
   It takes one of three cases: `Ops.enum`, `Ops.product`, `Ops.norm`. In the last case a state
   with `s² ≤ q⁵` goes to the general solver. There `q ≤ D`, so `s² ≤ D⁵`.

`giantD` is `Ops.giant`, whose children are charged calls, halving calls and overcosets.

**How the hypotheses speak of costs.** A call's children are known only once the program runs,
since a script chooses its next call from the last answer. So an operation does not name its
children in advance. `Runs` says: whatever bounds `B` hold for the calls below, the call returns the
right answer, and there is a list `cs` of children of the right shape such that its cost is at most
the node's own work plus `B` summed over `cs`.

**What `K` depends on.** `K` is built from `K₁`, the bound on the node's own work in `Ops`. `K₁` may
depend on `D` and on `Nm`, the root's bound for `N`, and on nothing else, so one `K` serves the whole
recursion. `Nm` is fixed along the recursion by `DGood.N_le`.

**Where the costs are paid.**

* The own work of a node is at most `K₁`, or `K₁ (1 + I)` when the node has `I` branches. It
  includes all the polynomial work, since values have weight polynomial in `Nm` and `D`:
  `value_wt_le` proves this and the bound needs nothing else. It also includes the calls to the
  general solver made in a round of `giantD`, on at most `q²` positions with `q ≤ D`. Each costs
  `exp(O(L²))` times a polynomial, and there are polynomially many.
* A state with `IsBase` calls the solver directly. If `s ≤ ρ`, the term `ρ L` of the potential pays
  (`Res.baseRho_closes`). If `s² ≤ D⁵` the cost is at most `exp(9 a L²)`, a term of `K`. If
  `s ≤ N₀` the cost is a constant, a term of `K`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Real
open GI.Cited (Val)

/-- `L = log(D + 2) + 2`. The constant term gives `L ≥ 2`, and the operations use that. -/
noncomputable def logD (D : ℕ) : ℝ := Real.log ((D : ℝ) + 2) + 2

theorem logD_ge (D : ℕ) : 2 ≤ logD D := by
  unfold logD
  have : 0 ≤ Real.log ((D : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    linarith)
  linarith

variable {Ω C : Type}

/-- **The invariant of the recursion.** `Nm` is the root's bound for `N`. -/
structure DGood (D Nm : ℕ) (S : State Ω C) : Prop where
  finite : Finite Ω
  N_gt : P₀.N₀ < S.N
  N_le : S.N ≤ Nm
  size_le : S.size ≤ S.N
  hier : S.HierInv
  rows : S.rows = none
  floor : S.floor = false
  h : S.h = 2
  caps : ∀ I ∈ S.hier, I.cap ≤ D
  gamma : GammaHat D S.G

theorem DGood.good {D Nm : ℕ} {S : State Ω C} (h : DGood D Nm S) : Good P₀ .cont S :=
  ⟨h.N_gt, h.size_le, h.hier⟩

/-- The values along the recursion stay polynomial in the root: `Canon` bounds the weight of
a value by `N`, and `DGood` bounds `N` by the root's `Nm`. So the arguments of every call in the
recursion have weight polynomial in `Nm + D`. -/
theorem value_wt_le {D Nm k : ℕ} {S : State Ω C} {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val}
    (hS : DGood D Nm S) (hv : GI.Impl.Canon e c v S) :
    (Val.list [.nat D, v]).wt ≤ 2 * (D + 2 + 10 ^ 4 * (Nm + 2) ^ 6) + 6 := by
  have h1 := wt_list2_le (.nat D) v
  have h2 := wt_nat_le D
  have h3 := hv.wt_le_poly
  have h4 : (S.N + 2) ^ 6 ≤ (Nm + 2) ^ 6 := Nat.pow_le_pow_left (by have := hS.N_le; omega) 6
  omega

/-- A call of the recursion, on a state of any types. -/
structure Child where
  Ω : Type
  C : Type
  T : State Ω C
  /-- The call is to `giantD`, not `contD`. -/
  giant : Bool

/-- The mode of a call. -/
def Child.mode (c : Child) : Mode := bif c.giant then .giant else .cont

/-- The resources of a call. -/
noncomputable def Child.res (c : Child) : Res := c.T.dres

/-- The fixed data of the recursion. -/
structure Ctx where
  /-- The program. -/
  Pg : Program
  /-- The interface for labels. -/
  I : Iface
  contD : ℕ
  transD : ℕ
  giantD : ℕ
  /-- The degree bound. -/
  D : ℕ
  /-- The root's bound for `N`. -/
  Nm : ℕ

/-- The constants of the operations, which depend on neither `D` nor `Nm`. Here `a` is the exponent
of the general solver, `cE` that of the primitive enumeration, `Cm, am` bound the mass of the
local calls, `Co, ao` the number of continuations, and `c₀`, `δ` are the drops of `ψ` and of `Q`. -/
structure Cst where
  a : ℝ
  cE : ℝ
  /-- The exponent of the product branches. -/
  cP : ℝ
  Cm : ℝ
  am : ℝ
  Co : ℝ
  ao : ℝ
  c₀ : ℝ
  δ : ℝ
  A : ℝ
  a_nn : 0 ≤ a
  cE_nn : 0 ≤ cE
  cP_nn : 0 ≤ cP
  Cm_nn : 0 ≤ Cm
  Co_nn : 0 ≤ Co
  cond : ACond a cE cP Cm am Co ao c₀ δ A

/-- **One choice of `A`, for all operations.** The exponent `p = 3` is fixed in `Res.W`. -/
theorem exists_cst {a cE cP Cm am Co ao c₀ δ : ℝ} (ha : 0 ≤ a) (hcE : 0 ≤ cE) (hcP : 0 ≤ cP)
    (hCm : 0 ≤ Cm) (hCo : 0 ≤ Co) (hc₀ : 0 < c₀) (hδ : 0 < δ) :
    ∃ ks : Cst, ks.a = a ∧ ks.cE = cE ∧ ks.cP = cP ∧ ks.Cm = Cm ∧ ks.am = am ∧ ks.Co = Co ∧
      ks.ao = ao ∧ ks.c₀ = c₀ ∧ ks.δ = δ := by
  obtain ⟨A, hA⟩ := exists_A (a := a) (cE := cE) (cP := cP) (Cm := Cm) (am := am) (Co := Co)
    (ao := ao) hcP hc₀ hδ
  exact ⟨⟨a, cE, cP, Cm, am, Co, ao, c₀, δ, A, ha, hcE, hcP, hCm, hCo, hA⟩, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

namespace Ctx

variable (X : Ctx) (ks : Cst)

/-- The function of a call. -/
def fn (giant : Bool) : ℕ := bif giant then X.giantD else X.contD

/-- The input of a call: `Iface.InVal`. A call of `giantD` also has labels with `q⁵ < N²`. -/
def In {Ω C : Type} {k : ℕ} (m : Mode) (e : Ω ≃ Fin k) (cc : C → ℕ) (v : Val) (T : State Ω C) :
    Prop :=
  X.I.InVal m e cc v T ∧ (m = .giant → ∃ (sv lv : Val) (L : SuppliedLabels T),
    v = .list [sv, lv] ∧ Canon e cc sv T ∧ X.I.LabVal e T lv L ∧ P₀.q₀ < L.q ∧
      lv.wt ≤ X.I.labW k T.N ∧ L.q ^ 5 < T.N ^ 2)

/-- The call on `c` returns the exact answer, at a cost of at most `b`. -/
def Spec (c : Child) (b : ℝ) : Prop :=
  ∀ (k : ℕ) (e : c.Ω ≃ Fin k) (cc : c.C → ℕ), Function.Injective cc → ∀ v : Val,
    X.In c.mode e cc v c.T →
      FunAll X.Pg (X.fn c.giant) v fun u cost =>
        AnsC e u c.T.answer ∧ (cost : ℝ) ≤ b

/-- The invariant of a call. -/
def Good (c : Child) : Prop :=
  DGood X.D X.Nm c.T ∧ GI.Algorithm.Good P₀ c.mode c.T

/-- `B` bounds every call below the measure `μ`. -/
def Below (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (B : Child → ℝ) : Prop :=
  ∀ c : Child, X.Good c → MLt (measure P₀ c.mode c.T) μ → X.Spec c (B c)

/-- **A node**: function `f` on a state `T` in mode `m`. If `B` bounds the calls below `μ`, the call
returns the exact answer, and there are children `cs` of shape `Shape` such that its cost is at most
`own` plus the sum of `B` over `cs`. -/
def Runs (f : ℕ) (m : Mode) (T : State Ω C) (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (own : ℝ)
    (Shape : List Child → Prop) : Prop :=
  ∀ B : Child → ℝ, X.Below μ B → ∀ (k : ℕ) (e : Ω ≃ Fin k) (cc : C → ℕ), Function.Injective cc →
    ∀ v : Val, X.In m e cc v T →
      FunAll X.Pg f v fun u cost =>
        AnsC e u T.answer ∧ ∃ cs, Shape cs ∧ (cost : ℝ) ≤ own + (cs.map B).sum

/-- `R` is a state after a reset: its phase is its domain. -/
def Ready (R : State Ω C) : Prop :=
  R.N = R.size

/-- `T` is small, and `contD` sends it to the general solver. -/
def IsSmall (T : State Ω C) : Prop :=
  T.size ≤ max P₀.N₀ (rhoNat T.hier)

/-- A state that the general solver can pay for. -/
def IsBase (T : State Ω C) : Prop :=
  Ctx.IsSmall T ∨ T.size ^ 2 ≤ X.D ^ 5

/-- The children of the orbit chain: at most two, nonempty, smaller than `T`, with at most the
resources of `T`, and with sizes that sum to at most `s`. The list has one entry when the first call
returns an empty answer. -/
def OrbitShape (T : State Ω C) (cs : List Child) : Prop :=
  cs.length ≤ 2 ∧ (cs.map fun c => c.res.s).sum ≤ T.size ∧
    ∀ c ∈ cs, c.giant = false ∧ c.res.Le T.dres ∧ 1 ≤ c.res.s ∧ c.res.s < T.size

/-- The children of the enumeration of a primitive quotient of degree `b`, with `I` branches. -/
def EnumShape (T : State Ω C) (lb I : ℝ) (cs : List Child) : Prop :=
  (cs.length : ℝ) ≤ I ∧ ∀ c ∈ cs, c.giant = false ∧ c.res.s ≤ T.dres.s ∧
    c.res.psi + lb / 3 ≤ T.dres.psi ∧ c.res.rho ≤ T.dres.rho ∧ c.res.Q ≤ T.dres.Q

/-- The children of normalization on a product with `r₁ + 1` coordinates, with `I` branches. -/
def ProductShape (T : State Ω C) (r₁ I : ℝ) (cs : List Child) : Prop :=
  (cs.length : ℝ) ≤ I ∧ ∀ c ∈ cs, c.giant = false ∧ c.res.s ≤ T.dres.s ∧
    c.res.psi ≤ T.dres.psi ∧ c.res.rho + r₁ ≤ T.dres.rho ∧ c.res.Q ≤ T.dres.Q

/-- The children of the single-factor case: at most two. A child in `giantD` has at most the
resources of `T`. A child in `contD` has lower `ψ`. -/
def NormShape (T : State Ω C) (cs : List Child) : Prop :=
  cs.length ≤ 2 ∧ ∀ c ∈ cs, c.res.s ≤ T.dres.s ∧ c.res.rho ≤ T.dres.rho ∧ c.res.Q ≤ T.dres.Q ∧
    (if c.giant then c.res.psi ≤ T.dres.psi else c.res.psi + ks.c₀ ≤ T.dres.psi)

/-- A charged call or a halving call of a round: lower `ψ`. -/
def LocalChild (T : State Ω C) (c : Child) : Prop :=
  c.giant = false ∧ c.res.psi + ks.c₀ ≤ T.dres.psi ∧ c.res.rho ≤ T.dres.rho ∧ c.res.Q ≤ T.dres.Q

/-- A continuation on an overcoset: lower `Q`, by `δ log q`. -/
def OverChild (T : State Ω C) (lq : ℝ) (c : Child) : Prop :=
  c.giant = false ∧ c.res.s ≤ T.dres.s ∧ c.res.psi ≤ T.dres.psi ∧ c.res.rho ≤ T.dres.rho ∧
    c.res.Q + ks.δ * lq ≤ T.dres.Q

/-- The mass of a list of calls, relative to the parent: the local mass bound. -/
def MassOK (T : State Ω C) (cs : List Child) : Prop :=
  (cs.map fun c => c.res.sz ^ 3).sum ≤ ks.Cm * exp (ks.am * logD X.D) * T.dres.sz ^ 3

/-- The children of a round of `giantD`, where `lq = log q`. -/
def GiantShape (T : State Ω C) (lq : ℝ) (cs : List Child) : Prop :=
  ∃ ch hv ov, cs = ch ++ hv ++ ov ∧
    (∀ c ∈ ch, Ctx.LocalChild ks T c) ∧ X.MassOK ks T ch ∧
    (∀ c ∈ hv, Ctx.LocalChild ks T c) ∧ X.MassOK ks T hv ∧
    (∀ c ∈ ov, Ctx.OverChild ks T lq c) ∧
    (ov.length : ℝ) ≤ ks.Co * exp (ks.ao * lq)

end Ctx

/-- **What `transD` does at a state `R`** with bounds `B` on the calls below: a call that costs
`cost`, in one of four cases. The program picks the case as it runs, since the exposure may return
any primitive quotient. -/
def Ctx.TransOut (X : Ctx) (ks : Cst) (K₁ : ℝ) (R : State Ω C) (B : Child → ℝ) (cost : ℕ) : Prop :=
  (∃ (b : ℕ) (I : ℝ) (cs : List Child), 2 ≤ b ∧ b ≤ R.size ∧ 1 ≤ I ∧
    I ≤ exp (ks.cE * logD X.D * Real.log b) ∧ Ctx.EnumShape R (Real.log b) I cs ∧
    (cost : ℝ) ≤ K₁ * (1 + I) + (cs.map B).sum) ∨
  (∃ (r₁ : ℕ) (I : ℝ) (cs : List Child), 1 ≤ r₁ ∧ (r₁ : ℝ) ≤ R.dres.rho ∧ 1 ≤ I ∧
    I ≤ exp (ks.cP * r₁ * logD X.D) ∧ Ctx.ProductShape R r₁ I cs ∧
    (cost : ℝ) ≤ K₁ * (1 + I) + (cs.map B).sum) ∨
  (R.size ^ 2 ≤ X.D ^ 5 ∧ (cost : ℝ) ≤ K₁ + exp (ks.a * Real.log ((R.size : ℝ) + 2) ^ 2)) ∨
  (∃ cs : List Child, Ctx.NormShape ks R cs ∧ (cost : ℝ) ≤ K₁ + (cs.map B).sum)

/-- **The operations**, each a hypothesis. `K₁` bounds the own work of a node. -/
structure Ops (X : Ctx) (ks : Cst) (K₁ : ℝ) where
  /-- **The general solver** on a small state. -/
  base : ∀ {Ω C : Type} (T : State Ω C), DGood X.D X.Nm T → Ctx.IsSmall T →
    X.Runs X.contD .cont T (measure P₀ .cont T)
      (K₁ + exp (ks.a * Real.log ((T.size : ℝ) + 2) ^ 2)) (· = [])
  /-- **The orbit chain.** -/
  orbit : ∀ {Ω C : Type} (T : State Ω C), DGood X.D X.Nm T → ¬ Ctx.IsSmall T → ¬ T.Transitive →
    X.Runs X.contD .cont T (measure P₀ .cont T) K₁ (Ctx.OrbitShape T)
  /-- **The reset.** A large transitive state has a state `R` with no more resources and no
  larger measure, which is again transitive with the invariant. If `transD` costs at most `b` on `R`,
  then `contD` costs at most `K₁ + b` on `T`. -/
  reset : ∀ {Ω C : Type} (T : State Ω C), DGood X.D X.Nm T → ¬ Ctx.IsSmall T → T.Transitive →
    ∃ (Ω' C' : Type) (R : State Ω' C'), DGood X.D X.Nm R ∧ R.Transitive ∧ Ctx.Ready R ∧
      R.size = T.size ∧ R.dres.Le T.dres ∧
      (∀ μ, MLt μ (measure P₀ .cont R) → MLt μ (measure P₀ .cont T)) ∧
      ∀ b : ℝ, (∀ (k : ℕ) (e : Ω' ≃ Fin k) (cc : C' → ℕ), Function.Injective cc → ∀ v : Val,
          X.In .cont e cc v R → FunAll X.Pg X.transD v fun u cost =>
            AnsC e u R.answer ∧ (cost : ℝ) ≤ b) →
        ∀ (k : ℕ) (e : Ω ≃ Fin k) (cc : C → ℕ), Function.Injective cc → ∀ v : Val,
          X.In .cont e cc v T → FunAll X.Pg X.contD v fun u cost =>
            AnsC e u T.answer ∧ (cost : ℝ) ≤ K₁ + b
  /-- **The three cases of a reset state.** -/
  trans : ∀ {Ω C : Type} (R : State Ω C), DGood X.D X.Nm R → R.Transitive → 2 ≤ R.size →
    Ctx.Ready R → ∀ B : Child → ℝ, X.Below (measure P₀ .cont R) B →
      ∀ (k : ℕ) (e : Ω ≃ Fin k) (cc : C → ℕ), Function.Injective cc → ∀ v : Val,
        X.In .cont e cc v R → FunAll X.Pg X.transD v fun u cost =>
          AnsC e u R.answer ∧ X.TransOut ks K₁ R B cost
  /-- **A round of `GiantStep`**: charged calls, halving calls and overcosets. The calls to the
  general solver of the round are part of its own work. -/
  giant : ∀ {Ω C : Type} (T : State Ω C), DGood X.D X.Nm T → Good P₀ .giant T →
    X.Runs X.giantD .giant T (measure P₀ .giant T) K₁
      (fun cs => ∃ lq : ℝ, 1 ≤ lq ∧ X.GiantShape ks T lq cs)

namespace Cst

variable (ks : Cst)

theorem A_nn : 0 ≤ ks.A := by have := ks.cond.five; linarith

/-- The constant of the main bound. -/
noncomputable def K (K₁ L : ℝ) : ℝ :=
  4 * K₁ + 2 * exp (ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2) + 2 * exp (9 * ks.a * L ^ 2) + 2

/-- The bound of a call. A call to `giantD` gets a quarter of the bound. -/
noncomputable def bound (K L : ℝ) (c : Child) : ℝ :=
  bif c.giant then K * c.res.W ks.A L / 4 else K * c.res.W ks.A L

theorem bound_nn {K L : ℝ} (hK : 0 ≤ K) (c : Child) : 0 ≤ ks.bound K L c := by
  have := c.res.W_pos ks.A L
  unfold bound
  cases c.giant <;> simp <;> positivity

end Cst

section Closing

variable {X : Ctx} {ks : Cst} {K₁ : ℝ}

/-- The bound on a list of children, all in `contD`. -/
theorem sum_bound_eq {K L : ℝ} (cs : List Child) (h : ∀ c ∈ cs, c.giant = false) :
    (cs.map (ks.bound K L)).sum = K * ((cs.map Child.res).map fun r => r.W ks.A L).sum := by
  induction cs with
  | nil => simp
  | cons a l ih =>
    have h1 := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [List.map_cons, List.sum_cons, h1, mul_add]
    simp [Cst.bound, h a List.mem_cons_self]

/-- The own work of a node is paid by `K`, at a state with weight at least one. -/
theorem K_facts (hK₁ : 0 ≤ K₁) (L : ℝ) :
    4 * K₁ ≤ ks.K K₁ L ∧ 2 ≤ ks.K K₁ L ∧
      2 * exp (ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2) ≤ ks.K K₁ L ∧
      2 * exp (9 * ks.a * L ^ 2) ≤ ks.K K₁ L := by
  have h1 := exp_pos (ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2)
  have h2 := exp_pos (9 * ks.a * L ^ 2)
  unfold Cst.K
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem one_le_N₀ : 1 ≤ P₀.N₀ := le_max_right _ _

/-- **The base case.** -/
theorem base_closes (hK₁ : 0 ≤ K₁) (hD : 1 ≤ X.D) {T : State Ω C} (hb : X.IsBase T) :
    2 * K₁ + exp (ks.a * Real.log ((T.size : ℝ) + 2) ^ 2) ≤
      ks.K K₁ (logD X.D) * T.dres.W ks.A (logD X.D) := by
  set L := logD X.D with hL
  have hL2 : 2 ≤ L := logD_ge _
  have hA := ks.A_nn
  obtain ⟨h1, h2, h3, h4⟩ := K_facts (ks := ks) hK₁ L
  set K := ks.K K₁ L
  have hW : 1 ≤ T.dres.W ks.A L := Res.one_le_W hA (by linarith) T.dres_ok
  have hK0 : 0 ≤ K := by linarith
  have hKW : K ≤ K * T.dres.W ks.A L := by nlinarith
  have hs0 : (0 : ℝ) ≤ T.size := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log ((T.size : ℝ) + 2) := Real.log_nonneg (by linarith)
  by_cases hN : T.size ≤ P₀.N₀
  · have h5 : Real.log ((T.size : ℝ) + 2) ≤ Real.log ((P₀.N₀ : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by
        have : (T.size : ℝ) ≤ P₀.N₀ := by exact_mod_cast hN
        linarith)
    have h6 := exp_le_exp.2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 h5 2) ks.a_nn)
    linarith
  rcases hb with hb | hb
  · have hρ : T.size ≤ rhoNat T.hier := by
      rcases le_max_iff.1 (show T.size ≤ max P₀.N₀ (rhoNat T.hier) from hb) with h | h
      · exact absurd h hN
      · exact h
    have hN1 : 1 ≤ T.size := by have := one_le_N₀; omega
    have := Res.baseRho_closes (r := T.dres) (K := K) (L := L) ks.a_nn ks.cond.base hL2
      (by linarith) T.dres_ok hN1 (by
        have : (T.size : ℝ) ≤ (rhoNat T.hier : ℝ) := by exact_mod_cast hρ
        exact this)
    have e : T.dres.s = T.size := rfl
    rw [e] at this
    linarith
  · have h5 := log_le_of_sq_le hb hD
    have h6 : Real.log ((X.D : ℝ) + 2) ≤ L := by rw [hL]; unfold logD; linarith
    have h7 : Real.log ((T.size : ℝ) + 2) ≤ 3 * L := by linarith
    have h8 : Real.log ((T.size : ℝ) + 2) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hlog0 h7 2
    have h9 : ks.a * Real.log ((T.size : ℝ) + 2) ^ 2 ≤ 9 * ks.a * L ^ 2 := by
      have := mul_le_mul_of_nonneg_left h8 ks.a_nn
      nlinarith
    have h10 := exp_le_exp.2 h9
    linarith

/-- **The orbit chain closes.** -/
theorem orbit_shape_closes {K L : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) {T : State Ω C} {cs : List Child}
    (h : Ctx.OrbitShape T cs) :
    K + (cs.map (ks.bound K L)).sum ≤ K * T.dres.W ks.A L := by
  obtain ⟨hn, hsum, hc⟩ := h
  have hA := ks.A_nn
  have hW : 1 ≤ T.dres.W ks.A L := Res.one_le_W hA hL T.dres_ok
  match cs, hn, hsum, hc with
  | [], _, _, _ =>
    simp only [List.map_nil, List.sum_nil, add_zero]
    nlinarith
  | [c], _, _, hc =>
    obtain ⟨hg, hle, h1, h2⟩ := hc c (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := Res.orbit_closes₁ (A := ks.A) hA hL hK T.dres_ok hle h2 h1
    simpa [Cst.bound, hg] using this
  | [c₁, c₂], _, hsum, hc =>
    obtain ⟨hg₁, hle₁, h1₁, -⟩ := hc c₁ (by simp)
    obtain ⟨hg₂, hle₂, h1₂, -⟩ := hc c₂ (by simp)
    have hs : c₁.res.s + c₂.res.s ≤ T.size := by simpa using hsum
    have := Res.orbit_closes (A := ks.A) hA hL hK T.dres_ok hle₁ hle₂ h1₁ h1₂ hs
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    simp only [Cst.bound, hg₁, hg₂, Bool.cond_false]
    linarith

/-- **The single-factor case closes.** -/
theorem norm_shape_closes {K L : ℝ} (hL : 2 ≤ L) (hK : 0 ≤ K) {T : State Ω C} {cs : List Child}
    (h : Ctx.NormShape ks T cs) (hψ : 1 ≤ T.dres.psi) :
    K + (cs.map (ks.bound K L)).sum ≤ K * T.dres.W ks.A L := by
  obtain ⟨hn, hc⟩ := h
  have := Res.norm_closes (A := ks.A) (K := K) (c₀ := ks.c₀) (r := T.dres) hK hL ks.cond.four
    ks.cond.norm T.dres_ok hψ (cs.map fun c => (c.res, c.giant)) (by simpa using hn) (by
      intro p hp
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hp
      exact hc c hc')
  rw [List.map_map] at this
  convert this using 3
  refine List.map_congr_left fun c _ => ?_
  by_cases hg : c.giant = true
  · simp [Cst.bound, hg]; ring
  · simp [Cst.bound, hg]

end Closing

/-- The own work of a node: a polynomial in `M` times the cost of the solver on `D²`-sized states.
This is the shape that `K₁` has. -/
noncomputable def ownBound (c b e M L : ℝ) : ℝ := c * M ^ b * exp (e * L ^ 2)

/-- `K₁` at the root. With `log M = O(x)` and `L = O(x)`, the own work of a node is
`exp(O(x L))`. So the oracle's `exp(O(L²))` is within the bound, since `L ≤ CL x`. -/
theorem ownBound_le {c b e M L x Cm CL : ℝ} (hc : 1 ≤ c) (hb : 0 ≤ b) (he : 0 ≤ e) (hM : 1 ≤ M)
    (hx : 1 ≤ x * L) (hmx : Real.log M ≤ Cm * x) (hL : 2 ≤ L) (hLx : L ≤ CL * x) :
    ownBound c b e M L ≤ exp ((Real.log c + b * Cm + e * CL) * x * L) := by
  have h0 : 0 < M := by linarith
  have h1 : M ^ b = exp (b * Real.log M) := by
    rw [Real.rpow_def_of_pos h0]; ring_nf
  have h2 : c = exp (Real.log c) := (Real.exp_log (by linarith)).symm
  have h3 : ownBound c b e M L = exp (Real.log c + b * Real.log M + e * L ^ 2) := by
    unfold ownBound
    rw [h1, exp_add, exp_add, ← h2]
  rw [h3]
  refine exp_le_exp.2 ?_
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have h4 : Real.log c ≤ Real.log c * (x * L) := le_mul_of_one_le_right hlc hx
  have h5 : b * Real.log M ≤ b * (Cm * x * L) := by
    refine mul_le_mul_of_nonneg_left ?_ hb
    have hl0 : 0 ≤ Real.log M := Real.log_nonneg hM
    have : Cm * x ≤ Cm * x * L := le_mul_of_one_le_right (hl0.trans hmx) (by linarith)
    linarith
  have h6 : e * L ^ 2 ≤ e * (CL * x * L) := by
    refine mul_le_mul_of_nonneg_left ?_ he
    nlinarith
  nlinarith

/-- The constant `K` at the root is `exp(O(x L))`. -/
theorem Cst.K_le (ks : Cst) {K₁ x L C₁ CL : ℝ} (hx : 1 ≤ x * L) (hC₁ : 0 ≤ C₁) (hCL : 0 ≤ CL)
    (hK₁ : K₁ ≤ exp (C₁ * x * L)) (hL : 2 ≤ L) (hLx : L ≤ CL * x) :
    ks.K K₁ L ≤ exp ((C₁ + ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2 + 9 * ks.a * CL + 4) * x * L) := by
  set c := ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2 with hc
  have hc0 : 0 ≤ c := mul_nonneg ks.a_nn (sq_nonneg _)
  have ha := ks.a_nn
  set E := (C₁ + c + 9 * ks.a * CL) * x * L with hE
  have hxL : 0 ≤ x * L := by linarith
  have h1 : C₁ * x * L ≤ E := by
    have := mul_nonneg (add_nonneg hc0 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) ha) hCL)) hxL
    rw [hE]; nlinarith
  have h2 : c ≤ E := by
    have h3 : c ≤ c * (x * L) := le_mul_of_one_le_right hc0 hx
    have := mul_nonneg (add_nonneg hC₁ (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) ha) hCL)) hxL
    rw [hE]; nlinarith
  have h3 : 9 * ks.a * L ^ 2 ≤ E := by
    have h4 : L ^ 2 ≤ CL * x * L := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) ha)
    have := mul_nonneg (add_nonneg hC₁ hc0) hxL
    rw [hE]; nlinarith
  have h0 : 0 ≤ E := hc0.trans h2
  have e1 := exp_le_exp.2 h1
  have e2 := exp_le_exp.2 h2
  have e3 := exp_le_exp.2 h3
  have e4 : 1 ≤ exp E := one_le_exp h0
  have h8 : (16 : ℝ) ≤ exp (4 * (x * L)) := by
    have e5 : exp 1 * exp 1 * (exp 1 * exp 1) = exp 4 := by
      rw [← exp_add, ← exp_add]; norm_num
    have e6 := add_one_le_exp (1 : ℝ)
    have e7 : (2 : ℝ) ≤ exp 1 := by linarith
    have e9 : (4 : ℝ) ≤ exp 1 * exp 1 := by nlinarith
    have e8 : (16 : ℝ) ≤ exp 4 := by rw [← e5]; nlinarith
    exact e8.trans (exp_le_exp.2 (by linarith))
  have h9 : ks.K K₁ L ≤ 16 * exp E := by
    unfold Cst.K
    have : K₁ ≤ exp E := hK₁.trans e1
    linarith
  have h10 : (C₁ + c + 9 * ks.a * CL + 4) * x * L = E + 4 * (x * L) := by rw [hE]; ring
  rw [h10, exp_add]
  nlinarith [exp_pos E]

/-- **The cost at the root.** Under the operations, a call with resources as at the root costs
`exp(O(x L))`, where `x = log(n + 2)`. This is the bound of the paper. -/
theorem Cst.bound_le (ks : Cst) (c : Child) {K₁ x L C₁ CL Cp Cq : ℝ} (hx : 1 ≤ x * L)
    (hx0 : 0 ≤ x) (hC₁ : 0 ≤ C₁) (hCL : 0 ≤ CL) (hK₁ : K₁ ≤ exp (C₁ * x * L)) (hL : 2 ≤ L)
    (hLx : L ≤ CL * x) (hs : c.res.sz ≤ exp x) (hp : c.res.psi + c.res.rho ≤ Cp * x)
    (hq : c.res.Q ≤ Cq * x * L) (hK0 : 0 ≤ ks.K K₁ L) :
    ks.bound (ks.K K₁ L) L c ≤ exp ((C₁ + ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2 +
      9 * ks.a * CL + 4 + (3 + ks.A * (Cp + Cq))) * x * L) := by
  have h1 := ks.K_le hx hC₁ hCL hK₁ hL hLx
  have h2 := Res.root_W_le (A := ks.A) (L := L) (r := c.res) ks.A_nn (by linarith) hx0 hs hp hq
  have hW := c.res.W_pos ks.A L
  have h3 : ks.K K₁ L * c.res.W ks.A L ≤ exp ((C₁ + ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2 +
      9 * ks.a * CL + 4 + (3 + ks.A * (Cp + Cq))) * x * L) := by
    have h4 := mul_le_mul h1 h2 hW.le (exp_pos _).le
    rw [← exp_add] at h4
    refine h4.trans (le_of_eq ?_)
    congr 1
    ring
  have hP : 0 ≤ ks.K K₁ L * c.res.W ks.A L := mul_nonneg hK0 hW.le
  unfold Cst.bound
  cases c.giant
  · simpa using h3
  · simp only [cond_true]
    linarith

/-- **The main theorem of the spine.** Under the operations, every call of the recursion returns the
exact answer, at a cost of at most `K W(T)`, or `K W(T) / 4` for `giantD`. The same `K` serves the
whole recursion. It depends on `K₁`, on `D` through `L`, and on the fixed constants. -/
theorem spine (X : Ctx) (ks : Cst) {K₁ : ℝ} (hK₁ : 0 ≤ K₁) (hD : 1 ≤ X.D) (ops : Ops X ks K₁) :
    ∀ c : Child, X.Good c → X.Spec c (ks.bound (ks.K K₁ (logD X.D)) (logD X.D) c) := by
  set L := logD X.D with hL
  set K := ks.K K₁ L with hKdef
  have hL2 : 2 ≤ L := logD_ge _
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hK1', hK2, -, -⟩ := K_facts (ks := ks) hK₁ L
  rw [← hKdef] at hK1' hK2
  have hK1 : 2 * K₁ ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hA := ks.A_nn
  suffices H : ∀ (μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (c : Child),
      measure P₀ c.mode c.T = μ → X.Good c → X.Spec c (ks.bound K L c) from
    fun c hc => H _ c rfl hc
  intro μ
  induction μ using MLt_wf.induction with
  | _ μ ih =>
  intro c hμ hc
  have hbelow : X.Below μ (ks.bound K L) := fun c' hg hlt => ih _ hlt c' rfl hg
  obtain ⟨Ω, C, T, gi⟩ := c
  obtain ⟨hd, hgd⟩ := hc
  have hfin : Finite Ω := hd.finite
  cases gi with
  | true =>
    change measure P₀ .giant T = μ at hμ
    change Good P₀ .giant T at hgd
    have hrun := ops.giant T hd hgd
    intro k e cc hcc v hv
    refine (hrun _ (hμ ▸ hbelow) k e cc hcc v hv).mono ?_
    rintro u cost ⟨ha, cs, ⟨lq, hlq, ch, hv', ov, rfl, hch, hmc, hhv, hmh, hov, hno⟩, hcost⟩
    refine ⟨ha, ?_⟩
    have hsize : 1 ≤ T.size := by
      obtain ⟨-, -, -, h, -⟩ := hgd
      have h0 : (0 : ℝ) < (T.N : ℝ) ^ P₀.γ := by
        have hN : 0 < T.N := lt_of_le_of_lt (Nat.zero_le _) hd.N_gt
        positivity
      have : (0 : ℝ) < T.size := h0.trans h
      exact_mod_cast this
    have hψ : 1 ≤ T.dres.psi := T.one_le_psi hsize
    have hg : ∀ c ∈ ch ++ hv' ++ ov, c.giant = false := by
      intro c hc'
      simp only [List.mem_append] at hc'
      rcases hc' with (h | h) | h
      · exact (hch c h).1
      · exact (hhv c h).1
      · exact (hov c h).1
    rw [sum_bound_eq _ hg, List.map_append, List.map_append, List.map_append, List.map_append,
      List.sum_append, List.sum_append] at hcost
    have key := Res.giant_closes (A := ks.A) (L := L) (K := K) (r := T.dres) (c₀ := ks.c₀)
      (δ := ks.δ) (lq := lq) (Cm := ks.Cm) (am := ks.am) (Co := ks.Co) (ao := ks.ao) hK0 hL2
      ks.cond.four ks.Cm_nn ks.Co_nn ks.cond.mass ks.cond.over hlq T.dres_ok hψ
      (ch.map Child.res) (hv'.map Child.res) (ov.map Child.res)
      (fun c hc' => by
        obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
        exact (hch c' hc'').2)
      (by rw [List.map_map]; exact hmc)
      (fun c hc' => by
        obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
        exact (hhv c' hc'').2)
      (by rw [List.map_map]; exact hmh)
      (fun c hc' => by
        obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
        exact (hov c' hc'').2)
      (by simpa using hno)
    change (cost : ℝ) ≤ K * T.dres.W ks.A L / 4
    have hK₁K : K₁ ≤ K := by linarith
    nlinarith
  | false =>
    change measure P₀ .cont T = μ at hμ
    subst hμ
    have hbd : ks.bound K L ⟨Ω, C, T, false⟩ = K * T.dres.W ks.A L := rfl
    change X.Spec ⟨Ω, C, T, false⟩ _
    rw [hbd]
    by_cases hb : Ctx.IsSmall T
    · intro k e cc hcc v hv
      refine (ops.base T hd hb _ hbelow k e cc hcc v hv).mono ?_
      rintro u cost ⟨ha, cs, rfl, hcost⟩
      refine ⟨ha, ?_⟩
      have := base_closes (X := X) (ks := ks) hK₁ hD (Or.inl hb)
      simp only [List.map_nil, List.sum_nil, add_zero] at hcost
      linarith
    have hN1 : 1 ≤ T.size := by
      by_contra hc
      exact hb (le_max_of_le_left (by have := one_le_N₀; omega))
    by_cases ht : T.Transitive
    · obtain ⟨Ω', C', R, hdR, htR, hrd, hsize, hle, hmeas, hlift⟩ := ops.reset T hd hb ht
      have hfinR : Finite Ω' := hdR.finite
      have hbelowR : X.Below (measure P₀ .cont R) (ks.bound K L) :=
        fun c' hg hlt => ih _ (hmeas _ hlt) c' rfl hg
      have hWle : R.dres.W ks.A L ≤ T.dres.W ks.A L := Res.W_mono hA hL0 hle
      have hR1 : 1 ≤ R.size := hsize ▸ hN1
      have hψ := R.one_le_psi hR1
      have hK₁K : K₁ ≤ K := by linarith
      have hR2 : 2 ≤ R.size := by
        rw [hsize]
        by_contra hc
        exact hb (le_max_of_le_left (by have := one_le_N₀; omega))
      intro k e cc hcc v hv
      refine (hlift (K * R.dres.W ks.A L - K₁) (fun k' e' cc' hcc' v' hv' => ?_) k e cc hcc v
        hv).mono ?_
      · refine (ops.trans R hdR htR hR2 hrd _ hbelowR k' e' cc' hcc' v' hv').mono ?_
        rintro u cost ⟨ha, hout⟩
        refine ⟨ha, ?_⟩
        rcases hout with ⟨b, I, cs, hb2, hbs, hI1, hIb, hs, hcost⟩ |
          ⟨r₁, I, cs, hr1, hrρ, hI1, hIb, hs, hcost⟩ | ⟨hsm, hcost⟩ | ⟨cs, hs, hcost⟩
        · have hg : ∀ c ∈ cs, c.giant = false := fun c hc' => (hs.2 c hc').1
          rw [sum_bound_eq _ hg] at hcost
          have hb2' : (2 : ℝ) ≤ b := by exact_mod_cast hb2
          have hlb : 1 / 2 ≤ Real.log b := by
            have h1 := Real.log_two_gt_d9
            have h2 : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb2'
            linarith
          have hbψ : Real.log b ≤ R.dres.psi := by
            have h1 := R.log_le_psi htR hR1
            have hbs' : (b : ℝ) ≤ R.size := by exact_mod_cast hbs
            have h2 : Real.log b ≤ Real.log ((R.size : ℝ) + 2) :=
              Real.log_le_log (by linarith) (by linarith)
            exact h2.trans h1
          have key := Res.enum_closes (A := ks.A) (K := K) (L := L) (r := R.dres)
            (lb := Real.log b) (I := I) (cE := ks.cE) hK0 hL2 hlb hbψ R.dres_ok ks.cE_nn
            ks.cond.enum hI1 hIb (cs.map Child.res) (by simpa using hs.1)
            (fun c hc' => by
              obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
              exact (hs.2 c' hc'').2)
          have h3 : K₁ + K₁ * (1 + I) ≤ K * (1 + I) := by nlinarith
          linarith
        · have hg : ∀ c ∈ cs, c.giant = false := fun c hc' => (hs.2 c hc').1
          rw [sum_bound_eq _ hg] at hcost
          have hr1' : (1 : ℝ) ≤ r₁ := by exact_mod_cast hr1
          have key := Res.product_closes (A := ks.A) (K := K) (L := L) (r := R.dres)
            (r₁ := (r₁ : ℝ)) (I := I) (cP := ks.cP) hK0 hL2 hr1' hrρ R.dres_ok ks.cP_nn
            ks.cond.prod hI1 hIb (cs.map Child.res) (by simpa using hs.1)
            (fun c hc' => by
              obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
              exact (hs.2 c' hc'').2)
          have h3 : K₁ + K₁ * (1 + I) ≤ K * (1 + I) := by nlinarith
          linarith
        · have key := base_closes (X := X) (ks := ks) hK₁ hD (T := R) (Or.inr hsm)
          linarith
        · have key := norm_shape_closes (ks := ks) hL2 hK0 hs hψ
          have h2 : 2 * K₁ ≤ K := hK1
          linarith
      · rintro u cost ⟨ha, hcost⟩
        refine ⟨ha, hcost.trans ?_⟩
        have := mul_le_mul_of_nonneg_left hWle hK0
        linarith
    · intro k e cc hcc v hv
      refine (ops.orbit T hd hb ht _ hbelow k e cc hcc v hv).mono ?_
      rintro u cost ⟨ha, cs, hs, hcost⟩
      have key := orbit_shape_closes (ks := ks) hL0 hK0 hs
      have h2 : K₁ ≤ K := by linarith
      exact ⟨ha, by linarith⟩

end GI.Degree
