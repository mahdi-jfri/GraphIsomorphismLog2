import Workspace.Impl.Fresh
import Workspace.Impl.DirectCoset

/-!
# The direct step of `Solve`

Algorithm 5, `Solve` with `|dom| ≤ N₀`: "return the answer by direct enumeration". In the
recursion this is `Run.direct`, with the exact answer `S.answer` and no children.

The step function `directBody` on a state value `v`:

1. `s := |dom|` (`size_spec`).
2. If `s = 0`, every element of `G` is an answer: return `[1, gs₀]`, where `gs₀` is a list of at
   most `k²` generators of `G` (`red_spec`, cited **PointwiseStab**).
3. Otherwise `p := prepF v` (`prep_spec`, as in the fresh step). It gives at most `k²`
   generators `gs₀` of `G`, the domain context, and the value of the fresh state on `Fin s`:
   at most `s²` generators `hs` of `G|_dom` and the codes `fx`, `fy` of the two colorings.
4. The answer coset on `Fin s`: `{σ ∈ ⟨hs⟩ | fy ∘ σ = fx}` (`cosetFin_spec`, by enumeration of
   `⟨hs⟩` with the bound `N₀!`, cited **Membership** for the coset normal form). It is the image
   of the answer `A'` of the restricted instance (`image_answer_dom`).
5. The lift of the coset to `Ω` (`lift_spec`, cited **Preimage** and **NormalizedFactor**). The
   lift of `A'` is `S.answer` (`liftAnswer_answer_dom`).

Cost: at most `directCost (wt v + 1)`. `N₀!` enters as a constant: the enumeration costs a
polynomial in `N₀! + wt v` (`cosetFinCost`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens PointwiseStab Preimage NormalizedFactor
  Membership)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### The answer on the domain -/

/-- The codes of a coloring on the positions of the domain. -/
noncomputable def domCol (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (x : Ω → C) :
    Fin (domFin e S.dom).length → ℕ :=
  fun i => freshCode e c S ((x ∘ Subtype.val) ((domEquiv e S.dom).symm i))

/-- The answer of the instance restricted to the domain. -/
def domAnswer (S : State Ω C) : Set (Perm S.dom) :=
  GI.Algorithm.answer S.domGroup Set.univ (S.x ∘ Subtype.val) (S.y ∘ Subtype.val)

theorem liftAnswer_answer_dom (S : State Ω C) : S.liftAnswer (domAnswer S) = S.answer := by
  unfold State.liftAnswer State.answer domAnswer
  rw [answer_restrict_image S.G S.dom S.dom_inv S.x S.y]
  rfl

/-- **The image of the restricted answer** is the transporter of the codes. -/
theorem image_answer_dom (e : Ω ≃ Fin k) (c : C → ℕ) (hc : Function.Injective c)
    (S : State Ω C) :
    toFin (domEquiv e S.dom) '' domAnswer S =
      {σ | σ ∈ groupFin (domEquiv e S.dom) S.domGroup ∧
        domCol e c S S.y ∘ σ = domCol e c S S.x} := by
  ext σ
  constructor
  · rintro ⟨g, ⟨hg, hxy⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hg, funext fun i => ?_⟩
    have h := hxy ((domEquiv e S.dom).symm i) trivial
    simp only [domCol, Function.comp_apply, toFin_apply, symm_apply_apply] at h ⊢
    rw [h]
  · rintro ⟨hσ, hcol⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hσ
    refine ⟨g, ⟨hg, fun a _ => ?_⟩, rfl⟩
    have h := congrFun hcol (domEquiv e S.dom a)
    simp only [domCol, Function.comp_apply, MulEquiv.coe_toMonoidHom, toFin_apply,
      symm_apply_apply] at h
    exact freshCode_injective e c S hc h

/-- The codes are below `2s`. -/
theorem domCol_le (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (i : Fin (domFin e S.dom).length) :
    domCol e c S S.x i ≤ 2 * (domFin e S.dom).length ∧
      domCol e c S S.y i ≤ 2 * (domFin e S.dom).length :=
  ⟨(freshCode_lt e c S _ (mem_codeList_of_dom_x e c S _)).le,
    (freshCode_lt e c S _ (mem_codeList_of_dom_y e c S _)).le⟩

/-! ### The program -/

/-- The body of the direct step on a state value `v`. -/
def directBody (sz prep red rg cf lift : ℕ) : Expr :=
  .letE (.call sz (.var 0))
  (.ite (.var 1)
    (.letE (.call prep (.var 0))
    (.letE (.get (.var 2) (.nat 3))
    (.letE (.call cf (mk4 (.get (.var 3) (.nat 0)) (.get (.var 3) (.nat 1))
      (.get (.var 3) (.nat 3)) (.get (.var 3) (.nat 4))))
    (.call lift (mk2 (mk4 (arg 0) (.get (.var 2) (.nat 2)) (.get (.var 2) (.nat 1))
      (.get (.var 2) (.nat 0))) (.var 4))))))
    (mk2 (.call rg (arg 0)) (.call red (mk2 (arg 0) (arg 1)))))

/-- Where the pieces of the direct step sit. The enumeration bound is `N₀!`. -/
structure DirectAt (P : Program) (f sz prep red dom col hier ap rep lo cnt ob jst cf en fl tf cp
    eq nf ap' rg jm lift jpre jfac : ℕ) : Prop where
  entry : P.funs[f]? = some (directBody sz prep red rg cf lift)
  sizeAt : P.HasAt sz (sizeFuns sz)
  prepAt : PrepAt P prep red dom col hier ap rep lo cnt ob jst
  cfAt : CosetFinAt P cf P₀.N₀.factorial en fl tf cp eq nf ap' rg jm
  liftAt : LiftAt P lift dom jpre jfac

/-- The cost of the direct step besides its result, in `X = wt v + 1`. -/
noncomputable def directCost (pst pp pf : Prim) (hm : Membership) (X : ℕ) : ℕ :=
  sizeK * X ^ 2 + prepCost pst X + cosetFinCost hm X P₀.N₀.factorial + liftCost pp pf X +
    10 ^ 8 * X ^ 6

theorem memCost_mono (h : Membership) {n n' : ℕ} (hn : n ≤ n') : memCost h n ≤ memCost h n' := by
  unfold memCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega) 6)) _)

theorem reduceCost_mono_n (h : Membership) {n n' : ℕ} (hn : n ≤ n') (m : ℕ) :
    reduceCost h n m ≤ reduceCost h n' m := by
  unfold reduceCost
  have h1 := Nat.mul_le_mul_left (m + 1) (memCost_mono h hn)
  have h2 : ((m + 2) * (n + 1)) ^ 6 ≤ ((m + 2) * (n' + 1)) ^ 6 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) 6
  have h3 := Nat.mul_le_mul_left reduceK h2
  omega

theorem cosetFinCost_mono (h : Membership) {s s' : ℕ} (hs : s ≤ s') (B : ℕ) :
    cosetFinCost h s B ≤ cosetFinCost h s' B := by
  unfold cosetFinCost
  have h1 : (B + s + 1) ^ 3 ≤ (B + s' + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : (B + s + 1) ^ 12 ≤ (B + s' + 1) ^ 12 := Nat.pow_le_pow_left (by omega) 12
  have h3 := reduceCost_mono h s (Nat.mul_le_mul_left 100 h1)
  have h4 := reduceCost_mono_n h hs (100 * (B + s' + 1) ^ 3)
  have h5 := Nat.mul_le_mul_left (10 ^ 20) h2
  omega

/-! ### Constants -/

/-- The constant of `cosetFinCost` with the bound `B`, for `cosetFinCost_le`. -/
noncomputable def cfConst (hm : Membership) (B : ℕ) : ℕ :=
  (100 * (B + 2) ^ 3 + 1) * ((membershipPrim hm).c * 25600 ^ (membershipPrim hm).k) +
    reduceK * (2 * (100 * (B + 2) ^ 3 + 2)) ^ 6 + 10 ^ 20 * (B + 2) ^ 12

/-- **The coset program costs at most a constant times `X^d`** for `X ≥ s`, when `d` is at least
`24` and `3 + 6` times the exponent of membership. The constant contains `(B + 2)^24`. -/
theorem cosetFinCost_le (hm : Membership) (B : ℕ) {d : ℕ} (hd : 24 ≤ d)
    (hk : 3 + 6 * (membershipPrim hm).k ≤ d) {X : ℕ} (hX : 1 ≤ X) :
    cosetFinCost hm X B ≤ cfConst hm B * X ^ d := by
  set pc := (membershipPrim hm).c
  set pk := (membershipPrim hm).k
  set Q := 100 * (B + 2) ^ 3 with hQ
  have pw : ∀ m, m ≤ d → X ^ m ≤ X ^ d := fun m hm => Nat.pow_le_pow_right hX hm
  have hY : B + X + 1 ≤ (B + 2) * X := by nlinarith
  have h3 : (B + X + 1) ^ 3 ≤ (B + 2) ^ 3 * X ^ 3 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hY 3
  have h12 : (B + X + 1) ^ 12 ≤ (B + 2) ^ 12 * X ^ 12 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hY 12
  have x3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX
  have hm1 : 100 * (B + X + 1) ^ 3 + 1 ≤ (Q + 1) * X ^ 3 := by
    have := Nat.mul_le_mul_left 100 h3
    have e : 100 * ((B + 2) ^ 3 * X ^ 3) = Q * X ^ 3 := by rw [hQ]; ring
    nlinarith
  have hm2 : (100 * (B + X + 1) ^ 3 + 2) * (X + 1) ≤ 2 * (Q + 2) * X ^ 4 := by
    have := Nat.mul_le_mul_left 100 h3
    have e : 100 * ((B + 2) ^ 3 * X ^ 3) = Q * X ^ 3 := by rw [hQ]; ring
    have a1 : 100 * (B + X + 1) ^ 3 + 2 ≤ (Q + 2) * X ^ 3 := by nlinarith
    have a2 : X + 1 ≤ 2 * X := by omega
    calc (100 * (B + X + 1) ^ 3 + 2) * (X + 1) ≤ ((Q + 2) * X ^ 3) * (2 * X) :=
          Nat.mul_le_mul a1 a2
      _ = 2 * (Q + 2) * X ^ 4 := by ring
  have hmem : memCost hm X ≤ pc * 25600 ^ pk * X ^ (6 * pk) := by
    unfold memCost
    have a1 : 400 * (X + 1) ^ 6 ≤ 25600 * X ^ 6 := by
      have : (X + 1) ^ 6 ≤ (2 * X) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have e : (2 * X) ^ 6 = 64 * X ^ 6 := by ring
      omega
    calc pc * (400 * (X + 1) ^ 6) ^ pk ≤ pc * (25600 * X ^ 6) ^ pk :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left a1 _)
      _ = pc * 25600 ^ pk * X ^ (6 * pk) := by rw [mul_pow, ← pow_mul]; ring
  have T1 : (100 * (B + X + 1) ^ 3 + 1) * memCost hm X ≤
      (Q + 1) * (pc * 25600 ^ pk) * X ^ d := by
    calc (100 * (B + X + 1) ^ 3 + 1) * memCost hm X
        ≤ ((Q + 1) * X ^ 3) * (pc * 25600 ^ pk * X ^ (6 * pk)) := Nat.mul_le_mul hm1 hmem
      _ = (Q + 1) * (pc * 25600 ^ pk) * X ^ (3 + 6 * pk) := by ring
      _ ≤ (Q + 1) * (pc * 25600 ^ pk) * X ^ d := Nat.mul_le_mul_left _ (pw _ hk)
  have T2 : reduceK * ((100 * (B + X + 1) ^ 3 + 2) * (X + 1)) ^ 6 ≤
      reduceK * (2 * (Q + 2)) ^ 6 * X ^ d := by
    calc reduceK * ((100 * (B + X + 1) ^ 3 + 2) * (X + 1)) ^ 6
        ≤ reduceK * (2 * (Q + 2) * X ^ 4) ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm2 6)
      _ = reduceK * (2 * (Q + 2)) ^ 6 * X ^ 24 := by ring
      _ ≤ reduceK * (2 * (Q + 2)) ^ 6 * X ^ d := Nat.mul_le_mul_left _ (pw _ hd)
  have T3 : 10 ^ 20 * (B + X + 1) ^ 12 ≤ 10 ^ 20 * (B + 2) ^ 12 * X ^ d := by
    calc 10 ^ 20 * (B + X + 1) ^ 12 ≤ 10 ^ 20 * ((B + 2) ^ 12 * X ^ 12) :=
          Nat.mul_le_mul_left _ h12
      _ = 10 ^ 20 * (B + 2) ^ 12 * X ^ 12 := by ring
      _ ≤ 10 ^ 20 * (B + 2) ^ 12 * X ^ d := Nat.mul_le_mul_left _ (pw _ (by omega))
  unfold cosetFinCost reduceCost cfConst
  rw [← hQ]
  have e : ((Q + 1) * (pc * 25600 ^ pk) + reduceK * (2 * (Q + 2)) ^ 6 +
      10 ^ 20 * (B + 2) ^ 12) * X ^ d = (Q + 1) * (pc * 25600 ^ pk) * X ^ d +
      reduceK * (2 * (Q + 2)) ^ 6 * X ^ d + 10 ^ 20 * (B + 2) ^ 12 * X ^ d := by ring
  rw [e]
  omega

/-- A constant for `Ks` that covers the direct step (`directK_of`). It contains `(N₀! + 2)^24`. -/
noncomputable def directConst (pst pp pf : Prim) (hm : Membership) : ℕ :=
  freshConst pst pp pf + sizeK + 10 ^ 8 + cfConst hm P₀.N₀.factorial

/-- **Sufficient constants for the direct step.** -/
theorem directCost_le (pst pp pf : Prim) (hm : Membership) {d : ℕ} (hd : 24 ≤ d)
    (h1 : 6 * pst.k ≤ d) (h2 : 6 * pp.k ≤ d) (h3 : 6 * pf.k ≤ d)
    (h4 : 3 + 6 * (membershipPrim hm).k ≤ d) {X : ℕ} (hX : 1 ≤ X) :
    directCost pst pp pf hm X ≤ directConst pst pp pf hm * X ^ d := by
  have pw : ∀ m, m ≤ d → X ^ m ≤ X ^ d := fun m hm => Nat.pow_le_pow_right hX hm
  have q1 := freshCost_le pst pp pf (by omega) h1 h2 h3 hX
  have q2 := cosetFinCost_le hm P₀.N₀.factorial hd h4 hX
  have q3 := Nat.mul_le_mul_left sizeK (pw 2 (by omega))
  have q4 := Nat.mul_le_mul_left (10 ^ 8) (pw 6 (by omega))
  unfold directCost directConst
  unfold freshCost at q1
  have e : (freshConst pst pp pf + sizeK + 10 ^ 8 + cfConst hm P₀.N₀.factorial) * X ^ d =
      freshConst pst pp pf * X ^ d + sizeK * X ^ d + 10 ^ 8 * X ^ d +
        cfConst hm P₀.N₀.factorial * X ^ d := by ring
  rw [e]
  omega

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The constants of `Solve` cover the direct step. -/
def DirectK (pst pp pf : Prim) (hm : Membership) : Prop :=
  ∀ X : ℕ, 1 ≤ X → directCost pst pp pf hm X ≤ I.Ks * X ^ I.ds

/-- **The direct step meets its specification.** -/
theorem directSpec (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hm : Membership)
    {f sz prep red dom col hier ap rep lo cnt ob jst cf en fl tf cp eq nf ap' rg jm lift jpre
      jfac : ℕ}
    (h : DirectAt Pg f sz prep red dom col hier ap rep lo cnt ob jst cf en fl tf cp eq nf ap' rg jm
      lift jpre jfac)
    (hjs : Pg.prims[jst]? = some (pointwiseStabPrim hst))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    (hjp : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjf : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hK : I.DirectK (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) hm) :
    I.DirectSpec Pg F f := by
  intro Ω C S k e c hc v hv hg hP ih
  have hsv : StateVal e c v S := hv
  have hP' : S.size ≤ P₀.N₀ := hP
  have hkv := StateVal.k_le_wt hsv
  obtain ⟨gv, dv, xv, yv, hv0, rv, hgv, -, -, -, -, -, hveq⟩ := id hsv
  set vs := [Val.nat k, gv, dv, xv, yv, hv0, rv, boolVal S.floor, .nat S.h, .nat S.N] with hvs
  subst hveq
  haveI : Finite S.dom := Finite.of_equiv _ (domEquiv e S.dom).symm
  have hown : I.own .solve (Run.direct S hP') (Val.list vs) =
      (I.Ks : ℝ) * (((Val.list vs).wt : ℝ) + 1) ^ I.ds := by simp [own]
  have hch : I.childCost (Run.direct S hP') = 0 := by simp [childCost, Run.children]
  set X := (Val.list vs).wt + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hkX : k + 1 ≤ X := by omega
  have fin : ∀ T : ℕ, T ≤ directCost (pointwiseStabPrim hst) (preimagePrim hpre)
      (normalizedFactorPrim hfac) hm X →
      (T : ℝ) ≤ (I.Ks : ℝ) * (((Val.list vs).wt : ℝ) + 1) ^ I.ds + 0 := by
    intro T hT
    have h1 := hT.trans (hK X hX1)
    have e2 : ((X : ℕ) : ℝ) = ((Val.list vs).wt : ℝ) + 1 := by rw [hX]; push_cast; ring
    rw [← e2, add_zero]
    exact_mod_cast h1
  have p12 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p36 : X ^ 3 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p69 : X ^ 6 ≤ X ^ 9 := Nat.pow_le_pow_right hX1 (by omega)
  have p921 : X ^ 9 ≤ X ^ 21 := Nat.pow_le_pow_right hX1 (by omega)
  have k2 : (k + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hkX 2
  have k6 : (k + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hkX 6
  have k9 : (k + 1) ^ 9 ≤ X ^ 9 := Nat.pow_le_pow_left hkX 9
  have hgvw : gv.wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have hS : S.size ≤ k := by
    unfold State.size; rw [card_dom_eq e S.dom]; exact length_domFin_le
  have wS := wt_nat_le S.size
  have wk := wt_nat_le k
  refine FunAll.intro h.entry ?_
  -- 1. the size of the domain
  have dS := Det.call (Det.var' (P := Pg) (env := [Val.list vs]) (i := 0) rfl)
    (size_spec h.sizeAt hsv)
  refine EvalAll.letE dS ?_
  rintro _ c0 ⟨rfl, hc0⟩
  refine EvalAll.ite (Det.var' (P := Pg) (env := [Val.list vs, .nat S.size]) (i := 1) rfl)
    (fun _ _ hh => ⟨_, hh.1⟩) fun x cc hx => ?_
  obtain ⟨hx1, hx2⟩ := hx
  simp only [Val.nat.injEq] at hx1
  subst hx1
  by_cases hs0 : S.size = 0
  · -- 2. an empty domain: the answer is `G`
    rw [if_pos hs0]
    have dR : FunDet Pg rg (.nat k) (encPerm (1 : Perm (Fin k)))
        (loopModK * (k + 1) * ((Val.nat k).wt + k + (encPerm (1 : Perm (Fin k))).wt + 1)) :=
      (range_spec h.cfAt.rgAt k).mono fun w c hw => by
        obtain ⟨rfl, hc⟩ := hw
        rw [range_eq_encPerm_one] at hc ⊢
        exact ⟨rfl, hc⟩
    have dRg := Det.call (Det.arg' (P := Pg) (vs := vs) (rest := [.nat S.size]) (j := 0) rfl) dR
    have dA := Det.mk2 (Det.arg' (P := Pg) (vs := vs) (rest := [.nat S.size]) (j := 0) rfl)
      (Det.arg' (P := Pg) (vs := vs) (rest := [.nat S.size]) (j := 1) rfl)
    refine (EvalAll.mk2_last dRg (EvalAll.call_spec dA (red_spec hst h.prepAt.redAt hjs hgv))).mono
      ?_
    rintro w c4 ⟨_, cb, ⟨cb', ⟨gs₀, rfl, hgs₀, hl₀, hcb'⟩, hcb⟩, rfl, hc4⟩
    have hempty : S.dom = ∅ := by
      have h0 : Nat.card S.dom = 0 := hs0
      rw [Nat.card_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact Set.isEmpty_coe_sort.mp h0
      · exact absurd h0 (not_infinite_iff_finite.mpr inferInstance)
    have hans : S.answer = S.G := by
      ext g
      simp [State.answer, GI.Algorithm.answer, hempty]
    refine ⟨S.answer, none, Run.direct S hP', rfl, by simp [Run.kind],
      Or.inr ⟨1, gs₀, rfl, hl₀, ?_⟩, ?_⟩
    · rw [one_smul, hgs₀, hans, groupFin, Subgroup.coe_map]
      rfl
    · rw [hown, hch]
      refine fin _ ?_
      have w1 := wt_encPerm_le (1 : Perm (Fin k))
      have w2 := wt_encGroup_le_sq hl₀
      have w3 := wt_list2_le (encPerm (1 : Perm (Fin k))) (encGroup gs₀)
      have w4 := wt_list2_le (.nat k) gv
      have w5 := wt_list2_le gv (.list [])
      have w6 : (Val.list []).wt = 4 := wt_list_nil
      have B1 : (pointwiseStabPrim hst).bound (.list [gv, .list []]) ≤
          (pointwiseStabPrim hst).c * (10 ^ 6 * X ^ 6 + 2) ^ (pointwiseStabPrim hst).k :=
        Prim.bound_le _ (by omega)
      have Pr : loopModK * (k + 1) * ((Val.nat k).wt + k + (encPerm (1 : Perm (Fin k))).wt + 1) ≤
          loopModK * X * (8 * X ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hkX) (by omega)
      have ePr : loopModK * X * (8 * X ^ 2) = 8000 * X ^ 3 := by simp only [loopModK]; ring
      have q9 := Nat.mul_le_mul_left (10 ^ 7) k9
      have q21 := Nat.mul_le_mul_left (10 ^ 22) p921
      have sK : sizeK * ((Val.list vs).wt + 1) ^ 2 = sizeK * X ^ 2 := by rw [hX]
      unfold directCost prepCost
      simp only [hs0] at hc0 hx2 wS
      clear dS dR dRg dA hown hch fin
      omega
  · -- 3. the value of the fresh state
    rw [if_neg hs0]
    have hsz : 0 < S.size := Nat.pos_of_ne_zero hs0
    refine EvalAll.letE (EvalAll.call_spec (Det.var' (P := Pg)
      (env := [Val.list vs, .nat S.size]) (i := 0) rfl) (prep_spec hst h.prepAt hjs e c S hsz hsv))
      ?_
    rintro w1 c1 ⟨cb1, ⟨⟨gs₀, hsF, labF, a, hgs₀, hl₀, hmax, hcan, rfl, hw1⟩, hcb1⟩, hc1⟩
    set hv' := fhierVal (encFun labF) (Nat.card (orb S.domGroup a)) with hhv'
    have hxv : natList (cmpCodes e c S S.x) = encFun (domCol e c S S.x) :=
      colorVal_fresh e c S fun p hp => mem_codeList_x e c S p hp
    have hyv : natList (cmpCodes e c S S.y) = encFun (domCol e c S S.y) :=
      colorVal_fresh e c S fun p hp => mem_codeList_y e c S p hp
    -- the generators of `G|_dom`
    obtain ⟨hgF, hlF⟩ : gens hsF = groupFin (domEquiv e S.dom) S.domGroup ∧ hsF.length ≤ (domFin e S.dom).length ^ 2 := by
      obtain ⟨gv', _, _, _, _, _, ⟨gs', hgs', hgens', hlen'⟩, _, _, _, _, _, hval⟩ := hcan.val
      simp only [freshVal, Val.list.injEq, List.cons.injEq] at hval
      obtain ⟨-, hgg, -⟩ := hval
      subst hgg
      obtain rfl := encGroup_injective hgs'
      exact ⟨hgens', hlen'⟩
    set fv := Val.list [.nat (domFin e S.dom).length, encGroup hsF,
      .list (List.replicate (domFin e S.dom).length (.nat 1)),
      encFun (domCol e c S S.x), encFun (domCol e c S S.y), hv', .list [], .nat 0, .nat 2,
      .nat (domFin e S.dom).length] with hfv
    have efv : freshVal (domFin e S.dom).length (encGroup hsF) (natList (cmpCodes e c S S.x))
        (natList (cmpCodes e c S S.y)) hv' = fv := by rw [hxv, hyv]; rfl
    rw [efv]
    rw [efv] at hc1 hw1
    set pv := [encGroup gs₀, domCtx e S.dom, .nat (domFin e S.dom).length, fv] with hpv
    have dF := Det.get' (Det.var' (P := Pg) (env := [Val.list vs, .nat S.size, .list pv]) (i := 2)
      rfl) (Det.nat 3) (show pv[3]? = some fv from rfl)
    refine EvalAll.letE dF ?_
    rintro _ c2 ⟨rfl, hc2⟩
    -- 4. the answer coset on `Fin s`
    set env3 := [Val.list vs, .nat S.size, .list pv, fv] with henv3
    have dA := Det.mk4
      (Det.get' (Det.var' (P := Pg) (env := env3) (i := 3) rfl) (Det.nat 0) rfl)
      (Det.get' (Det.var' (P := Pg) (env := env3) (i := 3) rfl) (Det.nat 1) rfl)
      (Det.get' (Det.var' (P := Pg) (env := env3) (i := 3) rfl) (Det.nat 3) rfl)
      (Det.get' (Det.var' (P := Pg) (env := env3) (i := 3) rfl) (Det.nat 4) rfl)
    have hsN : (domFin e S.dom).length ≤ P₀.N₀ := by rw [← card_dom_eq]; exact hP'
    have hB : (domFin e S.dom).length.factorial ≤ P₀.N₀.factorial := Nat.factorial_le hsN
    refine EvalAll.letE (EvalAll.call_spec dA (cosetFin_spec hm h.cfAt hjm hB hsF hlF
      (domCol e c S S.x) (domCol e c S S.y) (fun i => (domCol_le e c S i).1)
      (fun i => (domCol_le e c S i).2))) ?_
    rintro u c3 ⟨cb3, ⟨hu, hcb3⟩, hc3⟩
    have hA : AnsC (domEquiv e S.dom) u (domAnswer S) := by
      have himg := image_answer_dom e c hc S
      rw [← hgF] at himg
      rcases hu with ⟨rfl, hC⟩ | ⟨x', hs', rfl, hl', hC⟩
      · exact Or.inl ⟨rfl, Set.image_eq_empty.mp (himg.trans hC)⟩
      · exact Or.inr ⟨x', hs', rfl, hl', himg.trans hC⟩
    -- 5. the lift
    have hlift := lift_spec hpre hfac h.liftAt h.prepAt.domAt hjp hjf e S hgs₀ hl₀ hA
      (fun g hg => hg.1)
    set env4 := env3 ++ [u] with henv4
    have dL := Det.mk2 (Det.mk4 (Det.arg' (P := Pg) (vs := vs) (rest := env4.tail) (j := 0) rfl)
      (Det.get' (Det.var' (P := Pg) (env := env4) (i := 2) rfl) (Det.nat 2)
        (show pv[2]? = some (.nat (domFin e S.dom).length) from rfl))
      (Det.get' (Det.var' (P := Pg) (env := env4) (i := 2) rfl) (Det.nat 1)
        (show pv[1]? = some (domCtx e S.dom) from rfl))
      (Det.get' (Det.var' (P := Pg) (env := env4) (i := 2) rfl) (Det.nat 0)
        (show pv[0]? = some (encGroup gs₀) from rfl)))
      (Det.var' (P := Pg) (env := env4) (i := 4) rfl)
    refine (EvalAll.call_spec dL hlift).mono ?_
    rintro w c4 ⟨cb4, ⟨hAns, hcb4⟩, hc4⟩
    rw [liftAnswer_answer_dom] at hAns
    refine ⟨S.answer, none, Run.direct S hP', rfl, by simp [Run.kind], hAns, ?_⟩
    rw [hown, hch]
    refine fin _ ?_
    rw [← hfv] at hc3
    have hs_k : (domFin e S.dom).length ≤ k := length_domFin_le
    have wpv : (Val.list pv).wt ≤ 10 ^ 5 * X ^ 6 := hw1.trans (Nat.mul_le_mul_left _ k6)
    have wfv : fv.wt < (Val.list pv).wt := wt_le_wt_list (by simp [hpv])
    have wdc : (domCtx e S.dom).wt < (Val.list pv).wt := wt_le_wt_list (by simp [hpv])
    have wg0 : (encGroup gs₀).wt < (Val.list pv).wt := wt_le_wt_list (by simp [hpv])
    have wns : (Val.nat (domFin e S.dom).length).wt < fv.wt := wt_le_wt_list (by simp)
    have wgF : (encGroup hsF).wt < fv.wt := wt_le_wt_list (by simp)
    have wfx : (encFun (domCol e c S S.x)).wt < fv.wt := wt_le_wt_list (by simp)
    have wfy : (encFun (domCol e c S S.y)).wt < fv.wt := wt_le_wt_list (by simp)
    have wA4 := wt_list4_le (Val.nat (domFin e S.dom).length) (encGroup hsF)
      (encFun (domCol e c S S.x)) (encFun (domCol e c S S.y))
    have C3 : cb3 ≤ cosetFinCost hm X P₀.N₀.factorial :=
      hcb3.trans (cosetFinCost_mono hm (by omega) _)
    have wu : u.wt ≤ 1000 * X ^ 6 := by
      have h1 := hA.wt_le
      have h2 := ansW_le (domFin e S.dom).length
      have h3 : ((domFin e S.dom).length + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left (by omega) 6
      omega
    have ww : w.wt ≤ 1000 * X ^ 6 := by
      have h1 := hAns.wt_le
      have h2 := ansW_le k
      omega
    have C4 : cb4 ≤ liftCost (preimagePrim hpre) (normalizedFactorPrim hfac) X :=
      hcb4.trans (liftCost_mono _ _ (by omega))
    have wctx := wt_liftCtx_le e S.dom hl₀
    have ectx : (Val.list [Val.nat k, Val.nat (domFin e S.dom).length, domCtx e S.dom,
      encGroup gs₀]).wt = (liftCtx e S.dom gs₀).wt := rfl
    have ectx2 : (Val.list [Val.list [Val.nat k, Val.nat (domFin e S.dom).length, domCtx e S.dom,
      encGroup gs₀], u]).wt = (Val.list [liftCtx e S.dom gs₀, u]).wt := rfl
    have wl2 := wt_list2_le (liftCtx e S.dom gs₀) u
    have epv : (Val.list [encGroup gs₀, domCtx e S.dom, Val.nat (domFin e S.dom).length, fv]).wt =
      (Val.list pv).wt := rfl
    have sK : sizeK * ((Val.list vs).wt + 1) ^ 2 = sizeK * X ^ 2 := by rw [hX]
    have pK : prepCost (pointwiseStabPrim hst) ((Val.list vs).wt + 1) =
      prepCost (pointwiseStabPrim hst) X := by rw [hX]
    unfold directCost
    clear dS dA dL hown hch fin hlift hcan
    omega

/-- `DirectK` from explicit constants (`directCost_le`). -/
theorem directK_of {pst pp pf : Prim} {hm : Membership} (hK : directConst pst pp pf hm ≤ I.Ks)
    (hd : 24 ≤ I.ds) (h1 : 6 * pst.k ≤ I.ds) (h2 : 6 * pp.k ≤ I.ds) (h3 : 6 * pf.k ≤ I.ds)
    (h4 : 3 + 6 * (membershipPrim hm).k ≤ I.ds) : I.DirectK pst pp pf hm := fun _ hX =>
  (directCost_le pst pp pf hm hd h1 h2 h3 h4 hX).trans (Nat.mul_le_mul_right _ hK)

end Iface

/-- **The direct step with the concrete interface** `Rest.iface`: its constants cover the direct
step when `solveK ≥ directConst` and `solveD` is at least `24`, six times the exponents of the
three cited tasks of the fresh step and `3 +` six times the exponent of membership. -/
theorem Rest.directK (R : Rest) {pst pp pf : Prim} {hm : Membership}
    (hK : directConst pst pp pf hm ≤ R.solveK) (hd : 24 ≤ R.solveD) (h1 : 6 * pst.k ≤ R.solveD)
    (h2 : 6 * pp.k ≤ R.solveD) (h3 : 6 * pf.k ≤ R.solveD)
    (h4 : 3 + 6 * (membershipPrim hm).k ≤ R.solveD) : R.iface.DirectK pst pp pf hm :=
  R.iface.directK_of (hK.trans (Nat.le_add_left _ _)) (hd.trans (le_max_right _ _))
    (h1.trans (le_max_right _ _)) (h2.trans (le_max_right _ _)) (h3.trans (le_max_right _ _))
    (h4.trans (le_max_right _ _))

/-- **The constants of `Solve`.** `solveK` and `solveD` of `Rest` can be these numbers: they
cover both the fresh step (`Rest.freshK`) and the direct step (`Rest.directK`). -/
noncomputable def Rest.solveKOf (pst pp pf : Prim) (hm : Membership) : ℕ :=
  freshConst pst pp pf + directConst pst pp pf hm

/-- The exponent of `Solve` (see `Rest.solveKOf`). -/
noncomputable def Rest.solveDOf (pst pp pf : Prim) (hm : Membership) : ℕ :=
  24 + 6 * (pst.k + pp.k + pf.k) + 6 * (membershipPrim hm).k

/-- **Both steps of `Solve` are covered** when `solveK, solveD` are `solveKOf, solveDOf`. -/
theorem Rest.solve_consts (R : Rest) {pst pp pf : Prim} {hm : Membership}
    (hK : R.solveK = Rest.solveKOf pst pp pf hm) (hD : R.solveD = Rest.solveDOf pst pp pf hm) :
    R.iface.FreshK pst pp pf ∧ R.iface.DirectK pst pp pf hm := by
  unfold Rest.solveKOf at hK
  unfold Rest.solveDOf at hD
  exact ⟨R.freshK (by omega) (by omega) (by omega) (by omega) (by omega),
    R.directK (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

end GI.Impl
