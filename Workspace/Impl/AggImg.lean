import Workspace.Impl.AggCosets

/-!
# The order of `φ_T` on a pointwise stabilizer

Rules 1 to 4 of Algorithm 2 test the image under `φ_T` of subgroups of `A` of one form: the
pointwise stabilizer `A_{(U)}` of a set `U` of points of the domain.

* rule 1, `Full A`: `U = ∅`, the image is `Alt(T)`;
* rule 2, `Affected A v`: `U = {v}`, the image is not `Alt(T)`;
* rule 3, `Full (A_{(Ω \ W)})`: `U` the points outside the window;
* rule 4, `VisibleOrbit A v`: `U = v^A`, the image is trivial.

`imgCardFuns` computes the order of that image: the stabilizer of the positions of `U` in graph
form (**PointwiseStab**, `graphStabP_spec`), then the length of the orbit of the label points of
`T` under it (`graphTup_spec`). By `ncard_tupOrbit` the length is `|φ_T(A_{(U)})|`
(`imgCard_spec`). Each test compares it with `|Alt(T)|` or with `1` (`full_iff_card`,
`bot_iff_card`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.LocalGroups GI.Endpoint
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab PointwiseStab)

variable {k q : ℕ}

/-! ### The program -/

/-- On `[[k, q], pairs, X, x₀, B]`: the stabilizer of the points `X`, then the number of points
of the orbit of `x₀`. The environment after the `let` is `[input, stabilizer pairs]`. -/
def imgCardEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk3 (arg 0) (arg 1) (arg 2)))
    (.length (.call (b + 34) (mk4 (arg 0) (.var 1) (arg 3) (arg 4))))

/-- The module at base `b` (71 functions), with the cited primitive at `jp`. -/
def imgCardFuns (b jp : ℕ) : List Expr :=
  [imgCardEntry b] ++ graphStabFuns (b + 1) jp ++ graphTupFuns (b + 34)

/-- The cost constant of the module. -/
def imgCardK : ℕ := 10 ^ 16

/-- The size parameter of the module. -/
def imgM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) (X : List (Fin (k + q))) (B l : ℕ) :
    ℕ := k + q + ps.length + X.length + B + l + 20

theorem length_of_orbit {n : ℕ} {L : List (List (Fin n) × Perm (Fin n))}
    {O : Set (List (Fin n))} (hnd : (L.map Prod.fst).Nodup)
    (hmem : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ O) : L.length = O.ncard := by
  rw [← List.length_map (f := Prod.fst), ← List.toFinset_card_of_nodup hnd,
    ← Set.ncard_coe_finset]
  congr 1
  ext y
  simp [hmem]

theorem length_encPairs {n : ℕ} {X : Type} (key : X → List ℕ) (L : List (X × Perm (Fin n))) :
    ∃ vs : List Val, encPairs key L = .list vs ∧ vs.length = L.length :=
  ⟨L.map (GI.Lang.encPair key), rfl, List.length_map _⟩

/-- **The number of points of the orbit of `x₀` under the stabilizer of `X`.** -/
theorem imgCard_spec (h : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (imgCardFuns b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim h))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (X : List (Fin (k + q))) (x₀ : List (Fin (k + q)))
    {B : ℕ} (hB : ∀ qs : List (Perm (Fin k) × Perm (Fin q)),
      Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixPts k q X →
      (actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (qs.map encPair) x₀).ncard ≤ B) :
    FunAll P b (.list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X, natList (ptsKey x₀),
      .nat B])
      (fun w c => ∃ qs : List (Perm (Fin k) × Perm (Fin q)),
        Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixPts k q X ∧
        w = .nat (actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (qs.map encPair)
          x₀).ncard ∧
        c ≤ (pointwiseStabPrim h).bound (.list [encGroup (ps.map encPair), encPts X]) +
          imgCardK * imgM k q ps X B x₀.length ^ 24) := by
  have hentry : P.funs[b]? = some (imgCardEntry b) := by
    simpa using (hb.block 0 (gs := [imgCardEntry b]) (by rfl)).single
  have hst : P.HasAt (b + 1) (graphStabFuns (b + 1) jp) := hb.block 1 (by rfl)
  have hgt : P.HasAt (b + 34) (graphTupFuns (b + 34)) := hb.block 34 (by rfl)
  set A : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
    natList (ptsKey x₀), .nat B] with hA
  have dI := Det.mk3 (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      encPts X, natList (ptsKey x₀), .nat B]) (rest := []) (j := 0) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
      natList (ptsKey x₀), .nat B]) (rest := []) (j := 1) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
      natList (ptsKey x₀), .nat B]) (rest := []) (j := 2) rfl)
  have hpre : (Val.list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X]).wt ≤ A.wt :=
    wt_list_mono ⟨[natList (ptsKey x₀), .nat B], rfl⟩
  refine FunAll.intro hentry (EvalAll.letE (Ra := fun Q cq =>
      (∃ qs : List (Perm (Fin k) × Perm (Fin q)), Q = .list (qs.map pairV) ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixPts k q X) ∧
      cq ≤ (pointwiseStabPrim h).bound (.list [encGroup (ps.map encPair), encPts X]) +
        graphStabK * stabPM k q ps X ^ 8 + 20 * A.wt + Q.wt + 30)
    (EvalAll.call_funAll dI fun v ca hv => ?_) fun Q cq hQ => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine (graphStabP_spec h hst hj ps X).mono fun w cb hw => ?_
    obtain ⟨qs, rfl, hl, hc, hcb⟩ := hw
    have eA : (Val.list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
      natList (ptsKey x₀), .nat B]).wt = A.wt := rfl
    exact ⟨⟨qs, rfl, hl, hc⟩, by omega⟩
  obtain ⟨⟨qs, rfl, hlq, hcl⟩, hcI⟩ := hQ
  have dJ := Det.mk4 (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      encPts X, natList (ptsKey x₀), .nat B]) (rest := [.list (qs.map pairV)]) (j := 0) rfl)
    (Det.var' (P := P) (env := [A, .list (qs.map pairV)]) (i := 1) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
      natList (ptsKey x₀), .nat B]) (rest := [.list (qs.map pairV)]) (j := 3) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
      natList (ptsKey x₀), .nat B]) (rest := [.list (qs.map pairV)]) (j := 4) rfl)
  set J : Val := .list [.list [.nat k, .nat q], .list (qs.map pairV), natList (ptsKey x₀), .nat B]
    with hJ
  refine EvalAll.length (Ra := fun va ca =>
      (∃ L : List (List (Fin (k + q)) × Perm (Fin (k + q))), va = encPairs ptsKey L ∧
        (L.map Prod.fst).Nodup ∧
        (∀ y, y ∈ L.map Prod.fst ↔
          y ∈ actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (qs.map encPair) x₀)) ∧
      va.wt ≤ graphTupK * tupM k q qs B x₀.length ^ 12 ∧
      ca ≤ 2 * (graphTupK * tupM k q qs B x₀.length ^ 12) + 20 * A.wt + 10 * J.wt + 50)
    (EvalAll.call_funAll dJ fun v ca hv => ?_) ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (graphTup_spec hgt qs x₀ (hB qs hcl)).wt_lt.mono fun w cb hw => ?_
    obtain ⟨⟨L, rfl, hnd, hmem, -, hcT⟩, hwT⟩ := hw
    have eA : (Val.list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
      natList (ptsKey x₀), .nat B]).wt = A.wt := rfl
    have hq : (Val.list (qs.map pairV)).wt < J.wt := wt_le_wt_list (by simp)
    exact ⟨⟨L, rfl, hnd, hmem⟩, by omega, by omega⟩
  rintro va ca ⟨⟨L, rfl, hnd, hmem⟩, hva, hca⟩
  obtain ⟨vs, hvs, hlen⟩ := length_encPairs ptsKey L
  refine ⟨vs, hvs, qs, hcl, ?_, ?_⟩
  · rw [hlen, length_of_orbit hnd hmem]
  -- the cost
  set M := imgM k q ps X B x₀.length with hM
  have hMd : k + q + ps.length + X.length + B + x₀.length + 20 = M := rfl
  have hM1 : 1 ≤ M := by omega
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b hab => Nat.pow_le_pow_right hM1 hab
  have pl : ∀ x n, x ≤ M → x ^ n ≤ M ^ n := fun x n hx => Nat.pow_le_pow_left hx n
  have hq2 : qs.length ≤ M ^ 2 := hlq.trans (pl _ 2 (by omega))
  have cS : graphStabK * stabPM k q ps X ^ 8 ≤ graphStabK * M ^ 8 :=
    Nat.mul_le_mul_left _ (pl _ 8 (by unfold stabPM; omega))
  have cT : graphTupK * tupM k q qs B x₀.length ^ 12 ≤ graphTupK * (2 * M ^ 2) ^ 12 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      unfold tupM; have := Nat.le_self_pow (n := 2) (by norm_num) M; omega) 12)
  have e2 : (2 * M ^ 2) ^ 12 = 4096 * M ^ 24 := by ring
  have bps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
    have := wt_pairList_le ps
    have h3 := pl (pM k q ps) 3 (by unfold pM; omega)
    omega
  have bqs : (Val.list (qs.map pairV)).wt ≤ 50 * (2 * M ^ 2) ^ 3 := by
    have := wt_pairList_le qs
    have h3 := Nat.pow_le_pow_left (show pM k q qs ≤ 2 * M ^ 2 by
      unfold pM; have := Nat.le_self_pow (n := 2) (by norm_num) M; omega) 3
    omega
  have e3 : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
  have bX : (encPts X).wt ≤ 3 * M ^ 2 + 4 := by
    have h1 := wt_list_map_le X (fun i : Fin (k + q) => Val.nat i.val) (W := k + q + 2)
      fun i _ => by
      show (Val.nat (i : ℕ)).wt ≤ k + q + 2; have := wt_nat_le (i : ℕ); have := i.isLt; omega
    have h2 : X.length * (2 * (k + q + 2) + 1) ≤ M * (3 * M) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : M * (3 * M) = 3 * M ^ 2 := by ring
    rw [encPts_eq]
    omega
  have bx0 : (natList (ptsKey x₀)).wt ≤ 3 * M ^ 2 + 4 := by
    have := wt_ptsKey_le x₀
    have : x₀.length * (2 * (k + q) + 5) ≤ M * (3 * M) := Nat.mul_le_mul (by omega) (by omega)
    have e : M * (3 * M) = 3 * M ^ 2 := by ring
    omega
  have bkq := wt_list2_le (.nat k) (.nat q)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wB := wt_nat_le B
  have bA := wt_list_le [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
    natList (ptsKey x₀), .nat B]
  have bI := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (encPts X)
  have bJ := wt_list4_le (.list [.nat k, .nat q]) (.list (qs.map pairV)) (natList (ptsKey x₀))
    (.nat B)
  simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at bA
  have hl : (Val.nat vs.length).wt ≤ vs.length + 2 := wt_nat_le _
  have hlv : vs.length ≤ graphTupK * tupM k q qs B x₀.length ^ 12 := by
    have := length_lt_wt_list vs
    rw [← hvs] at this
    omega
  have m6 : M ^ 6 ≤ M ^ 24 := pw 6 24 (by omega)
  have m3 : M ^ 3 ≤ M ^ 24 := pw 3 24 (by omega)
  have m2 : M ^ 2 ≤ M ^ 24 := pw 2 24 (by omega)
  have m8 : M ^ 8 ≤ M ^ 24 := pw 8 24 (by omega)
  have eA : A.wt = (Val.list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X,
    natList (ptsKey x₀), .nat B]).wt := rfl
  have eJ : J.wt = (Val.list [.list [.nat k, .nat q], .list (qs.map pairV),
    natList (ptsKey x₀), .nat B]).wt := rfl
  have hkM : k + q + B + ps.length + X.length + x₀.length + 20 ≤ M ^ 2 := by
    have := Nat.le_self_pow (n := 2) (by norm_num) M
    omega
  clear dI dJ
  simp only [imgCardK, graphTupK, graphStabK] at *
  omega

/-- The cost of the stabilizer primitive inside `imgCard_spec`, bounded by the size
parameter. -/
theorem stabBound_le (h : PointwiseStab) (ps : List (Perm (Fin k) × Perm (Fin q)))
    (X : List (Fin (k + q))) (B l : ℕ) :
    (pointwiseStabPrim h).bound (.list [encGroup (ps.map encPair), encPts X]) ≤
      (pointwiseStabPrim h).boundSize (200 * imgM k q ps X B l ^ 4) := by
  apply Prim.bound_le
  set M := imgM k q ps X B l with hM
  have hMd : k + q + ps.length + X.length + B + l + 20 = M := rfl
  have h1 := wt_encGroup_le (ps.map encPair)
  rw [List.length_map] at h1
  have h2 : ((ps.length + 2) * (k + q + 1)) ^ 2 ≤ (M * M) ^ 2 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 2
  have e2 : (M * M) ^ 2 = M ^ 4 := by ring
  have bX : (encPts X).wt ≤ 3 * M ^ 2 + 4 := by
    have h1 := wt_list_map_le X (fun i : Fin (k + q) => Val.nat i.val) (W := k + q + 2)
      fun i _ => by
      show (Val.nat (i : ℕ)).wt ≤ k + q + 2; have := wt_nat_le (i : ℕ); have := i.isLt; omega
    have h2 : X.length * (2 * (k + q + 2) + 1) ≤ M * (3 * M) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : M * (3 * M) = 3 * M ^ 2 := by ring
    rw [encPts_eq]
    omega
  have m24 : M ^ 2 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hw := wt_list2_le (encGroup (ps.map encPair)) (encPts X)
  have hs := (Val.list [encGroup (ps.map encPair), encPts X]).size_le_wt
  have : 4 ≤ M ^ 4 := by
    have := Nat.one_le_pow 4 M (by omega)
    have : M ≤ M ^ 4 := Nat.le_self_pow (by norm_num) M
    omega
  omega

/-! ### The tests as orders of images -/

section Tests

variable {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- The positions in `Fin (k + q)` of points of the domain. -/
def posPts (e : Ω ≃ Fin k) (q : ℕ) (us : List S.dom) : List (Fin (k + q)) :=
  us.map fun u : S.dom => Fin.castAdd q (e (u : Ω))

theorem encPair_castAdd (p : Perm (Fin k) × Perm (Fin q)) (i : Fin k) :
    encPair p (Fin.castAdd q i) = Fin.castAdd q (p.1 i) :=
  Fin.ext (by rw [encPair_eq, sumToFin_sumCongr_castAdd]; rfl)

/-- **The graph of the lift of a pointwise stabilizer**: the pairs of the graph of the lift of
`A` whose first part fixes the positions of `U`. -/
theorem graphOf_lift_fix (A : Subgroup (Perm S.dom)) {U : Set S.dom} {X : List (Fin (k + L.q))}
    (hX : ∀ j, j ∈ X ↔ ∃ u ∈ U, Fin.castAdd L.q (e (u : Ω)) = j) :
    graphOf e L (S.liftGroup (fix A U)) =
      graphOf e L (S.liftGroup A) ⊓ fixPts k L.q X := by
  ext p
  rw [Subgroup.mem_inf, mem_graphOf, mem_graphOf]
  have key : ∀ g (hg : g ∈ S.G), toFin e g = p.1 →
      ((∀ u ∈ U, S.domHom ⟨g, hg⟩ u = u) ↔ p ∈ fixPts k L.q X) := by
    intro g hg h1
    show _ ↔ ∀ i ∈ X, encPair p i = i
    have hpt : ∀ u : S.dom, S.domHom ⟨g, hg⟩ u = u ↔
        encPair p (Fin.castAdd L.q (e u)) = Fin.castAdd L.q (e u) := by
      intro u
      rw [encPair_castAdd, ← h1, toFin_apply, Equiv.symm_apply_apply]
      constructor
      · intro h
        have h' : g u = u := by simpa using congrArg Subtype.val h
        rw [h']
      · intro h
        apply Subtype.ext
        rw [State.domHom_apply]
        exact e.injective (Fin.castAdd_injective _ _ h)
    constructor
    · intro h i hi
      obtain ⟨u, hu, rfl⟩ := (hX i).1 hi
      exact (hpt u).1 (h u hu)
    · intro h u hu
      exact (hpt u).2 (h _ ((hX _).2 ⟨u, hu, rfl⟩))
  constructor
  · rintro ⟨g, hg, hF, h1, h2⟩
    obtain ⟨hg', hF'⟩ := State.mem_liftGroup.1 hF
    obtain ⟨hA, hfix⟩ := mem_fix.1 hF'
    exact ⟨⟨g, hg, State.mem_liftGroup.2 ⟨hg, hA⟩, h1, h2⟩, (key g hg h1).1 hfix⟩
  · rintro ⟨⟨g, hg, hA', h1, h2⟩, hP⟩
    obtain ⟨hg', hA⟩ := State.mem_liftGroup.1 hA'
    exact ⟨g, hg, State.mem_liftGroup.2 ⟨hg, mem_fix.2 ⟨hA, (key g hg h1).2 hP⟩⟩, h1, h2⟩

theorem mem_posPts {U : Set S.dom} {us : List S.dom} (hU : ∀ u, u ∈ U ↔ u ∈ us)
    (j : Fin (k + L.q)) :
    j ∈ posPts (S := S) e L.q us ↔ ∃ u ∈ U, Fin.castAdd L.q (e (u : Ω)) = j := by
  simp only [posPts, List.mem_map, hU]

variable (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **The output of `imgCardFuns` is the order of `φ_T(A_{(U)})`**: here `ps` is a graph-form
generating list of the lift of `A`, the points are the positions of `U`, and the start tuple is
the label points of `T`. -/
theorem ncard_eq_card_img_fix (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps)
    {U : Set S.dom} {X : List (Fin (k + L.q))}
    (hX : ∀ j, j ∈ X ↔ ∃ u ∈ U, Fin.castAdd L.q (e (u : Ω)) = j)
    {qs : List (Perm (Fin k) × Perm (Fin L.q))}
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ fixPts k L.q X) :
    (actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (qs.map encPair)
      (labPts k (tlist T))).ncard = Nat.card (img (phiT S.domGroup πd T) (fix A U)) := by
  have hq : PairGens e L (S.liftGroup (fix A U)) qs := by
    unfold PairGens at *
    rw [hqs, hps, graphOf_lift_fix A hX]
  exact ncard_tupOrbit πd hπ ((inf_le_left : fix A U ≤ A).trans hA) hq

/-- The image of a subgroup under `φ_T` has at most `|Alt(T)|` elements. -/
theorem card_img_le {T : Finset (Fin L.q)} (A : Subgroup (Perm S.dom)) :
    Nat.card (img (phiT S.domGroup πd T) A) ≤ Nat.card (alternatingGroup T) :=
  Subgroup.card_le_card_group _

/-- `Full` is the test `|φ_T(A)| = |Alt(T)|`. -/
theorem full_iff_card {T : Finset (Fin L.q)} (A : Subgroup (Perm S.dom)) :
    Full (phiT S.domGroup πd T) A ↔
      Nat.card (img (phiT S.domGroup πd T) A) = Nat.card (alternatingGroup T) :=
  (Subgroup.card_eq_iff_eq_top _).symm

/-- `VisibleOrbit` and the other tests of triviality are the test `|φ_T(·)| = 1`. -/
theorem bot_iff_card {T : Finset (Fin L.q)} (A : Subgroup (Perm S.dom)) :
    img (phiT S.domGroup πd T) A = ⊥ ↔ Nat.card (img (phiT S.domGroup πd T) A) = 1 :=
  Subgroup.card_eq_one.symm

end Tests

end GI.Impl
