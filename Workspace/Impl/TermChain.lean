module

public import Workspace.Impl.TermChainStep
public import Workspace.Impl.GMPRepsCost

@[expose] public section

/-!
# Top-down nonabelian-chief chain from `H` to `N` in `GI.Lang`

This file assembles the full top-down nonabelian-chief chain algorithm of Section 2.2
in `GI.Lang`:

1. **`tcChainStep`**: Given `[[encGroup hs₀, encGroup ns₀], .nat i, [encGroup us_i, tcCsVal L_i]]`,
   calls `tcStepBody` on `[encGroup hs₀, encGroup ns₀, encGroup us_i]` to obtain `v₁ = encGroup vs`
   (`vs.length ≤ n ^ 2`), calls `normalizedIntersectionPrim` on `[v₁, v₁]` to obtain a clean
   generator list `v₂ = .list (vs'.map encPerm)` (`vs'.length ≤ n ^ 2`, `gens vs' = gens vs`),
   and returns `[v₁, tcCsVal (L_i ++ [vs'])]`.
2. **`tcChainEntry`**: Given `[encGroup hs, encGroup ns]` where `N = gens ns ⊴ H = gens hs`
   and `N` is transitive on `Fin n` (when `1 ≤ n`), reduces `hs` and `ns` to `≤ n ^ 2` generators
   (`reduceFuns`), obtains an initial clean generator list `v₃` for `H` (`normalizedIntersectionPrim`),
   iterates `tcChainStep` for `n ^ 2` steps (`iterFuns`), and returns `cs = tcCsVal L`.
3. **`tcChain_spec`**: Proves that `cs` satisfies `SeriesVal n cs Hs` and
   `IsNonabelianChiefChain (gens hs) (gens ns) Hs` for `Hs = L.map gens`, within cost
   `tcChainCost hmb hpre hmem hnc hni hder (Val.list [encGroup hs, encGroup ns]).wt n`.
4. **`tcChainPrim` and `tcChainCost_le_boundSize`**: Bounds `tcChainCost` polynomially in
   `W + tcRadQ n` (using `PBU`) and packages this bound as a synthetic `Prim` for seamless
   use in `TermRad.lean`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Cited Equiv Equiv.Perm
open GI.Machine (BinOp)
open scoped commutatorElement

set_option maxRecDepth 100000

variable {n : ℕ}

/-! ### 1. Chain Invariant and List Helpers -/

/-- A series of generator lists encoded as a `Val` (`radCsVal` in `TermRadLoop.lean`). -/
def tcCsVal (L : List (List (Perm (Fin n)))) : Val :=
  .list (L.map fun hs => .list (hs.map encPerm))

/-- The index bound `⌈n ^ log₂ n⌉₊` (`radQ` in `TermRadMath.lean`). -/
noncomputable def tcRadQ (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ Real.logb 2 n⌉₊

/-- Partial nonabelian-chief chain invariant for `Hs : List (Subgroup (Perm (Fin n)))`
from `H` down to `U`. -/
def TcPartialChain (H N U : Subgroup (Perm (Fin n)))
    (Hs : List (Subgroup (Perm (Fin n)))) : Prop :=
  Hs ≠ [] ∧ Hs.head? = some H ∧ Hs.getLast? = some U ∧
  (∀ W ∈ Hs, W ≤ H ∧ ∀ g ∈ H, ∀ x ∈ W, g * x * g⁻¹ ∈ W) ∧
  ∀ j (hj : j + 1 < Hs.length),
    Hs[j + 1] ≤ Hs[j] ∧
    (¬ ⁅Hs[j], Hs[j]⁆ ≤ N ⊔ Hs[j + 1] →
      ∀ M : Subgroup (Perm (Fin n)), N ⊔ Hs[j + 1] ≤ M → M ≤ N ⊔ Hs[j] →
        (∀ g ∈ H, ∀ x ∈ M, g * x * g⁻¹ ∈ M) → M = N ⊔ Hs[j + 1] ∨ M = N ⊔ Hs[j])

theorem tcPartialChain_singleton {H N U : Subgroup (Perm (Fin n))} (hUH : U = H) :
    TcPartialChain H N U [U] := by
  refine ⟨by simp, by simp [hUH], by simp, ?_, ?_⟩
  · intro W hW
    simp only [List.mem_singleton] at hW
    subst hW; subst hUH
    exact ⟨le_rfl, fun g hg x hx => mul_mem (mul_mem hg hx) (inv_mem hg)⟩
  · intro j hj
    simp at hj

theorem tcPartialChain_snoc {H N U V : Subgroup (Perm (Fin n))}
    {Hs : List (Subgroup (Perm (Fin n)))}
    (hch : TcPartialChain H N U Hs) (hUH : U ≤ H) (hrel : TcStepRel H N U V) :
    TcPartialChain H N V (Hs ++ [V]) := by
  obtain ⟨hne, hhead, hlast, hall, hstep⟩ := hch
  obtain ⟨hNV, hVU, hnV, -, hchief⟩ := hrel
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · rwa [List.head?_append_of_ne_nil _ hne]
  · simp
  · intro W hW
    rcases List.mem_append.mp hW with hW | hW
    · exact hall W hW
    · simp only [List.mem_singleton] at hW
      subst hW
      exact ⟨hVU.trans hUH, hnV⟩
  · intro j hj
    rw [List.length_append, List.length_singleton] at hj
    have hpos : 0 < Hs.length := List.length_pos_of_ne_nil hne
    by_cases hj' : j + 1 < Hs.length
    · have hj0 : j < Hs.length := by omega
      rw [List.getElem_append_left hj0, List.getElem_append_left hj']
      exact hstep j hj'
    · have hjeq : j = Hs.length - 1 := by omega
      have hj0 : j < Hs.length := by omega
      have hj1 : j + 1 = Hs.length := by omega
      have h_at_j : (Hs ++ [V])[j] = U := by
        rw [List.getElem_append_left hj0]
        rw [List.getLast?_eq_getElem?] at hlast
        have hsome : Hs[j]? = some U := by simpa [hjeq] using hlast
        rw [List.getElem?_eq_getElem hj0] at hsome
        exact Option.some.inj hsome
      have h_at_j1 : (Hs ++ [V])[j + 1] = V := by
        rw [List.getElem_append_right (by omega)]
        simp [hj1]
      rw [h_at_j, h_at_j1]
      exact ⟨hVU, hchief⟩

theorem tcPartialChain_to_nonabelianChief {H N U : Subgroup (Perm (Fin n))}
    {Hs : List (Subgroup (Perm (Fin n)))}
    (hch : TcPartialChain H N U Hs) (hUN : U ≤ N) :
    IsNonabelianChiefChain H N Hs :=
  ⟨hch.2.1, ⟨U, hch.2.2.1, hUN⟩, hch.2.2.2.1, hch.2.2.2.2⟩

theorem tcCsVal_snoc (L : List (List (Perm (Fin n)))) (vs : List (Perm (Fin n))) :
    tcCsVal (L ++ [vs]) =
      Val.list ((L.map fun hs => .list (hs.map encPerm)) ++ [.list (vs.map encPerm)]) := by
  simp [tcCsVal]

/-! ### 2. Program Definitions (`tcChainStep`, `tcChainEntry`, `TcChainAt`, `tcChainFuns`) -/

/-- **One step of the chain loop** on
`[.list [encGroup hs₀, encGroup ns₀], .nat i, .list [encGroup us, cs]]`:
1. Calls `tcs` (`tcStepBody`) on `[encGroup hs₀, encGroup ns₀, encGroup us]` to get `v₁ = encGroup vs`.
2. Calls `normalizedIntersectionPrim` (`jni`) on `[v₁, v₁]` to get `v₂ = .list (vs'.map encPerm)`
   with `vs'.length ≤ n ^ 2` and `gens vs' = gens vs`.
3. Returns `[v₁, cs.snoc v₂]`. -/
def tcChainStep (tcs jni : ℕ) : Expr :=
  .letE (.call tcs (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 2) (.nat 0))))
  (.letE (.prim jni (mk2 (.var 1) (.var 1)))
    (mk2 (.var 1) (.snoc (.get (arg 2) (.nat 1)) (.var 2))))

/-- **Entry of the top-down nonabelian-chief chain** on `[encGroup hs, encGroup ns]`:
1. Reduces `arg 0` (`encGroup hs`) to `v₁ = encGroup hs₀` (`hs₀.length ≤ n ^ 2`).
2. Reduces `arg 1` (`encGroup ns`) to `v₂ = encGroup ns₀` (`ns₀.length ≤ n ^ 2`).
3. Calls `normalizedIntersectionPrim` (`jni`) on `[v₁, v₁]` to get `v₃ = .list (hs₀'.map encPerm)`
   (`hs₀'.length ≤ n ^ 2`, `gens hs₀' = gens hs`).
4. Runs `iterFuns` (`it_ch`) for `n * n` steps starting from `[v₁, [v₃]]`.
5. Returns the second component `cs = (.var 4)[1]`. -/
def tcChainEntry (red jni it_ch : ℕ) : Expr :=
  .letE (.call red (arg 0))
  (.letE (.call red (arg 1))
  (.letE (.prim jni (mk2 (.var 1) (.var 1)))
  (.letE (.call it_ch (mk3 (mk2 (.var 1) (.var 2))
      (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0)))
      (mk2 (.var 1) (mk1 (.var 3)))))
    (.get (.var 4) (.nat 1)))))

/-- Where `tcChainEntry` and all its subroutines sit in the program. -/
structure TcChainAt (P : Program)
    (f it_ch ch_step tcs ap mg le red
     ob it_ob g_ob obk rep lo dom cls ker
     grd gr fl_g gs_g
     cnj itc cjp flc cjs iv mc cj cp
     jmb jpre jmem jnc jni jder : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) : Prop where
  entry : P.funs[f]? = some (tcChainEntry red jni it_ch)
  iter : P.HasAt it_ch (iterFuns it_ch ch_step)
  step : P.funs[ch_step]? = some (tcChainStep tcs jni)
  tcs : TcStepAt P tcs ap mg le red ob it_ob g_ob obk rep lo dom cls ker
    grd gr fl_g gs_g cnj itc cjp flc cjs iv mc cj cp
    jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder

/-- Header list of 12 single functions for `tcChainEntry` at base `b`. -/
def tcSingles (b jmb jnc jni jder : ℕ) : List Expr :=
  [tcChainEntry (b + 30) jni (b + 12),
   tcChainStep (b + 2) jni,
   tcStepBody (b + 15) (b + 18) (b + 25) (b + 30) (b + 3) (b + 6) (b + 8) jder,
   obEntry (b + 35) (b + 15) (b + 30),
   obStepBody (b + 15) (b + 25) (b + 5),
   obKernelBody (b + 38) (b + 172) (b + 96) (b + 18) (b + 121) (b + 145) jmb,
   tcGreedyEntry (b + 69) (b + 41),
   tcGreedyStep (b + 18) (b + 25) jnc,
   tcConjEntry (b + 44),
   tcConjPass (b + 47),
   tcConjStep (b + 50) (b + 62) (b + 18) (b + 25) jni,
   supConjF (b + 65)]

theorem length_gmpRepsFuns (b jm : ℕ) : (gmpRepsFuns b jm).length = 27 := rfl

theorem length_kerNFFuns (b jpre jmem : ℕ) : (kerNFFuns b jpre jmem).length = 27 := rfl

/-- Self-contained function bundle for `tcChainEntry` at base `b` (234 functions),
right-associated for O(1) `HasAt` splitting. -/
def tcChainFuns (b jmb jpre jmem jnc jni jder : ℕ) : List Expr :=
  tcSingles b jmb jnc jni jder ++
  (iterFuns (b + 12) (b + 1) ++
  (appendFuns (b + 15) ++
  (mkGroupFuns (b + 18) ++
  (leFuns (b + 25) jmem ++
  (reduceFuns (b + 30) jmem ++
  (iterFuns (b + 35) (b + 4) ++
  (replicateFuns (b + 38) ++
  (foldlFuns (b + 41) (b + 7) ++
  (iterFuns (b + 44) (b + 9) ++
  (foldlFuns (b + 47) (b + 10) ++
  (invFuns (b + 50) ++
  (mapFuns (b + 62) (b + 11) ++
  (composeFuns (b + 65) ++
  (gmpRepsFuns (b + 69) jmem ++
  (domFuns (b + 96) ++
  (clsFuns (b + 121) ++
  (kerNFFuns (b + 145) jpre jmem ++
  loFuns (b + 172))))))))))))))))))

theorem length_tcChainFuns (b jmb jpre jmem jnc jni jder : ℕ) :
    (tcChainFuns b jmb jpre jmem jnc jni jder).length = 234 := by
  simp [tcChainFuns, tcSingles, iterFuns, appendFuns, mkGroupFuns, leFuns, reduceFuns,
    replicateFuns, foldlFuns, invFuns, mapFuns, composeFuns, loopFuns, rangeFuns, allFuns,
    findFuns, length_gmpRepsFuns, length_domFuns, length_clsFuns, length_kerNFFuns,
    length_loFuns]

private theorem hasAt_step {P : Program} {b m d k : ℕ} {A B : List Expr}
    (h : P.HasAt (b + m) (A ++ B)) (hl : A.length = d) (hk : m + d = k) :
    P.HasAt (b + m) A ∧ P.HasAt (b + k) B :=
  ⟨h.left, by have := h.right; rwa [hl, Nat.add_assoc, hk] at this⟩

private theorem hasAt_cons {P : Program} {b m k : ℕ} {e : Expr} {es : List Expr}
    (h : P.HasAt (b + m) (e :: es)) (hk : m + 1 = k) :
    P.funs[b + m]? = some e ∧ P.HasAt (b + k) es :=
  ⟨(h.left (A := [e]) (B := es)).single,
   by have := h.right (A := [e]) (B := es); rwa [List.length_singleton, Nat.add_assoc, hk] at this⟩

/-- Layout constructor `TcChainAt` from `P.HasAt b (tcChainFuns ...)`. -/
theorem tcChainAt_of {P : Program} {b jmb jpre jmem jnc jni jder : ℕ}
    {hmb : MinimalBlocks} {hpre : Preimage} {hmem : Membership}
    {hnc : NormalClosure} {hni : NormalizedIntersection} {hder : DerivedSubgroup}
    (h : P.HasAt b (tcChainFuns b jmb jpre jmem jnc jni jder))
    (pmb : P.prims[jmb]? = some (minimalBlocksPrim hmb))
    (ppre : P.prims[jpre]? = some (preimagePrim hpre))
    (pmem : P.prims[jmem]? = some (membershipPrim hmem))
    (pnc : P.prims[jnc]? = some (normalClosurePrim hnc))
    (pni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (pder : P.prims[jder]? = some (derivedSubgroupPrim hder)) :
    TcChainAt P b (b + 12) (b + 1) (b + 2) (b + 15) (b + 18) (b + 25) (b + 30)
      (b + 3) (b + 35) (b + 4) (b + 5) (b + 38) (b + 172) (b + 96) (b + 121) (b + 145)
      (b + 6) (b + 69) (b + 41) (b + 7)
      (b + 8) (b + 44) (b + 9) (b + 47) (b + 10) (b + 50) (b + 62) (b + 11) (b + 65)
      jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder := by
  have h0 : P.HasAt (b + 0) (tcChainFuns b jmb jpre jmem jnc jni jder) := by simpa using h
  unfold tcChainFuns at h0
  obtain ⟨hs, h0⟩ := hasAt_step h0 (d := 12) (k := 12) rfl rfl
  obtain ⟨hit12, h0⟩ := hasAt_step h0 (d := 3) (k := 15) rfl rfl
  obtain ⟨hap, h0⟩ := hasAt_step h0 (d := 3) (k := 18) rfl rfl
  obtain ⟨hmg, h0⟩ := hasAt_step h0 (d := 7) (k := 25) rfl rfl
  obtain ⟨hle, h0⟩ := hasAt_step h0 (d := 5) (k := 30) rfl rfl
  obtain ⟨hred, h0⟩ := hasAt_step h0 (d := 5) (k := 35) rfl rfl
  obtain ⟨hit35, h0⟩ := hasAt_step h0 (d := 3) (k := 38) rfl rfl
  obtain ⟨hrep, h0⟩ := hasAt_step h0 (d := 3) (k := 41) rfl rfl
  obtain ⟨hfl41, h0⟩ := hasAt_step h0 (d := 3) (k := 44) rfl rfl
  obtain ⟨hit44, h0⟩ := hasAt_step h0 (d := 3) (k := 47) rfl rfl
  obtain ⟨hfl47, h0⟩ := hasAt_step h0 (d := 3) (k := 50) rfl rfl
  obtain ⟨hiv, h0⟩ := hasAt_step h0 (d := 12) (k := 62) rfl rfl
  obtain ⟨hmc, h0⟩ := hasAt_step h0 (d := 3) (k := 65) rfl rfl
  obtain ⟨hcp, h0⟩ := hasAt_step h0 (d := 4) (k := 69) rfl rfl
  obtain ⟨hreps, h0⟩ := hasAt_step h0 (length_gmpRepsFuns _ _) rfl
  obtain ⟨hdom, h0⟩ := hasAt_step h0 (length_domFuns _) rfl
  obtain ⟨hcls, h0⟩ := hasAt_step h0 (length_clsFuns _) rfl
  obtain ⟨hker, hlo⟩ := hasAt_step h0 (length_kerNFFuns _ _ _) rfl
  unfold tcSingles at hs
  obtain ⟨he0, hs⟩ := hasAt_cons hs (k := 1) rfl
  obtain ⟨he1, hs⟩ := hasAt_cons hs (k := 2) rfl
  obtain ⟨he2, hs⟩ := hasAt_cons hs (k := 3) rfl
  obtain ⟨he3, hs⟩ := hasAt_cons hs (k := 4) rfl
  obtain ⟨he4, hs⟩ := hasAt_cons hs (k := 5) rfl
  obtain ⟨he5, hs⟩ := hasAt_cons hs (k := 6) rfl
  obtain ⟨he6, hs⟩ := hasAt_cons hs (k := 7) rfl
  obtain ⟨he7, hs⟩ := hasAt_cons hs (k := 8) rfl
  obtain ⟨he8, hs⟩ := hasAt_cons hs (k := 9) rfl
  obtain ⟨he9, hs⟩ := hasAt_cons hs (k := 10) rfl
  obtain ⟨he10, hs⟩ := hasAt_cons hs (k := 11) rfl
  obtain ⟨he11, _⟩ := hasAt_cons hs (k := 12) rfl
  exact
  { entry := by simpa using he0
    iter := hit12
    step := he1
    tcs :=
      { entry := he2
        hap := hap
        hmg := hmg
        hle := hle
        hred := hred
        hob :=
          { entry := he3
            iter := hit35
            step := he4
            ap := hap
            le := hle
            red := hred
            obk :=
              { entry := he5
                rep := hrep
                lo := hlo
                dom := domAt_of_hasAt hdom
                mg := hmg
                cls := hcls
                ker := hker
                jmb_eq := pmb
                jpre_eq := ppre
                jmem_eq := pmem } }
        hgrd :=
          { entry := he6
            reps := gmpRepsAt_of hreps pmem
            fold := hfl41
            step := he7
            mg := hmg
            le := hle
            jnc_eq := pnc
            jmem_eq := pmem }
        hcnj :=
          { entry := he8
            iter := hit44
            pass := he9
            fold := hfl47
            step := he10
            iv := hiv
            mc := hmc
            cj := he11
            cp := hcp
            mg := hmg
            le := hle
            jni_eq := pni
            jmem_eq := pmem }
        jder_eq := pder } }

/-! ### 3. Specifications of `tcChainStep` and `tcChainEntry` -/

/-- Loop invariant after `i` steps (`i ≤ n ^ 2`) of `tcChainStep`. -/
def TcChainLoopInv (H N : Subgroup (Perm (Fin n))) (i : ℕ) (acc : Val) : Prop :=
  ∃ (us : List (Perm (Fin n))) (L : List (List (Perm (Fin n)))),
    acc = .list [encGroup us, tcCsVal L] ∧
    us.length ≤ n ^ 2 ∧
    L.length = i + 1 ∧
    (∀ gs ∈ L, gs.length ≤ n ^ 2) ∧
    N ≤ gens us ∧ gens us ≤ H ∧
    (∀ g ∈ H, ∀ x ∈ gens us, g * x * g⁻¹ ∈ gens us) ∧
    (gens us ≤ N ∨ 2 ^ i * Nat.card (gens us) ≤ Nat.card H) ∧
    TcPartialChain H N (gens us) (L.map gens)

theorem TcChainLoopInv.wt_le {H N : Subgroup (Perm (Fin n))} {i : ℕ} {acc : Val}
    (hi : i ≤ n ^ 2) (h : TcChainLoopInv H N i acc) : acc.wt ≤ 1000 * (n + 1) ^ 8 := by
  obtain ⟨us, L, rfl, hl_us, hL_len, hl_L, -⟩ := h
  have wus := wt_encGroup_le_sq hl_us
  have hser : SeriesVal n (tcCsVal L) (L.map gens) :=
    ⟨L, rfl, by omega, hl_L, rfl⟩
  have wcs := SeriesVal.wt_le hser
  have w2 := wt_list2_le (encGroup us) (tcCsVal L)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  omega

/-- Cost bound of a single `tcChainStep` call. -/
noncomputable def tcChainStepCost (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) (n : ℕ) : ℕ :=
  tcStepCost hmb hpre hmem hnc hni hder n +
    (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 9 * (n + 1) ^ 8

/-- **Specification of `tcChainStep`.** -/
theorem tcChainStep_spec (hMa : MarotiPrimitive)
    {hmb : MinimalBlocks} {hpre : Preimage} {hmem : Membership}
    {hnc : NormalClosure} {hni : NormalizedIntersection} {hder : DerivedSubgroup}
    {P : Program}
    {ch_step tcs ap mg le red
     ob it_ob g_ob obk rep lo dom cls ker
     grd gr fl_g gs_g
     cnj itc cjp flc cjs iv mc cj cp
     jmb jpre jmem jnc jni jder : ℕ}
    (hstep : P.funs[ch_step]? = some (tcChainStep tcs jni))
    (htcs : TcStepAt P tcs ap mg le red ob it_ob g_ob obk rep lo dom cls ker
      grd gr fl_g gs_g cnj itc cjp flc cjs iv mc cj cp
      jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder)
    {hs₀ ns₀ : List (Perm (Fin n))}
    (hnN : ∀ g ∈ gens hs₀, ∀ x ∈ gens ns₀, g * x * g⁻¹ ∈ gens ns₀)
    (htrN : 1 ≤ n → MulAction.IsPretransitive (gens ns₀) (Fin n))
    (hl_hs₀ : hs₀.length ≤ n ^ 2) (hl_ns₀ : ns₀.length ≤ n ^ 2)
    (i : ℕ) (hi : i < n ^ 2) {acc : Val}
    (hinv : TcChainLoopInv (gens hs₀) (gens ns₀) i acc) :
    FunAll P ch_step (.list [.list [encGroup hs₀, encGroup ns₀], .nat i, acc])
      (fun w c => TcChainLoopInv (gens hs₀) (gens ns₀) (i + 1) w ∧
        c ≤ tcChainStepCost hmb hpre hmem hnc hni hder n) := by
  obtain ⟨us, L, rfl, hl_us, hL_len, hl_L, hNU, hUH, hnU, hbr, hch⟩ := hinv
  set ctx := Val.list [encGroup hs₀, encGroup ns₀]
  set acc0 := Val.list [encGroup us, tcCsVal L]
  set inp := Val.list [ctx, .nat i, acc0]
  have whs₀ := wt_encGroup_le_sq hl_hs₀
  have wns₀ := wt_encGroup_le_sq hl_ns₀
  have wus := wt_encGroup_le_sq hl_us
  have wcs : (tcCsVal L).wt ≤ 100 * (n + 1) ^ 8 :=
    SeriesVal.wt_le ⟨L, rfl, by omega, hl_L, rfl⟩
  have wctx := wt_list2_le (encGroup hs₀) (encGroup ns₀)
  have wacc0 := wt_list2_le (encGroup us) (tcCsVal L)
  have wi := wt_nat_le i
  have winp := wt_list3_le ctx (.nat i) acc0
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hi2 : i ≤ (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  -- step 1: `v1 = encGroup vs` via `tcs`
  have dctx0 := Det.arg' (P := P) (vs := [ctx, .nat i, acc0]) (rest := []) (j := 0) rfl
  have dhs0 := Det.get' dctx0 (Det.nat 0) (v := encGroup hs₀) rfl
  have dns0 := Det.get' dctx0 (Det.nat 1) (v := encGroup ns₀) rfl
  have dacc0 := Det.arg' (P := P) (vs := [ctx, .nat i, acc0]) (rest := []) (j := 2) rfl
  have dus0 := Det.get' dacc0 (Det.nat 0) (v := encGroup us) rfl
  have dtcs_arg := Det.mk3 dhs0 dns0 dus0
  have htcs_call := tcStep_spec hMa htcs hNU hUH hnU hnN htrN hl_hs₀ hl_ns₀ hl_us
  have sv1 : EvalAll P [inp]
      (.call tcs (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 2) (.nat 0))))
      (fun v1 c1 => TcStepOut (gens hs₀) (gens ns₀) (gens us) v1 ∧
        c1 ≤ tcStepCost hmb hpre hmem hnc hni hder n + 10 ^ 6 * (n + 1) ^ 8) := by
    refine EvalAll.call_funAll dtcs_arg fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine htcs_call.mono fun v1 cb hv1 => ⟨hv1.1, ?_⟩
    clear htcs_call dtcs_arg dus0 dacc0 dns0 dhs0 dctx0
    have wv1 := hv1.1.wt_le
    have w3 := wt_list3_le (encGroup hs₀) (encGroup ns₀) (encGroup us)
    have hcb := hv1.2
    have e_inp : (Val.list [ctx, .nat i, acc0]).wt = inp.wt := rfl
    have e_ctx : (Val.list [encGroup hs₀, encGroup ns₀]).wt = ctx.wt := rfl
    have e_acc0 : (Val.list [encGroup us, tcCsVal L]).wt = acc0.wt := rfl
    clear_value inp ctx acc0
    generalize tcStepCost hmb hpre hmem hnc hni hder n = TCSC at *
    omega
  refine FunAll.intro hstep (EvalAll.letE sv1 fun v1 c1 hv1 => ?_)
  clear sv1 htcs_call dtcs_arg dus0 dacc0 dns0 dhs0 dctx0
  obtain ⟨⟨vs, rfl, hl_vs, hrel⟩, hc1⟩ := hv1
  have wvs := wt_encGroup_le_sq hl_vs
  -- step 2: `v2 = .list (vs'.map encPerm)` via `jni` on `[v1, v1]`
  set env1 := [inp, encGroup vs]
  have dv1_1 := Det.var' (P := P) (env := env1) (i := 1) (v := encGroup vs) rfl
  have dni_arg := Det.mk2 dv1_1 dv1_1
  have hnorm_vs : Normalizes (gens vs) (gens vs) :=
    fun g hg x hx => mul_mem (mul_mem hg hx) (inv_mem hg)
  have hni_raw := normalizedIntersection_call hni htcs.hcnj.jni_eq dni_arg
    ⟨vs, rfl, rfl⟩ ⟨vs, rfl, rfl⟩ hnorm_vs
  have sv2 : EvalAll P env1 (.prim jni (mk2 (.var 1) (.var 1)))
      (fun v2 c2 => GensVal n v2 (gens vs) ∧
        c2 ≤ (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          10 ^ 5 * (n + 1) ^ 8) := by
    refine hni_raw.mono fun v2 c2 hv2 => ⟨?_, ?_⟩
    · have h := hv2.1
      rwa [inf_idem] at h
    · clear hni_raw dni_arg dv1_1
      have w2_ni := wt_list2_le (encGroup vs) (encGroup vs)
      have hsz : (Val.list [encGroup vs, encGroup vs]).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
        (Val.size_le_wt _).trans (by omega)
      have hb := (normalizedIntersectionPrim hni).bound_le hsz
      have hc := hv2.2
      have e_inp : (Val.list [ctx, .nat i, acc0]).wt = inp.wt := rfl
      clear_value inp ctx acc0 env1
      omega
  refine EvalAll.letE sv2 fun v2 c2 hv2 => ?_
  clear sv2 hni_raw dni_arg dv1_1
  obtain ⟨⟨vs', rfl, hl_vs', hgens_vs'⟩, hc2⟩ := hv2
  -- step 3: `mk2 (.var 1) (.snoc (.get (arg 2) (.nat 1)) (.var 2))`
  set env2 := env1 ++ [.list (vs'.map encPerm)]
  have dv1_2 := Det.var' (P := P) (env := env2) (i := 1) (v := encGroup vs) rfl
  have dacc2 := Det.arg' (P := P) (vs := [ctx, .nat i, acc0])
    (rest := [encGroup vs, .list (vs'.map encPerm)]) (j := 2) (v := acc0) rfl
  have dcs2 := Det.get' dacc2 (Det.nat 1)
    (v := .list (L.map fun gs => .list (gs.map encPerm)))
    (show [encGroup us, tcCsVal L][1]? = some _ from rfl)
  have dv2_2 := Det.var' (P := P) (env := env2)
    (i := 2) (v := .list (vs'.map encPerm)) rfl
  have dsnoc := Det.snoc dcs2 dv2_2
  rw [← tcCsVal_snoc L vs'] at dsnoc
  have dout := Det.mk2 dv1_2 dsnoc
  refine dout.post fun c3 hc3 => ⟨?_, ?_⟩
  · refine ⟨vs, L ++ [vs'], rfl, hl_vs, ?_, ?_, hrel.1, hrel.2.1.trans hUH, hrel.2.2.1, ?_, ?_⟩
    · simp [hL_len]
    · intro gs hgs
      rcases List.mem_append.mp hgs with hgs | hgs
      · exact hl_L gs hgs
      · simp only [List.mem_singleton] at hgs
        rwa [hgs]
    · rcases hrel.2.2.2.1 with hUN | hcard_step
      · left; exact hrel.2.1.trans hUN
      · rcases hbr with hUN | hcard_i
        · left; exact hrel.2.1.trans hUN
        · right
          calc 2 ^ (i + 1) * Nat.card (gens vs)
              = 2 ^ i * (2 * Nat.card (gens vs)) := by ring
            _ ≤ 2 ^ i * Nat.card (gens us) := Nat.mul_le_mul_left _ hcard_step
            _ ≤ Nat.card (gens hs₀) := hcard_i
    · rw [List.map_append, List.map_singleton, hgens_vs']
      exact tcPartialChain_snoc hch hUH hrel
  · clear dout dsnoc dv2_2 dcs2 dacc2 dv1_2
    have wv2 := GensVal.wt_le ⟨vs', rfl, hl_vs', hgens_vs'⟩
    have hl_L' : ∀ gs ∈ L ++ [vs'], gs.length ≤ n ^ 2 := by
      intro gs hgs
      rcases List.mem_append.mp hgs with hgs | hgs
      · exact hl_L gs hgs
      · simp only [List.mem_singleton] at hgs; rwa [hgs]
    have wcs' : (tcCsVal (L ++ [vs'])).wt ≤ 100 * (n + 1) ^ 8 :=
      SeriesVal.wt_le ⟨L ++ [vs'], rfl, by simp [hL_len]; omega, hl_L', rfl⟩
    have wout := wt_list2_le (encGroup vs) (tcCsVal (L ++ [vs']))
    have e_inp : (Val.list [ctx, .nat i, acc0]).wt = inp.wt := rfl
    have e_ctx : (Val.list [encGroup hs₀, encGroup ns₀]).wt = ctx.wt := rfl
    have e_acc0 : (Val.list [encGroup us, tcCsVal L]).wt = acc0.wt := rfl
    have e_cs : (Val.list (L.map fun gs => .list (gs.map encPerm))).wt = (tcCsVal L).wt := rfl
    have e_cs' : (Val.list ((L.map fun gs => .list (gs.map encPerm)) ++
        [.list (vs'.map encPerm)])).wt = (tcCsVal (L ++ [vs'])).wt := by
      rw [tcCsVal_snoc]
    unfold tcChainStepCost
    clear_value inp ctx acc0 env1 env2
    generalize tcStepCost hmb hpre hmem hnc hni hder n = TCSC at *
    generalize (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) = NI at *
    omega

/-- Total cost bound of `tcChainEntry` on input of weight `W` and degree `n`. -/
noncomputable def tcChainCost (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup)
    (W n : ℕ) : ℕ :=
  2 * reduceCost hmem n W +
    (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    (n + 1) ^ 2 * tcChainStepCost hmb hpre hmem hnc hni hder n +
    10 ^ 10 * (n + 1) ^ 10 + 100 * W

/-- **Specification of `tcChainEntry`.**
On `[encGroup hs, encGroup ns]` where `gens ns ≤ gens hs`, `gens hs` normalizes `gens ns`,
and `gens ns` is transitive on `Fin n` (when `1 ≤ n`), returns `cs` satisfying
`SeriesVal n cs Hs` and `IsNonabelianChiefChain (gens hs) (gens ns) Hs` for some `Hs`,
within cost `tcChainCost hmb hpre hmem hnc hni hder (Val.list [encGroup hs, encGroup ns]).wt n`. -/
theorem tcChain_spec (hMa : MarotiPrimitive)
    {hmb : MinimalBlocks} {hpre : Preimage} {hmem : Membership}
    {hnc : NormalClosure} {hni : NormalizedIntersection} {hder : DerivedSubgroup}
    {P : Program}
    {f it_ch ch_step tcs ap mg le red
     ob it_ob g_ob obk rep lo dom cls ker
     grd gr fl_g gs_g
     cnj itc cjp flc cjs iv mc cj cp
     jmb jpre jmem jnc jni jder : ℕ}
    (hP : TcChainAt P f it_ch ch_step tcs ap mg le red
      ob it_ob g_ob obk rep lo dom cls ker
      grd gr fl_g gs_g cnj itc cjp flc cjs iv mc cj cp
      jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder)
    (hs ns : List (Perm (Fin n)))
    (hNH : gens ns ≤ gens hs)
    (hnN : ∀ g ∈ gens hs, ∀ x ∈ gens ns, g * x * g⁻¹ ∈ gens ns)
    (htrN : 1 ≤ n → MulAction.IsPretransitive (gens ns) (Fin n)) :
    FunAll P f (.list [encGroup hs, encGroup ns])
      (fun cs cost =>
        (∃ Hs, SeriesVal n cs Hs ∧ IsNonabelianChiefChain (gens hs) (gens ns) Hs) ∧
        cost ≤ tcChainCost hmb hpre hmem hnc hni hder
          (Val.list [encGroup hs, encGroup ns]).wt n) := by
  set inp := Val.list [encGroup hs, encGroup ns]
  set W := inp.wt
  have whs_lt : (encGroup hs).wt < W := wt_le_wt_list (by simp)
  have wns_lt : (encGroup ns).wt < W := wt_le_wt_list (by simp)
  have hl_hs_W : hs.length ≤ W := by
    have := S_le_wt_encGroup hs
    have : hs.length + 2 ≤ (hs.length + 2) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hl_ns_W : ns.length ≤ W := by
    have := S_le_wt_encGroup ns
    have : ns.length + 2 ≤ (ns.length + 2) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p810 : (n + 1) ^ 8 ≤ (n + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- step 1: `v1 = encGroup hs₀` via `red` on `arg 0`
  set hs₀ := keepList hs
  have hl_hs₀ : hs₀.length ≤ n ^ 2 := length_keepList_le hs
  have hgens_hs₀ : gens hs₀ = gens hs := gens_keepList hs
  have whs₀ := wt_encGroup_le_sq hl_hs₀
  have dhs0 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns]) (rest := []) (j := 0) rfl
  have dv1_raw := Det.call dhs0 (reduce_spec hmem hP.tcs.hred hP.tcs.hob.obk.jmem_eq hs)
  have hrc_hs := reduceCost_mono hmem n hl_hs_W
  have dv1 : Det P [inp] (.call red (arg 0)) (encGroup hs₀)
      (reduceCost hmem n W + 20 * W + 1000 * (n + 1) ^ 6) := by
    refine dv1_raw.mono ?_
    have e_inp : (Val.list [encGroup hs, encGroup ns]).wt = W := rfl
    have e_hs₀ : (encGroup (keepList hs)).wt = (encGroup hs₀).wt := rfl
    clear_value inp W hs₀
    omega
  -- step 2: `v2 = encGroup ns₀` via `red` on `arg 1`
  set ns₀ := keepList ns
  have hl_ns₀ : ns₀.length ≤ n ^ 2 := length_keepList_le ns
  have hgens_ns₀ : gens ns₀ = gens ns := gens_keepList ns
  have wns₀ := wt_encGroup_le_sq hl_ns₀
  set env1 := [inp, encGroup hs₀]
  have dns1 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns])
    (rest := [encGroup hs₀]) (j := 1) rfl
  have dv2_raw := Det.call dns1 (reduce_spec hmem hP.tcs.hred hP.tcs.hob.obk.jmem_eq ns)
  have hrc_ns := reduceCost_mono hmem n hl_ns_W
  have dv2 : Det P env1 (.call red (arg 1)) (encGroup ns₀)
      (reduceCost hmem n W + 20 * W + 1000 * (n + 1) ^ 6) := by
    refine dv2_raw.mono ?_
    have e_inp : (Val.list [encGroup hs, encGroup ns]).wt = W := rfl
    have e_ns₀ : (encGroup (keepList ns)).wt = (encGroup ns₀).wt := rfl
    clear_value inp W hs₀ ns₀ env1
    omega
  -- step 3: `v3 = .list (hs₀'.map encPerm)` via `jni` on `[.var 1, .var 1]`
  set env2 := env1 ++ [encGroup ns₀]
  have dv1_2 := Det.var' (P := P) (env := env2) (i := 1) (v := encGroup hs₀) rfl
  have dni_arg := Det.mk2 dv1_2 dv1_2
  have hnorm_hs₀ : Normalizes (gens hs₀) (gens hs₀) :=
    fun g hg x hx => mul_mem (mul_mem hg hx) (inv_mem hg)
  have hni_raw := normalizedIntersection_call hni hP.tcs.hcnj.jni_eq dni_arg
    ⟨hs₀, rfl, rfl⟩ ⟨hs₀, rfl, rfl⟩ hnorm_hs₀
  have sv3 : EvalAll P env2 (.prim jni (mk2 (.var 1) (.var 1)))
      (fun v3 c3 => GensVal n v3 (gens hs₀) ∧
        c3 ≤ (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          10 ^ 5 * (n + 1) ^ 6) := by
    refine hni_raw.mono fun v3 c3 hv3 => ⟨?_, ?_⟩
    · have h := hv3.1
      rwa [inf_idem] at h
    · clear hni_raw dni_arg dv1_2
      have w2_ni := wt_list2_le (encGroup hs₀) (encGroup hs₀)
      have hsz : (Val.list [encGroup hs₀, encGroup hs₀]).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
        (Val.size_le_wt _).trans (by omega)
      have hb := (normalizedIntersectionPrim hni).bound_le hsz
      have hc := hv3.2
      clear_value inp W hs₀ ns₀ env1 env2
      omega
  refine FunAll.intro hP.entry (EvalAll.letE dv1 fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  refine EvalAll.letE dv2 fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  refine EvalAll.letE sv3 fun v3 c3 hv3 => ?_
  clear sv3 hni_raw dni_arg dv1_2 dv2 dv2_raw dns1 dv1 dv1_raw dhs0
  obtain ⟨⟨hs₀', rfl, hl_hs₀', hgens_hs₀'⟩, hc3⟩ := hv3
  -- step 4: `iterFuns` (`it_ch`) for `k = n * n` steps
  set k := n * n
  have hk_eq : k = n ^ 2 := (sq n).symm
  have hk2 : k ≤ (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  set c_it := Val.list [encGroup hs₀, encGroup ns₀]
  set acc_init := Val.list [encGroup hs₀, tcCsVal [hs₀']]
  have hNH₀ : gens ns₀ ≤ gens hs₀ := by rwa [hgens_ns₀, hgens_hs₀]
  have hnN₀ : ∀ g ∈ gens hs₀, ∀ x ∈ gens ns₀, g * x * g⁻¹ ∈ gens ns₀ := by
    rwa [hgens_hs₀, hgens_ns₀]
  have htrN₀ : 1 ≤ n → MulAction.IsPretransitive (gens ns₀) (Fin n) := by
    intro hn1; rw [hgens_ns₀]; exact htrN hn1
  have h0 : TcChainLoopInv (gens hs₀) (gens ns₀) 0 acc_init := by
    refine ⟨hs₀, [hs₀'], rfl, hl_hs₀, rfl, ?_, hNH₀, le_rfl,
      fun g hg x hx => mul_mem (mul_mem hg hx) (inv_mem hg),
      Or.inr (by simp), ?_⟩
    · intro gs hgs
      simp only [List.mem_singleton] at hgs
      rwa [hgs]
    · simp only [List.map_singleton, hgens_hs₀']
      exact tcPartialChain_singleton rfl
  set B := tcChainStepCost hmb hpre hmem hnc hni hder n
  have hstep_it : ∀ i acc, i < k → TcChainLoopInv (gens hs₀) (gens ns₀) i acc →
      FunAll P ch_step (.list [c_it, .nat i, acc])
        (fun w cost => TcChainLoopInv (gens hs₀) (gens ns₀) (i + 1) w ∧ cost ≤ B) := by
    intro i acc hi hinv
    rw [hk_eq] at hi
    exact tcChainStep_spec hMa hP.step hP.tcs hnN₀ htrN₀ hl_hs₀ hl_ns₀ i hi hinv
  have hit := iter_spec hP.iter (c := c_it) (k := k) (M := 1000 * (n + 1) ^ 8) h0
    (fun i _ hi hinv => hinv.wt_le (hk_eq ▸ hi)) hstep_it
  set env3 := env2 ++ [.list (hs₀'.map encPerm)]
  have dv1_3 := Det.var' (P := P) (env := env3) (i := 1) (v := encGroup hs₀) rfl
  have dv2_3 := Det.var' (P := P) (env := env3) (i := 2) (v := encGroup ns₀) rfl
  have dc_it := Det.mk2 dv1_3 dv2_3
  have dhs3 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns])
    (rest := [encGroup hs₀, encGroup ns₀, .list (hs₀'.map encPerm)]) (j := 0) rfl
  have dn3 := Det.get' dhs3 (Det.nat 0) (v := .nat n)
    (show [Val.nat n, Val.list ((1 :: hs).map encPerm)][0]? = some (.nat n) from rfl)
  have dk := Det.arith' (z := k) (op := .mul) dn3 dn3 rfl
  have dv3_3 := Det.var' (P := P) (env := env3) (i := 3) (v := .list (hs₀'.map encPerm)) rfl
  have dacc_init := Det.mk2 dv1_3 (Det.mk1 dv3_3)
  have darg_it := Det.mk3 dc_it dk dacc_init
  refine EvalAll.letE
    (Ra := fun v4 c4 => TcChainLoopInv (gens hs₀) (gens ns₀) k v4 ∧
      c4 ≤ (n + 1) ^ 2 * B + 10 ^ 9 * (n + 1) ^ 10 + 20 * W)
    (EvalAll.call_funAll darg_it fun v ca hv => ?_) fun v4 c4 hv4 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hit.mono fun w cb hw => ⟨hw.1, ?_⟩
    clear hit hstep_it darg_it dacc_init dv3_3 dk dn3 dhs3 dc_it dv2_3 dv1_3
    have w_out := hw.1.wt_le (hk_eq ▸ le_rfl)
    have wv3 := GensVal.wt_le ⟨hs₀', rfl, hl_hs₀', hgens_hs₀'⟩
    have w1_v3 := wt_list1_le (.list (hs₀'.map encPerm))
    have w_acc_init := wt_list2_le (encGroup hs₀) (.list [.list (hs₀'.map encPerm)])
    have wc_it := wt_list2_le (encGroup hs₀) (encGroup ns₀)
    have wn := wt_nat_le n
    have wk := wt_nat_le k
    have w3_it := wt_list3_le c_it (.nat k) acc_init
    have w_hsL : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: hs).map encPerm)]) (by simp)
    have hcb := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcb
    have hkb : k * B ≤ (n + 1) ^ 2 * B := Nat.mul_le_mul_right _ hk2
    have e_cit : (Val.list [encGroup hs₀, encGroup ns₀]).wt = c_it.wt := rfl
    have e_acc : (Val.list [encGroup hs₀, .list [.list (hs₀'.map encPerm)]]).wt = acc_init.wt := rfl
    have e_w3 : (Val.list [Val.list [encGroup hs₀, encGroup ns₀], .nat k,
        Val.list [encGroup hs₀, .list [.list (hs₀'.map encPerm)]]]).wt =
      (Val.list [c_it, .nat k, acc_init]).wt := rfl
    have hloop : loopModK * (k + 1) *
        ((Val.list [c_it, .nat k, acc_init]).wt + k + 1000 * (n + 1) ^ 8 + 1) ≤
        loopModK * (2 * (n + 1) ^ 2) * (10000 * (n + 1) ^ 8) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have hloop' : loopModK * (2 * (n + 1) ^ 2) * (10000 * (n + 1) ^ 8) =
        2 * 10 ^ 7 * (n + 1) ^ 10 := by simp only [loopModK]; ring
    have e_inp : (Val.list [encGroup hs, encGroup ns]).wt = W := rfl
    clear_value inp W hs₀ ns₀ env1 env2 env3 k c_it acc_init B
    generalize (n + 1) ^ 2 * B = N2B at *
    omega
  -- step 5: `.get (.var 4) (.nat 1)` extracts `tcCsVal L`
  clear hit hstep_it darg_it dacc_init dv3_3 dk dn3 dhs3 dc_it dv2_3 dv1_3
  obtain ⟨⟨us, L, rfl, hl_us, hL_len, hl_L, hNU, hUH, hnU, hbr, hch⟩, hc4⟩ := hv4
  have hUN : gens us ≤ gens ns₀ := by
    rcases hbr with hUN | hcard
    · exact hUN
    · rw [hk_eq] at hcard
      by_contra hnot
      exact not_two_pow_sq_mul_card_le (one_le_of_not_le hnot) (gens us) (gens hs₀) hcard
  set env4 := env3 ++ [.list [encGroup us, tcCsVal L]]
  have dv4 := Det.var' (P := P) (env := env4) (i := 4)
    (v := .list [encGroup us, tcCsVal L]) rfl
  have dget := Det.get' dv4 (Det.nat 1) (v := tcCsVal L)
    (show [encGroup us, tcCsVal L][1]? = some (tcCsVal L) from rfl)
  refine dget.post fun c5 hc5 => ⟨?_, ?_⟩
  · refine ⟨L.map gens, ⟨L, rfl, by omega, hl_L, rfl⟩, ?_⟩
    rw [← hgens_hs₀, ← hgens_ns₀]
    exact tcPartialChain_to_nonabelianChief hch hUN
  · clear dget dv4
    have wus := wt_encGroup_le_sq hl_us
    have wcs : (tcCsVal L).wt ≤ 100 * (n + 1) ^ 8 :=
      SeriesVal.wt_le ⟨L, rfl, by omega, hl_L, rfl⟩
    have wv4 := wt_list2_le (encGroup us) (tcCsVal L)
    have wv3 := GensVal.wt_le ⟨hs₀', rfl, hl_hs₀', hgens_hs₀'⟩
    have e_B : (n + 1) ^ 2 * tcChainStepCost hmb hpre hmem hnc hni hder n = (n + 1) ^ 2 * B := rfl
    unfold tcChainCost
    rw [e_B]
    clear_value inp W hs₀ ns₀ env1 env2 env3 env4 k c_it acc_init B
    generalize reduceCost hmem n W = RC1 at *
    generalize (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) = NI at *
    generalize (n + 1) ^ 2 * B = N2B at *
    omega

/-! ### 4. Polynomial Cost Bound (`PBU`) and Synthetic `Prim` (`tcChainPrim`) -/

/-- `Prim.boundSize` preserves `PBU`. -/
theorem PBU.boundSize (p : Prim) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU (fun k W B => p.boundSize (f k W B)) :=
  PBU.smul p.c ((hf.addc 2).pow p.k)

/-- Composition of a `PBU` bound with three `PBU` arguments. -/
theorem PBU.comp {g fk fW fB : ℕ → ℕ → ℕ → ℕ}
    (hg : PBU g) (hk : PBU fk) (hW : PBU fW) (hB : PBU fB) :
    PBU (fun k W B => g (fk k W B) (fW k W B) (fB k W B)) := by
  obtain ⟨C, D, h⟩ := hg
  exact PBU.mono (PBU.smul C ((((hW.add hB).add hk).addc 2).pow D))
    fun k W B => h (fk k W B) (fW k W B) (fB k W B)

/-- Monotonicity of `gmpRepsCost` in `q`. -/
theorem tc_gmpRepsCost_mono_q (hm : Membership) (W : ℕ) {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    gmpRepsCost hm W q₁ ≤ gmpRepsCost hm W q₂ := by
  have hq2 : q₁ + 2 ≤ q₂ + 2 := Nat.add_le_add_right hq 2
  have hqY : (q₁ + 2) * gmpRepsWeight W ≤ (q₂ + 2) * gmpRepsWeight W :=
    Nat.mul_le_mul_right _ hq2
  have ht : tmRpTestC hm (gmpRepsWeight W) (q₁ + 2) ≤
      tmRpTestC hm (gmpRepsWeight W) (q₂ + 2) :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hq2)
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hq2 hq2)))
  have hr : tmRpRoundC hm (gmpRepsWeight W) (q₁ + 2) ≤
      tmRpRoundC hm (gmpRepsWeight W) (q₂ + 2) :=
    Nat.add_le_add (Nat.mul_le_mul_left _ ht)
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hqY))
  unfold gmpRepsCost
  refine Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_right hq 1) (Nat.add_le_add hr ?_))
    (Nat.mul_le_mul_left 10000 hqY)
  exact Nat.mul_le_mul_left tmRpWK
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hq _) (Nat.mul_le_mul_left 10 hqY)) 10)

/-- Monotonicity of `tcGreedyCost` in `q`. -/
theorem tcGreedyCost_mono_q (hnc : NormalClosure) (hmem : Membership) (n : ℕ)
    {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    tcGreedyCost hnc hmem n q₁ ≤ tcGreedyCost hnc hmem n q₂ := by
  unfold tcGreedyCost
  refine Nat.add_le_add
    (Nat.add_le_add (tc_gmpRepsCost_mono_q hmem _ hq)
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hq 1)))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2)))

/-- For all `n : ℕ`, `n ^ (1 + Nat.log 2 n) ≤ n * tcRadQ n`. -/
theorem pow_log_le_mul_tcRadQ (n : ℕ) : n ^ (1 + Nat.log 2 n) ≤ n * tcRadQ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  · rw [pow_add, pow_one]
    refine Nat.mul_le_mul_left n ?_
    have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog : (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
      have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (pow_pos (by norm_num) _) hpow
      simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using h1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hrpow : ((n ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
      calc ((n ^ Nat.log 2 n : ℕ) : ℝ) = (n : ℝ) ^ ((Nat.log 2 n : ℕ) : ℝ) := by
            rw [Real.rpow_natCast]; push_cast; rfl
        _ ≤ (n : ℝ) ^ Real.logb 2 n := Real.rpow_le_rpow_of_exponent_le hn1 hlog
    exact_mod_cast hrpow.trans (Nat.le_ceil _)

theorem tcConjIndexBd_le (n : ℕ) : tcConjIndexBd n ≤ n * tcRadQ n :=
  pow_log_le_mul_tcRadQ n

theorem tcObIndexBd_le (n : ℕ) :
    tcObIndexBd n ≤ (Nat.factorial 24 + n * tcRadQ n) * (n * tcRadQ n) := by
  unfold tcObIndexBd
  have h1 := pow_log_le_mul_tcRadQ n
  have h2 : max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) ≤ Nat.factorial 24 + n * tcRadQ n := by
    have := Nat.max_le.mpr ⟨Nat.le_add_right (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)),
      Nat.le_add_left (n ^ (1 + Nat.log 2 n)) (Nat.factorial 24)⟩
    omega
  exact Nat.mul_le_mul h2 h1

theorem memCost_pbu (hm : Membership) : PBU (fun n _ _ => memCost hm n) :=
  PBU.smul (membershipPrim hm).c ((PBU.smul 400 (PBU.k1.pow 6)).pow (membershipPrim hm).k)

theorem reduceCost_pbu (hm : Membership) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU (fun n W B => reduceCost hm n (f n W B)) :=
  ((hf.addc 1).mul (memCost_pbu hm)).add
    (PBU.smul reduceK (((hf.addc 2).mul PBU.k1).pow 6))

theorem obKernelCost_pbu (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership) :
    PBU (fun n _ _ => obKernelCost hmb hpre hmem n) := by
  have hn6 := PBU.k1.pow 6
  have h10_4 := PBU.smul (10 ^ 4) hn6
  have h1 := PBU.boundSize (minimalBlocksPrim hmb) h10_4
  have h2 := PBU.boundSize (preimagePrim hpre) h10_4
  have h3 := reduceCost_pbu hmem (PBU.smul 320 hn6)
  have h4 := PBU.smul kerK ((PBU.smul 700 hn6).pow 9)
  have h5 := PBU.smul (10 ^ 16) (PBU.k1.pow 21)
  exact (((h1.add h2).add h3).add h4).add h5

theorem obStepCost_pbu (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership) :
    PBU (fun n _ _ => obStepCost hmb hpre hmem n) := by
  have h10_4 := PBU.smul (10 ^ 4) (PBU.k1.pow 6)
  exact ((obKernelCost_pbu hmb hpre hmem).add
    (h10_4.mul (PBU.boundSize (membershipPrim hmem) h10_4))).add
    (PBU.smul (10 ^ 20) (PBU.k1.pow 18))

theorem obCost_pbu (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership) :
    PBU (fun n _ _ => obCost hmb hpre hmem n) :=
  (((PBU.k1.pow 2).mul (obStepCost_pbu hmb hpre hmem)).add
    (reduceCost_pbu hmem (PBU.smul 3 (PBU.k1.pow 2)))).add
    (PBU.smul (10 ^ 22) (PBU.k1.pow 20))

theorem tcGreedyStepCost_pbu (hnc : NormalClosure) (hmem : Membership) :
    PBU (fun n _ _ => tcGreedyStepCost hnc hmem n) := by
  have h10_4 := PBU.smul (10 ^ 4) (PBU.k1.pow 6)
  exact ((PBU.boundSize (normalClosurePrim hnc) h10_4).add
    (h10_4.mul (PBU.boundSize (membershipPrim hmem) h10_4))).add
    (PBU.smul (10 ^ 19) (PBU.k1.pow 18))

theorem tcGreedyCost_pbu (hnc : NormalClosure) (hmem : Membership)
    {fq : ℕ → ℕ → ℕ → ℕ} (hq : PBU fq) :
    PBU (fun n W B => tcGreedyCost hnc hmem n (fq n W B)) := by
  have hq1 := hq.addc 1
  have h1 := PBU.comp (gmpRepsCost_poly hmem) hq (PBU.smul 2000 (PBU.k1.pow 6)) (PBU.const 0)
  have h2 := hq1.mul (tcGreedyStepCost_pbu hnc hmem)
  have h3 := PBU.smul (10 ^ 10) ((hq1.pow 2).mul (PBU.k1.pow 6))
  exact (h1.add h2).add h3

theorem tcConjStepCost_pbu (hni : NormalizedIntersection) (hmem : Membership) :
    PBU (fun n _ _ => tcConjStepCost hni hmem n) := by
  have h10_4 := PBU.smul (10 ^ 4) (PBU.k1.pow 6)
  exact ((PBU.boundSize (normalizedIntersectionPrim hni) h10_4).add
    (h10_4.mul (PBU.boundSize (membershipPrim hmem) h10_4))).add
    (PBU.smul (10 ^ 19) (PBU.k1.pow 18))

theorem tcConjPassCost_pbu (hni : NormalizedIntersection) (hmem : Membership) :
    PBU (fun n _ _ => tcConjPassCost hni hmem n) :=
  ((PBU.smul 2 (PBU.k1.pow 2)).mul (tcConjStepCost_pbu hni hmem)).add
    (PBU.smul (10 ^ 9) (PBU.k1.pow 8))

theorem tcConjCost_pbu (hni : NormalizedIntersection) (hmem : Membership) :
    PBU (fun n _ _ => tcConjCost hni hmem n) :=
  ((PBU.k1.pow 2).mul (tcConjPassCost_pbu hni hmem)).add
    (PBU.smul (10 ^ 9) (PBU.k1.pow 8))

/-- Upper bound on `tcStepCost` parameterized by `B` (playing the role of `tcRadQ n`). -/
noncomputable def tcStepCostBd (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup)
    (n B : ℕ) : ℕ :=
  (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    reduceCost hmem n (3 * (n + 1) ^ 2) +
    2 * (10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6)) +
    obCost hmb hpre hmem n +
    tcGreedyCost hnc hmem n ((Nat.factorial 24 + n * B) * (n * B)) +
    tcConjCost hni hmem n +
    tcGreedyCost hnc hmem n (n * B) +
    10 ^ 20 * (n + 1) ^ 18

theorem tcStepCost_le_bd (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) (n : ℕ) :
    tcStepCost hmb hpre hmem hnc hni hder n ≤
      tcStepCostBd hmb hpre hmem hnc hni hder n (tcRadQ n) := by
  unfold tcStepCost tcStepCostBd
  have hg1 := tcGreedyCost_mono_q hnc hmem n (tcObIndexBd_le n)
  have hg2 := tcGreedyCost_mono_q hnc hmem n (tcConjIndexBd_le n)
  omega

theorem tcStepCostBd_pbu (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) :
    PBU (fun n _ B => tcStepCostBd hmb hpre hmem hnc hni hder n B) := by
  have h10_4 := PBU.smul (10 ^ 4) (PBU.k1.pow 6)
  have hq2 : PBU (fun n _ B => n * B) := PBU.k.mul PBU.B
  have hq1 : PBU (fun n _ B => (Nat.factorial 24 + n * B) * (n * B)) :=
    ((PBU.const (Nat.factorial 24)).add hq2).mul hq2
  have s1 := PBU.boundSize (derivedSubgroupPrim hder) h10_4
  have s2 := reduceCost_pbu hmem (PBU.smul 3 (PBU.k1.pow 2))
  have s3 := PBU.smul 2 (h10_4.mul (PBU.boundSize (membershipPrim hmem) h10_4))
  have s4 := obCost_pbu hmb hpre hmem
  have s5 := tcGreedyCost_pbu hnc hmem hq1
  have s6 := tcConjCost_pbu hni hmem
  have s7 := tcGreedyCost_pbu hnc hmem hq2
  have s8 := PBU.smul (10 ^ 20) (PBU.k1.pow 18)
  exact ((((((s1.add s2).add s3).add s4).add s5).add s6).add s7).add s8

/-- Upper bound on `tcChainCost` parameterized by `(n, W, B)`. -/
noncomputable def tcChainCostBd (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup)
    (n W B : ℕ) : ℕ :=
  2 * reduceCost hmem n W +
    (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    (n + 1) ^ 2 * (tcStepCostBd hmb hpre hmem hnc hni hder n B +
      (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
      10 ^ 9 * (n + 1) ^ 8) +
    10 ^ 10 * (n + 1) ^ 10 + 100 * W

theorem tcChainCost_le_bd (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup)
    (W n : ℕ) :
    tcChainCost hmb hpre hmem hnc hni hder W n ≤
      tcChainCostBd hmb hpre hmem hnc hni hder n W (tcRadQ n) := by
  unfold tcChainCost tcChainStepCost tcChainCostBd
  have h1 := tcStepCost_le_bd hmb hpre hmem hnc hni hder n
  have h2 : (n + 1) ^ 2 * (tcStepCost hmb hpre hmem hnc hni hder n +
      (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 9 * (n + 1) ^ 8) ≤
    (n + 1) ^ 2 * (tcStepCostBd hmb hpre hmem hnc hni hder n (tcRadQ n) +
      (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 9 * (n + 1) ^ 8) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem tcChainCostBd_pbu (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) :
    PBU (tcChainCostBd hmb hpre hmem hnc hni hder) := by
  have h10_4 := PBU.smul (10 ^ 4) (PBU.k1.pow 6)
  have hni_b := PBU.boundSize (normalizedIntersectionPrim hni) h10_4
  have c1 := PBU.smul 2 (reduceCost_pbu hmem PBU.W)
  have c2 := (PBU.k1.pow 2).mul
    (((tcStepCostBd_pbu hmb hpre hmem hnc hni hder).add hni_b).add
      (PBU.smul (10 ^ 9) (PBU.k1.pow 8)))
  have c3 := PBU.smul (10 ^ 10) (PBU.k1.pow 10)
  have c4 := PBU.smul 100 PBU.W
  exact (((c1.add hni_b).add c2).add c3).add c4

/-- Two-variable polynomial bound on `tcChainCost` when `n ≤ W`. -/
theorem tcChainCost_le (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) :
    ∃ C D : ℕ, ∀ W n : ℕ, n ≤ W →
      tcChainCost hmb hpre hmem hnc hni hder W n ≤ C * (W + tcRadQ n + 2) ^ D := by
  obtain ⟨C, D, h⟩ := tcChainCostBd_pbu hmb hpre hmem hnc hni hder
  refine ⟨C * 2 ^ D, D, fun W n hnW => ?_⟩
  have h1 := (tcChainCost_le_bd hmb hpre hmem hnc hni hder W n).trans (h n W (tcRadQ n))
  have h2 : W + tcRadQ n + n + 2 ≤ 2 * (W + tcRadQ n + 2) := by omega
  calc tcChainCost hmb hpre hmem hnc hni hder W n
      ≤ C * (W + tcRadQ n + n + 2) ^ D := h1
    _ ≤ C * (2 * (W + tcRadQ n + 2)) ^ D :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left h2 D)
    _ = C * 2 ^ D * (W + tcRadQ n + 2) ^ D := by rw [mul_pow]; ring

/-- Synthetic `Prim` whose `boundSize` at `W + tcRadQ n` bounds
`tcChainCost hmb hpre hmem hnc hni hder W n` whenever `n ≤ W`. -/
noncomputable def tcChainPrim (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) : Prim where
  Pre := fun _ => False
  Post := fun _ _ => True
  c := (tcChainCost_le hmb hpre hmem hnc hni hder).choose
  k := (tcChainCost_le hmb hpre hmem hnc hni hder).choose_spec.choose
  prog := (membershipPrim hmem).prog
  spec := fun x => x.2.elim

theorem tcChainCost_le_boundSize (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup)
    {W n : ℕ} (hnW : n ≤ W) :
    tcChainCost hmb hpre hmem hnc hni hder W n ≤
      (tcChainPrim hmb hpre hmem hnc hni hder).boundSize (W + tcRadQ n) :=
  (tcChainCost_le hmb hpre hmem hnc hni hder).choose_spec.choose_spec W n hnW

end GI.Impl
