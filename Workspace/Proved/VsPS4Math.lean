module

public import Workspace.Proved.VsPStep4Math
public import Workspace.Proved.VsPBasMath
public import Workspace.Proved.VsMIndep
public import Workspace.Impl.VsPFin

@[expose] public section

/-!
# The nondegenerate stage in permutation terms

`VsPS4` collects what holds when the pairing on `N̄₂ = vsPBar (gens gs)` is set up: `N̄₂`
centralizes `Ā`, has commutators and `r`-th powers in `S`, is normalized by the images of `hs`,
the commutator `ζ = ρ c0` gives the pairing, and the radical lies in `S`. From it:
* the key map of the program is a key map (`VsPS4.key`), with at most `D²` values;
* the orbit lists stay in `vsPT`, with fitting keys, for every number of passes;
* the spin dimension `d` of the program has `r^d ≤ D²` (`VsPS4.pow_dim_le`).
-/

set_option backward.isDefEq.respectTransparency false

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv Module
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]

/-- The images of the generators of `H`. -/
noncomputable abbrev vsPHg (hs : VsQStOK s) : Set (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ :=
  vsPRho hs '' {y | y ∈ s.hs}

/-- The pairing setup. -/
structure VsPS4 (hs : VsQStOK s) (as gs : List (Perm (Fin I.n))) (r : ℕ) (c0 : Perm (Fin I.n)) :
    Prop where
  hAc : ∀ a ∈ vsPBar hs (gens as), ∀ b ∈ vsPBar hs (gens as), a * b = b * a
  hdom : vsTDom (vsTAlg (vsPBar hs (gens as)))
  hgs : ∀ g ∈ gs, g ∈ gens s.hs
  hNC : vsPBar hs (gens gs) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _)
  hNn : ∀ h ∈ vsPHg hs, ∀ x ∈ vsPBar hs (gens gs), h * x * h⁻¹ ∈ vsPBar hs (gens gs)
  hc : ∀ x ∈ vsPBar hs (gens gs), ∀ y ∈ vsPBar hs (gens gs), ⁅x, y⁆ ∈ vsMScal (vsPBar hs (gens as))
  hpow : ∀ x ∈ vsPBar hs (gens gs), x ^ r ∈ vsMScal (vsPBar hs (gens as))
  hc0 : c0 ∈ gens s.hs
  hP : VsPPairHyp (vsPBar hs (gens gs)) r (vsPRho hs c0)
  hrad : ∀ x ∈ vsPBar hs (gens gs), (∀ g ∈ gs.map (vsPRho hs), x * g = g * x) →
    x ∈ vsMScal (vsPBar hs (gens as))

variable {hs : VsQStOK s} {as gs : List (Perm (Fin I.n))} {r : ℕ} {c0 : Perm (Fin I.n)}

/-- The local image of `⟨gs⟩` as a closure of a list. -/
theorem vsPBar_gens' (hgs : ∀ g ∈ gs, g ∈ gens s.hs) :
    vsPBar hs (gens gs) = Subgroup.closure {g | g ∈ gs.map (vsPRho hs)} := by
  rw [vsPBar_gens hs hgs]
  congr 1; ext u; simp [eq_comm]

theorem VsPS4.sc (h : VsPS4 hs as gs r c0) :
    ∀ x ∈ vsMScal (vsPBar hs (gens as)), ∀ y ∈ vsPBar hs (gens gs), x * y = y * x :=
  fun x hx y hy => (vsM_comm_scal (h.hNC hy) hx).symm

/-- **The key map.** -/
theorem VsPS4.key [NeZero r] (h : VsPS4 hs as gs r c0) :
    VsPKeyHyp (vsPBar hs (gens gs)) (vsMScal (vsPBar hs (gens as)))
      (vsPKV r (vsPRho hs c0) (gs.map (vsPRho hs))) :=
  vsPKV_hyp h.hP (vsPBar_gens' h.hgs) h.hrad h.sc

/-- **The index bound** `|N̄₂ : S| ≤ D²`. -/
theorem VsPS4.indep [Nontrivial (Fin (vsQD s) → ZMod I.p)] (h : VsPS4 hs as gs r c0) :
    (vsMScal (vsPBar hs (gens as))).relIndex (vsPBar hs (gens gs)) ≤ vsQD s ^ 2 := by
  have := vsM_indep (p := I.p) (V := Fin (vsQD s) → ZMod I.p) _ _ h.hAc h.hdom h.hNC h.hc
    (fun x hx hcomm => h.hrad x hx fun g hg => hcomm g (by
      rw [vsPBar_gens' h.hgs]; exact Subgroup.subset_closure hg))
  rwa [Module.finrank_fin_fun] at this

theorem VsPS4.gN (h : VsPS4 hs as gs r c0) : ∀ g ∈ gs, vsPRho hs g ∈ vsPBar hs (gens gs) :=
  fun g hg => vsPRho_mem_vsPBar hs (Subgroup.subset_closure hg) (h.hgs g hg)

/-- The orbit set `vsPT` is closed under conjugation by `1 :: hs`. -/
theorem VsPS4.T_conj (h : VsPS4 hs as gs r c0) {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) :
    ∀ g ∈ 1 :: s.hs, ∀ z ∈ vsPT hs (vsPBar hs (gens gs)) y, g * z * g⁻¹ ∈ vsPT hs (vsPBar hs (gens gs)) y := by
  intro g hg z hz
  rcases List.mem_cons.1 hg with rfl | hg
  · simpa using hz
  · exact vsPT_conj hs h.hNn hy g hg z hz

theorem vsPT_self {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) {N : Subgroup _}
    (hyN : vsPRho hs y ∈ N) : y ∈ vsPT hs N y :=
  ⟨⟨1, one_mem _, by simp⟩, hyN⟩

/-- The keys of the orbit set, as a finset. -/
noncomputable def vsPKT (hs : VsQStOK s) (gs : List (Perm (Fin I.n))) (r : ℕ) (c0 y : Perm (Fin I.n)) :
    Finset (List ℕ) := by
  classical exact (Finset.univ.filter (· ∈ vsPT hs (vsPBar hs (gens gs)) y)).image (vsPKf s c0 r gs)

theorem VsPS4.KT_card [NeZero r] [Nontrivial (Fin (vsQD s) → ZMod I.p)] (h : VsPS4 hs as gs r c0)
    {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) : (vsPKT hs gs r c0 y).card ≤ vsQD s ^ 2 := by
  classical
  haveI : Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ := inferInstance
  unfold vsPKT
  convert (vsPT_card hs h.hc0 h.hP h.hgs h.gN h.key hy).trans h.indep

theorem vsPKT_mem {y z : Perm (Fin I.n)} (hz : z ∈ vsPT hs (vsPBar hs (gens gs)) y) :
    vsPKf s c0 r gs z ∈ vsPKT hs gs r c0 y := by
  classical
  unfold vsPKT
  exact Finset.mem_image.2 ⟨z, by simpa using hz, rfl⟩

/-- **Orbit lists stay in the orbit set** when `cap > D²`. -/
theorem VsPS4.orb_inv [NeZero r] [Nontrivial (Fin (vsQD s) → ZMod I.p)] (h : VsPS4 hs as gs r c0)
    {cap : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs)
    (hyN : vsPRho hs y ∈ vsPBar hs (gens gs)) (F : ℕ) :
    VsPOInv (vsPKf s c0 r gs) (vsPT hs (vsPBar hs (gens gs)) y)
      (vsPOrbit (vsPKf s c0 r gs) cap (1 :: s.hs) F y) :=
  (vsPOrbit_grow (K := vsPKT hs gs r c0 y) (fun z hz => vsPKT_mem hz)
    ((h.KT_card hy).trans_lt hcap) (h.T_conj hy) (vsPT_self hy hyN) F).1

/-- The orbit keys fit. -/
theorem VsPS4.orb_fit [NeZero r] [Nontrivial (Fin (vsQD s) → ZMod I.p)] (h : VsPS4 hs as gs r c0)
    {cap : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs)
    (hyN : vsPRho hs y ∈ vsPBar hs (gens gs)) (F : ℕ) :
    ∀ p ∈ vsPOrbit (vsPKf s c0 r gs) cap (1 :: s.hs) F y,
      (∀ a ∈ p.2, a < r) ∧ p.2.length = gs.length := by
  intro p hp
  obtain ⟨e, hT⟩ := (h.orb_inv hcap hy hyN F).1 p hp
  rw [e]
  exact vsPKey_fit hs h.hc0 h.hP h.hgs h.gN (vsPT_gens hs hy hT) hT.2

/-- **The key span of a list** is the span of the keys of the local units. -/
theorem VsPS4.kspan [NeZero r] (h : VsPS4 hs as gs r c0) {cs : List (Perm (Fin I.n))}
    (hcs : ∀ c ∈ cs, c ∈ gens s.hs ∧ vsPRho hs c ∈ vsPBar hs (gens gs)) :
    vsPKSpan r (vsPKf s c0 r gs) cs = Submodule.span (ZMod r)
      (vsPKV r (vsPRho hs c0) (gs.map (vsPRho hs)) '' (vsPRho hs '' {c | c ∈ cs})) := by
  unfold vsPKSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨vsPRho hs c, ⟨c, hc, rfl⟩,
      (vsF_vsPKey hs h.hc0 h.hP h.hgs h.gN (hcs c hc).1 (hcs c hc).2).symm⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (vsF_vsPKey hs h.hc0 h.hP h.hgs h.gN (hcs c hc).1 (hcs c hc).2).symm⟩

/-- The perms of an orbit list are in `⟨hs⟩` with local unit in `N̄₂`. -/
theorem VsPS4.orb_mem [NeZero r] [Nontrivial (Fin (vsQD s) → ZMod I.p)] (h : VsPS4 hs as gs r c0)
    {cap : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs)
    (hyN : vsPRho hs y ∈ vsPBar hs (gens gs)) (F : ℕ) :
    ∀ c ∈ (vsPOrbit (vsPKf s c0 r gs) cap (1 :: s.hs) F y).map Prod.fst,
      c ∈ gens s.hs ∧ vsPRho hs c ∈ vsPBar hs (gens gs) := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  have hT := ((h.orb_inv hcap hy hyN F).1 p hp).2
  exact ⟨vsPT_gens hs hy hT, hT.2⟩

/-- **The spin dimension is small**: `r ^ d ≤ D²`. -/
theorem VsPS4.pow_dim_le [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (h : VsPS4 hs as gs r c0) {cap : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)}
    (hy : y ∈ gens s.hs) (hyN : vsPRho hs y ∈ vsPBar hs (gens gs)) (F : ℕ) :
    r ^ (vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r y).length ≤
      vsQD s ^ 2 := by
  classical
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  set O := vsPOrbit (vsPKf s c0 r gs) cap (1 :: s.hs) F y
  have hO : ∀ p ∈ O, p.2 = vsPKf s c0 r gs p.1 ∧ (∀ a ∈ p.2, a < r) ∧ p.2.length = gs.length :=
    fun p hp => ⟨((h.orb_inv hcap hy hyN F).1 p hp).1, h.orb_fit hcap hy hyN F p hp⟩
  obtain ⟨-, -, hrank⟩ := vsPBasis_math (kf := vsPKf s c0 r gs) hO
  have e : (vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r y).length =
      finrank (ZMod r) (vsPKSpan r (vsPKf s c0 r gs) (O.map Prod.fst)) := hrank.symm
  rw [e, h.kspan (h.orb_mem hcap hy hyN F)]
  set κ := vsPKV r (vsPRho hs c0) (gs.map (vsPRho hs))
  set X := vsPRho hs '' {c | c ∈ O.map Prod.fst}
  set W := Submodule.span (ZMod r) (κ '' X)
  have hX : X ⊆ vsPBar hs (gens gs) := by
    rintro _ ⟨c, hc, rfl⟩; exact (h.orb_mem hcap hy hyN F c hc).2
  haveI : FiniteDimensional (ZMod r) W :=
    FiniteDimensional.span_of_finite _ (((List.finite_toSet _).image _).image _)
  haveI : Finite W := Module.finite_of_finite (ZMod r)
  haveI : Fintype W := Fintype.ofFinite W
  have hcard := Module.card_eq_pow_finrank (K := ZMod r) (V := W)
  rw [ZMod.card] at hcard
  rw [← hcard]
  have hsub : (W : Set (ℕ → ZMod r)) ⊆ κ '' (vsPBar hs (gens gs)) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := h.key.span hX v hv
    exact ⟨x, (Subgroup.closure_le _).2 hX hx, rfl⟩
  have hfin : (κ '' (vsPBar hs (gens gs) : Set _)).Finite := Set.toFinite _
  calc Fintype.card W = (W : Set (ℕ → ZMod r)).ncard := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]; rfl
    _ ≤ (κ '' (vsPBar hs (gens gs) : Set _)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ _ := h.key.ncard_le
    _ ≤ _ := h.indep

/-- The perms of `⟨hs⟩` with local unit in `N`. -/
noncomputable def vsPYs (hs : VsQStOK s) (N : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) :
    Subgroup (Perm (Fin I.n)) :=
  (N.comap (vsQRho hs)).map (gens s.hs).subtype

theorem vsPYs_iff {N : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ} {g : Perm (Fin I.n)} :
    g ∈ vsPYs hs N ↔ g ∈ gens s.hs ∧ vsPRho hs g ∈ N := by
  unfold vsPYs
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨g', hg'⟩, h1, rfl⟩
    exact ⟨hg', by show vsPRho hs g' ∈ N; rw [vsPRho_of hs hg']; exact h1⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, by rw [vsPRho_of hs hg] at h1; exact h1, rfl⟩

/-- **The descent set**: what a descent round needs holds on `vsPYs N̄₂`, and the listed words
stay in it. -/
theorem VsPS4.desc_ok [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (h : VsPS4 hs as gs r c0) {cap N : ℕ} (hcap : vsQD s ^ 2 < cap) (hDN : vsQD s ^ 2 ≤ N) (F : ℕ) :
    ∀ y ∈ (vsPYs hs (vsPBar hs (gens gs)) : Set (Perm (Fin I.n))),
      VsPDOK I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r N y ∧
      ∀ z ∈ vsPEnum r (vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r y),
        z ∈ (vsPYs hs (vsPBar hs (gens gs)) : Set (Perm (Fin I.n))) := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  intro y hy
  obtain ⟨hyg, hyN⟩ := vsPYs_iff.1 hy
  refine ⟨⟨hs.prob.le hyg, h.orb_fit hcap hyg hyN F, (h.pow_dim_le hcap hyg hyN F).trans hDN⟩,
    fun z hz => ?_⟩
  have hB : ∀ b ∈ vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r y,
      b ∈ vsPYs hs (vsPBar hs (gens gs)) := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := vsPBasis_sub _ b hb
    exact vsPYs_iff.2 (h.orb_mem hcap hyg hyN F p.1 (List.mem_map.2 ⟨p, hp, rfl⟩))
  exact (Subgroup.closure_le _).2 (fun b hb => hB b hb) (vsPEnum_mem _ z hz)

/-- A round keeps `y` outside `L`. -/
theorem vsPDsStepF_ib (ws' cs : List (List ℕ)) (rows : List VsRow) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (cap : ℕ) (hs1 : List (Perm (Fin I.n))) (F r : ℕ)
    {y : Perm (Fin I.n)} (hy : vsPInLB I ws' cs rows y = false) :
    vsPInLB I ws' cs rows (vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y) = false := by
  set E := vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)
  set qq := vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length
  have hval : vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y =
      if h : E.findIdx qq < E.length then E[E.findIdx qq] else y := rfl
  rw [hval]
  split_ifs with hj
  · have := List.findIdx_getElem (w := hj)
    unfold qq vsPDQ at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1
  · exact hy

theorem vsPDsStepF_iter_ib (ws' cs : List (List ℕ)) (rows : List VsRow) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (cap : ℕ) (hs1 : List (Perm (Fin I.n))) (F r : ℕ)
    {y : Perm (Fin I.n)} (hy : vsPInLB I ws' cs rows y = false) :
    ∀ k, vsPInLB I ws' cs rows ((vsPDsStepF I ws' cs rows Zp gs cap hs1 F r)^[k] y) = false := by
  intro k
  induction k with
  | zero => exact hy
  | succ k ih => rw [Function.iterate_succ_apply']; exact vsPDsStepF_ib ws' cs rows Zp gs cap hs1 F r ih

end GI.Proved
