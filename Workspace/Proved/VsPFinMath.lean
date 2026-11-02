import Workspace.Proved.VsPS4Math
import Workspace.Proved.VsPHardMath

/-!
# The final stage, in local units

For `y ∈ vsPYs N̄₂`, the orbit list after `F ≥ D²` passes with `cap > D²` gives an orbit set
`vsPOb y` of `ρ y` (`VsPS4.orbHyp`), whose key span has dimension `|vsPDim y|`
(`VsPS4.finrank_eq`), and `⟨vsPOb y⟩ ⊔ S = vsPBar ⟨B⟩ ⊔ S` for the kept basis `B`
(`VsPS4.sup_eq`).
-/

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv Module
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]
variable {hs : VsQStOK s} {as gs : List (Perm (Fin I.n))} {r : ℕ} {c0 : Perm (Fin I.n)}

/-- The orbit list of `y`. -/
noncomputable abbrev vsPOL (s : VsQSt I) (gs : List (Perm (Fin I.n))) (r : ℕ) (c0 : Perm (Fin I.n))
    (cap F : ℕ) (y : Perm (Fin I.n)) : List (Perm (Fin I.n) × List ℕ) :=
  vsPOrbit (vsPKf s c0 r gs) cap (1 :: s.hs) F y

/-- The orbit set of `ρ y`. -/
noncomputable def vsPOb (hs : VsQStOK s) (gs : List (Perm (Fin I.n))) (r : ℕ) (c0 : Perm (Fin I.n))
    (cap F : ℕ) (y : Perm (Fin I.n)) : Set (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ :=
  vsPRho hs '' {z | ∃ p ∈ vsPOL s gs r c0 cap F y, p.1 = z}

/-- The key map. -/
noncomputable abbrev vsPκ (hs : VsQStOK s) (gs : List (Perm (Fin I.n))) (r : ℕ) (c0 : Perm (Fin I.n)) :
    (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ → ℕ → ZMod r :=
  vsPKV r (vsPRho hs c0) (gs.map (vsPRho hs))

theorem vsPOb_eq (cap F : ℕ) (y : Perm (Fin I.n)) :
    vsPOb hs gs r c0 cap F y = vsPRho hs '' {c | c ∈ (vsPOL s gs r c0 cap F y).map Prod.fst} := by
  unfold vsPOb; congr 1; ext z; simp

theorem vsPOb_finite (cap F : ℕ) (y : Perm (Fin I.n)) : (vsPOb hs gs r c0 cap F y).Finite := by
  rw [vsPOb_eq]; exact (List.finite_toSet _).image _

/-- **The orbit set hypotheses.** -/
theorem VsPS4.orbHyp [NeZero r] [Nontrivial (Fin (vsQD s) → ZMod I.p)] (h : VsPS4 hs as gs r c0)
    {cap F : ℕ} (hcap : vsQD s ^ 2 < cap) (hF : vsQD s ^ 2 ≤ F) {y : Perm (Fin I.n)}
    (hy : y ∈ vsPYs hs (vsPBar hs (gens gs))) :
    VsPOrbHyp (vsPHg hs) (vsPκ hs gs r c0) (vsPRho hs y) (vsPOb hs gs r c0 cap F y) := by
  obtain ⟨hyg, hyN⟩ := vsPYs_iff.1 hy
  have hK := h.KT_card hyg
  obtain ⟨hinv, hmem, hcl⟩ := vsPOrbit_closed (K := vsPKT hs gs r c0 y) (fun z hz => vsPKT_mem hz)
    (hK.trans_lt hcap) (h.T_conj hyg) (vsPT_self hyg hyN) (F := F) (hK.trans hF)
  exact vsP_orbHyp hs h.hc0 h.hP h.hgs h.gN h.hNn hyg (fun p hp => hinv.1 p hp) hmem
    fun p hp g hg => hcl p hp g (List.mem_cons_of_mem _ hg)

/-- **The dimension** of the key span of the orbit set. -/
theorem VsPS4.finrank_eq [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (h : VsPS4 hs as gs r c0) {cap F : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)}
    (hy : y ∈ vsPYs hs (vsPBar hs (gens gs))) :
    finrank (ZMod r) (Submodule.span (ZMod r) (vsPκ hs gs r c0 '' vsPOb hs gs r c0 cap F y)) =
      (vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r y).length := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  obtain ⟨hyg, hyN⟩ := vsPYs_iff.1 hy
  have hO : ∀ p ∈ vsPOL s gs r c0 cap F y, p.2 = vsPKf s c0 r gs p.1 ∧ (∀ a ∈ p.2, a < r) ∧
      p.2.length = gs.length :=
    fun p hp => ⟨((h.orb_inv hcap hyg hyN F).1 p hp).1, h.orb_fit hcap hyg hyN F p hp⟩
  obtain ⟨-, -, hrank⟩ := vsPBasis_math (kf := vsPKf s c0 r gs) hO
  rw [vsPOb_eq, ← h.kspan (h.orb_mem hcap hyg hyN F)]
  exact hrank

/-- The kept basis lies in `vsPYs N̄₂`. -/
theorem VsPS4.basis_mem [NeZero r] [Nontrivial (Fin (vsQD s) → ZMod I.p)] (h : VsPS4 hs as gs r c0)
    {cap F : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)}
    (hy : y ∈ vsPYs hs (vsPBar hs (gens gs))) :
    ∀ b ∈ vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r y,
      b ∈ gens s.hs ∧ vsPRho hs b ∈ vsPBar hs (gens gs) := by
  obtain ⟨hyg, hyN⟩ := vsPYs_iff.1 hy
  intro b hb
  obtain ⟨p, hp, rfl⟩ := vsPBasis_sub _ b hb
  exact h.orb_mem hcap hyg hyN F p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)

/-- **The key span of the basis** equals that of the orbit set. -/
theorem VsPS4.span_basis [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (h : VsPS4 hs as gs r c0) {cap F : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)}
    (hy : y ∈ vsPYs hs (vsPBar hs (gens gs))) :
    Submodule.span (ZMod r) (vsPκ hs gs r c0 '' (vsPRho hs '' {b | b ∈
      vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r y})) =
    Submodule.span (ZMod r) (vsPκ hs gs r c0 '' vsPOb hs gs r c0 cap F y) := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  obtain ⟨hyg, hyN⟩ := vsPYs_iff.1 hy
  have hO : ∀ p ∈ vsPOL s gs r c0 cap F y, p.2 = vsPKf s c0 r gs p.1 ∧ (∀ a ∈ p.2, a < r) ∧
      p.2.length = gs.length :=
    fun p hp => ⟨((h.orb_inv hcap hyg hyN F).1 p hp).1, h.orb_fit hcap hyg hyN F p hp⟩
  obtain ⟨-, hsp, -⟩ := vsPBasis_math (kf := vsPKf s c0 r gs) hO
  rw [vsPOb_eq, ← h.kspan (h.orb_mem hcap hyg hyN F), ← h.kspan (h.basis_mem hcap hy)]
  exact hsp

/-- **The same subgroup modulo `S`.** -/
theorem VsPS4.sup_eq [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (h : VsPS4 hs as gs r c0) {cap F : ℕ} (hcap : vsQD s ^ 2 < cap) {y : Perm (Fin I.n)}
    (hy : y ∈ vsPYs hs (vsPBar hs (gens gs))) :
    Subgroup.closure (vsPOb hs gs r c0 cap F y) ⊔ vsMScal (vsPBar hs (gens as)) =
      vsPBar hs (gens (vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs)
        F r y)) ⊔ vsMScal (vsPBar hs (gens as)) := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  obtain ⟨hyg, hyN⟩ := vsPYs_iff.1 hy
  have hB := h.basis_mem hcap hy (F := F)
  rw [vsPBar_gens hs fun b hb => (hB b hb).1]
  have hOb : vsPOb hs gs r c0 cap F y ⊆ vsPBar hs (gens gs) := by
    rw [vsPOb_eq]; rintro _ ⟨c, hc, rfl⟩; exact (h.orb_mem hcap hyg hyN F c hc).2
  have hBb : vsPRho hs '' {b | b ∈ vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap
      (1 :: s.hs) F r y} ⊆ vsPBar hs (gens gs) := by
    rintro _ ⟨b, hb, rfl⟩; exact (hB b hb).2
  have he := h.span_basis hcap hy (F := F)
  exact le_antisymm (vsP_sup_le_of_span h.key hOb hBb he.ge)
    (vsP_sup_le_of_span h.key hBb hOb he.le)

theorem vsP_gens_cons_one {n : ℕ} (B : List (Perm (Fin n))) : gens (1 :: B) = gens B := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun x hx => ?_
    rcases List.mem_cons.1 hx with rfl | hx
    · exact one_mem _
    · exact Subgroup.subset_closure hx
  · exact Subgroup.closure_mono fun x hx => List.mem_cons_of_mem _ hx

/-- The local units of perms commute iff their stored local matrices do. -/
theorem vsP_comm_iff_loc {g h : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hh : h ∈ gens s.hs) :
    vsPRho hs g * vsPRho hs h = vsPRho hs h * vsPRho hs g ↔
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g) := by
  rw [← vsPRho_mul hs hg hh, ← vsPRho_mul hs hh hg, vsPRho_of hs (mul_mem hg hh),
    vsPRho_of hs (mul_mem hh hg), vsQRho_ext hs, vsPLocL_eq_iff hs]

/-- **The hand-off is a hard case.** -/
theorem VsPS4.hard [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (h : VsPS4 hs as gs r c0) (hsolv : IsSolvable (vsPBar hs (gens s.hs)))
    (hAN : VsTAbNormal (vsPBar hs (gens s.hs)) (vsPBar hs (gens as)))
    {rows : List VsRow}
    (hib : ∀ z ∈ gens s.hs, vsPInLB I s.ws' (vsQCs s) rows z = true ↔
      vsPRho hs z ∈ vsMScal (vsPBar hs (gens as)))
    {cap F : ℕ} (hcap : vsQD s ^ 2 < cap) (hF : vsQD s ^ 2 ≤ F) {x0 : Perm (Fin I.n)}
    (hx0 : x0 ∈ vsPYs hs (vsPBar hs (gens gs)))
    (hfix : vsPDsStepF I s.ws' (vsQCs s) rows (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r x0
      = x0)
    (hiso : vsPIso I s.ws' (vsQCs s)
      (vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r x0) = false) :
    VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as))
      (vsPBar hs (gens (1 :: vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap
        (1 :: s.hs) F r x0)) ⊔ vsMScal (vsPBar hs (gens as))) r := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  haveI : Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ := inferInstance
  set B := vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r x0
  set S := vsMScal (vsPBar hs (gens as))
  set κ := vsPκ hs gs r c0
  set Ob := vsPOb hs gs r c0 cap F x0
  obtain ⟨hx0g, hx0N⟩ := vsPYs_iff.1 hx0
  have hB := h.basis_mem hcap hx0 (F := F)
  have hBOb : vsPRho hs '' {b | b ∈ B} ⊆ Ob := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨p, hp, rfl⟩ := vsPBasis_sub _ b hb
    exact ⟨p.1, ⟨p, hp, rfl⟩, rfl⟩
  have htop : vsPBar hs (gens s.hs) = Subgroup.closure (vsPHg hs) := vsPBar_top_eq hs
  rw [vsP_gens_cons_one, ← h.sup_eq hcap hx0, htop]
  rw [htop] at hsolv hAN
  have hOk := h.orbHyp hcap hF hx0
  refine vsP_hard hsolv hAN h.hdom h.hNC h.hNn h.hc h.hpow h.key hOk (vsPOb_finite cap F x0) hx0N
    (Wd := vsPRho hs '' {z | z ∈ vsPEnum r B}) ?_ ?_ ?_ ?_
  · -- the words lie in `⟨Ob⟩`
    rintro _ ⟨z, hz, rfl⟩
    have hzB := vsPEnum_mem B z hz
    have hBg : gens B ≤ gens s.hs := (Subgroup.closure_le _).2 fun b hb => (hB b hb).1
    have := vsPRho_mem_vsPBar hs (K := gens B) hzB (hBg hzB)
    rw [vsPBar_gens hs fun b hb => (hB b hb).1] at this
    exact Subgroup.closure_mono hBOb this
  · -- the words cover the key span
    intro v hv
    rw [← h.span_basis hcap hx0] at hv
    obtain ⟨w, hw, e⟩ := vsPEnum_cover h.key (f := vsPRho hs) (P := gens s.hs)
      (fun a ha b hb => vsPRho_mul hs ha hb) B (fun b hb => (hB b hb).1) (fun b hb => (hB b hb).2) v hv
    exact ⟨vsPRho hs w, ⟨w, hw, rfl⟩, e⟩
  · -- the descent test
    rintro _ ⟨z, hz, rfl⟩ hzS
    have hzY : z ∈ vsPYs hs (vsPBar hs (gens gs)) :=
      (h.desc_ok hcap (le_refl _) F x0 hx0).2 z hz
    have hzg := (vsPYs_iff.1 hzY).1
    have hib' : vsPInLB I s.ws' (vsQCs s) rows z = false := by
      cases e : vsPInLB I s.ws' (vsQCs s) rows z
      · rfl
      · exact absurd ((hib z hzg).1 e) hzS
    refine ⟨vsPOb hs gs r c0 cap F z, h.orbHyp hcap hF hzY, ?_⟩
    rw [h.finrank_eq hcap hx0, h.finrank_eq hcap hzY]
    exact vsPDsStepF_fix hfix z hz hib'
  · -- not abelian
    have hn : ¬ ∀ g ∈ 1 :: B, ∀ k ∈ 1 :: B,
        vsPLocL I s.ws' (vsQCs s) (g * k) = vsPLocL I s.ws' (vsQCs s) (k * g) := by
      intro hall; unfold vsPIso at hiso; simp only [decide_eq_false_iff_not] at hiso; exact hiso hall
    push Not at hn
    obtain ⟨g, hg, k, hk, hne⟩ := hn
    have hmem : ∀ x ∈ 1 :: B, x ∈ gens s.hs ∧ vsPRho hs x ∈ Subgroup.closure Ob := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨one_mem _, by rw [vsPRho_one]; exact one_mem _⟩
      · exact ⟨(hB x hx).1, Subgroup.subset_closure (hBOb ⟨x, hx, rfl⟩)⟩
    refine ⟨vsPRho hs g, (hmem g hg).2, vsPRho hs k, (hmem k hk).2, fun e => hne ?_⟩
    exact (vsP_comm_iff_loc (hmem g hg).1 (hmem k hk).1).1 e

/-- The sup of two commuting abelian subgroups is abelian. -/
theorem vsP_sup_abel {G : Type*} [Group G] {K T : Subgroup G}
    (hK : K ≤ Subgroup.centralizer (K : Set G)) (hT : T ≤ Subgroup.centralizer (T : Set G))
    (hKT : T ≤ Subgroup.centralizer (K : Set G)) :
    K ⊔ T ≤ Subgroup.centralizer ((K ⊔ T : Subgroup G) : Set G) := by
  have h1 : K ⊔ T ≤ Subgroup.centralizer (K : Set G) := sup_le hK hKT
  have h2 : K ⊔ T ≤ Subgroup.centralizer (T : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.1 hKT) hT
  exact sup_le (Subgroup.le_centralizer_iff.1 h1) (Subgroup.le_centralizer_iff.1 h2)

/-- **The isotropic case grows `A`.** -/
theorem VsPS4.iso_grow [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))} (hH : VsPHyp hs as Lb ccs)
    (h : VsPS4 hs as gs r c0) {cap F : ℕ} (hcap : vsQD s ^ 2 < cap) (hF : vsQD s ^ 2 ≤ F)
    {x0 : Perm (Fin I.n)} (hx0 : x0 ∈ vsPYs hs (vsPBar hs (gens gs)))
    (hx0S : vsPRho hs x0 ∉ vsMScal (vsPBar hs (gens as)))
    (hiso : vsPIso I s.ws' (vsQCs s)
      (vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r x0) = true)
    {as' : List (Perm (Fin I.n))} (hl : as'.length ≤ I.n ^ 2)
    (he : gens as' = Subgroup.closure {x | ∃ g ∈ gens s.hs ⊔ gens (as ++ [x0]), ∃ y ∈ as ++ [x0],
      x = g * y * g⁻¹}) :
    VsPGrowOut hs as as' := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  haveI : Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ := inferInstance
  set B := vsPDim I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap (1 :: s.hs) F r x0
  set S := vsMScal (vsPBar hs (gens as))
  obtain ⟨hx0g, hx0N⟩ := vsPYs_iff.1 hx0
  have hB := h.basis_mem hcap hx0 (F := F)
  have hBg : gens B ≤ gens s.hs := (Subgroup.closure_le _).2 fun b hb => (hB b hb).1
  have hyH : gens [x0] ≤ gens s.hs := (Subgroup.closure_le _).2 fun y hy => by
    simp at hy; rw [hy]; exact hx0g
  set Nx := vsPNcl (gens s.hs) [x0]
  have hNx : Nx ≤ gens s.hs :=
    vsPNcl_le hyH (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) fun y hy => hyH
      (Subgroup.subset_closure hy)
  -- the bound subgroup `Ȳ = ⟨B⟩ ⊔ S`
  have hSn : ∀ g ∈ vsPHg hs, ∀ t ∈ S, g * t * g⁻¹ ∈ S := fun g hg t ht =>
    vsM_scal_norm hH.abNormal g (by rw [vsPBar_top_eq hs]; exact Subgroup.subset_closure hg) t ht
  have hspin := vsP_spin_eq h.key (h.orbHyp hcap hF hx0) h.hNn hSn hx0N
  rw [h.sup_eq hcap hx0] at hspin
  have hbarN : vsPBar hs Nx ≤ vsPBar hs (gens B) ⊔ S := by
    rw [← hspin]
    have hX : {x | ∃ g ∈ gens s.hs ⊔ gens [x0], ∃ y ∈ [x0], x = g * y * g⁻¹} ⊆ (gens s.hs : Set _) :=
      fun x hx => hNx (Subgroup.subset_closure hx)
    show vsPBar hs (Subgroup.closure _) ≤ _
    rw [vsPBar_closure hs hX]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, ⟨g, hg, y, hy, rfl⟩, rfl⟩
    simp only [List.mem_singleton] at hy
    rw [hy]
    rw [sup_eq_left.2 hyH] at hg
    refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨vsPRho hs g, ?_, ?_⟩)
    · rw [← vsPBar_top_eq hs]; exact vsPRho_mem_vsPBar hs hg hg
    · rw [vsPRho_conj hs hx0g hg]
  have hBab : vsPBar hs (gens B) ≤ Subgroup.centralizer (vsPBar hs (gens B) : Set _) := by
    refine vsP_bar_abel hs hBg fun g hg k hk => ?_
    have hall : ∀ g ∈ 1 :: B, ∀ k ∈ 1 :: B,
        vsPLocL I s.ws' (vsQCs s) (g * k) = vsPLocL I s.ws' (vsQCs s) (k * g) := by
      unfold vsPIso at hiso; simpa using hiso
    exact (vsPLocL_eq_iff hs _ _).1 (hall g (List.mem_cons_of_mem _ hg) k (List.mem_cons_of_mem _ hk))
  have hBN : vsPBar hs (gens B) ≤ vsPBar hs (gens gs) := by
    rw [vsPBar_gens hs fun b hb => (hB b hb).1]
    exact (Subgroup.closure_le _).2 (by rintro _ ⟨b, hb, rfl⟩; exact (hB b hb).2)
  have hSab : S ≤ Subgroup.centralizer (S : Set _) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => vsM_scal_comm h.hAc hy hx
  have hSB : S ≤ Subgroup.centralizer (vsPBar hs (gens B) : Set _) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => vsM_comm_scal (h.hNC (hBN hy)) hx
  have hYab := vsP_sup_abel hBab hSab hSB
  have hYC : vsPBar hs (gens B) ⊔ S ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _) :=
    sup_le (hBN.trans h.hNC) (vsM_scal_le_centralizer h.hAc)
  refine vsP_grow_out hH hNx (vsPNcl_normd hyH) (xs := [x0]) (fun y hy => by
      simp at hy; rw [hy]; exact vsPNcl_mem (by simp)) ?_ (hbarN.trans hYC)
    (by simp : x0 ∈ [x0]) hx0S hl he
  intro u hu
  exact Subgroup.mem_centralizer_iff.2 fun v hv =>
    (Subgroup.mem_centralizer_iff.1 (hYab (hbarN hu)) v (hbarN hv))

end GI.Proved
