module

public import Workspace.Proved.VsPFinMath
public import Workspace.Impl.VsPRad
public import Workspace.Impl.VsPCtxP

@[expose] public section

/-!
# Setting up the pairing on `N₂`

* `vsP_N2_pair`: from the facts for `N₂ = ⟨x₂⟩^H` and a pair of generators whose local matrices
  do not commute, the commutator `ζ = ρ ⁅a, b⁆` gives the pairing (`VsPPairHyp`).
* `vsP_rad_of_prog`: if the radical stage finds no relation word outside `L`, the radical lies
  in `S`.
* `vsP_S4_of`: all of this gives `VsPS4`.
-/

set_option backward.isDefEq.respectTransparency false

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv Module
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]
variable {hs : VsQStOK s} {as gs : List (Perm (Fin I.n))} {r : ℕ} {c0 : Perm (Fin I.n)}

/-- The facts on `N̄₂` used below. -/
structure VsPN2 (hs : VsQStOK s) (as gs : List (Perm (Fin I.n))) (r : ℕ) : Prop where
  hgs : ∀ g ∈ gs, g ∈ gens s.hs
  hNC : vsPBar hs (gens gs) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _)
  hNn : ∀ h ∈ vsPHg hs, ∀ x ∈ vsPBar hs (gens gs), h * x * h⁻¹ ∈ vsPBar hs (gens gs)
  hc : ∀ x ∈ vsPBar hs (gens gs), ∀ y ∈ vsPBar hs (gens gs), ⁅x, y⁆ ∈ vsMScal (vsPBar hs (gens as))
  hpow : ∀ x ∈ vsPBar hs (gens gs), x ^ r ∈ vsMScal (vsPBar hs (gens as))

/-- **The facts on `N̄₂`** from those on `N₀`. -/
theorem vsP_N2_of [Nontrivial (Fin (vsQD s) → ZMod I.p)] {Lb : List (List (List ℕ))}
    {ccs : List (Perm (Fin I.n))} (hH : VsPHyp hs as Lb ccs)
    {N0 : Subgroup (Perm (Fin I.n))} (hN0 : N0 ≤ gens s.hs) (hN0n : VsPNormd (gens s.hs) N0)
    (hN0C : vsPBar hs N0 ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _))
    (hN0c : ∀ x ∈ N0, ∀ y ∈ N0, vsPRho hs ⁅x, y⁆ ∈ vsMScal (vsPBar hs (gens as)))
    {x2 : Perm (Fin I.n)} (hx2 : x2 ∈ N0)
    (hx2r : vsPRho hs (x2 ^ r) ∈ vsMScal (vsPBar hs (gens as)))
    (hgs2 : gens gs = vsPNcl (gens s.hs) [x2]) : VsPN2 hs as gs r ∧ gens gs ≤ N0 := by
  obtain ⟨hle, hC, hc, hp, hn⟩ := vsP_N2_facts hs hH.abNormal hN0 hN0n hN0C hN0c hx2 hx2r
  rw [← hgs2] at hle hC hc hp hn
  exact ⟨⟨fun g hg => hN0 (hle (Subgroup.subset_closure hg)), hC, hn, hc, hp⟩, hle⟩

/-- **The pairing** from a non-commuting pair of generators. -/
theorem vsP_N2_pair [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))} (hH : VsPHyp hs as Lb ccs)
    (h2 : VsPN2 hs as gs r) {a b : Perm (Fin I.n)} (ha : a ∈ 1 :: gs) (hb : b ∈ 1 :: gs)
    (hne : vsPLocL I s.ws' (vsQCs s) (a * b) ≠ vsPLocL I s.ws' (vsQCs s) (b * a)) :
    ⁅a, b⁆ ∈ gens s.hs ∧ VsPPairHyp (vsPBar hs (gens gs)) r (vsPRho hs ⁅a, b⁆) := by
  have hmem : ∀ x ∈ 1 :: gs, x ∈ gens s.hs ∧ vsPRho hs x ∈ vsPBar hs (gens gs) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨one_mem _, by rw [vsPRho_one]; exact one_mem _⟩
    · exact ⟨h2.hgs x hx, vsPRho_mem_vsPBar hs (Subgroup.subset_closure hx) (h2.hgs x hx)⟩
  obtain ⟨hag, haN⟩ := hmem a ha
  obtain ⟨hbg, hbN⟩ := hmem b hb
  have hcg : ⁅a, b⁆ ∈ gens s.hs := by
    rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem hag hbg) (inv_mem hag)) (inv_mem hbg)
  refine ⟨hcg, vsP_pairHyp (p := I.p) (V := Fin (vsQD s) → ZMod I.p)
    (fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hH.habl hy) x hx) hH.hdom hr.out h2.hNC h2.hc
    h2.hpow ⟨_, haN, _, hbN, vsPRho_comm hs hag hbg⟩ fun e => hne ?_⟩
  rw [vsPRho_comm hs hag hbg, commutatorElement_eq_one_iff_mul_comm] at e
  exact (vsP_comm_iff_loc hag hbg).1 e

/-- The test `vsPInLB` on the rows of `Lb` is membership in `S`. -/
theorem VsPHyp.ib {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) :
    ∀ z ∈ gens s.hs, vsPInLB I s.ws' (vsQCs s) (vsPRows I.p Lb) z = true ↔
      vsPRho hs z ∈ vsMScal (vsPBar hs (gens as)) := by
  intro z hz
  rw [vsPRho_of hs hz]
  exact vsPInLB_iff hs hH.has hH.hLb hH.hspan hz

/-- **No relation word outside `L`** ⇒ the radical lies in `S`. -/
theorem vsP_rad_of_prog [hr : Fact r.Prime] (h2 : VsPN2 hs as gs r) (hc0 : c0 ∈ gens s.hs)
    (hP : VsPPairHyp (vsPBar hs (gens gs)) r (vsPRho hs c0)) {rows : List VsRow}
    (hib : ∀ z ∈ gens s.hs, vsPInLB I s.ws' (vsQCs s) rows z = true ↔
      vsPRho hs z ∈ vsMScal (vsPBar hs (gens as)))
    (hall : ∀ t ∈ vsWKer r (vsPGram I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs),
      vsPInLB I s.ws' (vsQCs s) rows (vsPW gs t) = true) :
    ∀ x ∈ vsPBar hs (gens gs), (∀ g ∈ gs.map (vsPRho hs), x * g = g * x) →
      x ∈ vsMScal (vsPBar hs (gens as)) := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  have hgN : ∀ g ∈ gs, vsPRho hs g ∈ vsPBar hs (gens gs) :=
    fun g hg => vsPRho_mem_vsPBar hs (Subgroup.subset_closure hg) (h2.hgs g hg)
  have hQ : VsPQuotHyp (vsPBar hs (gens gs)) (vsMScal (vsPBar hs (gens as))) r :=
    ⟨fun t ht x hx => (vsM_comm_scal (h2.hNC hx) ht).symm, h2.hc, h2.hpow⟩
  set us := vsPGram I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs
  have hlen : us.length = (gs.map (vsPRho hs)).length := by simp [us, vsPGram]
  have hfit : VsWFit r (gs.map (vsPRho hs)).length us := by
    intro u hu
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hu
    rw [List.length_map]
    exact vsPKey_fit hs hc0 hP h2.hgs hgN (h2.hgs g hg) (hgN g hg)
  refine vsP_radical_prog hQ hP (vsPBar_gens' h2.hgs) hlen hfit (fun i j => ?_) fun t ht => ?_
  · have hi : (i : ℕ) < gs.length := by simpa using i.2
    have e : us.getD i [] = vsPKey I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs gs[(i : ℕ)] := by
      simp [us, vsPGram, List.getD_eq_getElem?_getD, hi]
    rw [e, vsF_vsPKey hs hc0 hP h2.hgs hgN (h2.hgs _ (List.getElem_mem hi)) (hgN _ (List.getElem_mem hi))]
    have hj : (j : ℕ) < gs.length := by simpa using j.2
    simp [vsPKV, List.getElem_map, hj]
  · have hW : vsPW gs t ∈ gens s.hs := vsPW_mem h2.hgs t
    rw [← vsPRho_W hs h2.hgs]
    exact (hib _ hW).1 (hall t ht)

/-- A relation among the rows combines them to zero. -/
theorem vsP_ker_comb {r : ℕ} [hr : Fact r.Prime] {d : ℕ} {us : List (List ℕ)} (hfit : VsWFit r d us)
    {t : List ℕ} (ht : t ∈ vsWKer r us) :
    (List.zipWith (fun (a : ℕ) u => (a : ZMod r) • vsF r u) t us).sum = 0 := by
  have htf := vsWKer_fit hr.out.one_lt hfit t ht
  have hsp : vsWV r us.length t ∈ vsWSp r us.length (vsWKer r us) :=
    Submodule.subset_span ⟨t, ht, rfl⟩
  rw [vsWKer_span hr.out hfit, LinearMap.mem_ker, vsWComb_apply] at hsp
  have hE := congrArg (vsWE r d) hsp
  rw [map_sum, map_zero] at hE
  rw [← hE, vsP_zipWith_ofFn _ t us (by rw [htf.2]), List.sum_ofFn]
  refine Fintype.sum_equiv (finCongr htf.2) _ _ fun i => ?_
  simp only [map_smul, finCongr_apply, Fin.getElem_fin, Fin.val_cast]
  have hu : us[(i : ℕ)]'(by rw [← htf.2]; exact i.2) ∈ us := List.getElem_mem _
  have e1 : vsWE r d (vsWV r d us[(i : ℕ)]) = vsF r us[(i : ℕ)] :=
    vsWE_vsWR (vsF_mem_vsWSupp (hfit _ hu).2.le)
  rw [e1]
  congr 1
  simp [vsF_apply, List.getD_eq_getElem?_getD]

/-- The key of a word is the combination of the keys. -/
theorem vsP_key_W {G M : Type*} [Group G] [AddCommGroup M] [Module (ZMod r) M] {N S : Subgroup G}
    {κ : G → M} (hk : VsPKeyHyp N S κ) {xs : List G} (hxN : ∀ x ∈ xs, x ∈ N) :
    ∀ t : List ℕ, t.length = xs.length →
      κ (vsPW xs t) = (List.zipWith (fun (a : ℕ) x => (a : ZMod r) • κ x) t xs).sum := by
  induction xs with
  | nil => intro t ht; simp at ht; subst ht; simp [vsPW, hk.one]
  | cons x xs ih =>
    intro t ht
    cases t with
    | nil => simp at ht
    | cons a t =>
      have hx := hxN x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ N := fun y hy => hxN y (by simp [hy])
      rw [vsPW_cons, hk.mul _ (pow_mem hx a) _ (vsPW_mem hxs t), hk.npow hx,
        ih hxs t (by simpa using ht), ← Nat.cast_smul_eq_nsmul (ZMod r)]
      simp

theorem vsP_zip_eval {α G : Type*} (kf : α → List ℕ) (ρ : α → G) (dl : G → ZMod r) (j : ℕ)
    {gs : List α} (hgs : ∀ g ∈ gs, vsF r (kf g) j = dl (ρ g)) :
    ∀ t : List ℕ, (List.zipWith (fun (a : ℕ) u => (a : ZMod r) • vsF r u) t (gs.map kf)).sum j =
      (List.zipWith (fun g (a : ℕ) => (a : ZMod r) * dl g) (gs.map ρ) t).sum := by
  induction gs with
  | nil => intro t; simp
  | cons g gs ih =>
    intro t
    cases t with
    | nil => simp
    | cons a t =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [hgs g (by simp), ih (fun x hx => hgs x (by simp [hx])) t]

/-- **A relation word outside `L` grows `A`.** -/
theorem vsP_rad_grow [hr : Fact r.Prime] [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))} (hH : VsPHyp hs as Lb ccs)
    (h2 : VsPN2 hs as gs r) (hc0 : c0 ∈ gens s.hs)
    (hP : VsPPairHyp (vsPBar hs (gens gs)) r (vsPRho hs c0)) {rows : List VsRow}
    (hib : ∀ z ∈ gens s.hs, vsPInLB I s.ws' (vsQCs s) rows z = true ↔
      vsPRho hs z ∈ vsMScal (vsPBar hs (gens as)))
    {t : List ℕ} (ht : t ∈ vsWKer r (vsPGram I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs))
    (hz : vsPInLB I s.ws' (vsQCs s) rows (vsPW gs t) = false)
    {as' : List (Perm (Fin I.n))} (hl : as'.length ≤ I.n ^ 2)
    (he : gens as' = Subgroup.closure {x | ∃ g ∈ gens s.hs ⊔ gens (as ++ [vsPW gs t]),
      ∃ y ∈ as ++ [vsPW gs t], x = g * y * g⁻¹}) :
    VsPGrowOut hs as as' := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  set N := vsPBar hs (gens gs)
  set S := vsMScal (vsPBar hs (gens as))
  set M := N ⊓ Subgroup.centralizer (N : Set (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
  set us := vsPGram I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs
  set z := vsPW gs t
  have hgN : ∀ g ∈ gs, vsPRho hs g ∈ N :=
    fun g hg => vsPRho_mem_vsPBar hs (Subgroup.subset_closure hg) (h2.hgs g hg)
  have hfit : VsWFit r gs.length us := by
    intro u hu
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hu
    exact vsPKey_fit hs hc0 hP h2.hgs hgN (h2.hgs g hg) (hgN g hg)
  have htl : t.length = gs.length := by
    rw [(vsWKer_fit hr.out.one_lt hfit t ht).2]; simp [us, vsPGram]
  have hzg : z ∈ gens s.hs := vsPW_mem h2.hgs t
  have hzW : vsPRho hs z = vsPW (gs.map (vsPRho hs)) t := vsPRho_W hs h2.hgs t
  have hzN : vsPRho hs z ∈ N := vsPRho_mem_vsPBar hs (vsPW_mem (fun g hg => Subgroup.subset_closure hg) t) hzg
  -- `ρ z` commutes with the generators
  have hcomm : ∀ g ∈ gs.map (vsPRho hs), vsPRho hs z * g = g * vsPRho hs z := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < gs.length := by simpa using hj
    have hw : (gs.map (vsPRho hs))[j] ∈ N := by rw [List.getElem_map]; exact hgN _ (List.getElem_mem hj')
    rw [← hP.dl_eq_zero_iff hzN hw, hzW,
      hP.dl_W (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hgN y hy) hw t
        (by rw [List.length_map]; exact htl)]
    have h0 := congrFun (vsP_ker_comb hfit ht) j
    rw [Pi.zero_apply] at h0
    rw [← h0, show us = gs.map (vsPKey I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs) from rfl,
      vsP_zip_eval (vsPKey I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs) (vsPRho hs)
        (fun x => vsPDl r (vsPRho hs c0) x (gs.map (vsPRho hs))[j]) j (fun x hx => ?_) t]
    rw [vsF_vsPKey hs hc0 hP h2.hgs hgN (h2.hgs x hx) (hgN x hx)]
    simp [vsPKV, hj']
  have hzM : vsPRho hs z ∈ M := by
    refine ⟨hzN, ?_⟩
    show vsPRho hs z ∈ Subgroup.centralizer (N : Set _)
    rw [Subgroup.mem_centralizer_iff]
    have : N ≤ Subgroup.centralizer ({vsPRho hs z} : Set _) := by
      rw [show N = _ from vsPBar_gens' h2.hgs]
      refine (Subgroup.closure_le _).2 fun g hg => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm g hg).symm
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (this hy))
  -- the subgroup `Nx`
  have hNcl : ∀ g ∈ vsPBar hs (gens s.hs), ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    rw [vsPBar_top_eq hs]; exact vsP_norm_closure h2.hNn
  have hNx : vsPYs hs M ≤ gens s.hs := fun x hx => (vsPYs_iff.1 hx).1
  have hNxn : VsPNormd (gens s.hs) (vsPYs hs M) := by
    intro g hg x hx
    obtain ⟨hxg, hxM⟩ := vsPYs_iff.1 hx
    refine vsPYs_iff.2 ⟨mul_mem (mul_mem hg hxg) (inv_mem hg), ?_⟩
    rw [vsPRho_conj hs hxg hg]
    have hgb := vsPRho_mem_vsPBar hs hg hg
    refine ⟨hNcl _ hgb _ hxM.1, ?_⟩
    show _ ∈ Subgroup.centralizer (N : Set (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (vsPRho hs g)⁻¹ * y * (vsPRho hs g)⁻¹⁻¹ ∈ N := hNcl _ (inv_mem hgb) _ hy
    have hc := Subgroup.mem_centralizer_iff.1 hxM.2 _ hy'
    calc y * (vsPRho hs g * vsPRho hs x * (vsPRho hs g)⁻¹)
        = vsPRho hs g * ((vsPRho hs g)⁻¹ * y * (vsPRho hs g)⁻¹⁻¹ * vsPRho hs x) * (vsPRho hs g)⁻¹ := by
          group
      _ = vsPRho hs g * (vsPRho hs x * ((vsPRho hs g)⁻¹ * y * (vsPRho hs g)⁻¹⁻¹)) * (vsPRho hs g)⁻¹ := by
          rw [hc]
      _ = vsPRho hs g * vsPRho hs x * (vsPRho hs g)⁻¹ * y := by group
  have hbar : vsPBar hs (vsPYs hs M) ≤ M := by
    intro u hu
    obtain ⟨x, hx, -, rfl⟩ := (vsPBar_mem_iff hs).1 hu
    exact (vsPYs_iff.1 hx).2
  have hzS : vsPRho hs z ∉ S := fun hS => by
    rw [← hib z hzg] at hS; rw [hS] at hz; exact Bool.noConfusion hz
  refine vsP_grow_out hH hNx hNxn (xs := [z]) (fun y hy => by
      simp at hy; rw [hy]; exact vsPYs_iff.2 ⟨hzg, hzM⟩) ?_ ?_ (by simp : z ∈ [z]) hzS hl he
  · intro u hu
    exact Subgroup.mem_centralizer_iff.2 fun v hv =>
      (Subgroup.mem_centralizer_iff.1 (hbar hv).2 u (hbar hu).1).symm
  · exact fun u hu => h2.hNC (hbar hu).1

end GI.Proved
