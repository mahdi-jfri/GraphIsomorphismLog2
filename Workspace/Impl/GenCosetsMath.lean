import Workspace.Algorithm.Dispatch
import Workspace.Assembly.Encoding
import Workspace.Impl.GenCosets

/-!
# Coset representatives of the block kernel: the mathematics

`cosetList_length` and `CosetReps.ofList`: a list of elements of `G` that meets every left coset
of `K` exactly once has length `|G : K|` and gives `CosetReps G K`.

For a primitive quotient `Q`, the labeling `Q.labFin e` of `Fin k` gives each point of the
domain its block and every other point the label `d`. An element `h ∈ G` fixes this labeling
(under `labAct`) exactly when it lies in the block kernel (`labAct_labFin_eq_iff`). So the
orbit program on `Q.labFin e` gives coset representatives of the kernel (`cosetReps_ofPairs`),
and its orbit has at most `|ρ(G)|` points (`ncard_orbit_le`).
-/

namespace GI.Algorithm
open Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type}

/-- **Coset representatives from a list.** A list of elements of `G` that meets every left coset
of `K` exactly once has length `|G : K|`, and gives `CosetReps G K`. -/
theorem cosetList_length {G K : Subgroup (Perm Ω)} (ts : List (Perm Ω)) (hmem : ∀ t ∈ ts, t ∈ G)
    (hcov : ∀ g ∈ G, ∃ t ∈ ts, t⁻¹ * g ∈ K)
    (hdist : ∀ i j (hi : i < ts.length) (hj : j < ts.length), ts[i]⁻¹ * ts[j] ∈ K → i = j) :
    ts.length = (K.subgroupOf G).index := by
  classical
  let φ : Fin ts.length → G ⧸ K.subgroupOf G := fun j =>
    QuotientGroup.mk (⟨ts[j], hmem _ (List.getElem_mem j.2)⟩ : G)
  have hinj : Function.Injective φ := by
    intro i j h
    have := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at this
    exact Fin.ext (hdist i j i.2 j.2 (by simpa using this))
  have hsurj : Function.Surjective φ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨t, ht, hk⟩ := hcov g g.2
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
      refine ⟨⟨j, hj⟩, QuotientGroup.eq.mpr ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simpa using hk
  rw [Subgroup.index, ← Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The coset representatives given by such a list. -/
def CosetReps.ofList {G K : Subgroup (Perm Ω)} (ts : List (Perm Ω)) (hmem : ∀ t ∈ ts, t ∈ G)
    (hcov : ∀ g ∈ G, ∃ t ∈ ts, t⁻¹ * g ∈ K)
    (hdist : ∀ i j (hi : i < ts.length) (hj : j < ts.length), ts[i]⁻¹ * ts[j] ∈ K → i = j) :
    CosetReps G K where
  τ j := ts[(j : ℕ)]'(by rw [cosetList_length ts hmem hcov hdist]; exact j.2)
  mem j := hmem _ (List.getElem_mem _)
  cover g hg := by
    obtain ⟨t, ht, hk⟩ := hcov g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    refine Set.mem_iUnion.mpr ⟨⟨j, by rw [← cosetList_length ts hmem hcov hdist]; exact hj⟩, ?_⟩
    exact ⟨ts[j]⁻¹ * g, hk, by simp⟩

/-- The coset property moves along an isomorphism of groups. -/
theorem cosetList_map {Ω' : Type} (φ : Perm Ω' ≃* Perm Ω) {G K : Subgroup (Perm Ω)}
    (ts : List (Perm Ω')) (hmem : ∀ t ∈ ts, φ t ∈ G)
    (hcov : ∀ g, φ g ∈ G → ∃ t ∈ ts, φ (t⁻¹ * g) ∈ K)
    (hdist : ∀ i j (hi : i < ts.length) (hj : j < ts.length), φ (ts[i]⁻¹ * ts[j]) ∈ K → i = j) :
    (∀ t ∈ ts.map φ, t ∈ G) ∧ (∀ g ∈ G, ∃ t ∈ ts.map φ, t⁻¹ * g ∈ K) ∧
      (∀ i j (hi : i < (ts.map φ).length) (hj : j < (ts.map φ).length),
        (ts.map φ)[i]⁻¹ * (ts.map φ)[j] ∈ K → i = j) := by
  refine ⟨fun t ht => ?_, fun g hg => ?_, fun i j hi hj h => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact hmem t' ht'
  · obtain ⟨t, ht, hk⟩ := hcov (φ.symm g) (by simpa using hg)
    refine ⟨φ t, List.mem_map_of_mem ht, ?_⟩
    simpa using hk
  · simp only [List.length_map] at hi hj
    refine hdist i j hi hj ?_
    simpa using h

namespace PrimitiveQuotient

variable {C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)

/-- **The block kernel**: the elements of `G` that map every block to itself. -/
theorem mem_kernel_iff {g : Perm Ω} :
    g ∈ Q.kernel ↔ g ∈ S.G ∧ ∀ v ∈ S.dom, Q.blk (g v) = Q.blk v := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g'.2, fun v hv => ?_⟩
    show Q.blk ((g' : Perm Ω) v) = _
    rw [Q.equivariant g' v hv, MonoidHom.mem_ker.1 hg']
    rfl
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    ext i
    obtain ⟨v, hv, rfl⟩ := Q.onto i
    rw [← Q.equivariant ⟨g, hg⟩ v hv]
    simp [h v hv]

open Classical in
/-- The block labeling on `Fin k`: the block of a point of the domain, and `d` elsewhere. -/
noncomputable def labFin {k : ℕ} (e : Ω ≃ Fin k) : Fin k → ℕ :=
  fun i => if e.symm i ∈ S.dom then (Q.blk (e.symm i) : ℕ) else Q.d

theorem labFin_le {k : ℕ} (e : Ω ≃ Fin k) (i : Fin k) : Q.labFin e i ≤ Q.d := by
  unfold labFin; split_ifs <;> omega

theorem d_le_card {k : ℕ} (e : Ω ≃ Fin k) : Q.d ≤ k := by
  have hs : Function.Surjective fun i : Fin k => Q.blk (e.symm i) := fun j => by
    obtain ⟨v, -, rfl⟩ := Q.onto j
    exact ⟨e v, by simp⟩
  simpa using Fintype.card_le_of_surjective _ hs

open GI.Lang GI.Assembly Classical in
/-- The action of `toFin e h` on the block labeling. -/
theorem labAct_labFin {k : ℕ} (e : Ω ≃ Fin k) {h : Perm Ω} (hh : h ∈ S.G) (i : Fin k) :
    labAct (toFin e h) (Q.labFin e) i =
      if e.symm i ∈ S.dom then ((Q.ρ ⟨h, hh⟩)⁻¹ (Q.blk (e.symm i)) : ℕ) else Q.d := by
  have hinv : (toFin e h)⁻¹ = toFin e h⁻¹ := (map_inv _ _).symm
  simp only [labAct, labFin, hinv]
  have h1 : e.symm (toFin e h⁻¹ i) = h⁻¹ (e.symm i) := by
    show e.symm (e (h⁻¹ (e.symm i))) = _
    simp
  rw [h1]
  have hdom : h⁻¹ (e.symm i) ∈ S.dom ↔ e.symm i ∈ S.dom :=
    S.dom_inv h⁻¹ (S.G.inv_mem hh) _
  by_cases hi : e.symm i ∈ S.dom
  · rw [if_pos (hdom.2 hi), if_pos hi]
    have := Q.equivariant ⟨h, hh⟩ (h⁻¹ (e.symm i)) (hdom.2 hi)
    simp only [Perm.apply_inv_self] at this
    rw [this]
    simp
  · rw [if_neg (fun h' => hi (hdom.1 h')), if_neg hi]

open GI.Lang GI.Assembly in
/-- **An element of `G` fixes the block labeling exactly when it lies in the kernel.** -/
theorem labAct_labFin_eq_iff {k : ℕ} (e : Ω ≃ Fin k) {h : Perm Ω} (hh : h ∈ S.G) :
    labAct (toFin e h) (Q.labFin e) = Q.labFin e ↔ h ∈ Q.kernel := by
  rw [Q.mem_kernel_iff]
  constructor
  · intro heq
    refine ⟨hh, fun v hv => ?_⟩
    have := congrFun heq (e v)
    rw [Q.labAct_labFin e hh] at this
    simp only [Equiv.symm_apply_apply, labFin] at this
    have hv' : e.symm (e v) ∈ S.dom := by simpa using hv
    rw [if_pos hv', if_pos hv'] at this
    have h2 : (Q.ρ ⟨h, hh⟩)⁻¹ (Q.blk v) = Q.blk v := Fin.ext this
    have h3 := Q.equivariant ⟨h, hh⟩ v hv
    rw [h3]
    have := congrArg (Q.ρ ⟨h, hh⟩) h2
    simp only [Perm.apply_inv_self] at this
    exact this.symm
  · rintro ⟨-, hk⟩
    funext i
    rw [Q.labAct_labFin e hh]
    unfold labFin
    split_ifs with hi
    · congr 1
      rw [Perm.inv_eq_iff_eq, ← Q.equivariant ⟨h, hh⟩ _ hi, hk _ hi]
    · rfl

open GI.Lang in
/-- Two labelings with the same fibers have the same stabilizer. -/
theorem labAct_eq_iff_of_fibers {k : ℕ} {f f' : Fin k → ℕ} (hfib : ∀ i j, f' i = f' j ↔ f i = f j)
    (g : Perm (Fin k)) : labAct g f' = f' ↔ labAct g f = f := by
  simp only [funext_iff, labAct]
  exact forall_congr' fun i => hfib _ _

open GI.Lang GI.Assembly in
/-- **An element of `G` fixes a block labeling exactly when it lies in the kernel**, for any
labeling with the fibers of `Q.labFin e`. -/
theorem labAct_eq_iff_mem_kernel {k : ℕ} (e : Ω ≃ Fin k) {lab : Fin k → ℕ}
    (hfib : ∀ i j, lab i = lab j ↔ Q.labFin e i = Q.labFin e j) {h : Perm Ω} (hh : h ∈ S.G) :
    labAct (toFin e h) lab = lab ↔ h ∈ Q.kernel := by
  rw [labAct_eq_iff_of_fibers hfib, Q.labAct_labFin_eq_iff e hh]

open GI.Lang GI.Assembly Classical in
/-- **The orbit of the block labeling has at most `|ρ(G)|` points.** -/
theorem ncard_orbit_le {k : ℕ} (e : Ω ≃ Fin k) {gs : List (Perm (Fin k))}
    (hG : genGroup gs = groupFin e S.G) :
    (actOrbit labAct gs (Q.labFin e)).ncard ≤ Nat.card Q.ρ.range := by
  let F : Perm (Fin Q.d) → (Fin k → ℕ) := fun σ i =>
    if e.symm i ∈ S.dom then (σ⁻¹ (Q.blk (e.symm i)) : ℕ) else Q.d
  have hsub : actOrbit labAct gs (Q.labFin e) ⊆ F '' (Q.ρ.range : Set (Perm (Fin Q.d))) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hG] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    refine ⟨Q.ρ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, ?_⟩
    funext i
    exact (Q.labAct_labFin e hh i).symm
  calc (actOrbit labAct gs (Q.labFin e)).ncard
      ≤ (F '' (Q.ρ.range : Set (Perm (Fin Q.d)))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Q.ρ.range : Set (Perm (Fin Q.d))).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card Q.ρ.range := (Nat.card_coe_set_eq _).symm

open GI.Lang GI.Assembly Classical in
/-- The same bound for any labeling with the fibers of `Q.labFin e`. -/
theorem ncard_orbit_le' {k : ℕ} (e : Ω ≃ Fin k) {gs : List (Perm (Fin k))}
    (hG : genGroup gs = groupFin e S.G) {lab : Fin k → ℕ}
    (hfib : ∀ i j, lab i = lab j ↔ Q.labFin e i = Q.labFin e j) :
    (actOrbit labAct gs lab).ncard ≤ Nat.card Q.ρ.range := by
  let ψ : ℕ → ℕ := fun m => if h : ∃ i, Q.labFin e i = m then lab h.choose else 0
  have hψ : ∀ i, ψ (Q.labFin e i) = lab i := fun i => by
    have h : ∃ j, Q.labFin e j = Q.labFin e i := ⟨i, rfl⟩
    simp only [ψ, dif_pos h]
    exact (hfib _ _).2 h.choose_spec
  have hsub : actOrbit labAct gs lab ⊆ (fun f => ψ ∘ f) '' actOrbit labAct gs (Q.labFin e) := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨labAct g (Q.labFin e), ⟨g, hg, rfl⟩, ?_⟩
    funext i
    simp only [Function.comp_apply, labAct, hψ]
  have hfin : (actOrbit labAct gs (Q.labFin e)).Finite :=
    (Set.finite_range fun g : Perm (Fin k) => labAct g (Q.labFin e)).subset
      (by rintro _ ⟨g, -, rfl⟩; exact ⟨g, rfl⟩)
  calc (actOrbit labAct gs lab).ncard
      ≤ ((fun f => ψ ∘ f) '' actOrbit labAct gs (Q.labFin e)).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (actOrbit labAct gs (Q.labFin e)).ncard := Set.ncard_image_le hfin
    _ ≤ Nat.card Q.ρ.range := Q.ncard_orbit_le e hG

open GI.Lang GI.Assembly in
/-- **Coset representatives of the block kernel from the orbit program.** The second entries
of the pairs, moved back to `Ω`, meet every coset of the kernel exactly once. -/
theorem pairs_cosetList {k : ℕ} (e : Ω ≃ Fin k) {gs : List (Perm (Fin k))}
    (hG : genGroup gs = groupFin e S.G) {lab : Fin k → ℕ}
    (hfib : ∀ i j, lab i = lab j ↔ Q.labFin e i = Q.labFin e j)
    (L : List ((Fin k → ℕ) × Perm (Fin k))) (hnd : (L.map Prod.fst).Nodup)
    (horb : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct gs lab)
    (hp : ∀ p ∈ L, p.2 ∈ genGroup gs ∧ labAct p.2 lab = p.1) :
    let ts := (L.map Prod.snd).map (toFin e).symm
    (∀ t ∈ ts, t ∈ S.G) ∧ (∀ g ∈ S.G, ∃ t ∈ ts, t⁻¹ * g ∈ Q.kernel) ∧
      (∀ i j (hi : i < ts.length) (hj : j < ts.length), ts[i]⁻¹ * ts[j] ∈ Q.kernel → i = j) := by
  have hmemG : ∀ g, g ∈ genGroup gs ↔ (toFin e).symm g ∈ S.G := fun g => by
    rw [hG]; exact Subgroup.mem_map_equiv
  refine cosetList_map (toFin e).symm _ (fun t ht => ?_) (fun g hg => ?_) (fun i j hi hj h => ?_)
  · obtain ⟨p, hpL, rfl⟩ := List.mem_map.mp ht
    exact (hmemG _).1 (hp p hpL).1
  · have hg' : g ∈ genGroup gs := (hmemG g).2 hg
    obtain ⟨p, hpL, hpf⟩ := List.mem_map.mp ((horb (labAct g lab)).2 ⟨g, hg', rfl⟩)
    refine ⟨p.2, List.mem_map_of_mem hpL, ?_⟩
    have hm : (toFin e).symm (p.2⁻¹ * g) ∈ S.G :=
      (hmemG _).1 ((genGroup gs).mul_mem ((genGroup gs).inv_mem (hp p hpL).1) hg')
    rw [← Q.labAct_eq_iff_mem_kernel e hfib hm, MulEquiv.apply_symm_apply, isAct_lab.mul, ← hpf,
      ← (hp p hpL).2, ← isAct_lab.mul, inv_mul_cancel, isAct_lab.one]
  · simp only [List.length_map] at hi hj
    have hti : (L.map Prod.snd)[i] ∈ genGroup gs := by
      simpa using (hp L[i] (List.getElem_mem hi)).1
    have htj : (L.map Prod.snd)[j] ∈ genGroup gs := by
      simpa using (hp L[j] (List.getElem_mem hj)).1
    have hm : (toFin e).symm ((L.map Prod.snd)[i]⁻¹ * (L.map Prod.snd)[j]) ∈ S.G :=
      (hmemG _).1 ((genGroup gs).mul_mem ((genGroup gs).inv_mem hti) htj)
    have := (Q.labAct_eq_iff_mem_kernel e hfib hm).2 (by simpa using h)
    rw [MulEquiv.apply_symm_apply, isAct_lab.mul] at this
    have h2 := congrArg (labAct (L.map Prod.snd)[i]) this
    rw [← isAct_lab.mul, mul_inv_cancel, isAct_lab.one] at h2
    simp only [List.getElem_map] at h2
    rw [(hp L[i] (List.getElem_mem hi)).2, (hp L[j] (List.getElem_mem hj)).2] at h2
    exact (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simpa using hi)
      (hj := by simpa using hj)).1 (by simpa using h2.symm)

open GI.Lang GI.Assembly Classical in
/-- The block labeling after `toFin e h`. -/
theorem labFin_toFin {k : ℕ} (e : Ω ≃ Fin k) {h : Perm Ω} (hh : h ∈ S.G) (i : Fin k) :
    Q.labFin e (toFin e h i) =
      if e.symm i ∈ S.dom then ((Q.ρ ⟨h, hh⟩) (Q.blk (e.symm i)) : ℕ) else Q.d := by
  have h1 : e.symm (toFin e h i) = h (e.symm i) := by
    show e.symm (e (h (e.symm i))) = _
    simp
  have hdom : h (e.symm i) ∈ S.dom ↔ e.symm i ∈ S.dom := S.dom_inv h hh _
  unfold labFin
  rw [h1]
  by_cases hi : e.symm i ∈ S.dom
  · rw [if_pos (hdom.2 hi), if_pos hi, Q.equivariant ⟨h, hh⟩ _ hi]
  · rw [if_neg (fun h' => hi (hdom.1 h')), if_neg hi]

open GI.Lang GI.Assembly in
/-- `G` preserves the block relation on `Fin k`. -/
theorem labFin_pres {k : ℕ} (e : Ω ≃ Fin k) {g : Perm (Fin k)} (hg : g ∈ groupFin e S.G)
    (i j : Fin k) : Q.labFin e (g i) = Q.labFin e (g j) ↔ Q.labFin e i = Q.labFin e j := by
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
  change Q.labFin e (toFin e h i) = Q.labFin e (toFin e h j) ↔ _
  rw [Q.labFin_toFin e hh, Q.labFin_toFin e hh]
  unfold labFin
  have hl : ∀ a : Fin Q.d, (a : ℕ) ≠ Q.d := fun a => a.2.ne
  split_ifs with hi hj hj
  · rw [Fin.val_inj, Fin.val_inj]; exact (Q.ρ ⟨h, hh⟩).injective.eq_iff
  · exact ⟨fun h => absurd h (hl _), fun h => absurd h (hl _)⟩
  · exact ⟨fun h => absurd h.symm (hl _), fun h => absurd h.symm (hl _)⟩
  · exact Iff.rfl

open GI.Lang GI.Assembly in
/-- **The kernel on `Fin k`**: the elements of `G` that keep every block label. -/
theorem mem_groupFin_kernel_iff {k : ℕ} (e : Ω ≃ Fin k) (g : Perm (Fin k)) :
    g ∈ groupFin e Q.kernel ↔ g ∈ groupFin e S.G ∧ ∀ i, Q.labFin e (g i) = Q.labFin e i := by
  have hmem : ∀ (H : Subgroup (Perm Ω)) g, g ∈ groupFin e H ↔ (toFin e).symm g ∈ H :=
    fun H g => Subgroup.mem_map_equiv
  constructor
  · intro hk
    have hG : g ∈ groupFin e S.G := (hmem _ g).2 (Q.kernel_le ((hmem _ g).1 hk))
    refine ⟨hG, fun i => ?_⟩
    have hh := Q.kernel_le ((hmem _ g).1 hk)
    have := (Q.labAct_labFin_eq_iff e hh).2 ((hmem _ g).1 hk)
    rw [MulEquiv.apply_symm_apply] at this
    have := congrFun this (g i)
    simpa [labAct] using this.symm
  · rintro ⟨hG, hi⟩
    have hh : (toFin e).symm g ∈ S.G := (hmem _ g).1 hG
    refine (hmem _ g).2 ((Q.labAct_labFin_eq_iff e hh).1 ?_)
    rw [MulEquiv.apply_symm_apply]
    funext i
    simp only [labAct]
    have := hi (g⁻¹ i)
    simpa using this.symm

open GI.Lang GI.Assembly in
/-- **The coset representatives of the block kernel** read off the orbit program's pairs. -/
noncomputable def cosetRepsOfPairs {k : ℕ} (e : Ω ≃ Fin k) {gs : List (Perm (Fin k))}
    (hG : genGroup gs = groupFin e S.G) {lab : Fin k → ℕ}
    (hfib : ∀ i j, lab i = lab j ↔ Q.labFin e i = Q.labFin e j)
    (L : List ((Fin k → ℕ) × Perm (Fin k))) (hnd : (L.map Prod.fst).Nodup)
    (horb : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct gs lab)
    (hp : ∀ p ∈ L, p.2 ∈ genGroup gs ∧ labAct p.2 lab = p.1) :
    CosetReps S.G Q.kernel :=
  have h := Q.pairs_cosetList e hG hfib L hnd horb hp
  CosetReps.ofList _ h.1 h.2.1 h.2.2

end PrimitiveQuotient

end GI.Algorithm
