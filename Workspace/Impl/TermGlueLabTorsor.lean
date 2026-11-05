module

public import Workspace.Impl.TermGlueLabMain

@[expose] public section

/-!
# The label torsor `A/B(x)` of Theorem A.23

Proof of Theorem A.23: "On the fixed type multiset, the possible `J`-orbits
form a torsor for `A/B(x)`, with an additional `C₂` orientation coordinate exactly when every
type is distinct."

We work in the general setting of `MulticosetTerminal`: a group `P` acting on the right on rows
`Ω`, a subgroup `N`, and `φ : N → A` with `A` abelian. Fix a row tuple `x : Fin q → Ω` and its
type multiset `T = types N x`. Every string below has type multiset `T`.

* `tmGLV N φ x`: the group `A/B(x)`, where `B(x) = labelGroup N φ x` is the sum of the groups
  `B_a`. We take it as `N` modulo the preimage of `B(x)`. This is `φ(N)/B(x)`, the paper's
  `A/B(x)` with `A = N/N*`, without asking `φ` to be onto.
* `tmGLc n`: the class `[n]` of `n ∈ N` in `A/B(x)`.
* `tmGLLab rep z`: the total label `s(z) = Σ_i α_i`. For row `z_i` of type `a`, write
  `z_i = (rep a)^{n_i}` with `n_i ∈ N` and add the classes `[n_i]`. It does not depend on the
  choice of `n_i` (`tmGLLab_eq`).
* `tmGLOr z`: the orientation. When every type is distinct, the rows of `z` and of `x` are
  matched by type in exactly one way, and the orientation is the sign of that matching. When a
  type repeats it is `1`.
* `tmGL_J_iff`: two strings are `J`-isomorphic exactly when their labels and orientations agree.
-/

namespace GI.Impl

open GI.Multicoset Equiv Equiv.Perm

section Torsor

variable {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
variable (N : Subgroup P) {A : Type*} [CommGroup A] (φ : N →* A) (x : Fin q → Ω)

/-! ### The group `A/B(x)` -/

/-- The map `N → A/B(x)`. -/
def tmGLf : N →* A ⧸ labelGroup N φ x := (QuotientGroup.mk' _).comp φ

/-- **The group `A/B(x)`**, as `N` modulo the preimage of `B(x)`. -/
abbrev tmGLV : Type _ := N ⧸ (tmGLf N φ x).ker

instance tmGLV.commGroup : CommGroup (tmGLV N φ x) :=
  { (inferInstance : Group (tmGLV N φ x)) with
    mul_comm := by
      rintro ⟨a⟩ ⟨b⟩
      change (QuotientGroup.mk (a * b) : tmGLV N φ x) = QuotientGroup.mk (b * a)
      rw [QuotientGroup.eq]
      change tmGLf N φ x _ = 1
      simp only [map_mul, map_inv]
      rw [mul_comm (tmGLf N φ x a) (tmGLf N φ x b), inv_mul_cancel] }

/-- The embedding `A/B(x) → φ(N)/B(x) ≤ A/B(x)`. -/
def tmGLψ : tmGLV N φ x →* A ⧸ labelGroup N φ x := QuotientGroup.kerLift (tmGLf N φ x)

theorem tmGLψ_injective : Function.Injective (tmGLψ N φ x) := QuotientGroup.kerLift_injective _

open Classical in
/-- **The class `[n]`** of `n ∈ N` in `A/B(x)` (`1` off `N`). -/
noncomputable def tmGLc (n : P) : tmGLV N φ x :=
  if hn : n ∈ N then QuotientGroup.mk ⟨n, hn⟩ else 1

variable {N φ x}

theorem tmGLψ_c {n : P} (hn : n ∈ N) :
    tmGLψ N φ x (tmGLc N φ x n) = QuotientGroup.mk (phiT N φ n) := by
  simp only [tmGLc, dif_pos hn, phiT]
  rfl

theorem tmGLc_one : tmGLc N φ x 1 = 1 := by
  simp only [tmGLc, dif_pos N.one_mem]
  rfl

theorem tmGLc_mul {n n' : P} (hn : n ∈ N) (hn' : n' ∈ N) :
    tmGLc N φ x (n * n') = tmGLc N φ x n * tmGLc N φ x n' := by
  simp only [tmGLc, dif_pos hn, dif_pos hn', dif_pos (N.mul_mem hn hn')]
  rfl

theorem tmGLc_inv {n : P} (hn : n ∈ N) : tmGLc N φ x n⁻¹ = (tmGLc N φ x n)⁻¹ := by
  simp only [tmGLc, dif_pos hn, dif_pos (N.inv_mem hn)]
  rfl

/-- Products of classes are read through `φ`. -/
theorem tmGLψ_prod {n : Fin q → P} (hn : ∀ i, n i ∈ N) :
    tmGLψ N φ x (∏ i, tmGLc N φ x (n i)) = QuotientGroup.mk (∏ i, phiT N φ (n i)) := by
  rw [map_prod, QuotientGroup.mk_prod]
  exact Finset.prod_congr rfl fun i _ => tmGLψ_c (hn i)

/-- **Equal class products**: exactly when the totals agree modulo `B(x)`. -/
theorem tmGLc_prod_eq_iff {n n' : Fin q → P} (hn : ∀ i, n i ∈ N) (hn' : ∀ i, n' i ∈ N) :
    ∏ i, tmGLc N φ x (n i) = ∏ i, tmGLc N φ x (n' i) ↔
      (∏ i, phiT N φ (n' i)) * (∏ i, phiT N φ (n i))⁻¹ ∈ labelGroup N φ x := by
  rw [← (tmGLψ_injective N φ x).eq_iff, tmGLψ_prod hn, tmGLψ_prod hn', eq_comm,
    QuotientGroup.eq, mul_comm]
  constructor
  · intro h
    have := (labelGroup N φ x).inv_mem h
    simpa [mul_comm] using this
  · intro h
    have := (labelGroup N φ x).inv_mem h
    simpa [mul_comm] using this

/-- A class is trivial when its `φ`-image lies in `B(x)`. -/
theorem tmGLc_eq_one {n : P} (hn : n ∈ N) (h : phiT N φ n ∈ labelGroup N φ x) :
    tmGLc N φ x n = 1 := by
  apply tmGLψ_injective N φ x
  rw [tmGLψ_c hn, map_one, QuotientGroup.eq_one_iff]
  exact h

/-- `B(x)` contains the labels of the stabilizer of any row of a type of `x`. -/
theorem tmGL_aut_label {j : Fin q} {c : P} (hc : c ∈ N) {s : P} (hs : s ∈ Aut N (x j ↼ c)) :
    phiT N φ s ∈ labelGroup N φ x := by
  classical
  obtain ⟨s', hs', he⟩ := (exists_label_aut_act_iff (φ := φ) hc (phiT N φ s)).mp ⟨s, hs, rfl⟩
  refine ⟨Pi.mulSingle j s', fun i => ?_, ?_⟩
  · by_cases hi : i = j
    · subst hi; simpa using hs'
    · simp [Pi.mulSingle_eq_of_ne hi, (Aut N (x i)).one_mem]
  · rw [Finset.prod_eq_single j (fun i _ hi => by simp [Pi.mulSingle_eq_of_ne hi, phiT_one])
      (by simp)]
    simpa using he

/-- **`B(x)` depends only on the type multiset.** -/
theorem tmGL_labelGroup_eq {z : Fin q → Ω} (hz : types N z = types N x) :
    labelGroup N φ z = labelGroup N φ x := by
  have key : ∀ {u v : Fin q → Ω}, types N u = types N v →
      labelGroup N φ u ≤ labelGroup N φ v := by
    intro u v huv
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.prod_mem _ fun i _ => ?_
    -- the type of `u_i` is the type of some `v_j`
    have hmem : orbitN N (u i) ∈ types N v := by
      rw [← huv]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
    have hu : u i ∈ orbitN N (v j) := by rw [hj]; exact ⟨1, N.one_mem, act_one _⟩
    obtain ⟨c, hc, hce⟩ := hu
    have hsi := hs i
    rw [← hce] at hsi
    exact tmGL_aut_label hc hsi
  exact le_antisymm (key hz) (key hz.symm)

/-! ### The total label -/

variable (N φ x)

open Classical in
/-- An element `n ∈ N` with `(rep a)^n = z_i`, for `a` the type of `z_i` (`1` if none). -/
noncomputable def tmGLn (rep : Set Ω → Ω) (z : Fin q → Ω) (i : Fin q) : P :=
  if h : ∃ n ∈ N, rep (orbitN N (z i)) ↼ n = z i then h.choose else 1

/-- **The total label** `s(z) = Σ_i [n_i]` in `A/B(x)`. -/
noncomputable def tmGLLab (rep : Set Ω → Ω) (z : Fin q → Ω) : tmGLV N φ x :=
  ∏ i, tmGLc N φ x (tmGLn N rep z i)

variable {N φ x}

/-- The representatives: `rep a` is a row of type `a`, for every type `a` of `x`. -/
def TmGLRep (N : Subgroup P) (x : Fin q → Ω) (rep : Set Ω → Ω) : Prop :=
  ∀ i, rep (orbitN N (x i)) ∈ orbitN N (x i)

/-- Every row of a string with type multiset `T` is reached from its representative. -/
theorem tmGL_rep_reach {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {z : Fin q → Ω}
    (hz : types N z = types N x) (i : Fin q) : ∃ n ∈ N, rep (orbitN N (z i)) ↼ n = z i := by
  have hmem : orbitN N (z i) ∈ types N x := by
    rw [← hz]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  have h1 := hrep j
  rw [hj] at h1
  obtain ⟨c, hc, hce⟩ := h1
  exact ⟨c⁻¹, N.inv_mem hc, by rw [← hce, act_act_inv]⟩

theorem tmGLn_spec {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {z : Fin q → Ω}
    (hz : types N z = types N x) (i : Fin q) :
    tmGLn N rep z i ∈ N ∧ rep (orbitN N (z i)) ↼ tmGLn N rep z i = z i := by
  have h := tmGL_rep_reach hrep hz i
  simp only [tmGLn, dif_pos h]
  exact h.choose_spec

/-- **The label does not depend on the choice of the `n_i`** ("The total `s(x)` is well
defined"): two choices differ by a stabilizer of the representative, whose class is trivial. -/
theorem tmGLLab_eq {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {z : Fin q → Ω}
    (hz : types N z = types N x) {a : Fin q → P} (ha : ∀ i, a i ∈ N)
    (haz : ∀ i, rep (orbitN N (z i)) ↼ a i = z i) :
    tmGLLab N φ x rep z = ∏ i, tmGLc N φ x (a i) := by
  unfold tmGLLab
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨hn, hnz⟩ := tmGLn_spec hrep hz i
  set n := tmGLn N rep z i
  -- `s = n a⁻¹` fixes the representative
  have hs : n * (a i)⁻¹ ∈ Aut N (rep (orbitN N (z i))) := by
    refine mem_aut.mpr ⟨N.mul_mem hn (N.inv_mem (ha i)), ?_⟩
    rw [← act_act, hnz, act_eq_iff, inv_inv]
    exact (haz i).symm
  -- the representative is a row of a type of `x`
  have hmem : orbitN N (z i) ∈ types N x := by
    rw [← hz]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  obtain ⟨c, hc, hce⟩ := hrep j
  rw [← hj, ← hce] at hs
  have h1 := tmGLc_eq_one (x := x) (N.mul_mem hn (N.inv_mem (ha i)))
    (tmGL_aut_label (φ := φ) hc hs)
  rw [tmGLc_mul hn (N.inv_mem (ha i)), tmGLc_inv (ha i), mul_inv_eq_one] at h1
  exact h1

/-! ### The orientation -/

variable (N x)

open Classical in
/-- **The orientation.** When every type of `x` is distinct, the sign of the matching `π` with
`type(z_{π i}) = type(x_i)`; otherwise `1`. -/
noncomputable def tmGLOr (z : Fin q → Ω) : ℤˣ :=
  if h : (types N x).Nodup ∧ ∃ π : Perm (Fin q), ∀ i, orbitN N (z (π i)) = orbitN N (x i) then
    sign h.2.choose else 1

variable {N x}

/-- Distinct types: a row is determined by its type. -/
theorem tmGL_types_inj {z : Fin q → Ω} (hz : types N z = types N x) (hT : (types N x).Nodup)
    {i j : Fin q} (h : orbitN N (z i) = orbitN N (z j)) : i = j := by
  rw [← hz, types] at hT
  exact (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hT i (by simp) j (by simp) h

/-- **The orientation is the sign of any type matching.** -/
theorem tmGLOr_eq {z : Fin q → Ω} (hz : types N z = types N x) (hT : (types N x).Nodup)
    {π : Perm (Fin q)} (hπ : ∀ i, orbitN N (z (π i)) = orbitN N (x i)) :
    tmGLOr N x z = sign π := by
  have h : (types N x).Nodup ∧ ∃ π : Perm (Fin q), ∀ i, orbitN N (z (π i)) = orbitN N (x i) :=
    ⟨hT, π, hπ⟩
  simp only [tmGLOr, dif_pos h]
  congr 1
  refine Equiv.ext fun i => tmGL_types_inj hz hT ?_
  rw [h.2.choose_spec i, hπ i]

theorem tmGLOr_of_not_nodup (hT : ¬ (types N x).Nodup) (z : Fin q → Ω) : tmGLOr N x z = 1 := by
  simp only [tmGLOr]
  rw [dif_neg (fun h => hT h.1)]

/-- A type matching from `x` exists for every string with the same type multiset. -/
theorem tmGL_match_x {z : Fin q → Ω} (hz : types N z = types N x) :
    ∃ π : Perm (Fin q), ∀ i, orbitN N (z (π i)) = orbitN N (x i) :=
  tmGL_exists_perm (f := fun i => orbitN N (x i)) (g := fun i => orbitN N (z i))
    hz.symm

/-! ### `J`-orbits are classified by the label and the orientation -/

/-- The label test for a type matching `π` with equal labels. -/
theorem tmGL_labelOK {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {z w : Fin q → Ω}
    (hz : types N z = types N x) (hw : types N w = types N x) {π : Perm (Fin q)}
    (hπ : ∀ i, orbitN N (w (π i)) = orbitN N (z i))
    (hl : tmGLLab N φ x rep z = tmGLLab N φ x rep w) : LabelOK N φ z w π := by
  have hA := tmGLn_spec hrep hz
  have hC := tmGLn_spec hrep hw
  set a := tmGLn N rep z
  set c := tmGLn N rep w
  refine ⟨fun i => (a i)⁻¹ * c (π i), fun i => N.mul_mem (N.inv_mem (hA i).1) (hC (π i)).1,
    fun i => ?_, ?_⟩
  · rw [← act_act, ← (hA i).2, act_act_inv, ← hπ i, (hC (π i)).2]
  · have hprod : ∏ i, phiT N φ ((a i)⁻¹ * c (π i)) =
        (∏ j, phiT N φ (c j)) * (∏ i, phiT N φ (a i))⁻¹ := by
      calc ∏ i, phiT N φ ((a i)⁻¹ * c (π i))
          = ∏ i, ((phiT N φ (a i))⁻¹ * phiT N φ (c (π i))) :=
            Finset.prod_congr rfl fun i _ => by
              rw [phiT_mul (N.inv_mem (hA i).1) (hC (π i)).1, phiT_inv (hA i).1]
        _ = (∏ i, phiT N φ (a i))⁻¹ * ∏ i, phiT N φ (c (π i)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
        _ = _ := by rw [Equiv.prod_comp π (fun j => phiT N φ (c j)), mul_comm]
    rw [hprod, tmGL_labelGroup_eq hz]
    exact (tmGLc_prod_eq_iff (fun i => (hA i).1) (fun i => (hC i).1)).mp hl

/-- A `J`-element keeps the type multiset, row by row along its matching. -/
theorem tmGL_orbit_J {z w : Fin q → Ω} {μ : Fin q → P} {π : Perm (Fin q)} (hμ : ∀ i, μ i ∈ N)
    (h : rowAct μ π z = w) (i : Fin q) : orbitN N (w (π i)) = orbitN N (z i) := by
  rw [← rowAct_eq_iff.mp h i, orbitN_kernel (hμ i)]

/-- Two rows of equal type when a type repeats. -/
theorem tmGL_repeat {z : Fin q → Ω} (hz : types N z = types N x) (hT : ¬ (types N x).Nodup) :
    ∃ i j, i ≠ j ∧ ∃ c ∈ N, z i ↼ c = z j := by
  rw [← hz, types] at hT
  have : ¬ ∀ i ∈ (Finset.univ.val : Multiset (Fin q)), ∀ j ∈ (Finset.univ.val : Multiset (Fin q)),
      orbitN N (z i) = orbitN N (z j) → i = j :=
    fun h => hT ((Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mpr h)
  push Not at this
  obtain ⟨i, -, j, -, hij, hne⟩ := this
  have hj : z j ∈ orbitN N (z i) := by rw [hij]; exact ⟨1, N.one_mem, act_one _⟩
  obtain ⟨c, hc, hce⟩ := hj
  exact ⟨i, j, hne, c, hc, hce⟩

/-- **The `J`-orbits form a torsor** ("Two strings are `J`-isomorphic exactly when their type
multisets agree, their total labels agree, and a matching of their fiber types can be chosen
even"). On the type multiset of `x`, two strings are `J`-isomorphic exactly when their labels in
`A/B(x)` and their orientations agree. -/
theorem tmGL_J_iff {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {z w : Fin q → Ω}
    (hz : types N z = types N x) (hw : types N w = types N x) :
    (∃ μ π, InJ N φ μ π ∧ rowAct μ π z = w) ↔
      tmGLLab N φ x rep z = tmGLLab N φ x rep w ∧ tmGLOr N x z = tmGLOr N x w := by
  constructor
  · rintro ⟨μ, π, ⟨hμN, hμ1, hπ⟩, h⟩
    have ho := tmGL_orbit_J hμN h
    have hA := tmGLn_spec hrep hz
    refine ⟨?_, ?_⟩
    · -- the label of `w` from the choices for `z` corrected by `μ`
      have hb : ∀ j, rep (orbitN N (w j)) ↼ (tmGLn N rep z (π.symm j) * μ (π.symm j)) = w j := by
        intro j
        have e := ho (π.symm j)
        rw [Equiv.apply_symm_apply] at e
        rw [e, ← act_act, (hA _).2]
        have := rowAct_eq_iff.mp h (π.symm j)
        rwa [Equiv.apply_symm_apply] at this
      rw [tmGLLab_eq hrep hw (fun j => N.mul_mem (hA _).1 (hμN _)) hb,
        Equiv.prod_comp π.symm (fun i => tmGLc N φ x (tmGLn N rep z i * μ i))]
      simp_rw [tmGLc_mul (hA _).1 (hμN _)]
      rw [Finset.prod_mul_distrib, tmGLLab]
      have h1 : ∏ i, tmGLc N φ x (μ i) = ∏ _i : Fin q, tmGLc N φ x 1 :=
        (tmGLc_prod_eq_iff hμN fun _ => N.one_mem).mpr (by
          rw [hμ1]; simp [phiT_one])
      rw [h1]
      simp [tmGLc_one]
    · by_cases hT : (types N x).Nodup
      · obtain ⟨πz, hπz⟩ := tmGL_match_x hz
        rw [tmGLOr_eq hz hT hπz, tmGLOr_eq (π := π * πz) hw hT (fun i => by
          rw [Perm.mul_apply, ho, hπz])]
        rw [Perm.sign_mul, Equiv.Perm.mem_alternatingGroup.mp hπ, one_mul]
      · rw [tmGLOr_of_not_nodup hT, tmGLOr_of_not_nodup hT]
  · rintro ⟨hl, ho⟩
    obtain ⟨π0, hπ0⟩ := tmGL_exists_perm (f := fun i => orbitN N (z i))
      (g := fun i => orbitN N (w i)) (hz.trans hw.symm)
    have hok := tmGL_labelOK hrep hz hw hπ0 hl
    rw [exists_jIso_iff]
    by_cases hev : π0 ∈ alternatingGroup (Fin q)
    · exact ⟨π0, hev, hok⟩
    by_cases hT : (types N x).Nodup
    · exfalso
      obtain ⟨πz, hπz⟩ := tmGL_match_x hz
      rw [tmGLOr_eq hz hT hπz, tmGLOr_eq (π := π0 * πz) hw hT (fun i => by
        rw [Perm.mul_apply, hπ0, hπz]), Perm.sign_mul] at ho
      apply hev
      rw [Equiv.Perm.mem_alternatingGroup]
      exact mul_eq_right.mp ho.symm
    · obtain ⟨i, j, hij, c, hc, hce⟩ := tmGL_repeat hz hT
      exact (exists_even_iff_exists_of_repeat hij hc hce).mpr ⟨π0, hok⟩

end Torsor

end GI.Impl
