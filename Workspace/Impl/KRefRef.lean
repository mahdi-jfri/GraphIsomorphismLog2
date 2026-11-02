import Workspace.Impl.KRefModel

/-!
# When one round gives two tuples the same color

`krefStep_eq_iff`: after one round, two tuples `a, b` (each with the input it belongs to) have
the same color exactly when `KrefRef col a b` holds: they had the same color, the same equality
pattern, the same colors after every map `τ`, and there is a bijection `π` of the points such
that the vector of `a` at `z` equals the vector of `b` at `π z`. The relation `KrefRef col`
depends only on which tuples `col` colors alike (`krefRef_congr`), and this is what makes the
rounds stop changing (`Workspace/Impl/KRefStable.lean`).
-/

namespace GI.Impl

open GI.Cited Equiv

variable {n k : ℕ}

/-- The relation that the colors after one round compare. -/
def KrefRef (col : KCol n k) (a b : Bool × (Fin k → Fin n)) : Prop :=
  col a.1 a.2 = col b.1 b.2 ∧ (∀ i j, (a.2 i = a.2 j ↔ b.2 i = b.2 j)) ∧
  (∀ τ : Fin k → Fin k, col a.1 (a.2 ∘ τ) = col b.1 (b.2 ∘ τ)) ∧
  ∃ π : Perm (Fin n), ∀ z i,
    col a.1 (Function.update a.2 i z) = col b.1 (Function.update b.2 i (π z))

/-- `KrefRef col` depends only on which tuples `col` colors alike. -/
theorem krefRef_congr {col col' : KCol n k}
    (h : ∀ a b : Bool × (Fin k → Fin n), col a.1 a.2 = col b.1 b.2 ↔ col' a.1 a.2 = col' b.1 b.2)
    (a b : Bool × (Fin k → Fin n)) : KrefRef col a b ↔ KrefRef col' a b := by
  unfold KrefRef
  rw [h a b]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
  · exact forall_congr' fun τ => h (a.1, a.2 ∘ τ) (b.1, b.2 ∘ τ)
  · exact exists_congr fun π => forall_congr' fun z => forall_congr' fun i =>
      h (a.1, Function.update a.2 i z) (b.1, Function.update b.2 i (π z))

/-! ### Equality patterns -/

/-- The first position of the entry `x i` in `x`. -/
theorem krefPat_eq (x : Fin k → Fin n) :
    krefPat x = List.ofFn fun i => (List.finRange k).findIdx fun j => decide (x j = x i) := by
  unfold krefPat krefDig
  rw [List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, List.ofFn_eq_map, List.findIdx_map]
  congr 1
  funext j
  simp [Fin.val_inj]

theorem kref_findIdx_spec (x : Fin k → Fin n) (i : Fin k) :
    ∃ h : (List.finRange k).findIdx (fun j => decide (x j = x i)) < k,
      x ⟨_, h⟩ = x i := by
  have hex : ∃ j ∈ List.finRange k, decide (x j = x i) = true := ⟨i, List.mem_finRange _, by simp⟩
  have hl := List.findIdx_lt_length_of_exists hex
  rw [List.length_finRange] at hl
  refine ⟨hl, ?_⟩
  have := List.findIdx_getElem (w := (by rwa [List.length_finRange]))
    (p := fun j => decide (x j = x i)) (xs := List.finRange k)
  simpa using this

theorem kref_findIdx_eq_iff (x : Fin k → Fin n) (i j : Fin k) :
    (List.finRange k).findIdx (fun l => decide (x l = x i)) =
      (List.finRange k).findIdx (fun l => decide (x l = x j)) ↔ x i = x j := by
  constructor
  · intro h
    obtain ⟨h1, e1⟩ := kref_findIdx_spec x i
    obtain ⟨h2, e2⟩ := kref_findIdx_spec x j
    rw [← e1, ← e2]
    congr 1
    exact Fin.ext h
  · intro h
    rw [h]

theorem krefPat_eq_iff (x y : Fin k → Fin n) :
    krefPat x = krefPat y ↔ ∀ i j, (x i = x j ↔ y i = y j) := by
  rw [krefPat_eq, krefPat_eq, List.ofFn_inj]
  constructor
  · intro h i j
    rw [← kref_findIdx_eq_iff x, ← kref_findIdx_eq_iff y]
    rw [congrFun h i, congrFun h j]
  · intro h
    funext i
    congr 1
    funext j
    exact decide_eq_decide.mpr (h j i)

/-! ### Multisets of values over the points -/

theorem kref_count_ofFn {m : ℕ} (f : Fin m → ℕ) (u : ℕ) :
    (List.ofFn f).count u = Fintype.card {z // f z = u} := by
  have h1 : (List.ofFn f).count u = Multiset.count u (Finset.univ.val.map f) := by
    rw [Fin.univ_val_map, Multiset.coe_count]
  rw [h1, Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro z _
  exact eq_comm

/-- Two functions on the points take each value equally often exactly when they differ by a
bijection of the points. -/
theorem kref_count_eq_iff {m : ℕ} (f g : Fin m → ℕ) :
    (∀ u, (List.ofFn f).count u = (List.ofFn g).count u) ↔
      ∃ π : Perm (Fin m), ∀ z, f z = g (π z) := by
  constructor
  · intro h
    have e : ∀ u, {z // f z = u} ≃ {z // g z = u} := fun u =>
      Fintype.equivOfCardEq (by rw [← kref_count_ofFn, ← kref_count_ofFn]; exact h u)
    refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans
      (Equiv.sigmaFiberEquiv g)), fun z => ?_⟩
    exact (e (f z) ⟨z, rfl⟩).2.symm
  · rintro ⟨π, hπ⟩ u
    have : List.ofFn f = List.ofFn (g ∘ π) := by
      rw [List.ofFn_inj]; funext z; exact hπ z
    rw [this]
    exact ((Equiv.Perm.ofFn_comp_perm π g).count_eq u)

/-! ### The signature -/

section Sig

variable (col : KCol n k)

theorem length_krefVAll : (krefVAll col).length = krefM n k := by
  unfold krefVAll krefVCodes krefM
  simp only [List.length_append, List.length_flatten, List.map_map, Function.comp_def,
    List.length_ofFn, List.map_const', List.sum_replicate, length_krefTups, smul_eq_mul]
  ring

theorem krefVec_code_mem (β : Bool) (x : Fin k → Fin n) (z : Fin n) :
    krefHorner (krefB n k) (krefVec col β x z) ∈ krefVAll col := by
  unfold krefVAll
  apply List.mem_append.mpr
  have hm : krefHorner (krefB n k) (krefVec col β x z) ∈ (krefVCodes col β).flatten := by
    refine List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨x, mem_krefTups x, rfl⟩, ?_⟩
    exact List.mem_ofFn.mpr ⟨z, rfl⟩
  cases β
  · exact Or.inl hm
  · exact Or.inr hm

theorem krefRl_lt (β : Bool) (x : Fin k → Fin n) (z : Fin n) :
    krefRank (krefVAll col) (krefHorner (krefB n k) (krefVec col β x z)) < krefM n k := by
  rw [← length_krefVAll col]
  exact krefRank_lt_length (krefVec_code_mem col β x z)

theorem krefCounts_eq_iff (β β' : Bool) (x y : Fin k → Fin n) :
    krefCounts col β x = krefCounts col β' y ↔
      ∀ u, (krefRl col β x).count u = (krefRl col β' y).count u := by
  unfold krefCounts
  constructor
  · intro h u
    by_cases hu : u < krefM n k
    · have := congrArg (fun l => l[u]?) h
      simpa [List.getElem?_map, List.getElem?_range hu] using this
    · rw [List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem]
      · intro hm
        obtain ⟨z, hz⟩ := List.mem_ofFn.mp hm
        exact hu (hz ▸ krefRl_lt col β' y z)
      · intro hm
        obtain ⟨z, hz⟩ := List.mem_ofFn.mp hm
        exact hu (hz ▸ krefRl_lt col β x z)
  · intro h
    exact List.map_congr_left fun u _ => h u

/-- Colors at most `2 n^k`, as all colorings of the rounds are. -/
def KrefSmall (col : KCol n k) : Prop := ∀ β x, col β x ≤ 2 * n ^ k

variable {col}

theorem krefB_gt (hs : KrefSmall col) (β : Bool) (x : Fin k → Fin n) : col β x < krefB n k := by
  have := hs β x; unfold krefB; omega

theorem krefVec_lt (hs : KrefSmall col) (β : Bool) (x : Fin k → Fin n) (z : Fin n) :
    ∀ a ∈ krefVec col β x z, a < krefB n k := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact krefB_gt hs β _

theorem krefVec_code_inj (hs : KrefSmall col) {β β' : Bool} {x y : Fin k → Fin n} {z z' : Fin n}
    (h : krefRank (krefVAll col) (krefHorner (krefB n k) (krefVec col β x z)) =
      krefRank (krefVAll col) (krefHorner (krefB n k) (krefVec col β' y z'))) :
    ∀ i, col β (Function.update x i z) = col β' (Function.update y i z') := by
  have h1 := krefRank_inj (krefVec_code_mem col β x z) (krefVec_code_mem col β' y z') h
  have h2 := krefHorner_inj (by unfold krefB; omega) (by simp [krefVec]) (krefVec_lt hs β x z)
    (krefVec_lt hs β' y z') h1
  unfold krefVec at h2
  exact congrFun (List.ofFn_inj.mp h2)

theorem krefCounts_eq_iff' (hs : KrefSmall col) (β β' : Bool) (x y : Fin k → Fin n) :
    krefCounts col β x = krefCounts col β' y ↔ ∃ π : Perm (Fin n), ∀ z i,
      col β (Function.update x i z) = col β' (Function.update y i (π z)) := by
  rw [krefCounts_eq_iff, krefRl, krefRl, kref_count_eq_iff]
  refine exists_congr fun π => ⟨fun h z => krefVec_code_inj hs (h z), fun h z => ?_⟩
  congr 2
  unfold krefVec
  exact List.ofFn_inj.mpr (funext (h z))

theorem length_krefSig (β : Bool) (x : Fin k → Fin n) :
    (krefSig col β x).length = 1 + k + k ^ k + krefM n k := by
  simp [krefSig, krefPat, krefDig, krefTauCols, krefCounts, length_krefTups]
  omega

theorem krefSig_lt (hs : KrefSmall col) (β : Bool) (x : Fin k → Fin n) :
    ∀ a ∈ krefSig col β x, a < krefB n k := by
  intro a ha
  have hB : n + k < krefB n k := by unfold krefB; omega
  simp only [krefSig, List.mem_append, List.mem_singleton] at ha
  rcases ha with ((rfl | ha) | ha) | ha
  · exact krefB_gt hs β x
  · unfold krefPat at ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    have := List.findIdx_le_length (p := fun y => decide (y = b)) (xs := krefDig x)
    simp only [krefDig, List.length_ofFn] at this
    unfold krefDig
    omega
  · unfold krefTauCols at ha
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp ha
    exact krefB_gt hs β _
  · unfold krefCounts at ha
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp ha
    have := List.count_le_length (a := u) (l := krefRl col β x)
    unfold krefRl at this ⊢
    simp only [List.length_ofFn] at this
    omega

theorem krefTauCols_eq_iff (β β' : Bool) (x y : Fin k → Fin n) :
    krefTauCols col β x = krefTauCols col β' y ↔
      ∀ τ : Fin k → Fin k, col β (x ∘ τ) = col β' (y ∘ τ) := by
  unfold krefTauCols
  rw [List.map_inj_left]
  exact ⟨fun h τ => h τ (mem_krefTups τ), fun h τ _ => h τ⟩

theorem krefSig_eq_iff (hs : KrefSmall col) (β β' : Bool) (x y : Fin k → Fin n) :
    krefSig col β x = krefSig col β' y ↔ KrefRef col (β, x) (β', y) := by
  unfold krefSig KrefRef
  simp only
  rw [← krefPat_eq_iff, ← krefTauCols_eq_iff, ← krefCounts_eq_iff' hs]
  have l1 : ∀ z : Fin k → Fin n, (krefPat z).length = k := by simp [krefPat, krefDig]
  have l2 : ∀ (γ : Bool) (z : Fin k → Fin n), (krefTauCols col γ z).length = k ^ k := by
    simp [krefTauCols, length_krefTups]
  constructor
  · intro h
    obtain ⟨h, h4⟩ := List.append_inj h (by simp [l1, l2])
    obtain ⟨h, h3⟩ := List.append_inj h (by simp [l1])
    obtain ⟨h1, h2⟩ := List.append_inj h rfl
    exact ⟨List.singleton_inj.mp h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rw [h1, h2, h3, h4]

theorem krefSCode_mem (β : Bool) (x : Fin k → Fin n) :
    krefHorner (krefB n k) (krefSig col β x) ∈ krefSAll col := by
  unfold krefSAll
  have hm : krefHorner (krefB n k) (krefSig col β x) ∈ krefSCodes col β :=
    List.mem_map.mpr ⟨x, mem_krefTups x, rfl⟩
  cases β
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ hm

/-- **One round.** Two tuples get the same new color exactly when `KrefRef` holds. -/
theorem krefStep_eq_iff (hs : KrefSmall col) (β β' : Bool) (x y : Fin k → Fin n) :
    krefStep col β x = krefStep col β' y ↔ KrefRef col (β, x) (β', y) := by
  rw [← krefSig_eq_iff hs]
  constructor
  · intro h
    have h1 := krefRank_inj (krefSCode_mem β x) (krefSCode_mem β' y) h
    exact krefHorner_inj (by unfold krefB; omega) (by rw [length_krefSig, length_krefSig])
      (krefSig_lt hs β x) (krefSig_lt hs β' y) h1
  · intro h
    unfold krefStep
    rw [h]

theorem length_krefSAll : (krefSAll col).length = 2 * n ^ k := by
  simp [krefSAll, krefSCodes, length_krefTups]; ring

/-- The new colors are below `2 n^k`. -/
theorem krefStep_lt (β : Bool) (x : Fin k → Fin n) : krefStep col β x < 2 * n ^ k := by
  rw [← length_krefSAll (col := col)]
  exact krefRank_lt_length (krefSCode_mem β x)

end Sig

end GI.Impl
