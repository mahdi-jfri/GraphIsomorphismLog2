import Workspace.Impl.CamXOrbits
import Workspace.Cited.AlgoPermGroups
import Workspace.AlternatingSimple

/-!
# The factors of the socle, by chief series and centralizers

The main fact is `camX_normal_prod`: for `m ≥ 5`, a subgroup of `camProd e S` that is normalized
by `camProd e S` is `camProd e T` for some `T ⊆ S`. The proof is the usual one for a power of a
nonabelian simple group `T₀ = Alt(m)`. If an element `y` of the subgroup `K` is nontrivial in
coordinate `i`, pick `b ∈ T₀` not commuting with `y i` (the center of `T₀` is trivial). The
commutator of `y` with `b` placed in coordinate `i` lies in `K` and lives in coordinate `i` only.
So the elements of `K` that live in coordinate `i` form a nontrivial normal subgroup of `T₀`,
which is all of `T₀`.

From it we get:
* `camX_factor_chief_last`: the last nontrivial term of a chief series of `camProd e S` is one
  factor `camProd e {i}`, because it is a minimal normal subgroup;
* `camX_centralizer`: the centralizer of the factor `i` in `camProd e S` is `camProd e (S.erase i)`.
`camX_chief_min` (minimality of the last nontrivial term of a chief series) and
`camX_normal_prod` are used again in `CamXSocle`.
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ} {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}

/-! ### Facts on chief series -/

/-- The terms of a chief series of `G` lie in `G`. -/
theorem camX_chief_le {G : Subgroup (Perm (Fin n))} {Hs : List (Subgroup (Perm (Fin n)))}
    (hHs : IsChiefSeries G Hs) : ∀ j (hj : j < Hs.length), Hs[j] ≤ G := by
  obtain ⟨h1, -, -, h4⟩ := hHs
  intro j
  induction j with
  | zero =>
    intro hj
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hj] at h1
    exact (Option.some.inj h1).le
  | succ j ih =>
    intro hj
    exact (h4 j hj).1.le.trans (ih (by omega))

/-- The last nontrivial term of a chief series of `G ≠ 1` is a minimal normal subgroup. -/
theorem camX_chief_min {G : Subgroup (Perm (Fin n))} {Hs : List (Subgroup (Perm (Fin n)))}
    (hHs : IsChiefSeries G Hs) (hG : G ≠ ⊥) :
    ∃ M : Subgroup (Perm (Fin n)), Hs[Hs.length - 2]? = some M ∧ M ≤ G ∧ M ≠ ⊥ ∧
      (∀ x ∈ G, ∀ y ∈ M, x * y * x⁻¹ ∈ M) ∧
      ∀ N : Subgroup (Perm (Fin n)), N ≤ M → (∀ x ∈ G, ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
        N = ⊥ ∨ N = M := by
  have hle := camX_chief_le hHs
  obtain ⟨h1, h2, h3, h4⟩ := hHs
  have hlen : 2 ≤ Hs.length := by
    match Hs, h1, h2 with
    | [], h1, _ => simp at h1
    | [a], h1, h2 =>
      simp only [List.head?_cons, Option.some.injEq] at h1
      simp only [List.getLast?_singleton, Option.some.injEq] at h2
      exact absurd (h1.symm.trans h2) hG
    | _ :: _ :: _, _, _ => simp
  obtain ⟨j, hj⟩ : ∃ j, Hs.length = j + 2 := ⟨Hs.length - 2, by omega⟩
  rw [List.getLast?_eq_getElem?, hj, show j + 2 - 1 = j + 1 by omega,
    List.getElem?_eq_getElem (by omega)] at h2
  have hb : Hs[j + 1]'(by omega) = ⊥ := Option.some.inj h2
  have hstep := h4 j (by omega)
  refine ⟨Hs[j]'(by omega), ?_, hle j (by omega), ?_, h3 _ (List.getElem_mem _), ?_⟩
  · rw [show Hs.length - 2 = j by omega, List.getElem?_eq_getElem]
  · rw [← bot_lt_iff_ne_bot, ← hb]
    exact hstep.1
  · intro N hN hn
    rcases hstep.2 N (hb ▸ bot_le) hN hn with h | h
    · exact Or.inl (h.trans hb)
    · exact Or.inr h

/-! ### The coordinate products -/

/-- The product of `Alt(m)` in the coordinates of `S`, before reading it through `e`. -/
def camX_pi (m : ℕ) {r : ℕ} (S : Finset (Fin r)) : Subgroup (Fin r → Perm (Fin m)) :=
  Subgroup.pi Set.univ fun i => if i ∈ S then alternatingGroup (Fin m) else ⊥

theorem camX_prod_eq (S : Finset (Fin r)) : camProd e S = (camX_pi m S).map (camHom e) := rfl

theorem camX_mulSingle_mem_pi {S : Finset (Fin r)} {i : Fin r} (hi : i ∈ S) {a : Perm (Fin m)}
    (ha : a ∈ alternatingGroup (Fin m)) : Pi.mulSingle i a ∈ camX_pi m S := by
  refine camX_mem_pi.mpr fun j => ⟨fun _ => ?_, fun hj => ?_⟩
  · by_cases hji : j = i
    · subst hji
      simpa using ha
    · rw [Pi.mulSingle_eq_of_ne hji]
      exact Subgroup.one_mem _
  · have hji : j ≠ i := fun h => hj (h ▸ hi)
    rw [Pi.mulSingle_eq_of_ne hji]

/-- The center of `Alt(m)` is trivial for `m ≥ 5`. -/
theorem camX_alt_center (hm : 5 ≤ m) {c : Perm (Fin m)} (hc : c ∈ alternatingGroup (Fin m))
    (h : ∀ a ∈ alternatingGroup (Fin m), a * c = c * a) : c = 1 := by
  haveI := GI.AlternatingSimple.isSimple_fin hm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (alternatingGroup (Fin m))) inferInstance with hb | ht
  · have hmem : (⟨c, hc⟩ : alternatingGroup (Fin m)) ∈ Subgroup.center _ :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h g g.2)
    rw [hb, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · obtain ⟨f, t, hft⟩ := GI.AlternatingSimple.nonabelian_fin hm
    have hmem : t ∈ Subgroup.center _ := ht ▸ Subgroup.mem_top t
    exact absurd ((Subgroup.mem_center_iff.mp hmem) f) hft

/-- The subgroups of `Alt(m)^S` normalized by `Alt(m)^S` are the sub-products. -/
theorem camX_normal_pi (hm : 5 ≤ m) {S : Finset (Fin r)} {K : Subgroup (Fin r → Perm (Fin m))}
    (hK : K ≤ camX_pi m S) (hnorm : ∀ x ∈ camX_pi m S, ∀ y ∈ K, x * y * x⁻¹ ∈ K) :
    ∃ T ⊆ S, K = camX_pi m T := by
  classical
  haveI := GI.AlternatingSimple.isSimple_fin hm
  refine ⟨S.filter fun i => ∃ y ∈ K, y i ≠ 1, Finset.filter_subset _ _, le_antisymm ?_ ?_⟩
  · -- An element of `K` is trivial in the coordinates where all of `K` is trivial.
    intro y hy
    have hyS := camX_mem_pi.mp (hK hy)
    refine camX_mem_pi.mpr fun i => ⟨fun hi => (hyS i).1 (Finset.mem_filter.mp hi).1,
      fun hi => ?_⟩
    by_cases hiS : i ∈ S
    · by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨hiS, y, hy, hne⟩)
    · exact (hyS i).2 hiS
  · -- In a coordinate where `K` is nontrivial, `K` contains all of `Alt(m)`.
    refine Subgroup.pi_le_iff.mpr fun i => ?_
    by_cases hi : i ∈ S.filter fun i => ∃ y ∈ K, y i ≠ 1
    · simp only [hi, if_true]
      obtain ⟨hiS, y, hy, hyi⟩ := Finset.mem_filter.mp hi
      have hsingle : ∀ b ∈ alternatingGroup (Fin m), Pi.mulSingle i b ∈ camX_pi m S :=
        fun b hb => camX_mulSingle_mem_pi hiS hb
      let L : Subgroup (alternatingGroup (Fin m)) :=
        K.comap ((MonoidHom.mulSingle (fun _ : Fin r => Perm (Fin m)) i).comp
          (alternatingGroup (Fin m)).subtype)
      have hmemL : ∀ a : alternatingGroup (Fin m), a ∈ L ↔ Pi.mulSingle i (a : Perm (Fin m)) ∈ K :=
        fun _ => Iff.rfl
      have hLn : L.Normal := ⟨fun a ha b => by
        rw [hmemL] at ha ⊢
        have hc := hnorm _ (hsingle b b.2) _ ha
        rwa [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul] at hc⟩
      have hyA : y i ∈ alternatingGroup (Fin m) := (camX_mem_pi.mp (hK hy) i).1 hiS
      obtain ⟨b, hb, hbne⟩ : ∃ b ∈ alternatingGroup (Fin m), b * y i ≠ y i * b := by
        by_contra hcon
        push Not at hcon
        exact hyi (camX_alt_center hm hyA hcon)
      have hz : Pi.mulSingle i b * y * (Pi.mulSingle i b)⁻¹ * y⁻¹ =
          Pi.mulSingle i (b * y i * b⁻¹ * (y i)⁻¹) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Pi.mulSingle_eq_of_ne hj]
      have hcA : b * y i * b⁻¹ * (y i)⁻¹ ∈ alternatingGroup (Fin m) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hyA)
          (Subgroup.inv_mem _ hb)) (Subgroup.inv_mem _ hyA)
      have hzL : (⟨_, hcA⟩ : alternatingGroup (Fin m)) ∈ L := by
        rw [hmemL]
        change Pi.mulSingle i (b * y i * b⁻¹ * (y i)⁻¹) ∈ K
        rw [← hz]
        exact K.mul_mem (hnorm _ (hsingle b hb) _ hy) (K.inv_mem hy)
      have hLtop : L = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L hLn with hbot | htop
        · exfalso
          rw [hbot, Subgroup.mem_bot] at hzL
          have h1 : b * y i * b⁻¹ * (y i)⁻¹ = 1 := congrArg Subtype.val hzL
          exact hbne (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1))
        · exact htop
      rw [Subgroup.map_le_iff_le_comap]
      intro a ha
      exact (hmemL ⟨a, ha⟩).mp (hLtop ▸ Subgroup.mem_top _)
    · simp only [hi, if_false, Subgroup.map_bot]
      exact bot_le

/-- **The `N`-normal subgroups of `N = camProd e S` are the `camProd e T`, `T ⊆ S`.** -/
theorem camX_normal_prod (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m) {S : Finset (Fin r)}
    {M : Subgroup (Perm (Fin n))} (hM : M ≤ camProd e S)
    (hnorm : ∀ x ∈ camProd e S, ∀ y ∈ M, x * y * x⁻¹ ∈ M) : ∃ T ⊆ S, M = camProd e T := by
  have hinj := camX_camHom_injective (e := e) hk1 hkm
  have hle : M.comap (camHom e) ≤ camX_pi m S := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (hM hy)
    exact hinj hxy ▸ hx
  have hn : ∀ x ∈ camX_pi m S, ∀ y ∈ M.comap (camHom e), x * y * x⁻¹ ∈ M.comap (camHom e) := by
    intro x hx y hy
    change camHom e (x * y * x⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (Subgroup.mem_map_of_mem _ hx) _ hy
  obtain ⟨T, hTS, hT⟩ := camX_normal_pi hm hle hn
  refine ⟨T, hTS, ?_⟩
  rw [camX_prod_eq, ← hT, Subgroup.map_comap_eq_self]
  exact hM.trans (Subgroup.map_le_range _ _)

theorem camX_prod_mono {T T' : Finset (Fin r)} (h : T ⊆ T') : camProd e T ≤ camProd e T' := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := camX_mem_prod.mp hg
  refine camX_mem_prod.mpr ⟨a, fun i => ⟨fun hi => ?_, fun hi => (ha i).2 fun hiT => hi (h hiT)⟩,
    rfl⟩
  by_cases hiT : i ∈ T
  · exact (ha i).1 hiT
  · rw [(ha i).2 hiT]
    exact Subgroup.one_mem _

theorem camX_prod_empty : camProd e (∅ : Finset (Fin r)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨a, ha, rfl⟩ := camX_mem_prod.mp hg
  have : a = 1 := funext fun i => (ha i).2 (Finset.notMem_empty i)
  rw [this, map_one]
  exact Subgroup.one_mem _

/-- Every `camProd e T` is normalized by every `camProd e S` (indeed by all of `camHom e`). -/
theorem camX_prod_normal (S T : Finset (Fin r)) :
    ∀ x ∈ camProd e S, ∀ y ∈ camProd e T, x * y * x⁻¹ ∈ camProd e T := by
  intro x hx y hy
  obtain ⟨a, -, rfl⟩ := camX_mem_prod.mp hx
  obtain ⟨b, hb, rfl⟩ := camX_mem_prod.mp hy
  refine camX_mem_prod.mpr ⟨a * b * a⁻¹, fun i => ⟨fun hi => ?_, fun hi => ?_⟩, by
    rw [map_mul, map_mul, map_inv]⟩
  · exact (alternatingGroup.normal (α := Fin m)).conj_mem _ ((hb i).1 hi) (a i)
  · change a i * b i * (a i)⁻¹ = 1
    rw [(hb i).2 hi, mul_one, mul_inv_cancel]

theorem camX_prod_ne_bot (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m) (i : Fin r) :
    camProd e {i} ≠ ⊥ := by
  intro h
  have hc := camX_card_prod (e := e) (by omega) hk1 hkm {i}
  rw [h, Subgroup.card_bot, Finset.card_singleton, pow_one] at hc
  have h5 : Nat.factorial 5 ≤ m.factorial := Nat.factorial_le hm
  have : Nat.factorial 5 = 120 := by decide
  omega

theorem camX_factor_chief_last (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m)
    {S : Finset (Fin r)} (hS : S.Nonempty) {Hs : List (Subgroup (Perm (Fin n)))}
    (hHs : IsChiefSeries (camProd e S) Hs) :
    ∃ i ∈ S, Hs[Hs.length - 2]? = some (camProd e {i}) := by
  obtain ⟨i₀, hi₀⟩ := hS
  have hne : camProd e S ≠ ⊥ := fun h => camX_prod_ne_bot hm hk1 hkm i₀
    (le_bot_iff.mp (h ▸ camX_prod_mono (Finset.singleton_subset_iff.mpr hi₀)))
  obtain ⟨M, hMeq, hMG, hMne, hMn, hMmin⟩ := camX_chief_min hHs hne
  obtain ⟨T, hTS, rfl⟩ := camX_normal_prod hm hk1 hkm hMG fun x hx y hy => hMn x hx y hy
  obtain ⟨i, hi⟩ : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hMne camX_prod_empty
  refine ⟨i, hTS hi, ?_⟩
  rw [hMeq]
  rcases hMmin (camProd e {i}) (camX_prod_mono (Finset.singleton_subset_iff.mpr hi))
      (camX_prod_normal S {i}) with h | h
  · exact absurd h (camX_prod_ne_bot hm hk1 hkm i)
  · rw [h]

/-- A tuple concentrated in coordinate `i`, read through `e`, lies in the factor `i`. -/
theorem camX_single_mem {i : Fin r} {a : Perm (Fin m)} (ha : a ∈ alternatingGroup (Fin m)) :
    camHom e (Pi.mulSingle i a) ∈ camProd e {i} :=
  Subgroup.mem_map_of_mem _ (camX_mulSingle_mem_pi (Finset.mem_singleton_self i) ha)

theorem camX_centralizer (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m)
    {S : Finset (Fin r)} {i : Fin r} (hi : i ∈ S) :
    {g | g ∈ camProd e S ∧ ∀ x ∈ camProd e {i}, g * x * g⁻¹ * x⁻¹ ∈ (⊥ : Subgroup (Perm (Fin n)))}
      = (camProd e (S.erase i) : Set (Perm (Fin n))) := by
  have hinj := camX_camHom_injective (e := e) hk1 hkm
  ext g
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_bot]
  constructor
  · rintro ⟨hg, hc⟩
    obtain ⟨h, hh, rfl⟩ := camX_mem_prod.mp hg
    have hhi : h i = 1 := by
      refine camX_alt_center hm ((hh i).1 hi) fun a ha => ?_
      have h1 := hc _ (camX_single_mem (e := e) (i := i) ha)
      have h2 : camHom e (h * Pi.mulSingle i a * h⁻¹ * (Pi.mulSingle i a)⁻¹) = 1 := by
        simpa only [map_mul, map_inv] using h1
      have h3 := (injective_iff_map_eq_one' _).mp hinj _ |>.mp h2
      have h4 := congrFun (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)) i
      simp only [Pi.mul_apply, Pi.mulSingle_eq_same] at h4
      exact h4.symm
    refine camX_mem_prod.mpr ⟨h, fun j => ⟨fun hj => (hh j).1 (Finset.mem_of_mem_erase hj),
      fun hj => ?_⟩, rfl⟩
    by_cases hji : j = i
    · rw [hji]
      exact hhi
    · exact (hh j).2 fun hjS => hj (Finset.mem_erase.mpr ⟨hji, hjS⟩)
  · intro hg
    refine ⟨camX_prod_mono (Finset.erase_subset i S) hg, fun x hx => ?_⟩
    obtain ⟨h, hh, rfl⟩ := camX_mem_prod.mp hg
    obtain ⟨s, hs, rfl⟩ := camX_mem_prod.mp hx
    have hcomm : h * s * h⁻¹ * s⁻¹ = 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        have : h j = 1 := (hh j).2 (by simp)
        simp [this]
      · have : s j = 1 := (hs j).2 (by simpa using hj)
        simp [this]
    simpa only [map_mul, map_inv, map_one] using congrArg (camHom e) hcomm

end GI.Impl
