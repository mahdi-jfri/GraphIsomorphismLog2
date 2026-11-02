import Workspace.Impl.Cases
import Workspace.Lang.Lib.NatList
import Workspace.Lang.Prims.Ops

/-!
# A largest orbit, in `GI.Lang`

Section 3.2: "We process a largest orbit of the group at the start of a chain first". The
orbit chain of `Continue` (`Run.orbitStop`, `Run.orbitChain`) needs a largest orbit `D₁` of `G`
in the active domain `D`, as the indicators of `D₁` and of `D \ D₁`.

`loFuns b` (62 functions at base `b`) does this on `[encGroup gs, ind D]`, where `gs` generates
the image of `G` and `ind D` is the indicator of `D` (`DomVal`):

1. the orbit labels `lab` of the group (`orbitFuns`; `lab x = lab y` exactly when `x, y` lie in
   one orbit);
2. for each point `i`, the size `[i ∈ D] · #{j | lab j = lab i}`, which is the size of the
   orbit of `i` when `i ∈ D` (`countFuns`);
3. the largest size `M` (`maxFuns`) and the first point `a` with size `M` (`findEqFuns`);
4. the indicator of the orbit of `a`, `[lab j = lab a]` (`eqIndFuns`), and the indicator of
   `D` minus it.

`lo_spec`: the result is `[ind D₁, ind (D \ D₁)]` for a largest orbit `D₁`, at cost at most
`loK (k + 1)^15` on `k` points with at most `k²` generators. The exponent comes from the orbit
program (`orbitK ((m + 1)(k + 1))^5` with `m ≤ k² + 1`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {Ω : Type} {k : ℕ}

/-! ### Indicators -/

open Classical in
/-- The indicator of a set of positions, as a function on `Fin k`. -/
noncomputable def indF (e : Ω ≃ Fin k) (D : Set Ω) : Fin k → ℕ :=
  fun i => if e.symm i ∈ D then 1 else 0

/-- The value of the indicator of a set (`DomVal`). -/
noncomputable def indVal (e : Ω ≃ Fin k) (D : Set Ω) : Val := encFun (indF e D)

theorem domVal_indVal (e : Ω ≃ Fin k) (D : Set Ω) : DomVal e (indVal e D) D := rfl

theorem DomVal.eq_indVal {e : Ω ≃ Fin k} {v : Val} {D : Set Ω} (h : DomVal e v D) :
    v = indVal e D := h

theorem indF_le_one (e : Ω ≃ Fin k) (D : Set Ω) (i : Fin k) : indF e D i ≤ 1 := by
  unfold indF; split_ifs <;> omega

/-! ### Orbits through the enumeration -/

theorem gens_cons_one {n : ℕ} (gs : List (Perm (Fin n))) : gens (1 :: gs) = gens gs := by
  unfold gens
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g hg
    simp only [List.mem_cons, Set.mem_setOf_eq] at hg
    rcases hg with rfl | hg
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg

theorem mem_groupFin {e : Ω ≃ Fin k} {G : Subgroup (Perm Ω)} {g : Perm (Fin k)} :
    g ∈ groupFin e G ↔ ∃ h ∈ G, toFin e h = g := by
  simp [groupFin]

theorem toFin_apply (e : Ω ≃ Fin k) (h : Perm Ω) (x : Fin k) :
    toFin e h x = e (h (e.symm x)) := rfl

/-- Two points lie in one orbit of the generated group exactly when the positions lie in one
orbit of `G`. -/
theorem mem_genOrbit_iff {e : Ω ≃ Fin k} {G : Subgroup (Perm Ω)} {gs : List (Perm (Fin k))}
    (hgs : gens gs = groupFin e G) (x y : Fin k) :
    y ∈ genOrbit (1 :: gs) x ↔ e.symm y ∈ orb G (e.symm x) := by
  rw [mem_genOrbit]
  have hg : genGroup (1 :: gs) = groupFin e G := (gens_cons_one gs).trans hgs
  rw [hg]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h, hh, rfl⟩ := mem_groupFin.1 hg
    exact ⟨h, hh, by simp [toFin_apply]⟩
  · rintro ⟨h, hh, hy⟩
    refine ⟨toFin e h, mem_groupFin.2 ⟨h, hh, rfl⟩, ?_⟩
    rw [toFin_apply, hy, Equiv.apply_symm_apply]

theorem card_filter_finRange (p : Fin k → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ((List.finRange k).filter (fun j => decide (p j))).length := by
  rw [Fin.univ_def]; rfl

theorem count_map_finRange (lab : Fin k → ℕ) (a : ℕ) :
    ((List.finRange k).map lab).count a = (Finset.univ.filter (fun j => lab j = a)).card := by
  rw [card_filter_finRange, List.count_eq_length_filter, List.filter_map, List.length_map]
  congr 2

/-- The number of points with the label of `i` is the size of the orbit of `i`. -/
theorem count_lab_eq {e : Ω ≃ Fin k} {G : Subgroup (Perm Ω)} {gs : List (Perm (Fin k))}
    (hgs : gens gs = groupFin e G) {lab : Fin k → ℕ}
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit (1 :: gs) x) (i : Fin k) :
    ((List.finRange k).map lab).count (lab i) = Nat.card (orb G (e.symm i)) := by
  classical
  rw [count_map_finRange, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun j => ⟨e.symm j.1, ?_⟩, fun w => ⟨e w.1, ?_⟩, fun j => ?_, fun w => ?_⟩
  · have := (hlab i j.1).1 j.2.symm
    exact (mem_genOrbit_iff hgs i j.1).1 this
  · have h := (mem_genOrbit_iff hgs i (e w.1)).2 (by simpa using w.2)
    exact ((hlab i _).2 h).symm
  · simp
  · simp

/-! ### The program -/

/-- The size of the orbit of a point of the domain: on `[[labs, ind], i]`,
`ind[i] · count(labs[i], labs)`. -/
def sizeF (cnt : ℕ) : Expr :=
  .arith .mul (.get (.get (arg 0) (.nat 1)) (arg 1))
    (.call cnt (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 0))))

/-- The difference of two indicators: on `[[u, w], i]`, `u[i] - w[i]`. -/
def subF : Expr :=
  .arith .sub (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (.get (arg 0) (.nat 1)) (arg 1))

/-- The body of the largest-orbit function. -/
def loBody (b : ℕ) : Expr :=
  .letE (.call (b + 1) (arg 0))
  (.letE (.call (b + 33) (.length (.var 1)))
  (.letE (.call (b + 36) (mk2 (mk2 (.var 1) (arg 1)) (.var 2)))
  (.letE (.call (b + 45) (.var 3))
  (.letE (.call (b + 50) (mk2 (.var 4) (.var 3)))
  (.letE (.call (b + 54) (mk2 (.get (.var 1) (.var 5)) (.var 1)))
  (.letE (.call (b + 58) (mk2 (mk2 (arg 1) (.var 6)) (.var 2)))
  (mk2 (.var 6) (.var 7))))))))

/-- The largest-orbit module at base `b` (62 functions). -/
def loFuns (b : ℕ) : List Expr :=
  [loBody b] ++ orbitFuns (b + 1) ++ rangeFuns (b + 33) ++ mapFuns (b + 36) (b + 39) ++
    [sizeF (b + 40)] ++ countFuns (b + 40) ++ maxFuns (b + 45) ++ findEqFuns (b + 50) ++
    eqIndFuns (b + 54) ++ mapFuns (b + 58) (b + 61) ++ [subF]

theorem length_loFuns (b : ℕ) : (loFuns b).length = 62 := by
  simp [loFuns, orbitFuns, rangeFuns, invMapFuns, mapFuns, loopFuns, invFuns, findFuns, iterFuns,
    roundFoldFuns, foldlFuns, minMapFuns, countFuns, filterFuns, maxFuns, findEqFuns, eqIndFuns]

/-- The cost constant of the largest-orbit module. -/
def loK : ℕ := 10 ^ 12

/-! ### The largest orbit from the sizes -/

/-- The sizes computed by the program, and the largest orbit they give. -/
theorem largest_of_sizes [Finite Ω] (e : Ω ≃ Fin k) {G : Subgroup (Perm Ω)} {D : Set Ω}
    (hD : Invariant G D) (hne : D.Nonempty) {gs : List (Perm (Fin k))}
    (hgs : gens gs = groupFin e G) {lab : Fin k → ℕ}
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit (1 :: gs) x) :
    let sz : Fin k → ℕ := fun i => indF e D i * ((List.finRange k).map lab).count (lab i)
    let M := ((List.finRange k).map sz).foldl max 0
    ∃ ha : ((List.finRange k).map sz).findIdx (fun x => decide (x = M)) < k,
      let a : Fin k := ⟨_, ha⟩
      e.symm a ∈ D ∧ sz a = M ∧ 1 ≤ M ∧ M ≤ k ∧ (∀ i, sz i ≤ M) ∧
      (∀ i, sz i ≤ k) ∧
      ∀ b ∈ D, Nat.card {w | ∃ g ∈ G, g b = w} ≤ Nat.card (orb G (e.symm a)) := by
  classical
  intro sz M
  have hsz : ∀ i, sz i = if e.symm i ∈ D then Nat.card (orb G (e.symm i)) else 0 := by
    intro i
    simp only [sz, indF, count_lab_eq hgs hlab i]
    split_ifs <;> simp
  have hcard_le : ∀ i, Nat.card (orb G (e.symm i)) ≤ k := by
    intro i
    have := Nat.card_le_card_of_injective (fun w : orb G (e.symm i) => e w.1)
      (fun x y h => Subtype.ext (e.injective h))
    simpa using this
  have hszk : ∀ i, sz i ≤ k := by
    intro i; rw [hsz]; split_ifs
    · exact hcard_le i
    · exact Nat.zero_le _
  obtain ⟨hM0, hMall⟩ := le_foldl_max ((List.finRange k).map sz) 0
  have hMle : ∀ i, sz i ≤ M := fun i => hMall _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
  obtain ⟨v, hv⟩ := hne
  have hpos : 1 ≤ sz (e v) := by
    rw [hsz, if_pos (by simpa using hv)]
    haveI : Finite (orb G (e.symm (e v))) := Subtype.finite
    exact Nat.card_pos_iff.2 ⟨⟨⟨e.symm (e v), 1, G.one_mem, rfl⟩⟩, inferInstance⟩
  have hM1 : 1 ≤ M := hpos.trans (hMle _)
  have hMk : M ≤ k := foldl_max_le (Nat.zero_le _) fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx; exact hszk i
  have hMmem : M ∈ (List.finRange k).map sz := by
    rcases foldl_max_mem ((List.finRange k).map sz) 0 with h | h
    · exact absurd h (by omega)
    · exact h
  have ha : ((List.finRange k).map sz).findIdx (fun x => decide (x = M)) < k := by
    have := List.findIdx_lt_length_of_exists (p := fun x => decide (x = M)) ⟨M, hMmem, by simp⟩
    simpa using this
  refine ⟨ha, ?_⟩
  intro a
  have hsa : sz a = M := by
    have := List.findIdx_getElem (p := fun x => decide (x = M)) (xs := (List.finRange k).map sz)
      (w := by simpa using ha)
    simpa [a] using this
  have haD : e.symm a ∈ D := by
    by_contra hn
    have : sz a = 0 := by rw [hsz, if_neg hn]
    omega
  refine ⟨haD, hsa, hM1, hMk, hMle, hszk, fun b hb => ?_⟩
  have h1 := hMle (e b)
  rw [hsz, if_pos (by simpa using hb), Equiv.symm_apply_apply] at h1
  have h2 := hsa
  rw [hsz, if_pos haD] at h2
  change Nat.card (orb G b) ≤ _
  omega

/-! ### The specification -/

theorem pow_le_pow15 (X : ℕ) (hX : 1 ≤ X) {j : ℕ} (hj : j ≤ 15) : X ^ j ≤ X ^ 15 :=
  Nat.pow_le_pow_right hX hj

/-- `k · (c X³) ≤ c X⁴` for `X = k + 1`. -/
theorem mul_X3_le (k c : ℕ) : k * (c * (k + 1) ^ 3) ≤ c * (k + 1) ^ 4 := by
  have : k * (c * (k + 1) ^ 3) ≤ (k + 1) * (c * (k + 1) ^ 3) := Nat.mul_le_mul_right _ (by omega)
  calc k * (c * (k + 1) ^ 3) ≤ (k + 1) * (c * (k + 1) ^ 3) := this
    _ = c * (k + 1) ^ 4 := by ring

theorem mapK_X_le (k c : ℕ) {Y : ℕ} (hY : Y ≤ c * (k + 1) ^ 2) :
    mapK * (k + 1) * Y ≤ 1000 * c * (k + 1) ^ 3 := by
  calc mapK * (k + 1) * Y ≤ mapK * (k + 1) * (c * (k + 1) ^ 2) := Nat.mul_le_mul_left _ hY
    _ = 1000 * c * (k + 1) ^ 3 := by simp only [mapK]; ring

/-- **The largest orbit.** On `[encGroup gs, ind D]`, where `gs` generates the image of `G` and
`D` is a nonempty `G`-invariant set, `loFuns` returns `[ind D₁, ind (D \ D₁)]` for a largest
orbit `D₁` of `G` in `D`. -/
theorem lo_spec {P : Program} {b : ℕ} (h : P.HasAt b (loFuns b)) (e : Ω ≃ Fin k)
    {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D) (hne : D.Nonempty)
    {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) (hl : gs.length ≤ k ^ 2) :
    ∃ D₁ : Set Ω, D₁ ⊆ D ∧ (∃ a ∈ D, D₁ = {w | ∃ g ∈ G, g a = w}) ∧
      (∀ b ∈ D, Nat.card {w | ∃ g ∈ G, g b = w} ≤ Nat.card D₁) ∧
      FunDet P b (.list [encGroup gs, indVal e D]) (.list [indVal e D₁, indVal e (D \ D₁)])
        (loK * (k + 1) ^ 15) := by
  classical
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  -- The blocks of the module.
  simp only [loFuns] at h
  have hbody : P.funs[b]? = some (loBody b) := h.left.left.left.left.left.left.left.left.left.left.single
  have horb : P.HasAt (b + 1) (orbitFuns (b + 1)) := by
    simpa using h.left.left.left.left.left.left.left.left.left.right
  have hrange : P.HasAt (b + 33) (rangeFuns (b + 33)) := by
    simpa [length_orbitFuns, Nat.add_assoc] using h.left.left.left.left.left.left.left.left.right
  have hmap1 : P.HasAt (b + 36) (mapFuns (b + 36) (b + 39)) := by
    simpa [length_orbitFuns, rangeFuns, loopFuns, Nat.add_assoc] using
      h.left.left.left.left.left.left.left.right
  have hsizeF : P.funs[b + 39]? = some (sizeF (b + 40)) := by
    simpa [length_orbitFuns, rangeFuns, mapFuns, loopFuns, Nat.add_assoc] using
      h.left.left.left.left.left.left.right.single
  have hcount : P.HasAt (b + 40) (countFuns (b + 40)) := by
    simpa [length_orbitFuns, rangeFuns, mapFuns, loopFuns, Nat.add_assoc] using
      h.left.left.left.left.left.right
  have hmax : P.HasAt (b + 45) (maxFuns (b + 45)) := by
    simpa [length_orbitFuns, rangeFuns, mapFuns, loopFuns, countFuns, filterFuns,
      Nat.add_assoc] using h.left.left.left.left.right
  have hfind : P.HasAt (b + 50) (findEqFuns (b + 50)) := by
    simpa [length_orbitFuns, rangeFuns, mapFuns, loopFuns, countFuns, filterFuns, maxFuns,
      foldlFuns, Nat.add_assoc] using h.left.left.left.right
  have heq : P.HasAt (b + 54) (eqIndFuns (b + 54)) := by
    simpa [length_orbitFuns, rangeFuns, mapFuns, loopFuns, countFuns, filterFuns, maxFuns,
      foldlFuns, findEqFuns, findFuns, Nat.add_assoc] using h.left.left.right
  have hmap2 : P.HasAt (b + 58) (mapFuns (b + 58) (b + 61)) := by
    simpa [length_orbitFuns, rangeFuns, mapFuns, loopFuns, countFuns, filterFuns, maxFuns,
      foldlFuns, findEqFuns, findFuns, eqIndFuns, Nat.add_assoc] using h.left.right
  have hsub : P.funs[b + 61]? = some subF := by
    simpa [length_orbitFuns, rangeFuns, mapFuns, loopFuns, countFuns, filterFuns, maxFuns,
      foldlFuns, findEqFuns, findFuns, eqIndFuns, Nat.add_assoc] using h.right.single
  -- The orbit labels and the largest orbit.
  obtain ⟨lab, hlabD, hlab, hlab2⟩ := orbits_spec horb (1 :: gs)
  have hlabk : ∀ x, lab x < k := fun x => (hlab2 x).1
  obtain ⟨ha, haD, hsa, hM1, hMk, hMle, hszk, hlarge⟩ := largest_of_sizes e hD hne hgs hlab
  set sz : Fin k → ℕ := fun i => indF e D i * ((List.finRange k).map lab).count (lab i)
    with hsz_def
  set M := ((List.finRange k).map sz).foldl max 0 with hM_def
  set a : ℕ := ((List.finRange k).map sz).findIdx (fun x => decide (x = M)) with ha_def
  set a' : Fin k := ⟨a, ha⟩ with ha'_def
  set D₁ : Set Ω := orb G (e.symm a') with hD₁
  have hk1 : 1 ≤ k := by have := hMk; omega
  -- The two indicators.
  have hd1 : ∀ i : Fin k, (if lab i = lab a' then 1 else 0) = indF e D₁ i := by
    intro i
    have := (hlab a' i).trans (mem_genOrbit_iff hgs a' i)
    simp only [indF, hD₁]
    by_cases hi : lab i = lab a'
    · rw [if_pos hi, if_pos (this.1 hi.symm)]
    · rw [if_neg hi, if_neg fun h' => hi (this.2 h').symm]
  have hD₁D : D₁ ⊆ D := orb_subset hD haD
  have hd2 : ∀ i : Fin k, indF e D i - indF e D₁ i = indF e (D \ D₁) i := by
    intro i
    simp only [indF, Set.mem_diff]
    by_cases h1 : e.symm i ∈ D₁
    · rw [if_pos h1, if_pos (hD₁D h1)]; simp [h1]
    · rw [if_neg h1]; split_ifs <;> simp_all
  refine ⟨D₁, hD₁D, ⟨e.symm a', haD, rfl⟩, hlarge, ?_⟩
  -- Weights.
  have hX1 : 1 ≤ k + 1 := by omega
  have p2 := pow_le_pow15 (k + 1) hX1 (j := 2) (by norm_num)
  have p3 := pow_le_pow15 (k + 1) hX1 (j := 3) (by norm_num)
  have p4 := pow_le_pow15 (k + 1) hX1 (j := 4) (by norm_num)
  have p6 := pow_le_pow15 (k + 1) hX1 (j := 6) (by norm_num)
  have p12 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ hX1
  have p23 : (k + 1) ^ 2 ≤ (k + 1) ^ 3 := Nat.pow_le_pow_right hX1 (by norm_num)
  have p26 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
  have pk : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hlabs_eq : encFun lab = natList ((List.finRange k).map lab) := encFun_eq_natList lab
  have hlabs_le : ∀ x ∈ (List.finRange k).map lab, x ≤ k := by
    intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx; exact (hlabk i).le
  have hlen_k : ((List.finRange k).map lab).length ≤ k := by simp
  have wlabs : (encFun lab).wt ≤ 5 * (k + 1) ^ 2 := hlabs_eq ▸ wt_natList_le_sq hlabs_le hlen_k
  have wind : ∀ D' : Set Ω, (indVal e D').wt ≤ 5 * (k + 1) ^ 2 := by
    intro D'
    have := wt_encFun_le (indF e D') (B := k) fun i => (indF_le_one e D' i).trans hk1
    have : k * (2 * k + 5) + 4 ≤ 5 * (k + 1) ^ 2 := by nlinarith
    rw [indVal]; omega
  have wgrp : (encGroup gs).wt ≤ 320 * (k + 1) ^ 6 := wt_encGroup_le_sq hl
  have wpts : (encPerm (1 : Perm (Fin k))).wt ≤ 4 * (k + 1) ^ 2 := wt_encPerm_le _
  have hszs_le : ∀ x ∈ (List.finRange k).map sz, x ≤ k := by
    intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx; exact hszk i
  have wszs : (natList ((List.finRange k).map sz)).wt ≤ 5 * (k + 1) ^ 2 :=
    wt_natList_le_sq hszs_le (by simp)
  have wA : (Val.list [encGroup gs, indVal e D]).wt ≤ 700 * (k + 1) ^ 6 := by
    have := wt_list2_le (encGroup gs) (indVal e D)
    have := wind D
    omega
  -- Step 1: the orbit labels.
  have d1 : Det P [.list [encGroup gs, indVal e D]] (.call (b + 1) (arg 0)) (encFun lab)
      (1400 * (k + 1) ^ 6 + 32 * orbitK * (k + 1) ^ 15 + 5 * (k + 1) ^ 2 + 6) := by
    refine (Det.call (Det.arg' (P := P) (vs := [encGroup gs, indVal e D]) (rest := []) (j := 0) rfl)
      hlabD).mono ?_
    have h1 : ((1 :: gs).length + 1) * (k + 1) ≤ 2 * (k + 1) ^ 3 := by
      have := measure_le_of_sq (n := k) hl
      simpa [Nat.add_assoc] using this
    have h2 : orbitK * (((1 :: gs).length + 1) * (k + 1)) ^ 5 ≤ 32 * orbitK * (k + 1) ^ 15 :=
      calc orbitK * (((1 :: gs).length + 1) * (k + 1)) ^ 5 ≤ orbitK * (2 * (k + 1) ^ 3) ^ 5 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 5)
        _ = 32 * orbitK * (k + 1) ^ 15 := by ring
    omega
  -- Step 2: the points.
  have d2 : Det P [.list [encGroup gs, indVal e D], encFun lab] (.call (b + 33) (.length (.var 1)))
      (encPerm (1 : Perm (Fin k))) (5 * (k + 1) ^ 2 + 8010 * (k + 1) ^ 3 + 10 * (k + 1)) := by
    have hv := Det.length (Det.var' (P := P) (env := [.list [encGroup gs, indVal e D], encFun lab])
      (i := 1) (v := .list ((List.finRange k).map fun i => .nat (lab i))) rfl)
    simp only [List.length_map, List.length_finRange] at hv
    refine (Det.call hv (range_det hrange k)).mono ?_
    have : (Val.list ((List.finRange k).map fun i => Val.nat (lab i))).wt = (encFun lab).wt := rfl
    omega
  -- Step 3: the sizes.
  have hf3 : ∀ i : Fin k, FunDet P (b + 39) (.list [.list [encFun lab, indVal e D], .nat i])
      (.nat (sz i)) (countK * (k + 1) ^ 3 + 1000 * (k + 1) ^ 2) := by
    intro i
    have hc : (Val.list [encFun lab, indVal e D]).wt ≤ 20 * (k + 1) ^ 2 + 6 := by
      have := wt_list2_le (encFun lab) (indVal e D); have := wind D; omega
    have hW : (Val.list [.list [encFun lab, indVal e D], .nat i]).wt ≤ 64 * (k + 1) ^ 2 := by
      have := wt_list2_le (.list [encFun lab, indVal e D]) (.nat i)
      have := wt_nat_le i; have := i.isLt; omega
    have g0 := Det.arg' (P := P) (vs := [.list [encFun lab, indVal e D], .nat i]) (rest := [])
      (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [.list [encFun lab, indVal e D], .nat i]) (rest := [])
      (j := 1) rfl
    have gind := Det.get' (Det.get' g0 (Det.nat 1) (v := indVal e D) rfl) g1
      (v := .nat (indF e D i)) (by simp [indVal, encFun])
    have glabs := Det.get' g0 (Det.nat 0) (v := encFun lab) rfl
    have glab := Det.get' glabs g1 (v := .nat (lab i)) (by simp [encFun])
    have hcnt := count_spec hcount (xs := (List.finRange k).map lab) (j := lab i) (B := k)
      hlabs_le (hlabk i).le hlen_k
    rw [← hlabs_eq] at hcnt
    have gcall := Det.call (Det.mk2 glab glabs) hcnt
    refine FunDet.intro hsizeF ((Det.arith' (op := .mul) (z := sz i) gind gcall rfl).mono ?_)
    have w1 := wind D
    have w2 := wt_nat_le (lab i)
    have w3 := wt_nat_le (((List.finRange k).map lab).count (lab i))
    have w4 : ((List.finRange k).map lab).count (lab i) ≤ k :=
      (List.count_le_length).trans hlen_k
    have w5 := wt_nat_le (indF e D i)
    have w6 := indF_le_one e D i
    have w7 : sz i ≤ k := hszk i
    have w8 := wt_list2_le (.nat (lab i)) (encFun lab)
    have w9 := (hlabk i)
    omega
  have d3 : Det P [.list [encGroup gs, indVal e D], encFun lab, encPerm (1 : Perm (Fin k))]
      (.call (b + 36) (mk2 (mk2 (.var 1) (arg 1)) (.var 2))) (encFun sz)
      (2000 * (k + 1) ^ 6 + countK * (k + 1) ^ 4 + 80000 * (k + 1) ^ 3) := by
    have hc := Det.mk2 (Det.mk2 (Det.var' (P := P) (env := [.list [encGroup gs, indVal e D],
      encFun lab, encPerm (1 : Perm (Fin k))]) (i := 1) rfl) (Det.arg' (vs := [encGroup gs,
      indVal e D]) (rest := [encFun lab, encPerm (1 : Perm (Fin k))]) (j := 1) rfl))
      (Det.var' (i := 2) rfl)
    have ht := tabulate_spec (m := k) hmap1 (c := .list [encFun lab, indVal e D])
      (F := fun i => .nat (sz i)) hf3
    refine (Det.call hc ht).mono ?_
    have e1 : (Val.list ((List.finRange k).map fun i => Val.nat (sz i))).wt = (encFun sz).wt := rfl
    have e2 : (encFun fun i : Fin k => (i : ℕ)) = encPerm (1 : Perm (Fin k)) := rfl
    rw [e1, e2]
    have hszw : (encFun sz).wt ≤ 5 * (k + 1) ^ 2 := by
      rw [encFun_eq_natList]; exact wszs
    have hc1 : (Val.list [encFun lab, indVal e D]).wt ≤ 20 * (k + 1) ^ 2 + 6 := by
      have := wt_list2_le (encFun lab) (indVal e D); have := wind D; omega
    have hc2 : (Val.list [.list [encFun lab, indVal e D], encPerm (1 : Perm (Fin k))]).wt ≤
        60 * (k + 1) ^ 2 := by
      have := wt_list2_le (.list [encFun lab, indVal e D]) (encPerm (1 : Perm (Fin k)))
      omega
    have hm := mapK_X_le k 70 (Y := (Val.list [.list [encFun lab, indVal e D],
      encPerm (1 : Perm (Fin k))]).wt + (encFun sz).wt + 1) (by omega)
    have hkB : k * (countK * (k + 1) ^ 3 + 1000 * (k + 1) ^ 2) ≤
        countK * (k + 1) ^ 4 + 1000 * (k + 1) ^ 3 := by
      have := mul_X3_le k countK
      have : k * (1000 * (k + 1) ^ 2) ≤ 1000 * (k + 1) ^ 3 := by
        have : k * (1000 * (k + 1) ^ 2) ≤ (k + 1) * (1000 * (k + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
        calc k * (1000 * (k + 1) ^ 2) ≤ (k + 1) * (1000 * (k + 1) ^ 2) := this
          _ = 1000 * (k + 1) ^ 3 := by ring
      rw [Nat.mul_add]; omega
    have hlist : (Val.list [Val.list [encFun lab, indVal e D], encPerm (1 : Perm (Fin k))]).wt =
      (Val.list [Val.list [encFun lab, indVal e D], encFun fun i : Fin k => (i : ℕ)]).wt := rfl
    have p36 : (k + 1) ^ 3 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
    clear hc ht
    omega
  -- Step 4: the largest size.
  have hszw : (encFun sz).wt ≤ 5 * (k + 1) ^ 2 := by rw [encFun_eq_natList]; exact wszs
  have hMw := wt_nat_le M
  have d4 : Det P [.list [encGroup gs, indVal e D], encFun lab, encPerm (1 : Perm (Fin k)),
      encFun sz] (.call (b + 45) (.var 3)) (.nat M) (100010 * (k + 1) ^ 3) := by
    have hv := Det.var' (P := P) (env := [.list [encGroup gs, indVal e D], encFun lab,
      encPerm (1 : Perm (Fin k)), encFun sz]) (i := 3) (v := natList ((List.finRange k).map sz))
      (by rw [← encFun_eq_natList]; rfl)
    refine (Det.call hv (max_spec hmax (B := k) hszs_le (by simp))).mono ?_
    rw [← encFun_eq_natList]
    rw [← hM_def]
    simp only [maxK]
    omega
  -- Step 5: the first point of largest size.
  have haw := wt_nat_le a
  have d5 : Det P [.list [encGroup gs, indVal e D], encFun lab, encPerm (1 : Perm (Fin k)),
      encFun sz, .nat M] (.call (b + 50) (mk2 (.var 4) (.var 3))) (.nat a)
      (100100 * (k + 1) ^ 3) := by
    have hv := Det.mk2 (Det.var' (P := P) (env := [.list [encGroup gs, indVal e D], encFun lab,
      encPerm (1 : Perm (Fin k)), encFun sz, .nat M]) (i := 4) rfl)
      (Det.var' (i := 3) (v := natList ((List.finRange k).map sz))
      (by rw [← encFun_eq_natList]; rfl))
    refine (Det.call hv (findEq_spec hfind (B := k) hszs_le hMk (by simp))).mono ?_
    have := wt_list2_le (.nat M) (natList ((List.finRange k).map sz))
    rw [← ha_def]
    simp only [findEqK]
    omega
  -- Step 6: the indicator of the orbit of `a`.
  have hd1v : natList (((List.finRange k).map lab).map fun x => if x = lab a' then 1 else 0) =
      indVal e D₁ := by
    simp only [natList, indVal, encFun, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [hd1 i]
  have wD₁ := wind D₁
  have d6 : Det P [.list [encGroup gs, indVal e D], encFun lab, encPerm (1 : Perm (Fin k)),
      encFun sz, .nat M, .nat a] (.call (b + 54) (mk2 (.get (.var 1) (.var 5)) (.var 1)))
      (indVal e D₁) (100200 * (k + 1) ^ 3) := by
    have hl := Det.var' (P := P) (env := [.list [encGroup gs, indVal e D], encFun lab,
      encPerm (1 : Perm (Fin k)), encFun sz, .nat M, .nat a]) (i := 1) rfl
    have hg := Det.get' (x := a) (v := .nat (lab a')) hl (Det.var' (i := 5) rfl)
      (by simp only [encFun, List.getElem?_map]; rw [List.getElem?_eq_getElem (by simp only [List.length_finRange]; exact a'.isLt)]; simp [a'])
    have hv := Det.mk2 hg (Det.var' (P := P) (env := [.list [encGroup gs, indVal e D], encFun lab,
      encPerm (1 : Perm (Fin k)), encFun sz, .nat M, .nat a]) (i := 1)
      (v := natList ((List.finRange k).map lab)) (by rw [← hlabs_eq]; rfl))
    have hspec := eqInd_spec heq (B := k) hlabs_le (hlabk a').le hlen_k hk1
    rw [hd1v] at hspec
    refine (Det.call hv hspec).mono ?_
    have := wt_list2_le (.nat (lab a')) (encFun lab)
    have := wt_nat_le (lab a')
    have := hlabk a'
    have : a < k := ha
    rw [← hlabs_eq]
    simp only [eqIndK]
    omega
  -- Step 7: the indicator of the rest of the domain.
  have hf7 : ∀ i : Fin k, FunDet P (b + 61) (.list [.list [indVal e D, indVal e D₁], .nat i])
      (.nat (indF e (D \ D₁) i)) (500 * (k + 1) ^ 2) := by
    intro i
    have g0 := Det.arg' (P := P) (vs := [.list [indVal e D, indVal e D₁], .nat i]) (rest := [])
      (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [.list [indVal e D, indVal e D₁], .nat i]) (rest := [])
      (j := 1) rfl
    have gu := Det.get' (Det.get' g0 (Det.nat 0) (v := indVal e D) rfl) g1
      (v := .nat (indF e D i)) (by simp [indVal, encFun])
    have gw := Det.get' (Det.get' g0 (Det.nat 1) (v := indVal e D₁) rfl) g1
      (v := .nat (indF e D₁ i)) (by simp [indVal, encFun])
    refine FunDet.intro hsub ((Det.arith' (op := .sub) (z := indF e (D \ D₁) i) gu gw
      (hd2 i)).mono ?_)
    have := wt_list2_le (indVal e D) (indVal e D₁)
    have := wt_list2_le (.list [indVal e D, indVal e D₁]) (.nat i)
    have := wt_nat_le i
    have := i.isLt
    have := wt_nat_le (indF e D i)
    have := wt_nat_le (indF e D₁ i)
    have := indF_le_one e D i
    have := indF_le_one e D₁ i
    have := indF_le_one e (D \ D₁) i
    have := wind D
    omega
  have wD₂ := wind (D \ D₁)
  have d7 : Det P [.list [encGroup gs, indVal e D], encFun lab, encPerm (1 : Perm (Fin k)),
      encFun sz, .nat M, .nat a, indVal e D₁]
      (.call (b + 58) (mk2 (mk2 (arg 1) (.var 6)) (.var 2))) (indVal e (D \ D₁))
      (5000 * (k + 1) ^ 6 + 100000 * (k + 1) ^ 3) := by
    have hc := Det.mk2 (Det.mk2 (Det.arg' (P := P) (vs := [encGroup gs, indVal e D])
      (rest := [encFun lab, encPerm (1 : Perm (Fin k)), encFun sz, .nat M, .nat a, indVal e D₁])
      (j := 1) rfl) (Det.var' (i := 6) rfl)) (Det.var' (i := 2) rfl)
    have ht := tabulate_spec (m := k) hmap2 (c := .list [indVal e D, indVal e D₁])
      (F := fun i => .nat (indF e (D \ D₁) i)) hf7
    refine (Det.call hc ht).mono ?_
    have e1 : (Val.list ((List.finRange k).map fun i => Val.nat (indF e (D \ D₁) i))) =
      indVal e (D \ D₁) := rfl
    have e2 : (encFun fun i : Fin k => (i : ℕ)) = encPerm (1 : Perm (Fin k)) := rfl
    rw [e1, e2]
    have hc1 := wt_list2_le (indVal e D) (indVal e D₁)
    have hc2 := wt_list2_le (.list [indVal e D, indVal e D₁]) (encPerm (1 : Perm (Fin k)))
    have hc3 := wt_list2_le (encGroup gs) (indVal e D)
    have hm := mapK_X_le k 70 (Y := (Val.list [.list [indVal e D, indVal e D₁],
      encPerm (1 : Perm (Fin k))]).wt + (indVal e (D \ D₁)).wt + 1) (by have := wind D; omega)
    have hkB : k * (500 * (k + 1) ^ 2) ≤ 500 * (k + 1) ^ 3 := by
      have : k * (500 * (k + 1) ^ 2) ≤ (k + 1) * (500 * (k + 1) ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      calc k * (500 * (k + 1) ^ 2) ≤ (k + 1) * (500 * (k + 1) ^ 2) := this
        _ = 500 * (k + 1) ^ 3 := by ring
    have p36 : (k + 1) ^ 3 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
    have := wind D
    clear hc ht
    omega
  -- Step 8: the pair.
  have d8 : Det P [.list [encGroup gs, indVal e D], encFun lab, encPerm (1 : Perm (Fin k)),
      encFun sz, .nat M, .nat a, indVal e D₁, indVal e (D \ D₁)] (mk2 (.var 6) (.var 7))
      (.list [indVal e D₁, indVal e (D \ D₁)]) (100 * (k + 1) ^ 2) := by
    refine (Det.mk2 (Det.var' (P := P) (i := 6) rfl) (Det.var' (i := 7) rfl)).mono ?_
    have := wt_list2_le (indVal e D₁) (indVal e (D \ D₁))
    omega
  -- Together.
  have hw2 : (encPerm (1 : Perm (Fin k))).wt ≤ 4 * (k + 1) ^ 2 := wpts
  have hres := wt_list2_le (indVal e D₁) (indVal e (D \ D₁))
  refine FunDet.intro hbody ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5
    (Det.letE d6 (Det.letE d7 d8))))))).mono ?_)
  simp only [orbitK, countK, loK] at *
  omega

end GI.Impl
