/-
**Mathematical objects as values.** The cited algorithms of `Workspace/Cited/Algo*.lean` read and
write groups, cosets, labelings, homomorphisms and series in the value format of
`Workspace.Cited.Encoding`. This file names these formats by predicates that relate a value to
the object it stands for, so that specifications can talk about objects:

* `GroupVal n v G`: `v = encGroup gs` for a list `gs` that generates `G` (the input format of the
  tasks: `[n, [1, g₁, …, g_m]]`);
* `GensVal n v G`: `v = [g₁, …, g_m]` for a list of at most `n²` permutations that generates `G`
  (the output format of the tasks, `GI.Cited.GensOf`);
* `CosetVal n v C`: `v = [x, encGroup gs]` with `C = x • ⟨gs⟩` (a left coset, as in stage 1);
* `PartVal n v R`: `v` is the list of the labels of a labeling whose classes are those of `R`;
  `OrbitVal n v G` is the case of the orbits of `G`, and `ReprVal n v R` the case where the label
  of a point is a point of its class with the same label (a representative);
* `HomVal n n' v G φ`: `v = [encGroup gs, [φ g₁, …, φ g_m]]` for generators `gs` of `G`;
* `SeriesVal n v Hs`: `v` is a list of at most `n² + 1` generating lists of the groups `Hs`, each
  of at most `n²` permutations (`GI.Cited.SeriesOf`).

Each value determines its object (`GroupVal.unique`, …), every object has a value
(`GroupVal.exists`, …), and the sizes and weights are polynomial in `n` and the number of
generators (`size_encGroup`, `wt_encGroup_le`). The output formats have weights bounded by a
polynomial in `n` alone (`GensVal.wt_le`, `labels_wt_le`, `SeriesVal.wt_le`), because the tasks
bound the number of generators and the labels.
-/
import Workspace.Lang.Lib.Orbit
import Workspace.Cited.AlgoPermGroups
import Workspace.CitedChecks.AlgoChecks

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms encGroup encPts gens GensOf)
open Equiv
open scoped Pointwise

/-! ### Injectivity of the basic encodings -/

theorem encGroup_injective {n : ℕ} : Function.Injective (encGroup (n := n)) := by
  intro gs hs h
  have := encPerms_injective h
  simpa using this

/-- The degree is read off from a group encoding. -/
theorem encGroup_deg {n n' : ℕ} {gs : List (Perm (Fin n))} {gs' : List (Perm (Fin n'))}
    (h : encGroup gs = encGroup gs') : n = n' := by
  simp only [encGroup, encPerms, Val.list.injEq, List.cons.injEq, Val.nat.injEq] at h
  exact h.1

/-- The points of a list, as numbers. -/
theorem encPts_eq {n : ℕ} (S : List (Fin n)) :
    encPts S = .list (S.map fun i : Fin n => Val.nat (i : ℕ)) := by
  simp only [encPts, Val.list.injEq]
  induction S with
  | nil => rfl
  | cons a S ih => simp_all

theorem encPts_injective {n : ℕ} : Function.Injective (encPts (n := n)) := by
  intro S T h
  simp only [encPts_eq, Val.list.injEq] at h
  refine List.map_injective_iff.mpr (fun a b hab => ?_) h
  simp only [Val.nat.injEq] at hab
  exact Fin.ext hab

theorem encFun_injective {n : ℕ} : Function.Injective (encFun (n := n)) := by
  intro f g h
  simp only [encFun, Val.list.injEq] at h
  rw [List.map_inj_left] at h
  funext i
  have := h i (List.mem_finRange i)
  simpa using this

/-! ### Sizes and weights -/

theorem size_encPerm {n : ℕ} (σ : Perm (Fin n)) : (encPerm σ).size = 2 * n + 3 :=
  GI.CitedChecks.encPerm_length σ

theorem size_list_encPerm {n : ℕ} (gs : List (Perm (Fin n))) :
    (Val.list (gs.map encPerm)).size = gs.length * (2 * n + 3) + 3 := by
  rw [size_list, length_cellsList, List.map_map]
  have : (gs.map (Val.size ∘ encPerm)) = gs.map fun _ => 2 * n + 3 := by
    refine List.map_congr_left fun g _ => ?_
    simp [size_encPerm]
  rw [this, List.map_const', List.sum_replicate, smul_eq_mul]

/-- The number of cells of a group encoding. -/
theorem size_encGroup {n : ℕ} (gs : List (Perm (Fin n))) :
    (encGroup gs).size = (gs.length + 1) * (2 * n + 3) + 8 := by
  have h := size_list_encPerm (1 :: gs)
  simp only [encGroup, encPerms, size_list, length_cellsList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, size_nat, List.length_cons] at h ⊢
  rw [← length_cellsList] at h ⊢
  omega

theorem wt_encGroup_le {n : ℕ} (gs : List (Perm (Fin n))) :
    (encGroup gs).wt ≤ 40 * ((gs.length + 2) * (n + 1)) ^ 2 := by
  have h1 := wt_list_encPerms_le (1 :: gs)
  have h2 := wt_list2_le (.nat n) (.list ((1 :: gs).map encPerm))
  have h3 := wt_nat_le n
  simp only [List.length_cons] at h1
  have e : (encGroup gs).wt = (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt := rfl
  have h4 : n + 1 ≤ ((gs.length + 2) * (n + 1)) ^ 2 := by
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact this.trans (Nat.le_self_pow (by norm_num) _)
  have h5 : ((gs.length + 1 + 1) * (n + 1)) = (gs.length + 2) * (n + 1) := by ring
  rw [h5] at h1
  omega

theorem wt_encPts_le {n : ℕ} (S : List (Fin n)) : (encPts S).wt ≤ 3 * S.length * (n + 2) + 4 := by
  have h1 := wt_list_le (S.map fun i : Fin n => Val.nat (i : ℕ))
  have h2 : ((S.map fun i : Fin n => Val.nat (i : ℕ)).map Val.wt).sum ≤ S.length * (n + 2) := by
    have := List.sum_le_card_nsmul ((S.map fun i : Fin n => Val.nat (i : ℕ)).map Val.wt) (n + 2) (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp]
      rintro _ i - rfl; have := wt_nat_le (i : ℕ); have := i.isLt; omega)
    simpa using this
  simp only [List.length_map] at h1
  rw [encPts_eq]
  nlinarith

/-! ### Groups -/

/-- `v` encodes generators of `G`, in the input format of the tasks: `v = encGroup gs` with
`⟨gs⟩ = G`. -/
def GroupVal (n : ℕ) (v : Val) (G : Subgroup (Perm (Fin n))) : Prop :=
  ∃ gs : List (Perm (Fin n)), v = encGroup gs ∧ gens gs = G

/-- `v` is a list of at most `n²` generators of `G`, in the output format of the tasks. -/
def GensVal (n : ℕ) (v : Val) (G : Subgroup (Perm (Fin n))) : Prop := GensOf G v

/-- `(m + 1) (n + 1)` with `m ≤ n²` is at most `(n + 1)³`. -/
theorem gens_measure_le {n m : ℕ} (hm : m ≤ n ^ 2) : (m + 1) * (n + 1) ≤ (n + 1) ^ 3 := by
  have : m + 1 ≤ (n + 1) ^ 2 := by
    have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  calc (m + 1) * (n + 1) ≤ (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ this
    _ = (n + 1) ^ 3 := by ring

/-- A list of at most `n²` permutations weighs at most `13 (n + 1)⁶`. -/
theorem wt_list_encPerms_le_sq {n : ℕ} {hs : List (Perm (Fin n))} (hl : hs.length ≤ n ^ 2) :
    (Val.list (hs.map encPerm)).wt ≤ 13 * (n + 1) ^ 6 := by
  have h1 := wt_list_encPerms_le hs
  have h2 : ((hs.length + 1) * (n + 1)) ^ 2 ≤ (n + 1) ^ 6 :=
    calc ((hs.length + 1) * (n + 1)) ^ 2 ≤ ((n + 1) ^ 3) ^ 2 :=
          Nat.pow_le_pow_left (gens_measure_le hl) 2
      _ = (n + 1) ^ 6 := by ring
  omega

/-- **The weight of a generator output**: at most `13 (n + 1)⁶`, since there are at most `n²`
generators. -/
theorem GensVal.wt_le {n : ℕ} {v : Val} {G : Subgroup (Perm (Fin n))} (h : GensVal n v G) :
    v.wt ≤ 13 * (n + 1) ^ 6 := by
  obtain ⟨hs, rfl, hl, -⟩ := h
  exact wt_list_encPerms_le_sq hl

theorem GroupVal.unique {n : ℕ} {v : Val} {G H : Subgroup (Perm (Fin n))} (hG : GroupVal n v G)
    (hH : GroupVal n v H) : G = H := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨hs, h, rfl⟩ := hH
  rw [encGroup_injective h]

theorem GensVal.unique {n : ℕ} {v : Val} {G H : Subgroup (Perm (Fin n))} (hG : GensVal n v G)
    (hH : GensVal n v H) : G = H := by
  obtain ⟨gs, rfl, -, rfl⟩ := hG
  obtain ⟨hs, h, -, rfl⟩ := hH
  simp only [Val.list.injEq] at h
  rw [(List.map_injective_iff.mpr encPerm_injective) h]

theorem gens_eq_of_set_eq {n : ℕ} {gs hs : List (Perm (Fin n))} (h : ∀ g, g ∈ gs ↔ g ∈ hs) :
    gens gs = gens hs := by
  unfold gens; congr 1; ext g; exact h g

theorem gens_one_cons {n : ℕ} (gs : List (Perm (Fin n))) : gens (1 :: gs) = gens gs := by
  unfold gens
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg

/-- A generating list `hs`, with the identity added in front, is a group value. -/
theorem GensVal.groupVal {n : ℕ} {hs : List (Perm (Fin n))} {G : Subgroup (Perm (Fin n))}
    (h : gens hs = G) : GroupVal n (encGroup hs) G := ⟨hs, rfl, h⟩

theorem GroupVal.exists {n : ℕ} (G : Subgroup (Perm (Fin n))) : ∃ v, GroupVal n v G := by
  obtain ⟨v, hs, rfl, -, h⟩ := GI.CitedChecks.exists_gensOf G
  exact ⟨_, hs, rfl, h⟩

theorem GensVal.exists {n : ℕ} (G : Subgroup (Perm (Fin n))) : ∃ v, GensVal n v G :=
  GI.CitedChecks.exists_gensOf G

/-- The generators in a group value lie in the group. -/
theorem GroupVal.mem {n : ℕ} {gs : List (Perm (Fin n))} {G : Subgroup (Perm (Fin n))}
    (h : gens gs = G) {g : Perm (Fin n)} (hg : g ∈ gs) : g ∈ G :=
  h ▸ Subgroup.subset_closure hg

/-! ### Cosets -/

/-- `v = [x, encGroup gs]` encodes the left coset `x • ⟨gs⟩`. -/
def CosetVal (n : ℕ) (v : Val) (C : Set (Perm (Fin n))) : Prop :=
  ∃ (x : Perm (Fin n)) (gs : List (Perm (Fin n))), v = .list [encPerm x, encGroup gs] ∧
    C = x • (gens gs : Set (Perm (Fin n)))

theorem CosetVal.unique {n : ℕ} {v : Val} {C D : Set (Perm (Fin n))} (hC : CosetVal n v C)
    (hD : CosetVal n v D) : C = D := by
  obtain ⟨x, gs, rfl, rfl⟩ := hC
  obtain ⟨y, hs, h, rfl⟩ := hD
  simp only [Val.list.injEq, List.cons.injEq, and_true] at h
  rw [encPerm_injective h.1, encGroup_injective h.2]

theorem CosetVal.mk {n : ℕ} {x : Perm (Fin n)} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) : CosetVal n (.list [encPerm x, gv]) (x • (G : Set (Perm (Fin n)))) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact ⟨x, gs, rfl, rfl⟩

/-- A coset value: its representative lies in the coset. -/
theorem CosetVal.rep_mem {n : ℕ} {x : Perm (Fin n)} {gv : Val} {C : Set (Perm (Fin n))}
    (h : CosetVal n (.list [encPerm x, gv]) C) : x ∈ C := by
  obtain ⟨y, gs, hv, rfl⟩ := h
  simp only [Val.list.injEq, List.cons.injEq, and_true] at hv
  rw [encPerm_injective hv.1]
  exact ⟨1, Subgroup.one_mem _, mul_one y⟩

/-! ### Labelings and partitions -/

/-- `v` lists the labels of a labeling `lab` whose classes are those of the relation `R`. -/
def PartVal (n : ℕ) (v : Val) (R : Fin n → Fin n → Prop) : Prop :=
  ∃ lab : Fin n → ℕ, v = encFun lab ∧ ∀ i j, lab i = lab j ↔ R i j

/-- `v` lists orbit labels of `G` (as `GI.Cited.IsOrbitLabeling`). -/
def OrbitVal (n : ℕ) (v : Val) (G : Subgroup (Perm (Fin n))) : Prop :=
  PartVal n v fun i j => ∃ g ∈ G, g i = j

/-- `v` lists representative labels for `R`: the label of `i` is a point `r i` of the class of
`i`, and `r` is constant on the classes. -/
def ReprVal (n : ℕ) (v : Val) (R : Fin n → Fin n → Prop) : Prop :=
  ∃ r : Fin n → Fin n, v = encFun (fun i => (r i : ℕ)) ∧ (∀ i j, r i = r j ↔ R i j) ∧
    ∀ i, r (r i) = r i

theorem PartVal.unique {n : ℕ} {v : Val} {R R' : Fin n → Fin n → Prop} (h : PartVal n v R)
    (h' : PartVal n v R') : R = R' := by
  obtain ⟨lab, rfl, hR⟩ := h
  obtain ⟨lab', he, hR'⟩ := h'
  rw [encFun_injective he] at hR
  funext i j
  exact propext ((hR i j).symm.trans (hR' i j))

theorem OrbitVal.unique {n : ℕ} {v : Val} {G : Subgroup (Perm (Fin n))}
    {R : Fin n → Fin n → Prop} (h : OrbitVal n v G) (h' : PartVal n v R) :
    R = fun i j => ∃ g ∈ G, g i = j := (PartVal.unique h h').symm

theorem ReprVal.partVal {n : ℕ} {v : Val} {R : Fin n → Fin n → Prop} (h : ReprVal n v R) :
    PartVal n v R := by
  obtain ⟨r, rfl, hR, -⟩ := h
  exact ⟨fun i => r i, rfl, fun i j => by rw [← hR, Fin.val_inj]⟩

theorem ReprVal.unique {n : ℕ} {v : Val} {R R' : Fin n → Fin n → Prop} (h : ReprVal n v R)
    (h' : ReprVal n v R') : R = R' := PartVal.unique h.partVal h'.partVal

/-- Every equivalence relation has representative labels: the least point of each class. -/
theorem ReprVal.exists {n : ℕ} (R : Fin n → Fin n → Prop) (hR : Equivalence R) :
    ∃ v, ReprVal n v R := by
  classical
  let r : Fin n → Fin n := fun i =>
    (Finset.univ.filter fun j => R i j).min' ⟨i, by simp [hR.refl i]⟩
  have hr : ∀ i, R i (r i) := fun i => by
    have := Finset.min'_mem (Finset.univ.filter fun j => R i j) ⟨i, by simp [hR.refl i]⟩
    simpa using this
  have hcongr : ∀ i j, R i j → r i = r j := fun i j hij => by
    have e : (Finset.univ.filter fun k => R i k) = Finset.univ.filter fun k => R j k := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => hR.trans (hR.symm hij) h, fun h => hR.trans hij h⟩
    simp only [r, e]
  refine ⟨_, r, rfl, fun i j => ⟨fun h => ?_, hcongr i j⟩, fun i => (hcongr _ _ (hr i)).symm⟩
  exact hR.trans (hr i) (h ▸ hR.symm (hr j))

/-- **The weight of a labeling output**: `n` labels below `n` weigh at most `7 (n + 1)²`. -/
theorem labels_wt_le {n : ℕ} {lab : Fin n → ℕ} (h : ∀ i, lab i < n) : (encFun lab).wt ≤ 7 * (n + 1) ^ 2 := by
  have := wt_encFun_le lab (B := n) fun i => (h i).le
  nlinarith

/-- The output format `LabelsOf` is a labeling value `encFun lab` with labels below `n`. -/
theorem labelsOf_iff {n : ℕ} {Q : (Fin n → ℕ) → Prop} {v : Val} :
    GI.Cited.LabelsOf Q v ↔ ∃ lab : Fin n → ℕ, v = encFun lab ∧ (∀ i, lab i < n) ∧ Q lab :=
  Iff.rfl

/-- The values of a labeling are its labels. -/
theorem encFun_getElem {n : ℕ} (lab : Fin n → ℕ) (i : Fin n) :
    ((List.finRange n).map fun i => Val.nat (lab i))[(i : ℕ)]? = some (.nat (lab i)) := by
  simp

/-! ### Homomorphisms given on generators -/

/-- `v = [encGroup gs, [h₁, …, h_m]]` encodes the homomorphism `φ` on `G = ⟨gs⟩` with
`φ gᵢ = hᵢ`. -/
def HomVal (n n' : ℕ) (v : Val) (G : Subgroup (Perm (Fin n))) (φ : G →* Perm (Fin n')) : Prop :=
  ∃ (gs : List (Perm (Fin n))) (hs : List (Perm (Fin n'))),
    v = .list [encGroup gs, .list (hs.map encPerm)] ∧ gens gs = G ∧
    List.Forall₂ (fun g h => ∃ hg : g ∈ G, φ ⟨g, hg⟩ = h) gs hs

theorem forall₂_both {α β : Type} {R S : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (h' : List.Forall₂ S l₁ l₂) :
    ∀ x ∈ l₁, ∃ y, R x y ∧ S x y := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    cases h' with
    | cons hs h' =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, hr, hs⟩
      · exact ih h' x hx

/-- Two homomorphisms that agree on generators agree. -/
theorem hom_eq_of_gens {n : ℕ} {M : Type*} [Group M] {gs : List (Perm (Fin n))}
    {G : Subgroup (Perm (Fin n))} (hG : gens gs = G) {φ ψ : G →* M}
    (h : ∀ g (hg : g ∈ G), g ∈ gs → φ ⟨g, hg⟩ = ψ ⟨g, hg⟩) : φ = ψ := by
  subst hG
  ext ⟨g, hg⟩ : 1
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x _ hx
  | one => exact (map_one φ).trans (map_one ψ).symm
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : gens gs) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, map_mul, ihx, ihy]
  | inv x hx ih =>
    have e : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : gens gs) = (⟨x, hx⟩)⁻¹ := rfl
    rw [e, map_inv, map_inv, ih]

theorem HomVal.unique {n n' : ℕ} {v : Val} {G H : Subgroup (Perm (Fin n))}
    {φ : G →* Perm (Fin n')} {ψ : H →* Perm (Fin n')} (hφ : HomVal n n' v G φ)
    (hψ : HomVal n n' v H ψ) : ∃ e : G = H, ∀ g (hg : g ∈ G), φ ⟨g, hg⟩ = ψ ⟨g, e ▸ hg⟩ := by
  obtain ⟨gs, hs, rfl, rfl, hf⟩ := hφ
  obtain ⟨gs', hs', he, rfl, hf'⟩ := hψ
  simp only [Val.list.injEq, List.cons.injEq, and_true] at he
  obtain rfl := encGroup_injective he.1
  obtain rfl := (List.map_injective_iff.mpr encPerm_injective) he.2
  refine ⟨rfl, fun g hg => ?_⟩
  have := hom_eq_of_gens (φ := φ) (ψ := ψ) rfl fun x hx hxs => by
    obtain ⟨y, ⟨_, e1⟩, ⟨_, e2⟩⟩ := forall₂_both hf hf' x hxs
    exact e1.trans e2.symm
  rw [this]

/-! ### Series -/

/-- `v` is a list of at most `n² + 1` generating lists of the groups `Hs`, in order, each of at
most `n²` permutations. -/
def SeriesVal (n : ℕ) (v : Val) (Hs : List (Subgroup (Perm (Fin n)))) : Prop :=
  ∃ L : List (List (Perm (Fin n))), v = .list (L.map fun hs => .list (hs.map encPerm)) ∧
    L.length ≤ n ^ 2 + 1 ∧ (∀ hs ∈ L, hs.length ≤ n ^ 2) ∧ L.map gens = Hs

/-- **The weight of a series output**: at most `100 (n + 1)⁸`. -/
theorem SeriesVal.wt_le {n : ℕ} {v : Val} {Hs : List (Subgroup (Perm (Fin n)))} (h : SeriesVal n v Hs) :
    v.wt ≤ 100 * (n + 1) ^ 8 := by
  obtain ⟨L, rfl, hL, hl, -⟩ := h
  have h1 := wt_list_le (L.map fun hs => Val.list (hs.map encPerm))
  have h2 := List.sum_le_card_nsmul ((L.map fun hs => Val.list (hs.map encPerm)).map Val.wt)
    (13 * (n + 1) ^ 6) (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp]
      rintro _ hs hhs rfl
      exact wt_list_encPerms_le_sq (hl hs hhs))
  simp only [List.length_map, smul_eq_mul] at h1 h2
  have hL2 : L.length ≤ (n + 1) ^ 2 := by
    have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have h3 : L.length * (13 * (n + 1) ^ 6) ≤ (n + 1) ^ 2 * (13 * (n + 1) ^ 6) :=
    Nat.mul_le_mul_right _ hL2
  have h4 : (n + 1) ^ 2 * (13 * (n + 1) ^ 6) = 13 * (n + 1) ^ 8 := by ring
  have h5 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  omega

theorem SeriesVal.unique {n : ℕ} {v : Val} {Hs Ks : List (Subgroup (Perm (Fin n)))}
    (h : SeriesVal n v Hs) (h' : SeriesVal n v Ks) : Hs = Ks := by
  obtain ⟨L, rfl, -, -, rfl⟩ := h
  obtain ⟨L', he, -, -, rfl⟩ := h'
  simp only [Val.list.injEq] at he
  have hinj : Function.Injective fun hs : List (Perm (Fin n)) => Val.list (hs.map encPerm) :=
    fun a b hab => by
      simp only [Val.list.injEq] at hab
      exact (List.map_injective_iff.mpr encPerm_injective) hab
  rw [(List.map_injective_iff.mpr hinj) he]

/-- The entries of a series value are generating lists. -/
theorem SeriesVal.getElem {n : ℕ} {L : List (List (Perm (Fin n)))}
    (hl : ∀ hs ∈ L, hs.length ≤ n ^ 2) (i : ℕ) (hi : i < L.length) :
    GensVal n (.list (L[i].map encPerm)) (gens L[i]) :=
  ⟨L[i], rfl, hl _ (List.getElem_mem hi), rfl⟩

end GI.Lang
