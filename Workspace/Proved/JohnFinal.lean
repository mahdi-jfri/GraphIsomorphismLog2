module

public import Workspace.Impl.JohnMain
public import Workspace.Impl.CamCells
public import Workspace.Lang.Bridge

@[expose] public section

/-!
# Johnson identification in polynomial time

The program `johnProgram` follows [H, §2.8] (Helfgott, Bajpai, Dona, arXiv:1710.04574v1). On input
`[encGroup gs, m, k]` it

1. labels the pairs of points by their orbital, with the orbit algorithm on pairs;
2. finds the orbitals `Δ` (disjoint `k`-sets) and `Υ` (`k`-sets meeting in `k - 1` elements) by
   their valencies in row `0`;
3. collects the distinct sets `C(x, y)` over the pairs `(x, y)` in `Υ`. These are the `m` sets
   "the points whose `k`-set contains `i`", one for each `i`;
4. outputs, for each point, the numbers of the sets that contain it.

The output is `ι` followed by a renaming of `Fin m` (`john_out_eq`), which is again a correct
answer (`john_isJohnsonId_trans`). The cost is at most `johnK · (wt + 1) ^ 15`
(`john_main_spec`).
-/

namespace GI.Proved

open GI.Lang GI.Cited GI.Impl Equiv

theorem john_two_mul {m k : ℕ} (h5 : 5 ≤ m) (h1 : 1 ≤ k) (hb : (k + 1) ^ 2 < m + 2) :
    2 * k + 2 ≤ m := by
  have hsq : k * k + 2 * k ≤ m := by nlinarith
  rcases Nat.lt_or_ge k 2 with hk | hk
  · omega
  · nlinarith

/-- The facts of `JohnHyp` for the labels of the orbit algorithm on pairs. -/
theorem john_hyp (I : JohnsonInst) : ∃ (ι : Fin I.n ≃ {A : Finset (Fin I.m) // A.card = I.k})
    (lab : Fin (I.n * I.n) → ℕ), IsJohnsonId (gens I.gs) ι ∧
      FunDet johnProgram 12 (encPerms ((1 :: I.gs).map johnPairPerm)) (encFun lab)
        (orbitK * ((((1 :: I.gs).map johnPairPerm).length + 1) * (I.n * I.n + 1)) ^ 5) ∧
      (∀ x, lab x < I.n * I.n) ∧ JohnHyp ι lab := by
  obtain ⟨ι, hι⟩ := I.johnson
  obtain ⟨lab, horb, hiff, hlt⟩ := orbits_spec john_at_orbit ((1 :: I.gs).map johnPairPerm)
  have hm2 := john_two_mul I.five_le I.one_le I.bound
  exact ⟨ι, lab, hι, horb, fun x => (hlt x).fst,
    ⟨I.five_le, I.one_le, I.bound, john_lab_iff hι hm2 hiff⟩⟩

theorem john_encGroup_size {n : ℕ} (gs : List (Perm (Fin n))) : n ≤ (encGroup gs).size := by
  rw [size_eq_length]
  simp only [encGroup, encPerms, cells_list, cellsList_cons, cellsList_nil, cells_nat,
    List.map_cons, List.length_append, List.length_cons, List.length_nil, cam_encPerm_size]
  omega

/-- The cells of the input are at most its size plus one, when `k ≤ m ≤ n`. -/
theorem john_cells {n : ℕ} (gs : List (Perm (Fin n))) {m k : ℕ} (hm : m ≤ n) (hk : k ≤ m) :
    ∀ a ∈ (Val.list [encGroup gs, .nat m, .nat k]).cells,
      a ≤ 1 * ((Val.list [encGroup gs, .nat m, .nat k]).size + 1) ^ 1 := by
  intro a ha
  have hG := cam_encGroup_cells gs
  have hs := john_encGroup_size gs
  rw [one_mul, pow_one, size_eq_length] at hG ⊢
  rw [size_eq_length] at hs
  have hlen : (Val.list [encGroup gs, .nat m, .nat k]).cells.length =
      (encGroup gs).cells.length + 7 := by
    simp only [cells_list, cellsList_cons, cellsList_nil, cells_nat, List.length_append,
      List.length_cons, List.length_nil]
    omega
  rw [hlen]
  simp only [cells_list, cellsList_cons, cellsList_nil, cells_nat, List.append_nil,
    List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | rfl | rfl | ha | ha
  · omega
  · omega
  · omega
  · have := hG a ha; omega
  · rcases ha with rfl | rfl | rfl | rfl | ha
    · omega
    · omega
    · omega
    · omega
    · simp at ha

/-- **Johnson identification in polynomial time.** -/
theorem johnsonIdentification : GI.Cited.JohnsonIdentification := by
  refine polyTimeAt_ofVal_of_lang_cells johnProgram 0 johnK 15 1 1 (fun I => ?_) fun I => ?_
  · obtain ⟨ι, lab, -, -, -, h⟩ := john_hyp I
    exact john_cells I.gs h.m_le (by have := h.two_mul; omega)
  obtain ⟨ι, lab, hι, horb, hlt, h⟩ := john_hyp I
  have hcntlen : (johnCnt (johnRow I.n (johnLabL lab))).length = I.n := by
    simp [johnCnt, johnRow]
  have hcntle : ∀ v ∈ johnCnt (johnRow I.n (johnLabL lab)), v ≤ I.n := by
    intro v hv
    simp only [johnCnt, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    exact List.count_le_length.trans (by simp [johnRow])
  have hδ := (john_findIdx (john_max_mem h)).fst
  have hυ := (john_findIdx (john_ups_mem h)).fst
  rw [hcntlen] at hδ hυ
  have hkm : I.k * (I.m - I.k) ≤ I.n * I.n :=
    (hcntle _ (john_ups_mem h)).trans (Nat.le_mul_self _)
  have hok : ∀ i ≤ I.n * I.n, JohnAccOK I.n (((List.range (I.n * I.n)).take i).foldl
      (johnStep I.n (johnLabL lab) (johnDelta (johnRow I.n (johnLabL lab)))
        (johnUps I.m I.k (johnRow I.n (johnLabL lab)))) []) := by
    intro i _
    obtain ⟨hl, hv⟩ := john_prefix h ((List.range (I.n * I.n)).take i)
      (fun p hp => List.mem_range.mp (List.mem_of_mem_take hp))
    refine ⟨hl.trans h.m_le, fun v hvm => ?_⟩
    obtain ⟨j, rfl⟩ := hv v hvm
    refine ⟨by simp [johnInd], fun b hb => ?_⟩
    simp only [johnInd, List.mem_map] at hb
    obtain ⟨r, -, rfl⟩ := hb
    split <;> omega
  obtain ⟨π, hπ⟩ := john_out_eq h
  refine FunAll.mono (john_main_spec I.gs I.m I.k lab horb hlt h.m_le hkm hδ hυ hok)
    fun v c hv => ⟨⟨ι.trans (kSetPerm π), john_isJohnsonId_trans π hι, ?_⟩, hv.2⟩
  rw [hv.1]
  erw [hπ]
  simp only [encKSets, natList, List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  congr 1
  induction ((ι.trans (kSetPerm π)) x).1.sort (· ≤ ·) with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons] at ih ⊢; rw [ih]; rfl

end GI.Proved
