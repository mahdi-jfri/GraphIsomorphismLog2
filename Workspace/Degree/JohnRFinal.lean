module

public import Workspace.Degree.JohnRDelta
public import Workspace.Proved.JohnFinal

@[expose] public section

/-!
# Johnson identification when `m ≥ 8` and `3k ≤ m`

`johnsonIdentificationR` is the Johnson identification of `Proved/JohnFinal.lean` for the range
`m ≥ 8`, `1 ≤ k`, `3k ≤ m` in place of `(k + 1)² < m + 2`. The program is `johnRProgram`: the step
that finds `Δ` is the ball search of `Degree/JohnBall.lean`, and the step that finds `Υ` is the
same, correct here by `john_ups_iffR`. The rest of the proof is that of `johnsonIdentification`,
through `JohnHypG`.
-/

namespace GI.Degree

open GI.Lang GI.Cited GI.Proved GI.Impl Equiv

/-- A group known to be `Alt(m)` acting on `k`-subsets, with `m ≥ 8` and `3k ≤ m`. -/
structure JohnsonRInst where
  n : ℕ
  m : ℕ
  k : ℕ
  gs : List (Perm (Fin n))
  eight_le : 8 ≤ m
  one_le : 1 ≤ k
  three_mul : 3 * k ≤ m
  johnson : ∃ ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}, IsJohnsonId (gens gs) ι

/-- **Johnson identification** for `m ≥ 8` and `3k ≤ m`. Input and output as in
`JohnsonIdentificationTask`. -/
def JohnsonIdentificationRTask : GI.Cited.Task JohnsonRInst :=
  Task.ofVal (fun I => .list [encGroup I.gs, .nat I.m, .nat I.k])
    (fun I v => ∃ ι : Fin I.n ≃ {A : Finset (Fin I.m) // A.card = I.k},
      IsJohnsonId (gens I.gs) ι ∧ v = encKSets ι)

def JohnsonIdentificationR : Prop := ∃ p, PolyTimeAt JohnsonIdentificationRTask p

theorem john_two_mulR {m k : ℕ} (h8 : 8 ≤ m) (h3 : 3 * k ≤ m) : 2 * k + 2 ≤ m := by
  omega

/-- The facts of `JohnHypG` for the labels of the orbit algorithm on pairs, with the labels
`johnDeltaR` and `johnUps` that `johnRProgram` finds. -/
theorem john_hypR (I : JohnsonRInst) : ∃ (ι : Fin I.n ≃ {A : Finset (Fin I.m) // A.card = I.k})
    (lab : Fin (I.n * I.n) → ℕ), IsJohnsonId (gens I.gs) ι ∧
      FunDet johnRProgram 12 (encPerms ((1 :: I.gs).map johnPairPerm)) (encFun lab)
        (orbitK * ((((1 :: I.gs).map johnPairPerm).length + 1) * (I.n * I.n + 1)) ^ 5) ∧
      (∀ x, lab x < I.n * I.n) ∧ JohnHyp0 ι lab ∧
      (∀ x y, lab (johnPair x y) = johnUps I.m I.k (johnRow I.n (johnLabL lab)) ↔
        johnInter ι x y + 1 = I.k) ∧
      JohnHypG ι lab (johnDeltaR I.n (johnLabL lab) (johnUps I.m I.k (johnRow I.n (johnLabL lab)))
        I.k) (johnUps I.m I.k (johnRow I.n (johnLabL lab))) := by
  obtain ⟨ι, hι⟩ := I.johnson
  obtain ⟨lab, horb, hiff, hlt⟩ :=
    orbits_spec (john_at_orbit (P := johnRProgram)) ((1 :: I.gs).map johnPairPerm)
  have hm2 := john_two_mulR I.eight_le I.three_mul
  have h0 : JohnHyp0 ι lab := ⟨I.one_le, hm2, john_lab_iff hι hm2 hiff⟩
  have hυ := john_ups_iffR h0 I.eight_le I.three_mul
  exact ⟨ι, lab, hι, horb, fun x => (hlt x).fst, h0, hυ,
    ⟨I.one_le, hm2, I.three_mul, john_deltaR_iff h0 hυ, hυ⟩⟩

/-- **Johnson identification in polynomial time**, for `m ≥ 8` and `3k ≤ m`. -/
theorem johnsonIdentificationR : JohnsonIdentificationR := by
  refine polyTimeAt_ofVal_of_lang_cells johnRProgram 0 johnK 15 1 1 (fun I => ?_) fun I => ?_
  · obtain ⟨ι, lab, -, -, -, -, -, h⟩ := john_hypR I
    exact john_cells I.gs h.m_le (by have := h.two_mul; omega)
  obtain ⟨ι, lab, hι, horb, hlt, h0, hυ', h⟩ := john_hypR I
  have hcntlen : (johnCnt (johnRow I.n (johnLabL lab))).length = I.n := by
    simp [johnCnt, johnRow]
  have hcntle : ∀ v ∈ johnCnt (johnRow I.n (johnLabL lab)), v ≤ I.n := by
    intro v hv
    simp only [johnCnt, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    exact List.count_le_length.trans (by simp [johnRow])
  have hυ := (john_findIdx (john_ups_mem h0)).fst
  rw [hcntlen] at hυ
  obtain ⟨hδ, -, hδeq⟩ := john_ball_first h0 hυ'
  have hkm : I.k * (I.m - I.k) ≤ I.n * I.n :=
    (hcntle _ (john_ups_mem h0)).trans (Nat.le_mul_self _)
  have hLlen : (johnLabL lab).length = I.n * I.n := by simp [johnLabL]
  have hLle : ∀ v ∈ johnLabL lab, v ≤ I.n * I.n := by
    intro v hv
    simp only [johnLabL, List.mem_map] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact (hlt x).le
  have hδle : johnDeltaR I.n (johnLabL lab) (johnUps I.m I.k (johnRow I.n (johnLabL lab))) I.k ≤
      I.n * I.n := by
    rw [hδeq]; exact (hlt _).le
  have hok : ∀ i ≤ I.n * I.n, JohnAccOK I.n (((List.range (I.n * I.n)).take i).foldl
      (johnStep I.n (johnLabL lab)
        (johnDeltaR I.n (johnLabL lab) (johnUps I.m I.k (johnRow I.n (johnLabL lab))) I.k)
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
  have s10 := johnR_delta_det I.gs I.m I.k (johnLabL lab) hLlen hLle h0.pos h.m_le
    (by have := I.three_mul; omega) hkm hυ hδ
  obtain ⟨π, hπ⟩ := john_out_eq h
  refine FunAll.mono (john_main_specG I.gs I.m I.k lab horb hlt h.m_le hkm johnDeltaRE johnR_main
      _ hδle s10 hυ hok)
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

end GI.Degree
