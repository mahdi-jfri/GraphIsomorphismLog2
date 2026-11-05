module

public import Workspace.Impl.KRefParts
public import Workspace.Impl.KRefRef

@[expose] public section

/-!
# The values of one round, and their weights

A round of the program works on the joint coloring `col` stored as two lists of numbers,
`krefAv col false` and `krefAv col true` (the colors of all tuples in index order). This file
links the values computed by the round modules to the model of `KRefModel.lean`
(`krefVCodes`, `krefRl`, `krefCounts`, `krefSig`, `krefStep`), and bounds their weights by
multiples of `X ^ 4`, where `X = krefX n k`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (len)

variable {n k : ℕ}

/-! ### The stored coloring and the look-ups -/

/-- The colors of input `β`, in index order. -/
def krefAv (col : KCol n k) (β : Bool) : List ℕ := (krefTups n k).map (col β)

theorem length_krefAv (col : KCol n k) (β : Bool) : (krefAv col β).length = n ^ k := by
  simp [krefAv, length_krefTups]

theorem kref_Av_getD (col : KCol n k) (β : Bool) (y : Fin k → Fin n) :
    (krefAv col β).getD (krefIdx y) 0 = col β y := by
  have hy := krefIdx_lt y
  rw [List.getD_eq_getElem _ _ (by rw [length_krefAv]; exact hy)]
  simp only [krefAv, krefTups, List.getElem_map, List.getElem_finRange, krefIdx]
  congr 1
  apply finFunctionFinEquiv.symm_apply_eq.mpr
  ext; simp

theorem kref_Av_getD' (col : KCol n k) (β : Bool) (y : Fin k → Fin n) :
    (krefAv col β)[krefIdx y]?.getD 0 = col β y := by
  rw [← List.getD_eq_getElem?_getD]; exact kref_Av_getD col β y

/-- The vector codes of `x`, over `z`. -/
def krefVcs (col : KCol n k) (β : Bool) (x : Fin k → Fin n) : List ℕ :=
  List.ofFn fun z => krefHorner (krefB n k) (krefVec col β x z)

theorem kref_look_upd (col : KCol n k) (β : Bool) (x : Fin k → Fin n) (z : Fin n) :
    (((List.finRange k).map fun i => krefIdx (Function.update x i z)).map fun i =>
      (krefAv col β).getD i 0) = krefVec col β x z := by
  simp [krefVec, List.ofFn_eq_map, kref_Av_getD']

theorem kref_look_tidx (col : KCol n k) (β : Bool) (x : Fin k → Fin n) :
    ((krefTidx x).map fun i => (krefAv col β).getD i 0) = krefTauCols col β x := by
  simp [krefTidx, krefTauCols, kref_Av_getD']

theorem kref_rl_eq (col : KCol n k) (β : Bool) (x : Fin k → Fin n) :
    (krefVcs col β x).map (krefRank (krefVAll col)) = krefRl col β x := by
  simp [krefVcs, krefRl, List.map_ofFn, Function.comp_def]

theorem kref_sig_horner (col : KCol n k) (β : Bool) (x : Fin k → Fin n) :
    krefHornerFrom (krefB n k) (krefHornerFrom (krefB n k) (krefHornerFrom (krefB n k) (col β x)
      (krefPat x)) (krefTauCols col β x)) (krefCounts col β x) =
      krefHorner (krefB n k) (krefSig col β x) := by
  unfold krefHorner krefSig
  simp only [krefHornerFrom_append]
  simp [krefHornerFrom]

theorem kref_vcodes_eq (col : KCol n k) (β : Bool) :
    krefVCodes col β = (krefTups n k).map (krefVcs col β) := rfl

theorem kref_scodes_rank (col : KCol n k) (β : Bool) :
    (krefSCodes col β).map (krefRank (krefSAll col)) = krefAv (krefStep col) β := by
  simp [krefSCodes, krefAv, krefStep, Function.comp_def]

/-! ### Weights -/

theorem kref_lt_two_pow_len (B : ℕ) : B < 2 ^ len B := by
  by_cases hB : B = 0
  · subst hB; simp
  · exact (GI.Machine.len_spec hB).2

/-- A Horner code of a list of digits below `B`. -/
theorem kref_wt_horner {B : ℕ} (hB : 1 < B) {l : List ℕ} (hl : ∀ d ∈ l, d < B) :
    (Val.nat (krefHorner B l)).wt ≤ l.length * B + 2 := by
  rw [wt_nat]
  have h1 : krefHorner B l < B ^ l.length := by
    rw [krefHorner_eq]
    have := Nat.ofDigits_lt_base_pow_length hB (l := l.reverse) (fun d hd => hl d (by simpa using hd))
    simpa using this
  have h2 : B ^ l.length ≤ 2 ^ (len B * l.length) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (kref_lt_two_pow_len B).le _
  have h3 := len_le_of_lt_two_pow (lt_of_lt_of_le h1 h2)
  have h4 : len B * l.length ≤ l.length * B := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (GI.Machine.len_le_self B)
  omega

theorem kref_wt_natList_C {xs : List ℕ} {C : ℕ} (h : ∀ a ∈ xs, (Val.nat a).wt ≤ C) :
    (natList xs).wt ≤ 2 * (xs.length * C) + xs.length + 4 :=
  kref_wt_listMap (f := Val.nat) h

section Wts

variable {col : KCol n k} (hs : KrefSmall col)

include hs

theorem kref_B_le : krefB n k ≤ 2 * krefX n k := by unfold krefB krefX; omega

theorem kref_wt_B : (Val.nat (krefB n k)).wt ≤ 3 * krefX n k := by
  have := wt_nat_le (krefB n k); have := kref_B_le hs; have := @krefX_two n k; omega

theorem kref_wt_col (β : Bool) (x : Fin k → Fin n) : (Val.nat (col β x)).wt ≤ 3 * krefX n k := by
  have := wt_nat_le (col β x); have := hs β x; have := @N_le_krefX n k
  have := @krefX_two n k; omega

theorem kref_wt_Av (β : Bool) : (natList (krefAv col β)).wt ≤ 10 * krefX n k ^ 2 := by
  have h := kref_wt_natList_C (xs := krefAv col β) (C := 3 * krefX n k) (fun a ha => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; exact kref_wt_col hs β x)
  rw [length_krefAv] at h
  obtain ⟨hX2, hX12, -, -, -⟩ := kref_X4 (n := n) (k := k)
  have hN := @N_le_krefX n k
  have : n ^ k * (3 * krefX n k) ≤ 3 * krefX n k ^ 2 := by
    rw [sq]; nlinarith
  omega

theorem kref_wt_vcode (β : Bool) (x : Fin k → Fin n) (z : Fin n) :
    (Val.nat (krefHorner (krefB n k) (krefVec col β x z))).wt ≤ 3 * krefX n k ^ 2 := by
  have h := kref_wt_horner (B := krefB n k) (by unfold krefB; omega) (krefVec_lt hs β x z)
  have hl : (krefVec col β x z).length = k := by simp [krefVec]
  rw [hl] at h
  have := kref_B_le hs; have := @k_le_krefX n k
  obtain ⟨hX2, hX12, -, -, -⟩ := kref_X4 (n := n) (k := k)
  have : k * krefB n k ≤ 2 * krefX n k ^ 2 := by rw [sq]; nlinarith
  omega

theorem kref_wt_vcs (β : Bool) (x : Fin k → Fin n) :
    (natList (krefVcs col β x)).wt ≤ 10 * krefX n k ^ 3 := by
  have h := kref_wt_natList_C (xs := krefVcs col β x) (C := 3 * krefX n k ^ 2) (fun a ha => by
    obtain ⟨z, rfl⟩ := List.mem_ofFn.mp ha; exact kref_wt_vcode hs β x z)
  have hl : (krefVcs col β x).length = n := by simp [krefVcs]
  rw [hl] at h
  obtain ⟨hX2, hX12, hX23, -, -⟩ := kref_X4 (n := n) (k := k)
  have := @n_le_krefX n k
  have : n * (3 * krefX n k ^ 2) ≤ 3 * krefX n k ^ 3 := by
    rw [show krefX n k ^ 3 = krefX n k * krefX n k ^ 2 by ring]; nlinarith
  omega

theorem kref_wt_vtab (β : Bool) :
    (Val.list ((krefTups n k).map fun x => natList (krefVcs col β x))).wt ≤
      30 * krefX n k ^ 4 := by
  have h := kref_wt_listMap (l := krefTups n k) (f := fun x => natList (krefVcs col β x))
    (C := 10 * krefX n k ^ 3) (fun x _ => kref_wt_vcs hs β x)
  rw [length_krefTups] at h
  obtain ⟨hX2, hX12, hX23, hX34, -⟩ := kref_X4 (n := n) (k := k)
  have := @N_le_krefX n k
  have : n ^ k * (10 * krefX n k ^ 3) ≤ 10 * krefX n k ^ 4 := by
    rw [show krefX n k ^ 4 = krefX n k * krefX n k ^ 3 by ring]; nlinarith
  omega

theorem kref_M_le : krefM n k ≤ 2 * krefX n k ^ 2 := by
  unfold krefM
  have h1 := @N_le_krefX n k; have h2 := @n_le_krefX n k
  have : n ^ k * n ≤ krefX n k ^ 2 := by rw [sq]; exact Nat.mul_le_mul h1 h2
  rw [Nat.mul_assoc]; omega

theorem kref_wt_VAll_sub {l : List ℕ} (hl : List.Sublist l (krefVAll col)) :
    (natList l).wt ≤ 20 * krefX n k ^ 4 := by
  have h := kref_wt_natList_C (xs := l) (C := 3 * krefX n k ^ 2) (fun a ha => by
    have ha' := hl.subset ha
    unfold krefVAll at ha'
    rw [List.mem_append] at ha'
    rcases ha' with ha' | ha'
    all_goals
      obtain ⟨cs, hcs, hacs⟩ := List.mem_flatten.mp ha'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hcs
      obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hacs
      exact kref_wt_vcode hs _ x z)
  have hlen : l.length ≤ 2 * krefX n k ^ 2 := by
    have := hl.length_le; rw [length_krefVAll] at this; have := kref_M_le (col := col) hs; omega
  obtain ⟨hX2, hX12, hX23, hX34, -⟩ := kref_X4 (n := n) (k := k)
  have : l.length * (3 * krefX n k ^ 2) ≤ 6 * krefX n k ^ 4 := by
    rw [show krefX n k ^ 4 = krefX n k ^ 2 * krefX n k ^ 2 by ring]; nlinarith
  omega

theorem kref_wt_VAll : (natList (krefVAll col)).wt ≤ 20 * krefX n k ^ 4 :=
  kref_wt_VAll_sub hs (List.Sublist.refl _)

theorem kref_wt_rl (β : Bool) (x : Fin k → Fin n) :
    (natList (krefRl col β x)).wt ≤ 10 * krefX n k ^ 3 := by
  have hM := kref_M_le (col := col) hs
  have h := kref_wt_natList_C (xs := krefRl col β x) (C := 3 * krefX n k ^ 2) (fun a ha => by
    obtain ⟨z, rfl⟩ := List.mem_ofFn.mp ha
    have := krefRl_lt col β x z
    have := wt_nat_le (krefRank (krefVAll col) (krefHorner (krefB n k) (krefVec col β x z)))
    have := @krefX_two n k
    have : 2 ≤ krefX n k ^ 2 := le_trans krefX_two kref_X_le_sq
    omega)
  have hl : (krefRl col β x).length = n := by simp [krefRl]
  rw [hl] at h
  obtain ⟨hX2, hX12, hX23, -, -⟩ := kref_X4 (n := n) (k := k)
  have := @n_le_krefX n k
  have : n * (3 * krefX n k ^ 2) ≤ 3 * krefX n k ^ 3 := by
    rw [show krefX n k ^ 3 = krefX n k * krefX n k ^ 2 by ring]; nlinarith
  omega

theorem kref_wt_counts (β : Bool) (x : Fin k → Fin n) :
    (natList (krefCounts col β x)).wt ≤ 20 * krefX n k ^ 3 := by
  have hM := kref_M_le (col := col) hs
  have h := kref_wt_natList_C (xs := krefCounts col β x) (C := 2 * krefX n k) (fun a ha => by
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp ha
    have : (krefRl col β x).count u ≤ n := by
      have := List.count_le_length (a := u) (l := krefRl col β x)
      simpa [krefRl] using this
    have := wt_nat_le ((krefRl col β x).count u)
    have := @n_le_krefX n k; have := @krefX_two n k
    omega)
  have hl : (krefCounts col β x).length = krefM n k := by simp [krefCounts]
  rw [hl] at h
  obtain ⟨hX2, hX12, hX23, -, -⟩ := kref_X4 (n := n) (k := k)
  have : krefM n k * (2 * krefX n k) ≤ 4 * krefX n k ^ 3 := by
    rw [show krefX n k ^ 3 = krefX n k ^ 2 * krefX n k by ring]; nlinarith
  omega

theorem kref_sigLen_le (β : Bool) (x : Fin k → Fin n) :
    (krefSig col β x).length ≤ 4 * krefX n k ^ 2 := by
  rw [length_krefSig]
  have := kref_M_le (col := col) hs; have := @k_le_krefX n k; have := @kk_le_krefX n k
  have := kref_two_X_le_sq (n := n) (k := k)
  have : 2 ≤ krefX n k ^ 2 := le_trans krefX_two kref_X_le_sq
  omega

theorem kref_wt_scode (β : Bool) (x : Fin k → Fin n) :
    (Val.nat (krefHorner (krefB n k) (krefSig col β x))).wt ≤ 9 * krefX n k ^ 3 := by
  have h := kref_wt_horner (B := krefB n k) (by unfold krefB; omega) (krefSig_lt hs β x)
  have h1 := kref_sigLen_le hs β x
  have h2 := kref_B_le hs
  obtain ⟨hX2, hX12, hX23, -, -⟩ := kref_X4 (n := n) (k := k)
  have : (krefSig col β x).length * krefB n k ≤ 8 * krefX n k ^ 3 := by
    rw [show krefX n k ^ 3 = krefX n k ^ 2 * krefX n k by ring]; nlinarith
  omega

theorem kref_wt_SAll_sub {l : List ℕ} (hl : List.Sublist l (krefSAll col)) :
    (natList l).wt ≤ 40 * krefX n k ^ 4 := by
  have h := kref_wt_natList_C (xs := l) (C := 9 * krefX n k ^ 3) (fun a ha => by
    have ha' := hl.subset ha
    unfold krefSAll krefSCodes at ha'
    rw [List.mem_append] at ha'
    rcases ha' with ha' | ha'
    all_goals
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha'
      exact kref_wt_scode hs _ x)
  have hlen : l.length ≤ 2 * krefX n k := by
    have := hl.length_le; rw [length_krefSAll] at this; have := @N_le_krefX n k; omega
  obtain ⟨hX2, hX12, hX23, hX34, -⟩ := kref_X4 (n := n) (k := k)
  have : l.length * (9 * krefX n k ^ 3) ≤ 18 * krefX n k ^ 4 := by
    rw [show krefX n k ^ 4 = krefX n k * krefX n k ^ 3 by ring]; nlinarith
  omega

theorem kref_wt_SAll : (natList (krefSAll col)).wt ≤ 40 * krefX n k ^ 4 :=
  kref_wt_SAll_sub hs (List.Sublist.refl _)

theorem kref_wt_SCodes (β : Bool) : (natList (krefSCodes col β)).wt ≤ 40 * krefX n k ^ 4 :=
  kref_wt_SAll_sub hs (by
    cases β
    · exact List.sublist_append_left _ _
    · exact List.sublist_append_right _ _)

end Wts

end GI.Impl
