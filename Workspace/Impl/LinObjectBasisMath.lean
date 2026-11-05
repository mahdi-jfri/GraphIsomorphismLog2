module

public import Workspace.Impl.LinObjectIndexed
public import Workspace.Impl.LinObjectConfigAdd
public import Workspace.Impl.TermRecProgShift

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped BigOperators

noncomputable def linObjectWordPieces {n : ℕ} (as : List (Equiv.Perm (Fin n)))
    (Y : List (TmRiO n)) (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    List (List (TmRiO n)) :=
  List.ofFn fun i : Fin (tmRiPcsO (gens as) Y).length =>
    ((tmRiPcsO (gens as) Y).get i).map
      (tmRiSh (linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ z i)))

theorem linObjectMs_flatten {n : ℕ} (Ps : List (List (TmRiO n))) :
    tmGlMs Ps.flatten = (Ps.map tmGlMs).sum := by
  induction Ps with
  | nil => simp [tmGlMs]
  | cons S Ps ih =>
    simp only [List.flatten_cons, List.map_cons, List.sum_cons, ← ih]
    simp [tmGlMs, List.map_append, Multiset.coe_add]

noncomputable def linObjectBasisWord {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (T : ↥(pieces (gens as) (tmGlMs Y))) : Equiv.Perm (Fin n) :=
  linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ z ((linObjectPieceIndex as Y).symm T))

noncomputable def linObjectBasisWords {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (T : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) : Equiv.Perm (Fin n) := by
  classical
  exact if hT : T ∈ pieces (gens as) (tmGlMs Y) then linObjectBasisWord as Y z ⟨T,hT⟩ else 1

theorem linObjectBasisWords_mem {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    ∀ T ∈ pieces (gens as) (tmGlMs Y), linObjectBasisWords as Y z T ∈ gens as := by
  intro T hT
  simp only [linObjectBasisWords, dif_pos hT]
  exact linPermWord_mem as _

theorem linObjectWordPieces_ms {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    tmGlMs (linObjectWordPieces as Y z).flatten =
      linObjectConfigOf (gens as) (tmGlMs Y) (linObjectBasisWords as Y z) := by
  classical
  rw [linObjectMs_flatten]
  simp only [linObjectWordPieces, List.map_ofFn, List.sum_ofFn, Function.comp_apply, tmRi_ms_shift]
  have he := (linObjectPieceIndex as Y).sum_comp
    (fun T => T.val ↼ linObjectBasisWords as Y z T.val)
  have hi (i : Fin (tmRiPcsO (gens as) Y).length) :
      (linObjectPieceIndex as Y i).val ↼ linObjectBasisWords as Y z (linObjectPieceIndex as Y i).val =
      tmGlMs ((tmRiPcsO (gens as) Y).get i) ↼
        linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ z i) := by
    simp only [linObjectBasisWords, dif_pos (linObjectPieceIndex as Y i).property]
    change _ ↼ linObjectBasisWord as Y z (linObjectPieceIndex as Y i) = _
    simp only [linObjectBasisWord, Equiv.symm_apply_apply]
    rfl
  simp_rw [hi] at he
  rw [he]
  exact Finset.sum_coe_sort (pieces (gens as) (tmGlMs Y))
    (fun T => T ↼ linObjectBasisWords as Y z T)

theorem linObjectWordPieces_conf {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    Conf (gens as) (tmGlMs Y) (tmGlMs (linObjectWordPieces as Y z).flatten) := by
  rw [linObjectWordPieces_ms]
  exact linObjectConfigOf_conf _ _ _ (linObjectBasisWords_mem as Y z)

/-- Lifting a vector to local words and rebuilding the pieces preserves its residue in W. -/
theorem linObjectWordPieces_coord {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (hπ : Function.Surjective π)
    (Y : List (TmRiO n))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) :
    linObjectIndexedConfigEquiv as π hπ Y hker
      ⟨tmGlMs (linObjectWordPieces as Y z).flatten, linObjectWordPieces_conf as Y z⟩ =
    linObjectProductMap
      (fun i => linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
      (linObjectLiftCoord as π) (linObjectUnflatten _ _ z) := by
  classical
  funext i
  rw [linObjectIndexedConfigEquiv_apply]
  change linObjectConfigCoord (gens as) π (tmGlMs Y)
    (tmGlMs (linObjectWordPieces as Y z).flatten) (linObjectPieceIndex as Y i) = _
  rw [linObjectWordPieces_ms,
    linObjectConfigOf_coord _ _ _ hker _ (linObjectBasisWords_mem as Y z)]
  have hw : linObjectBasisWords as Y z (linObjectPieceIndex as Y i).val =
      linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ z i) := by
    simp only [linObjectBasisWords, dif_pos (linObjectPieceIndex as Y i).property]
    change linObjectBasisWord as Y z (linObjectPieceIndex as Y i) = _
    simp only [linObjectBasisWord, Equiv.symm_apply_apply]
  change _ = (linObjectGroupImage (gens as) π
    (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i)))).mkQ
      (linObjectLiftCoord as π (linObjectUnflatten _ _ z i))
  have hc := linPermWord_coordinates as π (linObjectUnflatten _ _ z i)
  change linObjectLiftCoord as π (linObjectUnflatten _ _ z i) = _ at hc
  rw [hc]
  congr 2
  apply congrArg π
  apply Subtype.ext
  exact hw

theorem linObjectBasisWords_index {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (i : Fin (tmRiPcsO (gens as) Y).length) :
    linObjectBasisWords as Y z (linObjectPieceIndex as Y i).val =
      linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ z i) := by
  classical
  simp only [linObjectBasisWords, dif_pos (linObjectPieceIndex as Y i).property]
  change linObjectBasisWord as Y z (linObjectPieceIndex as Y i) = _
  simp only [linObjectBasisWord, Equiv.symm_apply_apply]

theorem linObjectWordPieces_piece {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n))
    (z : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ)
    (S : List (TmRiO n)) (hS : S ∈ linObjectWordPieces as Y z) :
    tmGlMs S ∈ pieces (gens as) (tmGlMs (linObjectWordPieces as Y z).flatten) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hS
  have hi := (linObjectPieceIndex as Y i).property
  have hp := linObjectConfig_part_mem_pieces (linObjectWordPieces_conf as Y z) hi
  rw [linObjectWordPieces_ms] at hp ⊢
  unfold linObjectConfigOf at hp ⊢
  rw [partAt_conf hi (linObjectBasisWords_mem as Y z), linObjectBasisWords_index] at hp
  rw [tmRi_ms_shift]
  exact hp

/-- Listing genuine pieces whose sum is Z also lists every piece of Z. -/
theorem linObjectPieces_cover {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (Ps : List (List (TmRiO n))) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hp : ∀ S ∈ Ps, tmGlMs S ∈ pieces A Z) (hZ : tmGlMs Ps.flatten = Z) :
    ∀ T ∈ pieces A Z, ∃ S ∈ Ps, tmGlMs S = T := by
  intro T hT
  obtain ⟨x,hx⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
  have hxZ := Multiset.mem_of_le (piece_le hT) hx
  rw [← hZ] at hxZ
  simp only [tmGlMs, Multiset.mem_coe, List.mem_map] at hxZ
  obtain ⟨o,ho,he⟩ := hxZ
  obtain ⟨Sl,hSl,hoSl⟩ := List.mem_flatten.mp ho
  have hxS : x ∈ tmGlMs Sl := by
    simp only [tmGlMs, Multiset.mem_coe, List.mem_map]
    exact ⟨o,hoSl,he⟩
  exact ⟨Sl,hSl,piece_eq_of_sameOrb (hp Sl hSl) hT hxS hx (sameOrb_refl A x)⟩

theorem linObjectWordPieces_zero {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) :
    linObjectWordPieces as Y (0 : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) =
      tmRiPcsO (gens as) Y := by
  have hw (i : Fin (tmRiPcsO (gens as) Y).length) :
      linGroupWord (fun j => as.get j) (linObjectUnflatten _ _ (0 : Fin (as.length * (tmRiPcsO (gens as) Y).length) → ℤ) i) = 1 := by
    change linGroupWord (fun j => as.get j) (0 : Fin as.length → ℤ) = 1
    simp [linGroupWord,linGroupWordPrefix]
  have hs : (tmRiSh (1 : Equiv.Perm (Fin n)) : TmRiO n → TmRiO n) = id := by
    funext o
    rcases o with ⟨c,gs,g⟩
    simp [tmRiSh]
  unfold linObjectWordPieces
  simp only [hw,hs,List.map_id]
  exact List.ofFn_get _

end GI.Impl
