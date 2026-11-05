module

public import Workspace.Impl.AggItemHvA
public import Workspace.Impl.AggItemC1Top

@[expose] public section

/-!
# Case 2a: the even aligner and the paired transposition, on labels

The halving item needs two label permutations (Lemma A.11):

* an **even aligner** `σ` with `σ Φ = Φ'`, for the dominant orbits `Φ`, `Φ'` of the two ideal
  certificate groups ("choose an even ideal permutation aligning their dominant orbits");
* the **paired transposition** `(a b)(c d)` with `a, b ∈ Φ` and `c, d ∉ Φ` ("an even paired
  transposition, one transposition in each of `Φ` and `C`, supplies its representative").

Both are computed from the indicator of `Φ` with the labeling tools of Case 1. The indicator is a
labeling with the two blocks `Φ` and `Φᶜ`. Its sorting key is (block size, label, point), and
`Φᶜ` is the smaller block since `Φ` is dominant (`q < 2 |Φ|`). So:

1. the alignment `itpAlign` of the two indicators maps blocks to blocks of the same size, hence
   `Φ` onto `Φ'` (`itHv_align_mem`); if it is odd, a transposition of the two least points of `Φ`
   makes it even and keeps `Φ` (`itHvSig`);
2. the first two points in key order lie outside `Φ` when `|Φᶜ| ≥ 2` (`itHv_posInv_not_mem`), so
   they give `c` and `d`.

The programs: `itHvIndF` builds the indicator from the sorted list of `Φ` (`it_hvInd_spec`), and
`itHvSgF` returns both permutations (`it_hvSg_spec`). No primitive is called.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm encPts)

variable {q : ℕ}

/-! ### The indicator as a labeling -/

open Classical in
/-- The indicator of `Φ`, as a labeling: `1` on `Φ`, `0` elsewhere. -/
noncomputable def itHvLab (Φ : Finset (Fin q)) (i : Fin q) : ℕ := if i ∈ Φ then 1 else 0

theorem itHvInd_eq_lab (Φ : Finset (Fin q)) : itHvInd Φ = encFun (itHvLab Φ) := rfl

theorem itHvLab_lt {Φ : Finset (Fin q)} (hq : 2 ≤ q) (i : Fin q) : itHvLab Φ i < q := by
  unfold itHvLab; split_ifs <;> omega

theorem itHv_blk (Φ : Finset (Fin q)) (a : Fin q) :
    itpBlk (itHvLab Φ) a = if a ∈ Φ then Φ else Φᶜ := by
  ext y
  rw [itp_mem_blk]
  unfold itHvLab
  by_cases ha : a ∈ Φ <;> by_cases hy : y ∈ Φ <;> simp [ha, hy]

theorem itHv_sz (Φ : Finset (Fin q)) (a : Fin q) :
    itpSz (itHvLab Φ) a = if a ∈ Φ then Φ.card else Φᶜ.card := by
  unfold itpSz
  rw [itHv_blk]
  split_ifs <;> rfl

theorem itHv_cnt_eq (Φ : Finset (Fin q)) (s : ℕ) : itpCnt (itHvLab Φ) s =
    Φ.card * (if Φ.card = s then 1 else 0) + Φᶜ.card * (if Φᶜ.card = s then 1 else 0) := by
  classical
  rw [itpCnt, Finset.card_filter, ← Finset.sum_add_sum_compl Φ]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun _ => if Φ.card = s then 1 else 0)
      (fun y hy => by rw [itHv_sz, if_pos hy])]
    simp
  · rw [Finset.sum_congr rfl (g := fun _ => if Φᶜ.card = s then 1 else 0)
      (fun y hy => by rw [itHv_sz, if_neg (Finset.mem_compl.1 hy)])]
    simp

/-- Two indicators of sets of the same size have the same number of points in blocks of each
size. -/
theorem itHv_cnt {Φ Φ' : Finset (Fin q)} (h : Φ.card = Φ'.card) (s : ℕ) :
    itpCnt (itHvLab Φ) s = itpCnt (itHvLab Φ') s := by
  rw [itHv_cnt_eq, itHv_cnt_eq, Finset.card_compl, Finset.card_compl, h]

/-! ### The aligner -/

/-- **The alignment of the indicators maps `Φ` into `Φ'`**: it keeps block sizes
(`itpSz_of_smul`), and the block `Φ'ᶜ` has size `q - |Φ| ≠ |Φ|` since `Φ` is dominant. -/
theorem itHv_align_mem {Φ Φ' : Finset (Fin q)} (h : Φ.card = Φ'.card) (hd : q < 2 * Φ.card)
    {a : Fin q} (ha : a ∈ Φ) : itpAlign (itHvLab Φ) (itHvLab Φ') a ∈ Φ' := by
  have hs := itpSz_of_smul (itpAlign_smul (itHv_cnt h)) a
  rw [itHv_sz, itHv_sz, if_pos ha] at hs
  by_contra hn
  rw [if_neg hn, Finset.card_compl, Fintype.card_fin] at hs
  omega

open Classical in
/-- **The even aligner**: the alignment of the indicators, times the transposition `(a b)` if the
alignment is odd (its number of inversions is odd). -/
noncomputable def itHvSig (Φ Φ' : Finset (Fin q)) (a b : Fin q) : Perm (Fin q) :=
  if itpNInv (itpAlign (itHvLab Φ) (itHvLab Φ')) % 2 = 0 then itpAlign (itHvLab Φ) (itHvLab Φ')
  else itpAlign (itHvLab Φ) (itHvLab Φ') * swap a b

theorem itHvSig_sign (Φ Φ' : Finset (Fin q)) {a b : Fin q} (hab : a ≠ b) :
    sign (itHvSig Φ Φ' a b) = 1 := by
  unfold itHvSig
  split_ifs with h
  · exact (itp_sign_one_iff _).2 (Nat.even_iff.2 h)
  · have h1 : sign (itpAlign (itHvLab Φ) (itHvLab Φ')) ≠ 1 := fun h1 =>
      h (Nat.even_iff.1 ((itp_sign_one_iff _).1 h1))
    rw [Perm.sign_mul, (itp_sign_cases _).resolve_left h1, Perm.sign_swap hab]
    decide

/-- The swap of two points of `Φ` maps `Φ` into itself. -/
theorem itHv_swap_mem {Φ : Finset (Fin q)} {a b x : Fin q} (ha : a ∈ Φ) (hb : b ∈ Φ) (hx : x ∈ Φ) :
    swap a b x ∈ Φ := by
  rw [Equiv.swap_apply_def]
  split_ifs
  · exact hb
  · exact ha
  · exact hx

theorem itHvSig_mem {Φ Φ' : Finset (Fin q)} (h : Φ.card = Φ'.card) (hd : q < 2 * Φ.card)
    {a b : Fin q} (ha : a ∈ Φ) (hb : b ∈ Φ) {x : Fin q} (hx : x ∈ Φ) : itHvSig Φ Φ' a b x ∈ Φ' := by
  unfold itHvSig
  split_ifs
  · exact itHv_align_mem h hd hx
  · rw [Perm.mul_apply]
    exact itHv_align_mem h hd (itHv_swap_mem ha hb hx)

/-- **The even aligner maps `Φ` onto `Φ'`.** -/
theorem itHvSig_image {Φ Φ' : Finset (Fin q)} (h : Φ.card = Φ'.card) (hd : q < 2 * Φ.card)
    {a b : Fin q} (ha : a ∈ Φ) (hb : b ∈ Φ) :
    (itHvSig Φ Φ' a b) '' (Φ : Set (Fin q)) = Φ' := by
  set σ := itHvSig Φ Φ' a b with hσ
  have hsub : Φ.map σ.toEmbedding ⊆ Φ' := by
    intro y hy
    rw [Finset.mem_map_equiv] at hy
    have := itHvSig_mem h hd ha hb hy
    rw [← hσ, Equiv.apply_symm_apply] at this
    exact this
  have heq : Φ.map σ.toEmbedding = Φ' :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map, h])
  ext y
  rw [← heq, Finset.coe_map]
  rfl

/-! ### Two points outside `Φ` -/

/-- **The first points in key order lie outside `Φ`**: every point of `Φᶜ` has a smaller key than
a point of `Φ` (its block is smaller, as `Φ` is dominant), so a point of `Φ` has position at least
`|Φᶜ|`. -/
theorem itHv_posInv_not_mem {Φ : Finset (Fin q)} (hd : q < 2 * Φ.card) (j : Fin q)
    (hj : (j : ℕ) < Φᶜ.card) : (itpPosE (itHvLab Φ))⁻¹ j ∉ Φ := by
  classical
  set x := (itpPosE (itHvLab Φ))⁻¹ j with hx
  intro hxΦ
  have hpos : itpPos (itHvLab Φ) x = j := by
    rw [← itpPosE_val, hx, Perm.apply_inv_self]
  have hsub : Φᶜ ⊆ univ.filter fun y => itpKey (itHvLab Φ) y < itpKey (itHvLab Φ) x := by
    intro y hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, itpKey_lt_iff.2 (Or.inl ?_)⟩
    rw [itHv_sz, itHv_sz, if_neg (Finset.mem_compl.1 hy), if_pos hxΦ, Finset.card_compl,
      Fintype.card_fin]
    omega
  have := Finset.card_le_card hsub
  unfold itpPos at hpos
  omega

/-- The first two points in key order, as a transposition (for `q ≥ 2`). -/
noncomputable def itHvCD (Φ : Finset (Fin q)) (hq : 2 ≤ q) : Perm (Fin q) :=
  swap ((itpPosE (itHvLab Φ))⁻¹ ⟨0, by omega⟩) ((itpPosE (itHvLab Φ))⁻¹ ⟨1, by omega⟩)

/-! ### The indicator from the sorted list -/

theorem itHv_encPts (l : List (Fin q)) : encPts l = natList (l.map Fin.val) := by
  simp only [encPts, natList]
  induction l with
  | nil => rfl
  | cons a l ih => simp_all

theorem itHv_pts_wt (Φ : Finset (Fin q)) : (encPts (Φ.sort (· ≤ ·))).wt ≤ 5 * (q + 1) ^ 2 := by
  rw [itHv_encPts]
  refine wt_natList_le_sq (B := q) (fun x hx => ?_) ?_
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact y.isLt.le
  · rw [List.length_map, Finset.length_sort]
    simpa using Finset.card_le_univ Φ

/-- The number of times `i` occurs in the sorted list of `Φ` is the indicator. -/
theorem itHv_count (Φ : Finset (Fin q)) (i : Fin q) :
    ((Φ.sort (· ≤ ·)).map Fin.val).count (i : ℕ) = itHvLab Φ i := by
  have hnd : ((Φ.sort (· ≤ ·)).map Fin.val).Nodup :=
    (Finset.sort_nodup Φ _).map Fin.val_injective
  rw [List.Nodup.count hnd, itHvLab]
  have hm : (i : ℕ) ∈ (Φ.sort (· ≤ ·)).map Fin.val ↔ i ∈ Φ := by
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, hyi⟩
      rw [← Fin.ext hyi]; exact (Finset.mem_sort _).1 hy
    · intro hi; exact ⟨i, (Finset.mem_sort _).2 hi, rfl⟩
  by_cases hi : i ∈ Φ
  · rw [if_pos (hm.2 hi), if_pos hi]
  · rw [if_neg (fun h => hi (hm.1 h)), if_neg hi]

/-- On `[c, i]` with `c` the sorted list of `Φ`: `1` if `i ∈ Φ`, else `0`. -/
def itHvIndB (cnt : ℕ) : Expr := .call cnt (mk2 (arg 1) (arg 0))

theorem it_hvIndB_spec {P : Program} {f cnt : ℕ} (hf : P.funs[f]? = some (itHvIndB cnt))
    (hcnt : P.HasAt cnt (countFuns cnt)) (Φ : Finset (Fin q)) (i : Fin q) :
    FunDet P f (.list [encPts (Φ.sort (· ≤ ·)), .nat i]) (.nat (itHvLab Φ i))
      (countK * (q + 1) ^ 3 + 1000 * (q + 1) ^ 3) := by
  set W := 50 * (q + 1) ^ 2
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpw := itHv_pts_wt Φ
  have hin := wt_list2_le (encPts (Φ.sort (· ≤ ·))) (.nat i)
  have hiw := wt_nat_le (i : ℕ)
  have hiq := i.isLt
  have hw2 := wt_list2_le (.nat i) (encPts (Φ.sort (· ≤ ·)))
  have hc : FunDet P cnt (.list [.nat i, natList ((Φ.sort (· ≤ ·)).map Fin.val)])
      (.nat (((Φ.sort (· ≤ ·)).map Fin.val).count (i : ℕ))) (countK * (q + 1) ^ 3) :=
    count_spec hcnt (B := q) (fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact y.isLt.le) hiq.le
      (by rw [List.length_map, Finset.length_sort (· ≤ ·)]; simpa using Finset.card_le_univ Φ)
  rw [← itHv_encPts, itHv_count] at hc
  set env : List Val := [.list [encPts (Φ.sort (· ≤ ·)), .nat i]]
  have g0 : StDC P env (arg 0) (encPts (Φ.sort (· ≤ ·))) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have g1 : StDC P env (arg 1) (.nat i) 3 0 W := StDC.arg rfl (by omega) (by omega) (by omega)
  have g2 := StDC.mk2 g1 g0 (by omega) (by omega)
  have hl : itHvLab Φ i ≤ 1 := by unfold itHvLab; split_ifs <;> omega
  have g3 := StDC.call g2 hc (by have := wt_nat_le (itHvLab Φ i); omega)
  refine StDC.funDet hf g3 ?_
  have : (3 + 3 + 3 + 1) * (W + 1) ≤ 1000 * (q + 1) ^ 3 := by
    have : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

/-- On `[q, encPts Φ.sort]`: the indicator `itHvInd Φ`, a map over `[0, …, q-1]`. -/
def itHvIndF (rng mp : ℕ) : Expr := .call mp (mk2 (arg 1) (.call rng (arg 0)))

/-- The cost bound of `itHvIndF`. -/
def itHvIndC (q : ℕ) : ℕ := 10 ^ 6 * (q + 1) ^ 4

/-- **The indicator of `Φ` from its sorted list.** -/
theorem it_hvInd_spec {P : Program} {f rng mp ib cnt : ℕ} (hf : P.funs[f]? = some (itHvIndF rng mp))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp ib))
    (hib : P.funs[ib]? = some (itHvIndB cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (Φ : Finset (Fin q)) :
    FunDet P f (.list [.nat q, encPts (Φ.sort (· ≤ ·))]) (itHvInd Φ) (itHvIndC q) := by
  set W := 50 * (q + 1) ^ 2
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpw := itHv_pts_wt Φ
  have hR := it_range_wt (q := q)
  have hI := it_hvInd_wt Φ
  have hqw := wt_nat_le q
  have hin := wt_list2_le (.nat q) (encPts (Φ.sort (· ≤ ·)))
  have hin2 := wt_list2_le (encPts (Φ.sort (· ≤ ·))) (natList (List.range q))
  have cR : FunDet P rng (.nat q) (natList (List.range q)) (10000 * (q + 1) ^ 3) :=
    st_range_det hrng q
  have cM := it_tab hmp (c := encPts (Φ.sort (· ≤ ·))) (itHvLab Φ)
    (fun i => by have := i.isLt; unfold itHvLab; split_ifs <;> omega)
    (fun i => it_hvIndB_spec hib hcnt Φ i)
  rw [← itHvInd_eq_lab] at cM
  set env : List Val := [.list [.nat q, encPts (Φ.sort (· ≤ ·))]]
  have g0 : StDC P env (arg 0) (.nat q) 3 0 W := StDC.arg rfl (by omega) (by omega) (by omega)
  have g1 : StDC P env (arg 1) (encPts (Φ.sort (· ≤ ·))) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have g2 := StDC.call g0 cR (by omega)
  have g3 := StDC.mk2 g1 g2 (by omega) (by omega)
  have g4 := StDC.call g3 cM (by omega)
  refine StDC.funDet hf g4 ?_
  have hc1 : q * (countK * (q + 1) ^ 3 + 1000 * (q + 1) ^ 3) ≤ 101000 * (q + 1) ^ 4 := by
    calc q * (countK * (q + 1) ^ 3 + 1000 * (q + 1) ^ 3)
        ≤ (q + 1) * (101000 * (q + 1) ^ 3) := by
          simp only [countK]; exact Nat.mul_le_mul (by omega) (by omega)
      _ = 101000 * (q + 1) ^ 4 := by ring
  have hm1 : mapK * (q + 1) * (2 * (encPts (Φ.sort (· ≤ ·))).wt + 22 * (q + 1) ^ 2) ≤
      32000 * (q + 1) ^ 3 := by
    calc mapK * (q + 1) * (2 * (encPts (Φ.sort (· ≤ ·))).wt + 22 * (q + 1) ^ 2)
        ≤ 1000 * (q + 1) * (32 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 32000 * (q + 1) ^ 3 := by ring
  unfold itHvIndC
  omega

/-! ### The aligner and the paired transposition, as a program -/

/-- On `[itHvInd Φ, itHvInd Φ', encPts Φ.sort]`: `[σ, (a b)(c d)]`, with `σ` the even aligner,
`a, b` the two least points of `Φ` and `c, d` the first two points in key order. -/
def itHvSgF (dat swt cmp par : ℕ) : Expr :=
  .letE (.call dat (.get (.var 0) (.nat 0)))
  (.letE (.call dat (.get (.var 0) (.nat 1)))
  (.letE (.call cmp (mk2 (.get (.var 2) (.nat 3)) (.get (.var 1) (.nat 2))))
  (.letE (.call par (.var 3))
  (.letE (.call swt (mk2 (mk2 (.get (.get (.var 0) (.nat 2)) (.nat 0))
      (.get (.get (.var 0) (.nat 2)) (.nat 1))) (.get (.var 1) (.nat 4))))
  (.letE (.call swt (mk2 (mk2 (.get (.get (.var 1) (.nat 3)) (.nat 0))
      (.get (.get (.var 1) (.nat 3)) (.nat 1))) (.get (.var 1) (.nat 4))))
    (mk2 (.ite (.var 4) (.call cmp (mk2 (.var 3) (.var 5))) (.var 3))
      (.call cmp (mk2 (.var 5) (.var 6)))))))))

/-- The cost bound of `itHvSgF`. -/
def itHvSgC (q : ℕ) : ℕ := 10 ^ 8 * (q + 1) ^ 4

set_option maxHeartbeats 4000000 in
/-- **The even aligner and the paired transposition as a program.** -/
theorem it_hvSg_spec {P : Program} {f dat swt cmp par : ℕ}
    (hf : P.funs[f]? = some (itHvSgF dat swt cmp par))
    (hdat : ∀ lab : Fin q → ℕ, (∀ x, lab x < q) → FunDet P dat (encFun lab) (itDatV lab) (itDatC q))
    (hswt : ∀ u v : Fin q, FunDet P swt (.list [.list [.nat u, .nat v], natList (List.range q)])
      (encPerm (Equiv.swap u v)) (10 ^ 5 * (q + 1) ^ 3))
    (hcmp : P.HasAt cmp (composeFuns cmp))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (hq : 2 ≤ q) (Φ Φ' : Finset (Fin q)) {a b : Fin q} {rest : List (Fin q)}
    (hs : Φ.sort (· ≤ ·) = a :: b :: rest) :
    FunDet P f (.list [itHvInd Φ, itHvInd Φ', encPts (Φ.sort (· ≤ ·))])
      (.list [encPerm (itHvSig Φ Φ' a b), encPerm (swap a b * itHvCD Φ hq)]) (itHvSgC q) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq4 : (q + 1) ^ 3 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨W, hW⟩ : ∃ W, W = 200 * (q + 1) ^ 2 := ⟨_, rfl⟩
  have hW4 : 4 ≤ W := by omega
  set lX := itHvLab Φ with hlX
  set lY := itHvLab Φ' with hlY
  have hltX : ∀ x, lX x < q := itHvLab_lt hq
  have hltY : ∀ x, lY x < q := itHvLab_lt hq
  -- weights
  have hIX := it_hvInd_wt Φ
  have hIY := it_hvInd_wt Φ'
  have hpw := itHv_pts_wt Φ
  have hDX := it_datV_wt lX hltX
  have hDY := it_datV_wt lY hltY
  have hR := it_range_wt (q := q)
  set σ₀ := itpAlign lX lY with hσ₀
  set t := swap a b with ht
  set cd := itHvCD Φ hq with hcd
  have w1 := wt_encPerm_le σ₀
  have w2 := wt_encPerm_le t
  have w3 := wt_encPerm_le cd
  have w4 := wt_encPerm_le (σ₀ * t)
  have w5 := wt_encPerm_le (t * cd)
  have w6 := wt_encPerm_le (itHvSig Φ Φ' a b)
  have w7 := wt_encPerm_le (itpPosE lY)⁻¹
  have w8 := wt_encPerm_le (itpPosE lX)
  have w9 := wt_encPerm_le (itpPosE lX)⁻¹
  have hin := wt_list3_le (itHvInd Φ) (itHvInd Φ') (encPts (Φ.sort (· ≤ ·)))
  have hpar2 : itpNInv σ₀ % 2 < 2 := Nat.mod_lt _ (by omega)
  have hpw2 : (Val.nat (itpNInv σ₀ % 2)).wt ≤ W := by
    have := wt_nat_le (itpNInv σ₀ % 2); omega
  have haq := a.isLt
  have hbq := b.isLt
  have wa := wt_nat_le (a : ℕ)
  have wb := wt_nat_le (b : ℕ)
  set c0 := (itpPosE lX)⁻¹ ⟨0, by omega⟩ with hc0
  set d0 := (itpPosE lX)⁻¹ ⟨1, by omega⟩ with hd0
  have wc := wt_nat_le (c0 : ℕ)
  have wd := wt_nat_le (d0 : ℕ)
  have hcq := c0.isLt
  have hdq := d0.isLt
  have l1 := wt_list2_le (.nat a) (.nat b)
  have l2 := wt_list2_le (.list [.nat a, .nat b]) (natList (List.range q))
  have l3 := wt_list2_le (.nat c0) (.nat d0)
  have l4 := wt_list2_le (.list [.nat c0, .nat d0]) (natList (List.range q))
  have l5 := wt_list2_le (encPerm (itpPosE lY)⁻¹) (encPerm (itpPosE lX))
  have l6 := wt_list2_le (encPerm σ₀) (encPerm t)
  have l7 := wt_list2_le (encPerm t) (encPerm cd)
  have l8 := wt_list2_le (encPerm (itHvSig Φ Φ' a b)) (encPerm (t * cd))
  -- the reads
  have hinW : (Val.list [itHvInd Φ, itHvInd Φ', encPts (Φ.sort (· ≤ ·))]).wt ≤ W := by omega
  set inp : Val := .list [itHvInd Φ, itHvInd Φ', encPts (Φ.sort (· ≤ ·))] with hinp
  have eD : ∀ lab : Fin q → ℕ, itDatV lab = .list [encFun lab, encFun (itpSz lab),
      encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹, natList (List.range q)] := fun _ => rfl
  have epts : encPts (Φ.sort (· ≤ ·)) = .list (.nat a :: .nat b :: rest.map fun i => .nat i) := by
    rw [hs]; rfl
  -- step 1, 2: the data of both labelings
  have d1 := StDC.call (StDC.get (StDC.var' (P := P) (env := [inp]) (i := 0) rfl (W := W) hinW)
    (StDC.nat 0 (by omega)) (v := itHvInd Φ) rfl (by omega)) (hdat lX hltX) (by omega)
  set E1 : List Val := [inp, itDatV lX]
  have d2 := StDC.call (StDC.get (StDC.var' (P := P) (env := E1) (i := 0) rfl (W := W) hinW)
    (StDC.nat 1 (by omega)) (v := itHvInd Φ') rfl (by omega)) (hdat lY hltY) (by omega)
  set E2 : List Val := E1 ++ [itDatV lY]
  -- step 3: the alignment
  have u1 : StDC P E2 (.var 1) (itDatV lX) 1 0 W := StDC.var' rfl (by omega)
  have u2 : StDC P E2 (.var 2) (itDatV lY) 1 0 W := StDC.var' rfl (by omega)
  rw [eD] at u1 u2
  have w1' := wt_encPerm_le ((itpPosE lY)⁻¹ * itpPosE lX)
  have d3 := StDC.call (StDC.mk2 (StDC.get u2 (StDC.nat 3 (by omega))
      (v := encPerm (itpPosE lY)⁻¹) rfl (by omega)) (StDC.get u1 (StDC.nat 2 (by omega))
      (v := encPerm (itpPosE lX)) rfl (by omega)) (by omega) hW4)
    (compose_spec hcmp (itpPosE lY)⁻¹ (itpPosE lX)) (by omega)
  rw [← itpAlign_eq] at d3
  set E3 : List Val := E2 ++ [encPerm σ₀]
  -- step 4: its parity
  have d4 := StDC.call (StDC.var' (W := W) (env := E3) (i := 3) rfl (by omega)) (hpar σ₀) hpw2
  set E4 : List Val := E3 ++ [Val.nat (itpNInv σ₀ % 2)]
  -- step 5: the transposition of `a, b`
  have x0 : StDC P E4 (.var 0) inp 1 0 W := StDC.var' rfl hinW
  have x1 : StDC P E4 (.var 1) (itDatV lX) 1 0 W := StDC.var' rfl (by omega)
  rw [eD] at x1
  have xp := StDC.get x0 (StDC.nat 2 (by omega)) (v := encPts (Φ.sort (· ≤ ·))) rfl (by omega)
  rw [epts] at xp
  have xa := StDC.get xp (StDC.nat 0 (by omega)) (v := .nat a) rfl (by omega)
  have xb := StDC.get xp (StDC.nat 1 (by omega)) (v := .nat b) rfl (by omega)
  have xr := StDC.get x1 (StDC.nat 4 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have w2' := wt_encPerm_le (Equiv.swap a b)
  have d5 := StDC.call (StDC.mk2 (StDC.mk2 xa xb (by omega) hW4) xr (by omega) hW4) (hswt a b)
    (by omega)
  set E5 : List Val := E4 ++ [encPerm t]
  -- step 6: the transposition of `c, d`
  have y1 : StDC P E5 (.var 1) (itDatV lX) 1 0 W := StDC.var' rfl (by omega)
  rw [eD] at y1
  have yi := StDC.get y1 (StDC.nat 3 (by omega)) (v := encPerm (itpPosE lX)⁻¹) rfl (by omega)
  have hi0 : ((List.finRange q).map fun i => Val.nat ((itpPosE lX)⁻¹ i))[0]? = some (.nat c0) :=
    encFun_getElem? (fun i => ((itpPosE lX)⁻¹ i : ℕ)) ⟨0, by omega⟩
  have hi1 : ((List.finRange q).map fun i => Val.nat ((itpPosE lX)⁻¹ i))[1]? = some (.nat d0) :=
    encFun_getElem? (fun i => ((itpPosE lX)⁻¹ i : ℕ)) ⟨1, by omega⟩
  have yc := StDC.get (vs := (List.finRange q).map fun i => Val.nat ((itpPosE lX)⁻¹ i)) yi
    (StDC.nat 0 (by omega)) hi0 (by omega)
  have yd := StDC.get (vs := (List.finRange q).map fun i => Val.nat ((itpPosE lX)⁻¹ i)) yi
    (StDC.nat 1 (by omega)) hi1 (by omega)
  have yr := StDC.get y1 (StDC.nat 4 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have w3' := wt_encPerm_le (Equiv.swap c0 d0)
  have d6 := StDC.call (StDC.mk2 (StDC.mk2 yc yd (by omega) hW4) yr (by omega) hW4) (hswt c0 d0)
    (by omega)
  have ecd : Equiv.swap c0 d0 = cd := rfl
  rw [ecd] at d6
  set E6 : List Val := E5 ++ [encPerm cd]
  -- the output
  have z3 : StDC P E6 (.var 3) (encPerm σ₀) 1 0 W := StDC.var' rfl (by omega)
  have z4 : StDC P E6 (.var 4) (.nat (itpNInv σ₀ % 2)) 1 0 W := StDC.var' rfl hpw2
  have z5 : StDC P E6 (.var 5) (encPerm t) 1 0 W := StDC.var' rfl (by omega)
  have z6 : StDC P E6 (.var 6) (encPerm cd) 1 0 W := StDC.var' rfl (by omega)
  have zi := StDC.ite (v := encPerm (itHvSig Φ Φ' a b)) z4
    (fun hp => by
      have hv : itHvSig Φ Φ' a b = σ₀ * t := by rw [itHvSig, if_neg hp]
      rw [hv]
      exact StDC.call (StDC.mk2 z3 z5 (by omega) hW4) (compose_spec hcmp σ₀ t) (by omega))
    (fun hp => by
      have hv : itHvSig Φ Φ' a b = σ₀ := by rw [itHvSig, if_pos hp]
      rw [hv]; exact z3) (by omega)
  have zc := StDC.call (StDC.mk2 z5 z6 (by omega) hW4) (compose_spec hcmp t cd) (by omega)
  have d7 := StDC.mk2 zi zc (by omega) hW4
  have hout : (Val.list [encPerm (itHvSig Φ Φ' a b), encPerm (t * cd)]).wt ≤ W := by omega
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 (StDC.letE d4 (StDC.letE d5
    (StDC.letE d6 d7 hout) hout) hout) hout) hout) hout
  refine StDC.funDet hf dall ?_
  unfold itHvSgC itDatC itParC
  simp only [permK]
  omega

end GI.Impl
