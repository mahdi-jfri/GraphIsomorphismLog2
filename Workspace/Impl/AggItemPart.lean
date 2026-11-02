import Workspace.Impl.AggCaseMath

/-!
# Case 1: the colored orbit partition, its alignment and its stabilizer

The Case 1 item (`caseOneItem`, Section A.3, "Case 1 and balanced colored partitions") is the
overcoset of the even stabilizer of the colored orbit partition of `π(F_x)`, through an even
permutation that maps it to the partition of `π(F_y)`. A program sees the two groups only by
generators, so it computes the orbit labels `lab` (`orbits_spec`) and works with the partition
"same label" (`itpPart lab`); for orbit labels this is `labelOrbitPart` (`itpPart_eq`).

This file gives the mathematics the program needs, for any labeling `lab : Fin q → ℕ`.

1. **Alignment.** Order the points by the key (block size, label, point) and let `itpPos lab a`
   be the number of points with a smaller key. This is a bijection onto `Fin q`, and
   `itpPos lab a = start + s·m + r`, where `s` is the size of the block of `a`, `start` the
   number of points in smaller blocks, `m` the number of blocks of size `s` with a smaller label,
   and `r` the rank of `a` in its block. If the two labelings have the same number of points in
   blocks of each size, the permutation `a ↦ b` with equal positions maps blocks to blocks
   (`itpAlign_smul`). Otherwise no permutation does (`itpCnt_eq_of_smul`).
2. **Generators of the stabilizer** (`itp_closure_eq`): the transpositions of each point with
   the center of its block, and the swaps of two blocks of equal size that keep the ranks.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm Finset

variable {q : ℕ} (lab : Fin q → ℕ)

/-! ### The partition of a labeling -/

/-- The block of `a`: the points with the label of `a`. -/
def itpBlk (a : Fin q) : Finset (Fin q) := univ.filter fun y => lab y = lab a

/-- The colored partition of a labeling: blocks are the label classes, colored by their size. -/
def itpPart : ColPart (Fin q) := ⟨itpBlk lab, fun a => (itpBlk lab a).card⟩

/-- The size of the block of `a`. -/
def itpSz (a : Fin q) : ℕ := (itpBlk lab a).card

variable {lab}

theorem itp_mem_blk {a y : Fin q} : y ∈ itpBlk lab a ↔ lab y = lab a := by simp [itpBlk]

theorem itpBlk_congr {a b : Fin q} (h : lab a = lab b) : itpBlk lab a = itpBlk lab b := by
  ext y; simp [itp_mem_blk, h]

theorem itpSz_congr {a b : Fin q} (h : lab a = lab b) : itpSz lab a = itpSz lab b := by
  simp only [itpSz, itpBlk_congr h]

/-- **When a permutation maps one partition to another**: exactly when it maps the relation "same
label" of the first labeling to that of the second. -/
theorem itpPart_smul_iff (labY : Fin q → ℕ) (σ : Perm (Fin q)) :
    σ • itpPart lab = itpPart labY ↔ ∀ a b, (labY (σ a) = labY (σ b) ↔ lab a = lab b) := by
  constructor
  · intro h a b
    have h1 := congrArg (fun z : ColPart (Fin q) => z.blk (σ b)) h
    simp only [ColPart.smul_blk, itpPart, Perm.inv_apply_self] at h1
    have h2 : σ a ∈ itpBlk labY (σ b) ↔ σ a ∈ (itpBlk lab b).map σ.toEmbedding := by rw [h1]
    rw [itp_mem_blk, Finset.mem_map_equiv, itp_mem_blk] at h2
    simpa using h2
  · intro h
    have hblk : ∀ a, (itpBlk lab (σ⁻¹ a)).map σ.toEmbedding = itpBlk labY a := by
      intro a
      ext y
      rw [Finset.mem_map_equiv, itp_mem_blk, itp_mem_blk]
      have := h (σ.symm y) (σ⁻¹ a)
      simp only [Equiv.apply_symm_apply, Perm.apply_inv_self] at this
      exact this.symm
    ext a y
    · simp only [ColPart.smul_blk, itpPart]
      rw [hblk]
    · simp only [ColPart.smul_col, itpPart]
      rw [← hblk a, Finset.card_map]

/-- **The stabilizer of the partition**: the permutations that keep the relation "same label". -/
theorem itp_mem_stab {σ : Perm (Fin q)} :
    σ ∈ MulAction.stabilizer (Perm (Fin q)) (itpPart lab) ↔
      ∀ a b, (lab (σ a) = lab (σ b) ↔ lab a = lab b) :=
  itpPart_smul_iff lab σ

/-- A permutation that maps the partition of `lab` to that of `labY` keeps block sizes. -/
theorem itpSz_of_smul {labY : Fin q → ℕ} {σ : Perm (Fin q)}
    (h : σ • itpPart lab = itpPart labY) (a : Fin q) : itpSz labY (σ a) = itpSz lab a := by
  have h1 := congrArg (fun z : ColPart (Fin q) => z.col (σ a)) h
  simp only [ColPart.smul_col, itpPart, Perm.inv_apply_self] at h1
  exact h1.symm

/-! ### Positions -/

variable (lab) in
/-- The key of a point: (block size, label, point), ordered lexicographically. -/
def itpKey (a : Fin q) : Lex (ℕ × Lex (ℕ × ℕ)) := toLex (itpSz lab a, toLex (lab a, (a : ℕ)))

variable (lab) in
/-- The position of a point: the number of points with a smaller key. -/
def itpPos (a : Fin q) : ℕ := (univ.filter fun y => itpKey lab y < itpKey lab a).card

theorem itpKey_lt_iff {a b : Fin q} : itpKey lab a < itpKey lab b ↔
    itpSz lab a < itpSz lab b ∨ (itpSz lab a = itpSz lab b ∧
      (lab a < lab b ∨ (lab a = lab b ∧ (a : ℕ) < b))) := by
  simp only [itpKey, Prod.Lex.toLex_lt_toLex]

theorem itpKey_injective : Function.Injective (itpKey lab) := by
  intro a b h
  simp only [itpKey, toLex_inj, Prod.mk.injEq] at h
  exact Fin.ext h.2.2

theorem itpPos_lt_of_key {a b : Fin q} (h : itpKey lab a < itpKey lab b) :
    itpPos lab a < itpPos lab b := by
  refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.trans h
  · have : a ∈ univ.filter fun y => itpKey lab y < itpKey lab a :=
      hsub (by simp [h])
    simp at this

theorem itpPos_lt (a : Fin q) : itpPos lab a < q := by
  have : itpPos lab a < (univ : Finset (Fin q)).card :=
    Finset.card_lt_card ⟨Finset.subset_univ _, fun hsub => by
      have := hsub (Finset.mem_univ a)
      simp at this⟩
  simpa using this

theorem itpPos_injective : Function.Injective (itpPos lab) := by
  intro a b h
  by_contra hne
  rcases lt_or_gt_of_ne (fun e => hne (itpKey_injective e)) with h' | h'
  · exact absurd h (itpPos_lt_of_key h').ne
  · exact absurd h (itpPos_lt_of_key h').ne'

variable (lab) in
/-- The positions as a permutation of `Fin q`. -/
noncomputable def itpPosE : Perm (Fin q) :=
  Equiv.ofBijective (fun a => ⟨itpPos lab a, itpPos_lt a⟩)
    (Finite.injective_iff_bijective.1 fun _ _ h => itpPos_injective (Fin.mk.inj_iff.1 h))

@[simp] theorem itpPosE_val (a : Fin q) : ((itpPosE lab a : Fin q) : ℕ) = itpPos lab a := rfl

/-! ### The decomposition of a position -/

variable (lab) in
/-- The number of points in blocks smaller than `s`. -/
def itpStart (s : ℕ) : ℕ := (univ.filter fun y : Fin q => itpSz lab y < s).card

variable (lab) in
/-- The number of points in blocks of size `s`. -/
def itpCnt (s : ℕ) : ℕ := (univ.filter fun y : Fin q => itpSz lab y = s).card

variable (lab) in
/-- The number of blocks of the size of `a` with a smaller label. -/
def itpM (a : Fin q) : ℕ :=
  ((univ.filter fun y => itpSz lab y = itpSz lab a ∧ lab y < lab a).image lab).card

variable (lab) in
/-- The rank of `a` in its block. -/
def itpRk (a : Fin q) : ℕ := (univ.filter fun y => lab y = lab a ∧ (y : ℕ) < a).card

/-- The points of the size of `a` with a smaller label fill `itpM` whole blocks. -/
theorem itp_card_smaller (a : Fin q) :
    (univ.filter fun y => itpSz lab y = itpSz lab a ∧ lab y < lab a).card =
      itpSz lab a * itpM lab a := by
  classical
  set A := univ.filter fun y => itpSz lab y = itpSz lab a ∧ lab y < lab a
  rw [Finset.card_eq_sum_card_image lab A, itpM, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hℓ
  have hyA := (Finset.mem_filter.1 hy).2
  rw [← hyA.1]
  congr 1
  ext z
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, itp_mem_blk]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨(itpSz_congr h).trans hyA.1, h ▸ hyA.2⟩, h⟩

/-- **The decomposition of a position**: `pos a = start + s·m + r`. -/
theorem itpPos_eq (a : Fin q) :
    itpPos lab a = itpStart lab (itpSz lab a) + itpSz lab a * itpM lab a + itpRk lab a := by
  classical
  rw [← itp_card_smaller, itpPos, itpStart, itpRk]
  have hsplit : (univ.filter fun y => itpKey lab y < itpKey lab a) =
      ((univ.filter fun y : Fin q => itpSz lab y < itpSz lab a) ∪
        (univ.filter fun y => itpSz lab y = itpSz lab a ∧ lab y < lab a)) ∪
        (univ.filter fun y => lab y = lab a ∧ (y : ℕ) < a) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, itpKey_lt_iff]
    constructor
    · rintro (h | ⟨h1, h2 | ⟨h2, h3⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr ⟨h2, h3⟩
    · rintro ((h | ⟨h1, h2⟩) | ⟨h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact Or.inr ⟨itpSz_congr h2, Or.inr ⟨h2, h3⟩⟩
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  · rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at h1 h2
    have := itpSz_congr h2.1
    omega

theorem itpRk_lt (a : Fin q) : itpRk lab a < itpSz lab a := by
  classical
  refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact itp_mem_blk.2 hy.1
  · have := hsub (itp_mem_blk.2 rfl : a ∈ itpBlk lab a)
    simp at this

/-- The positions of the points of size `s` lie in `[start s, start s + cnt s)`. -/
theorem itpPos_lt_start_cnt (a : Fin q) :
    itpPos lab a < itpStart lab (itpSz lab a) + itpCnt lab (itpSz lab a) := by
  classical
  rw [itpPos_eq, add_assoc]
  refine Nat.add_lt_add_left ?_ _
  rw [← itp_card_smaller, itpRk, ← Finset.card_union_of_disjoint]
  · refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
      rcases hy with h | h
      · exact h.1
      · exact itpSz_congr h.1
    · have := hsub (show a ∈ univ.filter fun y : Fin q => itpSz lab y = itpSz lab a by simp)
      simp at this
  · rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega

/-- Blocks of size below `s'` contain the blocks below `s` and those of size `s`, for `s < s'`. -/
theorem itpStart_add_le {s s' : ℕ} (h : s < s') :
    itpStart lab s + itpCnt lab s ≤ itpStart lab s' := by
  classical
  rw [itpStart, itpCnt, ← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
    omega
  · rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega

/-- `start s` is the sum of the counts below `s`. -/
theorem itpStart_eq_sum (s : ℕ) :
    itpStart lab s = ∑ t ∈ Finset.range s, itpCnt lab t := by
  classical
  rw [itpStart, Finset.card_eq_sum_card_fiberwise (f := itpSz lab) (t := Finset.range s)
    (fun y hy => by simpa using hy)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [itpCnt, Finset.filter_filter]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have := Finset.mem_range.1 ht
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ this, h⟩

/-- Same label exactly when same size and same number of smaller blocks. -/
theorem itp_lab_eq_iff {a b : Fin q} :
    lab a = lab b ↔ itpSz lab a = itpSz lab b ∧ itpM lab a = itpM lab b := by
  classical
  constructor
  · intro h
    refine ⟨itpSz_congr h, ?_⟩
    simp only [itpM, itpSz_congr h, h]
  · rintro ⟨hs, hm⟩
    by_contra hne
    have key : ∀ {a b : Fin q}, itpSz lab a = itpSz lab b → lab a < lab b →
        itpM lab a < itpM lab b := by
      intro a' b' hs hlt
      refine Finset.card_lt_card ⟨fun ℓ hℓ => ?_, fun hsub => ?_⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hℓ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact Finset.mem_image.2 ⟨y, by simp [hy.1, hs, hy.2.trans hlt], rfl⟩
      · have : lab a' ∈
            (univ.filter fun y => itpSz lab y = itpSz lab a' ∧ lab y < lab a').image lab :=
          hsub (Finset.mem_image.2 ⟨a', by simp [hs, hlt], rfl⟩)
        obtain ⟨y, hy, hya⟩ := Finset.mem_image.1 this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hm (key hs h).ne
    · exact absurd hm (key hs.symm h).ne'

/-! ### Alignment -/

/-- **Equal positions give equal size, block number and rank**, when the two labelings have the
same number of points in blocks of each size. -/
theorem itpPos_eq_iff {labY : Fin q → ℕ} (hc : ∀ s, itpCnt lab s = itpCnt labY s)
    {a b : Fin q} (h : itpPos labY b = itpPos lab a) :
    itpSz labY b = itpSz lab a ∧ itpM labY b = itpM lab a ∧ itpRk labY b = itpRk lab a := by
  have hst : ∀ s, itpStart lab s = itpStart labY s := fun s => by
    rw [itpStart_eq_sum, itpStart_eq_sum]
    exact Finset.sum_congr rfl fun t _ => hc t
  have ha1 := itpPos_eq (lab := lab) a
  have hb1 := itpPos_eq (lab := labY) b
  have ha2 := itpPos_lt_start_cnt (lab := lab) a
  have hb2 := itpPos_lt_start_cnt (lab := labY) b
  rw [← hst, ← hc] at hb2
  rw [← hst] at hb1
  have hs : itpSz labY b = itpSz lab a := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := itpStart_add_le (lab := lab) hlt
      omega
    · have := itpStart_add_le (lab := lab) hlt
      omega
  rw [hs] at hb1
  have hra := itpRk_lt (lab := lab) a
  have hrb := itpRk_lt (lab := labY) b
  rw [hs] at hrb
  have e : itpSz lab a * itpM labY b + itpRk labY b = itpSz lab a * itpM lab a + itpRk lab a := by
    omega
  have hpos : 0 < itpSz lab a := by omega
  have hm : itpM labY b = itpM lab a := by
    have := congrArg (· / itpSz lab a) e
    simp only at this
    rwa [Nat.mul_add_div hpos, Nat.mul_add_div hpos, Nat.div_eq_of_lt hra,
      Nat.div_eq_of_lt hrb, add_zero, add_zero] at this
  refine ⟨hs, hm, ?_⟩
  rw [hm] at e
  omega

variable (lab) in
/-- **The aligning permutation**: `a` goes to the point of the second labeling with the same
position. -/
noncomputable def itpAlign (labY : Fin q → ℕ) : Perm (Fin q) := (itpPosE lab).trans (itpPosE labY).symm

theorem itpPos_align (labY : Fin q → ℕ) (a : Fin q) :
    itpPos labY (itpAlign lab labY a) = itpPos lab a := by
  show itpPos labY ((itpPosE labY).symm (itpPosE lab a)) = _
  rw [← itpPosE_val, Equiv.apply_symm_apply, itpPosE_val]

/-- **The alignment maps the partition of `lab` to that of `labY`** when the two have the same
number of points in blocks of each size. -/
theorem itpAlign_smul {labY : Fin q → ℕ} (hc : ∀ s, itpCnt lab s = itpCnt labY s) :
    itpAlign lab labY • itpPart lab = itpPart labY := by
  rw [itpPart_smul_iff]
  intro a b
  obtain ⟨ha1, ha2, -⟩ := itpPos_eq_iff hc (itpPos_align labY a)
  obtain ⟨hb1, hb2, -⟩ := itpPos_eq_iff hc (itpPos_align labY b)
  rw [itp_lab_eq_iff (a := itpAlign lab labY a) (b := itpAlign lab labY b),
    itp_lab_eq_iff (a := a) (b := b), ha1, ha2, hb1, hb2]

/-- **No permutation maps the partitions when the counts differ.** -/
theorem itpCnt_eq_of_smul {labY : Fin q → ℕ} {σ : Perm (Fin q)}
    (h : σ • itpPart lab = itpPart labY) (s : ℕ) : itpCnt lab s = itpCnt labY s := by
  classical
  rw [itpCnt, itpCnt, ← Finset.card_map σ.toEmbedding]
  congr 1
  ext y
  simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← itpSz_of_smul h (σ.symm y), Equiv.apply_symm_apply]

/-- **A permutation maps the partitions exactly when the counts agree.** -/
theorem itp_exists_smul_iff (labY : Fin q → ℕ) :
    (∃ σ : Perm (Fin q), σ • itpPart lab = itpPart labY) ↔
      ∀ s, itpCnt lab s = itpCnt labY s :=
  ⟨fun ⟨_, h⟩ => itpCnt_eq_of_smul h, fun hc => ⟨_, itpAlign_smul hc⟩⟩

end GI.Impl
