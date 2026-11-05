module

public import Workspace.RowTransfers
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Data.Finset.Dedup

@[expose] public section

open scoped commutatorElement

/-! Concrete coordinate subgroups underlying Theorem A.18. -/
namespace GI
variable {I H : Type*} [DecidableEq I] [Group H]

def rowEval (i : I) : (I → H) →* H where
  toFun x := x i
  map_one' := rfl
  map_mul' _ _ := rfl

def rowSingle (j : I) (n : H) : I → H := fun r => if r = j then n else 1

def rowSingleHom (j : I) : H →* (I → H) where
  toFun := rowSingle j
  map_one' := by funext r; simp [rowSingle]
  map_mul' n p := by funext r; by_cases hr : r = j <;> simp [rowSingle, hr]

def rowKernelImage (K : Subgroup (I → H)) (i j : I) : Subgroup H :=
  (K ⊓ (rowEval i).ker).map (rowEval j)

def rowSingleKernel (K : Subgroup (I → H)) (j : I) : Subgroup H :=
  K.comap (rowSingleHom j)

def RowSubdirect (K : Subgroup (I → H)) : Prop :=
  ∀ j n, ∃ x ∈ K, x j = n

omit [DecidableEq I] in
theorem mem_rowKernelImage (K : Subgroup (I → H)) (i j : I) (n : H) :
    n ∈ rowKernelImage K i j ↔ ∃ x ∈ K, x i = 1 ∧ x j = n := by
  constructor
  · rintro ⟨x, ⟨hx, hxi⟩, hxj⟩
    exact ⟨x, hx, hxi, hxj⟩
  · rintro ⟨x, hx, hxi, hxj⟩
    exact ⟨x, ⟨hx, hxi⟩, hxj⟩

theorem mem_rowSingleKernel (K : Subgroup (I → H)) (j : I) (n : H) :
    n ∈ rowSingleKernel K j ↔ rowSingle j n ∈ K := Iff.rfl

theorem row_single_le_kernel (K : Subgroup (I → H)) {i j : I} (hij : i ≠ j) :
    rowSingleKernel K j ≤ rowKernelImage K i j := by
  intro n hn
  exact (mem_rowKernelImage K i j n).2
    ⟨rowSingle j n, hn, by simp [rowSingle, hij], by simp [rowSingle]⟩

omit [DecidableEq I] in
theorem row_kernel_normal (K : Subgroup (I → H)) (hs : RowSubdirect K) (i j : I) :
    (rowKernelImage K i j).Normal := by
  constructor
  intro n hn g
  obtain ⟨x, hx, hxi, hxj⟩ := (mem_rowKernelImage K i j n).1 hn
  obtain ⟨y, hy, hyj⟩ := hs j g
  refine (mem_rowKernelImage K i j _).2
    ⟨y * x * y⁻¹, K.mul_mem (K.mul_mem hy hx) (K.inv_mem hy), ?_, ?_⟩
  · simp [hxi]
  · simp [hxj, hyj]

theorem row_single_conj (y : I → H) (j : I) (n : H) :
    y * rowSingle j n * y⁻¹ = rowSingle j (y j * n * (y j)⁻¹) := by
  funext r
  by_cases hr : r = j <;> simp [rowSingle, hr]

theorem row_single_normal (K : Subgroup (I → H)) (hs : RowSubdirect K) (j : I) :
    (rowSingleKernel K j).Normal := by
  constructor
  intro n hn g
  obtain ⟨y, hy, hyj⟩ := hs j g
  change rowSingle j (g * n * g⁻¹) ∈ K
  have hc := K.mul_mem (K.mul_mem hy hn) (K.inv_mem hy)
  change y * rowSingle j n * y⁻¹ ∈ K at hc
  rwa [row_single_conj, hyj] at hc

theorem row_single_permute {s : Equiv.Perm I} {a j : I} (n : H) (ha : s a = j) :
    rowPermute s (rowSingle j n) = rowSingle a n := by
  funext r
  have he : s r = j ↔ r = a := by rw [← ha]; exact s.injective.eq_iff
  simp only [rowPermute, rowSingle, he]

variable [Fintype I]

theorem row_kernel_image_independent (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) {i j a b : I} (hij : i ≠ j) (hab : a ≠ b) :
    rowKernelImage K i j = rowKernelImage K a b := by
  have hle : ∀ {i j a b : I}, i ≠ j → a ≠ b →
      rowKernelImage K i j ≤ rowKernelImage K a b := by
    intro i j a b hij hab n hn
    obtain ⟨x, hx, hxi, hxj⟩ := (mem_rowKernelImage K i j n).1 hn
    obtain ⟨s, hs, hsa, hsb⟩ := even_perm_maps_pair hcard hab hij
    exact (mem_rowKernelImage K a b n).2
      ⟨rowPermute s x, hinv s hs x hx, by simpa [rowPermute, hsa] using hxi,
        by simpa [rowPermute, hsb] using hxj⟩
  exact le_antisymm (hle hij hab) (hle hab hij)

theorem row_single_mem_any (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) {n : H}
    (hn : n ∈ rowSingleKernel K j) (a : I) : rowSingle a n ∈ K := by
  have hlarge : 1 < (Finset.univ : Finset I).card := by simp only [Finset.card_univ]; omega
  obtain ⟨b, _, hba⟩ := Finset.exists_mem_ne hlarge a
  obtain ⟨s, hs, hsa, _⟩ := even_perm_maps_pair hcard (Ne.symm hba) (Ne.symm hij)
  have ht := hinv s hs (rowSingle j n) hn
  rwa [row_single_permute n hsa] at ht

theorem row_transfers_from_kernel (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 5 ≤ Fintype.card I) {i j a b : I} (hij : i ≠ j) (hab : a ≠ b)
    {n : H} (hn : n ∈ rowKernelImage K i j) : rowTransfer a b n ∈ K := by
  obtain ⟨x, hx, hxi, hxj⟩ := (mem_rowKernelImage K i j n).1 hn
  rw [← hxj]
  exact row_transfer_mem K hinv hcard hij hab x hx hxi

omit [Fintype I] in
/-- Commuting transfers on two pairs sharing just one row isolates the commutator. -/
theorem row_transfer_commutator {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n p : H) :
    ⁅rowTransfer i j n, rowTransfer i k p⁆ = rowSingle i ⁅n, p⁆ := by
  funext r
  by_cases hi : r = i
  · subst r
    simp [commutatorElement_def, rowTransfer, rowSingle]
  by_cases hj : r = j
  · subst r
    simp [commutatorElement_def, rowTransfer, rowSingle, Ne.symm hij, hjk]
  by_cases hk : r = k
  · subst r
    simp [commutatorElement_def, rowTransfer, rowSingle, Ne.symm hik, Ne.symm hjk]
  · simp [commutatorElement_def, rowTransfer, rowSingle, hi, hj, hk]

theorem row_kernel_commutator_le_single (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) :
    ⁅rowKernelImage K i j, rowKernelImage K i j⁆ ≤ rowSingleKernel K j := by
  have hlt : ({i, j} : Finset I).card < (Finset.univ : Finset I).card := by
    have hs : ({i, j} : Finset I).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hk' : k ≠ i ∧ k ≠ j := by simpa using hk
  apply Subgroup.commutator_le.mpr
  intro n hn p hp
  have ht := row_transfers_from_kernel K hinv hcard hij (Ne.symm hij) hn
  have hu := row_transfers_from_kernel K hinv hcard hij (Ne.symm hk'.2) hp
  have hc := K.mul_mem (K.mul_mem (K.mul_mem ht hu) (K.inv_mem ht)) (K.inv_mem hu)
  change ⁅rowTransfer j i n, rowTransfer j k p⁆ ∈ K at hc
  rw [row_transfer_commutator (Ne.symm hij) (Ne.symm hk'.2) (Ne.symm hk'.1)] at hc
  exact hc

omit [Fintype I] in
theorem row_singles_product (l : List I) (hn : l.Nodup) (x : I → H) :
    (l.map (fun r => rowSingle r (x r))).prod = fun r => if r ∈ l then x r else 1 := by
  induction l with
  | nil => funext r; simp
  | cons a l ih =>
    obtain ⟨han, hln⟩ := List.nodup_cons.mp hn
    rw [List.map_cons, List.prod_cons, ih hln]
    funext r
    by_cases hr : r = a
    · subst r
      simp [rowSingle, han]
    · simp [rowSingle, hr]

theorem row_single_power_le (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) {i j : I} (hij : i ≠ j)
    (x : I → H) (hx : ∀ r, x r ∈ rowSingleKernel K j) : x ∈ K := by
  let l := (Finset.univ : Finset I).toList
  have heq : (l.map (fun r => rowSingle r (x r))).prod = x := by
    rw [row_singles_product l (Finset.nodup_toList _)]
    funext r
    simp [l]
  rw [← heq]
  apply list_prod_mem
  intro y hy
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hy
  exact row_single_mem_any K hinv hcard hij (hx r) r

theorem row_coordinate_difference_mem (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j)
    (x : I → H) (hx : x ∈ K) (a b : I) : (x a)⁻¹ * x b ∈ rowKernelImage K i j := by
  by_cases hab : a = b
  · subst b
    simpa using (rowKernelImage K i j).one_mem
  have hspare : 1 < ({a, b} : Finset I)ᶜ.card := by
    rw [Finset.card_compl]
    have hs : ({a, b} : Finset I).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hspare
  have hc' : c ≠ a ∧ c ≠ b := by simpa using hc
  have hd' : d ≠ a ∧ d ≠ b := by simpa using hd
  let y := x⁻¹ * rowPermute (rowCycle a b c) x
  have hy : y ∈ K := K.mul_mem (K.inv_mem hx)
    (hinv _ (row_cycle_even hab (Ne.symm hc'.2)) x hx)
  have hyd : y d = 1 := by
    simp [y, rowPermute, row_cycle_outside hd'.1 hd'.2 (Ne.symm hcd)]
  have hya : y a = (x a)⁻¹ * x b := by
    simp [y, rowPermute, row_cycle_first hab (Ne.symm hc'.1)]
  have hn := (mem_rowKernelImage K d a _).2 ⟨y, hy, hyd, hya⟩
  rwa [row_kernel_image_independent K hinv (by omega) hd'.1 hij] at hn

/-- Every row has the same image in the actual coordinate-kernel quotient. -/
theorem row_diagonal_quotient (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j)
    (x : I → H) (hx : x ∈ K) (a b : I) :
    (QuotientGroup.mk (x a) : H ⧸ rowKernelImage K i j) = QuotientGroup.mk (x b) :=
  QuotientGroup.eq.mpr (row_coordinate_difference_mem K hinv hcard hij x hx a b)

end GI
