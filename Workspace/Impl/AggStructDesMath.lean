module

public import Workspace.Impl.AggStructDes
public import Workspace.Impl.AggStructPat

@[expose] public section

/-!
# The Case 3 test on lists of numbers

The program of the Case 3 test `StDes` (`AggStructDes.lean`) reads the refined coloring `c` as
the list `stDL c` of its values in the order of `finFunctionFinEquiv` (the order of
`encKColoring`), and the tuple `t` as the list `stL t` of its entries. This file gives the
test as a function `stDesB` of these two lists, built only from what the program computes:
list lookups, counts, and first indices. It proves `stDesB = decide (StDes c t _)`
(`stDesB_iff`).

The steps, for a prefix length `m < κ` (the prefix of `t` is `x`):
* `stDCol`: the color `c(x, z₁, z₂, …, z₂)`, at the index of the tuple, computed by Horner's rule
  (`stDHor`, `stDHor_eq`);
* `stDV`: the vertex colors `z ↦ c(x, z, …, z)` of the `q` labels; the number of times a color
  occurs in this list is the size of its vertex class (`stDV_count`);
* `stDBal`: no label lies in a class of at least `3q/4` points, which is outcome (a)
  (`stDBal_iff`);
* `stDSplit`: with `j` the dominant color, the first pair `p₀` of distinct labels of class `j`
  exists, and some pair of distinct labels of class `j` has another pair color; this is outcome
  (b) (`stDSplit_iff`);
* `stDHit`: outcome (a) or (b) at `m` (`stDHit_iff`);
* `stDesB`: at the first `m` with `stDHit`, outcome (a), or the class of `t κ` has at least
  `3q/4` points.

Pairs of labels are the numbers `p < q²`, with `p / q` and `p % q` the two labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Cited Equiv Equiv.Perm

/-! ### The index of a tuple -/

/-- Horner's rule on the entries `e (κ - 1), e (κ - 2), …`: after `i` steps. -/
def stDHor (q κ : ℕ) (e : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => stDHor q κ e i * q + e (κ - 1 - i)

theorem stDHor_sum (q κ : ℕ) (e : ℕ → ℕ) :
    ∀ i, i ≤ κ → stDHor q κ e i = ∑ j ∈ Finset.range i, e (κ - i + j) * q ^ j
  | 0, _ => by simp [stDHor]
  | i + 1, hi => by
    rw [stDHor, stDHor_sum q κ e i (by omega), Finset.sum_range_succ', Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show κ - (i + 1) + (j + 1) = κ - i + j by omega, pow_succ]; ring
    · simp only [pow_zero, mul_one, Nat.add_zero]
      congr 1
      omega

/-- **Horner's rule gives the index**: `∑ e j q^j`. -/
theorem stDHor_eq (q κ : ℕ) (e : ℕ → ℕ) :
    stDHor q κ e κ = ∑ j ∈ Finset.range κ, e j * q ^ j := by
  rw [stDHor_sum q κ e κ le_rfl]
  simp

/-- The index of a tuple in the order of `finFunctionFinEquiv`, by Horner's rule. -/
theorem stDHor_tuple {q κ : ℕ} (u : Fin κ → Fin q) (e : ℕ → ℕ)
    (he : ∀ i : Fin κ, e i = u i) : stDHor q κ e κ = finFunctionFinEquiv u := by
  rw [stDHor_eq, finFunctionFinEquiv_apply, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i]

/-! ### The colors as a list -/

/-- The values of a `κ`-ary coloring, in the order of `finFunctionFinEquiv`. -/
def stDL {q κ : ℕ} (c : (Fin κ → Fin q) → ℕ) : List ℕ :=
  (List.finRange (q ^ κ)).map fun j => c (finFunctionFinEquiv.symm j)

theorem natList_stDL {q κ : ℕ} (c : (Fin κ → Fin q) → ℕ) :
    GI.Lang.natList (stDL c) = encKColoring c := by
  simp [stDL, encKColoring, GI.Lang.natList, List.map_map, Function.comp_def]

theorem stDL_length {q κ : ℕ} (c : (Fin κ → Fin q) → ℕ) : (stDL c).length = q ^ κ := by
  simp [stDL]

theorem stDL_getD {q κ : ℕ} (c : (Fin κ → Fin q) → ℕ) (u : Fin κ → Fin q) :
    (stDL c).getD (finFunctionFinEquiv u) 0 = c u := by
  have hlt : (finFunctionFinEquiv u : ℕ) < (stDL c).length := by
    rw [stDL_length]; exact (finFunctionFinEquiv u).isLt
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [stDL, List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta,
    Equiv.symm_apply_apply]

/-- Entry `i` of the tuple `(x, z₁, z₂, …, z₂)`, with `x` the first `m` entries of `tl`. -/
def stDE (tl : List ℕ) (m z₁ z₂ : ℕ) (i : ℕ) : ℕ :=
  if i < m then tl.getD i 0 else if i = m then z₁ else z₂

/-- **The color `c(x, z₁, z₂, …, z₂)`**, read off the list of colors. -/
def stDCol (dl tl : List ℕ) (q κ m z₁ z₂ : ℕ) : ℕ :=
  dl.getD (stDHor q κ (stDE tl m z₁ z₂) κ) 0

theorem stDCol_eq {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ)
    {m : ℕ} (hm : m ≤ ℓ) (z₁ z₂ : Fin q) :
    stDCol (stDL c) (stL fun i => (t i : ℕ)) q κ m z₁ z₂ = skel₂ c (preT t h0 m) z₁ z₂ := by
  unfold stDCol skel₂
  rw [← stDL_getD c]
  congr 2
  refine stDHor_tuple _ _ fun i => ?_
  simp only [stDE, padTuple₂, preT]
  by_cases h1 : (i : ℕ) < m
  · rw [if_pos h1, dif_pos h1, dif_pos (by omega : (i : ℕ) < ℓ)]
    have hlt : (i : ℕ) < (stL fun i => (t i : ℕ)).length := by simp [stL]; omega
    rw [List.getD_eq_getElem _ _ hlt]
    simp [stL]
  · rw [if_neg h1, dif_neg h1]
    split_ifs <;> rfl

/-! ### Vertex classes -/

/-- The vertex colors `z ↦ c(x, z, …, z)` of the `q` labels. -/
def stDV (dl tl : List ℕ) (q κ m : ℕ) : List ℕ :=
  (List.range q).map fun z => stDCol dl tl q κ m z z

theorem stDV_length (dl tl : List ℕ) (q κ m : ℕ) : (stDV dl tl q κ m).length = q := by
  simp [stDV]

theorem stDV_eq {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ)
    {m : ℕ} (hm : m ≤ ℓ) :
    stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m =
      (List.finRange q).map fun z => skel₁ c (preT t h0 m) z := by
  unfold stDV
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun z _ => ?_
  simp only [Function.comp_apply]
  rw [stDCol_eq c t h0 hm, skel₁, skel₂, padTuple₂_self]

theorem stDV_getD {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ)
    {m : ℕ} (hm : m ≤ ℓ) (z : Fin q) :
    (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m).getD z 0 = skel₁ c (preT t h0 m) z := by
  rw [stDV_eq c t h0 hm]
  have hlt : (z : ℕ) < ((List.finRange q).map fun z => skel₁ c (preT t h0 m) z).length := by simp
  rw [List.getD_eq_getElem _ _ hlt]
  simp

theorem st_count_map_finRange {q : ℕ} (f : Fin q → ℕ) (j : ℕ) :
    ((List.finRange q).map f).count j = (Finset.univ.filter fun z => f z = j).card := by
  classical
  rw [List.count_eq_length_filter, List.filter_map, List.length_map]
  have hnd : ((List.finRange q).filter ((fun x => x == j) ∘ f)).Nodup :=
    (List.nodup_finRange q).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext z
  simp

/-- **Counts in the list of vertex colors are class sizes.** -/
theorem stDV_count {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ)
    {m : ℕ} (hm : m ≤ ℓ) (j : ℕ) :
    (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m).count j = vcard c (preT t h0 m) j := by
  rw [stDV_eq c t h0 hm, st_count_map_finRange]
  rfl

/-! ### Outcome (a) -/

/-- The class of color `j` in `V` has at least `3q/4` points. -/
def stDDomV (V : List ℕ) (q j : ℕ) : Bool := decide (3 * q ≤ 4 * V.count j)

/-- Label `z` lies in a class of at least `3q/4` points. -/
def stDDom (V : List ℕ) (q z : ℕ) : Bool := stDDomV V q (V.getD z 0)

/-- **Outcome (a)**: no label lies in a class of at least `3q/4` points. -/
def stDBal (V : List ℕ) (q : ℕ) : Bool := !(List.range q).any (stDDom V q)

section Prefix

variable {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ) {m : ℕ}
  (hm : m ≤ ℓ)

include hm in
theorem stDDomV_iff (j : ℕ) :
    stDDomV (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q j = true ↔
      Dominant c (preT t h0 m) j := by
  rw [stDDomV, decide_eq_true_iff, stDV_count c t h0 hm]
  rfl

include hm in
theorem stDDom_iff (z : Fin q) :
    stDDom (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q z = true ↔
      Dominant c (preT t h0 m) (skel₁ c (preT t h0 m) z) := by
  rw [stDDom, stDV_getD c t h0 hm, stDDomV_iff c t h0 hm]

include hm in
/-- **Outcome (a)** as a list test (for `q > 0`). -/
theorem stDBal_iff (hq : 0 < q) :
    stDBal (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q = true ↔
      Balanced c (preT t h0 m) := by
  rw [stDBal, Bool.not_eq_true', List.any_eq_false]
  constructor
  · intro h j
    by_contra hj
    push Not at hj
    have hpos : 0 < vcard c (preT t h0 m) j := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have := h z (List.mem_range.2 z.isLt)
    rw [show stDDom _ q (z : ℕ) = true from (stDDom_iff c t h0 hm z).2 (by
      unfold Dominant; rw [hz]; exact hj)] at this
    exact absurd this (by simp)
  · intro h z hz
    have hz' := List.mem_range.1 hz
    have := stDDom_iff c t h0 hm ⟨z, hz'⟩
    simp only at this
    cases hb : stDDom (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q z
    · simp
    · have hd := this.1 hb
      unfold Dominant at hd
      have := h (skel₁ c (preT t h0 m) ⟨z, hz'⟩)
      omega

include hm in
/-- If outcome (a) fails, the first label in a large class gives a dominant color. -/
theorem stDDom_first
    (hb : stDBal (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q = false) :
    (List.range q).findIdx (stDDom (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q) < q ∧
      Dominant c (preT t h0 m) ((stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m).getD
        ((List.range q).findIdx (stDDom (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q))
          0) := by
  set V := stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m with hV
  have hany : (List.range q).any (stDDom V q) = true := by
    rw [stDBal] at hb; simpa using hb
  obtain ⟨z, hz, hzp⟩ := List.any_eq_true.1 hany
  have hlt : (List.range q).findIdx (stDDom V q) < (List.range q).length :=
    List.findIdx_lt_length_of_exists ⟨z, hz, hzp⟩
  rw [List.length_range] at hlt
  refine ⟨hlt, ?_⟩
  have hspec := List.findIdx_getElem (w := (by simpa using hlt :
    (List.range q).findIdx (stDDom V q) < (List.range q).length))
  rw [List.getElem_range] at hspec
  have := (stDDom_iff c t h0 hm ⟨_, hlt⟩).1 hspec
  rwa [← stDV_getD c t h0 hm] at this

end Prefix

/-! ### Outcome (b) -/

/-- `p < q²` codes a pair of distinct labels, both of color `j`. -/
def stDRef (V : List ℕ) (q j p : ℕ) : Bool :=
  decide (p / q ≠ p % q ∧ V.getD (p / q) 0 = j ∧ V.getD (p % q) 0 = j)

/-- **Outcome (b) for the color `j`**: a first pair `p₀` of distinct labels of class `j` exists,
and some pair of distinct labels of class `j` has a pair color other than that of `p₀`. -/
def stDSplit (dl tl : List ℕ) (q κ m : ℕ) (V : List ℕ) (j : ℕ) : Bool :=
  decide ((List.range (q * q)).findIdx (stDRef V q j) < q * q) &&
    (List.range (q * q)).any fun p => stDRef V q j p &&
      !decide (stDCol dl tl q κ m (p / q) (p % q) =
        stDCol dl tl q κ m ((List.range (q * q)).findIdx (stDRef V q j) / q)
          ((List.range (q * q)).findIdx (stDRef V q j) % q))

theorem st_pair_lt {q u v : ℕ} (hu : u < q) (hv : v < q) : u * q + v < q * q := by
  have : (u + 1) * q ≤ q * q := Nat.mul_le_mul_right _ hu
  rw [Nat.add_mul, one_mul] at this
  omega

theorem st_pair_div {q u v : ℕ} (hv : v < q) : (u * q + v) / q = u := by
  have hq : 0 < q := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hv, zero_add]

theorem st_pair_mod {q u v : ℕ} (hv : v < q) : (u * q + v) % q = v := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem st_div_lt {q p : ℕ} (hp : p < q * q) : p / q < q :=
  Nat.div_lt_of_lt_mul hp

theorem st_mod_lt {q p : ℕ} (hp : p < q * q) : p % q < q :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by subst h; simp at hp)

section Split

variable {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ) {m : ℕ}
  (hm : m ≤ ℓ)

include hm in
theorem stDRef_iff {j p : ℕ} (hp : p < q * q) :
    stDRef (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q j p = true ↔
      ((⟨p / q, st_div_lt hp⟩ : Fin q) ≠ ⟨p % q, st_mod_lt hp⟩ ∧
        skel₁ c (preT t h0 m) ⟨p / q, st_div_lt hp⟩ = j ∧
        skel₁ c (preT t h0 m) ⟨p % q, st_mod_lt hp⟩ = j) := by
  rw [stDRef, decide_eq_true_iff]
  have h1 := stDV_getD c t h0 hm ⟨p / q, st_div_lt hp⟩
  have h2 := stDV_getD c t h0 hm ⟨p % q, st_mod_lt hp⟩
  simp only at h1 h2
  rw [h1, h2]
  simp only [Ne, Fin.mk.injEq]

include hm in
/-- **Outcome (b)** as a list test, for the dominant color `j`. -/
theorem stDSplit_iff (j : ℕ) :
    stDSplit (stDL c) (stL fun i => (t i : ℕ)) q κ m
        (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) j = true ↔
      ∃ u v w y : Fin q, skel₁ c (preT t h0 m) u = j ∧ skel₁ c (preT t h0 m) v = j ∧
        skel₁ c (preT t h0 m) w = j ∧ skel₁ c (preT t h0 m) y = j ∧ u ≠ v ∧ w ≠ y ∧
        skel₂ c (preT t h0 m) u v ≠ skel₂ c (preT t h0 m) w y := by
  set V := stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m with hV
  set x := preT t h0 m
  have hcol : ∀ p (hp : p < q * q), stDCol (stDL c) (stL fun i => (t i : ℕ)) q κ m (p / q) (p % q) =
      skel₂ c x ⟨p / q, st_div_lt hp⟩ ⟨p % q, st_mod_lt hp⟩ := fun p hp =>
    stDCol_eq c t h0 hm ⟨p / q, st_div_lt hp⟩ ⟨p % q, st_mod_lt hp⟩
  -- the code of a pair
  have hcode : ∀ u v : Fin q, (u : ℕ) * q + v < q * q ∧
      (⟨((u : ℕ) * q + v) / q, st_div_lt (st_pair_lt u.isLt v.isLt)⟩ : Fin q) = u ∧
      (⟨((u : ℕ) * q + v) % q, st_mod_lt (st_pair_lt u.isLt v.isLt)⟩ : Fin q) = v := by
    intro u v
    exact ⟨st_pair_lt u.isLt v.isLt, Fin.ext (st_pair_div v.isLt), Fin.ext (st_pair_mod v.isLt)⟩
  unfold stDSplit
  rw [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hp0, hany⟩
    obtain ⟨p, hp, hpt⟩ := List.any_eq_true.1 hany
    have hp' := List.mem_range.1 hp
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hpt
    obtain ⟨hr, hne⟩ := hpt
    have hr0 : stDRef V q j ((List.range (q * q)).findIdx (stDRef V q j)) = true := by
      have := List.findIdx_getElem (w := (by simpa using hp0 :
        (List.range (q * q)).findIdx (stDRef V q j) < (List.range (q * q)).length))
      rwa [List.getElem_range] at this
    obtain ⟨n1, a1, b1⟩ := (stDRef_iff c t h0 hm hp').1 hr
    obtain ⟨n0, a0, b0⟩ := (stDRef_iff c t h0 hm hp0).1 hr0
    refine ⟨_, _, _, _, a0, b0, a1, b1, n0, n1, fun he => hne ?_⟩
    rw [hcol p hp', hcol _ hp0, he]
  · rintro ⟨u, v, w, y, hu, hv, hw, hy, huv, hwy, hne⟩
    have hcol' : ∀ a b : Fin q, stDCol (stDL c) (stL fun i => (t i : ℕ)) q κ m
        (((a : ℕ) * q + b) / q) (((a : ℕ) * q + b) % q) = skel₂ c x a b := by
      intro a b
      rw [st_pair_div b.isLt, st_pair_mod b.isLt]
      exact stDCol_eq c t h0 hm a b
    have href : ∀ a b : Fin q, a ≠ b → skel₁ c x a = j → skel₁ c x b = j →
        stDRef V q j ((a : ℕ) * q + b) = true := by
      intro a b hab ha hb
      unfold stDRef
      rw [st_pair_div b.isLt, st_pair_mod b.isLt, stDV_getD c t h0 hm a, stDV_getD c t h0 hm b,
        decide_eq_true_iff]
      exact ⟨fun h => hab (Fin.ext h), ha, hb⟩
    have hruv := href u v huv hu hv
    have hrwy := href w y hwy hw hy
    have hp0 : (List.range (q * q)).findIdx (stDRef V q j) < q * q := by
      have := List.findIdx_lt_length_of_exists (p := stDRef V q j) (xs := List.range (q * q))
        ⟨_, List.mem_range.2 (hcode u v).1, hruv⟩
      simpa using this
    refine ⟨hp0, ?_⟩
    rw [List.any_eq_true]
    set p0 := (List.range (q * q)).findIdx (stDRef V q j)
    by_cases h1 : skel₂ c x u v = skel₂ c x ⟨p0 / q, st_div_lt hp0⟩ ⟨p0 % q, st_mod_lt hp0⟩
    · refine ⟨(w : ℕ) * q + y, List.mem_range.2 (hcode w y).1, ?_⟩
      rw [hrwy, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not, hcol' w y,
        hcol _ hp0, ← h1]
      exact fun h => hne h.symm
    · refine ⟨(u : ℕ) * q + v, List.mem_range.2 (hcode u v).1, ?_⟩
      rw [hruv, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not, hcol' u v,
        hcol _ hp0]
      exact h1

end Split

/-! ### A hit, and the test -/

/-- The first label in a class of at least `3q/4` points (`q` if there is none). -/
def stDZ (V : List ℕ) (q : ℕ) : ℕ := (List.range q).findIdx (stDDom V q)

/-- **Outcome (a) or (b) at the prefix of length `m`.** -/
def stDHit (dl tl : List ℕ) (q κ m : ℕ) : Bool :=
  decide (m < κ) && (stDBal (stDV dl tl q κ m) q ||
    (decide (m + 1 < κ) && stDSplit dl tl q κ m (stDV dl tl q κ m)
      ((stDV dl tl q κ m).getD (stDZ (stDV dl tl q κ m) q) 0)))

theorem stDHit_iff {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ)
    (hκ : κ ≤ ℓ) (hq : 0 < q) (m : ℕ) :
    stDHit (stDL c) (stL fun i => (t i : ℕ)) q κ m = true ↔ Hit c t h0 m := by
  unfold stDHit Hit
  rw [Bool.and_eq_true, decide_eq_true_iff]
  refine and_congr_right fun hmk => ?_
  have hm : m ≤ ℓ := by omega
  rw [Bool.or_eq_true, stDBal_iff c t h0 hm hq]
  by_cases hb : Balanced c (preT t h0 m)
  · simp only [hb, true_or]
  · have hbf : stDBal (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q = false := by
      cases h : stDBal (stDV (stDL c) (stL fun i => (t i : ℕ)) q κ m) q
      · rfl
      · exact absurd ((stDBal_iff c t h0 hm hq).1 h) hb
    obtain ⟨-, hdom⟩ := stDDom_first c t h0 hm hbf
    simp only [hb, false_or, Bool.and_eq_true, decide_eq_true_iff]
    unfold stDZ
    rw [stDSplit_iff c t h0 hm]
    unfold DomSplit
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, _, hdom, h2⟩
    · rintro ⟨h1, j, hj, h2⟩
      rw [dominant_unique hq hj hdom] at h2
      exact ⟨h1, h2⟩

/-- **The Case 3 test on lists**: at the first `m < κ` with a hit, outcome (a), or the class of
`t κ` has at least `3q/4` points. -/
def stDesB (dl tl : List ℕ) (q κ : ℕ) : Bool :=
  decide ((List.range κ).findIdx (stDHit dl tl q κ) < κ) &&
    (stDBal (stDV dl tl q κ ((List.range κ).findIdx (stDHit dl tl q κ))) q ||
      stDDomV (stDV dl tl q κ ((List.range κ).findIdx (stDHit dl tl q κ))) q
        (stDCol dl tl q κ ((List.range κ).findIdx (stDHit dl tl q κ)) (tl.getD κ 0)
          (tl.getD κ 0)))

theorem st_skel₂_self {q κ m : ℕ} (c : (Fin κ → Fin q) → ℕ) (x : Fin m → Fin q) (z : Fin q) :
    skel₂ c x z z = skel₁ c x z := by
  rw [skel₂, skel₁, padTuple₂_self]

/-- The first index of a range with a test is `Nat.find`. -/
theorem st_findIdx_range_eq {n : ℕ} {p : ℕ → Bool} {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ m, P m → m < n) (hp : ∀ m, m < n → (p m = true ↔ P m)) (hex : ∃ m, P m) :
    (List.range n).findIdx p = Nat.find hex := by
  have hlt : Nat.find hex < n := hP _ (Nat.find_spec hex)
  rw [List.findIdx_eq (by simpa using hlt)]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [List.getElem_range, hp _ hlt]; exact Nat.find_spec hex
  · rw [List.getElem_range]
    cases h : p j
    · rfl
    · exact absurd ((hp j (by omega)).1 h) (Nat.find_min hex hj)

/-- **The list test is the Case 3 test.** -/
theorem stDesB_iff {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) (hkl : κ < ℓ)
    (hq : 0 < q) :
    stDesB (stDL c) (stL fun i => (t i : ℕ)) q κ = true ↔ StDes c t hkl := by
  classical
  have h0 : 0 < ℓ := by omega
  set dl := stDL c
  set tl := stL fun i => (t i : ℕ)
  have hhit := stDHit_iff c t h0 hkl.le hq
  have htk : tl.getD κ 0 = t ⟨κ, hkl⟩ := by
    have hlt : κ < tl.length := by simp [tl, stL]; omega
    rw [List.getD_eq_getElem _ _ hlt]
    simp [tl, stL]
  -- the first hit
  have hfind : ∀ hex : ∃ m, Hit c t h0 m,
      (List.range κ).findIdx (stDHit dl tl q κ) = Nat.find hex := fun hex =>
    st_findIdx_range_eq (fun m h => h.1) (fun m _ => hhit m) hex
  unfold stDesB StDes
  rw [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hlt, hrest⟩
    have hex : ∃ m, Hit c t h0 m := by
      refine ⟨(List.range κ).findIdx (stDHit dl tl q κ), (hhit _).1 ?_⟩
      have := List.findIdx_getElem (w := (by simpa using hlt :
        (List.range κ).findIdx (stDHit dl tl q κ) < (List.range κ).length))
      rwa [List.getElem_range] at this
    refine ⟨hex, fun hnb j hj => ?_⟩
    rw [hfind hex] at hrest
    have hm : Nat.find hex ≤ ℓ := by have := (Nat.find_spec hex).1; omega
    rw [Bool.or_eq_true, stDBal_iff c t h0 hm hq, htk] at hrest
    rcases hrest with hb | hd
    · exact absurd hb hnb
    · rw [stDCol_eq c t h0 hm, st_skel₂_self, stDDomV_iff c t h0 hm] at hd
      exact (dominant_unique hq hj hd).symm
  · rintro ⟨hex, himp⟩
    rw [hfind hex]
    have hm : Nat.find hex ≤ ℓ := by have := (Nat.find_spec hex).1; omega
    refine ⟨(Nat.find_spec hex).1, ?_⟩
    rw [Bool.or_eq_true, stDBal_iff c t h0 hm hq, htk, stDCol_eq c t h0 hm, st_skel₂_self,
      stDDomV_iff c t h0 hm]
    by_cases hb : Balanced c (preT t h0 (Nat.find hex))
    · exact Or.inl hb
    · right
      have hs := (Nat.find_spec hex).2.resolve_left hb
      obtain ⟨-, j, hj, -⟩ := hs
      rw [himp hb j hj]
      exact hj

/-! ### The search -/

/-- The entries of the tuple of index `j` (in the order of `finFunctionFinEquiv`). -/
def stDDec (q ℓ j : ℕ) : List ℕ := (List.range ℓ).map fun i => j / q ^ i % q

theorem stDDec_eq {q ℓ : ℕ} (j : Fin (q ^ ℓ)) :
    stDDec q ℓ j = stL fun i => ((finFunctionFinEquiv.symm j i : Fin q) : ℕ) := by
  unfold stDDec stL
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem stDDec_top {q ℓ : ℕ} (hq : 0 < q) :
    stDDec q ℓ (q ^ ℓ) = stL fun _ : Fin ℓ => ((⟨0, hq⟩ : Fin q) : ℕ) := by
  unfold stDDec stL
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [Nat.pow_div i.isLt.le hq]
  obtain ⟨r, hr⟩ : ∃ r, ℓ - i = r + 1 := ⟨ℓ - i - 1, by have := i.isLt; omega⟩
  rw [hr, pow_succ, Nat.mul_mod_left]

/-- The index of the first tuple of length `ℓ` that passes the list test. -/
def stDSrcIdx (dl : List ℕ) (q κ ℓ : ℕ) : ℕ :=
  (List.range (q ^ ℓ)).findIdx fun j => stDesB dl (stDDec q ℓ j) q κ

/-- **The search finds `stSrc3`**: decoding the first index that passes the list test gives the
entries of the source tuple `stSrc3`. -/
theorem stDSrcIdx_eq {q κ ℓ : ℕ} (c : (Fin κ → Fin q) → ℕ) (hkl : κ < ℓ) (hq : 0 < q) :
    stDDec q ℓ (stDSrcIdx (stDL c) q κ ℓ) = stL fun i => (stSrc3 c hkl hq i : ℕ) := by
  classical
  have hidx : stDSrcIdx (stDL c) q κ ℓ =
      (stTs q ℓ).findIdx fun t => decide (StDes c t hkl) := by
    unfold stDSrcIdx stTs
    rw [← List.map_coe_finRange_eq_range, List.findIdx_map, List.findIdx_map]
    congr 1
    funext j
    simp only [Function.comp_apply]
    rw [stDDec_eq j]
    by_cases h : StDes c (finFunctionFinEquiv.symm j) hkl
    · rw [decide_eq_true h, (stDesB_iff c _ hkl hq).2 h]
    · rw [decide_eq_false h]
      cases hb : stDesB (stDL c) (stL fun i => ((finFunctionFinEquiv.symm j i : Fin q) : ℕ)) q κ
      · rfl
      · exact absurd ((stDesB_iff c _ hkl hq).1 hb) h
  unfold stSrc3
  rw [← hidx]
  by_cases hlt : stDSrcIdx (stDL c) q κ ℓ < q ^ ℓ
  · unfold stTs
    rw [List.getD_eq_getElem _ _ (by simp [hlt])]
    have := stDDec_eq (q := q) (ℓ := ℓ) ⟨_, hlt⟩
    simp only at this
    rw [this]
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
  · have hle : stDSrcIdx (stDL c) q κ ℓ ≤ q ^ ℓ := by
      unfold stDSrcIdx
      exact (List.findIdx_le_length).trans (by simp)
    have he : stDSrcIdx (stDL c) q κ ℓ = q ^ ℓ := by omega
    rw [List.getD_eq_default _ _ (by rw [stTs_length]; omega), he, stDDec_top hq]

end GI.Impl
