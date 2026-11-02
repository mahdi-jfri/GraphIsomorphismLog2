import Workspace.Impl.AggSubMath
import Workspace.Impl.AggStructRel

/-!
# The order of the test tuples that the program builds

The comparison phase runs over all pairs of ordered test tuples `(b, t)`: a string `b` and an
injective `κ`-tuple `t` of the `q` labels. The round fixes their order (`TestTupleOrder`), and the
items read the list in this order (`itSt`). The program of `AggCmpTupProg.lean` builds it by the
digit method of `sbOrder`: it runs over the numbers `j < 2 q ^ κ`, reads the quotient `j / q ^ κ`
(the string, `0` or `1`) and the `κ` base-`q` digits of `j` (`stDDec q κ j`, the digits of
`j mod q ^ κ`), and keeps `j` when the digits are pairwise distinct. The test is written in the
form the program computes: the list of the labels that occur among the digits (`sbSrt`) has `κ`
entries.

* `cmTupOk`, `cmTupOf`, `cmTups`: the test, the tuple of a kept number, the list.
* `cmTupOrder q κ hq`: the list is a `TestTupleOrder` (`cm_mem_tups`, `cm_tups_nodup`).
* `cm_tups_vals`: the value `stTT` of the tuple of a kept number `j` is the pair
  `[j / q ^ κ, digits of j]` that the digit program returns.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)

variable {q κ : ℕ}

/-! ### Distinct digits -/

/-- The labels of `d`, in increasing order, have as many entries as `d` exactly when the entries
of `d` are distinct (for entries below `q`). -/
theorem cm_srt_length_iff {d : List ℕ} (hd : ∀ x ∈ d, x < q) :
    (sbSrt q d).length = d.length ↔ d.Nodup := by
  have hn : (sbSrt q d).Nodup := (sb_srt_lt d).imp (fun h => ne_of_lt h)
  have hp : (sbSrt q d).Perm d.dedup := by
    refine (List.perm_ext_iff_of_nodup hn (List.nodup_dedup d)).2 fun c => ?_
    rw [sb_mem_srt, List.mem_dedup]
    exact ⟨fun h => h.2, fun h => ⟨hd c h, h⟩⟩
  rw [hp.length_eq]
  constructor
  · intro h
    have := (List.dedup_sublist d).eq_of_length h
    rw [← this]
    exact List.nodup_dedup d
  · intro h
    rw [List.Nodup.dedup h]

/-- The test of the number `j`: its `κ` digits are pairwise distinct. -/
def cmTupOk (q κ j : ℕ) : Bool := decide ((sbSrt q (stDDec q κ j)).length = κ)

theorem cm_ok_iff (hq : 0 < q) {j : ℕ} : cmTupOk q κ j = true ↔ (stDDec q κ j).Nodup := by
  rw [cmTupOk, decide_eq_true_iff, ← cm_srt_length_iff (stDDec_lt hq), stDDec_length]

/-- The tuple of the digits of `j`. -/
def cmTupFun (hq : 0 < q) (j : ℕ) : Fin κ → Fin q := fun i => ⟨j / q ^ (i : ℕ) % q, Nat.mod_lt _ hq⟩

theorem cm_dec_eq (hq : 0 < q) (j : ℕ) :
    stDDec q κ j = stL fun i : Fin κ => (cmTupFun hq j i : ℕ) := by
  unfold stDDec stL
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem cm_inj_of_ok (hq : 0 < q) {j : ℕ} (h : cmTupOk q κ j = true) :
    Function.Injective (cmTupFun (κ := κ) hq j) := by
  have hn := (cm_ok_iff hq).1 h
  rw [cm_dec_eq hq, stL] at hn
  intro a b hab
  have := (List.nodup_map_iff_inj_on (List.nodup_finRange κ)).1 hn a (List.mem_finRange a) b
    (List.mem_finRange b) (congrArg Fin.val hab)
  exact this

/-- The test tuple of a kept number: the string `j / q ^ κ` (`true` for `1`) and its digits. -/
def cmTupOf (hq : 0 < q) (j : ℕ) : Option (TestTuple q κ) :=
  if h : cmTupOk q κ j = true ∧ j < 2 * q ^ κ then
    some (decide (q ^ κ ≤ j), ⟨cmTupFun hq j, cm_inj_of_ok hq h.1⟩)
  else none

/-- **The test tuples, in the order of the program.** -/
def cmTups (hq : 0 < q) : List (TestTuple q κ) := (List.range (2 * q ^ κ)).filterMap (cmTupOf hq)

/-! ### Digits of `c q ^ κ + n` -/

/-- The digits below `κ` do not see the multiple of `q ^ κ`. -/
theorem cm_digit (hq : 0 < q) (c n : ℕ) {i : ℕ} (hi : i < κ) :
    (n + c * q ^ κ) / q ^ i % q = n / q ^ i % q := by
  have hpos : 0 < q ^ i := pow_pos hq _
  obtain ⟨r, hr⟩ : ∃ r, κ = i + (r + 1) := ⟨κ - i - 1, by omega⟩
  have e : n + c * q ^ κ = n + q ^ i * (q * (c * q ^ r)) := by
    rw [hr, pow_add, pow_succ]; ring
  rw [e, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

theorem cm_split (hq : 0 < q) {j : ℕ} (hj : j < 2 * q ^ κ) :
    j = j % q ^ κ + (decide (q ^ κ ≤ j)).toNat * q ^ κ := by
  have hpos : 0 < q ^ κ := pow_pos hq _
  by_cases h : q ^ κ ≤ j
  · simp only [h, decide_true, Bool.toNat_true, one_mul]
    have : j % q ^ κ = j - q ^ κ := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [h, decide_false, Bool.toNat_false, zero_mul, add_zero]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The digits of `j` are those of `j mod q ^ κ`. -/
theorem cm_fun_mod (hq : 0 < q) {j : ℕ} (hj : j < 2 * q ^ κ) :
    cmTupFun (κ := κ) hq j = cmTupFun hq (j % q ^ κ) := by
  funext i
  apply Fin.ext
  show j / q ^ (i : ℕ) % q = j % q ^ κ / q ^ (i : ℕ) % q
  conv_lhs => rw [cm_split hq hj]
  exact cm_digit hq _ _ i.isLt

/-- For `n < q ^ κ` the digits of `n` are `finFunctionFinEquiv.symm n`. -/
theorem cm_fun_equiv (hq : 0 < q) {n : ℕ} (hn : n < q ^ κ) :
    cmTupFun (κ := κ) hq n = finFunctionFinEquiv.symm ⟨n, hn⟩ := by
  funext i
  apply Fin.ext
  rw [finFunctionFinEquiv_symm_apply_val]
  rfl

/-! ### Every test tuple once -/

theorem cm_mem_tups (hq : 0 < q) (a : TestTuple q κ) : a ∈ cmTups hq := by
  obtain ⟨b, t⟩ := a
  have hpos : 0 < q ^ κ := pow_pos hq _
  set n := (finFunctionFinEquiv (⇑t) : ℕ) with hn
  have hnl : n < q ^ κ := (finFunctionFinEquiv (⇑t)).isLt
  set j := n + b.toNat * q ^ κ with hj
  have hjl : j < 2 * q ^ κ := by
    have := Bool.toNat_le b
    have : b.toNat * q ^ κ ≤ q ^ κ := by
      calc b.toNat * q ^ κ ≤ 1 * q ^ κ := Nat.mul_le_mul_right _ this
        _ = q ^ κ := one_mul _
    omega
  have hfun : cmTupFun (κ := κ) hq j = ⇑t := by
    funext i
    apply Fin.ext
    show (n + b.toNat * q ^ κ) / q ^ (i : ℕ) % q = _
    rw [cm_digit hq _ _ i.isLt]
    have := congrFun (cm_fun_equiv (κ := κ) hq hnl) i
    have h2 := congrArg Fin.val this
    simp only [cmTupFun] at h2
    rw [h2, show (⟨n, hnl⟩ : Fin (q ^ κ)) = finFunctionFinEquiv ⇑t from Fin.ext rfl,
      Equiv.symm_apply_apply]
  have hok : cmTupOk q κ j = true := by
    rw [cm_ok_iff hq, cm_dec_eq hq, stL, hfun]
    exact (List.nodup_finRange κ).map (fun a b h => t.injective (Fin.ext h))
  have hb : decide (q ^ κ ≤ j) = b := by
    cases b
    · simp [hj, Bool.toNat]; omega
    · simp [hj, Bool.toNat]
  refine List.mem_filterMap.2 ⟨j, List.mem_range.2 hjl, ?_⟩
  rw [cmTupOf, dif_pos ⟨hok, hjl⟩]
  congr 1
  refine Prod.ext hb ?_
  exact DFunLike.coe_injective hfun

theorem cm_tups_nodup (hq : 0 < q) : (cmTups (κ := κ) hq).Nodup := by
  have hpos : 0 < q ^ κ := pow_pos hq _
  refine (List.nodup_range).filterMap fun j j' a ha ha' => ?_
  unfold cmTupOf at ha ha'
  by_cases h : cmTupOk q κ j = true ∧ j < 2 * q ^ κ
  swap
  · rw [dif_neg h] at ha; simp at ha
  by_cases h' : cmTupOk q κ j' = true ∧ j' < 2 * q ^ κ
  swap
  · rw [dif_neg h'] at ha'; simp at ha'
  rw [dif_pos h] at ha
  rw [dif_pos h'] at ha'
  simp only [Option.mem_def, Option.some.injEq] at ha ha'
  rw [← ha'] at ha
  have hb := congrArg Prod.fst ha
  have hf : cmTupFun (κ := κ) hq j = cmTupFun hq j' :=
    congrArg (fun x : TestTuple q κ => (⇑x.2 : Fin κ → Fin q)) ha
  simp only at hb
  rw [cm_fun_mod hq h.2, cm_fun_mod hq h'.2, cm_fun_equiv hq (Nat.mod_lt _ hpos),
    cm_fun_equiv hq (Nat.mod_lt _ hpos)] at hf
  have hm := congrArg Fin.val (finFunctionFinEquiv.symm.injective hf)
  simp only at hm
  rw [cm_split hq h.2, cm_split hq h'.2, hm, hb]

/-- **The order of the test tuples that the program builds.** -/
def cmTupOrder (q κ : ℕ) (hq : 0 < q) : TestTupleOrder q κ :=
  ⟨cmTups hq, cm_tups_nodup hq, cm_mem_tups hq⟩

end GI.Impl
