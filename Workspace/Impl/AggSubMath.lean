module

public import Workspace.Impl.AggCertRep
public import Workspace.Impl.AggStructDesSrc

@[expose] public section

/-!
# The order of the test sets that the program builds

The certificate phase runs over all `κ`-subsets of the `q` labels, in an order that the round
fixes (`TestSetOrder`). The program of `AggSubProg.lean` builds this list as follows: it runs
over the numbers `j < q ^ κ`, reads the base-`q` digits of `j` (`stDDec q κ j`, the order of
`finFunctionFinEquiv`), and keeps `j` when its digits increase strictly. The kept digit lists are
the increasing lists of `κ` labels, each once, so their sets are the `κ`-subsets, each once.

The test "the digits increase strictly" is written in the form the program computes: the list of
the labels `c < q` that occur among the digits, in increasing order (`sbSrt`), equals the list of
digits (`sbOk`).

* `sbSets q κ`, `sbOrder q κ`: the sets and the order (`sb_mem_sets`, `sb_sets_nodup`).
* `sbEntV k q d`: the program value of the kept digit list `d`; `sb_entV_eq`: it is `tsV k` of
  its set, the value of a test set in the program states of the certificate phase.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)

variable {q κ : ℕ}

/-! ### Definitions -/

/-- The labels whose numbers occur in `d`. -/
def sbSet (q : ℕ) (d : List ℕ) : Finset (Fin q) := Finset.univ.filter fun c => (c : ℕ) ∈ d

/-- The numbers `c < q` that occur in `d`, in increasing order. -/
def sbSrt (q : ℕ) (d : List ℕ) : List ℕ := (List.range q).filter fun c => decide (d.count c ≠ 0)

/-- The test of the number `j`: its digits are the increasing list of the labels they name. -/
def sbOk (q κ j : ℕ) : Bool := decide (sbSrt q (stDDec q κ j) = stDDec q κ j)

/-- The kept numbers. -/
def sbIdx (q κ : ℕ) : List ℕ := (List.range (q ^ κ)).filter (sbOk q κ)

/-- The digit lists of the kept numbers. -/
def sbLists (q κ : ℕ) : List (List ℕ) := (sbIdx q κ).map (stDDec q κ)

/-- **The test sets, in the order of the program.** -/
def sbSets (q κ : ℕ) : List (Finset (Fin q)) := (sbLists q κ).map (sbSet q)

/-! ### Facts about `sbSrt` -/

theorem sb_mem_srt {d : List ℕ} {c : ℕ} : c ∈ sbSrt q d ↔ c < q ∧ c ∈ d := by
  simp [sbSrt, List.count_eq_zero]

theorem sb_srt_lt (d : List ℕ) : (sbSrt q d).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem sb_mem_set {d : List ℕ} {c : Fin q} : c ∈ sbSet q d ↔ (c : ℕ) ∈ d := by
  simp [sbSet]

theorem sb_tlist_lt (T : Finset (Fin q)) : ((tlist T).map Fin.val).Pairwise (· < ·) := by
  have h1 : (tlist T).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have h2 : (tlist T).Nodup := Finset.sort_nodup _ _
  have h3 : (tlist T).Pairwise (· < ·) :=
    (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2
  exact List.pairwise_map.2 (h3.imp fun h => h)

theorem sb_mem_tlist {T : Finset (Fin q)} {c : ℕ} :
    c ∈ (tlist T).map Fin.val ↔ ∃ h : c < q, (⟨c, h⟩ : Fin q) ∈ T := by
  simp only [List.mem_map, mem_tlist]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.isLt, hx⟩
  · rintro ⟨h, hc⟩
    exact ⟨_, hc, rfl⟩

/-- **A kept list is the increasing list of its set.** -/
theorem sb_tlist_set {d : List ℕ} (h : sbSrt q d = d) : (tlist (sbSet q d)).map Fin.val = d := by
  conv_rhs => rw [← h]
  refine (sb_tlist_lt _).eq_of_mem_iff (sb_srt_lt d) fun c => ?_
  rw [sb_mem_tlist, sb_mem_srt]
  constructor
  · rintro ⟨hc, hm⟩
    exact ⟨hc, sb_mem_set.1 hm⟩
  · rintro ⟨hc, hm⟩
    exact ⟨hc, sb_mem_set.2 hm⟩

/-- A kept digit list. -/
theorem sb_mem_lists {d : List ℕ} : d ∈ sbLists q κ ↔
    ∃ j < q ^ κ, sbSrt q (stDDec q κ j) = stDDec q κ j ∧ stDDec q κ j = d := by
  simp only [sbLists, sbIdx, sbOk, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  exact ⟨fun ⟨a, ⟨h1, h2⟩, h3⟩ => ⟨a, h1, h2, h3⟩, fun ⟨a, h1, h2, h3⟩ => ⟨a, ⟨h1, h2⟩, h3⟩⟩

theorem sb_card_set {d : List ℕ} (hd : d ∈ sbLists q κ) : (sbSet q d).card = κ := by
  obtain ⟨j, -, hok, rfl⟩ := sb_mem_lists.1 hd
  rw [← length_tlist, ← List.length_map (f := Fin.val), sb_tlist_set hok, stDDec_length]

/-! ### Every `κ`-subset once -/

/-- The digits of the number of a tuple are the entries of the tuple. -/
theorem sb_dec_equiv (t : Fin κ → Fin q) :
    stDDec q κ (finFunctionFinEquiv t) = (List.finRange κ).map fun i => (t i : ℕ) := by
  rw [stDDec_eq, Equiv.symm_apply_apply]
  rfl

theorem sb_mem_sets {T : Finset (Fin q)} : T ∈ sbSets q κ ↔ T.card = κ := by
  constructor
  · intro hT
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hT
    exact sb_card_set hd
  · intro hT
    set d := (tlist T).map Fin.val with hd
    have hlen : (tlist T).length = κ := by rw [length_tlist, hT]
    let t : Fin κ → Fin q := fun i => (tlist T)[i.1]'(by rw [hlen]; exact i.2)
    have hdt : (List.finRange κ).map (fun i => (t i : ℕ)) = d := by
      refine List.ext_getElem (by simp [hd, hlen]) fun i h1 h2 => ?_
      simp [hd, t]
    have hsrt : sbSrt q d = d := by
      refine (sb_srt_lt d).eq_of_mem_iff (sb_tlist_lt T) fun c => ?_
      rw [sb_mem_srt]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨(sb_mem_tlist.1 h).1, h⟩
    have hset : sbSet q d = T := by
      ext c
      rw [sb_mem_set, hd, sb_mem_tlist]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨c.isLt, h⟩⟩
    have hdl : d ∈ sbLists q κ := by
      refine sb_mem_lists.2 ⟨finFunctionFinEquiv t, (finFunctionFinEquiv t).isLt, ?_, ?_⟩
      · rw [sb_dec_equiv, hdt, hsrt]
      · rw [sb_dec_equiv, hdt]
    exact List.mem_map.2 ⟨d, hdl, hset⟩

theorem sb_dec_inj {j j' : ℕ} (hj : j < q ^ κ) (hj' : j' < q ^ κ)
    (h : stDDec q κ j = stDDec q κ j') : j = j' := by
  have e1 := stDDec_eq (q := q) (ℓ := κ) ⟨j, hj⟩
  have e2 := stDDec_eq (q := q) (ℓ := κ) ⟨j', hj'⟩
  simp only at e1 e2
  rw [e1, e2] at h
  have hf : finFunctionFinEquiv.symm (⟨j, hj⟩ : Fin (q ^ κ)) =
      finFunctionFinEquiv.symm (⟨j', hj'⟩ : Fin (q ^ κ)) := by
    funext i
    have := congrArg (fun l : List ℕ => l[i.1]?) h
    simp [stL] at this
    exact Fin.ext this
  exact congrArg Fin.val (finFunctionFinEquiv.symm.injective hf)

theorem sb_sets_nodup : (sbSets q κ).Nodup := by
  have hidx : (sbIdx q κ).Nodup := (List.nodup_range).filter _
  have hl : (sbLists q κ).Nodup := by
    refine hidx.map_on fun j hj j' hj' h => ?_
    simp only [sbIdx, List.mem_filter, List.mem_range] at hj hj'
    exact sb_dec_inj hj.1 hj'.1 h
  refine hl.map_on fun d hd d' hd' h => ?_
  obtain ⟨j, -, hok, rfl⟩ := sb_mem_lists.1 hd
  obtain ⟨j', -, hok', rfl⟩ := sb_mem_lists.1 hd'
  rw [← sb_tlist_set hok, ← sb_tlist_set hok', h]

/-- **The order of the test sets that the program builds.** -/
def sbOrder (q κ : ℕ) : TestSetOrder q κ :=
  ⟨sbSets q κ, sb_sets_nodup, fun _ => sb_mem_sets⟩

/-! ### The program value of a test set -/

/-- The indicator of the labels that occur in `d`. -/
def sbInd (q : ℕ) (d : List ℕ) : List ℕ :=
  (List.range q).map fun c => (decide (d.count c ≠ 0)).toNat

/-- **The value of a kept list `d`**: the indicator of its labels and the points `k + c`. -/
def sbEntV (k q : ℕ) (d : List ℕ) : Val := .list [natList (sbInd q d), natList (d.map (k + ·))]

/-- **The value of a kept list is the value of its test set.** -/
theorem sb_entV_eq (k : ℕ) {d : List ℕ} (hd : d ∈ sbLists q κ) :
    sbEntV k q d = tsV k (sbSet q d) := by
  obtain ⟨j, -, hok, rfl⟩ := sb_mem_lists.1 hd
  unfold sbEntV tsV
  congr 2
  · rw [indT, encFun_eq_natList, sbInd, ← List.map_coe_finRange_eq_range, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, sb_mem_set]
    by_cases h : (i : ℕ) ∈ stDDec q κ j
    · have : (stDDec q κ j).count (i : ℕ) ≠ 0 := (List.count_pos_iff.2 h).ne'
      simp [h, this]
    · have : (stDDec q κ j).count (i : ℕ) = 0 := List.count_eq_zero.2 h
      simp [h, this]
  · conv_lhs => rw [← sb_tlist_set hok]
    simp [ptsKey, labPts, List.map_map, Function.comp_def]

/-- The values of the test sets of `sbOrder`, as the program lists them. -/
theorem sb_order_vals (k q κ : ℕ) :
    (sbLists q κ).map (sbEntV k q) = (sbOrder q κ).sets.map (tsV k) := by
  show _ = (sbSets q κ).map (tsV k)
  rw [sbSets, List.map_map]
  exact List.map_congr_left fun d hd => sb_entV_eq k hd

end GI.Impl
