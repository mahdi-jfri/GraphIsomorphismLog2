module

public import Workspace.Impl.RowClean

@[expose] public section

/-!
# Localized lifts of window cycles, and the A.17 coordinates

The proof of Theorem A.17 lifts `k`-cycles on `k`-sets `T` of rows to elements of `G` that fix
every point outside the rows of `T` (the localization (LG2)). This file fixes the sets `T` that
the program uses, and proves what the program needs about them.

**Windows.** A window is the list `[0, x₁, b + s mod M, b + (s + 1) mod M, …]` of `k` rows
(`winF`, `winL`). Its cycle is `List.formPerm`: it sends each entry to the next one. The program
uses three kinds (with `5 ≤ k`, `k` odd, `2k ≤ q + 1`):

* `win1 = [0, 2, 3, …, k]`, whose cycle sends `0 ↦ 2`;
* `win2 = [0, 1, k + 1, …, 2k - 2]`, whose cycle sends `0 ↦ 1`; it meets `win1` only in `0`;
* `winJ j = [0, j, j + 1, …]` inside the rows `3, …, q - 1` (cyclically), for `j ≥ 3`; its
  cycle sends `0 ↦ j`, and it meets `{0, 1, 2}` only in `0`.

Each cycle is even, since `k` is odd (`winL_even`).

**Lifts** (`WinLift`). A lift of a window `t` is an element of `G` with top `formPerm t` that
fixes every point of the domain whose row is not in `t`. Its restriction to the domain is a
localized lift of `formPerm t` (`WinLift.localized`). Lifts exist under the logarithmic
threshold (`winLift_exists`); this is (LG2), through `localLiftAvailable_log`.

**Coordinates** (`pureCoords_of_lifts`). Given lifts `g₁, h₁` of `win1, win2` and `hⱼ` of
`winJ j`, put `c = [g₁, h₁]` and `dⱼ = [c, hⱼ]` (`rightLocalCommutator`). On the domain, `c`
is a clean cycle with top `(0 1 2)`, and `dⱼ` a clean cycle with top `(0 j 1)` that undoes `c`
on row `0` (`cleanBlockCycle_of_localized`, `comm_undo`). So the coordinates of
`Workspace/Impl/RowClean.lean` are pure, for every numbering of row `0`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Paper GI.Algorithm

/-! ### Windows -/

/-- Entry `i` of a window: `0`, then `x₁`, then `b + (s + i - 2) mod M`. -/
def winF (x1 base s M i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then x1 else base + (s + i - 2) % M

/-- A window of `k` rows, as a list of rows. -/
def winL (q k x1 base s M : ℕ) (h : ∀ i < k, winF x1 base s M i < q) : List (Fin q) :=
  List.ofFn fun i : Fin k => ⟨winF x1 base s M i, h i i.2⟩

section Win

variable {q k x1 base s M : ℕ} {h : ∀ i < k, winF x1 base s M i < q}

theorem length_winL : (winL q k x1 base s M h).length = k := by simp [winL]

theorem mem_winL {x : Fin q} : x ∈ winL q k x1 base s M h ↔ ∃ i < k, winF x1 base s M i = x := by
  simp only [winL, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, i.2, by rw [← hi]⟩
  · rintro ⟨i, hi, he⟩; exact ⟨⟨i, hi⟩, Fin.ext he⟩

theorem getElem_winL (i : ℕ) (hi : i < (winL q k x1 base s M h).length) :
    ((winL q k x1 base s M h)[i] : ℕ) = winF x1 base s M i := by
  simp [winL]

/-- Two offsets below `M` with the same residue after adding `s` are equal. -/
theorem mod_add_inj {s a a' M : ℕ} (ha : a < M) (ha' : a' < M)
    (h : (s + a) % M = (s + a') % M) : a = a' := by
  have h1 : a ≡ a' [MOD M] := Nat.ModEq.add_left_cancel' s h
  unfold Nat.ModEq at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h1

/-- **A window has no repeats** when `x₁` and `b` are positive, the offsets fit below `M`, and
`x₁` is not one of the later entries. -/
theorem winL_nodup (hx1 : 1 ≤ x1) (hb : 1 ≤ base) (hkM : k ≤ M + 2)
    (hx : ∀ m, m + 2 < k → x1 ≠ base + (s + m) % M) : (winL q k x1 base s M h).Nodup := by
  rw [winL, List.nodup_ofFn]
  intro i j hij
  simp only [Fin.mk.injEq] at hij
  apply Fin.ext
  have hi := i.2
  have hj := j.2
  unfold winF at hij
  split_ifs at hij with h1 h2 h3 h4 h5 h6 h7 h8 <;> try omega
  · rw [show s + (j : ℕ) - 2 = s + ((j : ℕ) - 2) by omega] at hij
    exact absurd hij (hx _ (by omega))
  · rw [show s + (i : ℕ) - 2 = s + ((i : ℕ) - 2) by omega] at hij
    exact absurd hij.symm (hx _ (by omega))
  · have := mod_add_inj (s := s) (a := (i : ℕ) - 2) (a' := (j : ℕ) - 2) (M := M) (by omega)
      (by omega)
      (by rw [show s + ((i : ℕ) - 2) = s + i - 2 by omega,
        show s + ((j : ℕ) - 2) = s + j - 2 by omega]; omega)
    omega

theorem winL_get_zero (hk : 2 ≤ k) :
    (winL q k x1 base s M h)[0]'(by rw [length_winL]; omega) =
      ⟨0, by have := h 0 (by omega); simpa [winF] using this⟩ := by
  apply Fin.ext; rw [getElem_winL]; simp [winF]

theorem winL_get_one (hk : 2 ≤ k) :
    (winL q k x1 base s M h)[1]'(by rw [length_winL]; omega) =
      ⟨x1, by have := h 1 (by omega); simpa [winF] using this⟩ := by
  apply Fin.ext; rw [getElem_winL]; simp [winF]

/-- **The window cycle sends `0` to `x₁`.** -/
theorem formPerm_winL_zero (hk : 2 ≤ k) (hnd : (winL q k x1 base s M h).Nodup) :
    (winL q k x1 base s M h).formPerm ⟨0, by have := h 0 (by omega); simpa [winF] using this⟩ =
      ⟨x1, by have := h 1 (by omega); simpa [winF] using this⟩ := by
  have e0 := winL_get_zero (h := h) hk
  have e1 := winL_get_one (h := h) hk
  rw [← e0, List.formPerm_apply_getElem_zero _ hnd (by rw [length_winL]; omega), e1]

/-- **The window cycle moves exactly the rows of the window.** -/
theorem formPerm_ne_iff (t : List (Fin q)) (hnd : t.Nodup) (h2 : 2 ≤ t.length) (x : Fin q) :
    t.formPerm x ≠ x ↔ x ∈ t := by
  constructor
  · exact List.mem_of_formPerm_apply_ne
  · intro hx; exact (List.formPerm_apply_mem_ne_self_iff _ hnd x hx).2 h2

/-- **The cycle of a window of odd length is even.** -/
theorem formPerm_even (t : List (Fin q)) (hnd : t.Nodup) (h3 : 3 ≤ t.length)
    (hodd : Odd t.length) : t.formPerm ∈ alternatingGroup (Fin q) := by
  rw [mem_alternatingGroup, (List.isCycle_formPerm hnd (by omega)).sign,
    List.support_formPerm_of_nodup _ hnd (by rintro x rfl; simp at h3),
    List.toFinset_card_of_nodup hnd, hodd.neg_one_pow]
  simp

end Win

/-! ### The three kinds of windows -/

/-- The window length: `5 ≤ k`, `k` odd, `2k ≤ q + 1`. -/
structure WinLen (q k : ℕ) : Prop where
  five : 5 ≤ k
  odd : Odd k
  le : 2 * k ≤ q + 1

namespace WinLen

variable {q k : ℕ} (hk : WinLen q k)
include hk

theorem nine_le : 9 ≤ q := by have := hk.five; have := hk.le; omega

theorem bound1 : ∀ i < k, winF 2 3 0 q i < q := by
  intro i hi; have := hk.five; have := hk.le
  unfold winF; split_ifs <;> try omega
  have := Nat.mod_le (0 + i - 2) q; omega

theorem bound2 : ∀ i < k, winF 1 (k + 1) 0 q i < q := by
  intro i hi; have := hk.five; have := hk.le
  unfold winF; split_ifs <;> try omega
  have := Nat.mod_le (0 + i - 2) q; omega

end WinLen

section Kinds

variable {q k : ℕ}

/-- `win1 = [0, 2, 3, …, k]`. -/
def win1 (hk : WinLen q k) : List (Fin q) := winL q k 2 3 0 q hk.bound1

/-- `win2 = [0, 1, k + 1, …, 2k - 2]`. -/
def win2 (hk : WinLen q k) : List (Fin q) := winL q k 1 (k + 1) 0 q hk.bound2

theorem boundJ (hk : WinLen q k) (j : Fin q) : ∀ i < k, winF j 3 (j - 2) (q - 3) i < q := by
  intro i hi; have := hk.nine_le; have := j.2
  unfold winF; split_ifs <;> try omega
  have := Nat.mod_lt (j - 2 + i - 2) (show 0 < q - 3 by omega); omega

/-- `winJ j = [0, j, …]`, inside the rows `3, …, q - 1`. -/
def winJ (hk : WinLen q k) (j : Fin q) : List (Fin q) :=
  winL q k j 3 (j - 2) (q - 3) (boundJ hk j)

/-- Entries of `win1` and `win2` past the second: `b + (i - 2)`. -/
theorem winF_zero_s {x1 base i : ℕ} (hi2 : 2 ≤ i) (hiq : i - 2 < q) :
    winF x1 base 0 q i = base + (i - 2) := by
  unfold winF
  rw [if_neg (by omega), if_neg (by omega), show 0 + i - 2 = i - 2 by omega, Nat.mod_eq_of_lt hiq]

theorem win1_nodup (hk : WinLen q k) : (win1 hk).Nodup :=
  winL_nodup (by norm_num) (by norm_num) (by have := hk.le; omega) (fun m _ => by omega)

theorem win2_nodup (hk : WinLen q k) : (win2 hk).Nodup :=
  winL_nodup (by norm_num) (by omega) (by have := hk.le; omega) (fun m _ => by omega)

theorem winJ_nodup (hk : WinLen q k) (j : Fin q) (hj : 3 ≤ (j : ℕ)) : (winJ hk j).Nodup := by
  have h9 := hk.nine_le
  have hkq := hk.le
  have hjq := j.2
  refine winL_nodup (by omega) (by norm_num) (by omega) fun m hm he => ?_
  -- `j - 3 + (m + 1)` is not `j - 3` modulo `q - 3`
  rw [show (j : ℕ) - 2 + m = ((j : ℕ) - 3 + (m + 1)) by omega] at he
  rcases Nat.lt_or_ge ((j : ℕ) - 3 + (m + 1)) (q - 3) with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at he; omega
  · rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega)] at he; omega

theorem length_win1 (hk : WinLen q k) : (win1 hk).length = k := length_winL
theorem length_win2 (hk : WinLen q k) : (win2 hk).length = k := length_winL
theorem length_winJ (hk : WinLen q k) (j : Fin q) : (winJ hk j).length = k := length_winL

theorem mem_win1 (hk : WinLen q k) {x : Fin q} :
    x ∈ win1 hk ↔ (x : ℕ) = 0 ∨ (x : ℕ) = 2 ∨ (3 ≤ (x : ℕ) ∧ (x : ℕ) ≤ k) := by
  have := hk.le
  rw [win1, mem_winL]
  constructor
  · rintro ⟨i, hi, he⟩
    rcases Nat.lt_or_ge i 2 with h | h
    · unfold winF at he; split_ifs at he <;> omega
    · rw [winF_zero_s h (by omega)] at he; omega
  · rintro (h | h | ⟨h1, h2⟩)
    · exact ⟨0, by have := hk.five; omega, by simp [winF, h]⟩
    · exact ⟨1, by have := hk.five; omega, by simp [winF, h]⟩
    · exact ⟨(x : ℕ) - 1, by omega, by rw [winF_zero_s (by omega) (by omega)]; omega⟩

theorem mem_win2 (hk : WinLen q k) {x : Fin q} :
    x ∈ win2 hk ↔ (x : ℕ) = 0 ∨ (x : ℕ) = 1 ∨ (k + 1 ≤ (x : ℕ) ∧ (x : ℕ) ≤ 2 * k - 2) := by
  have := hk.le
  rw [win2, mem_winL]
  constructor
  · rintro ⟨i, hi, he⟩
    rcases Nat.lt_or_ge i 2 with h | h
    · unfold winF at he; split_ifs at he <;> omega
    · rw [winF_zero_s h (by omega)] at he; omega
  · rintro (h | h | ⟨h1, h2⟩)
    · exact ⟨0, by have := hk.five; omega, by simp [winF, h]⟩
    · exact ⟨1, by have := hk.five; omega, by simp [winF, h]⟩
    · exact ⟨(x : ℕ) - k + 1, by omega, by rw [winF_zero_s (by omega) (by omega)]; omega⟩

theorem mem_winJ (hk : WinLen q k) (j : Fin q) (hj : 3 ≤ (j : ℕ)) {x : Fin q} (hx : x ∈ winJ hk j) :
    (x : ℕ) = 0 ∨ 3 ≤ (x : ℕ) := by
  rw [winJ, mem_winL] at hx
  obtain ⟨i, -, he⟩ := hx
  unfold winF at he; split_ifs at he <;> omega

/-- The zero row. -/
def row0 (hk : WinLen q k) : Fin q := ⟨0, by have := hk.nine_le; omega⟩

theorem formPerm_win1_zero (hk : WinLen q k) :
    (win1 hk).formPerm (row0 hk) = ⟨2, by have := hk.nine_le; omega⟩ :=
  formPerm_winL_zero (by have := hk.five; omega) (win1_nodup hk)

theorem formPerm_win2_zero (hk : WinLen q k) :
    (win2 hk).formPerm (row0 hk) = ⟨1, by have := hk.nine_le; omega⟩ :=
  formPerm_winL_zero (by have := hk.five; omega) (win2_nodup hk)

theorem formPerm_winJ_zero (hk : WinLen q k) (j : Fin q) (hj : 3 ≤ (j : ℕ)) :
    (winJ hk j).formPerm (row0 hk) = j :=
  (formPerm_winL_zero (by have := hk.five; omega) (winJ_nodup hk j hj)).trans (Fin.ext rfl)

/-- `win1` and `win2` meet only in `0`. -/
theorem meet12 (hk : WinLen q k) (i : Fin q) :
    ((win1 hk).formPerm i ≠ i ∧ (win2 hk).formPerm i ≠ i) ↔ i = row0 hk := by
  have h5 := hk.five
  rw [formPerm_ne_iff _ (win1_nodup hk) (by rw [length_win1]; omega),
    formPerm_ne_iff _ (win2_nodup hk) (by rw [length_win2]; omega), mem_win1, mem_win2]
  constructor
  · rintro ⟨h1, h2⟩; apply Fin.ext; simp only [row0]; omega
  · rintro rfl; simp [row0]

/-- `winJ j` meets `{0, 1, 2}` only in `0`. -/
theorem meetJ (hk : WinLen q k) (j : Fin q) (hj : 3 ≤ (j : ℕ)) (i : Fin q) :
    (cleanCycle (row0 hk) ⟨1, by have := hk.nine_le; omega⟩ ⟨2, by have := hk.nine_le; omega⟩ i ≠ i ∧
      (winJ hk j).formPerm i ≠ i) ↔ i = row0 hk := by
  have h5 := hk.five
  rw [formPerm_ne_iff _ (winJ_nodup hk j hj) (by rw [length_winJ]; omega), ne_eq,
    cleanCycle_apply_eq_self (by simp [row0]) (by simp [row0]) (by simp)]
  constructor
  · rintro ⟨h1, h2⟩
    rcases mem_winJ hk j hj h2 with h | h
    · exact Fin.ext h
    · exfalso; apply h1
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> (rw [e] at h; simp [row0] at h)
  · rintro rfl
    refine ⟨fun h => h.1 rfl, ?_⟩
    rw [winJ, mem_winL]
    exact ⟨0, by omega, by simp [winF, row0]⟩

end Kinds

/-! ### The window length of the program -/

/-- The largest odd `k` with `2k - 1 ≤ q`. -/
def kkOf (q : ℕ) : ℕ := (q + 1) / 2 - 1 + (q + 1) / 2 % 2

theorem kkOf_odd (q : ℕ) (hq : 1 ≤ q) : Odd (kkOf q) := by
  unfold kkOf
  rcases Nat.mod_two_eq_zero_or_one ((q + 1) / 2) with h | h
  · rw [h]; exact Nat.odd_iff.2 (by omega)
  · rw [h]; exact Nat.odd_iff.2 (by omega)

theorem kkOf_ge (q : ℕ) : q ≤ 2 * kkOf q + 2 := by
  unfold kkOf
  have := Nat.mod_two_eq_zero_or_one ((q + 1) / 2); omega

theorem kkOf_le (q : ℕ) (hq : 1 ≤ q) : 2 * kkOf q ≤ q + 1 := by
  unfold kkOf
  have := Nat.mod_two_eq_zero_or_one ((q + 1) / 2); omega

/-- **The window length meets (LG1)** when `q` passes the logarithmic threshold of Algorithm 4
for a row size `f ≤ s`. -/
theorem kkOf_thr {q f s : ℕ} (hf : f ≤ s) (hfpos : 0 < f)
    (hthr : 2 * max 63 (12 * Real.logb 2 s) + 3 ≤ (q : ℝ)) :
    WinLen q (kkOf q) ∧ max 63 (12 * Real.logb 2 f) < (kkOf q : ℝ) := by
  have h63 : (63 : ℝ) ≤ max 63 (12 * Real.logb 2 s) := le_max_left _ _
  have hq19 : 19 ≤ q := by
    have : (19 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hge := kkOf_ge q
  have hle := kkOf_le q (by omega)
  refine ⟨⟨by omega, kkOf_odd q (by omega), hle⟩, ?_⟩
  have hlog : Real.logb 2 f ≤ Real.logb 2 s :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hfpos) (by exact_mod_cast hf)
  have hmax : max 63 (12 * Real.logb 2 f) ≤ max 63 (12 * Real.logb 2 s) :=
    max_le_max le_rfl (by linarith)
  have hk : (q : ℝ) ≤ 2 * (kkOf q : ℝ) + 2 := by exact_mod_cast hge
  linarith

/-! ### Lifts -/

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- **A lift of a window**: an element of `G` with top `formPerm t` that fixes every point of
the domain outside the rows of `t`. -/
structure WinLift (S : State Ω C) (L : GiantLabels S) (label : Ω → Fin L.q) (t : List (Fin L.q))
    (g : Perm Ω) : Prop where
  mem : g ∈ S.G
  top : ((L.π ⟨g, mem⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = t.formPerm
  fix : ∀ v ∈ S.dom, label v ∉ t → g v = v

/-- The row labels on the domain. -/
def domLab (label : Ω → Fin L.q) (v : S.dom) : Fin L.q := label v

/-- **The restriction of a lift is a localized lift** (for a window without repeats). -/
theorem WinLift.localized (hnat : NaturalRows S L label) {t : List (Fin L.q)} {g : Perm Ω}
    (hg : WinLift S L label t g) (hnd : t.Nodup) (h2 : 2 ≤ t.length) :
    LocalizedBlockLift (domLab (S := S) label) t.formPerm (S.domHom ⟨g, hg.mem⟩) where
  action x := by
    show label (g x) = _
    rw [hnat.equivariant ⟨g, hg.mem⟩ x x.2, hg.top]
    rfl
  fixes x hx := by
    apply Subtype.ext
    show g x = x
    refine hg.fix x x.2 fun hm => ?_
    exact (formPerm_ne_iff t hnd h2 _).2 hm hx

/-- The fibers of natural row labels all have the size of row `0`. -/
theorem card_fiber_eq [Fintype S.dom] (hnat : NaturalRows S L label) (hq : 3 ≤ L.q)
    (i : Fin L.q) :
    Fintype.card {x : S.dom // label x = i} =
      Fintype.card {x : S.dom // label x = ⟨0, by omega⟩} := by
  classical
  haveI := alternatingGroup.isPretransitive_of_three_le_card (Fin L.q)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin L.q)) ⟨0, by omega⟩ i
  have ha' : a.val ⟨0, by omega⟩ = i := ha
  obtain ⟨g, hg⟩ := topHom_surjective hnat a
  symm
  refine Fintype.card_congr (Equiv.subtypeEquiv g.val fun x => ?_)
  have hx : label (g.val x) = a.val (label x) := by
    rw [← hg]; exact topHom_equivariant hnat g x
  rw [hx, ← ha']
  exact ⟨fun h => h ▸ rfl, fun h => a.val.injective h⟩

/-- **Lifts exist** (LG2): for a window `t` without repeats, of odd length `k ≥ 5` above the
logarithmic threshold of the row size, some element of `G` lifts `formPerm t` and fixes every
point of the domain outside the rows of `t` (`localLiftAvailable_log`). -/
theorem winLift_exists [Finite Ω]
    (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) (t : List (Fin L.q)) (hnd : t.Nodup)
    (h5 : 5 ≤ t.length) (hodd : Odd t.length) (f : ℕ)
    (hf : ∀ [Fintype S.dom], Fintype.card {x : S.dom // label x = ⟨0, by omega⟩} = f)
    (hthr : max 63 (12 * Real.logb 2 f) < (t.length : ℝ)) :
    ∃ g, WinLift S L label t g := by
  classical
  haveI : Fintype S.dom := Fintype.ofFinite _
  let A := rowAction hnat
  have hker : A.KernelTransitive := by
    intro x y hxy
    obtain ⟨k', hk1, hkx⟩ := (hnat.fibers x x.2 y y.2).1 hxy
    refine ⟨S.domHom.rangeRestrict k', ?_, Subtype.ext hkx⟩
    show topHom hnat _ = 1
    rw [topHom_apply, hk1]
  have hthrA : A.BelowLogThreshold t.length := by
    intro i
    change max 63 (12 * Real.logb 2 (Fintype.card {x : S.dom // label x = i})) < _
    rw [card_fiber_eq hnat (by omega) i, hf]
    exact hthr
  have hT : t.toFinset.card = t.length := List.toFinset_card_of_nodup hnd
  have hLA := localLiftAvailable_log A hker hthrA t.toFinset hT h5
  obtain ⟨g', hg'top, hg'fix⟩ := hLA ⟨t.formPerm, formPerm_even t hnd (by omega) hodd⟩
    (fun i hi => List.formPerm_apply_of_notMem (by simpa using hi))
  obtain ⟨g0, hg0⟩ := S.domHom.rangeRestrict_surjective g'
  refine ⟨g0.val, ⟨g0.2, ?_, ?_⟩⟩
  · have : topHom hnat (S.domHom.rangeRestrict g0) = topHom hnat g' := by rw [hg0]
    rw [topHom_apply] at this
    have h2 : (⟨g0.val, g0.2⟩ : S.G) = g0 := rfl
    rw [h2, this]
    exact congrArg Subtype.val hg'top
  · intro v hv hvt
    have h1 := hg'fix ⟨v, hv⟩ (by simpa [A, rowAction] using hvt)
    have h2 : (g'.val ⟨v, hv⟩ : Ω) = g0.val v := by
      rw [← hg0]; rfl
    rw [← h2, h1]

/-! ### The coordinates of the lifts -/

section Coords

variable {k : ℕ} (hk : WinLen L.q k)

/-- The commutator `c = [g₁, h₁]`. -/
def cOf (g1 h1 : Perm Ω) : Perm Ω := rightLocalCommutator g1 h1

/-- The commutator `dⱼ = [c, hⱼ]`. -/
def dOf (g1 h1 hj : Perm Ω) : Perm Ω := rightLocalCommutator (cOf g1 h1) hj

theorem domHom_comm (g h : S.G) :
    S.domHom (⟨rightLocalCommutator g.val h.val, local_commutator_mem S.G g.2 h.2⟩) =
      rightLocalCommutator (S.domHom g) (S.domHom h) := by
  have : (⟨rightLocalCommutator g.val h.val, local_commutator_mem S.G g.2 h.2⟩ : S.G) =
      h * g * h⁻¹ * g⁻¹ := rfl
  rw [this]
  simp [rightLocalCommutator, map_mul, map_inv]

/-- The lifts of the program. -/
structure Lifts (hk : WinLen L.q k) (g1 h1 : Perm Ω) (hs : Fin L.q → Perm Ω) : Prop where
  g1 : WinLift S L label (win1 hk) g1
  h1 : WinLift S L label (win2 hk) h1
  hs : ∀ j : Fin L.q, 3 ≤ (j : ℕ) → WinLift S L label (winJ hk j) (hs j)

variable {hk} {g1 h1 : Perm Ω} {hs : Fin L.q → Perm Ω}

theorem Lifts.c_mem (H : Lifts (S := S) (label := label) hk g1 h1 hs) : cOf g1 h1 ∈ S.G :=
  local_commutator_mem S.G H.g1.mem H.h1.mem

theorem Lifts.d_mem (H : Lifts (S := S) (label := label) hk g1 h1 hs) (j : Fin L.q)
    (hj : 3 ≤ (j : ℕ)) : dOf g1 h1 (hs j) ∈ S.G :=
  local_commutator_mem S.G H.c_mem (H.hs j hj).mem

/-- On the domain, `c` is a clean cycle with top `(0 1 2)`. -/
theorem Lifts.c_clean (hnat : NaturalRows S L label)
    (H : Lifts (S := S) (label := label) hk g1 h1 hs) :
    CleanBlockCycle (domLab (S := S) label) (row0 hk) ⟨1, by have := hk.nine_le; omega⟩
      ⟨2, by have := hk.nine_le; omega⟩ (S.domHom ⟨cOf g1 h1, H.c_mem⟩) := by
  have h5 := hk.five
  have hc := domHom_comm (S := S) ⟨g1, H.g1.mem⟩ ⟨h1, H.h1.mem⟩
  have e : (⟨cOf g1 h1, H.c_mem⟩ : S.G) =
      ⟨rightLocalCommutator g1 h1, local_commutator_mem S.G H.g1.mem H.h1.mem⟩ := rfl
  rw [e, hc]
  have := cleanBlockCycle_of_localized
    (H.g1.localized hnat (win1_nodup hk) (by rw [length_win1]; omega))
    (H.h1.localized hnat (win2_nodup hk) (by rw [length_win2]; omega)) (row0 hk) (meet12 hk)
  rwa [formPerm_win1_zero, formPerm_win2_zero] at this

theorem Lifts.d_eq (H : Lifts (S := S) (label := label) hk g1 h1 hs) (j : Fin L.q)
    (hj : 3 ≤ (j : ℕ)) :
    S.domHom ⟨dOf g1 h1 (hs j), H.d_mem j hj⟩ =
      rightLocalCommutator (S.domHom ⟨cOf g1 h1, H.c_mem⟩) (S.domHom ⟨hs j, (H.hs j hj).mem⟩) :=
  domHom_comm (S := S) ⟨cOf g1 h1, H.c_mem⟩ ⟨hs j, (H.hs j hj).mem⟩

/-- **The cycle data of the lifts**, on the domain. -/
noncomputable def Lifts.cycleData (hnat : NaturalRows S L label)
    (H : Lifts (S := S) (label := label) hk g1 h1 hs) :
    CycleData (domLab (S := S) label) (by have := hk.nine_le; omega : 3 ≤ L.q) where
  c := S.domHom ⟨cOf g1 h1, H.c_mem⟩
  d j := if hj : 3 ≤ (j : ℕ) then S.domHom ⟨dOf g1 h1 (hs j), H.d_mem j hj⟩ else 1
  hc := H.c_clean hnat
  hd j hj := by
    rw [dif_pos hj, H.d_eq j hj]
    have h5 := hk.five
    have := cleanBlockCycle_of_localized
      ((H.c_clean hnat).localized (by simp [row0]) (by simp [row0]) (by simp))
      ((H.hs j hj).localized hnat (winJ_nodup hk j hj) (by rw [length_winJ]; omega)) (row0 hk)
      (meetJ hk j hj)
    rw [formPerm_winJ_zero hk j hj] at this
    convert this using 2
    · rfl
    · simp [cleanCycle, row0, swap_apply_def]
  undo j hj x hx := by
    rw [dif_pos hj, H.d_eq j hj]
    have h5 := hk.five
    exact comm_undo (H.c_clean hnat) (by simp [row0]) (by simp [row0]) (by simp)
      ((H.hs j hj).localized hnat (winJ_nodup hk j hj) (by rw [length_winJ]; omega))
      (meetJ hk j hj) hx

/-- The permutation of `Ω` that carries row `0` to row `j`: `1`, `c`, `c²`, or `dⱼ`. -/
def rhoOf (g1 h1 : Perm Ω) (hs : Fin L.q → Perm Ω) (j : Fin L.q) : Perm Ω :=
  if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then cOf g1 h1
  else if (j : ℕ) = 2 then cOf g1 h1 * cOf g1 h1 else dOf g1 h1 (hs j)

theorem Lifts.rho_val (hnat : NaturalRows S L label)
    (H : Lifts (S := S) (label := label) hk g1 h1 hs) (j : Fin L.q) (v : S.dom) :
    ((H.cycleData hnat).rho j v : Ω) = rhoOf g1 h1 hs j v := by
  unfold CycleData.rho rhoOf
  split_ifs with h0 h1' h2
  · rfl
  · rfl
  · rfl
  · show ((if hj : 3 ≤ (j : ℕ) then S.domHom ⟨dOf g1 h1 (hs j), H.d_mem j hj⟩ else 1) v : Ω) = _
    rw [dif_pos (by omega)]
    rfl

/-- **The coordinates of the lifts are pure** (Theorem A.17), for every numbering `row0` of
row `0`. Point `(b, j)` is `rhoOf j (row0 b)` (`Lifts.coords_val`). -/
theorem Lifts.pureCoords (hnat : NaturalRows S L label)
    (H : Lifts (S := S) (label := label) hk g1 h1 hs) {B : Type}
    (row0 : B ≃ {x : S.dom // domLab label x = ⟨0, by have := hk.nine_le; omega⟩}) :
    PureCoords S L label ((H.cycleData hnat).coordsOf row0) where
  label_e b i := (H.cycleData hnat).label_coordsOf row0 b i
  mem := (H.cycleData hnat).coordsOf_mem row0 S.domGroup ⟨_, rfl⟩ fun j hj => by
    show (if hj : 3 ≤ (j : ℕ) then S.domHom ⟨dOf g1 h1 (hs j), H.d_mem j hj⟩ else 1) ∈ _
    rw [dif_pos hj]; exact ⟨_, rfl⟩

theorem Lifts.coords_val (hnat : NaturalRows S L label)
    (H : Lifts (S := S) (label := label) hk g1 h1 hs) {B : Type}
    (row0 : B ≃ {x : S.dom // domLab label x = ⟨0, by have := hk.nine_le; omega⟩}) (b : B)
    (j : Fin L.q) :
    (((H.cycleData hnat).coordsOf row0 (b, j) : S.dom) : Ω) = rhoOf g1 h1 hs j (row0 b).val.val :=
  H.rho_val hnat j _

end Coords

end GI.Impl
