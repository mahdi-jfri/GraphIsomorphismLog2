module

public import Workspace.Proved.SSInsert
public import Workspace.Proved.SSOrder

@[expose] public section

/-!
# Building a closed table

`ssBuild B gs` starts from the empty table, inserts every generator (`ssGens`), and then runs
`M + 1` rounds (`ssRound`), `M = |B| · n` being the number of slots. A round goes over all pairs
`(p, q)` of slots, as `k = p · M + q` for `k < M²`, and inserts the product of the two entries if
both slots are filled (`ssPair`).

A round either fills a slot, or changes nothing; in the second case every product of two entries
sifted through, so the table is closed (`ssRound_spec`). There are only `M` slots, so after
`M + 1` rounds the table is closed (`ssBuild_spec`).
-/

namespace GI.Proved

open Equiv GI.Cited

variable {n : ℕ}

/-- Insert generator `a`. -/
def ssGenStep (B : List (Fin n)) (gs : List (Perm (Fin n))) (st : SsState n) (a : ℕ) :
    SsState n :=
  ssInsert B st (gs[a]?.getD 1) (.gen a)

/-- Insert all generators. -/
def ssGens (B : List (Fin n)) (gs : List (Perm (Fin n))) (st : SsState n) : SsState n :=
  (List.range gs.length).foldl (ssGenStep B gs) st

/-- The pair `(k / M, k % M)` of slots: insert the product of their entries if both are
filled. -/
def ssPair (B : List (Fin n)) (M : ℕ) (st : SsState n) (k : ℕ) : SsState n :=
  match (st.1[k / M]?).join, (st.1[k % M]?).join with
  | some s, some t => ssInsert B st (s.1 * t.1) (.mul s.2 t.2)
  | _, _ => st

/-- One round: all pairs of slots. -/
def ssRound (B : List (Fin n)) (M : ℕ) (st : SsState n) : SsState n :=
  (List.range (M * M)).foldl (ssPair B M) st

/-- The empty state. -/
def ssInit (B : List (Fin n)) : SsState n := (List.replicate (B.length * n) none, [])

/-- **The algorithm.** -/
def ssBuild (B : List (Fin n)) (gs : List (Perm (Fin n))) : SsState n :=
  (List.range (B.length * n + 1)).foldl (fun st _ => ssRound B (B.length * n) st)
    (ssGens B gs (ssInit B))

section Spec

variable {B : List (Fin n)} {gs : List (Perm (Fin n))}

theorem ssInsert_of_thru (st : SsState n) {g : Perm (Fin n)} (ins0 : SlpInstr)
    (h : ssThru st.1 B 0 g = true) : ssInsert B st g ins0 = st := by
  unfold ssInsert
  have : (ssSift B st.1 g).2.2 = 0 := by rw [ssSift_eq, ssSiftR_stop]; exact h
  simp only [this, if_true]

theorem ssInv_init : SsInv B gs (ssInit B) := by
  refine ⟨by simp [ssInit], ⟨fun i j e he => ?_⟩, ⟨[], rfl, fun i j e he => ?_⟩, by simp [ssInit]⟩
  all_goals
    simp only [ssInit, ssGet, List.getElem?_replicate] at he
    split_ifs at he <;> simp at he

theorem ssFill_le (T : List (SsSlot n)) : ssFill T ≤ T.length := List.countP_le_length

/-- A filled slot `p < |B| · n` is the slot of level `p / n` and point `p % n`. -/
theorem ssGet_of_slot {T : List (SsSlot n)} {p : ℕ} {s : Perm (Fin n) × ℕ}
    (h : (T[p]?).join = some s) (hp : p < B.length * n) :
    ∃ i j, ssGet T i j = some s ∧ i * n + (j : ℕ) = p := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
  refine ⟨p / n, ⟨p % n, Nat.mod_lt _ hn⟩, ?_, ?_⟩
  · unfold ssGet; simp only; rw [Nat.div_add_mod' p n]; exact h
  · simp only; rw [Nat.div_add_mod']

theorem ssGens_spec (hinv : SsInv B gs (ssInit B)) :
    SsInv B gs (ssGens B gs (ssInit B)) ∧ ∀ g ∈ gs, ssThru (ssGens B gs (ssInit B)).1 B 0 g = true := by
  suffices h : ∀ a ≤ gs.length, SsInv B gs ((List.range a).foldl (ssGenStep B gs) (ssInit B)) ∧
      ∀ a' < a, ssThru ((List.range a).foldl (ssGenStep B gs) (ssInit B)).1 B 0
        (gs[a']?.getD 1) = true by
    obtain ⟨h1, h2⟩ := h gs.length le_rfl
    refine ⟨h1, fun g hg => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hg
    have := h2 a ha
    rwa [List.getElem?_eq_getElem ha, Option.getD_some] at this
  intro a
  induction a with
  | zero => intro _; exact ⟨hinv, fun a' ha' => absurd ha' (Nat.not_lt_zero _)⟩
  | succ a ih =>
    intro ha
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set st := (List.range a).foldl (ssGenStep B gs) (ssInit B)
    obtain ⟨es, hes, _⟩ := h1.slp
    have hga : gs[a]?.getD 1 = gs[a] := by
      rw [List.getElem?_eq_getElem (show a < gs.length by omega)]; rfl
    obtain ⟨i1, i2, i3, -⟩ := ssInsert_spec h1 hes (g := gs[a]?.getD 1) (ins0 := .gen a)
      (by rw [hga]; exact slpEntries_gen (by omega) es)
    refine ⟨i1, fun a' ha' => ?_⟩
    rcases Nat.lt_or_ge a' a with h | h
    · exact ssThru_mono i2 _ _ _ (h2 a' h)
    · obtain rfl : a' = a := by omega
      exact i3

/-- One pair step. -/
theorem ssPair_spec {M : ℕ} (hM : M = B.length * n) {st : SsState n} (hinv : SsInv B gs st)
    (k : ℕ) :
    SsInv B gs (ssPair B M st k) ∧ SsLe st.1 (ssPair B M st k).1 ∧
      ((ssPair B M st k = st ∧ ∀ s t, (st.1[k / M]?).join = some s →
          (st.1[k % M]?).join = some t → ssThru st.1 B 0 (s.1 * t.1) = true) ∨
        ssFill (ssPair B M st k).1 = ssFill st.1 + 1) := by
  unfold ssPair
  cases hs : (st.1[k / M]?).join with
  | none => exact ⟨hinv, SsLe.refl _, Or.inl ⟨rfl, fun s t h => by simp at h⟩⟩
  | some s =>
    cases ht : (st.1[k % M]?).join with
    | none => exact ⟨hinv, SsLe.refl _, Or.inl ⟨rfl, fun s t _ h => by simp at h⟩⟩
    | some t =>
      simp only
      obtain ⟨es, hes, hcons⟩ := hinv.slp
      have hlt : ∀ {p : ℕ}, (st.1[p]?).join = some s ∨ (st.1[p]?).join = some t → p < M := by
        intro p hp
        rw [hM, ← hinv.len]
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hp
        simp at hp
      obtain ⟨i, j, hij, -⟩ := ssGet_of_slot (B := B) hs (hM ▸ hlt (Or.inl hs))
      obtain ⟨i', j', hij', -⟩ := ssGet_of_slot (B := B) ht (hM ▸ hlt (Or.inr ht))
      have h1 := hcons _ _ _ hij
      have h2 := hcons _ _ _ hij'
      obtain ⟨hs1, hs2⟩ := List.getElem?_eq_some_iff.mp h1
      obtain ⟨ht1, ht2⟩ := List.getElem?_eq_some_iff.mp h2
      obtain ⟨i1, i2, -, i4⟩ := ssInsert_spec hinv hes (g := s.1 * t.1) (ins0 := .mul s.2 t.2)
        (by rw [slpEntries_mul _ hs1 ht1, hs2, ht2])
      refine ⟨i1, i2, ?_⟩
      rcases i4 with ⟨h5, h6⟩ | h5
      · refine Or.inl ⟨h6, fun s' t' h7 h8 => ?_⟩
        cases h7; cases h8
        exact h5
      · exact Or.inr h5

/-- A run of pair steps: either it fills a slot, or it changes nothing and every pair it looked
at sifted through. -/
theorem ssPairs_spec {M : ℕ} (hM : M = B.length * n) (l : List ℕ) :
    ∀ st : SsState n, SsInv B gs st →
      SsInv B gs (l.foldl (ssPair B M) st) ∧ SsLe st.1 (l.foldl (ssPair B M) st).1 ∧
      ssFill st.1 ≤ ssFill (l.foldl (ssPair B M) st).1 ∧
      (ssFill (l.foldl (ssPair B M) st).1 = ssFill st.1 → l.foldl (ssPair B M) st = st ∧
        ∀ k ∈ l, ∀ s t, (st.1[k / M]?).join = some s → (st.1[k % M]?).join = some t →
          ssThru st.1 B 0 (s.1 * t.1) = true) := by
  induction l with
  | nil => intro st h; exact ⟨h, SsLe.refl _, le_rfl, fun _ => ⟨rfl, fun k hk => by simp at hk⟩⟩
  | cons k l ih =>
    intro st hinv
    rw [List.foldl_cons]
    obtain ⟨p1, p2, p3⟩ := ssPair_spec (gs := gs) hM hinv k
    obtain ⟨q1, q2, q3, q4⟩ := ih _ p1
    rcases p3 with ⟨h, h'⟩ | h
    · rw [h] at q1 q2 q3 q4 ⊢
      refine ⟨q1, q2, q3, fun hf => ?_⟩
      obtain ⟨r1, r2⟩ := q4 hf
      refine ⟨r1, fun k' hk' => ?_⟩
      rcases List.mem_cons.mp hk' with rfl | hk'
      · exact h'
      · exact r2 k' hk'
    · exact ⟨q1, p2.trans q2, by omega, fun hf => by omega⟩

/-- The pairs of all filled slots appear in a round. -/
theorem ssClosed_of_round {T : List (SsSlot n)} (hlen : T.length = B.length * n)
    (h : ∀ k ∈ List.range (T.length * T.length), ∀ s t, (T[k / T.length]?).join = some s →
      (T[k % T.length]?).join = some t → ssThru T B 0 (s.1 * t.1) = true) : SsClosed B T := by
  intro i j e i' j' e' he he'
  have hp : ∀ {i : ℕ} {j : Fin n} {e : Perm (Fin n) × ℕ}, ssGet T i j = some e →
      i * n + (j : ℕ) < T.length := by
    intro i j e he
    by_contra hc
    unfold ssGet at he
    rw [List.getElem?_eq_none (by omega)] at he
    simp at he
  have h1 := hp he
  have h2 := hp he'
  set M := T.length
  have hM : 0 < M := by omega
  refine h ((i * n + j) * M + (i' * n + j')) ?_ e e' ?_ ?_
  · rw [List.mem_range]
    calc (i * n + j) * M + (i' * n + j') < (i * n + j) * M + M := by omega
      _ = (i * n + j + 1) * M := by ring
      _ ≤ M * M := Nat.mul_le_mul_right _ h1
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt h2, Nat.zero_add]; exact he
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]; exact he'

/-- On a closed table a round changes nothing. -/
theorem ssPairs_closed {M : ℕ} (l : List ℕ) (st : SsState n) (hlen : st.1.length = B.length * n)
    (hM : M = st.1.length) (hc : SsClosed B st.1) : l.foldl (ssPair B M) st = st := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons]
    have hp : ∀ {p : ℕ} {u : Perm (Fin n) × ℕ}, (st.1[p]?).join = some u →
        ∃ i j, ssGet st.1 i j = some u := by
      intro p u hu
      have hpl : p < st.1.length := by
        by_contra hc'; rw [List.getElem?_eq_none (by omega)] at hu; simp at hu
      obtain ⟨i, j, h, -⟩ := ssGet_of_slot (B := B) hu (by omega)
      exact ⟨i, j, h⟩
    have : ssPair B M st k = st := by
      unfold ssPair
      cases hs : (st.1[k / M]?).join with
      | none => rfl
      | some s =>
        cases ht : (st.1[k % M]?).join with
        | none => rfl
        | some t =>
          simp only
          obtain ⟨i, j, hij⟩ := hp hs
          obtain ⟨i', j', hij'⟩ := hp ht
          exact ssInsert_of_thru st _ (hc _ _ _ _ _ _ hij hij')
    rw [this]; exact ih

/-- The rounds: after `r` rounds the table is closed or has at least `r` entries. -/
theorem ssRounds_spec (st0 : SsState n) (hinv0 : SsInv B gs st0)
    (hgen0 : ∀ g ∈ gs, ssThru st0.1 B 0 g = true) : ∀ r,
    SsInv B gs ((List.range r).foldl (fun st _ => ssRound B (B.length * n) st) st0) ∧
    (∀ g ∈ gs, ssThru ((List.range r).foldl (fun st _ => ssRound B (B.length * n) st) st0).1
      B 0 g = true) ∧
    (SsClosed B ((List.range r).foldl (fun st _ => ssRound B (B.length * n) st) st0).1 ∨
      r ≤ ssFill ((List.range r).foldl (fun st _ => ssRound B (B.length * n) st) st0).1) := by
  intro r
  induction r with
  | zero => exact ⟨hinv0, hgen0, Or.inr (Nat.zero_le _)⟩
  | succ r ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set st := (List.range r).foldl (fun st _ => ssRound B (B.length * n) st) st0
    have hM : B.length * n = st.1.length := h1.len.symm
    obtain ⟨q1, q2, q3, q4⟩ := ssPairs_spec (gs := gs) (B := B) rfl
      (List.range (B.length * n * (B.length * n))) st h1
    refine ⟨q1, fun g hg => ssThru_mono q2 _ _ _ (h2 g hg), ?_⟩
    unfold ssRound
    rcases h3 with hc | hr
    · left
      rw [ssPairs_closed _ st h1.len hM hc]
      exact hc
    · by_cases hf : ssFill (List.foldl (ssPair B (B.length * n)) st
          (List.range (B.length * n * (B.length * n)))).1 = ssFill st.1
      · left
        obtain ⟨r1, r2⟩ := q4 hf
        rw [r1]
        refine ssClosed_of_round h1.len ?_
        rw [← hM]
        exact r2
      · right; omega

/-- **The algorithm builds a closed table.** -/
theorem ssBuild_spec :
    SsInv B gs (ssBuild B gs) ∧ SsClosed B (ssBuild B gs).1 ∧
      ∀ g ∈ gs, ssThru (ssBuild B gs).1 B 0 g = true := by
  obtain ⟨g1, g2⟩ := ssGens_spec (B := B) (gs := gs) ssInv_init
  obtain ⟨h1, h2, h3⟩ := ssRounds_spec _ g1 g2 (B.length * n + 1)
  refine ⟨h1, ?_, h2⟩
  rcases h3 with h | h
  · exact h
  · have := ssFill_le (ssBuild B gs).1
    unfold ssBuild at this
    rw [h1.len] at this
    omega

/-- The entries of an invariant state lie in `⟨gs⟩`. -/
theorem SsInv.entry_mem {st : SsState n} (hinv : SsInv B gs st) :
    ∀ i j e, ssGet st.1 i j = some e → e.1 ∈ gens gs := by
  obtain ⟨es, hes, hcons⟩ := hinv.slp
  intro i j e he
  exact slpEntries_mem_gens _ [] es (by simp) hes _ (List.mem_of_getElem? (hcons _ _ _ he))

end Spec

end GI.Proved
