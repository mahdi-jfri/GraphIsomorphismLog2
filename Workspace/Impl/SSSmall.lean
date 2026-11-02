import Workspace.Impl.SSSiftLoop

/-!
# Every state of the algorithm is small

A state with the invariant `SsInv` has a program of length at most `|B| n (2|B| + 1)`
(`SsInv.plen`, as at most `|B| n` slots are filled), every slot holds an index into that program,
and every instruction names an earlier entry or a generator. So with `Y ≥ n + |B| + |gs| + 2`,
the table and the program are `SsSmall (ssZ Y)` (`ssInv_small`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-- Every instruction of a valid program names an earlier entry or a generator. -/
theorem ss_slp_max (gs : List (Perm (Fin n))) (p : List SlpInstr) (acc es : List (Perm (Fin n)))
    (h : slpEntries gs p acc = some es) : ∀ ins ∈ p, ssInsMax ins < es.length + gs.length := by
  induction p generalizing acc with
  | nil => simp
  | cons ins p ih =>
    intro x hx
    have key : ∃ g, slpEntries gs p (acc ++ [g]) = some es ∧
        ssInsMax ins < acc.length + gs.length := by
      cases ins with
      | gen i =>
        cases hi : gs[i]? with
        | none => simp [slpEntries, hi] at h
        | some g =>
          refine ⟨g, by simpa [slpEntries, hi] using h, ?_⟩
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp only [ssInsMax]; omega
      | inv j =>
        cases hj : acc[j]? with
        | none => simp [slpEntries, hj] at h
        | some g =>
          refine ⟨g⁻¹, by simpa [slpEntries, hj] using h, ?_⟩
          have := (List.getElem?_eq_some_iff.mp hj).1
          simp only [ssInsMax]; omega
      | mul j k =>
        cases hj : acc[j]? with
        | none => simp [slpEntries, hj] at h
        | some g =>
          cases hk : acc[k]? with
          | none => simp [slpEntries, hj, hk] at h
          | some g' =>
            refine ⟨g * g', by simpa [slpEntries, hj, hk] using h, ?_⟩
            have := (List.getElem?_eq_some_iff.mp hj).1
            have := (List.getElem?_eq_some_iff.mp hk).1
            simp only [ssInsMax]; omega
    obtain ⟨g, hg, hm⟩ := key
    obtain ⟨v, rfl, -⟩ := slpEntries_prefix p _ es hg
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [List.length_append, List.length_singleton]; omega
    · exact ih _ hg x hx

/-- Numbers used to bound sizes. -/
theorem ss_Y_facts {L G Y : ℕ} (hY : n + L + G + 2 ≤ Y) :
    L * n * (2 * L + 1) ≤ 3 * Y ^ 3 ∧ L * n * (2 * n + 8) ≤ 10 * Y ^ 3 ∧
      (G + 1) * (2 * n + 3) ≤ 3 * Y ^ 3 ∧ Y ≤ Y ^ 3 ∧ 100 * Y ^ 3 + 1000 ≤ ssZ Y := by
  have h1 : 1 ≤ Y := by omega
  have e3 : Y ^ 3 = Y * Y * Y := by ring
  have hYY : Y ≤ Y * Y := Nat.le_mul_of_pos_left Y h1
  have hYYY : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc L * n * (2 * L + 1) ≤ Y * Y * (3 * Y) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = 3 * Y ^ 3 := by ring
  · calc L * n * (2 * n + 8) ≤ Y * Y * (10 * Y) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = 10 * Y ^ 3 := by ring
  · calc (G + 1) * (2 * n + 3) ≤ Y * (3 * Y) := Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * (Y * Y) := by ring
      _ ≤ 3 * Y ^ 3 := by rw [e3]; omega
  · rw [e3]; omega
  · have h4 : Y ^ 4 = Y ^ 3 * Y := by ring
    have hY3 : 8 ≤ Y ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have : Y ^ 3 * 2 ≤ Y ^ 3 * Y := Nat.mul_le_mul_left _ (by omega)
    unfold ssZ
    omega

/-- Facts about a state with the invariant. -/
structure SsSmallSt (Y : ℕ) (st : SsState n) : Prop where
  idx : ∀ s ∈ st.1, ∀ e, s = some e → e.2 ≤ ssZ Y
  tab : SsSmall (ssZ Y) (ssEncTab st.1)
  prog : SsSmall (ssZ Y) (ssEncProg st.2)
  ins : ∀ ins ∈ st.2, ssInsMax ins ≤ ssZ Y
  plen : st.2.length * 9 + 3 ≤ ssZ Y
  plen' : st.2.length ≤ 3 * Y ^ 3

/-- **Every state is small.** -/
theorem ssInv_small {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n}
    (hinv : SsInv B gs st) {Y : ℕ} (hY : n + B.length + gs.length + 2 ≤ Y) : SsSmallSt Y st := by
  obtain ⟨hK, hT, -, hY3, hZ⟩ := ss_Y_facts hY
  obtain ⟨es, hes, hcons⟩ := hinv.slp
  have hlen : es.length = st.2.length := by
    obtain ⟨v, rfl, hv⟩ := slpEntries_prefix _ _ _ hes
    simpa using hv
  have hp : st.2.length ≤ 3 * Y ^ 3 := by
    have h1 := hinv.plen
    have h2 : ssFill st.1 * (2 * B.length + 1) ≤ B.length * n * (2 * B.length + 1) :=
      Nat.mul_le_mul_right _ ((ssFill_le st.1).trans hinv.len.le)
    omega
  have hidx : ∀ s ∈ st.1, ∀ e, s = some e → e.2 < st.2.length := by
    rintro s hs e rfl
    obtain ⟨p, hp, hps⟩ := List.getElem_of_mem hs
    have hp' : p < B.length * n := hinv.len ▸ hp
    obtain ⟨i, j, hij, -⟩ := ssGet_of_slot (B := B) (T := st.1) (p := p) (s := e)
      (by rw [List.getElem?_eq_getElem hp, hps]; rfl) hp'
    have := (List.getElem?_eq_some_iff.mp (hcons i j e hij)).1
    omega
  have hins : ∀ ins ∈ st.2, ssInsMax ins ≤ ssZ Y := fun ins h => by
    have := ss_slp_max gs st.2 [] es hes ins h
    omega
  refine ⟨fun s hs e he => by have := hidx s hs e he; omega, ?_, ?_, hins, by omega, hp⟩
  · refine ssSmall_tab (fun s hs e he => by have := hidx s hs e he; omega) ?_ (by omega)
    rw [hinv.len]; omega
  · exact ssSmall_prog hins (by omega) (by omega)

theorem SsSmallSt.st {Y : ℕ} {st : SsState n} (h : SsSmallSt Y st) (hn : n + 2 ≤ Y)
    (hT : st.1.length * (2 * n + 8) ≤ 10 * Y ^ 3) : SsSmall (ssZ Y) (ssEncSt st) := by
  obtain ⟨-, -, -, hY3, hZ⟩ := ss_Y_facts (L := 0) (G := 0) (n := n) (by omega : n + 0 + 0 + 2 ≤ Y)
  refine ssSmall_list ?_ fun v hv => ?_
  · rw [size_list_eq]
    have h1 := size_ssEncTab st.1
    have h2 : (ssEncProg st.2).size ≤ st.2.length * 9 + 3 := by
      unfold ssEncProg
      refine (size_list_le fun v hv => ?_).trans (by rw [List.length_map])
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hv; exact size_encSlpInstr_le s
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := h.plen'
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact h.tab
    · exact h.prog

end GI.Impl
