import Workspace.Proved.SSSift

/-!
# Inserting into the table, with straight-line programs

The state of the algorithm is the table and a straight-line program `prog` over the generators.
Every entry `(t, k)` of the table has `t` as entry `k` of the program (`SsCons`).

To insert `g`, given an instruction `ins0` that computes `g` from the program so far, sift `g`.
If it stops at level `k`, the remainder `r = ssW es X * g` goes into the empty slot
`(k, r B[k])`, and the program gets `ins0`, then `inv u` and a `mul` for each used index `u`
(`ssChain`), so that its last entry is `r` (`ssChain_spec`).

`ssInsert_spec`: insertion keeps the invariant `SsInv`, only adds slots, lets `g` through
afterwards, and either changes nothing (when `g` already sifted through) or fills one more slot.
-/

namespace GI.Proved

open Equiv GI.Cited

variable {n : ℕ}

/-! ### Straight-line programs -/

section Slp

variable {gs : List (Perm (Fin n))}

theorem slpEntries_cons (ins : SlpInstr) (prog : List SlpInstr) (acc : List (Perm (Fin n))) :
    slpEntries gs (ins :: prog) acc = (match ins with
      | .gen i => gs[i]?
      | .inv j => acc[j]?.map (·⁻¹)
      | .mul j k => do let a ← acc[j]?; let b ← acc[k]?; pure (a * b)).bind
        (fun g => slpEntries gs prog (acc ++ [g])) := by
  cases ins <;> simp only [slpEntries] <;> split <;> rename_i h <;> rw [h] <;> rfl

theorem slpEntries_append (p q : List SlpInstr) (acc : List (Perm (Fin n))) :
    slpEntries gs (p ++ q) acc = (slpEntries gs p acc).bind (fun es => slpEntries gs q es) := by
  induction p generalizing acc with
  | nil => simp [slpEntries]
  | cons ins p ih =>
    rw [List.cons_append, slpEntries_cons, slpEntries_cons]
    cases (match ins with
      | .gen i => gs[i]?
      | .inv j => acc[j]?.map (·⁻¹)
      | .mul j k => do let a ← acc[j]?; let b ← acc[k]?; pure (a * b)) with
    | none => rfl
    | some g => simp only [Option.bind_some]; exact ih _

theorem slpEntries_prefix (p : List SlpInstr) (acc es : List (Perm (Fin n)))
    (h : slpEntries gs p acc = some es) : ∃ v, es = acc ++ v ∧ v.length = p.length := by
  induction p generalizing acc with
  | nil => simp only [slpEntries, Option.some.injEq] at h; exact ⟨[], by simp [h], rfl⟩
  | cons ins p ih =>
    rw [slpEntries_cons] at h
    cases hn : (match ins with
      | .gen i => gs[i]?
      | .inv j => acc[j]?.map (·⁻¹)
      | .mul j k => do let a ← acc[j]?; let b ← acc[k]?; pure (a * b)) with
    | none => rw [hn] at h; simp at h
    | some g =>
      rw [hn, Option.bind_some] at h
      obtain ⟨v, rfl, hv⟩ := ih _ h
      exact ⟨g :: v, by simp, by simp [hv]⟩

theorem slpEntries_mem_gens (p : List SlpInstr) (acc es : List (Perm (Fin n)))
    (hacc : ∀ x ∈ acc, x ∈ gens gs) (h : slpEntries gs p acc = some es) : ∀ x ∈ es, x ∈ gens gs := by
  induction p generalizing acc with
  | nil => simp only [slpEntries, Option.some.injEq] at h; rw [← h]; exact hacc
  | cons ins p ih =>
    rw [slpEntries_cons] at h
    cases hn : (match ins with
      | .gen i => gs[i]?
      | .inv j => acc[j]?.map (·⁻¹)
      | .mul j k => do let a ← acc[j]?; let b ← acc[k]?; pure (a * b)) with
    | none => rw [hn] at h; simp at h
    | some g =>
      rw [hn, Option.bind_some] at h
      refine ih _ (fun x hx => ?_) h
      rcases List.mem_append.mp hx with hx | hx
      · exact hacc x hx
      · rw [List.mem_singleton] at hx
        subst hx
        cases ins with
        | gen i =>
          obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hn
          exact Subgroup.subset_closure (List.getElem_mem hi)
        | inv j =>
          simp only [Option.map_eq_some_iff] at hn
          obtain ⟨a, ha, rfl⟩ := hn
          exact Subgroup.inv_mem _ (hacc a (List.mem_of_getElem? ha))
        | mul j k =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at hn
          obtain ⟨a, ha, b, hb, rfl⟩ := hn
          exact Subgroup.mul_mem _ (hacc a (List.mem_of_getElem? ha))
            (hacc b (List.mem_of_getElem? hb))

theorem slpEntries_gen {i : ℕ} (hi : i < gs.length) (acc : List (Perm (Fin n))) :
    slpEntries gs [.gen i] acc = some (acc ++ [gs[i]]) := by
  simp [slpEntries, hi]

theorem slpEntries_inv {j : ℕ} (acc : List (Perm (Fin n))) (hj : j < acc.length) :
    slpEntries gs [.inv j] acc = some (acc ++ [acc[j]⁻¹]) := by
  simp [slpEntries, hj]

theorem slpEntries_mul {j k : ℕ} (acc : List (Perm (Fin n))) (hj : j < acc.length)
    (hk : k < acc.length) : slpEntries gs [.mul j k] acc = some (acc ++ [acc[j] * acc[k]]) := by
  simp [slpEntries, hj, hk]

/-- One link of the chain: `inv u`, then multiply it by the last entry. -/
def ssChain (N : ℕ) (acc : List SlpInstr) (u : ℕ) : List SlpInstr :=
  acc ++ [.inv u, .mul (N + acc.length) (N + acc.length - 1)]

theorem length_foldl_ssChain (N : ℕ) (X : List ℕ) (loc : List SlpInstr) :
    (X.foldl (ssChain N) loc).length = loc.length + 2 * X.length := by
  induction X generalizing loc with
  | nil => simp
  | cons u X ih => rw [List.foldl_cons, ih]; simp [ssChain]; omega

/-- **The chain.** Starting from a local program `loc0` whose last entry is `x`, the chain of
`X` ends with `ssW es X * x`. -/
theorem ssChain_spec (es : List (Perm (Fin n))) (X : List ℕ) (hX : ∀ k ∈ X, k < es.length) :
    ∀ (loc0 : List SlpInstr) (v0 : List (Perm (Fin n))) (x : Perm (Fin n)),
      slpEntries gs loc0 es = some (es ++ v0) → v0.getLast? = some x →
      ∃ v, slpEntries gs (X.foldl (ssChain es.length) loc0) es = some (es ++ v) ∧
        v.getLast? = some (ssW es X * x) := by
  induction X with
  | nil => intro loc0 v0 x h1 h2; exact ⟨v0, h1, by simpa [ssW] using h2⟩
  | cons u X ih =>
    intro loc0 v0 x h1 h2
    rw [List.foldl_cons]
    obtain ⟨v, hv, hvl⟩ := slpEntries_prefix _ _ _ h1
    have hv0 : v0 = v := List.append_cancel_left hv
    subst hv0
    have hu : u < es.length := hX u (by simp)
    have hne : v0 ≠ [] := by rintro rfl; simp at h2
    have hlast : v0[v0.length - 1]'(by have := List.length_pos_of_ne_nil hne; omega) = x := by
      rw [List.getLast?_eq_getElem?] at h2
      exact Option.some_injective _ ((List.getElem?_eq_getElem _).symm.trans h2)
    -- the two new entries
    have hA : es.length + loc0.length = (es ++ v0).length := by simp [hvl]
    have hAp : 0 < v0.length := List.length_pos_of_ne_nil hne
    have h3 : slpEntries gs (ssChain es.length loc0 u) es =
        some ((es ++ v0) ++ [es[u]⁻¹, es[u]⁻¹ * x]) := by
      unfold ssChain
      rw [hA, slpEntries_append, h1, Option.bind_some,
        show [SlpInstr.inv u, .mul (es ++ v0).length ((es ++ v0).length - 1)] =
          [SlpInstr.inv u] ++ [.mul (es ++ v0).length ((es ++ v0).length - 1)] from
          rfl, slpEntries_append, slpEntries_inv _ (by simp only [List.length_append, List.length_singleton]; omega),
        Option.bind_some,
        slpEntries_mul _ (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)]
      have hu' : u < (es ++ v0).length := by simp only [List.length_append]; omega
      have e1 : (es ++ v0)[u]'hu' = es[u] := List.getElem_append_left hu
      have hL1 : (es ++ v0).length < ((es ++ v0) ++ [((es ++ v0)[u]'hu')⁻¹]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hL2 : (es ++ v0).length - 1 < ((es ++ v0) ++ [((es ++ v0)[u]'hu')⁻¹]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have g1 : ((es ++ v0) ++ [((es ++ v0)[u]'hu')⁻¹])[(es ++ v0).length]'hL1 = es[u]⁻¹ := by
        simp [e1]
      have g2 : ((es ++ v0) ++ [((es ++ v0)[u]'hu')⁻¹])[(es ++ v0).length - 1]'hL2 = x := by
        rw [List.getElem_append_left (by simp only [List.length_append]; omega),
          List.getElem_append_right (by omega)]
        rw [← hlast]
        congr 1
        simp only [List.length_append]
        omega
      rw [g1, g2, e1]
      simp
    obtain ⟨v, hv1, hv2⟩ := ih (fun k hk => hX k (by simp [hk])) _ (v0 ++ [es[u]⁻¹, es[u]⁻¹ * x]) _
      (by rw [h3, List.append_assoc]) (by rw [List.getLast?_append]; rfl)
    refine ⟨v, hv1, ?_⟩
    rw [hv2, ssW, mul_assoc]
    congr 2
    simp [hu]

end Slp

/-! ### Insertion -/

/-- The state: the table and the program. -/
abbrev SsState (n : ℕ) := List (SsSlot n) × List SlpInstr

/-- The number of filled slots. -/
def ssFill (T : List (SsSlot n)) : ℕ := T.countP fun s => s.isSome

/-- **Insertion** of `g`, computed by the instruction `ins0` from the program so far. -/
def ssInsert (B : List (Fin n)) (st : SsState n) (g : Perm (Fin n)) (ins0 : SlpInstr) :
    SsState n :=
  let r := ssSift B st.1 g
  if r.2.2 = 0 then st else
  match B[r.2.2 - 1]? with
  | none => st
  | some b =>
    let loc := r.2.1.foldl (ssChain st.2.length) [ins0]
    (st.1.set ((r.2.2 - 1) * n + (r.1 b : ℕ)) (some (r.1, st.2.length + loc.length - 1)),
      st.2 ++ loc)

/-- The invariant of the state. -/
structure SsInv (B : List (Fin n)) (gs : List (Perm (Fin n))) (st : SsState n) : Prop where
  len : st.1.length = B.length * n
  wf : SsWF B st.1
  slp : ∃ es, slpEntries gs st.2 [] = some es ∧ SsCons st.1 es
  plen : st.2.length ≤ ssFill st.1 * (2 * B.length + 1)

theorem ss_slot_eq {i k : ℕ} {j j' : Fin n} (h : i * n + (j' : ℕ) = k * n + (j : ℕ)) :
    i = k ∧ j' = j := by
  have hn : 0 < n := Fin.pos j
  have h1 : (i * n + (j' : ℕ)) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j'.isLt, Nat.zero_add]
  have h2 : (k * n + (j : ℕ)) / n = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have hik : i = k := by rw [← h1, h, h2]
  subst hik
  exact ⟨rfl, Fin.ext (by omega)⟩

theorem ssGet_set (T : List (SsSlot n)) (q : ℕ) (s : SsSlot n) (i : ℕ) (j : Fin n) :
    ssGet (T.set q s) i j = if i * n + (j : ℕ) = q ∧ q < T.length then s else ssGet T i j := by
  unfold ssGet
  rw [List.getElem?_set]
  by_cases h1 : q = i * n + (j : ℕ)
  · subst h1
    by_cases h2 : i * n + (j : ℕ) < T.length <;> simp [h2]
  · rw [if_neg h1, if_neg (fun h => h1 h.1.symm)]

section InsertSpec

variable {B : List (Fin n)} {gs : List (Perm (Fin n))}

/-- **Insertion.** -/
theorem ssInsert_spec {st : SsState n} (hinv : SsInv B gs st) {es : List (Perm (Fin n))}
    (hes : slpEntries gs st.2 [] = some es) {g : Perm (Fin n)} {ins0 : SlpInstr}
    (hins : slpEntries gs [ins0] es = some (es ++ [g])) :
    SsInv B gs (ssInsert B st g ins0) ∧ SsLe st.1 (ssInsert B st g ins0).1 ∧
      ssThru (ssInsert B st g ins0).1 B 0 g = true ∧
      ((ssThru st.1 B 0 g = true ∧ ssInsert B st g ins0 = st) ∨
        ssFill (ssInsert B st g ins0).1 = ssFill st.1 + 1) := by
  obtain ⟨T, prog⟩ := st
  obtain ⟨hlen, hwf, ⟨es', hes', hcons⟩, hplen⟩ := hinv
  simp only at hes hes' hcons hlen hwf hplen
  obtain rfl : es = es' := Option.some_injective _ (hes.symm.trans hes')
  have hsift := ssSift_eq B T g
  obtain ⟨X, hX1, hX2, hX3, hX4⟩ := ssSiftR_used hcons B 0 g []
  set r := ssSiftR T B 0 g [] with hr
  rcases hstop : r.2.2 with _ | k
  · -- `g` sifts through: nothing changes
    have hthru : ssThru T B 0 g = true := (ssSiftR_stop T B 0 g []).mp hstop
    have heq : ssInsert B (T, prog) g ins0 = (T, prog) := by
      unfold ssInsert; simp only [hsift, hstop, if_true]
    rw [heq]
    exact ⟨⟨hlen, hwf, ⟨es, hes, hcons⟩, hplen⟩, SsLe.refl _, hthru, Or.inl ⟨hthru, rfl⟩⟩
  · -- `g` stops at level `k`
    obtain ⟨hk, hfix, hdiag, hempty⟩ := ssSiftR_stop_succ hwf B.length 0 g [] (by omega)
      (by simp) k (by simpa using hstop)
    simp only [List.drop_zero, ← hr] at hfix hdiag hempty
    set j := r.1 B[k] with hj
    set loc := X.foldl (ssChain prog.length) [ins0] with hloc
    obtain ⟨vg, hvg, hvgl⟩ : ∃ v, slpEntries gs loc es = some (es ++ v) ∧
        v.getLast? = some (ssW es X * g) := by
      have hpl : prog.length = es.length := by
        obtain ⟨v, rfl, hv⟩ := slpEntries_prefix _ _ _ hes; simpa using hv.symm
      rw [hloc, hpl]
      exact ssChain_spec es X hX4 [ins0] [g] g hins rfl
    obtain ⟨vg', hvg', hvgl'⟩ := slpEntries_prefix _ _ _ hvg
    have hvv : vg = vg' := List.append_cancel_left hvg'
    subst hvv
    have hpl : prog.length = es.length := by
      obtain ⟨v, rfl, hv⟩ := slpEntries_prefix _ _ _ hes; simpa using hv.symm
    set idx := prog.length + loc.length - 1 with hidx
    set q := k * n + (j : ℕ) with hq
    have hqT : q < T.length := by
      rw [hlen]
      calc k * n + (j : ℕ) < k * n + n := by omega
        _ = (k + 1) * n := by ring
        _ ≤ B.length * n := Nat.mul_le_mul_right _ hk
    have hTq : T[q]? = some none := by
      have : (T[q]?).join = none := hempty
      rw [List.getElem?_eq_getElem hqT] at this ⊢
      simpa using this
    have heq : ssInsert B (T, prog) g ins0 = (T.set q (some (r.1, idx)), prog ++ loc) := by
      unfold ssInsert
      simp only [hsift, hstop, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
        List.getElem?_eq_getElem hk]
      rw [hX1, List.nil_append]
    rw [heq]
    have hgetT : ∀ i (j' : Fin n), ssGet (T.set q (some (r.1, idx))) i j' =
        if i = k ∧ j' = j then some (r.1, idx) else ssGet T i j' := by
      intro i j'
      rw [ssGet_set]
      by_cases h : i = k ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := h; rw [if_pos ⟨hq.symm, hqT⟩, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg h, if_neg (fun h' => h (ss_slot_eq h'.1))]
    have hold : SsLe T (T.set q (some (r.1, idx))) := by
      intro i j' e he
      rw [hgetT]
      by_cases h : i = k ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := h; rw [hempty] at he; simp at he
      · rw [if_neg h]; exact he
    have hlast : (es ++ vg)[idx]? = some r.1 := by
      have hll : loc.length = 1 + 2 * X.length := by
        rw [hloc, length_foldl_ssChain, List.length_singleton]
      have hidx' : idx = es.length + (vg.length - 1) := by rw [hidx, hpl, hvgl']; omega
      rw [List.getLast?_eq_getElem?] at hvgl
      rw [hidx', List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hvgl, hX2]
    refine ⟨⟨by simp [hlen], ⟨fun i j' e he => ?_⟩, ⟨es ++ vg, ?_, ?_⟩, ?_⟩, hold, ?_, Or.inr ?_⟩
    · -- well formed
      rw [hgetT] at he
      by_cases h : i = k ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := h
        rw [if_pos ⟨rfl, rfl⟩] at he
        cases he
        exact ⟨hk, hfix, rfl, by rw [hj]; exact hdiag⟩
      · rw [if_neg h] at he; exact hwf.slot _ _ _ he
    · simp only; rw [slpEntries_append, hes, Option.bind_some, hvg]
    · -- consistent
      intro i j' e he
      rw [hgetT] at he
      by_cases h : i = k ∧ j' = j
      · rw [if_pos h] at he; cases he; exact hlast
      · rw [if_neg h] at he
        have h1 := hcons _ _ _ he
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]
        exact h1
    · -- the length of the program
      simp only [List.length_append]
      have hfill : ssFill (T.set q (some (r.1, idx))) = ssFill T + 1 := by
        unfold ssFill
        rw [List.countP_set hqT]
        have : T[q] = none := by rw [List.getElem?_eq_getElem hqT] at hTq; simpa using hTq
        simp [this]
      rw [hfill, hloc, length_foldl_ssChain]
      simp only [List.length_singleton]
      have : X.length ≤ B.length := by simpa using hX3
      nlinarith
    · -- `g` sifts through now
      have := ssThru_of_stop (B := B) hold B.length 0 g [] (by omega) k hk
        (by simpa using hstop) ⟨idx, by simp only [List.drop_zero, ← hr]; rw [hgetT, if_pos ⟨rfl, rfl⟩]⟩
      simpa using this
    · unfold ssFill
      rw [List.countP_set hqT]
      have : T[q] = none := by rw [List.getElem?_eq_getElem hqT] at hTq; simpa using hTq
      simp [this]

end InsertSpec

end GI.Proved
