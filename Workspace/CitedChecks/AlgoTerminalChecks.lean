module

public import Workspace.Cited.AlgoTerminal
public import Workspace.CitedChecks.AlgoDetermined

@[expose] public section

/-!
Independent checks: the three terminal encodings determine their instances. Bounded normal-form
existence and bounded constructive membership are not assumed or proved in this file.
-/
namespace GI.CitedChecks
open GI.Cited Equiv

private theorem fold_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Nat.zero_bits]
  | bit b n h ih => rw [Nat.bits_append_bit n b h]; simp [ih]

/-- Binary signs and magnitudes determine an integer, including zero. -/
theorem terminal_encInt_injective : Function.Injective encInt := by
  intro a b h
  simp only [encInt, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
  have hb : a.natAbs.bits = b.natAbs.bits := by
    apply List.map_injective_iff.mpr ?_ h.2
    intro x y hxy
    cases x <;> cases y <;> simp_all
  have ha : a.natAbs = b.natAbs := by
    simpa [fold_bits] using congrArg (fun bs => bs.foldr Nat.bit 0) hb
  have hab := Int.natAbs_eq_natAbs_iff.mp ha
  by_cases hna : a < 0 <;> by_cases hnb : b < 0 <;> simp_all <;> omega

/-- A matrix of fixed dimensions is determined by its row encoding. -/
theorem terminal_encIntMatrix_injective {r c : ℕ} :
    Function.Injective (encIntMatrix (r := r) (c := c)) := by
  intro A B h
  have hr := List.map_inj_left.mp (detm_list_inj h)
  ext i j
  have hc := List.map_inj_left.mp (detm_list_inj (hr i (List.mem_finRange i)))
  exact terminal_encInt_injective (hc j (List.mem_finRange j))

/-- The Hermite input determines all data fields. -/
theorem terminal_fullRank_determined (I J : FullRankInst)
    (h : fullRankInput I = fullRankInput J) : I = J := by
  obtain ⟨r, c, hp, hl, A, hi⟩ := I
  obtain ⟨r', c', hp', hl', A', hi'⟩ := J
  simp only [fullRankInput, Val.list.injEq, List.cons.injEq, Val.nat.injEq,
    and_true] at h
  obtain ⟨rfl, rfl, h⟩ := h
  obtain rfl := terminal_encIntMatrix_injective h
  rfl

/-- The Smith input determines all data fields. -/
theorem terminal_nonsingular_determined (I J : NonsingularInst)
    (h : nonsingularInput I = nonsingularInput J) : I = J := by
  obtain ⟨n, hp, A, hi⟩ := I
  obtain ⟨n', hp', A', hi'⟩ := J
  simp only [nonsingularInput, Val.list.injEq, List.cons.injEq, Val.nat.injEq,
    and_true] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl := terminal_encIntMatrix_injective h
  rfl

/-- The constructive-membership input determines the instance. The promise `mem` is a proof, so it
is determined by the rest. -/
theorem terminal_member_determined (I J : KnownMemberInst)
    (h : knownMemberInput I = knownMemberInput J) : I = J := by
  obtain ⟨n, gs, x, hx⟩ := I
  obtain ⟨n', gs', x', hx'⟩ := J
  have := detm_memberInst ⟨n, gs, x⟩ ⟨n', gs', x'⟩ h
  simp only [MemberInst.mk.injEq] at this
  obtain ⟨rfl, hg, hx⟩ := this
  cases hg; cases hx; rfl

/-- Every entry of a successful evaluation belongs to the generated subgroup. -/
theorem terminal_slpEntries_mem {n : ℕ} (gs : List (Perm (Fin n)))
    (prog : List SlpInstr) (acc es : List (Perm (Fin n)))
    (hacc : ∀ g ∈ acc, g ∈ gens gs)
    (h : slpEntries gs prog acc = some es) : ∀ g ∈ es, g ∈ gens gs := by
  induction prog generalizing acc with
  | nil => cases h; exact hacc
  | cons ins prog ih =>
    have next_mem : ∀ g, (match ins with
        | .gen i => gs[i]?
        | .inv j => acc[j]?.map (·⁻¹)
        | .mul j k => do let a ← acc[j]?; let b ← acc[k]?; pure (a * b)) = some g →
        g ∈ gens gs := by
      intro g hg
      cases ins with
      | gen i => exact Subgroup.subset_closure (List.mem_of_getElem? hg)
      | inv j =>
        cases hj : acc[j]? with
        | none => simp [hj] at hg
        | some a =>
          simp [hj] at hg
          subst g
          exact (gens gs).inv_mem (hacc a (List.mem_of_getElem? hj))
      | mul j k =>
        cases hj : acc[j]? with
        | none => simp [hj] at hg
        | some a =>
          cases hk : acc[k]? with
          | none => simp [hj, hk] at hg
          | some b =>
            simp [hj, hk] at hg
            subst g
            exact (gens gs).mul_mem (hacc a (List.mem_of_getElem? hj))
              (hacc b (List.mem_of_getElem? hk))
    simp only [slpEntries] at h
    split at h
    · contradiction
    · rename_i g hg
      apply ih (acc ++ [g])
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hacc a ha
        · obtain rfl := List.mem_singleton.mp ha
          exact next_mem _ hg
      · exact h

/-- A successful program cannot accept a nonmember. -/
theorem terminal_slpReaches_mem {n : ℕ} {gs : List (Perm (Fin n))}
    {prog : List SlpInstr} {x : Perm (Fin n)} (h : SlpReaches gs prog x) : x ∈ gens gs := by
  obtain ⟨es, he, rfl⟩ := h
  have hm := terminal_slpEntries_mem gs prog [] es (by simp) he
  cases hl : es.getLast? with
  | none => simp
  | some a =>
    simp
    exact hm a (List.mem_of_getLast? hl)

/-- The empty program reaches exactly the identity, even for an empty generator list. -/
theorem terminal_empty_reaches {n : ℕ} (gs : List (Perm (Fin n))) (x : Perm (Fin n)) :
    SlpReaches gs [] x ↔ x = 1 := by
  simp [SlpReaches, slpEntries, eq_comm]

/-- An invalid reference in the first instruction is rejected. -/
theorem terminal_first_inverse_invalid {n : ℕ} (gs : List (Perm (Fin n)))
    (j : ℕ) (prog : List SlpInstr) : slpEntries gs (.inv j :: prog) [] = none := by
  simp [slpEntries]

/-- The form of constructive membership with both answers: output `0` if `x ∉ ⟨gs⟩`, and
otherwise `[1, prog]`. This was the cited task before it was narrowed to known members. -/
def ConstructiveMembershipFullTask (d : ℕ) : GI.Cited.Task MemberInst :=
  Task.ofVal memberInput
    (fun I v => (v = .nat 0 ∧ I.x ∉ gens I.gs) ∨
      ∃ prog : List SlpInstr, v = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
        prog.length ≤ (memberInput I).cells.length ^ d ∧ SlpReaches I.gs prog I.x)

/-- **The narrowed task is weaker.** A program for the form with both answers also solves the task
on known members, with the same exponent and the same time bound. On a member the answer `0` is
excluded, so the output is a program. -/
theorem constructiveMembership_of_full (d : ℕ) (p : GI.Machine.Program)
    (h : PolyTimeAt (ConstructiveMembershipFullTask d) p) :
    PolyTimeAt (ConstructiveMembershipTask d) p := by
  obtain ⟨c, k, hp⟩ := h
  refine ⟨c, k, fun I b mem hI => ?_⟩
  obtain ⟨fuel, o, st, cost, hex, hlow, hb, ⟨v, hv, hc⟩, hcost⟩ :=
    hp ⟨I.n, I.gs, I.x⟩ b mem hI
  refine ⟨fuel, o, st, cost, hex, hlow, hb, ⟨v, hv, ?_⟩, hcost⟩
  rcases hc with ⟨_, hn⟩ | hprog
  · exact (hn I.mem).elim
  · exact hprog

/-- The form with both answers implies the cited one. -/
theorem constructiveMembership_of_full' (h : ∃ d p, PolyTimeAt (ConstructiveMembershipFullTask d) p) :
    ConstructiveMembership := by
  obtain ⟨d, p, hp⟩ := h
  exact ⟨d, p, constructiveMembership_of_full d p hp⟩

end GI.CitedChecks
