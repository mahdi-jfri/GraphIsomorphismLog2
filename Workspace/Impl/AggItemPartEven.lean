module

public import Workspace.Impl.AggItemPartGen

@[expose] public section

/-!
# Case 1: the even part, the sign by inversions, and the orbit partition

* `itp_schreier`: **Schreier's lemma for index two.** If `S` generates `G` and `t ∈ G` is an odd
  involution, the list `itpSch t S` (for even `s`: `s` and `t s t`; for odd `s`: `s t` and `t s`)
  generates the even part `G ⊓ Alt`. The cosets of the even part are `1` and `t`; the proof goes
  along a word in `S` and keeps the invariant "`g` is in the closure if even, `g t` is if odd".
* `itp_sign_one_iff`: a permutation of `Fin q` is even exactly when its number of inversions is
  even, so a program can find the parity by counting.
* `itp_evenStab_map`: the even stabilizer of `labelOrbitPart`, as permutations, is the
  stabilizer meet the alternating group.
* `itpPart_eq`: for orbit labels, `labelOrbitPart` is the partition of the labeling.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset

variable {q : ℕ}

/-! ### Schreier's lemma for index two -/

/-- The Schreier generators for the transversal `{1, t}` of the even part. -/
def itpSch (t : Perm (Fin q)) (S : List (Perm (Fin q))) : List (Perm (Fin q)) :=
  S.flatMap fun s => if sign s = 1 then [s, t * s * t] else [s * t, t * s]

theorem itp_mem_sch {t g : Perm (Fin q)} {S : List (Perm (Fin q))} :
    g ∈ itpSch t S ↔ ∃ s ∈ S, (sign s = 1 ∧ (g = s ∨ g = t * s * t)) ∨
      (sign s ≠ 1 ∧ (g = s * t ∨ g = t * s)) := by
  simp only [itpSch, List.mem_flatMap]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  split_ifs with h <;> simp [h]

theorem itp_sign_cases (g : Perm (Fin q)) : sign g = 1 ∨ sign g = -1 := Int.units_eq_one_or _

/-- **Schreier's lemma for index two.** -/
theorem itp_schreier {t : Perm (Fin q)} {S : List (Perm (Fin q))}
    (ht : t ∈ Subgroup.closure {s | s ∈ S}) (htt : t * t = 1) (hst : sign t = -1) :
    Subgroup.closure {g | g ∈ itpSch t S} =
      Subgroup.closure {s | s ∈ S} ⊓ alternatingGroup (Fin q) := by
  set K := Subgroup.closure {g | g ∈ itpSch t S}
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have tt : ∀ y : Perm (Fin q), y * t * t = y := fun y => by rw [mul_assoc, htt, mul_one]
  refine le_antisymm ((Subgroup.closure_le _).2 fun g hg => ?_) fun g ⟨hg, hgA⟩ => ?_
  · obtain ⟨s, hs, h⟩ := itp_mem_sch.1 hg
    have hsG : s ∈ Subgroup.closure {s | s ∈ S} := Subgroup.subset_closure hs
    have hss := itp_sign_cases s
    rcases h with ⟨h1, rfl | rfl⟩ | ⟨h1, rfl | rfl⟩
    · exact ⟨hsG, h1⟩
    · refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hsG) ht, ?_⟩
      show sign _ = 1
      rw [Perm.sign_mul, Perm.sign_mul, h1, hst]; decide
    · refine ⟨Subgroup.mul_mem _ hsG ht, ?_⟩
      show sign _ = 1
      rw [Perm.sign_mul, hss.resolve_left h1, hst]; decide
    · refine ⟨Subgroup.mul_mem _ ht hsG, ?_⟩
      show sign _ = 1
      rw [Perm.sign_mul, hss.resolve_left h1, hst]; decide
  · have hK : ∀ s ∈ S, (sign s = 1 → s ∈ K ∧ t * s * t ∈ K) ∧
        (sign s = -1 → s * t ∈ K ∧ t * s ∈ K) := by
      intro s hs
      have mem : ∀ g, g ∈ itpSch t S → g ∈ K := fun g h => Subgroup.subset_closure h
      refine ⟨fun h1 => ⟨mem _ (itp_mem_sch.2 ⟨s, hs, Or.inl ⟨h1, Or.inl rfl⟩⟩),
        mem _ (itp_mem_sch.2 ⟨s, hs, Or.inl ⟨h1, Or.inr rfl⟩⟩)⟩, fun h1 => ?_⟩
      have h1' : sign s ≠ 1 := by rw [h1]; decide
      exact ⟨mem _ (itp_mem_sch.2 ⟨s, hs, Or.inr ⟨h1', Or.inl rfl⟩⟩),
        mem _ (itp_mem_sch.2 ⟨s, hs, Or.inr ⟨h1', Or.inr rfl⟩⟩)⟩
    -- the invariant along words in `S`
    have key : ∀ x ∈ Subgroup.closure {s | s ∈ S},
        (sign x = 1 → x ∈ K) ∧ (sign x = -1 → x * t ∈ K) := by
      intro x hx
      induction hx using Subgroup.closure_induction_right with
      | one => exact ⟨fun _ => K.one_mem, fun h => by rw [Perm.sign_one] at h; exact absurd h (by decide)⟩
      | mul_right x _ s hs ih =>
        obtain ⟨hs1, hs2⟩ := hK s hs
        rcases itp_sign_cases x with hx | hx <;> rcases itp_sign_cases s with h | h
        · refine ⟨fun _ => K.mul_mem (ih.1 hx) (hs1 h).1, fun h' => ?_⟩
          rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
          · rw [mul_assoc]; exact K.mul_mem (ih.1 hx) (hs2 h).1
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
          · rw [show x * s * t = x * t * (t * s * t) by
              simp only [← mul_assoc, tt]]
            exact K.mul_mem (ih.2 hx) (hs1 h).2
        · refine ⟨fun _ => ?_, fun h' => ?_⟩
          · rw [show x * s = x * t * (t * s) by
              simp only [← mul_assoc, tt]]
            exact K.mul_mem (ih.2 hx) (hs2 h).2
          · rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
      | mul_inv_cancel x _ s hs ih =>
        obtain ⟨hs1, hs2⟩ := hK s hs
        rcases itp_sign_cases x with hx | hx <;> rcases itp_sign_cases s with h | h
        · refine ⟨fun _ => K.mul_mem (ih.1 hx) (K.inv_mem (hs1 h).1), fun h' => ?_⟩
          rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
          · rw [show x * s⁻¹ * t = x * (t * s)⁻¹ by
              simp only [mul_inv_rev, hti, ← mul_assoc]]
            exact K.mul_mem (ih.1 hx) (K.inv_mem (hs2 h).2)
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
          · rw [show x * s⁻¹ * t = x * t * (t * s * t)⁻¹ by
              simp only [mul_inv_rev, hti, ← mul_assoc, tt]]
            exact K.mul_mem (ih.2 hx) (K.inv_mem (hs1 h).2)
        · refine ⟨fun _ => ?_, fun h' => ?_⟩
          · rw [show x * s⁻¹ = x * t * (s * t)⁻¹ by
              simp only [mul_inv_rev, hti, ← mul_assoc, tt]]
            exact K.mul_mem (ih.2 hx) (K.inv_mem (hs2 h).1)
          · rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
    exact (key g hg).1 hgA

/-! ### The sign by inversions -/

/-- The number of inversions: pairs `b < a` with `σ a < σ b`. -/
def itpNInv (σ : Perm (Fin q)) : ℕ := ∑ a : Fin q, (univ.filter fun b => b < a ∧ σ a < σ b).card

theorem itp_sign_eq_signAux (σ : Perm (Fin q)) : sign σ = signAux σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [Perm.sign_one, signAux_one]
  | swap_mul f x y hxy ih => rw [Perm.sign_mul, signAux_mul, ih, sign_swap hxy, signAux_swap hxy]

/-- The inversions counted by `signAux`. -/
theorem itp_card_inv (σ : Perm (Fin q)) :
    ((finPairsLT q).filter fun x => σ x.1 ≤ σ x.2).card = itpNInv σ := by
  classical
  rw [itpNInv, ← Finset.card_sigma]
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and, mem_finPairsLT]
  constructor
  · rintro ⟨hlt, hle⟩
    exact ⟨hlt, lt_of_le_of_ne hle (fun e => (ne_of_lt hlt) (σ.injective e).symm)⟩
  · rintro ⟨hlt, hlt'⟩
    exact ⟨hlt, hlt'.le⟩

/-- **The sign by inversions**: a permutation is even exactly when it has an even number of
inversions. -/
theorem itp_sign_one_iff (σ : Perm (Fin q)) : sign σ = 1 ↔ Even (itpNInv σ) := by
  classical
  rw [itp_sign_eq_signAux, signAux, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const, itp_card_inv, neg_one_pow_eq_one_iff_even (by decide)]

/-! ### The even stabilizer and the orbit partition -/

/-- The even stabilizer, as a group of permutations. -/
theorem itp_evenStab_map {Z : Type*} [MulAction (Perm (Fin q)) Z] (z : Z) :
    (evenStab (q := q) z).map (alternatingGroup (Fin q)).subtype =
      MulAction.stabilizer (Perm (Fin q)) z ⊓ alternatingGroup (Fin q) := by
  ext g
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨he, e.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨g, h2⟩, h1, rfl⟩

/-- **For orbit labels, the colored orbit partition is the partition of the labeling.** -/
theorem itpPart_eq {gs : List (Perm (Fin q))} {H : Subgroup (Perm (Fin q))} {lab : Fin q → ℕ}
    (hH : GI.Cited.gens gs = H) (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit gs x) :
    labelOrbitPart H = itpPart lab := by
  classical
  have h1 : ∀ b, lorb H b = itpBlk lab b := by
    intro b
    ext y
    simp only [lorb, itpBlk, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [eq_comm, hlab, mem_genOrbit]
    change (∃ h ∈ H, h b = y) ↔ ∃ g ∈ GI.Cited.gens gs, g b = y
    rw [hH]
  ext a b
  · simp only [labelOrbitPart, itpPart, h1]
  · simp only [labelOrbitPart, itpPart, h1]

end GI.Impl
