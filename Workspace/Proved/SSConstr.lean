module

public import Workspace.Proved.SSBuild

@[expose] public section

/-!
# A straight-line program for a member

Let the base contain every point. If `x` sifts through the table, the remainder fixes every
point, so it is `1`: `ssW es used * x = 1`, where `used` lists the program indices of the entries
used. So `x = (ssW es used)⁻¹`. The program `ssConstrProg` reaches it: after the program of the
table, it makes `1 = g₀⁻¹ g₀` from generator `0`, multiplies by the inverses of the used entries
(`ssChain`, as in insertion), and inverts the result (`ss_constr_reaches`).
-/

namespace GI.Proved

open Equiv GI.Cited

variable {n : ℕ}

/-- The local part: `1` from generator `0`, then the chain of `used`. -/
def ssConstrLoc (N : ℕ) (used : List ℕ) : List SlpInstr :=
  used.foldl (ssChain N) [.gen 0, .inv N, .mul (N + 1) N]

/-- The program for a member: the table program, the local part, and one inversion. -/
def ssConstrProg (prog : List SlpInstr) (used : List ℕ) : List SlpInstr :=
  prog ++ ssConstrLoc prog.length used ++
    [.inv (prog.length + (ssConstrLoc prog.length used).length - 1)]

theorem length_ssConstrLoc (N : ℕ) (used : List ℕ) :
    (ssConstrLoc N used).length = 3 + 2 * used.length := by
  unfold ssConstrLoc; rw [length_foldl_ssChain]; rfl

/-- **A member is reached.** -/
theorem ss_constr_reaches {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n}
    (hinv : SsInv B gs st) (hB : ∀ p, p ∈ B) (hgs : 0 < gs.length) {x : Perm (Fin n)}
    (hx : (ssSift B st.1 x).2.2 = 0) :
    SlpReaches gs (ssConstrProg st.2 (ssSift B st.1 x).2.1) x := by
  obtain ⟨es, hes, hcons⟩ := hinv.slp
  have hlen : es.length = st.2.length := by
    obtain ⟨v, rfl, hv⟩ := slpEntries_prefix _ _ _ hes
    simpa using hv
  rw [ssSift_eq] at hx ⊢
  obtain ⟨X, hX, hXv, -, hXl⟩ := ssSiftR_used hcons B 0 x []
  rw [List.nil_append] at hX
  rw [hX]
  -- the remainder is `1`
  have hfix := ssSiftR_stop_zero hinv.wf B.length 0 x [] (by simp) (by simp) hx
  have h1 : ssW es X * x = 1 := by
    rw [List.drop_zero] at hfix
    rw [← hXv]; ext p; rw [hfix p (hB p)]; rfl
  have hxv : x = (ssW es X)⁻¹ := eq_inv_of_mul_eq_one_right h1
  -- the start of the local part
  set N := st.2.length with hN
  set g0 := gs[0]'hgs with hg0
  have hloc0 : slpEntries gs [.gen 0, .inv N, .mul (N + 1) N] es =
      some (es ++ [g0, g0⁻¹, g0⁻¹ * g0]) := by
    simp [slpEntries, hgs, hlen, List.getElem?_append_right, hg0]
  obtain ⟨v, hv, hvl⟩ := ssChain_spec es X hXl _ _ (g0⁻¹ * g0) hloc0 (by simp)
  rw [inv_mul_cancel, mul_one] at hvl
  have hloc : slpEntries gs (ssConstrLoc N X) es = some (es ++ v) := by
    have e : ssChain N = ssChain es.length := by rw [hlen]
    unfold ssConstrLoc; rw [e]; exact hv
  obtain ⟨v', hv'1, hv'2⟩ := slpEntries_prefix _ _ _ hloc
  have hvv : v' = v := (List.append_cancel_left hv'1).symm
  subst hvv
  have hne : v' ≠ [] := by rintro rfl; simp at hvl
  have hpos := List.length_pos_of_ne_nil hne
  have hlast : (es ++ v')[N + (ssConstrLoc N X).length - 1]'(by simp; omega) = ssW es X := by
    rw [List.getElem_append_right (by omega)]
    rw [List.getLast?_eq_getElem?] at hvl
    have := (List.getElem?_eq_getElem (l := v') (i := v'.length - 1) (by omega)).symm.trans hvl
    simp only [Option.some.injEq] at this
    convert this using 2
    omega
  refine ⟨es ++ v' ++ [(ssW es X)⁻¹], ?_, by simp [hxv]⟩
  rw [show ssConstrProg st.2 X = st.2 ++ ssConstrLoc N X ++
    [.inv (N + (ssConstrLoc N X).length - 1)] from rfl]
  rw [slpEntries_append, slpEntries_append, hes, Option.bind_some, hloc, Option.bind_some,
    slpEntries_inv _ (by simp; omega), hlast]

/-- The length of the program for a member. -/
theorem length_ssConstrProg (prog : List SlpInstr) (used : List ℕ) :
    (ssConstrProg prog used).length = prog.length + 4 + 2 * used.length := by
  unfold ssConstrProg
  simp only [List.length_append, length_ssConstrLoc, List.length_singleton]
  omega

end GI.Proved
