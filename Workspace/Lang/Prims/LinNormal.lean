import Workspace.Lang.Prims.Other
import Workspace.Cited.AlgoTerminal
import Mathlib.Data.Nat.Size

/-! The A.20 normal-form tasks as hypothesis-dependent primitives.
They use only the two tasks `HermiteFullRank` and `SmithNonsingular`.
Bounds include writing the integer entries in binary. -/
namespace GI.Lang
open GI.Cited GI.Machine

/-- Uniform list-weight estimate. -/
theorem linWtList {vs : List Val} {B : ℕ} (h : ∀ v ∈ vs, v.wt ≤ B) :
    (Val.list vs).wt ≤ 2 * (vs.length * B) + vs.length + 4 := by
  have hs : (vs.map Val.wt).sum ≤ vs.length * B := by
    induction vs with
    | nil => simp
    | cons v vs ih =>
      have hv := h v (by simp)
      have ht := ih (fun w hw => h w (by simp [hw]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  exact (wt_list_le vs).trans (by omega)

/-- Binary integer encodings have weight linear in the bit bound. -/
theorem linWtInt {B : ℕ} {z : ℤ} (hz : z.natAbs < 2 ^ B) :
    (encInt z).wt ≤ 20 * (B + 1) := by
  have hl : z.natAbs.bits.length ≤ B := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hz
  have hd : ∀ b : Bool, (Val.nat (if b then 1 else 0)).wt ≤ 3 := by
    intro b; cases b <;> decide
  have hb := linWtList (vs := z.natAbs.bits.map fun b => .nat (if b then 1 else 0))
    (B := 3) (by intro v hv; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv; exact hd b)
  have hs : (Val.nat (if z < 0 then 1 else 0)).wt ≤ 3 := by
    split_ifs <;> decide
  have h := wt_list2_le (.nat (if z < 0 then 1 else 0))
    (.list (z.natAbs.bits.map fun b => .nat (if b then 1 else 0)))
  simp only [List.length_map] at hb
  unfold encInt
  omega

/-- Polynomial weight bound for a matrix with B-bit entries. -/
def linMatrixWt (r c B : ℕ) : ℕ :=
  2 * (r * (2 * (c * (20 * (B + 1))) + c + 4)) + r + 4

theorem linWtMatrix {r c B : ℕ} {A : Matrix (Fin r) (Fin c) ℤ}
    (hA : EntriesBits B A) : (encIntMatrix A).wt ≤ linMatrixWt r c B := by
  unfold encIntMatrix linMatrixWt
  apply (linWtList (B := 2 * (c * (20 * (B + 1))) + c + 4) ?_).trans
  · simp
  intro v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  have h := linWtList (vs := (List.finRange c).map fun j => encInt (A i j))
    (B := 20 * (B + 1)) (by
      intro w hw
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw
      exact linWtInt (hA i j))
  simpa using h

/-- The uniform output exponent supplied by the Hermite hypothesis. -/
noncomputable def linHermiteDegree (h : HermiteFullRank) : ℕ := h.choose
/-- Only the full-column-rank Hermite task is used. -/
noncomputable def linHermitePrim (h : HermiteFullRank) : Prim :=
  Prim.ofHyp _ _ h.choose_spec

/-- Hermite output, including the source's entry-bit bounds. -/
def linHermiteOut (d : ℕ) (I : FullRankInst) (v : Val) : Prop :=
  ∃ (U : Matrix (Fin I.r) (Fin I.r) ℤ) (H : Matrix (Fin I.r) (Fin I.c) ℤ),
    v = .list [encIntMatrix U, encIntMatrix H] ∧ IsUnit U.det ∧ U * I.A = H ∧
    IsHermiteForm H ∧ EntriesBits ((fullRankInput I).cells.length ^ d) U ∧
    EntriesBits ((fullRankInput I).cells.length ^ d) H

/-- Polynomial output-writing bound for the Hermite call. -/
def linHermiteWt (d : ℕ) (I : FullRankInst) : ℕ :=
  2 * (linMatrixWt I.r I.r ((fullRankInput I).cells.length ^ d) +
    linMatrixWt I.r I.c ((fullRankInput I).cells.length ^ d)) + 6

theorem linHermiteOut_wt {d : ℕ} {I : FullRankInst} {v : Val}
    (hv : linHermiteOut d I v) : v.wt ≤ linHermiteWt d I := by
  obtain ⟨U, H, rfl, _, _, _, hU, hH⟩ := hv
  have := wt_list2_le (encIntMatrix U) (encIntMatrix H)
  have := linWtMatrix hU
  have := linWtMatrix hH
  unfold linHermiteWt
  omega

theorem linHermitePrim_spec (h : HermiteFullRank) (I : FullRankInst) :
    PrimSpec (linHermitePrim h) (fullRankInput I) (linHermiteOut (linHermiteDegree h) I) := by
  apply Prim.ofHyp_spec h.choose_spec I
  obtain ⟨r, c, hc, hcr, A, hr⟩ := I
  rintro ⟨r', c', hc', hcr', A', hr'⟩ he
  simp only [fullRankInput, Val.list.injEq, List.cons.injEq, Val.nat.injEq,
    and_true] at he
  obtain ⟨rfl, rfl, he⟩ := he
  obtain rfl := encIntMatrix_injective he
  rfl

/-- The uniform output exponent supplied by the Smith hypothesis. -/
noncomputable def linSmithDegree (h : SmithNonsingular) : ℕ := h.choose
/-- The Smith primitive accepts square nonsingular input only. -/
noncomputable def linSmithPrim (h : SmithNonsingular) : Prim :=
  Prim.ofHyp _ _ h.choose_spec

def linSmithOut (d : ℕ) (I : NonsingularInst) (v : Val) : Prop :=
  ∃ (U V D : Matrix (Fin I.n) (Fin I.n) ℤ),
    v = .list [encIntMatrix U, encIntMatrix D, encIntMatrix V] ∧
    IsUnit U.det ∧ IsUnit V.det ∧ U * I.A * V = D ∧ IsSmithForm D ∧
    EntriesBits ((nonsingularInput I).cells.length ^ d) U ∧
    EntriesBits ((nonsingularInput I).cells.length ^ d) D ∧
    EntriesBits ((nonsingularInput I).cells.length ^ d) V

def linSmithWt (d : ℕ) (I : NonsingularInst) : ℕ :=
  6 * linMatrixWt I.n I.n ((nonsingularInput I).cells.length ^ d) + 7

theorem linSmithOut_wt {d : ℕ} {I : NonsingularInst} {v : Val}
    (hv : linSmithOut d I v) : v.wt ≤ linSmithWt d I := by
  obtain ⟨U, V, D, rfl, _, _, _, _, hU, hD, hV⟩ := hv
  have := wt_list3_le (encIntMatrix U) (encIntMatrix D) (encIntMatrix V)
  have := linWtMatrix hU
  have := linWtMatrix hD
  have := linWtMatrix hV
  unfold linSmithWt
  omega

theorem linSmithPrim_spec (h : SmithNonsingular) (I : NonsingularInst) :
    PrimSpec (linSmithPrim h) (nonsingularInput I) (linSmithOut (linSmithDegree h) I) := by
  apply Prim.ofHyp_spec h.choose_spec I
  obtain ⟨n, hn, A, hA⟩ := I
  rintro ⟨n', hn', A', hA'⟩ he
  simp only [nonsingularInput, Val.list.injEq, List.cons.injEq, Val.nat.injEq,
    and_true] at he
  obtain ⟨rfl, he⟩ := he
  obtain rfl := encIntMatrix_injective he
  rfl

end GI.Lang
