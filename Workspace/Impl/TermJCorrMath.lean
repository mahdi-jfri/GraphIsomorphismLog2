module

public import Workspace.Impl.TermJLabTr

@[expose] public section

/-!
# The correcting element of the zero-sum route

Proof of Theorem A.23: the possible local transporter images are the cosets
`α_{y,σ(i)} - α_{x,i} + B_{a_i}`; "their sum can be zero exactly when the totals agree … If any
type repeats, exchanging two equal-type matches reverses parity without changing the possible
sum." For `u = z⁻¹ g` the program solves `∏_k φ(g_k)^{c_k} = lab(u)` and, when the top of `u` is
odd, multiplies by the first lifted transposition. `tmJCorrE` is the result and
`tmJ_corrE_spec` its properties. `tmJ_lab_range` and `tmJ_odd_ne` show that a solution exists
whenever some element of `Aut_{N≀Sym}(X)` has the label and the top sign of `u`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Multicoset

variable {B : Type} [Nonempty B] {q : ℕ} {N : Subgroup (Perm B)} {A : Type*} [CommGroup A]
  {φ : N →* A} {C : Type} {x : Fin q → B → C}

theorem tmJLabOf_lam {lg : List (Fin q × Perm B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (c : Fin lg.length → ℤ) : tmJLabOf φ (tmJLam lg c) = tmJSumT N φ lg c := by
  have hd : ∀ i, tmJLamD lg c i ∈ N := by
    intro i
    unfold tmJLamD
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    split_ifs
    · exact N.zpow_mem (hlg k) _
    · exact N.one_mem
  unfold tmJLam
  rw [tmJLabOf_tmJP (p := (tmJLamD lg c, 1)) hd]
  unfold tmJLab
  simp_rw [phiT_lamD hlg]
  exact tmJSum_prod lg c

theorem tmJ_lam_aut {lg : List (Fin q × Perm B)}
    (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ tmJRowAut N (x (lg.get k).1))
    (c : Fin lg.length → ℤ) : tmJLam lg c ∈ tmJW N ⊓ tmJStab (tmJStr x) := by
  have hd := tmJLamD_mem hlg c
  exact ⟨⟨_, fun i => (hd i).1, rfl⟩, (tmJ_mem_iso x x (tmJLamD lg c, 1)).2 fun i => (hd i).2⟩

theorem tmJSumT_add (lg : List (Fin q × Perm B)) (e e' : Fin lg.length → ℤ) :
    tmJSumT N φ lg (e + e') = tmJSumT N φ lg e * tmJSumT N φ lg e' := by
  unfold tmJSumT
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by simp [zpow_add]

theorem tmJSumT_neg (lg : List (Fin q × Perm B)) (e : Fin lg.length → ℤ) :
    tmJSumT N φ lg (-e) = (tmJSumT N φ lg e)⁻¹ := by
  unfold tmJSumT
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun k _ => by simp [zpow_neg]

theorem tmJSumT_single (lg : List (Fin q × Perm B)) (k : Fin lg.length) :
    tmJSumT N φ lg (Pi.single k 1) = phiT N φ (lg.get k).2 := by
  classical
  unfold tmJSumT
  rw [Finset.prod_eq_single k]
  · simp
  · intro k' _ hk; simp [Pi.single_eq_of_ne hk]
  · simp

/-- **The labels of `Aut_{N≀Sym}(X)` are values of the sum map.** -/
theorem tmJ_lab_range {lg : List (Fin q × Perm B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    {Tl : List (Fin q × Fin q × Perm B)} (hTl : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ N)
    {σ : Perm (B × Fin q)} (hσ : σ ∈ Subgroup.closure ({σ | ∃ ag ∈ lg, σ = tmJLoc ag.1 ag.2} ∪
      {σ | ∃ t ∈ Tl, σ = tmJSw t.1 t.2.1 t.2.2})) :
    ∃ e, tmJLabOf φ σ = tmJSumT N φ lg e := by
  have hW : Subgroup.closure ({σ | ∃ ag ∈ lg, σ = tmJLoc ag.1 ag.2} ∪
      {σ | ∃ t ∈ Tl, σ = tmJSw t.1 t.2.1 t.2.2}) ≤ tmJW N := by
    rw [Subgroup.closure_le]
    rintro σ (⟨ag, hag, rfl⟩ | ⟨t, ht, rfl⟩)
    · obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hag
      refine ⟨(Pi.mulSingle (lg.get k).1 (lg.get k).2, 1), fun i => ?_, rfl⟩
      show (Pi.mulSingle (lg.get k).1 (lg.get k).2 : Fin q → Perm B) i ∈ N
      by_cases hi : i = (lg.get k).1
      · subst hi; simpa using hlg k
      · rw [Pi.mulSingle_eq_of_ne hi]; exact N.one_mem
    · exact tmJSw_mem (hTl t ht).2
  induction hσ using Subgroup.closure_induction with
  | mem σ h =>
    rcases h with ⟨ag, hag, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hag
      refine ⟨Pi.single k 1, ?_⟩
      have hd : ∀ i, (Pi.mulSingle (lg.get k).1 (lg.get k).2 : Fin q → Perm B) i ∈ N := by
        intro i
        by_cases hi : i = (lg.get k).1
        · subst hi; simpa using hlg k
        · rw [Pi.mulSingle_eq_of_ne hi]; exact N.one_mem
      rw [tmJSumT_single, tmJLoc, tmJLabOf_tmJP (p := (Pi.mulSingle _ _, 1)) hd, tmJLab_loc]
    · exact ⟨0, by
        rw [tmJLabOf_sw (hTl t ht).1 (hTl t ht).2]
        unfold tmJSumT; simp⟩
  | one =>
    refine ⟨0, ?_⟩
    rw [tmJLabOf, dif_pos (tmJW N).one_mem]
    rw [show tmJLabHom φ (q := q) ⟨1, (tmJW N).one_mem⟩ = 1 from map_one _]
    unfold tmJSumT; simp
  | mul σ τ hσ hτ ihσ ihτ =>
    obtain ⟨e, he⟩ := ihσ
    obtain ⟨e', he'⟩ := ihτ
    exact ⟨e + e', by rw [tmJLabOf_mul (hW hσ) (hW hτ), he, he', tmJSumT_add]⟩
  | inv σ hσ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨-e, by rw [tmJLabOf_inv (hW hσ), he, tmJSumT_neg]⟩

/-- **Odd tops need a transposition.** -/
theorem tmJ_odd_ne {L0 : Set (Perm (B × Fin q))} (h0 : ∀ σ ∈ L0, σ ∈ tmJW N ∧ tmJTop N σ = 1)
    {Tl : List (Fin q × Fin q × Perm B)} (hTl : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ N)
    {σ : Perm (B × Fin q)} (hσ : σ ∈ Subgroup.closure (L0 ∪
      {σ | ∃ t ∈ Tl, σ = tmJSw t.1 t.2.1 t.2.2})) (hodd : sign (tmJTop N σ) = -1) : Tl ≠ [] := by
  rintro rfl
  obtain ⟨w, hw, hwt⟩ := tmJ_top_match h0 (by rintro σ ⟨t, ht, -⟩; simp at ht) hσ
  have : {σ | ∃ t ∈ ([] : List (Fin q × Fin q × Perm B)), σ = tmJSw t.1 t.2.1 t.2.2} = ∅ := by
    ext σ; simp
  rw [this, Subgroup.closure_empty, Subgroup.mem_bot] at hw
  subst hw
  rw [← hwt, tmJTop, dif_pos (tmJW N).one_mem] at hodd
  rw [show tmJTopHom (N := N) (q := q) ⟨1, _⟩ = 1 from map_one _, Perm.sign_one] at hodd
  exact absurd hodd (by decide)

/-- The first lifted transposition, or `1`. -/
def tmJSw0 (Tl : List (Fin q × Fin q × Perm B)) : Perm (B × Fin q) :=
  match Tl with
  | [] => 1
  | t :: _ => tmJSw t.1 t.2.1 t.2.2

/-- **The correcting element**: the first lifted transposition if the top is odd, times the
local product of the solution `c`. -/
def tmJCorrE (Tl : List (Fin q × Fin q × Perm B)) (odd : Bool) (lg : List (Fin q × Perm B))
    (c : Fin lg.length → ℤ) : Perm (B × Fin q) :=
  (if odd then tmJSw0 Tl else 1) * tmJLam lg c

theorem tmJ_corrE_spec {Tl : List (Fin q × Fin q × Perm B)}
    (hTl : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ N ∧ x t.1 ∘ t.2.2 = x t.2.1)
    {lg : List (Fin q × Perm B)}
    (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ tmJRowAut N (x (lg.get k).1))
    (odd : Bool) (hne : odd = true → Tl ≠ []) (c : Fin lg.length → ℤ) :
    ∃ h : tmJCorrE Tl odd lg c ∈ tmJW N ⊓ tmJStab (tmJStr x),
      tmJLabOf φ (tmJCorrE Tl odd lg c) = tmJSumT N φ lg c ∧
      sign (tmJTop N (tmJCorrE Tl odd lg c)) = if odd then -1 else 1 := by
  have hlam := tmJ_lam_aut hlg c
  have hlgN : ∀ k : Fin lg.length, (lg.get k).2 ∈ N := fun k => (hlg k).1
  have hlamt : tmJTop N (tmJLam lg c) = 1 := by
    have hd := tmJLamD_mem hlg c
    exact tmJTop_tmJP (p := (tmJLamD lg c, 1)) fun i => (hd i).1
  have hs0 : odd = true → tmJSw0 Tl ∈ tmJW N ⊓ tmJStab (tmJStr x) ∧
      tmJLabOf φ (tmJSw0 Tl) = 1 ∧ sign (tmJTop N (tmJSw0 Tl)) = -1 := by
    intro ho
    cases Tl with
    | nil => exact absurd rfl (hne ho)
    | cons t Tr =>
      obtain ⟨h1, h2, h3⟩ := hTl t List.mem_cons_self
      have hm : tmJSw t.1 t.2.1 t.2.2 ∈ tmJW N ⊓ tmJStab (tmJStr x) := by
        refine ⟨tmJSw_mem h2, (tmJ_mem_iso x x _).2 fun i => ?_⟩
        simp only [tmJSwD, Function.update_apply]
        split_ifs with hi
        · subst hi
          rw [swap_apply_right, ← h3]
          funext c; simp
        · by_cases hi' : i = t.1
          · subst hi'; simpa [swap_apply_left] using h3
          · simp [Pi.mulSingle_eq_of_ne hi', swap_apply_of_ne_of_ne hi' hi]
      exact ⟨hm, tmJLabOf_sw h1 h2, by
        change sign (tmJTop N (tmJSw t.1 t.2.1 t.2.2)) = -1
        rw [tmJTop_sw h2, sign_swap h1]⟩
  unfold tmJCorrE
  cases odd with
  | false =>
    simp only [Bool.false_eq_true, if_false, one_mul]
    exact ⟨hlam, tmJLabOf_lam hlgN c, by rw [hlamt, Perm.sign_one]⟩
  | true =>
    simp only [if_true]
    obtain ⟨m1, l1, s1⟩ := hs0 rfl
    refine ⟨⟨(tmJW N).mul_mem m1.1 hlam.1, (tmJStab _).mul_mem m1.2 hlam.2⟩, ?_, ?_⟩
    · rw [tmJLabOf_mul m1.1 hlam.1, l1, one_mul, tmJLabOf_lam hlgN c]
    · rw [tmJTop_mul m1.1 hlam.1, hlamt, mul_one, s1]

end GI.Impl
