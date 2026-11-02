import Workspace.Impl.TermRepsMath
import Workspace.Impl.FreshPrep

/-!
# A loop over a growing list (T3)

The coset enumeration processes the listed representatives in turn while the list grows. The
library loop (`forBody`) needs its number of rounds in advance, and that number is the index
`[H : R]`, which the program does not know. So we use a loop that stops when the counter
reaches the length of the list: `tmRpWhileF self st` on `[c, i, acc]` calls the step `st` on
`[c, i, acc]` and itself on `[c, i + 1, acc']` while `i < |acc|`, and returns `acc` otherwise.

`tmRpWhile_spec` describes it by an invariant `Inv i l` that bounds the length of the list by
`K`. The number of rounds is at most `K + 1 - i₀`, and each round pays the step plus a term
linear in the weights.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

/-- **The loop body**, at index `self`, with step function `st`. -/
def tmRpWhileF (self st : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.length (arg 2)))
    (.call self (mk3 (arg 0) (.arith .add (arg 1) (.nat 1))
      (.call st (mk3 (arg 0) (arg 1) (arg 2)))))
    (arg 2)

/-- The overhead of one round of the loop. -/
def tmRpWK : ℕ := 100

/-- **The loop over a growing list.** -/
theorem tmRpWhile_spec {P : Program} {self st : ℕ}
    (hself : P.funs[self]? = some (tmRpWhileF self st)) {c : Val}
    {Inv : ℕ → List Val → Prop} {K M D : ℕ}
    (hK : ∀ i l, Inv i l → i ≤ l.length ∧ l.length ≤ K)
    (hM : ∀ i l, Inv i l → (Val.list l).wt ≤ M)
    (hstep : ∀ i l, Inv i l → i < l.length → FunAll P st (.list [c, .nat i, .list l])
      (fun w cb => ∃ l', w = .list l' ∧ Inv (i + 1) l' ∧ cb ≤ D)) :
    ∀ i l, Inv i l → FunAll P self (.list [c, .nat i, .list l])
      (fun w cost => ∃ j l', w = .list l' ∧ Inv j l' ∧ l'.length ≤ j ∧
        cost ≤ (K + 1 - i) * (D + tmRpWK * (c.wt + K + M + 10))) := by
  intro i l hinv
  induction hd : K + 1 - i generalizing i l with
  | zero => have := hK i l hinv; omega
  | succ d ih =>
    refine FunAll.intro hself ?_
    obtain ⟨hil, hlK⟩ := hK i l hinv
    have hlM := hM i l hinv
    set A : List Val := [c, .nat i, .list l] with hAdef
    have hA := wt_list3_le c (.nat i) (.list l)
    have hAe : (Val.list A).wt = (Val.list [c, .nat i, .list l]).wt := rfl
    have hni := wt_nat_le i
    have d1 := Det.arg' (P := P) (vs := A) (rest := []) (j := 1) (v := .nat i) rfl
    have d2 := Det.arg' (P := P) (vs := A) (rest := []) (j := 2) (v := .list l) rfl
    have dl := Det.length d2
    by_cases hlt : i < l.length
    · have hc := Det.arith' (op := .lt) d1 dl (z := 1) (by simp [BinOp.eval, hlt])
      refine EvalAll.ite hc (fun _ _ h => ⟨1, h.1⟩) fun x cc hx => ?_
      obtain ⟨hx1, hcc⟩ := hx
      cases hx1
      simp only [one_ne_zero, if_false]
      have d0 := Det.arg' (P := P) (vs := A) (rest := []) (j := 0) (v := c) rfl
      have hB := Det.mk3 d0 d1 d2
      have hg := EvalAll.call_spec hB (hstep i l hinv hlt)
      have hadd := Det.arith' (op := .add) d1 (Det.nat 1) (z := i + 1) rfl
      have hL := EvalAll.snoc_det (Det.mk2 d0 hadd) hg
      refine EvalAll.call_funAll hL fun v ca h => ?_
      obtain ⟨w, cw, ⟨cb, ⟨l', rfl, hinv', hcb⟩, hcw⟩, rfl, hca⟩ := h
      obtain ⟨hil', hlK'⟩ := hK (i + 1) l' hinv'
      have hlM' := hM (i + 1) l' hinv'
      refine (ih (i + 1) l' hinv' (by omega)).mono fun u cr hpost => ?_
      obtain ⟨j, l'', rfl, hj, hjl, hcr⟩ := hpost
      refine ⟨j, l'', rfl, hj, hjl, ?_⟩
      have hl''M := hM j l'' hj
      have hA' := wt_list3_le c (.nat (i + 1)) (.list l')
      have hn1 := wt_nat_le (i + 1)
      have h2 := wt_list2_le c (.nat (i + 1))
      have e : [c, Val.nat (i + 1)] ++ [Val.list l'] = [c, .nat (i + 1), .list l'] := rfl
      rw [e] at hca
      have hm : (d + 1) * (D + tmRpWK * (c.wt + K + M + 10)) =
          d * (D + tmRpWK * (c.wt + K + M + 10)) + (D + tmRpWK * (c.wt + K + M + 10)) := by ring
      rw [hm]
      generalize d * (D + tmRpWK * (c.wt + K + M + 10)) = Y at hcr ⊢
      clear hm
      simp only [tmRpWK] at *
      omega
    · have hc := Det.arith' (op := .lt) d1 dl (z := 0) (by simp [BinOp.eval, hlt])
      refine (Det.ite_zero hc d2).post fun cost hcost => ⟨i, l, rfl, hinv, by omega, ?_⟩
      have h2 : D + tmRpWK * (c.wt + K + M + 10) ≤
          (d + 1) * (D + tmRpWK * (c.wt + K + M + 10)) := Nat.le_mul_of_pos_left _ (by omega)
      simp only [tmRpWK] at *
      omega

end GI.Impl
