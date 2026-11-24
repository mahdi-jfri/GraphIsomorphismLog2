/-
Pass lemmas for the loops of the Turing machine in `Workspace.Turing.TM.Machine`.

Each loop statement (`popLoopStmt`, `restoreLoopStmt`, `movePopStmt`, `copyPopStmt`, `addLoopStmt`,
`subLoopStmt`, `drainLoopStmt`, `stripZerosStmt`, `retLoopStmt`, `flushOutStmt`) is proved once
against an abstract hypothesis `tmProg P self = ...`, by induction on the list of digits or stack
elements consumed. The instruction lemmas in `Step.lean` and the halting phase in `Main.lean`
compose these pass lemmas directly.
-/
module

public import Workspace.Turing.TM.Machine

@[expose] public section

namespace GI.Turing.TM

open _root_.Turing (FinTM2)
open _root_.Turing.TM2 (stepAux)
open Function (update)

/-- Push raw bits from a scratch stack onto a target stack as encoded digits `[true, b]`,
reversing their order. -/
def pushDigits : List Bool → List Bool → List Bool
  | [], t0 => t0
  | d :: ds, t0 => pushDigits ds (true :: d :: t0)

theorem pushDigits_append (xs ys t0 : List Bool) :
    pushDigits (xs ++ ys) t0 = pushDigits ys (pushDigits xs t0) := by
  induction xs generalizing t0 with
  | nil => rfl
  | cons x xs ih => exact ih (true :: x :: t0)

theorem pushDigits_reverse_false (bs rest : List Bool) :
    pushDigits bs.reverse (false :: rest) = encDigits bs ++ rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons, pushDigits_append, ih]
    rfl

private theorem tm_step_some {P : SM.Program} (lbl : Lab P.length) (v : State P.length)
    (S : K → List Bool) :
    (tm P).step ⟨some lbl, v, S⟩ = some (stepAux (tmProg P lbl) v S) := rfl

theorem reachesIn_popLoop {P : SM.Program} {s : K} {self : Lab P.length}
    {exitStmt : MStmt P.length} (hm : tmProg P self = popLoopStmt s self exitStmt)
    (bs rest : List Bool) (v : State P.length) (S : K → List Bool)
    (hs : S s = encDigits bs ++ rest) :
    ReachesIn (tm P) ⟨some self, v, S⟩
      (stepAux exitStmt { v with flag := false } (update S s rest)) (bs.length + 1) := by
  induction bs generalizing v S with
  | nil =>
    apply ReachesIn.single
    rw [tm_step_some, hm]
    simp only [popLoopStmt, stepAux, hs, encDigits, List.singleton_append, List.head?_cons,
      List.tail_cons]
    rfl
  | cons b bs ih =>
    have hstep : (tm P).step ⟨some self, v, S⟩ =
        some ⟨some self, { v with flag := true }, update S s (encDigits bs ++ rest)⟩ := by
      rw [tm_step_some, hm]
      simp only [popLoopStmt, stepAux, hs, encDigits, List.cons_append, List.head?_cons,
        List.tail_cons, Function.update_self, Function.update_idem]
      rfl
    have hrest := ih { v with flag := true } (update S s (encDigits bs ++ rest))
      (Function.update_self s _ S)
    simp only [Function.update_idem] at hrest
    simpa [List.length_cons, Nat.add_assoc] using ReachesIn.step_head hstep hrest

theorem reachesIn_restoreLoop {P : SM.Program} {scr tgt : K} (hne : scr ≠ tgt)
    {self : Lab P.length} {exitStmt : MStmt P.length}
    (hm : tmProg P self = restoreLoopStmt scr tgt self exitStmt)
    (ds : List Bool) (v : State P.length) (S : K → List Bool) (hscr : S scr = ds) :
    ∃ v' : State P.length,
      ReachesIn (tm P) ⟨some self, v, S⟩
        (stepAux exitStmt v' (update (update S scr []) tgt (pushDigits ds (S tgt))))
        (ds.length + 1) := by
  induction ds generalizing v S with
  | nil =>
    refine ⟨{ v with flag := false }, ReachesIn.single ?_⟩
    rw [tm_step_some, hm]
    simp only [restoreLoopStmt, stepAux, hscr, List.head?_nil, List.tail_nil, pushDigits,
      Bool.cond_false]
    have hupd : update (update S scr []) tgt (S tgt) = update S scr [] := by
      ext k
      by_cases hkt : k = tgt
      · subst hkt; rw [Function.update_self, Function.update_of_ne hne.symm]
      · rw [Function.update_of_ne hkt]
    rw [hupd]
    rfl
  | cons d ds ih =>
    let S₁ := update (update S scr ds) tgt (true :: d :: S tgt)
    have hstep : (tm P).step ⟨some self, v, S⟩ =
        some ⟨some self, { v with flag := true, bit := d }, S₁⟩ := by
      rw [tm_step_some, hm]
      simp only [restoreLoopStmt, stepAux, hscr, List.head?_cons, List.tail_cons, Bool.cond_true,
        Function.update_of_ne hne.symm, Function.update_self, Function.update_idem, S₁]
      rfl
    have hS₁_scr : S₁ scr = ds := by
      simp only [S₁, Function.update_of_ne hne, Function.update_self]
    have hS₁_tgt : S₁ tgt = true :: d :: S tgt := by
      simp only [S₁, Function.update_self]
    obtain ⟨v', hrest⟩ := ih { v with flag := true, bit := d } S₁ hS₁_scr
    rw [hS₁_tgt] at hrest
    have hEq : update (update S₁ scr []) tgt (pushDigits ds (true :: d :: S tgt)) =
        update (update S scr []) tgt (pushDigits (d :: ds) (S tgt)) := by
      ext k
      by_cases hkt : k = tgt
      · subst hkt; simp [pushDigits]
      · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
        by_cases hks : k = scr
        · subst hks; simp
        · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hkt]
    rw [hEq] at hrest
    exact ⟨v', by simpa [List.length_cons, Nat.add_assoc] using ReachesIn.step_head hstep hrest⟩

theorem reachesIn_movePop {P : SM.Program} {s t : K}
    (hs0 : s ≠ .scr0) (_ht0 : t ≠ .scr0) {self next : Lab P.length}
    (hm : tmProg P self = movePopStmt s t self next)
    (bs rest acc : List Bool) (v : State P.length) (S : K → List Bool)
    (hs : S s = encDigits bs ++ rest) (hscr : S .scr0 = acc) :
    ∃ v' : State P.length,
      ReachesIn (tm P) ⟨some self, v, S⟩
        ⟨some next, v',
          let S' := update (update S s rest) .scr0 (bs.reverse ++ acc)
          update S' t (false :: S' t)⟩
        (bs.length + 1) := by
  induction bs generalizing acc v S with
  | nil =>
    refine ⟨{ v with flag := false }, ReachesIn.single ?_⟩
    rw [tm_step_some, hm]
    simp only [movePopStmt, stepAux, hs, encDigits, List.singleton_append, List.head?_cons,
      List.tail_cons, List.reverse_nil, List.nil_append]
    have hscr' : update (update S s rest) .scr0 acc = update S s rest := by
      ext k
      by_cases hk : k = .scr0
      · subst hk; rw [Function.update_self, Function.update_of_ne hs0.symm, hscr]
      · rw [Function.update_of_ne hk]
    rw [hscr']
    rfl
  | cons b bs ih =>
    let S₁ := update (update S s (encDigits bs ++ rest)) .scr0 (b :: acc)
    have hstep : (tm P).step ⟨some self, v, S⟩ =
        some ⟨some self, { v with flag := true, bit := b }, S₁⟩ := by
      rw [tm_step_some, hm]
      simp only [movePopStmt, stepAux, hs, encDigits, List.cons_append, List.head?_cons,
        List.tail_cons, Function.update_self, Function.update_idem, Function.update_of_ne hs0.symm,
        hscr, S₁]
      rfl
    have hS₁s : S₁ s = encDigits bs ++ rest := by
      simp only [S₁, Function.update_of_ne hs0, Function.update_self]
    have hS₁0 : S₁ .scr0 = b :: acc := by
      simp only [S₁, Function.update_self]
    obtain ⟨v', hrest⟩ := ih (b :: acc) { v with flag := true, bit := b } S₁ hS₁s hS₁0
    have hS'eq : update (update S₁ s rest) .scr0 (bs.reverse ++ b :: acc) =
        update (update S s rest) .scr0 ((b :: bs).reverse ++ acc) := by
      ext k
      by_cases hk0 : k = .scr0
      · subst hk0; simp [List.reverse_cons, List.append_assoc]
      · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
        by_cases hks : k = s
        · subst hks; simp
        · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hk0]
    dsimp only at hrest ⊢
    rw [hS'eq] at hrest
    exact ⟨v', by simpa [List.length_cons, Nat.add_assoc] using ReachesIn.step_head hstep hrest⟩

theorem reachesIn_copyPop {P : SM.Program} {s : K}
    (hs0 : s ≠ .scr0) (hs1 : s ≠ .scr1) {self next : Lab P.length}
    (hm : tmProg P self = copyPopStmt s self next)
    (bs rest acc0 acc1 : List Bool) (v : State P.length) (S : K → List Bool)
    (hs : S s = encDigits bs ++ rest) (h0 : S .scr0 = acc0) (h1 : S .scr1 = acc1) :
    ∃ v' : State P.length,
      ReachesIn (tm P) ⟨some self, v, S⟩
        ⟨some next, v',
          update (update (update S s (false :: rest)) .scr0 (bs.reverse ++ acc0))
            .scr1 (bs.reverse ++ acc1)⟩
        (bs.length + 1) := by
  have h01 : K.scr0 ≠ K.scr1 := by decide
  induction bs generalizing acc0 acc1 v S with
  | nil =>
    refine ⟨{ v with flag := false }, ReachesIn.single ?_⟩
    rw [tm_step_some, hm]
    simp only [copyPopStmt, stepAux, hs, encDigits, List.singleton_append, List.head?_cons,
      List.tail_cons, Function.update_self, Function.update_idem, List.reverse_nil,
      List.nil_append]
    have hEq : update (update (update S s (false :: rest)) .scr0 acc0) .scr1 acc1 =
        update S s (false :: rest) := by
      ext k
      by_cases hk1 : k = .scr1
      · subst hk1; rw [Function.update_self, Function.update_of_ne hs1.symm, h1]
      · rw [Function.update_of_ne hk1]
        by_cases hk0 : k = .scr0
        · subst hk0; rw [Function.update_self, Function.update_of_ne hs0.symm, h0]
        · rw [Function.update_of_ne hk0]
    rw [hEq]
    rfl
  | cons b bs ih =>
    let S₁ := update (update (update S s (encDigits bs ++ rest)) .scr0 (b :: acc0)) .scr1 (b :: acc1)
    have hstep : (tm P).step ⟨some self, v, S⟩ =
        some ⟨some self, { v with flag := true, bit := b }, S₁⟩ := by
      rw [tm_step_some, hm]
      simp only [copyPopStmt, stepAux, hs, encDigits, List.cons_append, List.head?_cons,
        List.tail_cons, Function.update_self, Function.update_idem, Function.update_of_ne hs0.symm,
        Function.update_of_ne hs1.symm, Function.update_of_ne h01.symm, h0, h1, S₁]
      rfl
    have hS₁s : S₁ s = encDigits bs ++ rest := by
      simp only [S₁, Function.update_of_ne hs1, Function.update_of_ne hs0, Function.update_self]
    have hS₁0 : S₁ .scr0 = b :: acc0 := by
      simp only [S₁, Function.update_of_ne h01, Function.update_self]
    have hS₁1 : S₁ .scr1 = b :: acc1 := by
      simp only [S₁, Function.update_self]
    obtain ⟨v', hrest⟩ := ih (b :: acc0) (b :: acc1) { v with flag := true, bit := b } S₁
      hS₁s hS₁0 hS₁1
    have hEq : update (update (update S₁ s (false :: rest)) .scr0 (bs.reverse ++ b :: acc0))
          .scr1 (bs.reverse ++ b :: acc1) =
        update (update (update S s (false :: rest)) .scr0 ((b :: bs).reverse ++ acc0))
          .scr1 ((b :: bs).reverse ++ acc1) := by
      ext k
      by_cases hk1 : k = .scr1
      · subst hk1; simp [List.reverse_cons, List.append_assoc]
      · rw [Function.update_of_ne hk1, Function.update_of_ne hk1]
        by_cases hk0 : k = .scr0
        · subst hk0; simp [List.reverse_cons, List.append_assoc]
        · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
          by_cases hks : k = s
          · subst hks; simp
          · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hk0, Function.update_of_ne hk1]
    rw [hEq] at hrest
    exact ⟨v', by simpa [List.length_cons, Nat.add_assoc] using ReachesIn.step_head hstep hrest⟩

theorem reachesIn_addLoop {P : SM.Program} {s t : K}
    (hst : s ≠ t) (hs0 : s ≠ .scr0) (ht0 : t ≠ .scr0) {self next : Lab P.length}
    (hm : tmProg P self = addLoopStmt s t self next)
    (as bs rs rt acc : List Bool) (v : State P.length) (S : K → List Bool)
    (hs : S s = encDigits as ++ rs) (ht : S t = encDigits bs ++ rt) (h0 : S .scr0 = acc) :
    ∃ v' : State P.length,
      ReachesIn (tm P) ⟨some self, v, S⟩
        ⟨some next, v',
          update (update (update S s (false :: rs)) t rt) .scr0
            ((addBitsRaw as bs v.carry).reverse ++ acc)⟩
        (max as.length bs.length + 1) := by
  induction as generalizing bs acc v S with
  | nil =>
    induction bs generalizing acc v S with
    | nil =>
      refine ⟨{ v with flag := false, bit := false, flag2 := false, bit2 := false },
        ReachesIn.single ?_⟩
      rw [tm_step_some, hm]
      simp only [addLoopStmt, stepAux, hs, ht, encDigits, List.singleton_append, List.head?_cons,
        List.tail_cons, Function.update_of_ne ht0.symm, h0, addBitsRaw]
      cases hc : v.carry
      · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte, List.reverse_nil,
          List.nil_append]
        have hEq : update (update (update S s (false :: rs)) t rt) .scr0 acc = update S t rt := by
          ext k
          by_cases hk0 : k = .scr0
          · subst hk0; rw [Function.update_self, Function.update_of_ne ht0.symm, h0]
          · rw [Function.update_of_ne hk0]
            by_cases hkt : k = t
            · subst hkt; simp
            · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
              by_cases hks : k = s
              · subst hks; rw [Function.update_self, hs]; rfl
              · rw [Function.update_of_ne hks]
        rw [hEq]
        rfl
      · simp only [Bool.cond_true, ↓reduceIte, List.reverse_singleton, List.singleton_append]
        have hEq : update (update (update S s (false :: rs)) t rt) .scr0 (true :: acc) =
            update (update S t rt) .scr0 (true :: acc) := by
          ext k
          by_cases hk0 : k = .scr0
          · subst hk0; simp
          · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
            by_cases hkt : k = t
            · subst hkt; simp
            · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
              by_cases hks : k = s
              · subst hks; rw [Function.update_self, hs]; rfl
              · rw [Function.update_of_ne hks]
        rw [hEq]
        rfl
    | cons b bs ihb =>
      let d := xor b v.carry
      let c' := b && v.carry
      let v₁ : State P.length :=
        { v with flag := false, bit := false, flag2 := true, bit2 := b, carry := c' }
      let S₁ := update (update S t (encDigits bs ++ rt)) .scr0 (d :: acc)
      have hstep : (tm P).step ⟨some self, v, S⟩ = some ⟨some self, v₁, S₁⟩ := by
        rw [tm_step_some, hm]
        simp only [addLoopStmt, stepAux, hs, ht, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem,
          Function.update_of_ne ht0.symm, h0, Bool.false_or, Bool.false_xor, Bool.false_and,
          v₁, S₁, d, c']
        rfl
      have hS₁s : S₁ s = encDigits [] ++ rs := by
        simp only [S₁, Function.update_of_ne hs0, Function.update_of_ne hst, hs]
      have hS₁t : S₁ t = encDigits bs ++ rt := by
        simp only [S₁, Function.update_of_ne ht0, Function.update_self]
      have hS₁0 : S₁ .scr0 = d :: acc := by
        simp only [S₁, Function.update_self]
      obtain ⟨v', hrest⟩ := ihb (d :: acc) v₁ S₁ hS₁s hS₁t hS₁0
      have hEq : update (update (update S₁ s (false :: rs)) t rt) .scr0
            ((addBitsRaw [] bs v₁.carry).reverse ++ d :: acc) =
          update (update (update S s (false :: rs)) t rt) .scr0
            ((addBitsRaw [] (b :: bs) v.carry).reverse ++ acc) := by
        ext k
        by_cases hk0 : k = .scr0
        · subst hk0; simp [addBitsRaw, List.reverse_cons, List.append_assoc, v₁, d, c']
        · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
          by_cases hkt : k = t
          · subst hkt; simp
          · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
            by_cases hks : k = s
            · subst hks; simp
            · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hkt,
                Function.update_of_ne hk0]
      rw [hEq] at hrest
      exact ⟨v', by
        simpa [List.length_nil, List.length_cons, Nat.zero_max, Nat.add_assoc] using
          ReachesIn.step_head hstep hrest⟩
  | cons a as iha =>
    cases bs with
    | nil =>
      let d := xor a v.carry
      let c' := a && v.carry
      let v₁ : State P.length :=
        { v with flag := true, bit := a, flag2 := false, bit2 := false, carry := c' }
      let S₁ := update (update S s (encDigits as ++ rs)) .scr0 (d :: acc)
      have hstep : (tm P).step ⟨some self, v, S⟩ = some ⟨some self, v₁, S₁⟩ := by
        rw [tm_step_some, hm]
        simp only [addLoopStmt, stepAux, hs, ht, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem,
          Function.update_of_ne hst.symm, Function.update_of_ne hs0.symm, h0, Bool.or_false,
          Bool.xor_false, Bool.and_false, Bool.false_and, Bool.false_or, v₁, S₁, d, c']
        rfl
      have hS₁s : S₁ s = encDigits as ++ rs := by
        simp only [S₁, Function.update_of_ne hs0, Function.update_self]
      have hS₁t : S₁ t = encDigits [] ++ rt := by
        simp only [S₁, Function.update_of_ne ht0, Function.update_of_ne hst.symm, ht]
      have hS₁0 : S₁ .scr0 = d :: acc := by
        simp only [S₁, Function.update_self]
      obtain ⟨v', hrest⟩ := iha [] (d :: acc) v₁ S₁ hS₁s hS₁t hS₁0
      have hEq : update (update (update S₁ s (false :: rs)) t rt) .scr0
            ((addBitsRaw as [] v₁.carry).reverse ++ d :: acc) =
          update (update (update S s (false :: rs)) t rt) .scr0
            ((addBitsRaw (a :: as) [] v.carry).reverse ++ acc) := by
        ext k
        by_cases hk0 : k = .scr0
        · subst hk0; simp [addBitsRaw, List.reverse_cons, List.append_assoc, v₁, d, c']
        · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
          by_cases hkt : k = t
          · subst hkt; simp
          · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
            by_cases hks : k = s
            · subst hks; simp
            · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hk0]
      rw [hEq] at hrest
      exact ⟨v', by
        simpa [List.length_nil, List.length_cons, Nat.max_zero, Nat.add_assoc] using
          ReachesIn.step_head hstep hrest⟩
    | cons b bs =>
      let d := xor (xor a b) v.carry
      let c' := (a && b) || (a && v.carry) || (b && v.carry)
      let v₁ : State P.length :=
        { v with flag := true, bit := a, flag2 := true, bit2 := b, carry := c' }
      let S₁ := update (update (update S s (encDigits as ++ rs)) t (encDigits bs ++ rt))
        .scr0 (d :: acc)
      have hstep : (tm P).step ⟨some self, v, S⟩ = some ⟨some self, v₁, S₁⟩ := by
        rw [tm_step_some, hm]
        simp only [addLoopStmt, stepAux, hs, ht, encDigits, List.cons_append, List.head?_cons,
          List.tail_cons, Function.update_self, Function.update_idem, Function.update_of_ne hst.symm,
          Function.update_of_ne hs0.symm, Function.update_of_ne ht0.symm, h0, v₁, S₁, d, c']
        rfl
      have hS₁s : S₁ s = encDigits as ++ rs := by
        simp only [S₁, Function.update_of_ne hs0, Function.update_of_ne hst, Function.update_self]
      have hS₁t : S₁ t = encDigits bs ++ rt := by
        simp only [S₁, Function.update_of_ne ht0, Function.update_self]
      have hS₁0 : S₁ .scr0 = d :: acc := by
        simp only [S₁, Function.update_self]
      obtain ⟨v', hrest⟩ := iha bs (d :: acc) v₁ S₁ hS₁s hS₁t hS₁0
      have hEq : update (update (update S₁ s (false :: rs)) t rt) .scr0
            ((addBitsRaw as bs v₁.carry).reverse ++ d :: acc) =
          update (update (update S s (false :: rs)) t rt) .scr0
            ((addBitsRaw (a :: as) (b :: bs) v.carry).reverse ++ acc) := by
        ext k
        by_cases hk0 : k = .scr0
        · subst hk0; simp [addBitsRaw, List.reverse_cons, List.append_assoc, v₁, d, c']
        · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
          by_cases hkt : k = t
          · subst hkt; simp
          · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
            by_cases hks : k = s
            · subst hks; simp
            · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hkt,
                Function.update_of_ne hk0]
      rw [hEq] at hrest
      have hlen : max as.length bs.length + 1 + 1 =
          max (a :: as).length (b :: bs).length + 1 := by
        simp only [List.length_cons]; omega
      rw [← hlen]
      exact ⟨v', ReachesIn.step_head hstep hrest⟩

theorem reachesIn_subLoop {P : SM.Program} {s t : K}
    (hst : s ≠ t) (hs0 : s ≠ .scr0) (ht0 : t ≠ .scr0)
    {self onBorrow onNoBorrow : Lab P.length}
    (hm : tmProg P self = subLoopStmt s t self onBorrow onNoBorrow)
    (as bs rs rt acc : List Bool) (v : State P.length) (S : K → List Bool)
    (hs : S s = encDigits as ++ rs) (ht : S t = encDigits bs ++ rt) (h0 : S .scr0 = acc) :
    ∃ v' : State P.length,
      ReachesIn (tm P) ⟨some self, v, S⟩
        ⟨some (if (subBitsRaw as bs v.carry).2 then onBorrow else onNoBorrow), v',
          update (update (update S s (false :: rs)) t rt) .scr0
            ((subBitsRaw as bs v.carry).1.reverse ++ acc)⟩
        (max as.length bs.length + 1) := by
  induction as generalizing bs acc v S with
  | nil =>
    induction bs generalizing acc v S with
    | nil =>
      refine ⟨{ v with flag := false, bit := false, flag2 := false, bit2 := false },
        ReachesIn.single ?_⟩
      rw [tm_step_some, hm]
      simp only [subLoopStmt, stepAux, hs, ht, encDigits, List.singleton_append, List.head?_cons,
        List.tail_cons, subBitsRaw, List.reverse_nil, List.nil_append]
      have hEq : update (update (update S s (false :: rs)) t rt) .scr0 acc = update S t rt := by
        ext k
        by_cases hk0 : k = .scr0
        · subst hk0; rw [Function.update_self, Function.update_of_ne ht0.symm, h0]
        · rw [Function.update_of_ne hk0]
          by_cases hkt : k = t
          · subst hkt; simp
          · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
            by_cases hks : k = s
            · subst hks; rw [Function.update_self, hs]; rfl
            · rw [Function.update_of_ne hks]
      rw [hEq]
      cases v.carry <;> rfl
    | cons b bs ihb =>
      let d := xor b v.carry
      let c' := b || v.carry
      let v₁ : State P.length :=
        { v with flag := false, bit := false, flag2 := true, bit2 := b, carry := c' }
      let S₁ := update (update S t (encDigits bs ++ rt)) .scr0 (d :: acc)
      have hstep : (tm P).step ⟨some self, v, S⟩ = some ⟨some self, v₁, S₁⟩ := by
        rw [tm_step_some, hm]
        simp only [subLoopStmt, stepAux, hs, ht, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem,
          Function.update_of_ne ht0.symm, h0, Bool.false_or, Bool.false_xor, Bool.not_false,
          Bool.true_and, v₁, S₁, d, c']
        cases b <;> cases v.carry <;> rfl
      have hS₁s : S₁ s = encDigits [] ++ rs := by
        simp only [S₁, Function.update_of_ne hs0, Function.update_of_ne hst, hs]
      have hS₁t : S₁ t = encDigits bs ++ rt := by
        simp only [S₁, Function.update_of_ne ht0, Function.update_self]
      have hS₁0 : S₁ .scr0 = d :: acc := by
        simp only [S₁, Function.update_self]
      obtain ⟨v', hrest⟩ := ihb (d :: acc) v₁ S₁ hS₁s hS₁t hS₁0
      have hEq : update (update (update S₁ s (false :: rs)) t rt) .scr0
            ((subBitsRaw [] bs v₁.carry).1.reverse ++ d :: acc) =
          update (update (update S s (false :: rs)) t rt) .scr0
            ((subBitsRaw [] (b :: bs) v.carry).1.reverse ++ acc) := by
        ext k
        by_cases hk0 : k = .scr0
        · subst hk0; simp [subBitsRaw, List.reverse_cons, List.append_assoc, v₁, d, c']
        · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
          by_cases hkt : k = t
          · subst hkt; simp
          · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
            by_cases hks : k = s
            · subst hks; simp
            · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hkt,
                Function.update_of_ne hk0]
      rw [hEq] at hrest
      have hbr : (subBitsRaw [] bs v₁.carry).2 = (subBitsRaw [] (b :: bs) v.carry).2 := by
        simp [subBitsRaw, v₁, c']
      rw [hbr] at hrest
      exact ⟨v', by
        simpa [List.length_nil, List.length_cons, Nat.zero_max, Nat.add_assoc] using
          ReachesIn.step_head hstep hrest⟩
  | cons a as iha =>
    cases bs with
    | nil =>
      let d := xor a v.carry
      let c' := !a && v.carry
      let v₁ : State P.length :=
        { v with flag := true, bit := a, flag2 := false, bit2 := false, carry := c' }
      let S₁ := update (update S s (encDigits as ++ rs)) .scr0 (d :: acc)
      have hstep : (tm P).step ⟨some self, v, S⟩ = some ⟨some self, v₁, S₁⟩ := by
        rw [tm_step_some, hm]
        simp only [subLoopStmt, stepAux, hs, ht, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem,
          Function.update_of_ne hst.symm, Function.update_of_ne hs0.symm, h0, Bool.or_false,
          Bool.xor_false, Bool.false_or, Bool.false_and, v₁, S₁, d, c']
        rfl
      have hS₁s : S₁ s = encDigits as ++ rs := by
        simp only [S₁, Function.update_of_ne hs0, Function.update_self]
      have hS₁t : S₁ t = encDigits [] ++ rt := by
        simp only [S₁, Function.update_of_ne ht0, Function.update_of_ne hst.symm, ht]
      have hS₁0 : S₁ .scr0 = d :: acc := by
        simp only [S₁, Function.update_self]
      obtain ⟨v', hrest⟩ := iha [] (d :: acc) v₁ S₁ hS₁s hS₁t hS₁0
      have hEq : update (update (update S₁ s (false :: rs)) t rt) .scr0
            ((subBitsRaw as [] v₁.carry).1.reverse ++ d :: acc) =
          update (update (update S s (false :: rs)) t rt) .scr0
            ((subBitsRaw (a :: as) [] v.carry).1.reverse ++ acc) := by
        ext k
        by_cases hk0 : k = .scr0
        · subst hk0; simp [subBitsRaw, List.reverse_cons, List.append_assoc, v₁, d, c']
        · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
          by_cases hkt : k = t
          · subst hkt; simp
          · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
            by_cases hks : k = s
            · subst hks; simp
            · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hk0]
      rw [hEq] at hrest
      have hbr : (subBitsRaw as [] v₁.carry).2 = (subBitsRaw (a :: as) [] v.carry).2 := by
        simp [subBitsRaw, v₁, c']
      rw [hbr] at hrest
      exact ⟨v', by
        simpa [List.length_nil, List.length_cons, Nat.max_zero, Nat.add_assoc] using
          ReachesIn.step_head hstep hrest⟩
    | cons b bs =>
      let d := xor (xor a b) v.carry
      let c' := (!a && (b || v.carry)) || (b && v.carry)
      let v₁ : State P.length :=
        { v with flag := true, bit := a, flag2 := true, bit2 := b, carry := c' }
      let S₁ := update (update (update S s (encDigits as ++ rs)) t (encDigits bs ++ rt))
        .scr0 (d :: acc)
      have hstep : (tm P).step ⟨some self, v, S⟩ = some ⟨some self, v₁, S₁⟩ := by
        rw [tm_step_some, hm]
        simp only [subLoopStmt, stepAux, hs, ht, encDigits, List.cons_append, List.head?_cons,
          List.tail_cons, Function.update_self, Function.update_idem, Function.update_of_ne hst.symm,
          Function.update_of_ne hs0.symm, Function.update_of_ne ht0.symm, h0, v₁, S₁, d, c']
        rfl
      have hS₁s : S₁ s = encDigits as ++ rs := by
        simp only [S₁, Function.update_of_ne hs0, Function.update_of_ne hst, Function.update_self]
      have hS₁t : S₁ t = encDigits bs ++ rt := by
        simp only [S₁, Function.update_of_ne ht0, Function.update_self]
      have hS₁0 : S₁ .scr0 = d :: acc := by
        simp only [S₁, Function.update_self]
      obtain ⟨v', hrest⟩ := iha bs (d :: acc) v₁ S₁ hS₁s hS₁t hS₁0
      have hEq : update (update (update S₁ s (false :: rs)) t rt) .scr0
            ((subBitsRaw as bs v₁.carry).1.reverse ++ d :: acc) =
          update (update (update S s (false :: rs)) t rt) .scr0
            ((subBitsRaw (a :: as) (b :: bs) v.carry).1.reverse ++ acc) := by
        ext k
        by_cases hk0 : k = .scr0
        · subst hk0; simp [subBitsRaw, List.reverse_cons, List.append_assoc, v₁, d, c']
        · rw [Function.update_of_ne hk0, Function.update_of_ne hk0]
          by_cases hkt : k = t
          · subst hkt; simp
          · rw [Function.update_of_ne hkt, Function.update_of_ne hkt]
            by_cases hks : k = s
            · subst hks; simp
            · simp [S₁, Function.update_of_ne hks, Function.update_of_ne hkt,
                Function.update_of_ne hk0]
      rw [hEq] at hrest
      have hbr : (subBitsRaw as bs v₁.carry).2 = (subBitsRaw (a :: as) (b :: bs) v.carry).2 := by
        simp [subBitsRaw, v₁, c']
      rw [hbr] at hrest
      have hlen : max as.length bs.length + 1 + 1 =
          max (a :: as).length (b :: bs).length + 1 := by
        simp only [List.length_cons]; omega
      rw [← hlen]
      exact ⟨v', ReachesIn.step_head hstep hrest⟩

theorem reachesIn_drainLoop {P : SM.Program} {k : K} {self : Lab P.length}
    {exitStmt : MStmt P.length} (hm : tmProg P self = drainLoopStmt k self exitStmt)
    (l : List Bool) (v : State P.length) (S : K → List Bool) (hk : S k = l) :
    ReachesIn (tm P) ⟨some self, v, S⟩
      (stepAux exitStmt { v with flag := false } (update S k [])) (l.length + 1) := by
  induction l generalizing v S with
  | nil =>
    apply ReachesIn.single
    rw [tm_step_some, hm]
    simp only [drainLoopStmt, stepAux, hk, List.head?_nil, List.tail_nil, Option.isSome_none,
      Bool.cond_false]
    rfl
  | cons b bs ih =>
    have hstep : (tm P).step ⟨some self, v, S⟩ =
        some ⟨some self, { v with flag := true }, update S k bs⟩ := by
      rw [tm_step_some, hm]
      simp only [drainLoopStmt, stepAux, hk, List.head?_cons, List.tail_cons, Option.isSome_some,
        Bool.cond_true]
      rfl
    have hrest := ih { v with flag := true } (update S k bs) (Function.update_self k bs S)
    simp only [Function.update_idem] at hrest
    simpa [List.length_cons, Nat.add_assoc] using ReachesIn.step_head hstep hrest

theorem reachesIn_stripZeros {P : SM.Program} {self next : Lab P.length}
    (hm : tmProg P self = stripZerosStmt self next)
    (l : List Bool) (v : State P.length) (S : K → List Bool) (h0 : S .scr0 = l) :
    ∃ v' : State P.length,
      ReachesIn (tm P) ⟨some self, v, S⟩
        ⟨some next, v', update S .scr0 (stripLeadingFalse l)⟩
        (leadingFalseCount l + 1) := by
  induction l generalizing v S with
  | nil =>
    refine ⟨{ v with flag := false }, ReachesIn.single ?_⟩
    rw [tm_step_some, hm]
    simp only [stripZerosStmt, stepAux, h0, List.head?_nil, stripLeadingFalse]
    have hEq : update S .scr0 [] = S := by
      ext k; by_cases hk : k = .scr0
      · subst hk; rw [Function.update_self, h0]
      · rw [Function.update_of_ne hk]
    rw [hEq]
    rfl
  | cons b bs ih =>
    cases b with
    | true =>
      refine ⟨{ v with flag := false }, ReachesIn.single ?_⟩
      rw [tm_step_some, hm]
      simp only [stripZerosStmt, stepAux, h0, List.head?_cons, stripLeadingFalse]
      have hEq : update S .scr0 (true :: bs) = S := by
        ext k; by_cases hk : k = .scr0
        · subst hk; rw [Function.update_self, h0]
        · rw [Function.update_of_ne hk]
      rw [hEq]
      rfl
    | false =>
      have hstep : (tm P).step ⟨some self, v, S⟩ =
          some ⟨some self, { v with flag := true }, update S .scr0 bs⟩ := by
        rw [tm_step_some, hm]
        simp only [stripZerosStmt, stepAux, h0, List.head?_cons, List.tail_cons]
        rfl
      obtain ⟨v', hrest⟩ := ih { v with flag := true } (update S .scr0 bs)
        (Function.update_self .scr0 bs S)
      simp only [Function.update_idem] at hrest
      exact ⟨v', by
        simpa [leadingFalseCount, stripLeadingFalse, Nat.add_assoc] using
          ReachesIn.step_head hstep hrest⟩

theorem reachesIn_retLoop {P : SM.Program} {self : Lab P.length}
    (hm : tmProg P self = retLoopStmt self)
    (r : ℕ) (rest : List Bool) (v : State P.length) (S : K → List Bool)
    (hret : S .ret = encRet r ++ rest) (hle : v.addr.val + r ≤ P.length) :
    ∃ v' : State P.length,
      ReachesIn (tm P) ⟨some self, v, S⟩
        ⟨some (⟨v.addr.val + r, Nat.lt_succ_of_le hle⟩, .start), v', update S .ret rest⟩
        (r + 1) := by
  induction r generalizing v S with
  | zero =>
    refine ⟨{ v with flag := false }, ReachesIn.single ?_⟩
    rw [tm_step_some, hm]
    simp only [retLoopStmt, stepAux, hret, encRet, List.replicate_zero, List.nil_append,
      List.singleton_append, List.head?_cons, List.tail_cons, Nat.add_zero]
    rfl
  | succ r ih =>
    let v₁ : State P.length := { v with flag := true, addr := clampPc P.length (v.addr.val + 1) }
    have hstep : (tm P).step ⟨some self, v, S⟩ =
        some ⟨some self, v₁, update S .ret (encRet r ++ rest)⟩ := by
      rw [tm_step_some, hm]
      simp only [retLoopStmt, stepAux, hret, encRet, List.replicate_succ, List.cons_append,
        List.head?_cons, List.tail_cons, v₁]
      rfl
    have hv₁ : v₁.addr.val = v.addr.val + 1 := by
      simp only [v₁, clampPc]
      exact Nat.min_eq_left (by omega)
    have hle₁ : v₁.addr.val + r ≤ P.length := by omega
    obtain ⟨v', hrest⟩ := ih v₁ (update S .ret (encRet r ++ rest))
      (Function.update_self .ret _ S) hle₁
    simp only [Function.update_idem] at hrest
    have hfin : (⟨v₁.addr.val + r, Nat.lt_succ_of_le hle₁⟩ : Fin (P.length + 1)) =
        ⟨v.addr.val + (r + 1), Nat.lt_succ_of_le hle⟩ := by
      ext; dsimp only; omega
    rw [hfin] at hrest
    exact ⟨v', by simpa [Nat.add_assoc] using ReachesIn.step_head hstep hrest⟩

theorem reachesIn_flushOut {P : SM.Program} {self : Lab P.length}
    (hm : tmProg P self = flushOutStmt self)
    (l : List Bool) (v : State P.length) (S : K → List Bool) (hout : S .outBuf = l) :
    ReachesIn (tm P) ⟨some self, v, S⟩
      ⟨none, initState P.length, update (update S .outBuf []) .out (l.reverse ++ S .out)⟩
      (l.length + 1) := by
  have hne : K.outBuf ≠ K.out := by decide
  induction l generalizing v S with
  | nil =>
    apply ReachesIn.single
    rw [tm_step_some, hm]
    simp only [flushOutStmt, stepAux, hout, List.head?_nil, List.tail_nil, Bool.cond_false,
      List.reverse_nil, List.nil_append]
    have hEq : update (update S .outBuf []) .out (S .out) = update S .outBuf [] := by
      ext k
      by_cases hk : k = .out
      · subst hk; rw [Function.update_self, Function.update_of_ne hne.symm]
      · rw [Function.update_of_ne hk]
    rw [hEq]
    rfl
  | cons b bs ih =>
    let S₁ := update (update S .outBuf bs) .out (b :: S .out)
    have hstep : (tm P).step ⟨some self, v, S⟩ =
        some ⟨some self, { v with flag := true, bit := b }, S₁⟩ := by
      rw [tm_step_some, hm]
      simp only [flushOutStmt, stepAux, hout, List.head?_cons, List.tail_cons, Bool.cond_true,
        Function.update_of_ne hne.symm, S₁]
      rfl
    have hS₁b : S₁ .outBuf = bs := by
      simp only [S₁, Function.update_of_ne hne, Function.update_self]
    have hS₁o : S₁ .out = b :: S .out := by
      simp only [S₁, Function.update_self]
    have hrest := ih { v with flag := true, bit := b } S₁ hS₁b
    rw [hS₁o] at hrest
    have hEq : update (update S₁ .outBuf []) .out (bs.reverse ++ b :: S .out) =
        update (update S .outBuf []) .out ((b :: bs).reverse ++ S .out) := by
      ext k
      by_cases hko : k = .out
      · subst hko; simp [List.reverse_cons, List.append_assoc]
      · rw [Function.update_of_ne hko, Function.update_of_ne hko]
        by_cases hkb : k = .outBuf
        · subst hkb; simp
        · simp [S₁, Function.update_of_ne hkb, Function.update_of_ne hko]
    rw [hEq] at hrest
    simpa [List.length_cons, Nat.add_assoc] using ReachesIn.step_head hstep hrest

end GI.Turing.TM
