module

public import Workspace.Degree.LayoutDeg
public import Workspace.Degree.Thread

@[expose] public section

/-!
# One program for all degrees, and `StringSolver`

The programs `degProg h dpE D` differ only in three functions: the case decision at `dgb 4` and the
two functions of the root at `dgb 40` and `dgb 41` hold the number `D` in their text. This file
builds one program `strProg h` that takes `D` as an extra input of each function
(`Degree/Thread.lean`). Each function of `strProg h` is `thrBody (thr b)` for the function `b` of
`degProg h dpE 0`, except for the three functions above. There the number `D` becomes a read of `D`
(`.var 1`).

`strProg_rel` says that `strProg h` is `degProg h dpE D` with the degree in the environment, for
every `D`. With `dp_root` and `FunAll.thread` this gives `stringSolver`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang
open GI.Cited (Val gens)

set_option maxRecDepth 100000

/-! ### Lists of related functions -/

/-- The relation between a function of `P` and the function of `P'` at the same index. -/
def FunRel (D : ℕ) (b b' : Expr) : Prop := ∃ e, Rel D b e ∧ b' = thrBody e

/-- The usual text of a function with the degree in the environment. -/
def dpT (b : Expr) : Expr := thrBody (thr b)

theorem funRel_map (D : ℕ) : ∀ l : List Expr, List.Forall₂ (FunRel D) l (l.map dpT)
  | [] => .nil
  | b :: l => .cons ⟨_, rel_thr D b, rfl⟩ (funRel_map D l)

theorem forall₂_append' {R : Expr → Expr → Prop} {l₁ l₂ m₁ m₂ : List Expr}
    (h₁ : List.Forall₂ R l₁ m₁) (h₂ : List.Forall₂ R l₂ m₂) :
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem forall₂_set' {R : Expr → Expr → Prop} {l m : List Expr} (h : List.Forall₂ R l m)
    {a b : Expr} (hab : R a b) : ∀ i, List.Forall₂ R (l.set i a) (m.set i b) := by
  induction h with
  | nil => intro i; exact .nil
  | cons h _ ih =>
    intro i
    cases i with
    | zero => exact .cons hab ‹_›
    | succ i => exact .cons h (ih i)

theorem forall₂_getElem? {R : Expr → Expr → Prop} {l m : List Expr} (h : List.Forall₂ R l m) :
    ∀ (f : ℕ) (b : Expr), l[f]? = some b → ∃ b', R b b' ∧ m[f]? = some b' := by
  induction h with
  | nil => intro f b hb; simp at hb
  | cons hab _ ih =>
    intro f b hb
    cases f with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      exact ⟨_, hab, rfl⟩
    | succ f => simpa using ih f b (by simpa using hb)

theorem progRel_of {D : ℕ} {P P' : Program} (hp : P'.prims = P.prims)
    (hf : List.Forall₂ (FunRel D) P.funs P'.funs) : ProgRel D P P' where
  prims := hp
  funs f body hb := by
    obtain ⟨b', ⟨e, hr, rfl⟩, h⟩ := forall₂_getElem? hf f body hb
    exact ⟨e, hr, h⟩

/-! ### The two functions of the root that hold `D` -/

/-! The case decision is threaded in `Degree/CaseD.lean` (`caseDT`, `rel_caseD`). -/

theorem rel_mk1 {D : ℕ} {a a' : Expr} (ha : Rel D a a') : Rel D (mk1 a) (mk1 a') := .snoc .nil ha

theorem rel_mk2 {D : ℕ} {a a' b b' : Expr} (ha : Rel D a a') (hb : Rel D b b') :
    Rel D (mk2 a b) (mk2 a' b') := .snoc (rel_mk1 ha) hb

theorem rel_mk3 {D : ℕ} {a a' b b' c c' : Expr} (ha : Rel D a a') (hb : Rel D b b')
    (hc : Rel D c c') : Rel D (mk3 a b c) (mk3 a' b' c') := .snoc (rel_mk2 ha hb) hc

theorem rel_mk4 {D : ℕ} {a a' b b' c c' d d' : Expr} (ha : Rel D a a') (hb : Rel D b b')
    (hc : Rel D c c') (hd : Rel D d d') : Rel D (mk4 a b c d) (mk4 a' b' c' d') :=
  .snoc (rel_mk3 ha hb hc) hd

theorem rel_clampE {D : ℕ} {x x' d d' : Expr} (hx : Rel D x x') (hd : Rel D d d') :
    Rel D (clampE x d) (clampE x' d') :=
  .ite (.length hx)
    (rel_mk1 (rel_mk4 (.get (.get hx (.nat 0)) (.nat 0)) (.get (.get hx (.nat 0)) (.nat 1))
      (.ite (.arith .lt (.get (.get hx (.nat 0)) (.nat 2)) hd) (.get (.get hx (.nat 0)) (.nat 2)) hd)
      (.nat 0)))
    hx

/-- The top of the root with the degree in the environment. -/
def rootTopThr (fs rf N₀ : ℕ) : Expr :=
  .ite (thr (.arith .lt (.nat N₀) (.get (.var 0) (.nat 0))))
    (.ite (.arith .lt (.var 1) (thr (.get (.var 0) (.nat 0)))) (thr (.call rf (.var 0)))
      (thr (.call fs (.var 0))))
    (thr (.call fs (.var 0)))

theorem rel_rootTopThr (D fs rf N₀ : ℕ) : Rel D (rootTopBody fs rf N₀ (.nat D)) (rootTopThr fs rf N₀) :=
  .ite (rel_thr D _) (.ite (.arith .lt .degree (rel_thr D _)) (rel_thr D _) (rel_thr D _))
    (rel_thr D _)

/-- The fresh phase of the root with the degree in the environment. -/
def rootFreshThr (prep cont lift : ℕ) : Expr :=
  .letE (thr (.call prep (.var 0)))
  (.letE (clampE (thr (.get (.get (.var 1) (.nat 3)) (.nat 5))) (.var 1))
  (thr (.letE (Expr.mkList [.get (.get (.var 1) (.nat 3)) (.nat 0), .get (.get (.var 1) (.nat 3)) (.nat 1),
      .get (.get (.var 1) (.nat 3)) (.nat 2), .get (.get (.var 1) (.nat 3)) (.nat 3),
      .get (.get (.var 1) (.nat 3)) (.nat 4), .var 2, .get (.get (.var 1) (.nat 3)) (.nat 6),
      .get (.get (.var 1) (.nat 3)) (.nat 7), .get (.get (.var 1) (.nat 3)) (.nat 8),
      .get (.get (.var 1) (.nat 3)) (.nat 9)])
  (.letE (.call cont (.var 3))
    (.call lift (mk2 (mk4 (arg 0) (.get (.var 1) (.nat 2)) (.get (.var 1) (.nat 1))
      (.get (.var 1) (.nat 0))) (.var 4)))))))

theorem rel_rootFreshThr (D prep cont lift : ℕ) :
    Rel D (rootFreshBody prep cont lift (.nat D)) (rootFreshThr prep cont lift) :=
  .letE (rel_thr D _) (.letE (rel_clampE (rel_thr D _) .degree) (rel_thr D _))

/-! ### The program -/

/-- The functions of `degProg` before the new functions. -/
noncomputable abbrev dpHead : List Expr :=
  asmPad asmSlot asmCore ++ asmPad asmSlot gsGen ++ asmPad asmSlot cRow ++ asmPad 2000000 cAgg

/-- The new functions after the singles. -/
noncomputable abbrev degRest (E : ℕ) : List Expr :=
  asmPad 10 (foldlFuns (dgb 100) (dgb 15)) ++
    asmPad 10 (mapFuns (dgb 110) (dgb 16)) ++ asmPad 20 (degTestFuns (dgb 120) E) ++
    asmPad 10 (mapFuns (dgb 140) (dgb 13)) ++ asmPad 10 (mapFuns (dgb 150) (dgb 14)) ++
    asmPad 10 (log2Funs (dgb 160)) ++ mapFuns (dgb 170) (dgb 30)

theorem dp_funs_eq (h : JohnsonRecognition) (E D : ℕ) : (degProg h E D).funs =
    dpHead ++ (degSingles degJr D ++ (List.replicate 58 .nil ++ degRest E)) := by
  simp only [degProg, asmProg, degFuns, List.append_assoc]
  congr 4

theorem degSingles_set (jr D : ℕ) : degSingles jr D =
    (((degSingles jr 0).set 4 (caseDE (dgb 120) jr D)).set 40
      (rootTopBody 0 (dgb 41) P₀.N₀ (.nat D))).set 41 (rootFreshBody 9 (dgb 0) 289 (.nat D)) :=
  rfl

/-- The singles with the degree in the environment. -/
noncomputable def degSinglesT (jr : ℕ) : List Expr :=
  ((((degSingles jr 0).map dpT).set 4 (thrBody (caseDT (dgb 120) jr))).set 40
    (thrBody (rootTopThr 0 (dgb 41) P₀.N₀))).set 41 (thrBody (rootFreshThr 9 (dgb 0) 289))

/-- **The program of the string theorem**, for the recognition `h`. It takes `[D, v]`. -/
noncomputable def strProg (h : JohnsonRecognition) : Program where
  funs := dpHead.map dpT ++ (degSinglesT degJr ++ (List.replicate 58 Expr.nil ++ degRest dpE).map dpT)
  prims := (degProg h dpE 0).prims

/-- **`strProg h` is `degProg h dpE D` with the degree in the environment**, for every `D`. -/
theorem strProg_rel (h : JohnsonRecognition) (D : ℕ) : ProgRel D (degProg h dpE D) (strProg h) := by
  refine progRel_of rfl ?_
  rw [dp_funs_eq]
  refine forall₂_append' (funRel_map D _) (forall₂_append' ?_ (funRel_map D _))
  rw [degSingles_set]
  exact forall₂_set' (forall₂_set' (forall₂_set' (funRel_map D _) ⟨_, rel_caseD _ _ D, rfl⟩ 4)
    ⟨_, rel_rootTopThr D _ _ _, rfl⟩ 40) ⟨_, rel_rootFreshThr D _ _ _, rfl⟩ 41

/-! ### The string theorem -/

theorem size_stringState {k : ℕ} (G : Subgroup (Equiv.Perm (Fin k))) (x y : Fin k → ℕ) :
    (stringState G x y).size = k := by
  simp [State.size, stringState]

/-- The cost bound after threading. -/
theorem thread_cost_le {C : ℝ} (hC : 0 ≤ C) (K m D k w : ℕ) {c c₀ : ℕ}
    (hc₀ : (c₀ : ℝ) ≤ Real.exp (C * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) * K *
      ((w : ℝ) + 1) ^ m)
    (hc : c ≤ threadM D * c₀ + 6 * ((Val.nat D).wt + w) + 40) :
    (c : ℝ) ≤ Real.exp ((C + 2) * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) *
      ((6400 * K + 52 : ℕ) : ℝ) * ((w : ℝ) + 1) ^ (m + 1) := by
  set L := Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2) with hL
  have hk2 : (1 / 2 : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
    have h2 : Real.log 2 ≤ Real.log ((k : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    have := Real.log_two_gt_d9
    linarith
  have hD0 : 0 ≤ Real.log ((D : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  have hL0 : 0 ≤ L := mul_nonneg (by linarith) hD0
  -- `D + 2 ≤ exp (2 L)`, since `log (D + 2) ≤ 2 L`.
  have hDe : (D : ℝ) + 2 ≤ Real.exp (2 * L) := by
    have h1 : Real.log ((D : ℝ) + 2) ≤ 2 * L := by rw [hL]; nlinarith
    calc (D : ℝ) + 2 = Real.exp (Real.log ((D : ℝ) + 2)) :=
          (Real.exp_log (by have := Nat.cast_nonneg (α := ℝ) D; linarith)).symm
      _ ≤ Real.exp (2 * L) := Real.exp_le_exp.2 h1
  have hwD : ((Val.nat D).wt : ℝ) ≤ D + 2 := by exact_mod_cast wt_nat_le D
  have hM : (threadM D : ℝ) ≤ 6400 * ((D : ℝ) + 2) := by
    have : (threadM D : ℝ) = 200 * (((Val.nat D).wt : ℝ) + 30) := by
      unfold threadM; push_cast; ring
    rw [this]
    have := Nat.cast_nonneg (α := ℝ) D
    nlinarith
  have hw1 : (1 : ℝ) ≤ (w : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) w; linarith
  have hpm : ((w : ℝ) + 1) ^ m ≤ ((w : ℝ) + 1) ^ (m + 1) :=
    pow_le_pow_right₀ hw1 (Nat.le_succ m)
  have hp1 : (w : ℝ) + 1 ≤ ((w : ℝ) + 1) ^ (m + 1) := by
    simpa using pow_le_pow_right₀ hw1 (Nat.succ_le_succ (Nat.zero_le m))
  have hp0 : (1 : ℝ) ≤ ((w : ℝ) + 1) ^ (m + 1) := one_le_pow₀ hw1
  have hE2 : Real.exp (2 * L) ≤ Real.exp ((C + 2) * L) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hEsplit : Real.exp ((C + 2) * L) = Real.exp (2 * L) * Real.exp (C * L) := by
    rw [← Real.exp_add]; ring_nf
  have hE1 : 1 ≤ Real.exp ((C + 2) * L) := Real.one_le_exp (by nlinarith)
  have hEC : 0 ≤ Real.exp (C * L) := (Real.exp_pos _).le
  have hc₀' : (c₀ : ℝ) ≤ Real.exp (C * L) * K * ((w : ℝ) + 1) ^ m := by
    rw [hL]; simpa [mul_assoc] using hc₀
  have hcR : (c : ℝ) ≤ (threadM D : ℝ) * c₀ + 6 * (((Val.nat D).wt : ℝ) + w) + 40 := by
    exact_mod_cast hc
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
  -- The main term.
  have t1 : (threadM D : ℝ) * c₀ ≤
      6400 * K * (Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1)) := by
    calc (threadM D : ℝ) * c₀ ≤ 6400 * ((D : ℝ) + 2) * (Real.exp (C * L) * K * ((w : ℝ) + 1) ^ m) :=
          mul_le_mul hM hc₀' hc0 (by positivity)
      _ ≤ 6400 * Real.exp (2 * L) * (Real.exp (C * L) * K * ((w : ℝ) + 1) ^ (m + 1)) := by
          gcongr
      _ = 6400 * K * (Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1)) := by
          rw [hEsplit]; ring
  -- The other terms.
  have t2 : 6 * (((Val.nat D).wt : ℝ) + w) + 40 ≤
      52 * (Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1)) := by
    have a1 : 6 * ((D : ℝ) + 2) ≤ 6 * (Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1)) := by
      have : Real.exp (2 * L) ≤ Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1) := by
        nlinarith
      linarith
    have a2 : 46 * ((w : ℝ) + 1) ≤ 46 * (Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1)) := by
      have : (w : ℝ) + 1 ≤ Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1) := by nlinarith
      linarith
    nlinarith
  have : (c : ℝ) ≤ (6400 * K + 52) * (Real.exp ((C + 2) * L) * ((w : ℝ) + 1) ^ (m + 1)) := by
    nlinarith
  calc (c : ℝ) ≤ _ := this
    _ = _ := by rw [hL]; push_cast; ring_nf

/-- **The string theorem of the paper**, as the graph program calls it: function `dgb 40` of
`strProg h` meets `StringSolver`. -/
theorem stringSolver (h : JohnsonRecognition) : StringSolver (strProg h) (dgb 40) := by
  obtain ⟨C, K, m, hC, hr⟩ := dp_root h
  refine ⟨C + 2, 6400 * K + 52, m + 1, by linarith, fun D k gs x y hD hgs hG hxy => ?_⟩
  have hcan := canon_stringVal gs x y hgs hxy
  have h1 := hr D hD (stringState (gens gs) x y) k (Equiv.refl _) id Function.injective_id hG
    (size_stringState _ x y) _ hcan.stateVal
  refine (FunAll.thread (strProg_rel h D) h1).mono ?_
  rintro u c ⟨c₀, ⟨hA, hc₀⟩, hc⟩
  exact ⟨hA, thread_cost_le hC K m D k _ hc₀ hc⟩

end GI.Degree
