module

public import Workspace.Impl.AggItemCiCfgOs

@[expose] public section

/-!
# The configuration query: the overcoset from the extension and the generators

`itcqOuF fnd par cmp sch` on `[σ₀, S, w]` (`σ₀ = itciExt X Y p₁` and `S` a generator list of
`itciMG X`) returns the finished result with the overcosets `itcqOs X σ₀ S` and the kept
value `w` (`itcq_ouF_spec`):
* it finds the first odd entry `t` of `S` (`find` with the parity, `itcqOdT`);
* the representative is `σ₀` if `σ₀` is even, `σ₀ t` if `σ₀` is odd and `t` exists, and there is
  no overcoset otherwise (`itcqRep`);
* the generators of the even part are the Schreier list of `t` (`itSchF`, costed by
  `itcq_sch_spec`), or `S` itself if all entries are even (`itcqEG`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- On `[c, encPerm s]`: the parity of `s`. -/
def itcqOdT (par : ℕ) : Expr := .call par (arg 1)

/-- The finished result `[0, [⟨⟩, ⟨[σ, E]⟩, w]]` with one overcoset. -/
def itcqRes1 (σ E : Expr) : Expr := mk2 (.nat 0) (mk3 .nil (.snoc .nil (mk2 σ E)) (arg 2))

/-- The finished result `[0, [⟨⟩, ⟨⟩, w]]` with no overcoset. -/
def itcqRes0 : Expr := mk2 (.nat 0) (mk3 .nil .nil (arg 2))

/-- **The overcoset program** on `[σ₀, S, w]`. -/
def itcqOuF (fnd par cmp sch : ℕ) : Expr :=
  .letE (.call fnd (mk2 .nil (arg 1)))
  (.letE (.call par (arg 0))
  (.ite (.arith .lt (.var 1) (.length (arg 1)))
    (.letE (.call sch (mk2 (.get (arg 1) (.var 1)) (arg 1)))
      (.ite (.var 2)
        (itcqRes1 (.call cmp (mk2 (arg 0) (.get (arg 1) (.var 1)))) (.var 3))
        (itcqRes1 (arg 0) (.var 3))))
    (.ite (.var 2) itcqRes0 (itcqRes1 (arg 0) (arg 1)))))

/-- The odd test on values. -/
noncomputable def itcqOq (q : ℕ) (v : Val) : Bool :=
  @decide (∃ s : Perm (Fin q), v = encPerm s ∧ sign s ≠ 1) (Classical.propDecidable _)

theorem itcqOq_enc (s : Perm (Fin q)) : itcqOq q (encPerm s) = decide (sign s ≠ 1) := by
  unfold itcqOq
  rw [Bool.eq_iff_iff, @decide_eq_true_iff _ (Classical.propDecidable _), decide_eq_true_iff]
  constructor
  · rintro ⟨s', hs', h'⟩
    rwa [encPerm_injective hs']
  · intro h
    exact ⟨s, rfl, h⟩

theorem itcq_par_val (s : Perm (Fin q)) : itpNInv s % 2 = (decide (sign s ≠ 1)).toNat := by
  by_cases h : sign s = 1
  · have : ¬ itpNInv s % 2 ≠ 0 := fun h' => it_parity_ne.1 h' h
    simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.toNat_false]
    omega
  · have h1 := it_parity_ne.2 h
    simp only [h, ne_eq, not_false_eq_true, decide_true, Bool.toNat_true]
    omega

/-- The first odd entry, by its index. -/
theorem itcq_find_idx (S : List (Perm (Fin q))) :
    (∀ h : S.findIdx (fun s => decide (sign s ≠ 1)) < S.length,
      itcqOdd S = some S[S.findIdx (fun s => decide (sign s ≠ 1))]) ∧
    (¬ S.findIdx (fun s => decide (sign s ≠ 1)) < S.length → itcqOdd S = none) := by
  unfold itcqOdd
  induction S with
  | nil => simp
  | cons s S ih =>
    by_cases hs : sign s = 1
    · have e : (s :: S).findIdx (fun s => decide (sign s ≠ 1)) =
          S.findIdx (fun s => decide (sign s ≠ 1)) + 1 := by
        simp [List.findIdx_cons, hs]
      have e2 : (s :: S).find? (fun s => decide (sign s ≠ 1)) =
          S.find? (fun s => decide (sign s ≠ 1)) := by simp [hs]
      rw [e2]
      refine ⟨fun h => ?_, fun h => ih.2 (by simp only [e, List.length_cons] at h; omega)⟩
      have h' : S.findIdx (fun s => decide (sign s ≠ 1)) < S.length := by
        simp only [e, List.length_cons] at h; omega
      rw [ih.1 h']
      simp only [e, List.getElem_cons_succ]
    · have e : (s :: S).findIdx (fun s => decide (sign s ≠ 1)) = 0 := by
        simp [List.findIdx_cons, hs]
      have e2 : (s :: S).find? (fun s => decide (sign s ≠ 1)) = some s := by
        simp [hs]
      rw [e2]
      refine ⟨fun h => by simp only [e, List.getElem_cons_zero], fun h => ?_⟩
      rw [e] at h; simp at h

theorem itcq_findIdx_map (S : List (Perm (Fin q))) :
    (S.map encPerm).findIdx (itcqOq q) = S.findIdx (fun s => decide (sign s ≠ 1)) := by
  rw [List.findIdx_map]
  congr 1
  funext s
  exact itcqOq_enc s

/-- The cost bound of the overcoset program. -/
def itcqOuC (M : ℕ) : ℕ := 10 ^ 10 * (M + 1) ^ 6

section Prog

variable {P : Program}

/-- **The odd test**, in cost `itParC q + 10 (q + 1)²` (`40 (q+1)²` bounds the input weight). -/
theorem itcq_odT_spec {f par : ℕ} (hf : P.funs[f]? = some (itcqOdT par))
    (hpar : ∀ σ : Perm (Fin q), FunDet P par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q))
    (s : Perm (Fin q)) :
    FunDet P f (.list [.list [], encPerm s]) (boolVal (itcqOq q (encPerm s)))
      (itParC q + 200 * (q + 1) ^ 2) := by
  have hs := wt_encPerm_le s
  have hin := wt_list2_le (.list []) (encPerm s)
  simp only [wt_list_nil] at hin
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [.list [], encPerm s]) (j := 1) rfl
    (W := 30 * (q + 1) ^ 2) (by omega) (by omega) (by omega)
  have hv : boolVal (itcqOq q (encPerm s)) = .nat (itpNInv s % 2) := by
    rw [itcqOq_enc, itcq_par_val]
  rw [hv]
  have c := StDC.call A1 (hpar s) (by have := wt_nat_le (itpNInv s % 2); omega)
  exact StDC.funDet hf c (by omega)

end Prog

end GI.Impl
