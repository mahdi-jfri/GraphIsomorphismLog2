import Workspace.Impl.AggItemCiCfgX

/-!
# The configuration query: the values the step program computes

The step program reads the answer `[x, encGroup gs]` of the pair-structure call and builds the
overcoset of `cfgItem` (Lemma A.12). It works with the list `itciL X` of the fiber points of `X`
followed by the other points, which is the permutation `itciEnum X` of `Fin q`:
* `itcqRho X a`: the permutation of the positions of `itciL X` that the lift `itciLift X a` gives;
  it is `a` on the first `n` positions and the identity on the others (`itcqRho_apply`). So
  `itciLift X a = itciEnum X * itcqRho X a * (itciEnum X)⁻¹` (`itcq_lift_rho`) and the
  extension `itciExt X Y p = itciEnum Y * itcqRho X p * (itciEnum X)⁻¹` (`itcq_ext_rho`).
* `a i` is read from a diagonal permutation `itciD n a` at the position `i (n + 1)` of `(i, i)`
  (`itcq_dec_val`).
* `itcqCs X`: the transpositions of two outer points of the same color, by one number
  `j ↦ (D[j / d], D[j % d])` with `D = itciFo X` (the identity when the colors differ); it has
  the same members as `itciCsw X` (`itcq_cs_mem`), so with the lifted generators it generates
  `itciMG X` (`itcq_mg_gens`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

noncomputable section

variable {q : ℕ}

/-! ### The points outside the fiber -/

/-- The test "not in the fiber" on values. -/
def itcqNq (X : PairCfg q) (v : Val) : Bool := !itcqFq X v

/-- The points outside the fiber in increasing order, as a value. -/
def itcqDR (X : PairCfg q) : Val := natList ((itciFl X.fiberᶜ).map Fin.val)

/-- The points outside the fiber by color (`itciFo`), as a value. -/
def itcqDV (X : PairCfg q) : Val := natList ((itciFo X).map Fin.val)

theorem itcq_nq_filter (X : PairCfg q) :
    ((List.range q).map Val.nat).filter (itcqNq X) =
      ((itciFl X.fiberᶜ).map Fin.val).map Val.nat := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.filter_map, itciFl, List.map_map]
  congr 2
  funext a
  simp [itcqNq, itcqFq, PairCfg.mem_fiber, a.isLt]

/-- The enumeration as a value: the fiber points, then the other points. -/
theorem itcq_enum_enc (X : PairCfg q) :
    encPerm (itciEnum X) = .list (((itciFl X.fiber).map Fin.val).map Val.nat ++
      ((itciFo X).map Fin.val).map Val.nat) := by
  rw [← List.map_append, ← List.map_append]
  unfold encPerm
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_append, itciFl_length,
      itciFo_length, Finset.card_add_card_compl, Fintype.card_fin]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_finRange, itciEnum_apply]
    rfl

/-! ### The positions of a lift -/

/-- The permutation of the positions of `itciL X` given by the lift of `a`. -/
def itcqRho (X : PairCfg q) (a : Perm (Fin X.fiber.card)) : Perm (Fin q) :=
  (itciEnum X)⁻¹ * itciLift X a * itciEnum X

theorem itcqRho_apply (X : PairCfg q) (a : Perm (Fin X.fiber.card)) (t : Fin q) :
    (itcqRho X a t : ℕ) = if h : t.1 < X.fiber.card then (a ⟨t.1, h⟩ : ℕ) else t.1 := by
  simp only [itcqRho, Perm.mul_apply]
  split_ifs with h
  · have e : itciEnum X t = X.emb rfl ⟨t.1, h⟩ := itciEnum_emb X rfl ⟨t.1, h⟩
    rw [e, itciLift_emb, ← itciEnum_emb X rfl (a ⟨t.1, h⟩), Perm.inv_apply_self]
  · have hout : itciEnum X t ∉ X.fiber := fun hm => h ((itciEnum_fiber X t).1 hm)
    rw [itciLift_out X a hout, Perm.inv_apply_self]

theorem itcq_lift_rho (X : PairCfg q) (a : Perm (Fin X.fiber.card)) :
    itciLift X a = itciEnum X * itcqRho X a * (itciEnum X)⁻¹ := by
  simp only [itcqRho, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

theorem itcq_ext_rho (X Y : PairCfg q) (p : Perm (Fin X.fiber.card)) :
    itciExt X Y p = itciEnum Y * itcqRho X p * (itciEnum X)⁻¹ := by
  simp only [itciExt, itciE0, itcqRho, mul_assoc, mul_inv_cancel, mul_one]

/-! ### Reading a diagonal permutation -/

theorem itcq_diag_lt {n i : ℕ} (hi : i < n) : i * (n + 1) < n * n := by
  have : i * (n + 1) = i + n * i := by ring
  rw [this]
  have := Nat.mul_le_mul_left n (show i ≤ n - 1 by omega)
  have e : n * (n - 1) + n = n * n := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.mul_succ]
  omega

/-- **The value of `a` at `i`** read from `itciD n a` at the position `i (n + 1)`. -/
theorem itcq_dec_val {n : ℕ} (a : Perm (Fin n)) (i : Fin n) :
    (itciD n a ⟨i.1 * (n + 1), itcq_diag_lt i.2⟩ : ℕ) / (n + 1) = a i := by
  have e : (⟨i.1 * (n + 1), itcq_diag_lt i.2⟩ : Fin (n * n)) = itciPE n (i, i) :=
    Fin.ext (by simp only [finProdFinEquiv_apply_val]; ring)
  have h2 : itciD n a (itciPE n (i, i)) = itciPE n (a i, a i) := by
    simp [itciD, toFin, Equiv.permCongr_apply, diagHom_apply]
  rw [e, h2, finProdFinEquiv_apply_val, show ((a i : ℕ) + n * (a i : ℕ)) = (a i : ℕ) * (n + 1) by
    ring, Nat.mul_div_cancel _ (by omega)]

/-! ### The transpositions of the outer classes, by number -/

/-- Entry `j` of the transpositions of the list `D`: `(D[j / |D|], D[j % |D|])` if the two points
have the same color in `X`, else the identity. -/
def itcqCsE (X : PairCfg q) (D : List (Fin q)) (j : ℕ) : Perm (Fin q) :=
  match D[j / D.length]?, D[j % D.length]? with
  | some a, some b => if X.col a a = X.col b b then swap a b else 1
  | _, _ => 1

/-- The transpositions of the outer points of the same color, by number. -/
def itcqCs (X : PairCfg q) : List (Perm (Fin q)) :=
  (List.range ((itciFo X).length * (itciFo X).length)).map (itcqCsE X (itciFo X))

theorem itcq_cs_mem (X : PairCfg q) (s : Perm (Fin q)) : s ∈ itcqCs X ↔ s ∈ itciCsw X := by
  set D := itciFo X with hD
  unfold itcqCs itciCsw
  rw [← hD, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.mem_range] at hj
    have hd : 0 < D.length := by
      rcases Nat.eq_zero_or_pos D.length with h | h
      · rw [h] at hj; omega
      · exact h
    have h1 : j / D.length < D.length := (Nat.div_lt_iff_lt_mul hd).2 hj
    have h2 : j % D.length < D.length := Nat.mod_lt _ hd
    refine ⟨D[j / D.length], List.getElem_mem h1, List.mem_map.2 ⟨D[j % D.length],
      List.getElem_mem h2, ?_⟩⟩
    simp only [itcqCsE, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
  · rintro ⟨a, ha, hs⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    have hd : 0 < D.length := by omega
    have e1 : (i * D.length + k) / D.length = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hk, zero_add]
    have e2 : (i * D.length + k) % D.length = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    refine ⟨i * D.length + k, List.mem_range.2 ?_, ?_⟩
    · have := Nat.mul_le_mul_right D.length (show i + 1 ≤ D.length by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    · simp only [itcqCsE, e1, e2, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hk]

/-- **The lifted generators and the transpositions of the outer classes generate `itciMG X`.** -/
theorem itcq_mg_gens (X : PairCfg q) {A : List (Perm (Fin X.fiber.card))}
    (hA : Subgroup.closure {a | a ∈ A} = itciAut X) :
    gens (A.map (itciLift X) ++ itcqCs X) = itciMG X := by
  rw [← itci_mg_closure X hA]
  unfold gens
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, List.mem_append, itcq_cs_mem]

theorem itciDec_one {n : ℕ} : itciDec (1 : Perm (Fin (n * n))) = 1 := by
  have := itciDec_D (n := n) 1
  rwa [map_one] at this

/-- Prepending the identity does not change the generated group. -/
theorem itcq_closure_one {n : ℕ} {gs : List (Perm (Fin (n * n)))} {H : Subgroup (Perm (Fin n))}
    (h : Subgroup.closure {a | a ∈ gs.map itciDec} = H) :
    Subgroup.closure {a | a ∈ (1 :: gs).map itciDec} = H := by
  rw [← h, List.map_cons, itciDec_one]
  have e : {a | a ∈ (1 : Perm (Fin n)) :: gs.map itciDec} = insert 1 {a | a ∈ gs.map itciDec} := by
    ext a; simp
  rw [e, Subgroup.closure_insert_one]

end

end GI.Impl
