import Workspace.Impl.LinIntBasis

/-! Assemble the integer relation rows from cyclic orders and SLP exponents. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linRelationsStep (basis sub : ℕ) : Expr :=
  .letE (.call basis (mk3 (arg 1) (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.length (.get (arg 0) (.nat 0)))))
    (.snoc (arg 2) (.call sub (mk2 (.var 1) (.get (.get (arg 0) (.nat 1)) (arg 1)))))

def linRelationsFuns (b basis sub : ℕ) : List Expr :=
  loopFuns b (.length (arg 0)) .nil (linRelationsStep basis sub)

def linRelationsBasisArg (W n : ℕ) : ℕ := 10 * (W + n + 1)
def linRelationsBasisCost (W n : ℕ) : ℕ := linBasisCost (linRelationsBasisArg W n) n
def linRelationsSubArg (W n : ℕ) : ℕ := 10 * (W + linRelationsBasisCost W n + 1)
def linRelationsRowCost (W n : ℕ) : ℕ :=
  linVectorBinaryCost (linRelationsSubArg W n) n (20 * (linRelationsSubArg W n + 2))
def linRelationsAccWt (W n : ℕ) : ℕ := linVectorAccWt n (linRelationsRowCost W n)
def linRelationsStepCost (W n : ℕ) : ℕ :=
  1000 * (W + n + linRelationsBasisCost W n + linRelationsRowCost W n + linRelationsAccWt W n + 1)
def linRelationsCost (W n : ℕ) : ℕ :=
  n * linRelationsStepCost W n + loopModK * (n + 1) * (W + n + linRelationsAccWt W n + 1)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 200000 in
theorem linRelations_spec {P : Program} {b basis sub ib n : ℕ}
    (hp : P.HasAt b (linRelationsFuns b basis sub))
    (hb : P.HasAt basis (linBasisFuns basis)) (hi : linIntSpec P ib)
    (hs : P.HasAt sub (linVectorBinaryFuns sub (ib + 12)))
    (e : Fin n → ℕ) (C : Matrix (Fin n) (Fin n) ℤ) :
    FunDet P b (.list [linVecVal (fun i => (e i : ℤ)), encIntMatrix C])
      (encIntMatrix (linRelationMatrix e C))
      (linRelationsCost (Val.list [linVecVal (fun i => (e i : ℤ)), encIntMatrix C]).wt n) := by
  let ev := linVecVal (fun i => (e i : ℤ))
  let a := Val.list [ev, encIntMatrix C]
  let W := a.wt
  let rows := (List.finRange n).map fun i => linVecVal (linRelationMatrix e C i)
  let M := linRelationsAccWt W n
  have we : ev.wt < W := wt_le_wt_list (by simp)
  have wc : (encIntMatrix C).wt < W := wt_le_wt_list (by simp)
  have wcoef (i : Fin n) : (linVecVal (C i)).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)).trans wc
  have hrow (i : Fin n) : FunDet P sub
      (.list [linVecVal (Pi.single i (e i : ℤ)), linVecVal (C i)])
      (linVecVal (linRelationMatrix e C i)) (linRelationsRowCost W n) := by
    have went : (encInt (e i : ℤ)).wt < W := (linVecEntryWt (fun i => (e i : ℤ)) i).trans we
    have wbi := wt_list3_le (.nat i.val) (encInt (e i : ℤ)) (.nat n)
    have win : (Val.list [.nat i.val, encInt (e i : ℤ), .nat n]).wt ≤ linRelationsBasisArg W n := by
      have wn := wt_nat_le n
      have wi := wt_nat_le i.val
      have hii := i.isLt
      unfold linRelationsBasisArg
      omega
    have hbs := (linBasis_spec hb i (e i : ℤ)).mono (show
      linBasisCost (Val.list [.nat i.val, encInt (e i : ℤ), .nat n]).wt n ≤ linRelationsBasisCost W n by
        unfold linRelationsBasisCost linBasisCost
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    have wb := hbs.wt_lt.le
    have wsi := wt_list2_le (linVecVal (Pi.single i (e i : ℤ))) (linVecVal (C i))
    have wsub : (Val.list [linVecVal (Pi.single i (e i : ℤ)), linVecVal (C i)]).wt ≤ linRelationsSubArg W n := by
      unfold linRelationsSubArg
      have := wcoef i
      omega
    exact (linVectorSub_spec hi hs (Pi.single i (e i : ℤ)) (C i)).mono
      (linVectorBinaryCost_mono wsub le_rfl (by omega :
        20 * ((Val.list [linVecVal (Pi.single i (e i : ℤ)), linVecVal (C i)]).wt + 2) ≤
        20 * (linRelationsSubArg W n + 2)))
  have wrow (i : Fin n) : (linVecVal (linRelationMatrix e C i)).wt ≤ linRelationsRowCost W n := (hrow i).wt_lt.le
  have wacc (k : ℕ) : (Val.list (rows.take k)).wt ≤ M := by
    have h := linWtList (vs := rows.take k) (B := linRelationsRowCost W n) (by
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv)
      exact wrow i)
    have hl : (rows.take k).length ≤ n := by simp [rows]
    exact h.trans (by
      unfold M linRelationsAccWt linVectorAccWt
      have hm := Nat.mul_le_mul_right (linRelationsRowCost W n) hl
      omega)
  have dl := Det.length (Det.arg' (P := P) (vs := [ev, encIntMatrix C]) (rest := []) (j := 0) rfl)
  simp only [ev, List.length_map, List.length_finRange] at dl
  have hlp := loopBdd_spec hp dl Det.nil (by
    have := a.two_le_size
    have := a.size_le_wt
    simp only [a, ev] at *
    omega)
    (Inv := fun k acc => acc = .list (rows.take k)) (M := M) (D := fun _ => linRelationsStepCost W n)
    (by simp) (fun k acc _ he => he ▸ wacc k) (fun k acc hk he => ?_)
  · refine hlp.mono fun out cost ho => ⟨?_, ?_⟩
    · have hlen : rows.length = n := by simp [rows]
      simpa only [← hlen, List.take_length] using ho.1
    · simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, linRelationsCost] using ho.2
  · subst acc
    let i : Fin n := ⟨k, hk⟩
    have wi := wt_nat_le k
    have wn := wt_nat_le n
    have went : (encInt (e i : ℤ)).wt < W := (linVecEntryWt (fun i => (e i : ℤ)) i).trans we
    have wbi := wt_list3_le (.nat k) (encInt (e i : ℤ)) (.nat n)
    have win : (Val.list [.nat k, encInt (e i : ℤ), .nat n]).wt ≤ linRelationsBasisArg W n := by
      unfold linRelationsBasisArg; omega
    have hbs := (linBasis_spec hb i (e i : ℤ)).mono (show
      linBasisCost (Val.list [.nat k, encInt (e i : ℤ), .nat n]).wt n ≤ linRelationsBasisCost W n by
        unfold linRelationsBasisCost linBasisCost
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    have wb := hbs.wt_lt.le
    have darg (j : ℕ) (rest : List Val) {v : Val} (hv : [a, .nat k, .list (rows.take k)][j]? = some v) :=
      Det.arg' (P := P) (vs := [a, .nat k, .list (rows.take k)]) (rest := rest) (j := j) hv
    have dev := Det.get' (darg 0 [] rfl) (Det.nat 0) rfl
    -- Integer entries use the same finite-range indexing, with encInt rather than nat.
    have de' := Det.get' dev (darg 1 [] rfl) (show
      ((List.finRange n).map fun j => encInt (e j : ℤ))[k]? = some (encInt (e i : ℤ)) by
        rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk)]
        simp [i])
    have dlen := Det.length dev
    simp only [ev, List.length_map, List.length_finRange] at dlen
    have db := Det.call (Det.mk3 (darg 1 [] rfl) de' dlen) hbs
    have dcm := Det.get' (darg 0 [linVecVal (Pi.single i (e i : ℤ))] rfl) (Det.nat 1) rfl
    have dci := Det.get' dcm (darg 1 [linVecVal (Pi.single i (e i : ℤ))] rfl) (show
      ((List.finRange n).map fun j => linVecVal (C j))[k]? = some (linVecVal (C i)) by
        rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk)]
        simp [i])
    have ds := Det.call (Det.mk2
      (Det.var' (P := P) (env := [.list [a, .nat k, .list (rows.take k)], linVecVal (Pi.single i (e i : ℤ))]) (i := 1) rfl) dci) (hrow i)
    have da := darg 2 [linVecVal (Pi.single i (e i : ℤ))] rfl
    have step := Det.letE db (Det.snoc da ds)
    have hout : rows.take (k + 1) = rows.take k ++ [linVecVal (linRelationMatrix e C i)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [rows]; exact hk)]
      simp [rows, i]
    refine step.post fun cost hc => ⟨?_, ?_⟩
    · dsimp only
      rw [hout]
    · have wa := wt_list3_le a (.nat k) (.list (rows.take k))
      have wcur := wacc k
      have wnext := wacc (k + 1)
      rw [hout] at wnext
      have wc' := wcoef i
      have wr := wrow i
      have wsub := wt_list2_le (linVecVal (Pi.single i (e i : ℤ))) (linVecVal (C i))
      change cost ≤ linRelationsStepCost W n + 100 * (W + n + M + 1)
      unfold linRelationsStepCost
      simp only [ev, W, a, i] at *
      omega

end GI.Impl

namespace GI.Impl
open GI.Cited GI.Lang

/-- The relation assembler's output meets the presentation theorem's hypotheses.
The caller supplies the quotient map, SLP relation proofs and chain-order product. -/
theorem linRelationsPresentation_spec {P : Program} {b basis sub ib n : ℕ}
    (hp : P.HasAt b (linRelationsFuns b basis sub))
    (hb : P.HasAt basis (linBasisFuns basis)) (hi : linIntSpec P ib)
    (hs : P.HasAt sub (linVectorBinaryFuns sub (ib + 12)))
    (e : Fin n → ℕ) (he : ∀ i, 0 < e i)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : linEarlierCoefficients C)
    {Q : Type*} [AddCommGroup Q] (f : (Fin n → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f)
    (hrel : ∀ i, f (Pi.single i (e i : ℤ)) = f (C i))
    (hcard : Nat.card Q = ∏ i, e i) :
    FunAll P b (.list [linVecVal (fun i => (e i : ℤ)), encIntMatrix C])
      (fun out cost => out = encIntMatrix (linRelationMatrix e C) ∧
        Nonempty (((Fin n → ℤ) ⧸ linRelations (linRelationMatrix e C)) ≃ₗ[ℤ] Q) ∧
        cost ≤ linRelationsCost (Val.list [linVecVal (fun i => (e i : ℤ)), encIntMatrix C]).wt n) := by
  refine FunAll.mono (linRelations_spec hp hb hi hs e C) fun out cost ho => ?_
  exact ⟨ho.1, ⟨linCyclicPresentationEquiv e he C hC f hf hrel hcard⟩, ho.2⟩

end GI.Impl
