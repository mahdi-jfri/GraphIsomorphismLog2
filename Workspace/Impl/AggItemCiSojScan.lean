module

public import Workspace.Impl.AggItemCiSojOne

@[expose] public section

/-!
# One scan for the cut test and the imprimitive choice

In a good configuration, an off-diagonal disconnected color has balanced equal
components. Thus no imprimitive pair exists exactly when the literal primitive-cut
predicate holds. The forward scan both decides that predicate and fixes the first
pair used by the imprimitive branch.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Finset
open GI.Cited (Val)

variable {q : ℕ}

/-- The cut predicate fails exactly when the imprimitive-pair scan succeeds. -/
theorem itcs_imp_cut_iff (X : PairCfg q) (hX : X.Good deltaB) {x₀ : Fin q} (hx : x₀ ∈ X.fiber) :
    (∃ a b, ImpPair X a b) ↔ ¬ PrimitiveColorCuts X.coloring false := by
  constructor
  · rintro ⟨a, b, hab⟩ hp
    have hm := (itcs_primitive_one X hx).1 hp a b hab.1
    have hs := ((itcs_imp_one X hX hx a b).1 hab).2
    rw [hm] at hs
    have hi := (X.idx hx).isLt
    omega
  · exact itcs_imp_exists hX

open Classical in
/-- The predicate of the forward pair scan, on values. -/
noncomputable def itcsImpQ (X : PairCfg q) : Val → Bool
  | .nat t => if ht : t < X.fiber.card * X.fiber.card then
      decide (ImpPair X ((itciPE X.fiber.card).symm ⟨t, ht⟩).1
        ((itciPE X.fiber.card).symm ⟨t, ht⟩).2) else false
  | _ => false

open Classical in
/-- The scan's predicate is exactly the pair predicate at every valid index. -/
theorem itcs_impQ_iff (X : PairCfg q) (t : Fin (X.fiber.card * X.fiber.card)) :
    itcsImpQ X (.nat t) = true ↔
      ImpPair X ((itciPE X.fiber.card).symm t).1 ((itciPE X.fiber.card).symm t).2 := by
  simp only [itcsImpQ, dif_pos t.isLt, decide_eq_true_eq]

/-- The forward scan index, with `n²` as its no-hit value. -/
noncomputable def itcsImpScan (X : PairCfg q) : ℕ :=
  ((List.range (X.fiber.card * X.fiber.card)).map Val.nat).findIdx (itcsImpQ X)

/-- Scan failure tests exactly the model's cut predicate. -/
theorem itcs_imp_scan_primitive (X : PairCfg q) (hX : X.Good deltaB)
    {x₀ : Fin q} (hx : x₀ ∈ X.fiber) :
    itcsImpScan X = X.fiber.card * X.fiber.card ↔ PrimitiveColorCuts X.coloring false := by
  classical
  have hn : itcsImpScan X = X.fiber.card * X.fiber.card ↔ ¬ ∃ a b, ImpPair X a b := by
    unfold itcsImpScan
    have hi := List.findIdx_eq_length (p := itcsImpQ X)
      (xs := (List.range (X.fiber.card * X.fiber.card)).map Val.nat)
    simp only [List.length_map, List.length_range] at hi
    rw [hi]
    constructor
    · intro h ⟨a, b, hab⟩
      let t := itciPE X.fiber.card (a, b)
      have hfalse := h (.nat t) (List.mem_map.2 ⟨t, List.mem_range.2 t.isLt, rfl⟩)
      have htrue : itcsImpQ X (.nat t) = true := (itcs_impQ_iff X t).2 (by
        simpa only [t, Equiv.symm_apply_apply] using hab)
      simp only [hfalse, Bool.false_eq_true] at htrue
    · intro h w hw
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
      have ht := List.mem_range.1 ht
      by_cases hh : itcsImpQ X (.nat t) = true
      · have hp := (itcs_impQ_iff X ⟨t, ht⟩).1 hh
        exact False.elim (h ⟨_, _, hp⟩)
      · exact Bool.eq_false_iff.2 hh
  rw [hn, itcs_imp_cut_iff X hX hx, not_not]

/-- A successful forward scan returns the index of the fixed implication choice. -/
theorem itcs_imp_scan_first (X : PairCfg q) (h : ∃ a b, ImpPair X a b) :
    itcsImpScan X = (itciPE X.fiber.card (itcsImp X h).1 : ℕ) := by
  classical
  let t₀ := itciPE X.fiber.card (itcsImp X h).1
  have ht₀ : itcsImpQ X (.nat t₀) = true := (itcs_impQ_iff X t₀).2 (by
    simpa only [t₀, Equiv.symm_apply_apply] using (itcsImp X h).2)
  unfold itcsImpScan
  apply (List.findIdx_eq (i := (t₀ : ℕ)) (by simp only [List.length_map, List.length_range]; exact t₀.isLt)).2
  constructor
  · simpa only [List.getElem_map, List.getElem_range] using ht₀
  · intro j hj
    simp only [List.getElem_map, List.getElem_range]
    by_cases hp : itcsImpQ X (.nat j) = true
    · have hjn : j < X.fiber.card * X.fiber.card := hj.trans t₀.isLt
      have himp := (itcs_impQ_iff X ⟨j, hjn⟩).1 hp
      have hmin := itcs_imp_first X h ((itciPE X.fiber.card).symm ⟨j, hjn⟩).1
        ((itciPE X.fiber.card).symm ⟨j, hjn⟩).2 himp
      have hm : (t₀ : ℕ) ≤ j := by
        simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using Fin.le_def.1 hmin
      exact False.elim (Nat.not_lt_of_ge hm hj)
    · exact Bool.eq_false_iff.2 hp

/-- The search program has exactly this scan result. The callback's numeric test
is supplied separately by its component-count program. -/
theorem itcs_imp_scan_prog {Pg : Program} {fd ft : ℕ}
    (hd : Pg.HasAt fd (findFuns fd ft)) (X : PairCfg q) (ctx : Val) {Ct : ℕ}
    (ht : ∀ t ∈ List.range (X.fiber.card * X.fiber.card),
      FunDet Pg ft (.list [ctx, .nat t]) (boolVal (itcsImpQ X (.nat t))) Ct) :
    FunDet Pg fd (.list [ctx, natList (List.range (X.fiber.card * X.fiber.card))])
      (.nat (itcsImpScan X))
      (X.fiber.card * X.fiber.card * Ct + loopModK * (X.fiber.card * X.fiber.card + 1) *
        ((Val.list [ctx, natList (List.range (X.fiber.card * X.fiber.card))]).wt +
          2 * (X.fiber.card * X.fiber.card) + 3)) := by
  have h := find_spec hd (c := ctx)
    (xs := (List.range (X.fiber.card * X.fiber.card)).map Val.nat)
    (q := itcsImpQ X) (B := fun _ => Ct) (fun w hw => by
      obtain ⟨t, ht', rfl⟩ := List.mem_map.1 hw
      exact ht t ht')
  simpa only [itcsImpScan, List.map_const', List.sum_replicate, List.length_map,
    List.length_range, smul_eq_mul, natList, FunDet] using h

end GI.Impl
