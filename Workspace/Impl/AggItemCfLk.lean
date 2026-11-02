import Workspace.Impl.AggItemCfMath
import Workspace.Impl.AggStructDC

/-!
# Cases 2b and 3: the cache lookup

The cache of binary values is the list of the values `[⟨c_Y⟩, [⟨d⟩, ⟨d'⟩]]` of its entries
(`itCfEntV`). A key is looked up by `find` with the key test `itCfKeyF` (equality of the two
lists of numbers, `eqNats`): the result is the index of the first entry with that key, or the
length of the cache when there is none (`it_cfLk_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encKColoring)

variable {q : ℕ}

/-- The value of a cache entry: `[⟨key⟩, [⟨d⟩, ⟨d'⟩]]`. -/
def itCfEntV (a : ItCfEnt q) : Val :=
  .list [encKColoring a.1, .list [encKColoring a.2.1, encKColoring a.2.2]]

theorem itCfEntV_injective : Function.Injective (itCfEntV (q := q)) := by
  intro a b h
  simp only [itCfEntV, Val.list.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext (encKColoring_injective h1)
    (Prod.ext (encKColoring_injective h2) (encKColoring_injective h3))

/-- The values of a binary coloring, as a list of numbers. -/
def itCfKL (c : (Fin 2 → Fin q) → ℕ) : List ℕ :=
  (List.finRange (q ^ 2)).map fun j => c (finFunctionFinEquiv.symm j)

theorem itCf_encK_eq (c : (Fin 2 → Fin q) → ℕ) : encKColoring c = natList (itCfKL c) := by
  simp only [encKColoring, natList, itCfKL, List.map_map]
  rfl

theorem itCfKL_length (c : (Fin 2 → Fin q) → ℕ) : (itCfKL c).length = q ^ 2 := by
  simp [itCfKL]

theorem itCfKL_inj {c c' : (Fin 2 → Fin q) → ℕ} : itCfKL c = itCfKL c' ↔ c = c' := by
  constructor
  · intro h
    apply encKColoring_injective
    rw [itCf_encK_eq, itCf_encK_eq, h]
  · rintro rfl; rfl

/-- The key test: on `[⟨c⟩, entry]`, `1` if the key of the entry is `c`. -/
def itCfKeyF (eqn : ℕ) : Expr := .call eqn (mk2 (arg 0) (.get (arg 1) (.nat 0)))

/-- The cost of the key test, for a weight bound `V` of the input. -/
def itCfKeyC (V : ℕ) : ℕ := 2 * 10 ^ 4 * (V + 1) ^ 2

theorem it_cfKey_spec {P : Program} {f eqn : ℕ} (hf : P.funs[f]? = some (itCfKeyF eqn))
    (heqn : P.HasAt eqn (eqNatsFuns eqn)) (c : (Fin 2 → Fin q) → ℕ) (a : ItCfEnt q) {V : ℕ}
    (hV : (Val.list [encKColoring c, itCfEntV a]).wt ≤ V) :
    FunDet P f (.list [encKColoring c, itCfEntV a]) (boolVal (decide (a.1 = c))) (itCfKeyC V) := by
  have e1 := itCf_encK_eq c
  have e2 := itCf_encK_eq a.1
  have hin := eqNats_spec heqn (itCfKL c) (itCfKL a.1)
  have hdec : decide (itCfKL c = itCfKL a.1) = decide (a.1 = c) := by
    rw [decide_eq_decide, itCfKL_inj, eq_comm]
  rw [hdec, ← e1, ← e2] at hin
  have g0 := Det.arg' (P := P) (vs := [encKColoring c, itCfEntV a]) (rest := []) (j := 0)
    (v := encKColoring c) rfl
  have g1 := Det.arg' (P := P) (vs := [encKColoring c, itCfEntV a]) (rest := []) (j := 1)
    (v := itCfEntV a) rfl
  have g2 := Det.get' g1 (Det.nat 0) (v := encKColoring a.1) (vs := [encKColoring a.1,
    .list [encKColoring a.2.1, encKColoring a.2.2]]) rfl
  have d := Det.call (Det.mk2 g0 g2) hin
  refine FunDet.intro hf (d.mono ?_)
  have w1 : (encKColoring c).wt < (Val.list [encKColoring c, itCfEntV a]).wt :=
    wt_le_wt_list (by simp)
  have w2 : (itCfEntV a).wt < (Val.list [encKColoring c, itCfEntV a]).wt :=
    wt_le_wt_list (by simp)
  have w3 : (encKColoring a.1).wt < (itCfEntV a).wt := wt_le_wt_list (by simp [itCfEntV])
  have w4 := wt_list2_le (encKColoring c) (encKColoring a.1)
  have hl : (itCfKL c).length < (encKColoring c).wt := by
    rw [e1]; have := length_lt_wt_list ((itCfKL c).map Val.nat); simpa [natList] using this
  have hb := wt_boolVal_le (decide (a.1 = c))
  have hz := wt_nat_le 0
  have hsq : (V + 1) * (V + 1) = (V + 1) ^ 2 := by ring
  have hm : loopModK * ((itCfKL c).length + 1) *
      ((Val.list [encKColoring c, encKColoring a.1]).wt + (itCfKL c).length + 4) ≤
      loopModK * (V + 1) * (10 * (V + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hm2 : loopModK * (V + 1) * (10 * (V + 1)) = 10 * loopModK * (V + 1) ^ 2 := by ring
  have hV1 : V + 1 ≤ (V + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold itCfKeyC loopModK at *
  omega

/-- The index of the first cache entry with key `c`. -/
noncomputable def itCfIdx (cache : List (ItCfEnt q)) (c : (Fin 2 → Fin q) → ℕ) : ℕ :=
  cache.findIdx fun a => decide (a.1 = c)

/-- The cost of the lookup, for a weight bound `V` of the input. -/
def itCfLkC (V : ℕ) : ℕ := 10 ^ 7 * (V + 1) ^ 3

/-- **The lookup**: on `[⟨c⟩, ⟨cache⟩]`, the index of the first entry with key `c`. -/
theorem it_cfLk_spec {P : Program} {fd kt eqn : ℕ} (hfd : P.HasAt fd (findFuns fd kt))
    (hkt : P.funs[kt]? = some (itCfKeyF eqn)) (heqn : P.HasAt eqn (eqNatsFuns eqn))
    (c : (Fin 2 → Fin q) → ℕ) (cache : List (ItCfEnt q)) {V : ℕ}
    (hV : (Val.list [encKColoring c, .list (cache.map itCfEntV)]).wt ≤ V) :
    FunDet P fd (.list [encKColoring c, .list (cache.map itCfEntV)]) (.nat (itCfIdx cache c))
      (itCfLkC V) := by
  classical
  set xs := cache.map itCfEntV with hxs
  let qf : Val → Bool := fun v => decide (∃ a, v = itCfEntV a ∧ a.1 = c)
  have hq : ∀ a, qf (itCfEntV a) = decide (a.1 = c) := by
    intro a
    simp only [qf, decide_eq_decide]
    constructor
    · rintro ⟨a', h1, h2⟩; rw [itCfEntV_injective h1]; exact h2
    · intro h; exact ⟨a, rfl, h⟩
  have wc : (encKColoring c).wt < (Val.list [encKColoring c, .list xs]).wt :=
    wt_le_wt_list (by simp)
  have wx : (Val.list xs).wt < (Val.list [encKColoring c, .list xs]).wt := wt_le_wt_list (by simp)
  have hp : ∀ x ∈ xs, FunDet P kt (.list [encKColoring c, x]) (boolVal (qf x))
      (10 ^ 6 * (V + 1) ^ 2) := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    rw [hq]
    have wa : (itCfEntV a).wt < (Val.list xs).wt := wt_le_wt_list hx
    have := wt_list2_le (encKColoring c) (itCfEntV a)
    refine (it_cfKey_spec hkt heqn c a (V := 4 * V + 6) (by omega)).mono ?_
    unfold itCfKeyC
    have : (4 * V + 6 + 1) ^ 2 ≤ (7 * (V + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [mul_pow] at this
    omega
  have hf := find_spec hfd hp
  have hidx : xs.findIdx qf = itCfIdx cache c := by
    rw [hxs, List.findIdx_map]
    unfold itCfIdx
    congr 1
    funext a
    exact hq a
  refine hf.mono fun w cost ⟨hw, hc⟩ => ⟨by rw [hw, hidx], ?_⟩
  have hl : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have hsum : (xs.map fun _ => 10 ^ 6 * (V + 1) ^ 2).sum = xs.length * (10 ^ 6 * (V + 1) ^ 2) := by
    simp [List.sum_replicate, List.map_const']
  rw [hsum] at hc
  unfold itCfLkC
  unfold loopModK at hc
  have h1 : xs.length * (10 ^ 6 * (V + 1) ^ 2) ≤ 10 ^ 6 * (V + 1) ^ 3 := by
    have : xs.length ≤ V + 1 := by omega
    calc xs.length * (10 ^ 6 * (V + 1) ^ 2) ≤ (V + 1) * (10 ^ 6 * (V + 1) ^ 2) :=
          Nat.mul_le_mul_right _ this
      _ = 10 ^ 6 * (V + 1) ^ 3 := by ring
  have h2 : 1000 * (xs.length + 1) * ((Val.list [encKColoring c, .list xs]).wt +
      2 * xs.length + 3) ≤ 1000 * (V + 1) * (3 * V + 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h3 : 1000 * (V + 1) * (3 * V + 3) ≤ 3000 * (V + 1) ^ 3 := by
    have : (V + 1) * (3 * V + 3) = 3 * (V + 1) ^ 2 := by ring
    have h4 : (V + 1) ^ 2 ≤ (V + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  omega

/-- **What the lookup finds**: an entry with the key at the index, or no entry with the key. -/
theorem itCfIdx_spec (cache : List (ItCfEnt q)) (c : (Fin 2 → Fin q) → ℕ) :
    (∃ h : itCfIdx cache c < cache.length, (cache[itCfIdx cache c]'h).1 = c) ∨
      (itCfIdx cache c = cache.length ∧ ∀ a ∈ cache, a.1 ≠ c) := by
  by_cases h : itCfIdx cache c < cache.length
  · left
    refine ⟨h, ?_⟩
    have := List.findIdx_getElem (xs := cache) (p := fun a : ItCfEnt q => decide (a.1 = c))
      (w := h)
    simpa using this
  · right
    have hle : itCfIdx cache c ≤ cache.length := List.findIdx_le_length
    have heq : itCfIdx cache c = cache.length := by omega
    refine ⟨heq, fun a ha hac => ?_⟩
    have := (List.findIdx_eq_length (p := fun a : ItCfEnt q => decide (a.1 = c))
      (xs := cache)).1 heq a ha
    simp [hac] at this

end GI.Impl
