module

public import Workspace.Impl.LinSlp

@[expose] public section

/-! Integer exponent vectors of the SLPs in A.20. Multiplication becomes vector
addition, and inversion becomes negation. Each instruction increases the bit bound
by at most one, even when it reuses a preceding entry twice. -/
namespace GI.Impl
open GI.Cited

/-- A bound on every coordinate of an integer exponent vector. -/
def linExponentBound {t : ℕ} (B : ℕ) (v : Multiplicative (Fin t → ℤ)) : Prop :=
  ∀ i, (Multiplicative.toAdd v i).natAbs ≤ B

private theorem linExponentBound_mono {t B C : ℕ} {v : Multiplicative (Fin t → ℤ)}
    (h : B ≤ C) (hv : linExponentBound B v) : linExponentBound C v := fun i => (hv i).trans h

/-- One valid instruction at most doubles the coordinate bound. -/
theorem linExponentStep_bound {t B : ℕ} {gs acc : List (Multiplicative (Fin t → ℤ))}
    (hg : ∀ v ∈ gs, linExponentBound B v) (ha : ∀ v ∈ acc, linExponentBound B v)
    {ins : SlpInstr} {v : Multiplicative (Fin t → ℤ)} (h : linSlpStep gs acc ins = some v) :
    linExponentBound (2 * B) v := by
  cases ins with
  | gen i =>
    exact linExponentBound_mono (by omega) (hg v (List.mem_of_getElem? h))
  | inv j =>
    simp only [linSlpStep, Option.map_eq_some_iff] at h
    obtain ⟨a, ha', rfl⟩ := h
    have hab := ha a (List.mem_of_getElem? ha')
    intro i
    change (-(Multiplicative.toAdd a i)).natAbs ≤ _
    rw [Int.natAbs_neg]
    exact (hab i).trans (by omega)
  | mul j k =>
    cases hj : acc[j]? with
    | none => simp [linSlpStep, hj] at h
    | some a =>
      cases hk : acc[k]? with
      | none => simp [linSlpStep, hk] at h
      | some b =>
        have hv : a * b = v := by simpa [linSlpStep, hj, hk] using h
        subst v
        have hab := ha a (List.mem_of_getElem? hj)
        have hbb := ha b (List.mem_of_getElem? hk)
        intro i
        change (Multiplicative.toAdd a i + Multiplicative.toAdd b i).natAbs ≤ _
        exact (Int.natAbs_add_le _ _).trans (by have := hab i; have := hbb i; omega)

/-- A program of length L multiplies the coordinate bound by at most 2^L. -/
theorem linExponentEntries_bound {t : ℕ} (prog : List SlpInstr)
    (gs acc es : List (Multiplicative (Fin t → ℤ))) (B : ℕ)
    (hg : ∀ v ∈ gs, linExponentBound B v) (ha : ∀ v ∈ acc, linExponentBound B v)
    (h : linSlpEntries gs prog acc = some es) :
    ∀ v ∈ es, linExponentBound (2 ^ prog.length * B) v := by
  induction prog generalizing acc B with
  | nil =>
    simp only [linSlpEntries, Option.some.injEq] at h
    subst es
    simpa using ha
  | cons ins prog ih =>
    obtain ⟨x, hx⟩ : ∃ x, linSlpStep gs acc ins = some x := by
      cases hx : linSlpStep gs acc ins with
      | none => simp [linSlpEntries, hx] at h
      | some x => exact ⟨x, rfl⟩
    have he : linSlpEntries gs prog (acc ++ [x]) = some es := by
      simpa [linSlpEntries, hx] using h
    have hb := linExponentStep_bound hg ha hx
    have hnext : ∀ v ∈ acc ++ [x], linExponentBound (2 * B) v := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact linExponentBound_mono (by omega) (ha v hv)
      · obtain rfl := List.mem_singleton.mp hv
        exact hb
    have hres := ih (acc ++ [x]) (2 * B)
      (fun v hv => linExponentBound_mono (by omega) (hg v hv)) hnext he
    simpa only [List.length_cons, pow_succ, mul_assoc] using hres

/-- The actual integer exponent-vector evaluator. N-generators are assigned zero,
and each a-generator is assigned its unit vector by the caller. -/
def linExponentValue {t : ℕ} (vectors : List (Fin t → ℤ)) (prog : List SlpInstr) :
    Option (Fin t → ℤ) :=
  (linSlpValue (vectors.map Multiplicative.ofAdd) prog).map Multiplicative.toAdd

/-- With zero and unit-vector inputs, a length-L program has at most L+1 bits
in every output coordinate. This is a bound on values, independent of sharing in the SLP. -/
theorem linExponentValue_bits {t : ℕ} (vectors : List (Fin t → ℤ))
    (hvec : ∀ v ∈ vectors, ∀ i, (v i).natAbs ≤ 1)
    (prog : List SlpInstr) (z : Fin t → ℤ) (hz : linExponentValue vectors prog = some z) :
    ∀ i, (z i).natAbs < 2 ^ (prog.length + 1) := by
  unfold linExponentValue linSlpValue at hz
  obtain ⟨es, he⟩ : ∃ es, linSlpEntries (vectors.map Multiplicative.ofAdd) prog [] = some es := by
    cases he : linSlpEntries (vectors.map Multiplicative.ofAdd) prog [] with
    | none => simp [he] at hz
    | some es => exact ⟨es, rfl⟩
  have hb := linExponentEntries_bound prog (vectors.map Multiplicative.ofAdd) [] es 1
    (by
      intro v hv
      obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
      rw [← huv]
      exact hvec u hu) (by simp) he
  simp only [he, Option.map_some, Option.some.injEq] at hz
  subst z
  intro i
  cases hl : es.getLast? with
  | none => simp
  | some v =>
    have hv := hb v (List.mem_of_mem_getLast? (by rw [hl]; rfl)) i
    simp only [Option.getD_some]
    simp only [mul_one] at hv
    rw [pow_succ]
    have := Nat.two_pow_pos prog.length
    omega

/-- Interpret an exponent vector and evaluate the permutation SLP in the quotient.
Matching the generator images suffices for the resulting relation to hold. -/
theorem linExponent_relation {G : Type*} [Group G] {t : ℕ} {Q : Type*} [Group Q]
    (f : G →* Q) (q : Multiplicative (Fin t → ℤ) →* Q)
    (gs : List G) (vectors : List (Fin t → ℤ))
    (hgen : gs.map f = (vectors.map Multiplicative.ofAdd).map q)
    (prog : List SlpInstr) (x : G) (hx : linSlpValue gs prog = some x)
    (z : Fin t → ℤ) (hz : linExponentValue vectors prog = some z) :
    q (Multiplicative.ofAdd z) = f x := by
  have hf : linSlpValue (gs.map f) prog = some (f x) := by
    rw [linSlpValue_map, hx, Option.map_some]
  rw [hgen, linSlpValue_map] at hf
  unfold linExponentValue at hz
  cases he : linSlpValue (vectors.map Multiplicative.ofAdd) prog with
  | none => simp [he] at hz
  | some v =>
    simp only [he, Option.map_some, Option.some.injEq] at hz hf
    subst z
    exact hf

end GI.Impl
