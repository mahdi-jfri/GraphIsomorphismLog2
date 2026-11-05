module

public import Workspace.Impl.LinIntSlpStep

@[expose] public section

/-! Prefix traces and uniform size bounds for exponent-vector evaluation. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linSlpEntries_append {G : Type*} [Group G] (gs : List G)
    (p q : List SlpInstr) (acc : List G) :
    linSlpEntries gs (p ++ q) acc = (linSlpEntries gs p acc).bind (linSlpEntries gs q) := by
  induction p generalizing acc with
  | nil => rfl
  | cons ins p ih =>
    simp only [List.cons_append, linSlpEntries]
    cases linSlpStep gs acc ins <;> simp [ih]

theorem linSlpEntries_length {G : Type*} [Group G] (gs : List G)
    (p : List SlpInstr) (acc es : List G) (h : linSlpEntries gs p acc = some es) :
    es.length = acc.length + p.length := by
  induction p generalizing acc with
  | nil => simpa [linSlpEntries] using (congrArg (Option.map List.length) h).symm
  | cons ins p ih =>
    cases hs : linSlpStep gs acc ins with
    | none => simp [linSlpEntries, hs] at h
    | some x =>
      have hh : linSlpEntries gs p (acc ++ [x]) = some es := by simpa [linSlpEntries, hs] using h
      have hl := ih (acc ++ [x]) hh
      simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *
      omega

/-- A successful full program has a successful prefix at every position. -/
theorem linSlpPrefix_exists {G : Type*} [Group G] (gs : List G)
    (p : List SlpInstr) (es : List G) (h : linSlpEntries gs p [] = some es) (i : ℕ) :
    ∃ acc, linSlpEntries gs (p.take i) [] = some acc := by
  rw [← List.take_append_drop i p, linSlpEntries_append] at h
  cases hp : linSlpEntries gs (p.take i) [] with
  | none => simp [hp] at h
  | some acc => exact ⟨acc, rfl⟩

/-- The deterministic mathematical table after i instructions. -/
def linSlpPrefix {G : Type*} [Group G] (gs : List G) (p : List SlpInstr) (i : ℕ) : List G :=
  (linSlpEntries gs (p.take i) []).getD []

theorem linSlpPrefix_valid {G : Type*} [Group G] (gs : List G)
    (p : List SlpInstr) (es : List G) (h : linSlpEntries gs p [] = some es) (i : ℕ) :
    linSlpEntries gs (p.take i) [] = some (linSlpPrefix gs p i) := by
  obtain ⟨acc, ha⟩ := linSlpPrefix_exists gs p es h i
  simp [linSlpPrefix, ha]

theorem linSlpPrefix_step {G : Type*} [Group G] (gs : List G)
    (p : List SlpInstr) (es : List G) (h : linSlpEntries gs p [] = some es)
    (i : ℕ) (hi : i < p.length) :
    ∃ x, linSlpStep gs (linSlpPrefix gs p i) p[i] = some x ∧
      linSlpPrefix gs p (i + 1) = linSlpPrefix gs p i ++ [x] := by
  have hnext := linSlpPrefix_valid gs p es h (i + 1)
  have ht : p.take (i + 1) = p.take i ++ [p[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  rw [ht, linSlpEntries_append, linSlpPrefix_valid gs p es h i] at hnext
  simp only [Option.bind_some, linSlpEntries] at hnext
  cases hx : linSlpStep gs (linSlpPrefix gs p i) p[i] with
  | none => simp [hx] at hnext
  | some x =>
    simp only [hx, Option.bind_some, Option.some.injEq] at hnext
    exact ⟨x, rfl, by simpa using hnext.symm⟩

def linSlpTableBudget (L t : ℕ) : ℕ :=
  2 * (L * linVectorAccWt t (20 * (L + 2))) + L + 4

theorem linSlpPrefix_wt {t : ℕ} (gs : List (Multiplicative (Fin t → ℤ)))
    (hg : ∀ v ∈ gs, linExponentBound 1 v) (p : List SlpInstr)
    (es : List (Multiplicative (Fin t → ℤ))) (h : linSlpEntries gs p [] = some es)
    (i : ℕ) : (linSlpTable (linSlpPrefix gs p i)).wt ≤ linSlpTableBudget p.length t := by
  have hv := linSlpPrefix_valid gs p es h i
  have hb := linExponentEntries_bound (p.take i) gs [] (linSlpPrefix gs p i) 1 hg (by simp) hv
  have hl := linSlpEntries_length gs (p.take i) [] (linSlpPrefix gs p i) hv
  have hi : (p.take i).length ≤ p.length := by simp only [List.length_take]; omega
  have ht := linWtList (vs := (linSlpPrefix gs p i).map fun v => linVecVal (Multiplicative.toAdd v))
    (B := linVectorAccWt t (20 * (p.length + 2))) (by
      intro v hvm
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hvm
      have hbits (j : Fin t) : (Multiplicative.toAdd v j).natAbs < 2 ^ (p.length + 1) := by
        have hh := hb v hv j
        simp only [Nat.mul_one] at hh
        exact (hh.trans (Nat.pow_le_pow_right (by decide) hi)).trans_lt
          (Nat.pow_lt_pow_right (by decide) (by omega))
      have hw := linWtList (vs := (List.finRange t).map fun j => encInt (Multiplicative.toAdd v j))
        (B := 20 * (p.length + 2)) (by
          intro w hw
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw
          exact linWtInt (hbits j))
      simpa [linVecVal, linVectorAccWt, Nat.add_assoc] using hw)
  simp only [List.length_map, List.length_nil, Nat.zero_add] at ht hl
  unfold linSlpTable linSlpTableBudget
  exact ht.trans (by gcongr <;> omega)

end GI.Impl
