import Workspace.Impl.LinIntSlpValue

namespace GI.Impl
open GI.Cited GI.Lang

private theorem linGetExists {α β : Type*} {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length) {i : ℕ} {x : α} (hx : xs[i]? = some x) :
    ∃ y, ys[i]? = some y := by
  have hi : i < xs.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hx
    contradiction
  exact ⟨ys[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩

/-- Validity depends on the reference indices, not on the group used to evaluate. -/
theorem linSlpStep_valid {G H : Type*} [Group G] [Group H]
    (gs : List G) (gs' : List H) (acc : List G) (acc' : List H)
    (hg : gs.length = gs'.length) (ha : acc.length = acc'.length)
    (ins : SlpInstr) (x : G) (hx : linSlpStep gs acc ins = some x) :
    ∃ y, linSlpStep gs' acc' ins = some y := by
  cases ins with
  | gen i => exact linGetExists hg hx
  | inv j =>
    obtain ⟨a, ha', _⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨b, hb⟩ := linGetExists ha ha'
    exact ⟨b⁻¹, by simp [linSlpStep, hb]⟩
  | mul j k =>
    cases hj : acc[j]? with
    | none => simp [linSlpStep, hj] at hx
    | some a =>
      cases hk : acc[k]? with
      | none => simp [linSlpStep, hj, hk] at hx
      | some b =>
        obtain ⟨a', ha'⟩ := linGetExists ha hj
        obtain ⟨b', hb'⟩ := linGetExists ha hk
        exact ⟨a' * b', by simp [linSlpStep, ha', hb']⟩

theorem linSlpEntries_valid {G H : Type*} [Group G] [Group H]
    (gs : List G) (gs' : List H) (hg : gs.length = gs'.length)
    (prog : List SlpInstr) (acc : List G) (acc' : List H) (ha : acc.length = acc'.length)
    (es : List G) (he : linSlpEntries gs prog acc = some es) :
    ∃ es', linSlpEntries gs' prog acc' = some es' := by
  induction prog generalizing acc acc' with
  | nil => exact ⟨acc', rfl⟩
  | cons ins prog ih =>
    cases hx : linSlpStep gs acc ins with
    | none => simp [linSlpEntries, hx] at he
    | some x =>
      obtain ⟨y, hy⟩ := linSlpStep_valid gs gs' acc acc' hg ha ins x hx
      obtain ⟨es', hes⟩ := ih (acc ++ [x]) (acc' ++ [y]) (by simp [ha])
        (by simpa [linSlpEntries, hx] using he)
      exact ⟨es', by simpa [linSlpEntries, hy] using hes⟩

/-- A membership SLP is executable on any equally long list of zero/unit vectors. -/
theorem linExponent_of_reaches {n t : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (vectors : List (Fin t → ℤ)) (hlen : gs.length = vectors.length)
    (prog : List SlpInstr) (x : Equiv.Perm (Fin n)) (hx : SlpReaches gs prog x) :
    ∃ z, linExponentValue vectors prog = some z := by
  obtain ⟨es, he, _⟩ := hx
  rw [← linSlpEntries_perm] at he
  obtain ⟨es', hes⟩ := linSlpEntries_valid gs (vectors.map Multiplicative.ofAdd)
    (by simpa using hlen) prog [] [] rfl es he
  exact ⟨Multiplicative.toAdd (es'.getLast?.getD 1), by simp [linExponentValue, linSlpValue, hes]⟩

/-- The public exponent-vector program agrees with linExponentValue. -/
theorem linExponent_spec {P : Program} {f table step add scale ib t : ℕ}
    (hf : P.funs[f]? = some (linSlpValueF table))
    (hp : P.HasAt table (linSlpFuns table step))
    (hstep : P.funs[step]? = some (linSlpStepF add scale)) (hi : linIntSpec P ib)
    (ha : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hs : P.HasAt scale (linVectorScaleFuns scale ib))
    (vectors : List (Fin t → ℤ)) (hg : ∀ v ∈ vectors, ∀ i, (v i).natAbs ≤ 1)
    (prog : List SlpInstr) (z : Fin t → ℤ) (hz : linExponentValue vectors prog = some z) :
    FunDet P f (.list [.list (vectors.map linVecVal), .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)])
      (linVecVal z)
      (linSlpValueCost (Val.list [.list (vectors.map linVecVal), .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)]).wt prog.length t) := by
  obtain ⟨es, he⟩ : ∃ es, linSlpEntries (vectors.map Multiplicative.ofAdd) prog [] = some es := by
    cases he : linSlpEntries (vectors.map Multiplicative.ofAdd) prog [] with
    | none => simp [linExponentValue, linSlpValue, he] at hz
    | some es => exact ⟨es, rfl⟩
  have hgs : ∀ v ∈ vectors.map Multiplicative.ofAdd, linExponentBound 1 v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hg u hu
  have heq : Multiplicative.toAdd (es.getLast?.getD 1) = z := by
    simpa [linExponentValue, linSlpValue, he] using hz
  have h := linSlpValue_spec hf hp hstep hi ha hs (vectors.map Multiplicative.ofAdd) hgs prog es he
  simpa only [heq, linSlpTable, List.map_map, Function.comp_def] using h

end GI.Impl
