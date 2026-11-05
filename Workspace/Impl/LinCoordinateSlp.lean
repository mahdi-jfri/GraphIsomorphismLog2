module

public import Workspace.Impl.LinCoordinates
public import Workspace.Impl.LinIntSlpValid

@[expose] public section

/-! Zero/unit assignments for the cyclic-prefix SLPs. Later coordinates remain
zero, and evaluation in the quotient proves each assembled relation. -/
namespace GI.Impl
open GI.Cited

/-- Assign zero to N-generators and unit vectors to the preceding A-generators. -/
def linPrefixVectors (t ns i : ℕ) : List (Fin t → ℤ) :=
  List.replicate ns 0 ++ ((List.finRange t).take i).map (fun j => Pi.single j 1)

theorem linPrefixVectors_bound (t ns i : ℕ) :
    ∀ v ∈ linPrefixVectors t ns i, ∀ j, (v j).natAbs ≤ 1 := by
  intro v hv j
  rcases List.mem_append.mp hv with hv | hv
  · obtain rfl := List.eq_of_mem_replicate hv
    simp
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
    by_cases h : j = k <;> simp [Pi.single_apply, h]

theorem linPrefixVectors_zero (t ns i : ℕ) (j : Fin t) (hij : i ≤ j.val) :
    ∀ v ∈ linPrefixVectors t ns i, v j = 0 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain rfl := List.eq_of_mem_replicate hv
    rfl
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    have hki : k.val < i := by
      obtain ⟨a, ha, he⟩ := List.mem_take_iff_getElem.mp hk
      have hval : a = k.val := by
        rw [← he, List.getElem_finRange]
        rfl
      omega
    have hjk : j ≠ k := by intro he; subst k; omega
    simp [Pi.single_apply, hjk]

private theorem linSlpStep_zero {t : ℕ} (gs acc : List (Multiplicative (Fin t → ℤ)))
    (j : Fin t) (hg : ∀ v ∈ gs, Multiplicative.toAdd v j = 0)
    (ha : ∀ v ∈ acc, Multiplicative.toAdd v j = 0)
    (ins : SlpInstr) (x : Multiplicative (Fin t → ℤ)) (hx : linSlpStep gs acc ins = some x) :
    Multiplicative.toAdd x j = 0 := by
  cases ins with
  | gen k => exact hg x (List.mem_of_getElem? hx)
  | inv k =>
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    change -Multiplicative.toAdd y j = 0
    rw [ha y (List.mem_of_getElem? hy), neg_zero]
  | mul k l =>
    cases hk : acc[k]? with
    | none => simp [linSlpStep, hk] at hx
    | some y =>
      cases hl : acc[l]? with
      | none => simp [linSlpStep, hk, hl] at hx
      | some z =>
        have he : y * z = x := by simpa [linSlpStep, hk, hl] using hx
        subst x
        change Multiplicative.toAdd y j + Multiplicative.toAdd z j = 0
        rw [ha y (List.mem_of_getElem? hk), ha z (List.mem_of_getElem? hl), add_zero]

private theorem linSlpEntries_zero {t : ℕ} (gs : List (Multiplicative (Fin t → ℤ)))
    (j : Fin t) (hg : ∀ v ∈ gs, Multiplicative.toAdd v j = 0)
    (prog : List SlpInstr) (acc es : List (Multiplicative (Fin t → ℤ)))
    (ha : ∀ v ∈ acc, Multiplicative.toAdd v j = 0) (he : linSlpEntries gs prog acc = some es) :
    ∀ v ∈ es, Multiplicative.toAdd v j = 0 := by
  induction prog generalizing acc with
  | nil =>
    have heq : acc = es := by simpa [linSlpEntries] using he
    rw [← heq]
    exact ha
  | cons ins prog ih =>
    cases hx : linSlpStep gs acc ins with
    | none => simp [linSlpEntries, hx] at he
    | some x =>
      have hnext : linSlpEntries gs prog (acc ++ [x]) = some es := by simpa [linSlpEntries, hx] using he
      apply ih (acc ++ [x]) ?_ hnext
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact ha v hv
      · rw [List.mem_singleton.mp hv]
        exact linSlpStep_zero gs acc j hg ha ins x hx

/-- No instruction can introduce a coordinate that vanishes on all assigned generators. -/
theorem linExponentValue_zero {t : ℕ} (vectors : List (Fin t → ℤ)) (j : Fin t)
    (hg : ∀ v ∈ vectors, v j = 0) (prog : List SlpInstr) (z : Fin t → ℤ)
    (hz : linExponentValue vectors prog = some z) : z j = 0 := by
  obtain ⟨es, he⟩ : ∃ es, linSlpEntries (vectors.map Multiplicative.ofAdd) prog [] = some es := by
    cases he : linSlpEntries (vectors.map Multiplicative.ofAdd) prog [] with
    | none => simp [linExponentValue, linSlpValue, he] at hz
    | some es => exact ⟨es, rfl⟩
  have hgs : ∀ v ∈ vectors.map Multiplicative.ofAdd, Multiplicative.toAdd v j = 0 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact hg u hu
  have hall := linSlpEntries_zero _ j hgs prog [] es (by simp) he
  have hz' : Multiplicative.toAdd (es.getLast?.getD 1) = z := by
    simpa [linExponentValue, linSlpValue, he] using hz
  rw [← hz']
  cases hl : es.getLast? with
  | none => rfl
  | some v => exact hall v (List.mem_of_mem_getLast? (by rw [hl]; rfl))

end GI.Impl
