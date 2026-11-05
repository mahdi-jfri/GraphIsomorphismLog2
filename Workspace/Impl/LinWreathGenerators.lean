module

public import Workspace.Impl.LinWreath

@[expose] public section

/-! The explicit generating list for the two-copy wreath calculation. -/
namespace GI.Impl
variable {H : Type*} [Group H]

/-- Place a cover element in just one copy. -/
def linWreathSingle (q : linTwo) : H →* (H ≀ᵣ linTwo) where
  toFun h := ⟨fun r => if r = q then h else 1, 1⟩
  map_one' := by ext r <;> simp
  map_mul' h k := by
    ext r
    · simp only [RegularWreathProduct.mul_left, Pi.mul_apply, inv_one, one_mul]
      change (if r = q then h * k else 1) =
        (if r = q then h else 1) * (if r = q then k else 1)
      split_ifs <;> simp
    · rfl

/-- Swap the two copies and leave their internal coordinates unchanged. -/
def linWreathSwap : H ≀ᵣ linTwo := ⟨fun _ => 1, linTwoSwap⟩

/-- At most twice as many cover generators, plus one swap. -/
def linWreathGenerators (xs : List H) : List (H ≀ᵣ linTwo) :=
  xs.map (linWreathSingle 1) ++ xs.map (linWreathSingle linTwoSwap) ++ [linWreathSwap]

@[simp] theorem linWreathGenerators_length (xs : List H) :
    (linWreathGenerators xs).length = 2 * xs.length + 1 := by
  simp only [linWreathGenerators, List.length_append, List.length_map, List.length_singleton]
  omega

theorem linWreathGenerators_generate (xs : List H)
    (hxs : Subgroup.closure {h | h ∈ xs} = ⊤) :
    Subgroup.closure {w | w ∈ linWreathGenerators xs} = ⊤ := by
  classical
  let K := Subgroup.closure {w | w ∈ linWreathGenerators xs}
  have hsingle (q : linTwo) (hq : q = 1 ∨ q = linTwoSwap) (h : H) : linWreathSingle q h ∈ K := by
    have hh : Subgroup.closure {h | h ∈ xs} ≤ K.comap (linWreathSingle q) := by
      rw [Subgroup.closure_le]
      intro h hh
      change linWreathSingle q h ∈ K
      apply Subgroup.subset_closure
      change h ∈ xs at hh
      simp only [linWreathGenerators, List.mem_append, List.mem_map, List.mem_singleton]
      rcases hq with rfl | rfl
      · exact Or.inl (Or.inl ⟨h, hh, rfl⟩)
      · exact Or.inl (Or.inr ⟨h, hh, rfl⟩)
    exact hh (by rw [hxs]; exact Subgroup.mem_top h)
  have hswap : (linWreathSwap : H ≀ᵣ linTwo) ∈ K :=
    Subgroup.subset_closure (by simp [linWreathGenerators])
  apply top_unique
  intro w hw
  have hbase : (⟨w.left, 1⟩ : H ≀ᵣ linTwo) ∈ K := by
    have he : linWreathSingle 1 (w.left 1) * linWreathSingle linTwoSwap (w.left linTwoSwap) =
        (⟨w.left, 1⟩ : H ≀ᵣ linTwo) := by
      ext q
      · rcases linTwo_cases q with rfl | rfl <;> simp [linWreathSingle, Ne.symm linTwoSwap_ne_one]
      · rfl
    rw [← he]
    exact K.mul_mem (hsingle 1 (Or.inl rfl) _) (hsingle linTwoSwap (Or.inr rfl) _)
  rcases linTwo_cases w.right with hr | hr
  · convert hbase using 1
    cases w
    simp_all
  · have he : (⟨w.left, 1⟩ : H ≀ᵣ linTwo) * linWreathSwap = w := by
      ext q <;> simp [linWreathSwap, hr]
    rw [← he]
    exact K.mul_mem hbase hswap

end GI.Impl
