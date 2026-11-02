import Workspace.Impl.CamPFac
import Workspace.Impl.CamPTrans
import Workspace.Impl.CamReindex
import Workspace.Impl.CamBranch

/-!
# Step 10 of `camProg`: putting the coordinates together

The factor loop finds the factors in some order `τ` (the index of the `j`-th factor found is
`τ j`). For each `j`, the column of the `j`-th factor satisfies `CamFacOut e (τ j)`. Read through
the renumbered identification `camReindex e τ`, these are the hypotheses of `cam_combine`, which
gives a Maróti identification `e'` whose coordinates are the computed ones. The transpose of the
columns is then `encKSetTuples e'` (`cam_assemble`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

variable {n m k r : ℕ}

/-- The order in which the loop found the factors. -/
noncomputable def camTau (L : List (Fin r)) (hL : L.Nodup) (hl : L.length = r) : Perm (Fin r) :=
  Equiv.ofBijective (fun j => L.get (Fin.cast hl.symm j))
    (Finite.injective_iff_bijective.mp fun _ _ h => Fin.cast_injective _ (hL.injective_get h))

theorem camTau_apply (L : List (Fin r)) (hL : L.Nodup) (hl : L.length = r) (j : Fin r) :
    camTau L hL hl j = L.get (Fin.cast hl.symm j) := rfl

/-- In the `[1]` branch, `m = 6` forces `k = 1`. -/
theorem cam_six (hk1 : 1 ≤ k) (hk : 2 * k < m) (hb : (k + 1) ^ 2 < m + 2) : m = 6 → k = 1 := by
  rintro rfl
  have : k ≤ 2 := by omega
  interval_cases k
  · rfl
  · norm_num at hb

/-- **Putting the coordinates together.** -/
theorem cam_assemble {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hM : MarotiStructure G e)
    (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) (hb : (k + 1) ^ 2 < m + 2) (x₀ : Fin n)
    (L : List (Fin r)) (hL : L.Nodup) (hl : L.length = r) (cols : List Val)
    (hcols : List.Forall₂ (fun i v => CamFacOut e i x₀ v) L cols) :
    ∃ e' : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}), MarotiStructure G e' ∧
      ∃ colsF : List (Fin n → Val), cols = colsF.map camColV ∧
        Val.list ((List.finRange n).map fun x => .list (colsF.map fun f => f x)) =
          encKSetTuples e' := by
  set τ := camTau L hL hl with hτ
  have hlc : cols.length = r := hcols.length_eq ▸ hl
  have hj : ∀ j : Fin r, CamFacOut e (τ j) x₀ (cols.get (Fin.cast hlc.symm j)) := by
    intro j
    have := hcols.get (i := j) (by omega) (by omega)
    simpa [camTau_apply] using this
  choose O ts' ι hinj hν hH hι F hF hv using hj
  set e₀ := camReindex e τ with he₀
  have hν' : ∀ j y, (∃ w, (O j).get w = y) ↔ ∀ j', j' ≠ j → e₀ y j' = e₀ x₀ j' := by
    intro j y
    rw [hν j y]
    simp only [he₀, camReindex_apply]
    constructor
    · intro h j' hj'
      exact h (τ j') fun h' => hj' (τ.injective h')
    · intro h i' hi'
      have := h (τ.symm i') fun h' => hi' (by rw [← h']; simp)
      simpa using this
  have hH' : ∀ j g, g ∈ gens (ts' j) ↔ ∃ t ∈ camProd e₀ {j}, ∀ w, (O j).get (g w) = t ((O j).get w) := by
    intro j g
    rw [hH j g, he₀, camProd_reindex, Finset.map_singleton]
    rfl
  obtain ⟨e', he', hM'⟩ := cam_combine (cam_maroti_reindex τ hM) hm hk1 hk (cam_six hk1 hk hb) x₀
    (fun j => (O j).length) (fun j => (O j).get) hinj hν' (fun j => gens (ts' j)) hH' ι hι
    (fun x j => F j x) (fun x j w h => hF j x w (by simpa [he₀] using h))
  refine ⟨e', hM', (List.finRange r).map fun j x => kVal (F j x), ?_, ?_⟩
  · refine List.ext_get (by simp [hlc]) fun i h1 h2 => ?_
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    have := hv ⟨i, by simpa using h2⟩
    simpa using this
  · simp only [encKSetTuples, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, he']
    rfl

end GI.Impl
