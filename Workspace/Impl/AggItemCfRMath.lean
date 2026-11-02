import Workspace.Impl.AggItemCfDMath

/-!
# Reading the refined orbital object

The supplied binary table already contains the colors after refinement.
Its tuple index is `a + q * b`. Reading the table as rows and its diagonal
at the source vertex therefore gives the object without another refinement.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv

/-- A binary color read from the flat tuple table. -/
def itCfRColor (dl : List ℕ) (q a b : ℕ) : ℕ := dl.getD (a + q * b) 0

/-- The binary table as rows indexed by the first vertex. -/
def itCfRTable (dl : List ℕ) (q : ℕ) : Val :=
  .list ((List.range q).map fun a => natList ((List.range q).map fun b =>
    itCfRColor dl q a b))

/-- Read the object once the transitivity degree has been computed. -/
def itCfROut (dl tl : List ℕ) (q d : ℕ) : Val :=
  if d < tl.length then
    let u := tl.getD (d - 1) 0
    .list [.nat 2, .list [itCfRTable dl q, .nat (itCfRColor dl q u u), .nat u]]
  else .list [.nat 0]

theorem itCfRColor_eq {q : ℕ} (c : (Fin 2 → Fin q) → ℕ) (a b : Fin q) :
    itCfRColor (stDL c) q a b = skel₂ c nilT a b := by
  unfold itCfRColor skel₂
  have hi : (finFunctionFinEquiv (padTuple₂ nilT a b : Fin 2 → Fin q) : ℕ) =
      (a : ℕ) + q * b := by
    rw [finFunctionFinEquiv_apply, Fin.sum_univ_two]
    simp [padTuple₂, Nat.mul_comm]
  rw [← hi, stDL_getD]

theorem itCfRTable_eq {q : ℕ} (c : (Fin 2 → Fin q) → ℕ) (j : ℕ) :
    itCfRTable (stDL c) q = rcColVal (skelCfg c nilT j) := by
  unfold itCfRTable rcColVal
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  unfold natList encFun
  simp only [List.map_map, Function.comp_apply]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, itCfRColor_eq, skelCfg]

/-- The two table reads agree with `orbitalOut` for every refinement function. -/
theorem itCfROut_eq {q ℓ : ℕ} (H : Subgroup (Perm (Fin q)))
    (t : Fin ℓ → Fin q) (R : Refiner2 q) :
    itCfROut (stDL (R (orbColOut H t))) (stL fun i => (t i : ℕ)) q
        (transDeg H (domSet H)) = itCfOutV (orbitalOut R H t) := by
  have htlen : (stL fun i => (t i : ℕ)).length = ℓ := by simp [stL]
  unfold itCfROut orbitalOut orbitalAt
  rw [htlen]
  by_cases hd : transDeg H (domSet H) < ℓ
  swap
  · rw [if_neg hd, dif_neg hd]
    rfl
  rw [if_pos hd, dif_pos hd]
  have hu : (stL fun i => (t i : ℕ)).getD (transDeg H (domSet H) - 1) 0 =
      t ⟨transDeg H (domSet H) - 1, by omega⟩ := by
    rw [List.getD_eq_getElem _ _ (by rw [htlen]; omega)]
    simp [stL]
  dsimp only
  rw [hu, itCfRTable_eq, itCfRColor_eq, st_skel₂_self]
  unfold itCfOutV orbitalCfg rcCertIn
  have hc : orbColOut H t = orbCol H (domSet H \ ancSet t (transDeg H (domSet H)))
      (ancSet t (transDeg H (domSet H))) (ancList t (transDeg H (domSet H)))
      (t ⟨transDeg H (domSet H) - 1, by omega⟩)
      (t ⟨transDeg H (domSet H), hd⟩) := by
    unfold orbColOut orbColAt
    rw [dif_pos hd]
  rw [hc]
  rfl

end GI.Impl
