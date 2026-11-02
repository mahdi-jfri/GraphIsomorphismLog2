import Workspace.Impl.AggItemCfDeg
import Workspace.Impl.AggTup
import Workspace.Impl.AggStructRel

/-!
# The orbital coloring of Case 2b: the facts the program uses

The program `col` (`AggItemCfCol.lean`) computes `orbColOut H t` as a table over the `q²` pairs
of points. This file holds the facts that link what it computes to the definitions of
`OutOrbital.lean`.

* `itCfAnc t d`: the anchors `t_0, …, t_{d-2}` as a list, the first `d - 1` entries of `t`
  (`itCf_mem_anc`: its points are `ancSet t d`).
* `itCf_orb_iff`: with `⟨gs⟩` the pointwise stabilizer of the anchors in `H`, a pair `(a, b)` is
  in the orbital of `(u, v)` exactly when the list `[a, b]` is in the orbit of `[u, v]` under
  `⟨1 :: gs⟩`, the orbit the program computes (`tupOrb_spec`).
* `itCf_orbit_ncard`: that orbit has at most `q²` points.
* `itCf_symm_zero`, `itCf_symm_one`: entry `j` of the table is the pair `(j % q, j / q)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab encKColoring)

variable {q ℓ : ℕ}

/-- The anchors `t_0, …, t_{d-2}`, as a list (`ancList`). -/
def itCfAnc (t : Fin ℓ → Fin q) (d : ℕ) : List (Fin q) := ancList t d

theorem itCf_mem_anc (t : Fin ℓ → Fin q) (d : ℕ) (a : Fin q) :
    a ∈ itCfAnc t d ↔ a ∈ ancSet t d := mem_ancList t d a

/-- The anchors as the program reads them: a prefix of the list `stTv t`. -/
theorem itCf_anc_val (t : Fin ℓ → Fin q) (d : ℕ) :
    encPts (itCfAnc t d) =
      .list (((List.finRange ℓ).map fun i => (t i : ℕ)).map Val.nat |>.take (d - 1)) := by
  rw [itCf_encPts_eq, itCfAnc, ancList, List.map_take, List.map_map, List.map_map]
  rfl

theorem itCf_stTv_eq (t : Fin ℓ → Fin q) :
    stTv t = .list (((List.finRange ℓ).map fun i => (t i : ℕ)).map Val.nat) := rfl

/-- An entry of the list of `stTv t`. -/
theorem itCf_stTv_get (t : Fin ℓ → Fin q) (i : ℕ) (hi : i < ℓ) :
    (((List.finRange ℓ).map fun i => (t i : ℕ)).map Val.nat)[i]? = some (.nat (t ⟨i, hi⟩)) := by
  simp [hi]

/-- **The orbital through the orbit of a list.** -/
theorem itCf_orb_iff (H : Subgroup (Perm (Fin q))) (A : Finset (Fin q)) (As : List (Fin q))
    (hA : ∀ a, a ∈ As ↔ a ∈ A) (gs : List (Perm (Fin q)))
    (hgs : gens gs = pointwiseStab H As) (u v a b : Fin q) :
    Orb H A u v a b ↔ [a, b] ∈ actOrbit (fun g (xs : List (Fin q)) => xs.map g) (1 :: gs) [u, v] := by
  have hG : genGroup (1 :: gs) = pointwiseStab H As := by
    change gens (1 :: gs) = _
    rw [gens_one_cons, hgs]
  change _ ↔ ∃ g ∈ genGroup (1 :: gs), [u, v].map g = [a, b]
  rw [hG]
  constructor
  · rintro ⟨g, ⟨hgH, hgA⟩, rfl, rfl⟩
    exact ⟨g, ⟨hgH, fun i hi => hgA i ((hA i).1 hi)⟩, rfl⟩
  · rintro ⟨g, ⟨hgH, hgA⟩, he⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    exact ⟨g, ⟨hgH, fun i hi => hgA i ((hA i).2 hi)⟩, he.1, he.2⟩

/-- The orbit of a pair has at most `q²` points. -/
theorem itCf_orbit_ncard (gs : List (Perm (Fin q))) (u v : Fin q) :
    (actOrbit (fun g (xs : List (Fin q)) => xs.map g) gs [u, v]).ncard ≤ q * q := by
  have hsub : actOrbit (fun g (xs : List (Fin q)) => xs.map g) gs [u, v] ⊆
      (fun p : Fin q × Fin q => [p.1, p.2]) '' Set.univ := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨(g u, g v), Set.mem_univ _, rfl⟩
  calc _ ≤ ((fun p : Fin q × Fin q => [p.1, p.2]) '' Set.univ).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ : Set (Fin q × Fin q)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = q * q := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod,
        Fintype.card_fin]

theorem itCf_symm_zero (j : Fin (q ^ 2)) : ((finFunctionFinEquiv.symm j) 0 : ℕ) = j % q := by
  rw [finFunctionFinEquiv_symm_apply_val]
  simp

theorem itCf_symm_one (j : Fin (q ^ 2)) : ((finFunctionFinEquiv.symm j) 1 : ℕ) = j / q := by
  rw [finFunctionFinEquiv_symm_apply_val]
  have hj := j.isLt
  have h1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  rw [h1, pow_one]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← sq]; exact hj))

/-- The zero coloring as a table. -/
theorem itCf_encK_zero :
    encKColoring (fun _ : Fin 2 → Fin q => 0) = .list (List.replicate (q * q) (.nat 0)) := by
  unfold encKColoring
  rw [List.map_const', List.length_finRange, sq]

end GI.Impl
