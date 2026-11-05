module

public import Workspace.Proved.VsPS3Math

@[expose] public section

/-!
# The first branches

* `VsPHyp.N0`: the facts for `N₀ = C^{(j)}` from the derived series program.
* `VsPHyp.grow_abel`: an abelian subgroup `⟨ns⟩` (by the local test), normalized, inside `C`,
  with a generator outside `L`, grows `A` (branches `N₀` and `N₂` abelian).
* `VsPHyp.two_le_n`: `n ≥ 2` (since `C̄` is not abelian).
-/

set_option backward.isDefEq.respectTransparency false

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]
variable {hs : VsQStOK s} {as ccs : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}

/-- **The facts for `N₀`.** -/
theorem VsPHyp.N0 (hH : VsPHyp hs as Lb ccs) {j : ℕ}
    (hj : vsPDer (gens ccs) (j + 1) ≤ vsPSp hs as) :
    vsPDer (gens ccs) j ≤ gens s.hs ∧ VsPNormd (gens s.hs) (vsPDer (gens ccs) j) ∧
      vsPBar hs (vsPDer (gens ccs) j) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _) ∧
      ∀ x ∈ vsPDer (gens ccs) j, ∀ y ∈ vsPDer (gens ccs) j,
        vsPRho hs ⁅x, y⁆ ∈ vsMScal (vsPBar hs (gens as)) := by
  have hle : vsPDer (gens ccs) j ≤ gens s.hs := (vsPDer_le _ j).trans hH.hcc
  refine ⟨hle, vsPDer_normd hH.hccn j, (vsPBar_le hs (vsPDer_le _ j)).trans hH.hccC,
    fun x hx y hy => ?_⟩
  have hc : ⁅x, y⁆ ∈ vsPDer (gens ccs) (j + 1) := Subgroup.commutator_mem_commutator hx hy
  exact (vsPSp_iff hs as (hle (vsPDer_succ_le _ j hc))).1 (hj hc)

/-- **An abelian piece grows `A`.** -/
theorem VsPHyp.grow_abel (hH : VsPHyp hs as Lb ccs) {ns : List (Perm (Fin I.n))}
    (hle : gens ns ≤ gens s.hs) (hn : VsPNormd (gens s.hs) (gens ns))
    (hC : vsPBar hs (gens ns) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _))
    (hab : ∀ g ∈ 1 :: ns, ∀ h ∈ 1 :: ns,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))
    (hout : ¬ gens ns ≤ vsPSp hs as)
    {as' : List (Perm (Fin I.n))} (hl : as'.length ≤ I.n ^ 2)
    (he : gens as' = Subgroup.closure {x | ∃ g ∈ gens s.hs ⊔ gens (as ++ ns), ∃ y ∈ as ++ ns,
      x = g * y * g⁻¹}) :
    VsPGrowOut hs as as' := by
  obtain ⟨x, hx, hxS⟩ := vsP_exists_gen_not_mem hout
  have hxg : x ∈ gens s.hs := hle (Subgroup.subset_closure hx)
  refine vsP_grow_out hH hle hn (fun y hy => Subgroup.subset_closure hy) ?_ hC hx
    (fun h' => hxS ((vsPSp_iff hs as hxg).2 h')) hl he
  refine vsP_bar_abel hs hle fun g hg k hk => ?_
  exact (vsPLocL_eq_iff hs _ _).1 (hab g (List.mem_cons_of_mem _ hg) k (List.mem_cons_of_mem _ hk))

/-- **`n ≥ 2`**, since `C̄` is not abelian. -/
theorem VsPHyp.two_le_n (hH : VsPHyp hs as Lb ccs) : 2 ≤ I.n := by
  by_contra hn
  push Not at hn
  haveI : Subsingleton (Perm (Fin I.n)) := by
    constructor; intro a b; ext i; exact congrArg Fin.val (Subsingleton.elim (h := by
      constructor; intro u v; ext; omega) (a i) (b i))
  apply hH.hnab
  intro u hu
  obtain ⟨x, -, hx, rfl⟩ := (vsPBar_mem_iff hs).1 hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨y, -, hy, rfl⟩ := (vsPBar_mem_iff hs).1 hv
  rw [Subsingleton.elim x y]

end GI.Proved
