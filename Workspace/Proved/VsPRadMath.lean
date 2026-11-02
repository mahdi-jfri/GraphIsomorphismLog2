import Workspace.Proved.VsPPairMath
import Workspace.Proved.VsWLinMath

/-!
# The radical test as the program runs it

The program stores the Gram matrix as the rows `us`, row `i` holding `dl(g_i, g_j)` at `j`,
and computes the relations `vsWKer r us` among the rows. If the word `∏ g_i^{t_i}` of every
relation `t` lies in `S`, then the radical of the pairing lies in `S` (`vsP_radical_prog`, from
`vsP_radical` and `vsWKer_span`).
-/

namespace GI.Proved

open GI.Impl
open scoped commutatorElement

variable {G : Type*} [Group G] {N S : Subgroup G} {r : ℕ} {ζ : G}

theorem vsP_radical_prog [hr : Fact r.Prime] (hQ : VsPQuotHyp N S r) (hP : VsPPairHyp N r ζ)
    {gs : List G} (hN : N = Subgroup.closure {g | g ∈ gs}) {us : List (List ℕ)}
    (hlen : us.length = gs.length) (hfit : VsWFit r gs.length us)
    (hus : ∀ i j : Fin gs.length, vsF r (us.getD i []) j = vsPDl r ζ gs[i] gs[j])
    (hA : ∀ t ∈ vsWKer r us, vsPW gs t ∈ S) :
    ∀ x ∈ N, (∀ g ∈ gs, x * g = g * x) → x ∈ S := by
  have hfitK := vsWKer_fit hr.out.one_lt hfit
  let φ : (Fin us.length → ZMod r) →ₗ[ZMod r] (Fin gs.length → ZMod r) :=
    LinearMap.funLeft (ZMod r) (ZMod r) (Fin.cast hlen.symm)
  refine vsP_radical hQ hP hN (A := (vsWKer r us).map fun t => φ (vsWV r us.length t)) ?_ ?_
  · intro e he
    let e' : Fin us.length → ZMod r := fun i => e (Fin.cast hlen i)
    have hφ : φ e' = e := by funext i; rfl
    have hker : e' ∈ LinearMap.ker (vsWComb r gs.length us) := by
      rw [LinearMap.mem_ker]
      funext j
      rw [vsWComb_apply, Finset.sum_apply, Pi.zero_apply]
      rw [← he j]
      refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
      simp only [Pi.smul_apply, smul_eq_mul, vsWV_apply, e', finCongr_apply]
      congr 1
      rw [← hus (Fin.cast hlen i) j]
      simp [List.getD_eq_getElem?_getD]
    rw [← vsWKer_span hr.out hfit] at hker
    rw [← hφ]
    have hmap := Submodule.mem_map_of_mem (f := φ) hker
    rw [vsWSp, Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact List.mem_map.2 ⟨u, hu, rfl⟩
  · intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
    have htf := hfitK t ht
    have e : vsPExp (φ (vsWV r us.length t)) = t := by
      refine List.ext_getElem (by rw [vsPExp_length, htf.2, hlen]) fun i hi hi' => ?_
      simp only [vsPExp, List.getElem_map, List.getElem_finRange]
      simp only [φ, LinearMap.funLeft_apply, vsWV_apply, vsF_apply, Fin.val_cast]
      rw [List.getD_eq_getElem _ _ hi', ZMod.val_cast_of_lt (htf.1 _ (List.getElem_mem hi'))]
    rw [e]; exact hA t ht

end GI.Proved
