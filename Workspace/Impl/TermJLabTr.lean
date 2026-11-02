import Workspace.Impl.TermJAutJ3

/-!
# Two presentations of `A = N/N*`

The row terminal gives `φ : N → A` with kernel `N*` (`RowTerminal.φ_ker`); the program works in
the quotient `⟨σN⟩ / ⟨σS⟩` of the Lin* coordinates. Two maps with the same kernel give the same
equalities of labels (`tmJ_phiT_eq_iff`, `tmJLab_eq_sumT_iff`, `tmJSumT_eq_one_iff`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Multicoset

variable {B : Type} {q : ℕ} {N N' : Subgroup (Perm B)} {A A' : Type*} [CommGroup A] [CommGroup A']
  {φ : N →* A} {ψ : N' →* A'}

/-- The kernels agree. -/
def TmJSameKer (φ : N →* A) (ψ : N' →* A') : Prop :=
  (∀ g, g ∈ N ↔ g ∈ N') ∧ ∀ g (h : g ∈ N) (h' : g ∈ N'), φ ⟨g, h⟩ = 1 ↔ ψ ⟨g, h'⟩ = 1

theorem tmJ_phiT_one_iff (hk : TmJSameKer φ ψ) {g : Perm B} (hg : g ∈ N) :
    phiT N φ g = 1 ↔ phiT N' ψ g = 1 := by
  have hg' := (hk.1 g).1 hg
  simp only [phiT, dif_pos hg, dif_pos hg']
  exact hk.2 g hg hg'

theorem tmJ_phiT_eq_iff (hk : TmJSameKer φ ψ) {g g' : Perm B} (hg : g ∈ N) (hg' : g' ∈ N) :
    phiT N φ g = phiT N φ g' ↔ phiT N' ψ g = phiT N' ψ g' := by
  have h1 := (hk.1 g).1 hg
  have h2 := (hk.1 g').1 hg'
  rw [← mul_inv_eq_one, ← phiT_inv hg', ← phiT_mul hg (N.inv_mem hg'),
    tmJ_phiT_one_iff hk (N.mul_mem hg (N.inv_mem hg')), phiT_mul h1 (N'.inv_mem h2), phiT_inv h2,
    mul_inv_eq_one]

/-- The ordered product behind the sum map. -/
def tmJSumP (lg : List (Fin q × Perm B)) (e : Fin lg.length → ℤ) : Perm B :=
  ((List.finRange lg.length).map fun k => (lg.get k).2 ^ e k).prod

theorem tmJSumP_mem {lg : List (Fin q × Perm B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (e : Fin lg.length → ℤ) : tmJSumP lg e ∈ N := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  exact N.zpow_mem (hlg k) _

theorem tmJSumT_eq_phiT {lg : List (Fin q × Perm B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (e : Fin lg.length → ℤ) : tmJSumT N φ lg e = phiT N φ (tmJSumP lg e) := by
  unfold tmJSumT tmJSumP
  rw [phiT_list_prod, Fin.prod_univ_def, List.map_map]
  · congr 1
    apply List.map_congr_left
    intro k _
    exact (phiT_zpow (hlg k) _).symm
  · intro g hg
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact N.zpow_mem (hlg k) _

theorem tmJSumT_eq_one_iff (hk : TmJSameKer φ ψ) {lg : List (Fin q × Perm B)}
    (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N) (e : Fin lg.length → ℤ) :
    tmJSumT N φ lg e = 1 ↔ tmJSumT N' ψ lg e = 1 := by
  rw [tmJSumT_eq_phiT hlg, tmJSumT_eq_phiT fun k => (hk.1 _).1 (hlg k)]
  exact tmJ_phiT_one_iff hk (tmJSumP_mem hlg e)

theorem tmJLab_eq_sumT_iff (hk : TmJSameKer φ ψ) {d : Fin q → Perm B} (hd : ∀ i, d i ∈ N)
    {lg : List (Fin q × Perm B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (e : Fin lg.length → ℤ) :
    tmJLab N φ d = tmJSumT N φ lg e ↔ tmJLab N' ψ d = tmJSumT N' ψ lg e := by
  have hd' : ∀ i, d i ∈ N' := fun i => (hk.1 _).1 (hd i)
  rw [tmJLab_eq_prod hd, tmJLab_eq_prod hd', tmJSumT_eq_phiT hlg,
    tmJSumT_eq_phiT fun k => (hk.1 _).1 (hlg k)]
  exact tmJ_phiT_eq_iff hk (tmJProd_mem hd) (tmJSumP_mem hlg e)

end GI.Impl
