module

public import Workspace.NormalTransposeColumns
public import Workspace.NormalTranspose

@[expose] public section

/-!
# Lemma A.14: the interchange for the concrete clean product

The proof of Lemma A.14: "Explicitly, modulo `𝓜`, write the clean product as
`Alt(m) × Q`. The cell and row stabilizers are `Alt(m-1) × U` and `Alt(m-1) × Q`,
respectively. Each intermediate subgroup contains `Alt(m-1) × 1` and is therefore
exactly `Alt(m-1) × V` for some `U ≤ V ≤ Q`."

Here `Q = H/N`. From a clean row normal form (`IsRowNormalForm`) and the top action
`top : G → Alt(m)` with kernel `K`, for which `s` is a section, we build
`π = (top, θ) : G → Alt(m) × H/N`, with `θ` the diagonal map of the normal form, and
prove that `π` is onto with kernel `M`. The physical cell and row stabilizers are
then preimages of `Alt(m-1) × U` and `Alt(m-1) × Q`, every subgroup between them is
the preimage of some `Alt(m-1) × V`, and the indices of these preimages are the
indices in `Alt(m) × H/N` (`GI.NormalTranspose.ratio_interchange`).
-/

namespace GI.NormalTranspose

open Equiv GI.Paper

variable {V B I : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Perm V)} {K : Subgroup G} {e : B × I ≃ V}
variable {s : alternatingGroup I →* G} {i0 : I}
variable {N Nstar : Subgroup (cleanLocalGroup G e i0)} [N.Normal] [Nstar.Normal]

/-- The clean product map `π = (top, θ) : G → Alt(m) × H/N`. -/
def cleanProduct (top : G →* alternatingGroup I) (θ : G →* cleanLocalGroup G e i0 ⧸ N) :
    G →* alternatingGroup I × (cleanLocalGroup G e i0 ⧸ N) :=
  top.prod θ

/-- The cell `{i} × Δ` of points in row `i` and column `Δ`. -/
def InCell (e : B × I ≃ V) (N : Subgroup (cleanLocalGroup G e i0)) (i : I)
    (Δ : Quotient (MulAction.orbitRel N B)) (v : V) : Prop :=
  (e.symm v).2 = i ∧ colOf e N v = Δ

/-- The physical stabilizer of the cell `{i} × Δ`. -/
def cellStab (e : B × I ≃ V) (N : Subgroup (cleanLocalGroup G e i0)) (i : I)
    (Δ : Quotient (MulAction.orbitRel N B)) : Subgroup G where
  carrier := {g | ∀ v, InCell e N i Δ (g.val v) ↔ InCell e N i Δ v}
  one_mem' := fun v => Iff.rfl
  mul_mem' := by
    intro g h hg hh v
    change InCell e N i Δ (g.val (h.val v)) ↔ _
    rw [hg, hh]
  inv_mem' := by
    intro g hg v
    rw [← hg]
    change InCell e N i Δ (g.val (g.val⁻¹ v)) ↔ _
    rw [Perm.apply_inv_self]

/-- The physical stabilizer of row `i`. -/
def rowStab (e : B × I ≃ V) (i : I) : Subgroup G where
  carrier := {g | ∀ v, (e.symm (g.val v)).2 = i ↔ (e.symm v).2 = i}
  one_mem' := fun v => Iff.rfl
  mul_mem' := by
    intro g h hg hh v
    change (e.symm (g.val (h.val v))).2 = i ↔ _
    rw [hg, hh]
  inv_mem' := by
    intro g hg v
    rw [← hg]
    change (e.symm (g.val (g.val⁻¹ v))).2 = i ↔ _
    rw [Perm.apply_inv_self]

variable (top : G →* alternatingGroup I)
  (htop : ∀ (g : G) b i, (e.symm (g.val (e (b, i)))).2 = (top g : Perm I) i)

include htop

omit [N.Normal] [Nstar.Normal] in
theorem top_apply (g : G) (v : V) : (e.symm (g.val v)).2 = (top g : Perm I) (e.symm v).2 := by
  have := htop g (e.symm v).1 (e.symm v).2
  simpa using this

omit [N.Normal] [Nstar.Normal] in
/-- The row stabilizer is `top⁻¹(Alt(m-1))`. -/
theorem rowStab_eq [Nonempty B] (i : I) :
    rowStab e i = (MulAction.stabilizer (alternatingGroup I) i).comap top := by
  ext g
  change (∀ v, _ ↔ _) ↔ (top g : Perm I) i = i
  constructor
  · intro h
    obtain ⟨b⟩ := ‹Nonempty B›
    have := (h (e (b, i))).mpr (by simp)
    rw [top_apply top htop] at this
    simpa using this
  · intro h v
    rw [top_apply top htop]
    constructor
    · intro hv
      rw [← h] at hv
      exact (top g : Perm I).injective hv
    · intro hv
      rw [hv, h]

section Product

variable (hRNF : IsRowNormalForm G K e i0 s N Nstar)
  (htopK : top.ker = K) (htops : ∀ p, top (s p) = p)
  (θ : G →* cleanLocalGroup G e i0 ⧸ N)
  (hθK : Function.Surjective (θ.comp K.subtype))
  (hθker : θ.ker = rowNormalM G K e i0 N ⊔ s.range)

omit htop in
include htopK htops hθK hθker in
/-- `π = (top, θ)` is onto `Alt(m) × H/N`. -/
theorem cleanProduct_surjective : Function.Surjective (cleanProduct top θ) := by
  rintro ⟨a, h⟩
  obtain ⟨k, hk⟩ := hθK h
  refine ⟨s a * k.val, Prod.ext ?_ ?_⟩
  · change top (s a * k.val) = a
    have hk1 : top k.val = 1 := by
      rw [← MonoidHom.mem_ker, htopK]; exact k.property
    rw [map_mul, hk1, mul_one, htops]
  · change θ (s a * k.val) = h
    have hs1 : θ (s a) = 1 := by
      rw [← MonoidHom.mem_ker, hθker]; exact Subgroup.mem_sup_right ⟨a, rfl⟩
    rw [map_mul, hs1, one_mul]
    exact hk

omit htop in
include hRNF htopK htops hθker in
/-- The kernel of `π = (top, θ)` is `M`: so `G/M ≅ Alt(m) × H/N`. -/
theorem cleanProduct_ker : (cleanProduct top θ).ker = rowNormalM G K e i0 N := by
  haveI := hRNF.m_normal
  ext g
  rw [MonoidHom.mem_ker]
  change (top g, θ g) = 1 ↔ _
  rw [Prod.mk_eq_one]
  constructor
  · rintro ⟨htg, hθg⟩
    have hg : g ∈ rowNormalM G K e i0 N ⊔ s.range := by
      rw [← hθker]; exact hθg
    obtain ⟨m, hm, r, ⟨p, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have hm1 : top m = 1 := by
      rw [← MonoidHom.mem_ker, htopK]; exact hRNF.m_le hm
    rw [map_mul, hm1, one_mul, htops] at htg
    rw [htg, map_one, mul_one]
    exact hm
  · intro hm
    refine ⟨?_, ?_⟩
    · rw [← MonoidHom.mem_ker, htopK]; exact hRNF.m_le hm
    · rw [← MonoidHom.mem_ker, hθker]; exact Subgroup.mem_sup_left hm

/-- The stabilizer of row `i` in `Alt(m)`, the paper's `Alt(m-1)`. -/
abbrev rowFix (i : I) : Subgroup (alternatingGroup I) := MulAction.stabilizer (alternatingGroup I) i

omit htop [Nstar.Normal] in
theorem comap_rowFix_top (i : I) :
    ((rowFix i).prod ⊤).comap (cleanProduct top θ) = (rowFix i).comap top := by
  ext g
  simp [cleanProduct, Subgroup.mem_prod]

omit htop in
include hRNF htopK htops hθker in
/-- "The cell ... stabilizer" contains `π⁻¹(Alt(m-1) × 1)`: an element `m s(p)`, with
`m ∈ M` and `p` fixing row `i`, keeps row `i` and moves each point inside its
`M`-orbit, a cell (`m_orbit_iff`). -/
theorem cellStab_lower (hm : 2 ≤ Fintype.card I) (i : I) (Δ : Quotient (MulAction.orbitRel N B))
    (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) :
    ((rowFix i).prod ⊥).comap (cleanProduct top θ) ≤ cellStab e N i Δ := by
  haveI := hRNF.m_normal
  intro g hg
  obtain ⟨hgA, hgθ⟩ := hg
  have hθg : θ g = 1 := Subgroup.mem_bot.mp hgθ
  have hg' : g ∈ rowNormalM G K e i0 N ⊔ s.range := by
    rw [← hθker]; exact hθg
  obtain ⟨m, hmM, r, ⟨p, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
  have hm1 : top m = 1 := by
    rw [← MonoidHom.mem_ker, htopK]; exact hRNF.m_le hmM
  have hpi : (p : Perm I) i = i := by
    have : (top (m * s p) : Perm I) i = i := hgA
    rwa [map_mul, hm1, one_mul, htops] at this
  intro v
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective v
  have hmv : ∃ g ∈ rowNormalM G K e i0 N,
      g.val (e (b, (p : Perm I) j)) = e (e.symm (m.val (e (b, (p : Perm I) j)))) :=
    ⟨m, hmM, by simp⟩
  obtain ⟨hrow, n, hn⟩ := (m_orbit_iff hRNF b _ _ _ hm).mp hmv
  change (p : Perm I) j = (e.symm (m.val (e (b, (p : Perm I) j)))).2 at hrow
  change n • b = (e.symm (m.val (e (b, (p : Perm I) j)))).1 at hn
  have hval : (m * s p).val (e (b, j)) = m.val (e (b, (p : Perm I) j)) := by
    change m.val ((s p).val (e (b, j))) = _
    rw [hpure]
  have hcol : (Quotient.mk _ (e.symm (m.val (e (b, (p : Perm I) j)))).1 :
      Quotient (MulAction.orbitRel N B)) = Quotient.mk _ b :=
    Quotient.sound ⟨n, hn⟩
  change ((e.symm ((m * s p).val (e (b, j)))).2 = i ∧
      colOf e N ((m * s p).val (e (b, j))) = Δ) ↔ ((e.symm (e (b, j))).2 = i ∧ colOf e N (e (b, j)) = Δ)
  rw [hval, colOf, hcol, ← hrow, e.symm_apply_apply, colOf_apply]
  have : (p : Perm I) j = i ↔ j = i := by
    conv_lhs => rw [← hpi]
    exact (p : Perm I).injective.eq_iff
  rw [this]

omit [N.Normal] [Nstar.Normal] in
/-- "The cell and row stabilizers": the cell stabilizer lies in the row stabilizer
(the cell is nonempty, and its row is determined). -/
theorem cellStab_le_rowStab (i : I) (Δ : Quotient (MulAction.orbitRel N B)) :
    cellStab e N i Δ ≤ (rowFix i).comap top := by
  intro g hg
  obtain ⟨b₀, rfl⟩ := Quotient.exists_rep Δ
  have hin : InCell e N i (Quotient.mk _ b₀) (e (b₀, i)) := by
    refine ⟨by simp, ?_⟩
    rw [colOf_apply]
  have := ((hg (e (b₀, i))).mpr hin).1
  rw [htop] at this
  exact this

omit htop in
include htopK htops hθK hθker in
/-- Indices of preimages under `π` are indices in `Alt(m) × H/N`. -/
theorem relIndex_comap_cleanProduct (S T : Subgroup (alternatingGroup I × (cleanLocalGroup G e i0 ⧸ N))) :
    (S.comap (cleanProduct top θ)).relIndex (T.comap (cleanProduct top θ)) = S.relIndex T := by
  rw [Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (cleanProduct_surjective top htopK htops θ hθK hθker)]

omit htop in
include hRNF htopK htops hθK hθker in
/-- "Each intermediate subgroup contains `Alt(m-1) × 1` and is therefore exactly
`Alt(m-1) × V`": every subgroup of `G` between the cell stabilizer and the row
stabilizer is `π⁻¹(Alt(m-1) × V)`, with `V` its image in `H/N`. In particular the cell
stabilizer is `π⁻¹(Alt(m-1) × U)`. -/
theorem intermediate_eq (hm : 2 ≤ Fintype.card I) (i : I) (Δ : Quotient (MulAction.orbitRel N B))
    (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) (X : Subgroup G)
    (hlow : cellStab e N i Δ ≤ X) (hhigh : X ≤ (rowFix i).comap top) :
    X = ((rowFix i).prod ((X.map (cleanProduct top θ)).map (MonoidHom.snd _ _))).comap
      (cleanProduct top θ) := by
  have hsurj := cleanProduct_surjective top htopK htops θ hθK hθker
  have hker := cleanProduct_ker top hRNF htopK htops θ hθker
  have hcell := cellStab_lower top hRNF htopK htops θ hθker hm i Δ hpure
  have hMX : (cleanProduct top θ).ker ≤ X := by
    refine le_trans ?_ (hcell.trans hlow)
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    change cleanProduct top θ g ∈ (rowFix i).prod ⊥
    rw [hg]
    exact Subgroup.one_mem _
  have hlow' : (rowFix i).prod ⊥ ≤ X.map (cleanProduct top θ) := by
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj ((rowFix i).prod ⊥)]
    exact Subgroup.map_mono (hcell.trans hlow)
  have hhigh' : X.map (cleanProduct top θ) ≤ (rowFix i).prod ⊤ := by
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj ((rowFix i).prod ⊤),
      comap_rowFix_top top θ]
    exact Subgroup.map_mono hhigh
  rw [← prod_intermediate _ _ hlow' hhigh', Subgroup.comap_map_eq,
    sup_eq_left.mpr hMX]

end Product

end GI.NormalTranspose
