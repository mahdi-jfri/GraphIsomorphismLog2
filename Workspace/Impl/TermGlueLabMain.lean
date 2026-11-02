import Workspace.Impl.TermGlueLabGroup
import Workspace.Impl.TermCosetMath

/-!
# Local transporters and the empty case of the label step

Proof of Theorem A.23. For `h` in the residual set `Res = tmGlRes I r`, the type
multiset of `x` moved by `h` is that of `y`. So the rows can be matched by type, and local
transporters `n_i ∈ N` exist (`tmGL_z_exists`). An empty residual set gives an empty label coset
(`tmGL_lab_res_empty`).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type}

/-- **A matching from equal multisets.** If `f` and `g` list the same multiset, some
permutation `π` has `g ∘ π = f`: match the fibers of each value, which have equal sizes. -/
theorem tmGL_exists_perm {α : Type} {q : ℕ} {f g : Fin q → α}
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ π : Perm (Fin q), ∀ i, g (π i) = f i := by
  classical
  have hc : ∀ c, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.filter_val, eq_comm] using this
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c), Equiv.ofFiberEquiv_map _⟩

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- The string `X` of the rows of `x`. -/
abbrev tmGLX : I.B × Fin L.q → C := tmGLStr (rowTuple I.e S.x)

/-- The string `Y` of the rows of `y`. -/
abbrev tmGLY : I.B × Fin L.q → C := tmGLStr (rowTuple I.e S.y)

/-- **The residual set is a union of `N`-cosets.** -/
theorem tmGL_res_N {r : Perm I.B} (hr : r ∈ I.Hb) {h n : Perm I.B} (hh : h ∈ tmGlRes I r)
    (hn : n ∈ I.Nb) : h * n ∈ tmGlRes I r := by
  obtain ⟨⟨hhH, hT⟩, x, hx, rfl⟩ := hh
  have hNR := (radicalPreimage_spec I.Nb_le I.normalizes).2.1
  have hT' : (types I.Nb (rowTuple I.e S.x) : Multiset (Set (I.B → C))) ↼ (x * r * n) =
      types I.Nb (rowTuple I.e S.y) := by
    rw [← act_act, hT, multiset_act_def]
    conv_rhs => rw [← Multiset.map_id (types I.Nb (rowTuple I.e S.y))]
    exact Multiset.map_congr rfl fun t ht => fixes_types I.Nb (rowTuple I.e S.y) n hn t ht
  refine ⟨⟨I.Hb.mul_mem hhH (I.Nb_le hn), hT'⟩, x * (r * n * r⁻¹), (tmRad I).mul_mem hx
    (hNR (I.normalizes r hr n hn)), by group⟩

/-- **Local transporters exist on the residual set.** For `h ∈ Res`, the type multiset of `x`
moved by `h` is that of `y`, so a matching `π` and elements `n_i ∈ N` with `x_i^{h n_i} = y_{π i}`
exist. The pair `(h n_i; π)` has class `h` and carries `Y` to `X`. -/
theorem tmGL_z_exists {r h : Perm I.B} (hh : h ∈ tmGlRes I r) :
    ∃ σ, tmGLCls I.Nb h σ ∧ tmGLY I ∘ σ = tmGLX I := by
  obtain ⟨⟨hH, hT⟩, -⟩ := hh
  rw [types, types, multiset_act_def, Multiset.map_map] at hT
  have hT' : Finset.univ.val.map (fun i => orbitN I.Nb (rowTuple I.e S.x i ↼ h)) =
      Finset.univ.val.map (fun i => orbitN I.Nb (rowTuple I.e S.y i)) := by
    rw [← hT]
    exact Multiset.map_congr rfl fun i _ => (orbitN_act I.normalizes hH _).symm
  obtain ⟨π, hπ⟩ := tmGL_exists_perm hT'
  have hn : ∀ i, ∃ n ∈ I.Nb, rowTuple I.e S.x i ↼ h ↼ n = rowTuple I.e S.y (π i) := by
    intro i
    have : rowTuple I.e S.y (π i) ∈ orbitN I.Nb (rowTuple I.e S.y (π i)) :=
      ⟨1, I.Nb.one_mem, act_one _⟩
    rw [hπ i] at this
    exact this
  choose n hnN hne using hn
  refine ⟨tmGLP (fun i => h * n i, π), ⟨_, _, rfl, fun i => by simpa using hnN i⟩, ?_⟩
  rw [tmGL_str_comp]
  intro i
  rw [← hne i, act_act]
  rfl

/-- **An empty residual set gives an empty label coset.** -/
theorem tmGL_lab_res_empty {r : Perm I.B} (h : tmGlRes I r = ∅) : tmGlLab I r = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hg
  have : g ∈ tmGlRes I r := hg.1
  rw [h] at this
  exact this

end RT

end GI.Impl
