module

public import Workspace.Impl.TermJHTail
public import Workspace.Impl.RowPure

@[expose] public section

/-!
# The transporter of one label: the main theorem

For one label `h` the program `tmJHMainF` builds the `J`-transporter `t_h` by the route of
Theorem A.23: lift `(h; 1)` by NormalizedFactor in `⟨G|_dom, N^q⟩`, take the local transporter
`z`, decode `u = z⁻¹ g = (d, π)`, solve the zero-sum equation for `c`, read the parity of `π`, and
return `t_h = z · tmJCorrE Tl odd lg c`. The final theorem `tmJH_spec` is not proved yet. This
file holds the facts it needs beyond `tmJH_tail_spec`.

The facts proved here first:
* `tmJH_D_norm`: the pairs of one class normalize `N^q`, so `G|_dom` normalizes `N^q`
  (`tmJH_normalizes`).
* `tmJH_const_fac`: `(h; 1) = (k(h); 1) · (d; 1)` with all `d i ∈ N`, so `(h; 1)` lies in
  `G|_dom · N^q` (the precondition of NormalizedFactor).
* `tmJH_odd_ne`: if `π` is odd then `Tl` is not empty.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Paper GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens encInt encIntMatrix)
open scoped IsMulCommutative

/-! ### `N^q` is normalized by the pairs of one class -/

theorem tmJH_D_norm {B : Type} [Nonempty B] {q : ℕ} {H N : Subgroup (Perm B)}
    (hn : GI.Multicoset.Normalizes H N) {g : Perm (B × Fin q)} (hg : g ∈ tmJD H N hn)
    {d : Fin q → Perm B} (hd : ∀ i, d i ∈ N) :
    ∃ d' : Fin q → Perm B, (∀ i, d' i ∈ N) ∧ g * tmJP (d, 1) * g⁻¹ = tmJP (d', 1) := by
  have hw : tmJP (d, 1) ∈ tmJW (q := q) N := ⟨(d, 1), hd, rfl⟩
  obtain ⟨p'', hp'', he⟩ := tmJD_normalizes_W hn hg hw
  obtain ⟨h, hh, p, hp, rfl⟩ := hg
  obtain ⟨Y, hY⟩ : ∃ Y, tmJP p * tmJP (d, 1) * (tmJP p)⁻¹ = tmJP (Y, 1) := by
    rw [tmJP_inv, tmJP_mul, tmJP_mul]
    exact ⟨_, congrArg tmJP (Prod.ext rfl (by simp))⟩
  have e : p'' = (Y, 1) := tmJP_injective (he.trans hY)
  subst e
  exact ⟨Y, hp'', hY⟩

section RT

attribute [local instance] stringRAct

variable {Ω C : Type} {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- **The constant pair factors**: `(h; 1) = (k(h); 1) · (d; 1)` with `d i = h k_i(h)⁻¹ ∈ N`. -/
theorem tmJH_const_fac {h : Perm I.B} (hh : h ∈ I.Hb) :
    ∃ g ∈ tmJG I, ∃ d : Fin L.q → Perm I.B, (∀ i, d i ∈ I.Nb) ∧
      tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * tmJP (d, 1) := by
  have hg : tmJP (rowLift I.e I.i0 h, 1) ∈ tmJG I := by
    refine (tmJG_mem_iff I).2 ⟨_, ⟨h, hh, 1, ⟨fun _ => I.Nb.one_mem, ?_, ?_⟩, by simp⟩, rfl⟩
    · simp [phiT_one]
    · exact Subgroup.one_mem _
  refine ⟨_, hg, fun i => h * (rowLift I.e I.i0 h i)⁻¹, fun i => ?_, ?_⟩
  · have e : h * (rowLift I.e I.i0 h i)⁻¹ = h * (h⁻¹ * rowLift I.e I.i0 h i)⁻¹ * h⁻¹ := by group
    show h * (rowLift I.e I.i0 h i)⁻¹ ∈ I.Nb
    rw [e]
    exact I.normalizes h hh _ (I.Nb.inv_mem (I.lift_mem hh i))
  · rw [tmJP_mul]
    congr 1
    ext1
    · funext i; simp
    · simp

/-- **An odd top needs a transposition.** -/
theorem tmJH_odd_ne [Nonempty I.B] {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r)
    {g w z : Perm (I.B × Fin L.q)} (hg : g ∈ tmJG I) (hw : w ∈ tmJW I.Nb)
    (hf : tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * w)
    (hzY : tmJStr (rowTuple I.e S.y) ∘ z = tmJStr (rowTuple I.e S.x))
    (hzc : z ∈ tmJCls I.Nb h) {d : Fin L.q → Perm I.B} {π : Perm (Fin L.q)}
    (hd : ∀ i, d i ∈ I.Nb) (he : z⁻¹ * g = tmJP (d, π))
    {lg : List (Fin L.q × Perm I.B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ I.Nb)
    {Tl : List (Fin L.q × Fin L.q × Perm I.B)} (hTl : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ I.Nb)
    (hAut : tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)) ≤
      Subgroup.closure (tmJHLocs lg ∪ tmJHSws Tl)) :
    sign π = -1 → Tl ≠ [] := by
  intro ho
  have hhH : h ∈ I.Hb := tmJ_lab_le I hL
  have hgc : g ∈ tmJCls I.Nb h := tmJ_lift_cls I.normalizes hw hf hhH
  have hu : z⁻¹ * g ∈ tmJW I.Nb := tmJ_u_mem I hhH hzc hgc
  obtain ⟨-, htu⟩ := tmJH_lab_u I hu hd he
  obtain ⟨a0, ha0, -, hs0⟩ := tmJ_corr_exists I hr hL hg hw hf hzY hzc hu
  have hodd' : sign (tmJTop I.Nb a0) = -1 := by
    rw [tmJTop, dif_pos (show a0 ∈ tmJW I.Nb from ha0.1), hs0, htu]
    exact ho
  exact tmJ_odd_ne (tmJH_locs_top hlg) hTl (hAut ha0) hodd'

/-- **`G|_dom` normalizes `N^q`** on `Fin n`, for generator lists of the two groups. -/
theorem tmJH_normalizes [Nonempty I.B] {n : ℕ} (e : I.B × Fin L.q ≃ Fin n)
    {gsG gsNq : List (Perm (Fin n))} (hG : gens gsG = (tmJG I).map (toFin e).toMonoidHom)
    (hNq : ∀ σ, σ ∈ gens gsNq ↔
      ∃ d : Fin L.q → Perm I.B, (∀ i, d i ∈ I.Nb) ∧ σ = toFin e (tmJP (d, 1))) :
    GI.Lang.Normalizes (gens gsG) (gens gsNq) := by
  intro g hg x hx
  rw [hG] at hg
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨d, hd, rfl⟩ := (hNq x).1 hx
  obtain ⟨d', hd', he⟩ := tmJH_D_norm I.normalizes (tmJG_le_D I hσ) hd
  refine (hNq _).2 ⟨d', hd', ?_⟩
  rw [← he]
  simp [map_mul, map_inv]

end RT

end GI.Impl
