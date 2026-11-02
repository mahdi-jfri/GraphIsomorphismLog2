import Workspace.Impl.TermCosetObjs
import Workspace.Impl.TermCosetMath

/-!
# The computed objects are the coset objects of the types

The table `vs` holds canonical answers of `Iso_H(x_i, y_j)` at `i q + j` (hypothesis
`TmCsTabOK`). For such a table, the facts that `tmCsObjXF` and `tmCsObjYF` record
(`TmCsXObj`, `TmCsYObj`) say that the computed objects are the coset objects `tmCsF H N y` of
the types (`tmCs_x_obj`, `tmCs_y_obj`, `tmCs_ms_x`, `tmCs_ms_y`), that the partner tests of
`tmCsObjsF` test partners (`tmCs_has_x`, `tmCs_has_y`), and that objects of one color have one
group (`tmCs_x_gens`, `tmCs_y_gens`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {n : ℕ} {Ω : Type*} [RAct (Perm (Fin n)) Ω]

/-- The table `vs` holds canonical answers of the coset calls `Iso_H(x_i, y_j)`. -/
def TmCsTabOK (H : Subgroup (Perm (Fin n))) {q : ℕ} (x y : Fin q → Ω) (vs : List Val) : Prop :=
  vs.length = q * q ∧ ∀ i j : Fin q, ∃ v, vs[i.1 * q + j.1]? = some v ∧
    AnsC (Equiv.refl (Fin n)) v (Iso H (x i) (y j))

theorem tmCs_toFin_refl (A : Set (Perm (Fin n))) : toFin (Equiv.refl (Fin n)) '' A = A := by
  have : ∀ a : Perm (Fin n), toFin (Equiv.refl (Fin n)) a = a := fun a => by
    ext; simp [Equiv.permCongr_apply]
  simp [this]

/-- A canonical answer of a coset is `[]` exactly for the empty set, and `[g, gs]` gives the
coset `g ⟨gs⟩`. -/
theorem tmCs_ansC_cons {v : Val} {A : Set (Perm (Fin n))} (h : AnsC (Equiv.refl (Fin n)) v A)
    {g : Perm (Fin n)} {gs : List (Perm (Fin n))} (hv : v = .list [encPerm g, encGroup gs]) :
    A = (fun k => g * k) '' (gens gs : Set (Perm (Fin n))) := by
  rcases h with ⟨rfl, -⟩ | ⟨x, gs', rfl, -, hA⟩
  · cases hv
  · simp only [Val.list.injEq, List.cons.injEq, and_true] at hv
    obtain ⟨h1, h2⟩ := hv
    have hx := encPerm_injective h1
    have hg : gens gs' = gens gs := by
      have hinj := List.map_injective_iff.2 (encPerm_injective (n := n))
      unfold encGroup GI.Cited.encPerms at h2
      simp only [Val.list.injEq, List.cons.injEq, true_and, List.map_cons] at h2
      rw [hinj h2.1]
    rw [tmCs_toFin_refl] at hA
    rw [hA, hx, hg]
    rfl

theorem tmCs_ansC_nil {v : Val} {A : Set (Perm (Fin n))} (h : AnsC (Equiv.refl (Fin n)) v A)
    (hv : v = .list []) : A = ∅ := by
  rcases h with ⟨-, hA⟩ | ⟨x, gs', rfl, -, hA⟩
  · exact hA
  · cases hv

section Table

variable {H N : Subgroup (Perm (Fin n))} {q : ℕ} {x y : Fin q → Ω} {vs : List Val}

theorem tmCs_tab_of (hT : TmCsTabOK H x y vs) : TmCsTab (m := n) vs q := by
  refine ⟨hT.1, fun i hi j hj => ?_⟩
  obtain ⟨v, hv, hA⟩ := hT.2 ⟨i, hi⟩ ⟨j, hj⟩
  refine ⟨v, hv, ?_⟩
  rcases hA with ⟨rfl, -⟩ | ⟨g, gs, rfl, hl, -⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨g, gs, rfl, hl⟩

theorem tmCs_entry_empty (hT : TmCsTabOK H x y vs) {i j : Fin q}
    (h : vs[i.1 * q + j.1]? = some (.list [])) : Iso H (x i) (y j) = ∅ := by
  obtain ⟨v, hv, hA⟩ := hT.2 i j
  rw [h] at hv; cases hv
  exact tmCs_ansC_nil hA rfl

theorem tmCs_entry_cons (hT : TmCsTabOK H x y vs) {i j : Fin q} {g : Perm (Fin n)}
    {gs : List (Perm (Fin n))} (h : vs[i.1 * q + j.1]? = some (.list [encPerm g, encGroup gs])) :
    Iso H (x i) (y j) = (fun k => g * k) '' (gens gs : Set (Perm (Fin n))) := by
  obtain ⟨v, hv, hA⟩ := hT.2 i j
  rw [h] at hv; cases hv
  exact tmCs_ansC_cons hA rfl

theorem tmCs_mem_of_cons (hT : TmCsTabOK H x y vs) {i j : Fin q} {g : Perm (Fin n)}
    {gs : List (Perm (Fin n))} (h : vs[i.1 * q + j.1]? = some (.list [encPerm g, encGroup gs])) :
    g ∈ Iso H (x i) (y j) := by
  rw [tmCs_entry_cons hT h]; exact ⟨1, (gens gs).one_mem, mul_one g⟩

/-- **A nonempty entry of the table is a nonempty transporter.** -/
theorem tmCs_entry_ne (hT : TmCsTabOK H x y vs) (i j : Fin q) :
    (∃ (a : Val) (l : List Val), vs[i.1 * q + j.1]? = some (.list (a :: l))) ↔
      (Iso H (x i) (y j)).Nonempty := by
  obtain ⟨v, hv, hA⟩ := hT.2 i j
  rw [hv]
  rcases hA with ⟨rfl, hA⟩ | ⟨g, gs, rfl, -, hA⟩
  · rw [hA]; simp
  · refine ⟨fun _ => ?_, fun _ => ⟨_, _, rfl⟩⟩
    exact ⟨g, tmCs_mem_of_cons hT hv⟩

theorem tmCs_has_x (hT : TmCsTabOK H x y vs) (i : Fin q) :
    TmCsHas vs (i.1 * q) 1 q ↔ ∃ j : Fin q, (Iso H (x i) (y j)).Nonempty := by
  constructor
  · rintro ⟨j, hj, a, l, h⟩
    rw [one_mul] at h
    exact ⟨⟨j, hj⟩, (tmCs_entry_ne hT i ⟨j, hj⟩).1 ⟨a, l, h⟩⟩
  · rintro ⟨j, hj⟩
    obtain ⟨a, l, h⟩ := (tmCs_entry_ne hT i j).2 hj
    exact ⟨j.1, j.2, a, l, by rw [one_mul]; exact h⟩

theorem tmCs_has_y (hT : TmCsTabOK H x y vs) (j : Fin q) :
    TmCsHas vs j.1 q q ↔ ∃ i : Fin q, (Iso H (x i) (y j)).Nonempty := by
  constructor
  · rintro ⟨i, hi, a, l, h⟩
    rw [show j.1 + q * i = i * q + j.1 by ring] at h
    exact ⟨⟨i, hi⟩, (tmCs_entry_ne hT ⟨i, hi⟩ j).1 ⟨a, l, h⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨a, l, h⟩ := (tmCs_entry_ne hT i j).2 hi
    exact ⟨i.1, i.2, a, l, by rw [show j.1 + q * i.1 = i.1 * q + j.1 by ring]; exact h⟩

/-- The group of a nonempty entry `[g, gs]` of column `j` is `Aut_H(y_j)`. -/
theorem tmCs_entry_aut (hT : TmCsTabOK H x y vs) {i j : Fin q} {g : Perm (Fin n)}
    {gs : List (Perm (Fin n))} (h : vs[i.1 * q + j.1]? = some (.list [encPerm g, encGroup gs])) :
    gens gs = Aut H (y j) :=
  SetLike.ext fun k => tmCs_gens_aut (tmCs_entry_cons hT h) k

variable {σN : List (Perm (Fin n))}

/-- **The group of the object of `x_i`** is `Aut_H(y_c) N`, with `c` its color. -/
theorem tmCs_x_gens (hT : TmCsTabOK H x y vs) (hn : GI.Multicoset.Normalizes H N) (hN : gens σN = N)
    {i : Fin q} {o : ℕ × List (Perm (Fin n)) × Perm (Fin n)} (ho : TmCsXObj vs σN q i o) :
    ∃ hc : o.1 < q, ∀ z, z ∈ gens o.2.1 ↔ ∃ a ∈ Aut H (y ⟨o.1, hc⟩), ∃ k ∈ N, z = a * k := by
  obtain ⟨g, gs, -, hc, -, hv, hgens, -⟩ := ho
  refine ⟨hc, fun z => ?_⟩
  rw [hgens]
  exact tmCs_mem_gens_append hn (tmCs_entry_aut hT (j := ⟨o.1, hc⟩) hv) hN z

/-- **The group of the object of `y_j`** is `Aut_H(y_c) N`, with `c` its color. -/
theorem tmCs_y_gens (hT : TmCsTabOK H x y vs) (hn : GI.Multicoset.Normalizes H N) (hN : gens σN = N)
    {j : Fin q} {o : ℕ × List (Perm (Fin n)) × Perm (Fin n)} (ho : TmCsYObj vs σN q j o) :
    ∃ hc : o.1 < q, ∀ z, z ∈ gens o.2.1 ↔ ∃ a ∈ Aut H (y ⟨o.1, hc⟩), ∃ k ∈ N, z = a * k := by
  obtain ⟨I, g, g', gs, gs', -, hI, -, -, hc, -, hv, hgens, -⟩ := ho
  refine ⟨hc, fun z => ?_⟩
  rw [hgens]
  exact tmCs_mem_gens_append hn (tmCs_entry_aut hT (i := ⟨I, hI⟩) (j := ⟨o.1, hc⟩) hv) hN z

/-- **The object of `x_i` is the coset object of its type.** -/
theorem tmCs_x_obj (hT : TmCsTabOK H x y vs) (hNH : N ≤ H) (hn : GI.Multicoset.Normalizes H N)
    (hN : gens σN = N) {i : Fin q} {o : ℕ × List (Perm (Fin n)) × Perm (Fin n)}
    (ho : TmCsXObj vs σN q i o) :
    tmGlObj o.1 o.2.1 o.2.2 = tmCsF H N y (orbitN N (x i)) := by
  obtain ⟨hc, hL⟩ := tmCs_x_gens hT hn hN ho
  obtain ⟨g, gs, hrep, -, hemp, hv, -, -⟩ := ho
  have hg := tmCs_mem_of_cons hT (j := ⟨o.1, hc⟩) hv
  have hstar : tmCsStar H N y (orbitN N (x i)) = o.1 := by
    refine tmCsStar_eq ((tmCs_in_iff hNH (x i) ⟨o.1, hc⟩).2 ⟨g, hg⟩) fun j' hj' hin => ?_
    have hj'q : j' < q := by omega
    have := (tmCs_in_iff hNH (x i) ⟨j', hj'q⟩).1 hin
    rw [tmCs_entry_empty hT (j := ⟨j', hj'q⟩) (hemp j' hj')] at this
    exact Set.not_nonempty_empty this
  refine tmCs_obj_eq hNH hn hc hstar hL (h := o.2.2) ?_ ?_
  · rw [hrep]; exact H.inv_mem hg.1
  · rw [hrep, ← hg.2, act_act, mul_inv_cancel, act_one]

/-- **The object of `y_j` is the coset object of its type.** -/
theorem tmCs_y_obj (hT : TmCsTabOK H x y vs) (hNH : N ≤ H) (hn : GI.Multicoset.Normalizes H N)
    (hN : gens σN = N) {j : Fin q} {o : ℕ × List (Perm (Fin n)) × Perm (Fin n)}
    (ho : TmCsYObj vs σN q j o) :
    tmGlObj o.1 o.2.1 o.2.2 = tmCsF H N y (orbitN N (y j)) := by
  obtain ⟨hc, hL⟩ := tmCs_y_gens hT hn hN ho
  obtain ⟨I, g, g', gs, gs', hrep, hI, -, hv', -, hemp, hv, -, -⟩ := ho
  have hg := tmCs_mem_of_cons hT (i := ⟨I, hI⟩) (j := ⟨o.1, hc⟩) hv
  have hg' := tmCs_mem_of_cons hT (i := ⟨I, hI⟩) (j := j) hv'
  have hstar : tmCsStar H N y (orbitN N (y j)) = o.1 := by
    refine tmCsStar_eq ((tmCs_in_iff_y hNH (j' := ⟨o.1, hc⟩) hg').2 ⟨g, hg⟩) fun j' hj' hin => ?_
    have hj'q : j' < q := by omega
    have := (tmCs_in_iff_y hNH (j' := ⟨j', hj'q⟩) hg').1 hin
    rw [tmCs_entry_empty hT (i := ⟨I, hI⟩) (j := ⟨j', hj'q⟩) (hemp j' hj')] at this
    exact Set.not_nonempty_empty this
  refine tmCs_obj_eq hNH hn hc hstar hL (h := o.2.2) ?_ ?_
  · rw [hrep]; exact H.mul_mem (H.inv_mem hg.1) hg'.1
  · rw [hrep, ← hg.2, act_act, mul_inv_cancel_left, hg'.2]

/-- A list of `q` objects indexed by the rows gives the multiset of the rows. -/
theorem tmCs_ms_list {F : Set Ω → CObj ℕ (Perm (Fin n))} {z : Fin q → Ω}
    {OX : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))} (hl : OX.length = q)
    (hf : ∀ i (hi : i < q), tmGlObj (OX[i]'(by omega)).1 (OX[i]'(by omega)).2.1
      (OX[i]'(by omega)).2.2 = F (orbitN N (z ⟨i, hi⟩))) :
    tmGlMs OX = (types N z).map F := by
  have hOX : OX = (List.finRange q).map fun i => OX[i.1]'(by omega) := by
    apply List.ext_getElem (by simp [hl])
    intro k h1 h2
    simp
  rw [hOX]
  exact tmCs_ms_rows _ fun i => hf i.1 i.2

end Table

/-! ### The residual set from the answer on the supplement -/

section Res

variable {H N : Subgroup (Perm (Fin n))} {q : ℕ} {x y : Fin q → Ω}

/-- The residual set of Corollary A.22 in the radical coset `R r`. -/
def tmCsResSet (H N : Subgroup (Perm (Fin n))) (x y : Fin q → Ω) (r : Perm (Fin n)) :
    Set (Perm (Fin n)) :=
  {h | h ∈ Iso H (types N x) (types N y) ∧ ∃ z ∈ radicalPreimage H N, h = z * r}

/-- **No partner, no transporter.** -/
theorem tmCs_res_empty (hNH : N ≤ H) (hn : GI.Multicoset.Normalizes H N) {r : Perm (Fin n)}
    (h : ¬((∀ i, ∃ j, (Iso H (x i) (y j)).Nonempty) ∧ (∀ j, ∃ i, (Iso H (x i) (y j)).Nonempty))) :
    tmCsResSet H N x y r = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hg, -⟩
  exact h ⟨tmCs_partner_x hNH hn hg, tmCs_partner_y hNH hn hg⟩

/-- A supplement `S` of `N` in `R` covers `R` as `N S`. -/
theorem tmCs_cover {R S : Subgroup (Perm (Fin n))} (hSN : GI.Multicoset.Normalizes S N)
    (hsup : S ⊔ N = R) : ∀ z ∈ R, ∃ m ∈ N, ∃ s ∈ S, z = m * s := by
  intro z hz
  rw [← hsup, Subgroup.sup_eq_closure] at hz
  obtain ⟨s, hs, k, hk, rfl⟩ := closure_mem_mul hSN (fun γ hγ => by
    rcases hγ with h | h
    · exact ⟨γ, h, 1, N.one_mem, by simp⟩
    · exact ⟨1, S.one_mem, γ, h, by simp⟩) z hz
  exact ⟨s * k * s⁻¹, hSN s hs k hk, s, hs, by group⟩

/-- The group of a canonical answer of a transporter in `S` lies in `S`. -/
theorem tmCs_gens_le {S : Subgroup (Perm (Fin n))} {A : Set (Perm (Fin n))} (hA : A ⊆ S)
    {x0 : Perm (Fin n)} {gs : List (Perm (Fin n))}
    (he : A = (fun k => x0 * k) '' (gens gs : Set (Perm (Fin n)))) : gens gs ≤ S := by
  intro g hg
  have h1 : x0 ∈ A := by rw [he]; exact ⟨1, (gens gs).one_mem, mul_one x0⟩
  have h2 : x0 * g ∈ A := by rw [he]; exact ⟨g, hg, rfl⟩
  have := S.mul_mem (S.inv_mem (hA h1)) (hA h2)
  simpa using this

end Res

end GI.Impl
