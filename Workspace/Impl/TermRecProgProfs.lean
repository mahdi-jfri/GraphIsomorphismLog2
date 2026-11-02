import Workspace.Impl.TermRecProgProf

/-!
# T5, the profiles of one side

`tmRi_profs_spec`: the map `b + 78` over `[0, …, m - 1]` with context `[gens A, table, o]`
returns the profiles of the pieces `P_o, …, P_{o+m-1}` (`tmRi_prof_spec` for each).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

theorem tmRi_wt_profOut {H A : Subgroup (Perm (Fin n))} {Ps : List (List (TmRiO n))} {j : ℕ}
    {ob : TmRiO n} (h : TmRiProfOut H A Ps j ob) :
    (tmGlObjVal ob).wt ≤ 2 * Ps.length + 700 * (n + 1) ^ 6 := by
  have h1 := wt_list3_le (.nat ob.1) (encGroup ob.2.1) (encPerm ob.2.2)
  have h2 := wt_nat_le ob.1
  have h3 := wt_encGroup_le_sq h.2.2.2.2.1
  have h4 := wt_encPerm_le ob.2.2
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have := h.1
  show (Val.list [.nat ob.1, encGroup ob.2.1, encPerm ob.2.2]).wt ≤ _
  omega

theorem tmRiProfC_mono (hm : Membership) (n : ℕ) {W W' : ℕ} (h : W ≤ W') :
    tmRiProfC hm n W ≤ tmRiProfC hm n W' := by
  unfold tmRiProfC
  have := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2
  omega

theorem tmRi_forall₂_enc {α β : Type} {f : β → Val} {Q : α → β → Prop} :
    ∀ {xs : List α} {ws : List Val},
      List.Forall₂ (fun x w => ∃ p : β, w = f p ∧ Q x p) xs ws →
      ∃ ps : List β, ws = ps.map f ∧ List.Forall₂ Q xs ps
  | [], [], _ => ⟨[], rfl, List.Forall₂.nil⟩
  | _ :: _, _ :: _, List.Forall₂.cons ⟨p, hp, hq⟩ h =>
    let ⟨ps, e, h'⟩ := tmRi_forall₂_enc h
    ⟨p :: ps, by rw [hp, e]; rfl, List.Forall₂.cons hq h'⟩

/-- **The profiles of `m` pieces from position `o`.** -/
theorem tmRi_profs_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {σA : List (Perm (Fin n))}
    (hAl : σA.length ≤ n ^ 2) {H : Subgroup (Perm (Fin n))} {Ps : List (List (TmRiO n))}
    {tab : List Val} (ht : TmRiTab H Ps tab) {o m : ℕ} (hm : o + m ≤ Ps.length) {Wa : ℕ}
    (hWa : (Val.list [encGroup σA, .list tab, .nat o]).wt + m + 10 ≤ Wa) :
    FunAll P (b + 78) (.list [.list [encGroup σA, .list tab, .nat o], natList (List.range m)])
      (fun w cost => ∃ obs : List (TmRiO n), w = .list (obs.map tmGlObjVal) ∧
        obs.length = m ∧ (∀ i (hi : i < obs.length), TmRiProfOut H (gens σA) Ps (o + i) obs[i]) ∧
        w.wt ≤ m * (2 * (2 * Ps.length + 700 * (n + 1) ^ 6) + 1) + 4 ∧
        cost ≤ m * tmRiProfC hmem n (3 * Wa) +
          mapK * (m + 1) * ((Val.list [.list [encGroup σA, .list tab, .nat o],
            natList (List.range m)]).wt + m * (2 * (2 * Ps.length + 700 * (n + 1) ^ 6) + 1) + 5)) := by
  set c0 : Val := .list [encGroup σA, .list tab, .nat o] with hc0
  have hf : ∀ x ∈ (List.range m).map Val.nat, FunAll P (b + 13) (.list [c0, x]) (fun w cost =>
      (∃ i < m, x = .nat i ∧ ∃ ob, w = tmGlObjVal ob ∧ TmRiProfOut H (gens σA) Ps (o + i) ob) ∧
      w.wt ≤ 2 * Ps.length + 700 * (n + 1) ^ 6 ∧ cost ≤ tmRiProfC hmem n (3 * Wa)) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hi
    refine (tmRi_prof_spec hP hAl ht (o := o) (i := i) (by omega)).mono fun w cw h => ?_
    obtain ⟨⟨ob, rfl, hob⟩, hcw⟩ := h
    refine ⟨⟨i, hi, rfl, ob, rfl, hob⟩, tmRi_wt_profOut hob, le_trans hcw ?_⟩
    have h1 := wt_list2_le c0 (.nat i)
    have h2 := wt_nat_le i
    have e : (Val.list [c0, .nat i]).wt =
        (Val.list [Val.list [encGroup σA, .list tab, .nat o], .nat i]).wt := rfl
    exact tmRiProfC_mono hmem n (by omega)
  refine (tmRi_mapU hP.mapProf hf).mono fun w cw ⟨ws, hw, hR, hww, hcw⟩ => ?_
  have hR' : List.Forall₂ (fun x w => ∃ ob : TmRiO n, w = tmGlObjVal ob ∧
      ∃ i < m, x = .nat i ∧ TmRiProfOut H (gens σA) Ps (o + i) ob) ((List.range m).map Val.nat) ws :=
    hR.imp fun x w ⟨i, hi, hx, ob, hob, hp⟩ => ⟨ob, hob, i, hi, hx, hp⟩
  obtain ⟨obs, rfl, hQ⟩ := tmRi_forall₂_enc hR'
  have hl : obs.length = m := by
    have := hQ.length_eq; simpa using this.symm
  have hlx : ((List.range m).map Val.nat).length = m := by simp
  refine ⟨obs, hw, hl, fun i hi => ?_, by rw [hlx] at hww; exact hww, by rw [hlx] at hcw; exact hcw⟩
  have hQi := (List.forall₂_iff_get.1 hQ).2 i (by rw [hlx]; omega) hi
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at hQi
  obtain ⟨i', -, hi', hp⟩ := hQi
  cases hi'
  exact hp

end GI.Impl
