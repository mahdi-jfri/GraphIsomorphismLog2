import Workspace.Proved.VsWEigCount

/-!
# The chain of partial sums of pieces

For independent nonzero pieces `P_0, …, P_{b-1}` of equal dimension `e` that span everything,
the spans `V_j` of the first `j` pieces form a strict chain `⊤ = V_b > … > V_1 > V_0 = ⊥` with
steps of dimension `e` (`vsH_chain`), in the form of `vsQ_splitC` with
`Qs = (range (b - 1)).map (k ↦ (Ps.take (b - 1 - k)).flatten)`.
-/

open Module

namespace GI.Proved

variable {p : ℕ} [hp : Fact p.Prime]

/-- The span of the first `j` pieces. -/
noncomputable def vsHV (p D : ℕ) (Ps : List (List (List ℕ))) (j : ℕ) :
    Submodule (ZMod p) (Fin D → ZMod p) :=
  vsWSp p D (Ps.take j).flatten

theorem vsHV_succ {D : ℕ} (Ps : List (List (List ℕ))) {j : ℕ} (hj : j < Ps.length) :
    vsHV p D Ps (j + 1) = vsHV p D Ps j ⊔ vsWSp p D Ps[j] := by
  rw [vsHV, vsHV, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.flatten_append, List.flatten_singleton, vsWSp_append]

theorem vsHV_zero {D : ℕ} (Ps : List (List (List ℕ))) : vsHV p D Ps 0 = ⊥ := by
  simp [vsHV, vsWSp]

theorem vsHV_le_iSup {D : ℕ} (Ps : List (List (List ℕ))) :
    ∀ j ≤ Ps.length, vsHV p D Ps j ≤ ⨆ i : Fin Ps.length, ⨆ (_ : (i : ℕ) < j), vsWSp p D Ps[i] := by
  intro j
  induction j with
  | zero => intro _; rw [vsHV_zero]; exact bot_le
  | succ j ih =>
    intro hj
    rw [vsHV_succ Ps (by omega)]
    refine sup_le ((ih (by omega)).trans (iSup_mono fun i => iSup_le fun hi =>
      le_iSup_of_le (by omega) le_rfl)) ?_
    exact le_iSup_of_le ⟨j, by omega⟩ (le_iSup_of_le (by simp) le_rfl)

/-- **The dimensions of the partial sums.** -/
theorem vsHV_finrank {D e : ℕ} {Ps : List (List (List ℕ))}
    (hind : iSupIndep fun i : Fin Ps.length => vsWSp p D Ps[i])
    (hdim : ∀ i : Fin Ps.length, finrank (ZMod p) (vsWSp p D Ps[i]) = e) :
    ∀ j ≤ Ps.length, finrank (ZMod p) (vsHV p D Ps j) = j * e := by
  intro j
  induction j with
  | zero => intro _; rw [vsHV_zero, finrank_bot]; ring
  | succ j ih =>
    intro hj
    rw [vsHV_succ Ps (by omega)]
    have hd : Disjoint (vsHV p D Ps j) (vsWSp p D Ps[j]) := by
      have h1 := (hind ⟨j, by omega⟩).symm
      refine h1.mono_left ((vsHV_le_iSup Ps j (by omega)).trans ?_)
      refine iSup_le fun i => iSup_le fun hi => ?_
      exact le_iSup₂_of_le i (fun h => by rw [Fin.ext_iff] at h; simp at h; omega) le_rfl
    have := Submodule.finrank_sup_add_finrank_inf_eq (vsHV p D Ps j) (vsWSp p D Ps[j])
    rw [hd.eq_bot, finrank_bot, add_zero, ih (by omega)] at this
    have e2 : finrank (ZMod p) (vsWSp p D Ps[j]) = e := hdim ⟨j, by omega⟩
    refine this.trans ?_
    rw [e2]; ring

/-- **The chain of partial sums.** -/
theorem vsH_chain {D e : ℕ} {Ps : List (List (List ℕ))}
    (hind : iSupIndep fun i : Fin Ps.length => vsWSp p D Ps[i])
    (hdim : ∀ i : Fin Ps.length, finrank (ZMod p) (vsWSp p D Ps[i]) = e) (he : 0 < e)
    (htop : ⨆ i : Fin Ps.length, vsWSp p D Ps[i] = ⊤) (hb : 1 ≤ Ps.length) :
    let b := Ps.length
    let Qs := (List.range (b - 1)).map fun k => (Ps.take (b - 1 - k)).flatten
    let L := (⊤ :: Qs.map (vsWSp p D)) ++ [⊥]
    L.IsChain (fun a c => c < a) ∧
      ∀ x ∈ List.zipWith (fun (a c : Submodule (ZMod p) (Fin D → ZMod p)) =>
        finrank (ZMod p) a - finrank (ZMod p) c) L L.tail, x = e := by
  intro b Qs L
  have hfr := vsHV_finrank hind hdim
  -- `V_b = ⊤`
  have hD : finrank (ZMod p) (⊤ : Submodule (ZMod p) (Fin D → ZMod p)) = b * e := by
    classical
    have h1 := vsW_finrank_biSup hind Finset.univ
    have h2 : (⨆ i ∈ (Finset.univ : Finset (Fin Ps.length)), vsWSp p D Ps[i]) = ⊤ := by
      rw [← htop]; simp
    rw [h2] at h1
    rw [h1, Finset.sum_congr rfl fun i _ => hdim i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hVb : vsHV p D Ps b = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((hfr b le_rfl).trans (by rw [← hD, finrank_top]))
  have hLl : L.length = b + 1 := by simp [L, Qs]; omega
  have hL : ∀ t (ht : t < L.length), L[t] = vsHV p D Ps (b - t) := by
    intro t ht
    rw [hLl] at ht
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp [L, hVb]
    · rcases Nat.lt_or_ge t b with htb | htb
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        have hu : u < (Qs.map (vsWSp p D)).length := by simp [Qs]; omega
        simp only [L, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_left hu]
        simp only [Qs, List.getElem_map, List.getElem_range, vsHV]
        congr 3
        omega
      · have htb' : t = b := by omega
        subst htb'
        simp only [L, List.cons_append, Nat.sub_self, vsHV_zero]
        obtain ⟨u, hu⟩ : ∃ u, b = u + 1 := ⟨b - 1, by omega⟩
        simp only [hu, List.getElem_cons_succ]
        rw [List.getElem_append_right (by simp [Qs]; omega)]
        simp [Qs]
  have hstep : ∀ t, t < b → vsHV p D Ps (b - t - 1) < vsHV p D Ps (b - t) := by
    intro t ht
    have e1 : b - t = (b - t - 1) + 1 := by omega
    have hle : vsHV p D Ps (b - t - 1) ≤ vsHV p D Ps (b - t) := by
      rw [e1, vsHV_succ Ps (by omega)]; exact le_sup_left
    refine lt_of_le_of_ne hle fun h => ?_
    have := congrArg (fun U : Submodule (ZMod p) (Fin D → ZMod p) => finrank (ZMod p) U) h
    simp only at this
    rw [hfr _ (by omega), hfr _ (by omega)] at this
    have : (b - t - 1) * e < (b - t) * e := Nat.mul_lt_mul_of_pos_right (by omega) he
    omega
  refine ⟨List.isChain_iff_getElem.2 fun t ht => ?_, fun x hx => ?_⟩
  · rw [hL t (by omega), hL (t + 1) ht]
    have := hstep t (by omega)
    rwa [show b - (t + 1) = b - t - 1 by omega]
  · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_zipWith, List.getElem_tail]
    have ht' : t < b := by simp [List.length_zipWith, hLl] at ht; omega
    have et : L.tail[t]'(by simp [hLl]; omega) = L[t + 1]'(by omega) := List.getElem_tail ..
    rw [et, hL t (by omega), hL (t + 1) (by omega), hfr _ (by omega), hfr _ (by omega)]
    rw [show b - (t + 1) = b - t - 1 by omega]
    have h1 : (b - t) * e = (b - t - 1) * e + e := by
      obtain ⟨u, hu⟩ : ∃ u, b - t = u + 1 := ⟨b - t - 1, by omega⟩
      rw [hu, Nat.add_sub_cancel]; ring
    omega

/-- **Invariance.** A map that sends every piece into itself sends every partial sum into
itself. -/
theorem vsHV_map_le {D : ℕ} {Ps : List (List (List ℕ))}
    (T : Module.End (ZMod p) (Fin D → ZMod p))
    (hT : ∀ P ∈ Ps, (vsWSp p D P).map T ≤ vsWSp p D P) :
    ∀ j ≤ Ps.length, (vsHV p D Ps j).map T ≤ vsHV p D Ps j := by
  intro j
  induction j with
  | zero => intro _; rw [vsHV_zero, Submodule.map_bot]
  | succ j ih =>
    intro hj
    rw [vsHV_succ Ps (by omega), Submodule.map_sup]
    exact sup_le_sup (ih (by omega)) (hT _ (List.getElem_mem _))

end GI.Proved
