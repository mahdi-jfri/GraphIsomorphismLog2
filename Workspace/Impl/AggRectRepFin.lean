import Workspace.Impl.AggRectRepRowL

/-!
# The representation function and the cells the program writes

`rcRRf e I hx`: the representation function of the program (`rcRRep` with the carrier
representation `RectRep.ofCarrier (rcRCarD …)` for single labels, `rcRNat`). Its twist is
`none` (`rcR_twist`), so the program writes the empty twist list.

The cells. The program writes, for each position `i`, `rcRCellN`: `0` off the domain, and else
the code read from the key at `i` in the orbit table: `rcRCodeN` of the two labels (pairs), or
`rcRCarCodeN` of the row of `i` and the label (single labels). These are the cell codes of the
representation: `rcR_cells_pair`, `rcR_cells_car`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-! ### Codes on numbers -/

/-- The cell code of a pair of labels, with indicator lists `wl`, `rl` of `W`, `R`. -/
def rcRCodeN (wl rl : List ℕ) (q : ℕ) (uno : Bool) (c d : ℕ) : ℕ :=
  if wl.getD c 0 = 1 ∧ rl.getD d 0 = 1 then 1 + c * q + d
  else if uno = true ∧ wl.getD d 0 = 1 ∧ rl.getD c 0 = 1 then 1 + d * q + c else 0

/-- The cell code of a row and a label (single labels). -/
def rcRCarCodeN (wl rl : List ℕ) (q r c : ℕ) : ℕ :=
  if r < q ∧ wl.getD r 0 = 1 ∧ rl.getD c 0 = 1 then 1 + r * q + c else 0

/-- The indicator list of a set of labels (the list of `rcSetVal`). -/
abbrev rcRInd {q : ℕ} (W : Finset (Fin q)) : List ℕ :=
  (List.finRange q).map fun i => if i ∈ W then 1 else 0

theorem rcR_ind_getD {q : ℕ} (W : Finset (Fin q)) (c : Fin q) :
    (rcRInd W).getD c 0 = 1 ↔ c ∈ W := by
  rw [show rcRInd W = rcRL (fun i => if i ∈ W then 1 else 0) from rfl, rcR_L_getD]
  split_ifs with h <;> simp [h]

theorem rcR_codeN {q : ℕ} (W R : Finset (Fin q)) (uno : Bool) (c d : Fin q) :
    rcRCodeN (rcRInd W) (rcRInd R) q uno c d = rcRCode W R uno c d := by
  unfold rcRCodeN rcRCode
  simp only [rcR_ind_getD]

theorem rcR_carCodeN {m : ℕ} (W R : Finset (Fin L.q)) (r : Fin m) (c : Fin L.q) :
    rcRCarCodeN (rcRInd W) (rcRInd R) L.q r c = rcRCarCode W R r c := by
  unfold rcRCarCodeN rcRCarCode
  by_cases h : (r : ℕ) < L.q
  · rw [dif_pos h]
    have : (rcRInd W).getD r 0 = 1 ↔ (⟨r, h⟩ : Fin L.q) ∈ W := rcR_ind_getD W ⟨r, h⟩
    simp only [h, true_and, this, rcR_ind_getD]
  · rw [dif_neg h]
    simp [h]

/-- **The cell the program writes at position `i`.** -/
def rcRCellN (dl : List ℕ) (Lk : List (List ℕ)) (k q : ℕ) (wl rl : List ℕ) (car uno : Bool)
    (rowT : List ℕ) (i : ℕ) : ℕ :=
  if dl.getD i 0 = 0 then 0
  else if car then rcRCarCodeN wl rl q (rowT.getD i 0) ((rcRLook Lk i).getD 1 0 - k)
  else rcRCodeN wl rl q uno ((rcRLook Lk i).getD 1 0 - k) ((rcRLook Lk i).getD 2 0 - k)

/-! ### The representation function -/

section Rf

variable [Finite Ω] {k : ℕ} (e : Ω ≃ Fin k) (I : AggregationData P₀ S L)

open Classical in
/-- Single labels: the carrier representation of Lemma A.30 with the program's row numbers and
labels. (The last branch is never used: with `q > λ` and natural labels there is a one-label
quotient.) -/
noncomputable def rcRNat (W R : Finset (Fin L.q)) (hc : RectConds P₀ S L W R) : RectRep P₀ S L W R :=
  if hf : Nonempty (KernelQuotient I.πd S.dom (Fin L.q)) then
    RectRep.ofCarrier (rcRCarD e I hc.1 hf.some) (le_trans (by norm_num) I.θ_half) hc.2.2.2.2
  else I.defaultRep W R hc

/-- **The representation function of the program.** -/
noncomputable def rcRRf {x : Ω} (hx : x ∈ S.dom) (W R : Finset (Fin L.q))
    (hc : RectConds P₀ S L W R) : RectRep P₀ S L W R :=
  rcRRep I hx (rcRNat e I) W R hc

variable {x : Ω} (hx : x ∈ S.dom) {W R : Finset (Fin L.q)} (hc : RectConds P₀ S L W R)

include hx hc in
/-- The twist is `none` in the cases the program meets. -/
theorem rcR_twist (hsm : (∃ d₁ d₂, d₁ < d₂ ∧ rcRSmall (rcRStab S L x) = [d₁, d₂]) ∨
    ∃ a, rcRSmall (rcRStab S L x) = [a]) : (rcRRf e I hx W R hc).twist = none := by
  classical
  rcases hsm with ⟨d₁, d₂, -, hsm⟩ | ⟨a, hsm⟩
  · unfold rcRRf rcRRep
    split_ifs with ho hu
    · rfl
    · rfl
    · exfalso
      rcases I.kq_cases hc.1 with hf | hf | hf
      · obtain ⟨f⟩ := hf
        rw [rcR_stab_one I.πd_spec f hx, rcR_small_one (rcR_q8 I)] at hsm
        simp at hsm
      · exact ho hf
      · exact hu hf
  · unfold rcRRf
    rw [rcR_nat_of_small I hx (rcRNat e I) hc hsm]
    obtain ⟨f, -⟩ := rcR_one_of_small I hx hc.1 hsm
    unfold rcRNat
    rw [dif_pos ⟨f⟩]
    rfl

/-- The domain indicator. -/
noncomputable abbrev rcRDom (e : Ω ≃ Fin k) (S : State Ω C) (i : Fin k) : ℕ :=
  open Classical in if e.symm i ∈ S.dom then 1 else 0

omit [Finite Ω] in
theorem rcR_dom_getD (i : Fin k) :
    (rcRL (rcRDom e S)).getD i 0 = 0 ↔ e.symm i ∉ S.dom := by
  classical
  rw [rcR_L_getD]
  unfold rcRDom
  split_ifs with h <;> simp [h]

include I hx in
/-- The key at a domain position `v = g x` is the key of an element `g'` with `g' x = v`. -/
theorem rcR_look_dom {d₁ d₂ : Fin L.q} {Lk : List (List ℕ)} (hT : RcRTab e x d₁ d₂ Lk)
    {v : Ω} (hv : v ∈ S.dom) : ∃ g' : S.G, (g' : Perm Ω) x = v ∧
      rcRLook Lk (e v) = rcRKeyOf e x d₁ d₂ g' := by
  obtain ⟨g, hg, hgv⟩ := I.htr x hx v hv
  obtain ⟨g', h1, h2⟩ := rcR_look hT ⟨g, hg⟩
  refine ⟨g', h1.trans hgv, ?_⟩
  rw [← hgv]; exact h2

include hc in
/-- **The cells in the pair cases.** -/
theorem rcR_cells_pair {d₁ d₂ : Fin L.q} (hsm : rcRSmall (rcRStab S L x) = [d₁, d₂])
    {Lk : List (List ℕ)} (hT : RcRTab e x d₁ d₂ Lk) (rowT : List ℕ) (i : Fin k) :
    rcRCellN (rcRL (rcRDom e S)) Lk k L.q (rcRInd W) (rcRInd R) false
      (decide (d₂ ∈ rcROrb (rcRStab S L x) d₁)) rowT i =
      rcCellCode ((rcRRf e I hx W R hc).cell (e.symm i)) := by
  obtain ⟨-, hoff, hcode⟩ := rcR_pair_cells I hx (rcRNat e I) hc hsm
  unfold rcRCellN rcRRf
  by_cases hv : e.symm i ∈ S.dom
  · rw [if_neg (fun h => ((rcR_dom_getD e i).1 h) hv), if_neg (by simp)]
    obtain ⟨g', hg'x, hlk⟩ := rcR_look_dom e I hx hT hv
    have hi : (i : ℕ) = (e (e.symm i) : ℕ) := by simp
    rw [hi, hlk, rcR_key_getD1, rcR_key_getD2, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
      rcR_codeN, ← hg'x, hcode g']
  · rw [if_pos ((rcR_dom_getD e i).2 hv), hoff _ hv]

include hc in
/-- In the single-label case the representation is the carrier representation of a one-label
quotient `f` with `f(x) = a`. -/
theorem rcR_rf_car {a : Fin L.q} (hsm : rcRSmall (rcRStab S L x) = [a]) :
    ∃ f : KernelQuotient I.πd S.dom (Fin L.q), f.map ⟨x, hx⟩ = a ∧
      rcRRf e I hx W R hc = RectRep.ofCarrier (rcRCarD e I hc.1 f)
        (le_trans (by norm_num) I.θ_half) hc.2.2.2.2 := by
  classical
  obtain ⟨f₀, -⟩ := rcR_one_of_small I hx hc.1 hsm
  have hne : Nonempty (KernelQuotient I.πd S.dom (Fin L.q)) := ⟨f₀⟩
  refine ⟨hne.some, ?_, ?_⟩
  · have h := hsm
    rw [rcR_stab_one I.πd_spec hne.some hx, rcR_small_one (rcR_q8 I)] at h
    simpa using h
  · unfold rcRRf
    rw [rcR_nat_of_small I hx (rcRNat e I) hc hsm]
    unfold rcRNat
    rw [dif_pos hne]

include hc in
/-- **The cells in the single-label case.** -/
theorem rcR_cells_car {a : Fin L.q} (hsm : rcRSmall (rcRStab S L x) = [a])
    {Lk : List (List ℕ)} (hT : RcRTab e x a a Lk) {R₀ : RowRecord Ω} (hR₀ : S.rows = some R₀)
    (rlab : Fin k → ℕ) (hrl : ∀ i j, rlab i = rlab j ↔ R₀.rows.r (e.symm i) (e.symm j))
    (uno : Bool) (i : Fin k) :
    rcRCellN (rcRL (rcRDom e S)) Lk k L.q (rcRInd W) (rcRInd R) true uno
      ((List.range k).map (rcRRowN' (rcRL (rcRDom e S)) (rcRL rlab) k)) i =
      rcCellCode ((rcRRf e I hx W R hc).cell (e.symm i)) := by
  classical
  obtain ⟨f, hfx, hrf⟩ := rcR_rf_car e I hx hc hsm
  rw [hrf]
  show _ = rcCellCode ((rcRCarD e I hc.1 f).cell W R (e.symm i))
  have hrec : rcRRec I hc.1 f = R₀ := Option.some_injective _ ((rcR_rec_spec I hc.1 f).1.symm.trans hR₀)
  unfold rcRCellN
  by_cases hv : e.symm i ∈ S.dom
  · rw [if_neg (fun h => ((rcR_dom_getD e i).1 h) hv), if_pos rfl, rcR_car_code e I hc.1 f hv]
    obtain ⟨g', hg'x, hlk⟩ := rcR_look_dom e I hx hT hv
    have hi : (i : ℕ) = (e (e.symm i) : ℕ) := by simp
    -- the row
    have hrow : ((List.range k).map (rcRRowN' (rcRL (rcRDom e S)) (rcRL rlab) k)).getD i 0 =
        (rcRRowN e I hc.1 f (e.symm i) : ℕ) := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, hi]
      subst hrec
      exact rcR_rowN_eq e S.dom (rcRRec I hc.1 f).rows (rcRDom e S) rlab (fun _ => rfl) hrl
        (rcR_spec0 I hc.1 f) (rcR_m_pos I hc.1 f) hv
    -- the label
    have hlab : rcRLab (rcR_q_pos I) f (e.symm i) = rcRPi L g' a := by
      rw [← hg'x, (rcR_natRows I.πd_spec (rcR_q_pos I) f).equivariant g' x hx]
      simp only [rcRLab, dif_pos hx, hfx]
    rw [hrow]
    conv_lhs => rw [hi, hlk]
    rw [rcR_key_getD1, Nat.add_sub_cancel_left, ← hlab, rcR_carCodeN]
  · rw [if_pos ((rcR_dom_getD e i).2 hv), rcR_car_off e I hc.1 f hv]

end Rf

end GI.Impl
