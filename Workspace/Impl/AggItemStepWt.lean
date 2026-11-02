import Workspace.Impl.AggItemStepSpec
import Workspace.Impl.AggCmpRun

/-!
# The sizes of the context of the items

For a call of the aggregation round with input weight `W₀ = inW .giant S` and a context `K` of
the items (`ItSCtx`, `ItSCtx.OK`), the data of `K` have weight polynomial in `W₀`. We write
`K₀ = 2 W₀ + 3` as in `AggCmpRun.lean`.
* `itS_size`: `k + q + 1 ≤ K₀`, `κ ≤ K₀`, `q^κ ≤ K₀^64`, and `0 < q`;
* `itS_stW`: the start state `K.st` weighs at most `cmOutB K₀` (it has the form of the output of
  the comparison phase, `cm_wt_out`);
* `itS_vW`: the output `K.v` of the structure step weighs at most `itSVB W₀`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-- The weight bound of the output of the structure step. -/
def itSVB (W₀ : ℕ) : ℕ :=
  2 * (cmOutB (2 * W₀ + 3) + 2 * (2 * (5 * ((2 * W₀ + 3) ^ 64 + 1) ^ 2) + 6) + 5 +
    5 * (2 * W₀ + 3 + 1) ^ 2) + 8

section Size

variable (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  {sv lv : Val} {L : SuppliedLabels S}

/-- **The sizes of a call.** -/
theorem itS_size (hc : AsCall I Pg F e c S sv lv L) :
    k + L.q + 1 ≤ 2 * I.inW .giant S + 3 ∧ P₀.κ + 1 ≤ 2 * I.inW .giant S + 3 ∧
      L.q ^ P₀.κ ≤ (2 * I.inW .giant S + 3) ^ 64 ∧ 0 < L.q ∧ sv.wt ≤ I.inW .giant S ∧
      P₀.κ + 1 < L.q := by
  have hsvW : sv.wt ≤ I.inW .giant S := by
    have := Canon.wt_le hc.can
    simp only [Iface.inW, Iface.card_eq e]
    omega
  have hk : k ≤ sv.wt := StateVal.k_le_wt hc.can.stateVal
  have hqk := GiantLabels.q_le e L.toGiantLabels
  have hκ : P₀.κ = 64 := rfl
  have hq₀ : P₀.q₀ = 2064 := rfl
  have hq0 : 2064 < L.q := by have := hc.q₀; omega
  refine ⟨by omega, by rw [hκ]; omega, ?_, by omega, hsvW, by rw [hκ]; omega⟩
  rw [hκ]
  exact Nat.pow_le_pow_left (by omega) 64

/-- The canonical value of the context weighs at most `W₀`. -/
theorem itS_svW (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c) :
    K.sv.wt ≤ I.inW .giant S := by
  have := Canon.wt_le hK.can
  simp only [Iface.inW, Iface.card_eq e]
  omega

end Size

/-- An order of the test tuples has at most `2 q^κ` entries. -/
theorem itS_tt_length {q κ : ℕ} (O : TestTupleOrder q κ) : O.tuples.length ≤ 2 * q ^ κ := by
  have h := O.nodup.length_le_card
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_fin] at h
  have := Nat.descFactorial_le_pow q κ
  omega

/-- **The start state** has the form of the output of the comparison phase. -/
theorem itS_st_eq {S : State Ω C} {L : SuppliedLabels S} (K : ItSCtx k S L) :
    K.st = cmOutV K.sv k K.ps K.fx K.fy K.O.tuples
      (K.O.tuples.flatMap fun a => K.O.tuples.map (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ a)) := rfl

/-- **The weight of the start state.** -/
theorem itS_stW (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ}
    {S : State Ω C} {sv lv : Val} {L : SuppliedLabels S} (hc : AsCall I Pg F e c S sv lv L)
    {K : ItSCtx k S L} (hK : K.OK e c) :
    K.st.wt ≤ cmOutB (2 * I.inW .giant S + 3) := by
  obtain ⟨hkq, hκ, hq, -, -, -⟩ := itS_size I Pg F hc
  have hsv := itS_svW I Pg F hc hK
  have htl : K.O.tuples.length ≤ cmNb (2 * I.inW .giant S + 3) := by
    have := itS_tt_length K.O
    unfold cmNb
    omega
  have hP := cm_wt_par (sv := K.sv) (ps := K.ps) (fx := K.fx) (fy := K.fy)
    (logs := ([] : List (CmLog k L.q))) (tt := K.O.tuples) (n := 0)
    (K := 2 * I.inW .giant S + 3) (by omega) hkq hK.lps hK.lfx hK.lfy (by simp)
    (by simp) htl (by omega) (by omega)
  rw [itS_st_eq]
  refine cm_wt_out hP htl ?_
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

/-- **The weight of the output of the structure step.** -/
theorem itS_vW (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ}
    {S : State Ω C} {sv lv : Val} {L : SuppliedLabels S} (hc : AsCall I Pg F e c S sv lv L)
    {K : ItSCtx k S L} (hK : K.OK e c) : K.v.wt ≤ itSVB (I.inW .giant S) := by
  obtain ⟨hkq, hκ, hq, -, -, -⟩ := itS_size I Pg F hc
  have hst := itS_stW I Pg F hc hK
  set K₀ := 2 * I.inW .giant S + 3 with hK₀
  have hd := wt_encKColoring_le hK.dlt
  have hd' := wt_encKColoring_le hK.dlt'
  have hpow : (L.q ^ P₀.κ + 1) ^ 2 ≤ (K₀ ^ 64 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hw2 := wt_list2_le (encKColoring K.d) (encKColoring K.d')
  have hcode : (Val.nat (AggCase.code K.case)).wt ≤ 5 :=
    (wt_nat_le _).trans (by have := it_code_le K.case; omega)
  have hsrc := it_wt_src (itSrc K.Ag₀ K.J) (W := K₀) (by omega) (by omega)
  have h4 := wt_list4_le K.st (.list [encKColoring K.d, encKColoring K.d'])
    (.nat (AggCase.code K.case)) (natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ)))
  have e : K.v.wt = (Val.list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]).wt := rfl
  have hA : 5 * (L.q ^ P₀.κ + 1) ^ 2 ≤ 5 * (K₀ ^ 64 + 1) ^ 2 := Nat.mul_le_mul_left _ hpow
  rw [e]
  refine h4.trans ?_
  show _ ≤ 2 * (cmOutB K₀ + 2 * (2 * (5 * (K₀ ^ 64 + 1) ^ 2) + 6) + 5 + 5 * (K₀ + 1) ^ 2) + 8
  have : (Val.list [encKColoring K.d, encKColoring K.d']).wt ≤
      2 * (2 * (5 * (K₀ ^ 64 + 1) ^ 2) + 6) := by omega
  omega

end GI.Impl
