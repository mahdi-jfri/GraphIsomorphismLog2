module

public import Workspace.Impl.AggReadSpec
public import Workspace.Impl.AggReadRounds
public import Workspace.Impl.PolyBd

@[expose] public section

/-!
# `AsReadOK`: the reading meets its contract

`rd_asReadOK`: the reading `rdF b` at `fr` meets `AsReadOK` for any hand-over `H` whose relation
`cert` contains `CpHand`, with the polynomial phase bound `rdX hpre` (`rd_pbu`).

From the facts of a call (`AsCall`):
* the label value is standard (`hLab`; for `Rest.iface` this is the identity), so `lv` holds
  `q`, the pairs `ps` of `G` (a graph form, `pairGens_of_fst`) and the selected interval;
* the state value is canonical, so `sv` holds `k` and the domain indicator;
* the test-set list `sbOrder q κ` is nonempty, as `q > q₀ ≥ κ`;
* the input weighs at most `W₀ = inW .giant S`, so `k ≤ W₀` and `q ≤ k + 2`; this bounds the
  budget of `rd_spec` by `rdU hpre W₀`.

Then `rd_spec` gives the result, and `CpHand` holds by `rd_cpAll`, `rd_card_dom`,
`cp_card_alt`, `domMap_spec` and `rd_asRounds_nonempty`. The last one uses the cited results
that `Aggregation.ofLabels` needs.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.LocalGroups
open GI.Cited (Val encPerm encGroup encPts gens Preimage)

/-! ### The budget -/

/-- The first budget level (weight of the input and the test-set list) at input weight `W`. -/
def rdU1 (W : ℕ) : ℕ := sbK * ((W + 2) ^ 64 + 2 * W + 77) ^ 5 + W

/-- The size bound of the pairs of `G` and of `M_T`. -/
def rdM (W : ℕ) : ℕ := W ^ 2 + 2 * W + 4

/-- **The budget of the reading** at input weight `W`. -/
noncomputable def rdU (hpre : Preimage) (W : ℕ) : ℕ :=
  1000 * (rdU1 W + 1) * (3 * rdU1 W + 1) + rdU1 W + domListK * (W + 1) ^ 3 +
    8000 * (W + 3) ^ 3 + grpK * rdM W ^ 6 +
    (preimagePrim hpre).boundSize (1000 * ((W + 2) ^ 3 + rdM W) ^ 4) + ptK * rdM W ^ 24 +
    rdD + 11 * W + 30

/-- **The phase bound of the reading.** -/
noncomputable def rdX (hpre : Preimage) (W : ℕ) : ℕ := 10 ^ 8 * (rdU hpre W + 20)

/-- The phase bound is polynomial. -/
theorem rd_pbu (hpre : Preimage) : PBU fun _ W _ => rdX hpre W := by
  have hW := PBU.W
  have hU1 : PBU fun _ W _ => rdU1 W :=
    PBU.add (PBU.smul _ (PBU.pow (PBU.addc (PBU.add (PBU.pow (PBU.addc hW 2) 64)
      (PBU.smul 2 hW)) 77) 5)) hW
  have hM : PBU fun _ W _ => rdM W :=
    PBU.addc (PBU.add (PBU.pow hW 2) (PBU.smul 2 hW)) 4
  have hbs : PBU fun _ W _ => (preimagePrim hpre).boundSize (1000 * ((W + 2) ^ 3 + rdM W) ^ 4) :=
    PBU.smul _ (PBU.pow (PBU.addc (PBU.smul 1000 (PBU.pow (PBU.add (PBU.pow (PBU.addc hW 2) 3)
      hM) 4)) 2) _)
  have hU : PBU fun _ W _ => rdU hpre W := by
    unfold rdU
    exact PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
      (PBU.mul (PBU.smul 1000 (PBU.addc hU1 1)) (PBU.addc (PBU.smul 3 hU1) 1)) hU1)
      (PBU.smul _ (PBU.pow (PBU.addc hW 1) 3))) (PBU.smul _ (PBU.pow (PBU.addc hW 3) 3)))
      (PBU.smul _ (PBU.pow hM 6))) hbs) (PBU.smul _ (PBU.pow hM 24))) (PBU.const _))
      (PBU.smul 11 hW)) 30
  exact PBU.smul _ (PBU.addc hU 20)

/-- The budget bounds at input weight `W`, for `k ≤ W` and `q ≤ k + 2`. -/
theorem rd_bud (hpre : Preimage) {k q W : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q)))
    (T : Finset (Fin q)) {A : Val} (hA : A.wt ≤ W) (hk : k ≤ W) (hq : q ≤ k + 2)
    (hpl : ps.length ≤ k ^ 2) : RdBud hpre k q ps T A (rdU1 W) (rdU hpre W) := by
  have hqW : q ≤ W + 2 := by omega
  have hU1 : W ≤ rdU1 W := by unfold rdU1; omega
  have hkk : k ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hk 2
  have hpM : pM k q ps ≤ rdM W := by unfold pM rdM; omega
  have hptM : ptM k q ps ≤ rdM W := by unfold ptM rdM; omega
  have hpreM : preM k q ps (mtGens q T) ≤ (W + 2) ^ 3 + rdM W := by
    have hl : (mtGens q T).length = q ^ 3 := by simp [mtGens]
    have : q ^ 3 ≤ (W + 2) ^ 3 := Nat.pow_le_pow_left hqW 3
    unfold preM rdM; rw [hl]; omega
  have hsb : sbK * (q ^ 64 + k + q + 64 + 10 + 1) ^ 5 ≤ rdU1 W := by
    have : q ^ 64 ≤ (W + 2) ^ 64 := Nat.pow_le_pow_left hqW 64
    have h5 : (q ^ 64 + k + q + 64 + 10 + 1) ^ 5 ≤ ((W + 2) ^ 64 + 2 * W + 77) ^ 5 :=
      Nat.pow_le_pow_left (by omega) 5
    have := Nat.mul_le_mul_left sbK h5
    unfold rdU1; omega
  have hdom : domListK * (k + 1) ^ 3 ≤ domListK * (W + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hrk : 8000 * (k + 1) ^ 3 ≤ 8000 * (W + 3) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hrq : 8000 * (q + 1) ^ 3 ≤ 8000 * (W + 3) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hgrp : grpK * pM k q ps ^ 6 ≤ grpK * rdM W ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpM 6)
  have hbs : (preimagePrim hpre).boundSize (1000 * preM k q ps (mtGens q T) ^ 4) ≤
      (preimagePrim hpre).boundSize (1000 * ((W + 2) ^ 3 + rdM W) ^ 4) :=
    boundSize_mono _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpreM 4))
  have hpt : ptK * ptM k q ps ^ 24 ≤ ptK * rdM W ^ 24 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hptM 24)
  refine ⟨hA.trans hU1, hsb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold rdU <;> omega

/-! ### The contract -/

theorem rd_sets_ne (q : ℕ) (hq : P₀.κ ≤ q) : ∃ T Ts, (sbOrder q P₀.κ).sets = T :: Ts := by
  set T : Finset (Fin q) := (Finset.univ : Finset (Fin P₀.κ)).map (Fin.castLEEmb hq) with hT
  have hc : T.card = P₀.κ := by simp [hT]
  have hm : T ∈ (sbOrder q P₀.κ).sets := ((sbOrder q P₀.κ).mem T).2 hc
  cases h : (sbOrder q P₀.κ).sets with
  | nil => rw [h] at hm; simp at hm
  | cons T' Ts => exact ⟨T', Ts, rfl⟩

theorem rd_beta_cap {Ω C : Type} {S : State Ω C} (L : GiantLabels S) :
    abCap L = 9 * L.q / 10 := by
  unfold abCap
  rw [show P₀.β = 9 / 10 from rfl]
  exact lc_floor L.q

set_option maxHeartbeats 2000000 in
/-- **The reading meets `AsReadOK`**, for any hand-over whose relation `cert` contains `CpHand`.
The cited results enter through `rd_asRounds_nonempty`. -/
theorem rd_asReadOK (hpre : Preimage)
    (hK : GI.Cited.KaryCoherentRefinement)
    (hDl : GI.Cited.DesignLemma) (I : Iface) (Pg : Program) (F : Funs) {b jpre fr : ℕ}
    (hf : Pg.funs[fr]? = some (rdF b)) (hb : Pg.HasAt b (rdFuns b jpre))
    (hj : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hLab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
      (L : SuppliedLabels S), I.LabVal e S lv L → LabValStd e S lv L)
    (H : AsHand)
    (hH : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val),
      CpHand e c S L Cs st → H.cert e c S L Cs st) :
    AsReadOK I Pg F H (rdX hpre) fr := by
  intro Ω C k e c S sv lv L hcall
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  -- the input
  obtain ⟨ps, rfl, hpl, hgen, hπps⟩ := hLab e S lv L hcall.lab
  have hcan := hcall.can
  have hkW := StateVal.k_le_wt hcan.stateVal
  obtain ⟨gv, dv, xv, yv, hv, rv, -, hd, -, -, -, -, rfl⟩ := hcan.val
  rw [DomVal.eq_indVal hd] at hcan hkW ⊢
  have hpg : PairGens e L.toGiantLabels S.G ps := pairGens_of_fst hgen hπps
  have hq0 : 0 < L.q := by have := hcall.q₀; omega
  have hκ : P₀.κ ≤ L.q := by have := hcall.q₀; rw [rd_kappa]; exact le_of_lt (by
    have : P₀.q₀ = 2064 := rfl; omega)
  obtain ⟨T, Ts, hO⟩ := rd_sets_ne L.q hκ
  have hTc : T.card = P₀.κ := ((sbOrder L.q P₀.κ).mem T).1 (by rw [hO]; simp)
  set πd := L.toGiantLabels.domMap L.con.onDomain with hπd
  have hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g := L.toGiantLabels.domMap_spec _
  -- the weight
  set W₀ := I.inW .giant S with hW₀
  have hAW : (Val.list [.list [.nat k, gv, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor,
      .nat S.h, .nat S.N], .list [.nat L.q, .list (ps.map fun p => .list [encPerm p.1,
      encPerm p.2]), .nat L.sel, .nat L.con.blocks.h, .nat L.con.blocks.f,
      blkMapVal e L.con.blocks]]).wt ≤ W₀ := by
    have h1 := wt_list2_le (.list [.nat k, gv, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor,
      .nat S.h, .nat S.N]) (.list [.nat L.q, .list (ps.map fun p => .list [encPerm p.1,
      encPerm p.2]), .nat L.sel, .nat L.con.blocks.h, .nat L.con.blocks.f,
      blkMapVal e L.con.blocks])
    have h2 := Canon.wt_le hcan
    have h3 := hcall.lw
    simp only [hW₀, Iface.inW, Iface.card_eq e]
    omega
  have hkW₀ : k ≤ W₀ := by
    have := wt_le_wt_list (vs := [.list [.nat k, gv, indVal e S.dom, xv, yv, hv, rv,
      boolVal S.floor, .nat S.h, .nat S.N], .list [.nat L.q, .list (ps.map fun p =>
      .list [encPerm p.1, encPerm p.2]), .nat L.sel, .nat L.con.blocks.h, .nat L.con.blocks.f,
      blkMapVal e L.con.blocks]]) (List.mem_cons_self ..)
    omega
  have hqk := GiantLabels.q_le e L.toGiantLabels
  have hU := rd_bud hpre ps T hAW hkW₀ hqk hpl
  -- the program
  refine ((rd_spec hpre hf hb hj e S L.toGiantLabels (sel := L.sel) rfl rfl rfl rfl rfl hpg πd hπ
    hO hq0 hU).wt_lt).mono fun w cost h => ?_
  obtain ⟨⟨p0, rfl, hp0, hp0l, hc⟩, hwc⟩ := h
  have hX : 10 ^ 8 * (rdU hpre W₀ + 20) = rdX hpre W₀ := rfl
  set sv : Val := .list [.nat k, gv, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
    .nat S.N] with hsv
  have hctx : CpCtx e c S L.toGiantLabels πd sv ps (rdOsA e S L.q) (P₀.κ.factorial / 2) := by
    obtain ⟨-, -, htr, -, -, -⟩ := hcall.good
    exact { inj := hcall.inj, canon := hcan, good := hcall.good, tr := htr, hπ := hπ, hgp := hpg
            hgpl := hpl.trans (Nat.pow_le_pow_left (by omega) 2), hosA := rd_cpAll e S L.q
            hD := fun T' hT' => cp_card_alt T' hT' }
  have hst : cpInitV sv k L.q (domNat e S.dom).length ps (rdOsA e S L.q) T Ts p0 =
      cpInitV sv k L.q (Fintype.card S.dom) ps (rdOsA e S L.q) T Ts p0 := by
    rw [rd_card_dom e S L.q]
  refine ⟨cpInitV sv k L.q (domNat e S.dom).length ps (rdOsA e S L.q) T Ts p0, ps,
    by rw [rd_beta_cap], hpg, hH e c S L _ _ ⟨rfl, rd_asRounds_nonempty hK hDl hcall,
    sv, ps, rdOsA e S L.q, T, Ts, p0, hO, hctx, hp0, hp0l, hst⟩, by omega, by omega⟩


/-- `AsReadOK` for a larger phase bound. The four phases share one bound `X`; this lets the
assembly take the largest of the bounds of the phases. -/
theorem rd_asReadOK_mono {I : Iface} {Pg : Program} {F : Funs} {H : AsHand} {X X' : ℕ → ℕ}
    {fr : ℕ} (h : AsReadOK I Pg F H X fr) (hX : ∀ W, X W ≤ X' W) : AsReadOK I Pg F H X' fr :=
  fun e c S sv lv L hc => (h e c S sv lv L hc).mono fun _ _ ⟨st, ps, h1, h2, h3, h4, h5⟩ =>
    ⟨st, ps, h1, h2, h3, h4.trans (hX _), h5.trans (hX _)⟩

end GI.Impl
