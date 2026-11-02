import Workspace.Impl.TermJCorrMath
import Workspace.Impl.TermJLabRT
import Workspace.Impl.TermJVecList

/-!
# The transporter of one label (mathematics)

Proof of Theorem A.23: "Finally lift the surviving quotient representative and correct it by the
constructed `J`-transporter." For one label `h` the program has a lift `g` (NormalizedFactor of
`(h; 1)` in `G|_dom · N^q`), a local transporter `z`, the pair `u = z⁻¹ g = (d, π)` with all
`d i ∈ N`, a solution `c` of the zero-sum equation and the parity of `π`. This file shows that the
result `z · tmJCorrE Tl odd lg c` lies in the piece and has class `h`.

* `tmJH_corr`: the correction is right when `c` solves `∏ φ(g_k)^{c_k} = lab(u)` and `odd`
  says that `π` is odd.
* `tmJH_exists`: some `e` solves the equation (from `tmJ_corr_exists` and `tmJ_lab_range`).
* `tmJH_sound`, `tmJH_solvable`: the same equation in the Lin* coordinates of
  `⟨σN⟩ / ⟨σS⟩`, written as `s + c B + y M = 0`; `tmJH_triv` covers `σN = []`.
* `tmJH_lam_fold`, `tmJH_pow_inv`, `tmJH_dec_div`, `tmJH_dec_mod`: the facts used by the small
  programs (the local product as a fold, integer powers, and reading a pair off `Fin (m q)`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Paper Equiv Equiv.Perm
open GI.Cited (gens)
open scoped IsMulCommutative

/-! ### Generic sets of generators -/

section Sets

variable {B : Type} {q : ℕ}

/-- The local generators `(g at a; 1)` of a list of pairs `(a, g)`. -/
def tmJHLocs (lg : List (Fin q × Perm B)) : Set (Perm (B × Fin q)) :=
  {σ | ∃ ag ∈ lg, σ = tmJLoc ag.1 ag.2}

/-- The lifted transpositions of a list of triples. -/
def tmJHSws (Tl : List (Fin q × Fin q × Perm B)) : Set (Perm (B × Fin q)) :=
  {σ | ∃ t ∈ Tl, σ = tmJSw t.1 t.2.1 t.2.2}

theorem tmJH_locs_top [Nonempty B] {N : Subgroup (Perm B)} {lg : List (Fin q × Perm B)}
    (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N) :
    ∀ σ ∈ tmJHLocs lg, σ ∈ tmJW N ∧ tmJTop N σ = 1 := by
  rintro σ ⟨ag, hag, rfl⟩
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hag
  have hd : ∀ i, (Pi.mulSingle (lg.get k).1 (lg.get k).2 : Fin q → Perm B) i ∈ N := by
    intro i
    by_cases hi : i = (lg.get k).1
    · subst hi; simpa using hlg k
    · rw [Pi.mulSingle_eq_of_ne hi]; exact N.one_mem
  exact ⟨⟨_, hd, rfl⟩, tmJTop_tmJP (p := (Pi.mulSingle _ _, 1)) hd⟩

end Sets

/-! ### The correction at a row terminal -/

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

variable [Nonempty I.B]

/-- The label and the top of `u = z⁻¹ g`, read from a pair. -/
theorem tmJH_lab_u {u : Perm (I.B × Fin L.q)} (hu : u ∈ tmJW I.Nb)
    {d : Fin L.q → Perm I.B} {π : Perm (Fin L.q)} (hd : ∀ i, d i ∈ I.Nb) (he : u = tmJP (d, π)) :
    tmJLabHom I.φ ⟨u, hu⟩ = tmJLab I.Nb I.φ d ∧ tmJTopHom ⟨u, hu⟩ = π := by
  subst he
  exact ⟨tmJLabHom_tmJP I.φ (p := (d, π)) hd, tmJTopHom_tmJP (p := (d, π)) hd⟩

/-- **The correction is right.** If `c` solves `∏ φ(g_k)^{c_k} = lab(u)` and `odd` says that the
top of `u` is odd, then `z · tmJCorrE Tl odd lg c` lies in the piece and has class `h`. -/
theorem tmJH_corr {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r)
    {g w z : Perm (I.B × Fin L.q)} (hg : g ∈ tmJG I) (hw : w ∈ tmJW I.Nb)
    (hf : tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * w)
    (hzY : tmJStr (rowTuple I.e S.y) ∘ z = tmJStr (rowTuple I.e S.x))
    (hzc : z ∈ tmJCls I.Nb h) {d : Fin L.q → Perm I.B} {π : Perm (Fin L.q)}
    (hd : ∀ i, d i ∈ I.Nb) (he : z⁻¹ * g = tmJP (d, π))
    {lg : List (Fin L.q × Perm I.B)}
    (hlg : ∀ k : Fin lg.length,
      (lg.get k).2 ∈ tmJRowAut I.Nb (rowTuple I.e S.x (lg.get k).1))
    {Tl : List (Fin L.q × Fin L.q × Perm I.B)}
    (hTl : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ I.Nb ∧
      rowTuple I.e S.x t.1 ∘ t.2.2 = rowTuple I.e S.x t.2.1)
    (hAut : tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)) ≤
      Subgroup.closure (tmJHLocs lg ∪ tmJHSws Tl))
    (c : Fin lg.length → ℤ) (hc : tmJSumT I.Nb I.φ lg c = tmJLab I.Nb I.φ d)
    (odd : Bool) (hodd : odd = true ↔ sign π = -1) :
    z * tmJCorrE Tl odd lg c ∈ tmJP '' tmCosetT I r ∧
      z * tmJCorrE Tl odd lg c ∈ tmJCls I.Nb h := by
  have hhH : h ∈ I.Hb := tmJ_lab_le I hL
  have hgc : g ∈ tmJCls I.Nb h := tmJ_lift_cls I.normalizes hw hf hhH
  have hu : z⁻¹ * g ∈ tmJW I.Nb := tmJ_u_mem I hhH hzc hgc
  obtain ⟨hlu, htu⟩ := tmJH_lab_u I hu hd he
  have hTl' : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ I.Nb := fun t ht => ⟨(hTl t ht).1, (hTl t ht).2.1⟩
  -- an odd top needs a transposition: the hypothesis `hAut` is used here
  have hne : odd = true → Tl ≠ [] := by
    intro ho
    obtain ⟨a0, ha0, -, hs0⟩ := tmJ_corr_exists I hr hL hg hw hf hzY hzc hu
    have hodd' : sign (tmJTop I.Nb a0) = -1 := by
      rw [tmJTop, dif_pos (show a0 ∈ tmJW I.Nb from ha0.1), hs0, htu]
      exact hodd.1 ho
    exact tmJ_odd_ne (tmJH_locs_top fun k => (hlg k).1) hTl' (hAut ha0) hodd'
  obtain ⟨ha, hla, hsa⟩ := tmJ_corrE_spec (φ := I.φ) hTl hlg odd hne c
  refine tmJ_corr_lab I hr hL hg hw hf hzY hzc hu ha ?_ ?_
  · rw [hlu, ← hc, ← hla, tmJLabOf, dif_pos (show tmJCorrE Tl odd lg c ∈ tmJW I.Nb from ha.1)]
  · rw [htu]
    have e : sign (tmJTop I.Nb (tmJCorrE Tl odd lg c)) =
        sign (tmJTopHom (⟨tmJCorrE Tl odd lg c, ha.1⟩ : tmJW (q := L.q) I.Nb)) := by
      rw [tmJTop, dif_pos (show tmJCorrE Tl odd lg c ∈ tmJW I.Nb from ha.1)]
    rw [← e, hsa]
    cases odd with
    | true => exact (hodd.1 rfl).symm
    | false =>
      rcases Int.units_eq_one_or (sign π) with h1 | h1
      · exact h1.symm
      · exact absurd (hodd.2 h1) (by decide)

/-- **The zero-sum equation has a solution** (Theorem A.23: the possible sums are the cosets of
the sum map, and some element of the piece has class `h`). -/
theorem tmJH_exists {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r)
    {g w z : Perm (I.B × Fin L.q)} (hg : g ∈ tmJG I) (hw : w ∈ tmJW I.Nb)
    (hf : tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * w)
    (hzY : tmJStr (rowTuple I.e S.y) ∘ z = tmJStr (rowTuple I.e S.x))
    (hzc : z ∈ tmJCls I.Nb h) {d : Fin L.q → Perm I.B} {π : Perm (Fin L.q)}
    (hd : ∀ i, d i ∈ I.Nb) (he : z⁻¹ * g = tmJP (d, π))
    {lg : List (Fin L.q × Perm I.B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ I.Nb)
    {Tl : List (Fin L.q × Fin L.q × Perm I.B)} (hTl : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ I.Nb)
    (hAut : tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)) ≤
      Subgroup.closure (tmJHLocs lg ∪ tmJHSws Tl)) :
    ∃ e : Fin lg.length → ℤ, tmJSumT I.Nb I.φ lg e = tmJLab I.Nb I.φ d := by
  have hhH : h ∈ I.Hb := tmJ_lab_le I hL
  have hgc : g ∈ tmJCls I.Nb h := tmJ_lift_cls I.normalizes hw hf hhH
  have hu : z⁻¹ * g ∈ tmJW I.Nb := tmJ_u_mem I hhH hzc hgc
  obtain ⟨hlu, -⟩ := tmJH_lab_u I hu hd he
  obtain ⟨a0, ha0, hl0, -⟩ := tmJ_corr_exists I hr hL hg hw hf hzY hzc hu
  obtain ⟨e, he'⟩ := tmJ_lab_range (φ := I.φ) hlg hTl (hAut ha0)
  refine ⟨e, ?_⟩
  rw [← he', ← hlu, ← hl0, tmJLabOf, dif_pos (show a0 ∈ tmJW I.Nb from ha0.1)]

end RT

/-! ### The equation in the Lin* coordinates -/

section Lin

variable {m q : ℕ} {N : Subgroup (Perm (Fin m))} {A : Type*} [CommGroup A] {φ : N →* A}
  {σS σN : List (Perm (Fin m))} [((gens σS).subgroupOf (gens σN)).Normal]
  [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))]

/-- The coordinate map of the Lin* presentation. -/
noncomputable abbrev tmJHF (σS σN : List (Perm (Fin m))) [((gens σS).subgroupOf (gens σN)).Normal]
    [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))] :
    (Fin σN.length → ℤ) →ₗ[ℤ] Additive ((gens σN) ⧸ (gens σS).subgroupOf (gens σN)) :=
  linCoordMap (fun i : Fin σN.length => QuotientGroup.mk' ((gens σS).subgroupOf (gens σN))
    (linIntoSubgroup (gens σN) σN[i.val]))

/-- The quotient map `⟨σN⟩ → ⟨σN⟩ / ⟨σS⟩`. -/
noncomputable abbrev tmJHPsi (σS σN : List (Perm (Fin m))) [((gens σS).subgroupOf (gens σN)).Normal]
    [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))] :
    gens σN →* (gens σN) ⧸ (gens σS).subgroupOf (gens σN) :=
  QuotientGroup.mk' ((gens σS).subgroupOf (gens σN))

theorem tmJH_phiT_into {g : Perm (Fin m)} (hg : g ∈ gens σN) :
    phiT (gens σN) (tmJHPsi σS σN) g =
      QuotientGroup.mk' ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) g) := by
  rw [phiT, dif_pos hg, tmJV_into_eq _ _ hg]

/-- The image of the stored offset vector `s` is `lab'(u)⁻¹`. -/
theorem tmJH_f_s (d : Fin q → Perm (Fin m)) (hd : ∀ i, d i ∈ gens σN) {s : Fin σN.length → ℤ}
    (hs : Additive.ofMul ((((List.finRange q).map fun i => (d i)⁻¹).map fun u =>
        QuotientGroup.mk' ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) u)).prod) =
      tmJHF σS σN s) :
    tmJHF σS σN s = Additive.ofMul (tmJLab (gens σN) (tmJHPsi σS σN) d)⁻¹ := by
  rw [← hs, List.map_map, ← Fin.prod_univ_def, tmJLab, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  rw [← tmJH_phiT_into ((gens σN).inv_mem (hd i)), phiT_inv (hd i)]

/-- The image of `c B` is the value of the sum map. -/
theorem tmJH_f_B {lg : List (Fin q × Perm (Fin m))} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ gens σN)
    (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
    (hB : ∀ k, tmJHF σS σN (Bm k) = Additive.ofMul (QuotientGroup.mk'
      ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) (lg.get k).2)))
    (c : Fin lg.length → ℤ) :
    tmJHF σS σN (Matrix.vecMul c Bm) = Additive.ofMul (tmJSumT (gens σN) (tmJHPsi σS σN) lg c) := by
  rw [Matrix.vecMul_eq_sum, map_sum, tmJSumT, ofMul_prod]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, hB k, ofMul_zpow, tmJH_phiT_into (hlg k)]

/-- **A solution of the stacked equation solves the label equation.** -/
theorem tmJH_sound (hk : TmJSameKer φ (tmJHPsi σS σN)) {M : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hrel : linRelations M ≤ LinearMap.ker (tmJHF σS σN))
    {lg : List (Fin q × Perm (Fin m))} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
    (hB : ∀ k, tmJHF σS σN (Bm k) = Additive.ofMul (QuotientGroup.mk'
      ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) (lg.get k).2)))
    (d : Fin q → Perm (Fin m)) (hd : ∀ i, d i ∈ N) {s : Fin σN.length → ℤ}
    (hs : Additive.ofMul ((((List.finRange q).map fun i => (d i)⁻¹).map fun u =>
        QuotientGroup.mk' ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) u)).prod) =
      tmJHF σS σN s)
    {c : Fin lg.length → ℤ} {y : Fin σN.length → ℤ}
    (hcy : s + Matrix.vecMul c Bm + Matrix.vecMul y M = 0) :
    tmJSumT N φ lg c = tmJLab N φ d := by
  have hd' : ∀ i, d i ∈ gens σN := fun i => (hk.1 _).1 (hd i)
  have hlg' : ∀ k : Fin lg.length, (lg.get k).2 ∈ gens σN := fun k => (hk.1 _).1 (hlg k)
  rw [eq_comm, tmJLab_eq_sumT_iff hk hd hlg c]
  have e3 : tmJHF σS σN (Matrix.vecMul y M) = 0 := hrel ⟨y, rfl⟩
  have := congrArg (tmJHF σS σN) hcy
  rw [map_add, map_add, tmJH_f_s d hd' hs, tmJH_f_B hlg' Bm hB c, e3, map_zero, add_zero] at this
  have h2 := congrArg Additive.toMul this
  rw [toMul_add, toMul_ofMul, toMul_ofMul, toMul_zero] at h2
  exact (inv_mul_eq_one.1 h2)

/-- **The stacked equation is solvable** when the label equation is. -/
theorem tmJH_solvable (hk : TmJSameKer φ (tmJHPsi σS σN))
    {M : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hcert : linPresentationCertificate M (tmJHF σS σN))
    {lg : List (Fin q × Perm (Fin m))} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
    (hB : ∀ k, tmJHF σS σN (Bm k) = Additive.ofMul (QuotientGroup.mk'
      ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) (lg.get k).2)))
    (d : Fin q → Perm (Fin m)) (hd : ∀ i, d i ∈ N) {s : Fin σN.length → ℤ}
    (hs : Additive.ofMul ((((List.finRange q).map fun i => (d i)⁻¹).map fun u =>
        QuotientGroup.mk' ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) u)).prod) =
      tmJHF σS σN s)
    (hex : ∃ e : Fin lg.length → ℤ, tmJSumT N φ lg e = tmJLab N φ d) :
    ∃ (c : Fin lg.length → ℤ) (y : Fin σN.length → ℤ),
      s + Matrix.vecMul c Bm + Matrix.vecMul y M = 0 := by
  obtain ⟨e, he⟩ := hex
  have hd' : ∀ i, d i ∈ gens σN := fun i => (hk.1 _).1 (hd i)
  have hlg' : ∀ k : Fin lg.length, (lg.get k).2 ∈ gens σN := fun k => (hk.1 _).1 (hlg k)
  rw [eq_comm, tmJLab_eq_sumT_iff hk hd hlg e] at he
  have h0 : tmJHF σS σN (s + Matrix.vecMul e Bm) = 0 := by
    rw [map_add, tmJH_f_s d hd' hs, tmJH_f_B hlg' Bm hB e, ← he, ← ofMul_mul, inv_mul_cancel,
      ofMul_one]
  obtain ⟨y', hy'⟩ := (tmJ_cert_ker hcert _).1 h0
  refine ⟨e, -y', ?_⟩
  change Matrix.vecMul y' M = _ at hy'
  rw [Matrix.neg_vecMul, hy', add_neg_cancel]

/-- **The trivial quotient**: with `σN = []` every label is `1`, so `c = 0` solves. -/
theorem tmJH_triv (hk : TmJSameKer φ (tmJHPsi σS σN)) (h0 : σN = [])
    (lg : List (Fin q × Perm (Fin m))) (d : Fin q → Perm (Fin m)) (hd : ∀ i, d i ∈ N) :
    tmJSumT N φ lg 0 = tmJLab N φ d := by
  have hd1 : d = 1 := by
    funext i
    have := (hk.1 _).1 (hd i)
    subst h0
    have e : gens ([] : List (Perm (Fin m))) = ⊥ := by
      unfold gens
      rw [show {g : Perm (Fin m) | g ∈ ([] : List (Perm (Fin m)))} = ∅ by ext; simp,
        Subgroup.closure_empty]
    rw [e, Subgroup.mem_bot] at this
    exact this
  subst hd1
  rw [tmJLab_one]
  simp [tmJSumT]

end Lin

/-! ### Facts for the small programs -/

section Small

variable {B : Type} {q : ℕ}

/-- The coordinates of the local product after the first `i` indices. -/
def tmJHLamDi (lg : List (Fin q × Perm B)) (c : Fin lg.length → ℤ) (i : ℕ) : Fin q → Perm B :=
  fun a => (((List.finRange lg.length).take i).map fun k =>
    if (lg.get k).1 = a then (lg.get k).2 ^ c k else 1).prod

theorem tmJHLamDi_zero (lg : List (Fin q × Perm B)) (c : Fin lg.length → ℤ) :
    tmJHLamDi lg c 0 = 1 := by
  funext a; simp [tmJHLamDi]

theorem tmJHLamDi_full (lg : List (Fin q × Perm B)) (c : Fin lg.length → ℤ) :
    tmJHLamDi lg c lg.length = tmJLamD lg c := by
  funext a
  simp only [tmJHLamDi, tmJLamD]
  rw [List.take_of_length_le (by simp)]

/-- **One step of the fold**: multiply by the local element `(g_k^{c_k} at a_k; 1)` on the left. -/
theorem tmJHLamDi_succ (lg : List (Fin q × Perm B)) (c : Fin lg.length → ℤ) {i : ℕ}
    (hi : i < lg.length) :
    tmJLoc (lg.get ⟨i, hi⟩).1 ((lg.get ⟨i, hi⟩).2 ^ c ⟨i, hi⟩) * tmJP (tmJHLamDi lg c i, 1) =
      tmJP (tmJHLamDi lg c (i + 1), 1) := by
  rw [tmJLoc, tmJP_mul]
  congr 1
  ext1
  · funext a
    simp only [tmJHLamDi, Perm.one_apply]
    rw [List.take_succ_eq_append_getElem (by simpa using hi), List.map_append, List.prod_append]
    simp only [List.getElem_finRange, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    congr 1
    by_cases ha : a = (lg.get ⟨i, hi⟩).1
    · subst ha; simp [Fin.cast]
    · rw [Pi.mulSingle_eq_of_ne ha, if_neg]
      · intro h; apply ha; rw [← h]; rfl
  · simp

/-- The inverse of an integer power, as in the power program. -/
theorem tmJH_pow_inv {G : Type*} [Group G] (g : G) (c : ℤ) :
    (g ^ c)⁻¹ = if c < 0 then g ^ c.natAbs else g⁻¹ ^ c.natAbs := by
  split_ifs with hc
  · have : c = -(c.natAbs : ℤ) := by omega
    rw [this, zpow_neg, inv_inv, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
  · have : c = (c.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, Int.natAbs_natCast, inv_pow]

/-- Reading a pair on `Fin (m q)`: the point `i + q c` goes to `π i + q (d_i⁻¹ c)`. -/
theorem tmJH_pair_val {m : ℕ} (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (c : Fin m)
    (i : Fin q) :
    ((toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π))
      (finProdFinEquiv (c, i)) : Fin (m * q)) : ℕ) = π i + q * ((d i)⁻¹ c) := by
  simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply, tmJP, finProdFinEquiv_apply_val]

theorem tmJH_dec_div {m : ℕ} (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (c : Fin m)
    (i : Fin q) :
    ((toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π))
      (finProdFinEquiv (c, i)) : Fin (m * q)) : ℕ) / q = (d i)⁻¹ c := by
  rw [tmJH_pair_val]
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0)
  rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt (π i).2, zero_add]

theorem tmJH_dec_mod {m : ℕ} (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (c : Fin m)
    (i : Fin q) :
    ((toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π))
      (finProdFinEquiv (c, i)) : Fin (m * q)) : ℕ) % q = π i := by
  rw [tmJH_pair_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (π i).2]

end Small

end GI.Impl
