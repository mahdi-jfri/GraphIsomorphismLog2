import Workspace.Algorithm.Aggregation

/-!
# The structure choices of an aggregation round, as a program makes them

After the certificate and comparison phases the program fixes three choices of the round:
the numbers of the comparison classes
(`num`), the joint `κ`-ary refinement of the two tuple colorings (`hK` at that one argument) and
the source tuple (`src`). None of them enters the certificate or comparison scripts, so the
program may fix them after those phases ran. This file gives the mathematics.

* `stNum`: numbers a class by the first tuple `t₀`, in a list of all tuples, with `(x, t₀)` in
  the class. `stNum_ok`: it separates the classes of `x` (`ClassNum.OK`). `tcol_stNum`: the tuple
  color of `(z, t)` is the index of the first `t₀` with `tupleRel (x, t₀) (z, t)`; this is what
  a program computes from the comparison table. The numbers are at most `q^κ`, as the cited
  refinement task asks of its input.
* `stSetJ`: a joint refinement function with one value replaced (`stSetJ_same`, `stSetJ_ne`).
* `st_orbitalOut_good`: in Case 2b every source tuple whose first six entries are distinct
  points of the dominant orbit is good, for every refiner (the proof of `exists_orbitalOut_good`
  uses only this). So a program needs no transitivity degree to choose `src`.
* `stSrcGood_*`: the condition `src_good` from the case of the round.
* `stRound`: the round with the three choices replaced; its certificate and comparison scripts
  are those of the old round (`stRound_certScript`, `stRound_compScript`).
-/

namespace GI.Impl

open GI.Algorithm GI.Cited Equiv Equiv.Perm GI.LocalCertificates

variable {Ω C : Type}

/-! ### Class numbers by first occurrence -/

section Num

variable (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom] {q : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ)

theorem st_tcls_eq_iff {z z' : S.dom → C} {t t' : Fin κ → Fin q} :
    tcls S πd κ z t = tcls S πd κ z' t' ↔ tupleRel S.domGroup πd κ (z, t) (z', t') := by
  have he := tupleRel_equivalence (G := S.domGroup) (π := πd) (k := κ) (C := C)
  constructor
  · intro h
    have : (z, t) ∈ tcls S πd κ z' t' := h ▸ he.refl (z, t)
    exact this
  · intro h
    ext p
    exact ⟨fun hp => he.trans hp h, fun hp => he.trans hp (he.symm h)⟩

open Classical in
/-- **Class numbers by first occurrence**: a class gets the index, in `ts`, of the first tuple
`t₀` such that `(x, t₀)` lies in the class (the length of `ts` if there is none). -/
noncomputable def stNum (ts : List (Fin κ → Fin q)) (x : S.dom → C) : ClassNum S κ q :=
  fun c => ts.findIdx fun t₀ => decide ((x, t₀) ∈ c)

open Classical in
/-- The tuple color under `stNum`: the index of the first `t₀` in `ts` with
`tupleRel (x, t₀) (z, t)`. -/
theorem tcol_stNum (ts : List (Fin κ → Fin q)) (x z : S.dom → C) (t : Fin κ → Fin q) :
    tcol S πd κ (stNum S κ ts x) z t =
      ts.findIdx fun t₀ => decide (tupleRel S.domGroup πd κ (x, t₀) (z, t)) := rfl

theorem tcol_stNum_le (ts : List (Fin κ → Fin q)) (x z : S.dom → C) (t : Fin κ → Fin q) :
    tcol S πd κ (stNum S κ ts x) z t ≤ ts.length := by
  rw [tcol_stNum]; exact List.findIdx_le_length

open Classical in
/-- **The first-occurrence numbers separate the classes of `x`**, when `ts` holds every tuple. -/
theorem stNum_numOK (ts : List (Fin κ → Fin q)) (hts : ∀ t, t ∈ ts) (x y : S.dom → C) :
    NumOK S πd κ (stNum S κ ts x) x y := by
  have he := tupleRel_equivalence (G := S.domGroup) (π := πd) (k := κ) (C := C)
  rintro c hc d hd h
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hc hd
  obtain ⟨t, rfl⟩ := hc
  obtain ⟨t', rfl⟩ := hd
  change tcol S πd κ (stNum S κ ts x) x t = tcol S πd κ (stNum S κ ts x) x t' at h
  rw [tcol_stNum, tcol_stNum] at h
  have hlt : (ts.findIdx fun t₀ => decide (tupleRel S.domGroup πd κ (x, t₀) (x, t))) <
      ts.length := List.findIdx_lt_length_of_exists ⟨t, hts t, by simpa using he.refl _⟩
  have hlt' : (ts.findIdx fun t₀ => decide (tupleRel S.domGroup πd κ (x, t₀) (x, t'))) <
      ts.length := by rw [← h]; exact hlt
  have h1 := List.findIdx_getElem (w := hlt)
  have h2 := List.findIdx_getElem (w := hlt')
  simp only [decide_eq_true_eq] at h1 h2
  rw [← st_tcls_eq_iff] at h1 h2
  have e : ts[ts.findIdx fun t₀ => decide (tupleRel S.domGroup πd κ (x, t₀) (x, t))]'hlt =
      ts[ts.findIdx fun t₀ => decide (tupleRel S.domGroup πd κ (x, t₀) (x, t'))]'hlt' := by
    simp only [h]
  rw [e] at h1
  exact h1.symm.trans h2

theorem stNum_ok (fin : Finite Ω) (S : State Ω C) (L : GiantLabels S)
    (πd : S.domGroup →* alternatingGroup (Fin L.q)) (κ : ℕ) (ts : List (Fin κ → Fin L.q))
    (hts : ∀ t, t ∈ ts) :
    haveI := fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq S.dom := Classical.decEq _
    ClassNum.OK fin S L πd κ (stNum S κ ts (dstr S S.x)) := by
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  exact stNum_numOK S πd κ ts hts _ _

end Num

/-! ### One value of a joint refinement function -/

open Classical in
/-- `J` with its value at `(n, k, c, c')` replaced by `(d, d')`. -/
noncomputable def stSetJ (J : JointFn) (n k : ℕ) (c c' d d' : (Fin k → Fin n) → ℕ)
    (h : JointOK c c' d d') : JointFn := fun n' k' =>
  if hn : n' = n ∧ k' = k then
    hn.1 ▸ hn.2 ▸ fun a a' => if hc : a = c ∧ a' = c' then ⟨(d, d'), hc.1 ▸ hc.2 ▸ h⟩
      else J n k a a'
  else J n' k'

theorem stSetJ_same (J : JointFn) (n k : ℕ) (c c' d d' : (Fin k → Fin n) → ℕ)
    (h : JointOK c c' d d') : (stSetJ J n k c c' d d' h n k c c').1 = (d, d') := by
  simp [stSetJ]

theorem stSetJ_ne (J : JointFn) (n k : ℕ) (c c' d d' : (Fin k → Fin n) → ℕ)
    (h : JointOK c c' d d') {k' : ℕ} (hk : k' ≠ k) (n' : ℕ) :
    stSetJ J n k c c' d d' h n' k' = J n' k' := by
  simp [stSetJ, hk]

/-- The other values at the same degree and arity are kept; so a program that fixes the values
of a joint refinement one argument at a time (with a cache, so that an argument seen before is not
asked again) keeps the earlier ones. -/
theorem stSetJ_other (J : JointFn) (n k : ℕ) (c c' d d' : (Fin k → Fin n) → ℕ)
    (h : JointOK c c' d d') (a a' : (Fin k → Fin n) → ℕ) (ha : ¬ (a = c ∧ a' = c')) :
    stSetJ J n k c c' d d' h n k a a' = J n k a a' := by
  simp [stSetJ, ha]

/-- **The refined colors of the structures are the replaced value**: with `J` replaced at the
pair of tuple colorings by `(d, d')`, the structures of `x` and `y` carry `d` and `d'`. -/
theorem stSetJ_col (fin : Finite Ω) (S : State Ω C) (L : GiantLabels S)
    (πd : S.domGroup →* alternatingGroup (Fin L.q)) (J : JointFn) (κ : ℕ)
    (nm : ClassNum S κ L.q) :
    haveI := fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq S.dom := Classical.decEq _
    ∀ (d d' : (Fin κ → Fin L.q) → ℕ)
      (h : JointOK (tcol S πd κ nm (dstr S S.x)) (tcol S πd κ nm (dstr S S.y)) d d') {ℓ : ℕ}
      (t : Fin ℓ → Fin L.q),
      (structX fin S L πd (stSetJ J L.q κ _ _ d d' h) κ nm t).col = d ∧
      (structY fin S L πd (stSetJ J L.q κ _ _ d d' h) κ nm t).col = d' := by
  intro d d' h ℓ t
  have e := stSetJ_same J L.q κ _ _ d d' h
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-! ### The source tuple -/

section Src

variable {q : ℕ}

/-- **Case 2b: a source tuple whose first six entries are distinct points of the dominant orbit
is good**, for every refiner with the clauses of one side of a joint refinement. The degree `d`
of transitivity is at most `5`, so the anchors and the orbital pair use only these six entries
(`orbitalAt_good`). -/
theorem st_orbitalOut_good (h6 : SixTransitiveContainsAlt) {H : Subgroup (Perm (Fin q))}
    (hq : 16 ≤ q) {ℓ : ℕ} (hne : (domSet H).Nonempty) (hng : ¬ GiantOn H (domSet H))
    (t : Fin ℓ → Fin q) (hinj : ∀ i j : Fin ℓ, i.val < 6 → j.val < 6 → t i = t j → i = j)
    (hin : ∀ i : Fin ℓ, i.val < 6 → t i ∈ domSet H) (hℓ : 6 ≤ ℓ) {β : ℝ} (R : Refiner2 q)
    (hR : SideOK R) : (orbitalOut R H t).Good β := by
  classical
  set Φ := domSet H with hΦdef
  have hdom : q < 2 * Φ.card := domSet_card_lt hne
  have hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ := fun h hh a ha => apply_mem_domSet hh ha
  set d := transDeg H Φ with hddef
  obtain ⟨htr, -⟩ := transDeg_spec H Φ
  have hd5 : d ≤ 5 := transDeg_le_five h6 hpres (by omega) hng
  have hd1 : 1 ≤ d := by
    refine le_transDeg (by omega) (transOn_one_of_orbit fun a ha b hb => ?_)
    have hb' : b ∈ lorb H a := by rw [← domSet_eq_lorb ha]; exact hb
    exact mem_lorb.1 hb'
  have hntr : ¬ TransOn H Φ (d + 1) := fun h => by
    have := le_transDeg (by omega) h
    omega
  unfold orbitalOut
  exact orbitalAt_good hR hq (by omega) hd1 hd5 hdom htr hntr
    (fun i j hi hj e => hinj i j (by omega) (by omega) e) (fun i hi => hin i (by omega))

/-- **The source tuple of Case 2b as a program computes it**: the six smallest points of the
dominant orbit `Φ`, then the smallest point again. -/
noncomputable def stSrc2b (Φ : Finset (Fin q)) (hΦ : 6 ≤ Φ.card) {ℓ : ℕ} : Fin ℓ → Fin q :=
  fun i => if h : i.val < 6 then Φ.orderEmbOfFin rfl ⟨i.val, by omega⟩
    else Φ.orderEmbOfFin rfl ⟨0, by omega⟩

theorem stSrc2b_inj (Φ : Finset (Fin q)) (hΦ : 6 ≤ Φ.card) {ℓ : ℕ} (i j : Fin ℓ)
    (hi : i.val < 6) (hj : j.val < 6) (e : stSrc2b Φ hΦ i = stSrc2b Φ hΦ j) : i = j := by
  simp only [stSrc2b, dif_pos hi, dif_pos hj] at e
  exact Fin.ext (Fin.mk.inj_iff.1 ((Φ.orderEmbOfFin rfl).injective e))

theorem stSrc2b_mem (Φ : Finset (Fin q)) (hΦ : 6 ≤ Φ.card) {ℓ : ℕ} (i : Fin ℓ) :
    stSrc2b Φ hΦ i ∈ Φ := by
  unfold stSrc2b
  split_ifs <;> exact Finset.orderEmbOfFin_mem _ _ _

variable {Ω C : Type} (fin : Finite Ω) (S : State Ω C) (L : GiantLabels S)
  (πd : S.domGroup →* alternatingGroup (Fin L.q)) (J : JointFn) (κ : ℕ) (nm : ClassNum S κ L.q)
  {β : ℝ}

/-- The condition `src_good` of a round, for the data `J`, `nm`, `src`. -/
def StSrcGood (β : ℝ) {ℓ : ℕ} (src : Fin ℓ → Fin L.q) : Prop :=
  (aggCase (structX fin S L πd J κ nm src).grp = .twoB ∨
      aggCase (structX fin S L πd J κ nm src).grp = .three) →
    ∀ Y, (outPair J (structX fin S L πd J κ nm src) Y).1.Good β

/-- The ideal certificate group of the source string does not depend on the choices. -/
theorem st_structX_grp {ℓ : ℕ} (src : Fin ℓ → Fin L.q) :
    (structX fin S L πd J κ nm src).grp =
      (haveI := fin
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq S.dom := Classical.decEq _
       idealGrp S πd κ (dstr S S.x)) := rfl

/-- Cases 1 and 2a: every tuple is good. -/
theorem stSrcGood_other {ℓ : ℕ} (src : Fin ℓ → Fin L.q)
    (h : aggCase (structX fin S L πd J κ nm src).grp = .one ∨
      aggCase (structX fin S L πd J κ nm src).grp = .twoA) :
    StSrcGood fin S L πd J κ nm β src := by
  rintro (h' | h') <;> rcases h with h | h <;> rw [h] at h' <;> cases h'

/-- **Case 2b**: the first six entries of `src` are distinct points of the dominant orbit. -/
theorem stSrcGood_twoB (h6 : SixTransitiveContainsAlt) (hq : 16 ≤ L.q) {ℓ : ℕ} (hℓ : 6 ≤ ℓ)
    (src : Fin ℓ → Fin L.q)
    (hc : aggCase (structX fin S L πd J κ nm src).grp = .twoB)
    (hinj : ∀ i j : Fin ℓ, i.val < 6 → j.val < 6 → src i = src j → i = j)
    (hin : ∀ i : Fin ℓ, i.val < 6 → src i ∈ domSet (structX fin S L πd J κ nm src).grp) :
    StSrcGood fin S L πd J κ nm β src := by
  intro _ Y
  set H := (structX fin S L πd J κ nm src).grp
  have hne : (domSet H).Nonempty := by
    unfold aggCase at hc
    by_contra h
    rw [if_neg h] at hc
    split_ifs at hc
  have hng : ¬ GiantOn H (domSet H) := by
    unfold aggCase at hc
    rw [if_pos hne] at hc
    split_ifs at hc with h
    exact h
  rw [outPair_twoB J Y hc]
  exact st_orbitalOut_good h6 hq hne hng _ hinj hin hℓ _ (J.left_ok _ _ _)

/-- **Case 2b with the computed tuple** `stSrc2b`: the dominant orbit has more than `q/2 ≥ 8`
points. -/
theorem stSrcGood_twoB' (h6 : SixTransitiveContainsAlt) (hq : 16 ≤ L.q) {ℓ : ℕ} (hℓ : 6 ≤ ℓ)
    (hc : aggCase (haveI := fin
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq S.dom := Classical.decEq _
       idealGrp S πd κ (dstr S S.x)) = .twoB)
    (hΦ : 6 ≤ (domSet (haveI := fin
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq S.dom := Classical.decEq _
       idealGrp S πd κ (dstr S S.x))).card) :
    StSrcGood fin S L πd J κ nm β (stSrc2b (ℓ := ℓ) _ hΦ) :=
  stSrcGood_twoB fin S L πd J κ nm h6 hq hℓ _ hc (stSrc2b_inj _ hΦ) fun i _ => stSrc2b_mem _ hΦ i

/-- In Case 2b the dominant orbit has at least six points, since it has more than `q/2` points
and `q ≥ 16`. -/
theorem st_domSet_six {H : Subgroup (Perm (Fin q))} (hq : 16 ≤ q) (hc : aggCase H = .twoB) :
    6 ≤ (domSet H).card := by
  have hne : (domSet H).Nonempty := by
    unfold aggCase at hc
    by_contra h
    rw [if_neg h] at hc
    split_ifs at hc
  have := domSet_card_lt hne
  omega

/-- **Case 3**: the object of the Design Lemma on the refined colors of the source string is
good; it does not depend on the target structure. -/
theorem stSrcGood_three {ℓ : ℕ} (src : Fin ℓ → Fin L.q)
    (hc : aggCase (structX fin S L πd J κ nm src).grp = .three)
    (hg : (designOut (structX fin S L πd J κ nm src).col src).Good β) :
    StSrcGood fin S L πd J κ nm β src := by
  intro _ Y
  rw [outPair_three J Y hc]
  exact hg

end Src

/-! ### The round with the structure choices replaced -/

section Round

variable {P : Params} {S : State Ω C} {L : GiantLabels S}

/-- **The round `I` with the class numbers `nm`, the joint refinement function `J` and the
source tuple `src`**; every other field is that of `I`. -/
noncomputable def stRound (I : Aggregation P S L) (nm : ClassNum S P.κ L.q)
    (hnm : ClassNum.OK I.fin S L (L.domMap I.con.onDomain) P.κ nm) (J : JointFn)
    (src : Fin (P.κ + 1) → Fin L.q)
    (hsrc : StSrcGood I.fin S L (L.domMap I.con.onDomain) J P.κ nm P.β src) :
    Aggregation P S L :=
  { I with
    toAggregationData := { I.toAggregationData with hK := J }
    num := nm
    num_ok := hnm
    src := src
    src_good := hsrc }

variable (I : Aggregation P S L) (nm : ClassNum S P.κ L.q)
  (hnm : ClassNum.OK I.fin S L (L.domMap I.con.onDomain) P.κ nm) (J : JointFn)
  (src : Fin (P.κ + 1) → Fin L.q)
  (hsrc : StSrcGood I.fin S L (L.domMap I.con.onDomain) J P.κ nm P.β src)

theorem stRound_certScript : (stRound I nm hnm J src hsrc).certScript = I.certScript := rfl
theorem stRound_compScript : (stRound I nm hnm J src hsrc).compScript = I.compScript := rfl
theorem stRound_num : (stRound I nm hnm J src hsrc).num = nm := rfl
theorem stRound_src : (stRound I nm hnm J src hsrc).src = src := rfl
theorem stRound_hK : (stRound I nm hnm J src hsrc).hK = J := rfl
theorem stRound_sel : (stRound I nm hnm J src hsrc).sel = I.sel := rfl
theorem stRound_con : (stRound I nm hnm J src hsrc).con = I.con := rfl

/-- The script of the new round: the old certificate and comparison phases, then the new
items. -/
theorem stRound_script : (stRound I nm hnm J src hsrc).script =
    I.certScript.bind fun _ => I.compScript.bind fun _ => (stRound I nm hnm J src hsrc).itemsScript :=
  rfl

end Round

end GI.Impl
