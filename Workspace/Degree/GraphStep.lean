module

public import Workspace.Degree.GraphLevels
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.List.GetD

/-!
# One step of the layers

Section 9.2 of the paper.

* `slotGroup A`: the group `W(A)` on the slots `V × Fin D`.
* `slotColor`: the string of a step.
* `Query`: the set `Iso_{W(A_r)}(c_X, c_Y)`.
* `decMap`: the map `dec` of Lemma 9.2. It reads the action on the ball, and it reads the action on
  the new layer through one slot `par w` for each new vertex `w`.
* `query_dec`, `query_lift`, `query_dec_mul`: parts (a), (b) and (c) of Lemma 9.2.
-/

@[expose] public section

namespace GI.Degree

open Equiv

variable {V : Type*} {D : ℕ}

/-- The group `W(A)`: the permutations of the slots that permute the fibers as an element of `A`
does. -/
def slotGroup (D : ℕ) (A : Subgroup (Perm V)) : Subgroup (Perm (V × Fin D)) where
  carrier := {f | ∃ a ∈ A, ∀ s, (f s).1 = a s.1}
  mul_mem' := by
    rintro f f' ⟨a, ha, h⟩ ⟨a', ha', h'⟩
    exact ⟨a * a', A.mul_mem ha ha', fun s => by simp [Perm.mul_apply, h, h']⟩
  one_mem' := ⟨1, A.one_mem, fun _ => rfl⟩
  inv_mem' := by
    rintro f ⟨a, ha, h⟩
    refine ⟨a⁻¹, A.inv_mem ha, fun s => ?_⟩
    have h1 := h (f⁻¹ s)
    have h2 : f (f⁻¹ s) = s := f.apply_symm_apply s
    rw [h2] at h1
    rw [h1]
    simp

/-- The target of a slot, if it is live. -/
def tgt (f : V → List V) (s : V × Fin D) : Option V := (f s.1)[(s.2 : ℕ)]?

theorem mem_of_tgt {f : V → List V} {s : V × Fin D} {w : V} (h : tgt f s = some w) : w ∈ f s.1 :=
  List.mem_of_getElem? h

theorem exists_tgt {f : V → List V} {u w : V} (hD : (f u).length ≤ D) (h : w ∈ f u) :
    ∃ i : Fin D, tgt f (u, i) = some w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨⟨i, by omega⟩, by simp [tgt, hi]⟩

/-- `f` lists the forward neighbours of each vertex without repetition. -/
structure FwdOK (ℓ : V → ℕ) (X : SimpleGraph V) (f : V → List V) : Prop where
  nodup : ∀ u, (f u).Nodup
  mem : ∀ u w, w ∈ f u ↔ X.Adj u w ∧ ℓ w = ℓ u + 1

open Classical in
/-- The string of a step: the colour of a pair of slots. -/
noncomputable def slotColor (ℓ : V → ℕ) (r : ℕ) (X : SimpleGraph V) (f : V → List V)
    (s s' : V × Fin D) : ℕ :=
  if ℓ s.1 = r ∧ ℓ s'.1 = r then
    match tgt f s, tgt f s' with
    | some w, some w' => 2 + (if w = w' then 1 else 0) + 2 * (if X.Adj w w' then 1 else 0)
    | _, _ => 1
  else 0

variable {ℓ : V → ℕ} {r : ℕ} {X Y : SimpleGraph V} {fX fY : V → List V}

open Classical in
theorem slotColor_some {s s' : V × Fin D} {w w' : V} (h : ℓ s.1 = r) (h' : ℓ s'.1 = r)
    (ht : tgt fX s = some w) (ht' : tgt fX s' = some w') :
    slotColor ℓ r X fX s s' = 2 + (if w = w' then 1 else 0) + 2 * (if X.Adj w w' then 1 else 0) := by
  simp only [slotColor, h, h', and_self, if_true, ht, ht']

theorem slotColor_none {s : V × Fin D} (h : ℓ s.1 = r) (ht : tgt fX s = none) :
    slotColor ℓ r X fX s s = 1 := by
  simp only [slotColor, h, and_self, if_true, ht]

theorem slotColor_none' {s s' : V × Fin D} (h : ℓ s.1 = r) (h' : ℓ s'.1 = r)
    (ht : tgt fX s = none ∨ tgt fX s' = none) : slotColor ℓ r X fX s s' = 1 := by
  simp only [slotColor, h, h', and_self, if_true]
  rcases ht with ht | ht <;> rw [ht]
  cases tgt fX s <;> rfl

theorem slotColor_off {s s' : V × Fin D} (h : ¬(ℓ s.1 = r ∧ ℓ s'.1 = r)) :
    slotColor ℓ r X fX s s' = 0 := by
  simp only [slotColor, h, if_false]

theorem slotColor_le (s s' : V × Fin D) : slotColor ℓ r X fX s s' ≤ 5 := by
  unfold slotColor
  split_ifs
  · cases tgt fX s <;> cases tgt fX s' <;> simp only <;> try omega
    split_ifs <;> omega
  · omega

/-- The set `Iso_{W(A_r)}(c_X, c_Y)`. -/
def Query (D : ℕ) (ℓ : V → ℕ) (r : ℕ) (X Y : SimpleGraph V) (fX fY : V → List V) :
    Set (Perm (V × Fin D)) :=
  {g | g ∈ slotGroup D (ballGroup ℓ r X) ∧
    ∀ s s', slotColor ℓ r Y fY (g s) (g s') = slotColor ℓ r X fX s s'}

section Facts

variable {g : Perm (V × Fin D)}

theorem Query.level (hg : g ∈ Query D ℓ r X Y fX fY) (s : V × Fin D) : ℓ (g s).1 = ℓ s.1 := by
  obtain ⟨⟨a, ha, h⟩, -⟩ := hg
  rw [h, ha.1]

theorem Query.tgt_some (hg : g ∈ Query D ℓ r X Y fX fY) {s : V × Fin D} {w : V} (h : ℓ s.1 = r)
    (ht : tgt fX s = some w) : ∃ z, tgt fY (g s) = some z := by
  have h2 := hg.2 s s
  rw [slotColor_some h h ht ht] at h2
  have hl := Query.level hg s
  rcases hz : tgt fY (g s) with _ | z
  · rw [slotColor_none (hl.trans h) hz] at h2
    simp at h2
  · exact ⟨z, rfl⟩

theorem Query.tgt_none (hg : g ∈ Query D ℓ r X Y fX fY) {s : V × Fin D} (h : ℓ s.1 = r)
    (ht : tgt fX s = none) : tgt fY (g s) = none := by
  have h2 := hg.2 s s
  rw [slotColor_none h ht] at h2
  have hl := Query.level hg s
  rcases hz : tgt fY (g s) with _ | z
  · rfl
  · rw [slotColor_some (hl.trans h) (hl.trans h) hz hz] at h2
    simp at h2

/-- Equal targets and adjacent targets are preserved, in both directions. -/
theorem Query.pair (hg : g ∈ Query D ℓ r X Y fX fY) {s s' : V × Fin D} {w w' z z' : V}
    (h : ℓ s.1 = r) (h' : ℓ s'.1 = r) (ht : tgt fX s = some w) (ht' : tgt fX s' = some w')
    (hz : tgt fY (g s) = some z) (hz' : tgt fY (g s') = some z') :
    (w = w' ↔ z = z') ∧ (X.Adj w w' ↔ Y.Adj z z') := by
  classical
  have h2 := hg.2 s s'
  rw [slotColor_some h h' ht ht',
    slotColor_some ((Query.level hg s).trans h) ((Query.level hg s').trans h') hz hz'] at h2
  constructor
  · by_cases a : w = w' <;> by_cases b : z = z' <;> simp only [a, b] <;> simp_all <;> split_ifs at h2 <;> omega
  · by_cases a : X.Adj w w' <;> by_cases b : Y.Adj z z' <;> simp only [a, b] <;> simp_all <;> split_ifs at h2 <;> omega

end Facts

variable [Fintype V] [DecidableEq V]

/-- The map `dec`. On levels at most `r` it reads the fiber of a vertex through the slot number `z`.
On level `r + 1` it reads the target of the image of the slot `par u`. -/
def decMap (ℓ : V → ℕ) (r : ℕ) (fY : V → List V) (par : V → V × Fin D) (z : Fin D)
    (g : Perm (V × Fin D)) (u : V) : V :=
  if ℓ u ≤ r then (g (u, z)).1
  else if ℓ u = r + 1 then (tgt fY (g (par u))).getD u else u

/-- `par` gives a slot of level `r` for each vertex of level `r + 1`. -/
def ParOK (ℓ : V → ℕ) (r : ℕ) (fX : V → List V) (par : V → V × Fin D) : Prop :=
  ∀ w, ℓ w = r + 1 → ℓ (par w).1 = r ∧ tgt fX (par w) = some w

section Dec

variable {R : ℕ} {par : V → V × Fin D} {z : Fin D} {g : Perm (V × Fin D)}

/-- **Lemma 9.2(a).** -/
theorem query_dec (hX : HasLevels X ℓ R) (hY : HasLevels Y ℓ R) (hr : r + 1 ≤ R)
    (fXok : FwdOK ℓ X fX) (fYok : FwdOK ℓ Y fY) (hDX : ∀ u, (fX u).length ≤ D)
    (hDY : ∀ u, (fY u).length ≤ D) (hpar : ParOK ℓ r fX par) (h1 : 1 ∈ Ball ℓ r X Y)
    (hg : g ∈ Query D ℓ r X Y fX fY) :
    ∃ h ∈ Ball ℓ (r + 1) X Y, ∀ u, h u = decMap ℓ r fY par z g u := by
  obtain ⟨a, ha, hfst⟩ := hg.1
  obtain ⟨a1, a2, a3⟩ := ha
  set F := decMap ℓ r fY par z g with hF
  have hlow : ∀ u, ℓ u ≤ r → F u = a u := fun u hu => by
    simp only [hF, decMap, hu, if_true]
    exact hfst _
  have hmid : ∀ u, ℓ u = r + 1 → tgt fY (g (par u)) = some (F u) := fun u hu => by
    obtain ⟨p1, p2⟩ := hpar u hu
    obtain ⟨y, hy⟩ := Query.tgt_some hg p1 p2
    simp only [hF, decMap]
    rw [if_neg (by omega), if_pos hu, hy]
    rfl
  have hhi : ∀ u, r + 1 < ℓ u → F u = u := fun u hu => by
    simp only [hF, decMap]
    rw [if_neg (by omega), if_neg (by omega)]
  have hmidl : ∀ u, ℓ u = r + 1 → ℓ (F u) = r + 1 := fun u hu => by
    have h3 := mem_of_tgt (hmid u hu)
    have h4 := ((fYok.mem _ _).1 h3).2
    rw [h4, Query.level hg, (hpar u hu).1]
  have hl : ∀ u, ℓ (F u) = ℓ u := fun u => by
    rcases lt_trichotomy (ℓ u) (r + 1) with h | h | h
    · rw [hlow u (by omega), a1]
    · rw [hmidl u h, h]
    · rw [hhi u h]
  have hinj : Function.Injective F := by
    intro u v huv
    have hlv : ℓ u = ℓ v := by rw [← hl u, huv, hl v]
    rcases lt_trichotomy (ℓ u) (r + 1) with h | h | h
    · rw [hlow u (by omega), hlow v (by omega)] at huv
      exact a.injective huv
    · have p := hpar u h
      have p' := hpar v (hlv ▸ h)
      have := Query.pair hg p.1 p'.1 p.2 p'.2 (hmid u h) (hmid v (hlv ▸ h))
      exact this.1.2 huv
    · rwa [hhi u h, hhi v (hlv ▸ h)] at huv
  have hcross : ∀ u v, ℓ u ≤ r → ℓ v = r + 1 → (X.Adj u v ↔ Y.Adj (F u) (F v)) := by
    intro u v hu hv
    rw [hlow u hu]
    by_cases hur : ℓ u = r
    · constructor
      · intro hadj
        have hm : v ∈ fX u := (fXok.mem _ _).2 ⟨hadj, by omega⟩
        obtain ⟨i, hi⟩ := exists_tgt (hDX u) hm
        obtain ⟨y, hy⟩ := Query.tgt_some hg (s := (u, i)) hur hi
        have p := hpar v hv
        have h3 := Query.pair hg (s := (u, i)) hur p.1 hi p.2 hy (hmid v hv)
        have h4 : y = F v := h3.1.1 rfl
        have h5 := mem_of_tgt hy
        rw [hfst, h4] at h5
        exact ((fYok.mem _ _).1 h5).1
      · intro hadj
        have hm : F v ∈ fY (a u) := (fYok.mem _ _).2 ⟨hadj, by rw [hmidl v hv, a1]; omega⟩
        obtain ⟨i, hi⟩ := exists_tgt (hDY _) hm
        set s := g⁻¹ (a u, i) with hs
        have hgs : g s = (a u, i) := by simp [hs]
        have hs1 : s.1 = u := by
          have := hfst s
          rw [hgs] at this
          exact (a.injective this).symm
        have hsr : ℓ s.1 = r := by rw [hs1]; exact hur
        rcases hv' : tgt fX s with _ | v'
        · have := Query.tgt_none hg hsr hv'
          rw [hgs, hi] at this
          cases this
        · have p := hpar v hv
          have h3 := Query.pair hg hsr p.1 hv' p.2 (by rw [hgs]; exact hi) (hmid v hv)
          have h4 : v' = v := h3.1.2 rfl
          have h5 := mem_of_tgt hv'
          rw [hs1, h4] at h5
          exact ((fXok.mem _ _).1 h5).1
    · constructor
      · intro hadj
        have := hX.step u v hadj (by omega)
        omega
      · intro hadj
        have := hY.step _ _ hadj (by rw [a1]; omega)
        rw [hmidl v hv, a1] at this
        omega
  have hbij : Function.Bijective F := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective F hbij, ⟨fun u => hl u, fun u hu => hhi u hu, fun u v hu hv => ?_⟩,
    fun u => rfl⟩
  simp only [Equiv.ofBijective_apply]
  rcases Nat.lt_or_ge (ℓ u) (r + 1) with h | h <;> rcases Nat.lt_or_ge (ℓ v) (r + 1) with h' | h'
  · rw [hlow u (by omega), hlow v (by omega), a3 u v (by omega) (by omega)]
    exact h1.2.2 _ _ (by rw [a1]; omega) (by rw [a1]; omega)
  · exact hcross u v (by omega) (by omega)
  · rw [X.adj_comm, Y.adj_comm]
    exact hcross v u (by omega) (by omega)
  · have e1 : ℓ u = r + 1 := by omega
    have e2 : ℓ v = r + 1 := by omega
    have p := hpar u e1
    have p' := hpar v e2
    exact (Query.pair hg p.1 p'.1 p.2 p'.2 (hmid u e1) (hmid v e2)).2

/-- Lists with the same members under an injection: a permutation of the indices matches them. -/
theorem exists_index_perm {l l' : List V} {φ : V → V} (hφ : Function.Injective φ) (hn : l.Nodup)
    (hn' : l'.Nodup) (hm : ∀ w, w ∈ l ↔ φ w ∈ l') (hsurj : ∀ y ∈ l', ∃ w, φ w = y)
    (hD : l.length ≤ D) : ∃ τ : Perm (Fin D), ∀ i : Fin D, l'[(τ i : ℕ)]? = l[(i : ℕ)]?.map φ := by
  classical
  have hnm : (l.map φ).Nodup := hn.map hφ
  have hperm : (l.map φ).Perm l' := (List.perm_ext_iff_of_nodup hnm hn').2 fun y => by
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
      exact (hm w).1 hw
    · intro hy
      obtain ⟨w, rfl⟩ := hsurj y hy
      exact List.mem_map.2 ⟨w, (hm w).2 hy, rfl⟩
  have hlen : l.length = l'.length := by simpa using hperm.length_eq
  set p : Fin D → Prop := fun i => (i : ℕ) < l.length with hp
  let pt : {i // p i} → V := fun i => φ (l.get ⟨((i.1 : Fin D) : ℕ), i.2⟩)
  have hmem : ∀ i, pt i ∈ l' := fun i => (hm _).1 (List.get_mem _ _)
  have hidx : ∀ i, l'.idxOf (pt i) < l.length := fun i => by
    rw [hlen]
    exact List.idxOf_lt_length_iff.2 (hmem i)
  let σ : {i // p i} → {i // p i} := fun i =>
    ⟨⟨l'.idxOf (pt i), by have := hidx i; omega⟩, hidx i⟩
  have hσ : Function.Injective σ := by
    intro i j hij
    have h1 : l'.idxOf (pt i) = l'.idxOf (pt j) := congrArg (fun x => ((x.1 : Fin D) : ℕ)) hij
    have h2 := (List.idxOf_inj (hmem i)).1 h1
    have h3 := hφ h2
    have h4 := hn.get_inj_iff.1 h3
    exact Subtype.ext (Fin.ext (Fin.mk.inj_iff.1 h4))
  let e : {i // p i} ≃ {i // p i} := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  by_cases hi : p i
  · have h1 : ((e.extendSubtype i : Fin D) : ℕ) = l'.idxOf (pt ⟨i, hi⟩) := by
      rw [Equiv.extendSubtype_apply_of_mem _ _ hi]
      rfl
    rw [h1]
    have h2 : l'.idxOf (pt ⟨i, hi⟩) < l'.length := List.idxOf_lt_length_iff.2 (hmem _)
    rw [List.getElem?_eq_getElem h2, List.getElem_idxOf h2]
    have hi' : (i : ℕ) < l.length := hi
    rw [List.getElem?_eq_getElem hi']
    rfl
  · have h1 := e.extendSubtype_not_mem i hi
    have h2 : l.length ≤ (i : ℕ) := not_lt.1 hi
    have h3 : l'.length ≤ (e.extendSubtype i : ℕ) := by
      have : ¬ ((e.extendSubtype i : Fin D) : ℕ) < l.length := h1
      omega
    rw [List.getElem?_eq_none h3, List.getElem?_eq_none h2]
    rfl

/-- **Lemma 9.2(b).** -/
theorem query_lift (fXok : FwdOK ℓ X fX) (fYok : FwdOK ℓ Y fY) (hDX : ∀ u, (fX u).length ≤ D)
    (hpar : ParOK ℓ r fX par) (h1 : 1 ∈ Ball ℓ r X Y) {h : Perm V}
    (hh : h ∈ Ball ℓ (r + 1) X Y) :
    ∃ g ∈ Query D ℓ r X Y fX fY, ∀ u, decMap ℓ r fY par z g u = h u := by
  classical
  obtain ⟨h1', h2', h3'⟩ := id hh
  set a := ballCut ℓ r h h1' with ha
  have hab : a ∈ Ball ℓ r X Y := Ball.cut hh
  have haG : a ∈ ballGroup ℓ r X := by simpa using Ball.inv_mul h1 hab
  have ha_eq : ∀ u, ℓ u ≤ r → a u = h u := fun u hu => ballCut_apply_of_le h1' hu
  have hmem : ∀ u, ℓ u = r → ∀ w, w ∈ fX u ↔ h w ∈ fY (a u) := by
    intro u hu w
    rw [fXok.mem, fYok.mem, ha_eq u (by omega), h1', h1']
    constructor
    · rintro ⟨e1, e2⟩
      exact ⟨(h3' u w (by omega) (by omega)).1 e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact ⟨(h3' u w (by omega) (by omega)).2 e1, e2⟩
  have hex : ∀ u, ∃ τ : Perm (Fin D), ℓ u = r → ∀ i : Fin D,
      (fY (a u))[(τ i : ℕ)]? = (fX u)[(i : ℕ)]?.map h := by
    intro u
    by_cases hu : ℓ u = r
    · obtain ⟨τ, hτ⟩ := exists_index_perm h.injective (fXok.nodup u) (fYok.nodup (a u))
        (hmem u hu) (fun y _ => ⟨h⁻¹ y, by simp⟩) (hDX u)
      exact ⟨τ, fun _ => hτ⟩
    · exact ⟨1, fun hu' => absurd hu' hu⟩
  choose τ hτ using hex
  set g : Perm (V × Fin D) := Equiv.prodShear a τ with hg
  have hgs : ∀ s, g s = (a s.1, τ s.1 s.2) := fun s => rfl
  have hgt : ∀ s, ℓ s.1 = r → tgt fY (g s) = (tgt fX s).map h := by
    intro s hs
    rw [hgs]
    exact hτ _ hs _
  have hglev : ∀ s : V × Fin D, ℓ (g s).1 = ℓ s.1 := fun s => by rw [hgs]; exact hab.1 _
  refine ⟨g, ⟨⟨a, haG, fun s => rfl⟩, fun s s' => ?_⟩, fun u => ?_⟩
  · by_cases hc : ℓ s.1 = r ∧ ℓ s'.1 = r
    · obtain ⟨c1, c2⟩ := hc
      rcases e1 : tgt fX s with _ | w
      · have e2 := hgt s c1
        rw [e1, Option.map_none] at e2
        rw [slotColor_none' ((hglev s).trans c1) ((hglev s').trans c2) (Or.inl e2),
          slotColor_none' c1 c2 (Or.inl e1)]
      · have e2 := hgt s c1
        rw [e1, Option.map_some] at e2
        rcases e1' : tgt fX s' with _ | w'
        · have e2' := hgt s' c2
          rw [e1', Option.map_none] at e2'
          rw [slotColor_none' ((hglev s).trans c1) ((hglev s').trans c2) (Or.inr e2'),
            slotColor_none' c1 c2 (Or.inr e1')]
        · have e2' := hgt s' c2
          rw [e1', Option.map_some] at e2'
          rw [slotColor_some c1 c2 e1 e1', slotColor_some ((hglev s).trans c1)
            ((hglev s').trans c2) e2 e2']
          have ll : ℓ w = r + 1 := by
            rw [((fXok.mem _ _).1 (mem_of_tgt e1)).2, c1]
          have ll' : ℓ w' = r + 1 := by
            rw [((fXok.mem _ _).1 (mem_of_tgt e1')).2, c2]
          have q1 : h w = h w' ↔ w = w' := h.injective.eq_iff
          have q2 : Y.Adj (h w) (h w') ↔ X.Adj w w' := (h3' w w' (by omega) (by omega)).symm
          split_ifs <;> first | rfl | (exfalso; tauto)
    · simp only [slotColor, hglev, if_neg hc]
  · simp only [decMap]
    split_ifs with c1 c2
    · exact ha_eq u c1
    · obtain ⟨p1, p2⟩ := hpar u c2
      rw [hgt _ p1, p2]
      rfl
    · exact (h2' u (by omega)).symm

/-- **Lemma 9.2(c).** On `Query` for `Y = X`, the map `dec` is multiplicative. -/
theorem query_dec_mul (hpar : ParOK ℓ r fX par) (fXok : FwdOK ℓ X fX)
    {f f' : Perm (V × Fin D)} (hf : f ∈ Query D ℓ r X X fX fX) (hf' : f' ∈ Query D ℓ r X X fX fX)
    (u : V) :
    decMap ℓ r fX par z (f * f') u = decMap ℓ r fX par z f (decMap ℓ r fX par z f' u) := by
  obtain ⟨a, ha, hfst⟩ := hf.1
  obtain ⟨a', ha', hfst'⟩ := hf'.1
  have hl' : ∀ u, ℓ (a' u) = ℓ u := ha'.1
  rcases lt_trichotomy (ℓ u) (r + 1) with h | h | h
  · have e1 : decMap ℓ r fX par z f' u = a' u := by
      simp only [decMap, show ℓ u ≤ r by omega, if_true]
      exact hfst' _
    rw [e1]
    simp only [decMap, hl', show ℓ u ≤ r by omega, if_true, Perm.mul_apply]
    rw [hfst, hfst', hfst]
  · obtain ⟨p1, p2⟩ := hpar u h
    obtain ⟨y, hy⟩ := Query.tgt_some hf' p1 p2
    have e1 : decMap ℓ r fX par z f' u = y := by
      simp only [decMap]
      rw [if_neg (by omega), if_pos h, hy]
      rfl
    have hyl : ℓ y = r + 1 := by
      have := ((fXok.mem _ _).1 (mem_of_tgt hy)).2
      rw [this, Query.level hf', p1]
    obtain ⟨q1, q2⟩ := hpar y hyl
    have hs : ℓ (f' (par u)).1 = r := (Query.level hf' _).trans p1
    obtain ⟨z1, hz1⟩ := Query.tgt_some hf hs hy
    obtain ⟨z2, hz2⟩ := Query.tgt_some hf q1 q2
    have hzz := (Query.pair hf hs q1 hy q2 hz1 hz2).1.1 rfl
    rw [e1]
    simp only [decMap]
    rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos hyl, Perm.mul_apply, hz1, hz2, hzz]
    rfl
  · have e1 : decMap ℓ r fX par z f' u = u := by
      simp only [decMap]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e1]
    simp only [decMap, if_neg (show ¬ ℓ u ≤ r by omega), if_neg (show ¬ ℓ u = r + 1 by omega)]

end Dec

end GI.Degree
