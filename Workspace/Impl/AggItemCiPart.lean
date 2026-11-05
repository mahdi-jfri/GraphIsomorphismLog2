module

public import Workspace.Impl.AggItemC1Sch

@[expose] public section

/-!
# The overcoset item of a colored partition given by a coloring

The configuration branch has the item `objItem zX zY` (`Workspace/Algorithm/AuxPartitions.lean`)
for three kinds of colored partitions: the vertex-class partition of Case 3(a)
(`classPart`, blocks = color classes), the balanced partition at a source vertex (`balPart`,
singleton blocks) and the imprimitive partition (`impPart`). For the first two, whether a
permutation maps the source object to the target object depends only on one coloring of each
side: `σ • zX = zY` exactly when `fY (σ a) = fX a` for all points `a`. This file computes the
item from the two colorings, as the program does.

1. **Alignment.** Order the points by (color, point) and let `itciPos f a` be the number of
   points before `a`. If the two colorings have the same number of points of each color, the
   permutation `itciAl fX fY` that matches equal positions maps `fX` to `fY`
   (`itci_al_apply`). If some permutation maps `fX` to `fY`, the counts agree
   (`itci_cnt_of_map`).
2. **The stabilizer.** The transpositions of each point with the least point of its color class
   (`itciT`) generate the permutations that keep `f` (`itci_closure`, from `itp_mem_of_lab`).
3. **The even part.** If some class has two points, one such transposition `t` is odd, and the
   Schreier list of `t` (`itSchE`) generates the even part (`itp_schreier`). Otherwise `f` is
   injective and the stabilizer is trivial.
4. **The item** (`itci_item`): the program's list `itciOs` stands for the script of `objItem`.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm Finset
open GI.Cited (gens)

variable {q : ℕ}

/-! ### Positions in the order by color and point -/

section Pos

variable (f : Fin q → ℕ)

/-- The number of points before `a` in the order by (color, point). -/
def itciPos (a : Fin q) : ℕ :=
  (univ.filter fun y => f y < f a ∨ (f y = f a ∧ y < a)).card

variable {f}

theorem itci_lt_trans {a b c : Fin q} (h1 : f a < f b ∨ (f a = f b ∧ a < b))
    (h2 : f b < f c ∨ (f b = f c ∧ b < c)) : f a < f c ∨ (f a = f c ∧ a < c) := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

theorem itciPos_lt_of {a b : Fin q} (h : f a < f b ∨ (f a = f b ∧ a < b)) :
    itciPos f a < itciPos f b := by
  refine card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact itci_lt_trans hy h
  · have := hsub (show a ∈ univ.filter fun y => f y < f b ∨ (f y = f b ∧ y < b) by simpa using h)
    simp at this

theorem itciPos_injective : Function.Injective (itciPos f) := by
  intro a b hab
  by_contra hne
  rcases lt_trichotomy (f a) (f b) with h | h | h
  · exact absurd hab (itciPos_lt_of (Or.inl h)).ne
  · rcases lt_or_gt_of_ne hne with h' | h'
    · exact absurd hab (itciPos_lt_of (Or.inr ⟨h, h'⟩)).ne
    · exact absurd hab.symm (itciPos_lt_of (Or.inr ⟨h.symm, h'⟩)).ne
  · exact absurd hab.symm (itciPos_lt_of (Or.inl h)).ne

theorem itciPos_lt (a : Fin q) : itciPos f a < q := by
  have h : (univ.filter fun y => f y < f a ∨ (f y = f a ∧ y < a)) ⊆ univ.erase a := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    refine mem_erase.2 ⟨fun e => ?_, mem_univ _⟩
    subst e
    rcases hy with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
  have h2 := card_le_card h
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
  have := a.isLt
  unfold itciPos; omega

variable (f) in
/-- The positions as a permutation. -/
noncomputable def itciPosE : Perm (Fin q) :=
  Equiv.ofBijective (fun a => ⟨itciPos f a, itciPos_lt a⟩)
    (Finite.injective_iff_bijective.1 fun a b h => itciPos_injective (Fin.ext_iff.1 h))

@[simp] theorem itciPosE_val (a : Fin q) : (itciPosE f a : ℕ) = itciPos f a := rfl

/-- The points of a smaller color, then the earlier points of the same color. -/
theorem itciPos_eq (a : Fin q) :
    itciPos f a = (univ.filter fun y => f y < f a).card +
      (univ.filter fun y => f y = f a ∧ y < a).card := by
  unfold itciPos
  rw [filter_or, card_union_of_disjoint]
  rw [disjoint_filter]
  intro y _ h1 h2
  omega

theorem itci_rk_lt (a : Fin q) :
    (univ.filter fun y => f y = f a ∧ y < a).card < (univ.filter fun y => f y = f a).card := by
  refine card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hy ⊢; exact hy.1
  · have := hsub (show a ∈ univ.filter fun y => f y = f a by simp)
    simp at this

/-- A smaller color class and its points come before a larger color. -/
theorem itci_lt_add {u w : ℕ} (h : u < w) :
    (univ.filter fun y : Fin q => f y < u).card + (univ.filter fun y => f y = u).card ≤
      (univ.filter fun y => f y < w).card := by
  rw [← card_union_of_disjoint]
  · refine card_le_card fun y hy => ?_
    simp only [mem_union, mem_filter, mem_univ, true_and] at hy ⊢
    omega
  · rw [disjoint_filter]; intro y _ h1 h2; omega

/-- The number of points of color below `v`, as a sum of class sizes. -/
theorem itci_cnt_lt_sum (v : ℕ) :
    (univ.filter fun y => f y < v).card =
      ∑ u ∈ range v, (univ.filter fun y => f y = u).card := by
  rw [card_eq_sum_card_fiberwise (f := f) (s := univ.filter fun y => f y < v) (t := range v)
    (fun y hy => mem_range.2 (mem_filter.1 hy).2)]
  refine sum_congr rfl fun u hu => ?_
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  intro e; rw [e]; exact mem_range.1 hu

end Pos

/-! ### The aligning permutation -/

section Align

variable {fX fY : Fin q → ℕ}

/-- The colorings have the same number of points of each color. -/
def ItciCnt (fX fY : Fin q → ℕ) : Prop :=
  ∀ v, (univ.filter fun y => fX y = v).card = (univ.filter fun y => fY y = v).card

theorem ItciCnt.symm (h : ItciCnt fX fY) : ItciCnt fY fX := fun v => (h v).symm

theorem ItciCnt.lt (h : ItciCnt fX fY) (v : ℕ) :
    (univ.filter fun y => fX y < v).card = (univ.filter fun y => fY y < v).card := by
  rw [itci_cnt_lt_sum, itci_cnt_lt_sum]
  exact sum_congr rfl fun u _ => h u

variable (fX fY) in
/-- **The aligning permutation**: `a` goes to the point of the same position. -/
noncomputable def itciAl : Perm (Fin q) := (itciPosE fY)⁻¹ * itciPosE fX

theorem itciPos_al (a : Fin q) : itciPos fY (itciAl fX fY a) = itciPos fX a := by
  rw [← itciPosE_val, ← itciPosE_val, itciAl, Perm.mul_apply, Perm.apply_inv_self]

/-- One direction of the alignment: equal positions do not allow a smaller source color. -/
theorem itci_not_lt (h : ItciCnt fX fY) {a b : Fin q} (hp : itciPos fY b = itciPos fX a) :
    ¬ fX a < fY b := by
  intro hl
  have h1 := itciPos_eq (f := fX) a
  have h2 := itci_rk_lt (f := fX) a
  have h3 := itci_lt_add (f := fX) hl
  have h4 := itciPos_eq (f := fY) b
  rw [h.lt (fY b)] at h3
  omega

/-- **The aligning permutation maps `fX` to `fY`** when the counts agree. -/
theorem itci_al_apply (h : ItciCnt fX fY) (a : Fin q) : fY (itciAl fX fY a) = fX a := by
  have hp := itciPos_al (fX := fX) (fY := fY) a
  rcases lt_trichotomy (fX a) (fY (itciAl fX fY a)) with hl | he | hl
  · exact absurd hl (itci_not_lt h hp)
  · exact he.symm
  · have hp' : itciPos fX (itciAl fY fX (itciAl fX fY a)) = itciPos fY (itciAl fX fY a) :=
      itciPos_al _
    -- the inverse alignment brings the point back to `a`
    have hinv : itciAl fY fX (itciAl fX fY a) = a := by
      simp only [itciAl, Perm.mul_apply, Perm.apply_inv_self, Perm.inv_apply_self]
    rw [hinv] at hp'
    exact absurd hl (itci_not_lt h.symm hp')

/-- **A permutation that maps `fX` to `fY` forces equal counts.** -/
theorem itci_cnt_of_map {σ : Perm (Fin q)} (h : ∀ a, fY (σ a) = fX a) : ItciCnt fX fY := by
  intro v
  have e : (univ.filter fun y => fY y = v) = (univ.filter fun a => fX a = v).map σ.toEmbedding := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_map_equiv]
    rw [← h (σ.symm y), Equiv.apply_symm_apply]
  rw [e, card_map]

end Align

/-! ### The stabilizer of a coloring -/

section Stab

variable (f : Fin q → ℕ)

/-- The least point of the color class of `a`. -/
def itciC (a : Fin q) : Fin q := (univ.filter fun y => f y = f a).min' ⟨a, by simp⟩

variable {f}

theorem itciC_f (a : Fin q) : f (itciC f a) = f a := by
  have := min'_mem (univ.filter fun y => f y = f a) ⟨a, by simp⟩
  simpa [itciC] using this

theorem itciC_le {a y : Fin q} (h : f a = f y) : itciC f a ≤ y :=
  min'_le _ _ (by simp [h])

variable (f) in
/-- The centers as numbers. -/
def itciCN (a : Fin q) : ℕ := itciC f a

theorem itcC_itciCN (x : Fin q) : itcC (itciCN f) x = itciC f x := by
  simp [itcC, itciCN, (itciC f x).isLt]

variable (f) in
/-- **The transpositions of each point with its center**, as the program lists them. -/
def itciT : List (Perm (Fin q)) := (List.range q).map (itcTrN (itciCN f))

theorem itciT_length : (itciT f).length = q := by simp [itciT]

theorem itciT_mem_self (a : Fin q) : Equiv.swap (itciC f a) a ∈ itciT f := by
  refine List.mem_map.2 ⟨a, List.mem_range.2 a.isLt, ?_⟩
  simp [itcTrN, a.isLt, itcC_itciCN]

theorem itciT_keep {g : Perm (Fin q)} (hg : g ∈ itciT f) (z : Fin q) : f (g z) = f z := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
  unfold itcTrN
  split_ifs with h
  · rw [itcC_itciCN]; exact itp_swap_lab (itciC_f _) z
  · rfl

/-- **The transpositions generate the permutations that keep the coloring.** -/
theorem itci_mem_closure {σ : Perm (Fin q)} (hσ : ∀ z, f (σ z) = f z) :
    σ ∈ gens (itciT f) :=
  itp_mem_of_lab (lab := f) (c := itciC f) itciC_f (fun _ _ h => itciC_le h)
    (S := {g | g ∈ itciT f}) (fun x => itciT_mem_self x) _ σ hσ le_rfl

theorem itci_keep_of_mem {σ : Perm (Fin q)} (hσ : σ ∈ gens (itciT f)) (z : Fin q) :
    f (σ z) = f z := by
  refine Subgroup.closure_induction (p := fun g _ => ∀ z, f (g z) = f z)
    (fun g hg z => itciT_keep hg z) (fun _ => rfl)
    (fun g h _ _ hg hh z => by rw [Perm.mul_apply, hg, hh]) (fun g _ hg z => ?_) hσ z
  have := hg (g⁻¹ z)
  rw [Perm.apply_inv_self] at this
  exact this.symm

/-- If no class has two points, the coloring is injective. -/
theorem itci_inj_of_c (h : ∀ a, itciC f a = a) : Function.Injective f := by
  intro a b hab
  have h1 := itciC_le (f := f) hab
  have h2 := itciC_le (f := f) hab.symm
  rw [h a] at h1; rw [h b] at h2
  exact le_antisymm h1 h2

/-- A permutation that keeps an injective coloring is the identity. -/
theorem itci_eq_one {σ : Perm (Fin q)} (hinj : Function.Injective f) (hσ : ∀ z, f (σ z) = f z) :
    σ = 1 := Equiv.ext fun z => hinj (hσ z)

end Stab

/-! ### The even part -/

section Even

variable {f : Fin q → ℕ}

/-- The transposition of `a` with its center. -/
def itciTr (f : Fin q → ℕ) (a : Fin q) : Perm (Fin q) := Equiv.swap (itciC f a) a

/-- The program's generators of the even part: the Schreier list of the transposition at `a`
when `a` is not its center, none when every point is its own center. -/
noncomputable def itciMs (f : Fin q → ℕ) : Option (Fin q) → List (Perm (Fin q))
  | some a => (List.range (2 * (itciT f).length)).map (itSchE (itciTr f a) (itciT f))
  | none => []

/-- **The program's list generates the even part of the stabilizer.** -/
theorem itciMs_gens {ot : Option (Fin q)}
    (hot : (ot = none → ∀ a, itciC f a = a) ∧ ∀ a, ot = some a → itciC f a ≠ a) :
    gens (itciMs f ot) = gens (itciT f) ⊓ alternatingGroup (Fin q) := by
  cases ot with
  | none =>
    have hinj := itci_inj_of_c (hot.1 rfl)
    refine le_antisymm (by simp [itciMs, gens]) fun σ ⟨hσ, _⟩ => ?_
    rw [itci_eq_one hinj (itci_keep_of_mem hσ)]
    exact Subgroup.one_mem _
  | some a =>
    have ha := hot.2 a rfl
    rw [itciMs, itSchE_gens]
    exact itp_schreier (Subgroup.subset_closure (itciT_mem_self a)) (Equiv.swap_mul_self _ _)
      (Perm.sign_swap ha)

end Even

/-! ### The overcosets -/

section Item

open Classical in
/-- **The program's overcosets of the item**: if the alignment maps `fX` to `fY`, one overcoset
with the alignment (times the transposition at the found point `a` if the alignment is odd);
with no found point, the alignment if it is even; else none. -/
noncomputable def itciOs (fX fY : Fin q → ℕ) (ot : Option (Fin q))
    (E₀ : Subgroup (alternatingGroup (Fin q))) : List (LcOver q) :=
  if ∀ a, fY (itciAl fX fY a) = fX a then
    match ot with
    | some a =>
      if hs : sign (itciAl fX fY) = 1 then [(⟨itciAl fX fY, hs⟩, E₀, itciMs fX (some a))]
      else if hs' : sign (itciAl fX fY * itciTr fX a) = 1 then
        [(⟨itciAl fX fY * itciTr fX a, hs'⟩, E₀, itciMs fX (some a))]
      else []
    | none =>
      if hs : sign (itciAl fX fY) = 1 then [(⟨itciAl fX fY, hs⟩, E₀, [])] else []
  else []

/-- Every entry of the list has the group `E₀` and the program's generators. -/
theorem itciOs_snd {fX fY : Fin q → ℕ} {ot : Option (Fin q)}
    {E₀ : Subgroup (alternatingGroup (Fin q))} {o : LcOver q} (ho : o ∈ itciOs fX fY ot E₀) :
    o.2.1 = E₀ ∧ o.2.2 = itciMs fX ot := by
  classical
  cases ot <;> simp only [itciOs] at ho <;> split_ifs at ho <;>
    simp only [List.mem_singleton, List.not_mem_nil] at ho <;> subst ho <;> exact ⟨rfl, rfl⟩

variable {Ω C : Type} {P : Params} {S : State Ω C}

/-- A representative that maps the object stands for the overcoset of `objItem`. -/
theorem itci_ovAt (L : GiantLabels S) {Z : Type*} [MulAction (Perm (Fin L.q)) Z] {zX zY : Z}
    (h : ∃ σ : alternatingGroup (Fin L.q), (σ : Perm (Fin L.q)) • zX = zY)
    {σ' : alternatingGroup (Fin L.q)} (h' : (σ' : Perm (Fin L.q)) • zX = zY)
    (ms : List (Perm (Fin L.q))) :
    asOvAt L (σ', evenStab (q := L.q) zX, ms)
      (AuxItem.liftOver L (evenStab (q := L.q) zX) h.choose) := by
  refine it_ovAt_of_mem L ?_ ms
  show ((h.choose⁻¹ * σ' : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
    MulAction.stabilizer (Perm (Fin L.q)) zX
  rw [MulAction.mem_stabilizer_iff, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h',
    inv_smul_eq_iff]
  exact h.choose_spec.symm

/-- **The overcoset item of a colored partition given by colorings, as the program computes
it.** The hypotheses say that `σ` maps `zX` to `zY` exactly when it maps `fX` to `fY`, and fixes
`zX` exactly when it keeps `fX`; `ot` is a point that is not its center, if there is one. Then the
script of `objItem zX zY` returns no piece and overcosets for which `itciOs` stands, and each
group of the list is generated by its generators. -/
theorem itci_item (L : GiantLabels S) {Z : Type*} [MulAction (Perm (Fin L.q)) Z] (zX zY : Z)
    {fX fY : Fin L.q → ℕ} (hT : ∀ σ : Perm (Fin L.q), σ • zX = zY ↔ ∀ a, fY (σ a) = fX a)
    (hS : ∀ σ : Perm (Fin L.q), σ • zX = zX ↔ ∀ a, fX (σ a) = fX a) {ot : Option (Fin L.q)}
    (hot : (ot = none → ∀ a, itciC fX a = a) ∧ ∀ a, ot = some a → itciC fX a ≠ a) :
    ∃ ovs, (objItem (P := P) zX zY : AuxItem P S L).script = Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L) (itciOs fX fY ot (evenStab (q := L.q) zX)) ovs ∧
      ∀ o ∈ itciOs fX fY ot (evenStab (q := L.q) zX),
        gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
  classical
  -- the even stabilizer, as a group of permutations
  have hE : (evenStab (q := L.q) zX).map (alternatingGroup (Fin L.q)).subtype =
      gens (itciT fX) ⊓ alternatingGroup (Fin L.q) := by
    rw [itp_evenStab_map]
    congr 1
    ext σ
    rw [MulAction.mem_stabilizer_iff, hS]
    exact ⟨itci_mem_closure, fun h => itci_keep_of_mem h⟩
  have hgens : ∀ o ∈ itciOs fX fY ot (evenStab (q := L.q) zX),
      gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
    intro o ho
    obtain ⟨h1, h2⟩ := itciOs_snd ho
    rw [h1, h2, hE]
    exact itciMs_gens hot
  -- the even aligner of the program maps `zX` to `zY`
  have hal : ∀ (hc : ∀ a, fY (itciAl fX fY a) = fX a) (a : Fin L.q),
      (itciAl fX fY * itciTr fX a) • zX = zY := by
    intro hc a
    rw [hT]
    intro z
    rw [Perm.mul_apply, hc, itciTr]
    exact itp_swap_lab (itciC_f a) z
  unfold objItem
  split_ifs with hex
  · obtain ⟨σ, hσ⟩ := hex
    have hc : ∀ a, fY (itciAl fX fY a) = fX a :=
      itci_al_apply (itci_cnt_of_map ((hT σ).1 hσ))
    have hal0 : (itciAl fX fY) • zX = zY := (hT _).2 hc
    refine ⟨_, rfl, ?_, hgens⟩
    simp only [itciOs, if_pos hc]
    cases ot with
    | some a =>
      simp only
      have ha := hot.2 a rfl
      split_ifs with hs hs'
      · exact List.Forall₂.cons (itci_ovAt L ⟨σ, hσ⟩ hal0 _) List.Forall₂.nil
      · exact List.Forall₂.cons (itci_ovAt L ⟨σ, hσ⟩ (hal hc a) _) List.Forall₂.nil
      · exact absurd (by rw [Perm.sign_mul, (itp_sign_cases _).resolve_left hs, itciTr,
          Perm.sign_swap ha]; decide) hs'
    | none =>
      simp only
      -- every aligner is the alignment, since the stabilizer is trivial
      have hinj := itci_inj_of_c (hot.1 rfl)
      have he : (σ : Perm (Fin L.q)) = itciAl fX fY := by
        have h1 : (itciAl fX fY)⁻¹ * (σ : Perm (Fin L.q)) = 1 := by
          refine itci_eq_one hinj fun z => ?_
          have h2 := hc ((itciAl fX fY)⁻¹ ((σ : Perm (Fin L.q)) z))
          rw [Perm.apply_inv_self] at h2
          rw [Perm.mul_apply, ← h2]
          exact (hT _).1 hσ z
        rw [← mul_inv_cancel_left (itciAl fX fY) (σ : Perm (Fin L.q)), h1, mul_one]
      have hs : sign (itciAl fX fY) = 1 := he ▸ σ.2
      rw [dif_pos hs]
      exact List.Forall₂.cons (itci_ovAt L ⟨σ, hσ⟩ hal0 _) List.Forall₂.nil
  · refine ⟨[], rfl, ?_, hgens⟩
    cases ot with
    | some a =>
      simp only [itciOs]
      split_ifs with hc hs hs'
      · exact absurd ⟨⟨_, hs⟩, (hT _).2 hc⟩ hex
      · exact absurd ⟨⟨_, hs'⟩, hal hc a⟩ hex
      · exact List.Forall₂.nil
      · exact List.Forall₂.nil
    | none =>
      simp only [itciOs]
      split_ifs with hc hs
      · exact absurd ⟨⟨_, hs⟩, (hT _).2 hc⟩ hex
      · exact List.Forall₂.nil
      · exact List.Forall₂.nil

/-- **The vertex-class partition** (Case 3(a)) is given by its coloring. -/
theorem itci_classPart_iff (σ : Perm (Fin q)) (fX fY : Fin q → ℕ) :
    σ • classPart fX = classPart fY ↔ ∀ a, fY (σ a) = fX a := by
  rw [classPart_smul]
  constructor
  · intro h a
    have := congrFun (congrArg ColPart.col h) (σ a)
    simp only [classPart, Perm.inv_apply_self] at this
    exact this.symm
  · intro h
    have e : (fun a => fX (σ⁻¹ a)) = fY := funext fun a => by
      rw [← h (σ⁻¹ a), Perm.apply_inv_self]
    rw [e]

end Item

end GI.Impl
