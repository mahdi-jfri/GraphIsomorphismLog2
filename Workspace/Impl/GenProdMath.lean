import Workspace.Impl.GenCosetsMath
import Workspace.Impl.Canon
import Mathlib.Data.Nat.Digits.Defs

/-!
# The product refinement: the mathematics

Algorithm 5: "if … a product refinement applies then apply that reduction and solve its
children with `Continue`". The quotient `Q` has a product structure `E : Fin d ≃ (Fin r → KSet m
l)` with `r ≥ 2` coordinates. The children run under the coordinate group `K`, the elements of
`G` whose block action fixes every coordinate (`PrimitiveQuotient.coordinateGroup`). A program
must compute generators of `K`, one element of `G` in each coset of `K`, and the split
hierarchy.

**The idea.** For two positions `v, w` and a coordinate `i < r`, the bit `pbit i v w` says
whether `v` and `w` agree in coordinate `i` (both in the domain with equal coordinate `i` of
their blocks, or both off the domain); the bit `pbit r v w` says whether both or neither lie in
the domain. An element `g` of `G` permutes the coordinates by some `σ`, so it permutes these
bits (`pbit_smul`). The mask `pmask v w` packs the bits into one number (binary digits). So:

* `g` keeps every mask exactly when `σ = 1`, that is, when `g ∈ K` (`pmask_stab_iff`);
* the relation "equal masks" on pairs of positions is kept by `G` (`pmask_smul_iff`), and its
  kernel is `K`; the kernel program (cited `Preimage`) computes it on the pairs;
* the masks, as a labeling of the pairs, have stabilizer `K` under the action of `G` on pairs, so
  the orbit program with a transversal gives coset representatives of `K`
  (`cosetList_of_stab`); the orbit has at most `r!` points (`ncard_orbit_mask_le`).

The pairs `(p, q)` of points of `Fin k` are the points of `Fin (k * k)` (`finProdFinEquiv`), and
`g` acts on them by `sqPerm g = g × g`.

The coordinate partitions of the split hierarchy (`coordPart s`: agreement in all coordinates
`j ≥ s`) are read from the number `plead v w` of leading bits `r, r - 1, …` that are `1`
(`coordPart_iff_plead`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open scoped Pointwise

/-! ### Horner sums and leading ones -/

/-- The Horner sum of the bits `b r, b (r - 1), …`: after `t` steps it is the number with binary
digits `b (r + 1 - t), …, b r` (lowest first). -/
def hornerN (b : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => 2 * hornerN b r t + b (r - t)

/-- The number of leading ones among the bits `b r, b (r - 1), …`, after `t` steps. -/
def leadN (b : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if leadN b r t = t ∧ b (r - t) = 1 then t + 1 else leadN b r t

theorem hornerN_eq (b : ℕ → ℕ) (r : ℕ) {t : ℕ} (ht : t ≤ r + 1) :
    hornerN b r t = Nat.ofDigits 2 ((List.range t).map fun j => b (r + 1 - t + j)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [hornerN, ih (by omega), List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.ofDigits_cons]
    have h1 : r + 1 - (t + 1) + 0 = r - t := by omega
    have h2 : ((fun j => b (r + 1 - (t + 1) + j)) ∘ Nat.succ) = fun j => b (r + 1 - t + j) := by
      funext j; simp only [Function.comp_apply]; congr 1; omega
    rw [h1, h2]
    ring

theorem hornerN_full (b : ℕ → ℕ) (r : ℕ) :
    hornerN b r (r + 1) = Nat.ofDigits 2 ((List.range (r + 1)).map b) := by
  rw [hornerN_eq b r le_rfl]
  simp

theorem leadN_le (b : ℕ → ℕ) (r : ℕ) (t : ℕ) : leadN b r t ≤ t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => rw [leadN]; split_ifs <;> omega

/-- **Leading ones.** For `n ≤ t`, at least `n` leading bits are counted after `t` steps exactly
when the bits `b r, …, b (r + 1 - n)` are `1`. -/
theorem le_leadN_iff (b : ℕ → ℕ) (r : ℕ) {t n : ℕ} (hn : n ≤ t) :
    n ≤ leadN b r t ↔ ∀ u < n, b (r - u) = 1 := by
  induction t generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this; simp [leadN]
  | succ t ih =>
    rw [leadN]
    by_cases hc : leadN b r t = t ∧ b (r - t) = 1
    · rw [if_pos hc]
      have hall : ∀ u < t + 1, b (r - u) = 1 := by
        intro u hu
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · exact (ih le_rfl).1 hc.1.ge u hu
        · exact hc.2
      exact ⟨fun _ u hu => hall u (by omega), fun _ => hn⟩
    · rw [if_neg hc]
      rcases Nat.lt_or_ge n (t + 1) with hlt | hge
      · exact ih (by omega)
      · have hnt : n = t + 1 := by omega
        subst hnt
        refine ⟨fun h => absurd h (by have := leadN_le b r t; omega), fun h => ?_⟩
        exact absurd ⟨le_antisymm (leadN_le b r t) ((ih le_rfl).2 fun u hu => h u (by omega)),
          h t (by omega)⟩ hc

/-- Equal Horner sums of bit sequences have equal bits. -/
theorem bits_eq_of_hornerN {b b' : ℕ → ℕ} {r : ℕ} (hb : ∀ i ≤ r, b i ≤ 1)
    (hb' : ∀ i ≤ r, b' i ≤ 1) (h : hornerN b r (r + 1) = hornerN b' r (r + 1)) :
    ∀ i ≤ r, b i = b' i := by
  rw [hornerN_full, hornerN_full] at h
  have := Nat.ofDigits_inj_of_len_eq (b := 2) (by norm_num) (by simp)
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have := hb i (by simp at hi; omega); omega)
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have := hb' i (by simp at hi; omega); omega) h
  intro i hi
  have := congrArg (fun l => l[i]?) this
  simpa [List.getElem?_map, List.getElem?_range (show i < r + 1 by omega)] using this

/-- The Horner sum is below `2 ^ (r + 1)` for bits `0, 1`. -/
theorem hornerN_lt {b : ℕ → ℕ} {r : ℕ} (hb : ∀ i ≤ r, b i ≤ 1) :
    hornerN b r (r + 1) < 2 ^ (r + 1) := by
  have key : ∀ t ≤ r + 1, hornerN b r t < 2 ^ t := by
    intro t ht
    induction t with
    | zero => simp [hornerN]
    | succ t ih =>
      rw [hornerN, pow_succ]
      have := ih (by omega)
      have := hb (r - t) (by omega)
      omega
  exact key _ le_rfl

/-! ### The square action on pairs -/

variable {k : ℕ}

/-- `g × g` on the pairs of points, as a permutation of `Fin (k * k)`. -/
def sqPerm (g : Perm (Fin k)) : Perm (Fin (k * k)) :=
  (finProdFinEquiv.symm.trans (Equiv.prodCongr g g)).trans finProdFinEquiv

/-- `g ↦ g × g` is a homomorphism. -/
def sqHom : Perm (Fin k) →* Perm (Fin (k * k)) where
  toFun := sqPerm
  map_one' := by ext j; simp [sqPerm, Nat.mod_add_div]
  map_mul' g h := by ext j; simp [sqPerm]

theorem sqHom_apply (g : Perm (Fin k)) : sqHom g = sqPerm g := rfl

theorem sqPerm_val (g : Perm (Fin k)) (j : Fin (k * k)) :
    (sqPerm g j : ℕ) = g (finProdFinEquiv.symm j).1 * k + g (finProdFinEquiv.symm j).2 := by
  simp only [sqPerm, Equiv.trans_apply, Equiv.prodCongr_apply, finProdFinEquiv_apply_val,
    Prod.map_fst, Prod.map_snd]
  ring

theorem sqPerm_pair (g : Perm (Fin k)) (p q : Fin k) :
    sqPerm g (finProdFinEquiv (p, q)) = finProdFinEquiv (g p, g q) := by
  simp [sqPerm]

/-- The pair `(p, 0)`: index `k p`. -/
theorem pair_zero_val (hk : 0 < k) (p : Fin k) :
    ((finProdFinEquiv (p, (⟨0, hk⟩ : Fin k)) : Fin (k * k)) : ℕ) = k * p := by
  simp [finProdFinEquiv_apply_val]

open Classical in
/-- **Back from pairs.** The permutation `t` with `sqPerm t = x`, read off the images of the
pairs `(p, 0)`: `t p = x (k p) / k`. It is the identity when `x` is not of this form. -/
noncomputable def unsq (x : Perm (Fin (k * k))) : Perm (Fin k) :=
  if h : ∃ t, sqPerm t = x then h.choose else 1

theorem unsq_sqPerm (t : Perm (Fin k)) : unsq (sqPerm t) = t := by
  have h : ∃ t', sqPerm t' = sqPerm t := ⟨t, rfl⟩
  rw [unsq, dif_pos h]
  have hinj : Function.Injective (sqPerm (k := k)) := by
    intro a b hab
    ext p
    have := congrArg (fun x => (finProdFinEquiv.symm (x (finProdFinEquiv (p, p)))).1) hab
    simpa [sqPerm] using congrArg Fin.val this
  exact hinj h.choose_spec

theorem sqPerm_injective : Function.Injective (sqPerm (k := k)) := fun a b h => by
  rw [← unsq_sqPerm a, h, unsq_sqPerm]

/-- The formula of `unsq` that a program computes. -/
theorem unsq_val (hk : 0 < k) (t : Perm (Fin k)) (p : Fin k) :
    (unsq (sqPerm t) p : ℕ) = (sqPerm t ⟨k * p, by nlinarith [p.2]⟩ : ℕ) / k := by
  rw [unsq_sqPerm]
  have e : (⟨k * p, by nlinarith [p.2]⟩ : Fin (k * k)) = finProdFinEquiv (p, ⟨0, hk⟩) :=
    Fin.ext (pair_zero_val hk p).symm
  rw [e, sqPerm_pair, finProdFinEquiv_apply_val]
  have h0 := (t ⟨0, hk⟩).2
  rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt h0, zero_add]

/-- The group generated by the squares of a list is the square of the group. -/
theorem genGroup_map_sq (gs : List (Perm (Fin k))) :
    genGroup (gs.map sqPerm) = (genGroup gs).map sqHom := by
  rw [genGroup, genGroup, MonoidHom.map_closure]
  congr 1
  ext x
  simp [sqHom_apply]

theorem gens_map_sq (gs : List (Perm (Fin k))) :
    GI.Cited.gens (gs.map sqPerm) = (GI.Cited.gens gs).map sqHom := by
  rw [GI.Cited.gens, GI.Cited.gens, MonoidHom.map_closure]
  congr 1
  ext x
  simp [sqHom_apply]

/-- An element of the square of a group is the square of an element. -/
theorem mem_map_sq {H : Subgroup (Perm (Fin k))} {x : Perm (Fin (k * k))} (hx : x ∈ H.map sqHom) :
    unsq x ∈ H ∧ sqPerm (unsq x) = x := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
  rw [sqHom_apply, unsq_sqPerm]
  exact ⟨ht, rfl⟩

/-- **Generators back from pairs.** If the squares `hs` generate the square of `H`, then the
`unsq` of `hs` generate `H`. -/
theorem gens_map_unsq {H : Subgroup (Perm (Fin k))} (hs : List (Perm (Fin (k * k))))
    (hH : GI.Cited.gens hs = H.map sqHom) : GI.Cited.gens (hs.map unsq) = H := by
  have hmem : ∀ x ∈ hs, sqPerm (unsq x) = x := fun x hx =>
    (mem_map_sq (hH ▸ Subgroup.subset_closure hx : x ∈ H.map sqHom)).2
  have hmap : (hs.map unsq).map sqPerm = hs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id hs]
    exact List.map_congr_left fun x hx => hmem x hx
  have h1 := gens_map_sq (hs.map unsq)
  rw [hmap, hH] at h1
  have hinj : Function.Injective (sqHom (k := k)) := sqPerm_injective
  exact (Subgroup.map_injective hinj h1).symm

/-! ### Coset representatives from a stabilizer -/

/-- **Coset representatives from an orbit with a transversal**, for any action whose stabilizer
of `x₀` in `G` is `K`. The second entries of the pairs, moved back to `Ω`, meet every coset of
`K` exactly once. -/
theorem cosetList_of_stab {Ω X : Type} [DecidableEq X] {act : Perm (Fin k) → X → X}
    (hact : IsAct act) {x₀ : X} {G K : Subgroup (Perm Ω)} (e : Ω ≃ Fin k)
    {gs : List (Perm (Fin k))} (hG : genGroup gs = groupFin e G)
    (hstab : ∀ h ∈ G, act (toFin e h) x₀ = x₀ ↔ h ∈ K)
    (L : List (X × Perm (Fin k))) (hnd : (L.map Prod.fst).Nodup)
    (horb : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit act gs x₀)
    (hp : ∀ p ∈ L, p.2 ∈ genGroup gs ∧ act p.2 x₀ = p.1) :
    let ts := (L.map Prod.snd).map (toFin e).symm
    (∀ t ∈ ts, t ∈ G) ∧ (∀ g ∈ G, ∃ t ∈ ts, t⁻¹ * g ∈ K) ∧
      (∀ i j (hi : i < ts.length) (hj : j < ts.length), ts[i]⁻¹ * ts[j] ∈ K → i = j) := by
  have hmemG : ∀ g, g ∈ genGroup gs ↔ (toFin e).symm g ∈ G := fun g => by
    rw [hG]; exact Subgroup.mem_map_equiv
  refine cosetList_map (toFin e).symm _ (fun t ht => ?_) (fun g hg => ?_) (fun i j hi hj h => ?_)
  · obtain ⟨p, hpL, rfl⟩ := List.mem_map.mp ht
    exact (hmemG _).1 (hp p hpL).1
  · have hg' : g ∈ genGroup gs := (hmemG g).2 hg
    obtain ⟨p, hpL, hpf⟩ := List.mem_map.mp ((horb (act g x₀)).2 ⟨g, hg', rfl⟩)
    refine ⟨p.2, List.mem_map_of_mem hpL, ?_⟩
    have hm : (toFin e).symm (p.2⁻¹ * g) ∈ G :=
      (hmemG _).1 ((genGroup gs).mul_mem ((genGroup gs).inv_mem (hp p hpL).1) hg')
    rw [← hstab _ hm, MulEquiv.apply_symm_apply, hact.mul, ← hpf, ← (hp p hpL).2, ← hact.mul,
      inv_mul_cancel, hact.one]
  · simp only [List.length_map] at hi hj
    have hti : (L.map Prod.snd)[i] ∈ genGroup gs := by
      simpa using (hp L[i] (List.getElem_mem hi)).1
    have htj : (L.map Prod.snd)[j] ∈ genGroup gs := by
      simpa using (hp L[j] (List.getElem_mem hj)).1
    have hm : (toFin e).symm ((L.map Prod.snd)[i]⁻¹ * (L.map Prod.snd)[j]) ∈ G :=
      (hmemG _).1 ((genGroup gs).mul_mem ((genGroup gs).inv_mem hti) htj)
    have := (hstab _ hm).2 (by simpa using h)
    rw [MulEquiv.apply_symm_apply, hact.mul] at this
    have h2 := congrArg (act (L.map Prod.snd)[i]) this
    rw [← hact.mul, mul_inv_cancel, hact.one] at h2
    simp only [List.getElem_map] at h2
    rw [(hp L[i] (List.getElem_mem hi)).2, (hp L[j] (List.getElem_mem hj)).2] at h2
    exact (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simpa using hi)
      (hj := by simpa using hj)).1 (by simpa using h2.symm)

/-- The action of `Sym(k)` on labelings of pairs. -/
def sqAct (t : Perm (Fin k)) (f : Fin (k * k) → ℕ) : Fin (k * k) → ℕ := labAct (sqPerm t) f

theorem isAct_sq : IsAct (sqAct (k := k)) :=
  ⟨fun f => by
      show labAct (sqHom 1) f = f
      rw [map_one]; exact isAct_lab.one f,
    fun g h f => by
      show labAct (sqHom (g * h)) f = labAct (sqHom g) (labAct (sqHom h) f)
      rw [map_mul]; exact isAct_lab.mul _ _ f⟩

theorem actOrbit_sq (gs : List (Perm (Fin k))) (f : Fin (k * k) → ℕ) :
    actOrbit labAct (gs.map sqPerm) f = actOrbit sqAct gs f := by
  ext y
  simp only [actOrbit, Set.mem_setOf_eq, genGroup_map_sq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨sqHom t, Subgroup.mem_map_of_mem _ ht, rfl⟩

/-- **The pairs of the orbit program on squares, moved back.** -/
theorem sqPairs_good (gs : List (Perm (Fin k))) (f : Fin (k * k) → ℕ)
    (L : List ((Fin (k * k) → ℕ) × Perm (Fin (k * k))))
    (hp : ∀ p ∈ L, p.2 ∈ genGroup (gs.map sqPerm) ∧ labAct p.2 f = p.1) :
    ∀ p ∈ L.map (fun p => (p.1, unsq p.2)), p.2 ∈ genGroup gs ∧ sqAct p.2 f = p.1 ∧
      ∃ x ∈ L, p = (x.1, unsq x.2) ∧ sqPerm p.2 = x.2 := by
  intro p hpL
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hpL
  have hm := (hp x hx).1
  rw [genGroup_map_sq] at hm
  obtain ⟨h1, h2⟩ := mem_map_sq hm
  refine ⟨h1, ?_, x, hx, rfl, h2⟩
  simp only [sqAct, h2]
  exact (hp x hx).2

/-! ### Canonical labels of a partition -/

open Classical in
/-- The label of a point: the first point of its class. -/
noncomputable def firstLab {Ω : Type} (e : Ω ≃ Fin k) (R : Setoid Ω) (p : Fin k) : ℕ :=
  (List.finRange k).findIdx fun q => decide (R.r (e.symm p) (e.symm q))

/-- **The first point of each class labels the partition.** -/
theorem firstLab_partitionValC {Ω : Type} (e : Ω ≃ Fin k) (R : Setoid Ω) :
    PartitionValC e (encFun (firstLab e R)) R := by
  classical
  refine ⟨_, rfl, fun p => ?_, fun p q => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := List.findIdx_lt_length_of_exists (p := fun q => decide (R.r (e.symm p) (e.symm q)))
      (xs := List.finRange k) ⟨p, List.mem_finRange p, by simpa using R.iseqv.refl _⟩
    simpa [firstLab] using this
  · have hlt : firstLab e R p < (List.finRange k).length := by
      have := List.findIdx_lt_length_of_exists (p := fun q => decide (R.r (e.symm p) (e.symm q)))
        (xs := List.finRange k) ⟨p, List.mem_finRange p, by simpa using R.iseqv.refl _⟩
      simpa [firstLab] using this
    have h1 := List.findIdx_getElem (xs := List.finRange k)
      (p := fun q => decide (R.r (e.symm p) (e.symm q))) (w := hlt)
    have hlt' : firstLab e R q < (List.finRange k).length := h ▸ hlt
    have h2 := List.findIdx_getElem (xs := List.finRange k)
      (p := fun z => decide (R.r (e.symm q) (e.symm z))) (w := hlt')
    simp only [decide_eq_true_eq] at h1 h2
    have h2' : R.r (e.symm q) (e.symm (List.finRange k)[firstLab e R p]) := by
      have : (List.finRange k)[firstLab e R q] = (List.finRange k)[firstLab e R p] := by
        congr 1; exact h.symm
      rw [← this]; exact h2
    exact R.iseqv.trans h1 (R.iseqv.symm h2')
  · have : (fun z => decide (R.r (e.symm p) (e.symm z))) =
        fun z => decide (R.r (e.symm q) (e.symm z)) := by
      funext z
      exact Bool.decide_congr ⟨fun h' => R.iseqv.trans (R.iseqv.symm h) h', fun h' => R.iseqv.trans h h'⟩
    simp only [firstLab, this]

/-! ### The coordinate bits of two positions -/

section bits

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
  (E : Fin Q.d ≃ (Fin r → Product.KSet m l))

open Classical in
/-- **The coordinate bits.** For `i < r`: whether `v` and `w` agree in coordinate `i` (both in
the domain with equal coordinate `i` of their blocks, or both off the domain). For `i ≥ r`:
whether both or neither lie in the domain. -/
noncomputable def pbit (i : ℕ) (v w : Ω) : ℕ :=
  if h : i < r then
    (if (v ∈ S.dom ∧ w ∈ S.dom ∧ E (Q.blk v) ⟨i, h⟩ = E (Q.blk w) ⟨i, h⟩) ∨
      (v ∉ S.dom ∧ w ∉ S.dom) then 1 else 0)
  else if (v ∈ S.dom ↔ w ∈ S.dom) then 1 else 0

/-- The mask of two positions: the bits `0, …, r` as binary digits. -/
noncomputable def pmask (v w : Ω) : ℕ := hornerN (fun i => pbit Q E i v w) r (r + 1)

/-- The number of leading ones among the bits `r, r - 1, …, 0`. -/
noncomputable def plead (v w : Ω) : ℕ := leadN (fun i => pbit Q E i v w) r (r + 1)

theorem pbit_le_one (i : ℕ) (v w : Ω) : pbit Q E i v w ≤ 1 := by
  unfold pbit; split_ifs <;> omega

theorem pbit_self (i : ℕ) (v : Ω) : pbit Q E i v v = 1 := by
  unfold pbit
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd (by by_cases hv : v ∈ S.dom <;> simp [hv]) h2
  · rfl
  · exact absurd Iff.rfl h3

theorem hornerN_congr {b b' : ℕ → ℕ} {r : ℕ} (h : ∀ i ≤ r, b i = b' i) :
    ∀ t ≤ r + 1, hornerN b r t = hornerN b' r t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => rw [hornerN, hornerN, ih (by omega), h _ (by omega)]

/-- **Equal masks are equal bits.** -/
theorem pmask_eq_iff (v w v' w' : Ω) :
    pmask Q E v w = pmask Q E v' w' ↔ ∀ i ≤ r, pbit Q E i v w = pbit Q E i v' w' :=
  ⟨bits_eq_of_hornerN (fun i _ => pbit_le_one Q E i v w) (fun i _ => pbit_le_one Q E i v' w'),
    fun h => hornerN_congr h _ le_rfl⟩

theorem pmask_lt (v w : Ω) : pmask Q E v w < 2 ^ (r + 1) :=
  hornerN_lt fun i _ => pbit_le_one Q E i v w

/-- **An element of `G` permutes the bits** as it permutes the coordinates. -/
theorem pbit_smul {g : Perm Ω} (hg : g ∈ S.G) {σ : Perm (Fin r)} {hh : Fin r → Perm (Fin m)}
    (hp : Product.IsProd E (Q.ρ ⟨g, hg⟩) σ hh) (v w : Ω) (i : ℕ) :
    pbit Q E i (g v) (g w) =
      if hi : i < r then pbit Q E (σ ⟨i, hi⟩) v w else pbit Q E i v w := by
  have hv := S.dom_inv g hg v
  have hw := S.dom_inv g hg w
  unfold pbit
  by_cases hi : i < r
  · simp only [dif_pos hi, (σ ⟨i, hi⟩).2]
    by_cases hvd : v ∈ S.dom <;> by_cases hwd : w ∈ S.dom
    · have e1 : E (Q.blk (g v)) ⟨i, hi⟩ = GI.Cited.kSetPerm (hh ⟨i, hi⟩) (E (Q.blk v) (σ ⟨i, hi⟩)) := by
        rw [Q.equivariant ⟨g, hg⟩ v hvd]; exact congrFun (hp _) _
      have e2 : E (Q.blk (g w)) ⟨i, hi⟩ = GI.Cited.kSetPerm (hh ⟨i, hi⟩) (E (Q.blk w) (σ ⟨i, hi⟩)) := by
        rw [Q.equivariant ⟨g, hg⟩ w hwd]; exact congrFun (hp _) _
      have hinj : ∀ a b : Product.KSet m l, GI.Cited.kSetPerm (hh ⟨i, hi⟩) a =
          GI.Cited.kSetPerm (hh ⟨i, hi⟩) b ↔ a = b := fun a b =>
        (GI.Cited.kSetPerm (hh ⟨i, hi⟩)).injective.eq_iff
      simp only [hv.2 hvd, hw.2 hwd, hvd, hwd, true_and, not_true_eq_false, and_false, or_false,
        e1, e2, hinj]
      simp
    · simp [hv, hw, hvd, hwd]
    · simp [hv, hw, hvd, hwd]
    · simp [hv, hw, hvd, hwd]
  · simp only [dif_neg hi]
    have hc := iff_congr hv hw
    by_cases h1 : (v ∈ S.dom ↔ w ∈ S.dom)
    · rw [if_pos (hc.2 h1), if_pos h1]
    · rw [if_neg (fun h => h1 (hc.1 h)), if_neg h1]

/-- The bits after `g`, as bits before `g`. -/
theorem pbits_smul_iff {g : Perm Ω} (hg : g ∈ S.G) {σ : Perm (Fin r)}
    {hh : Fin r → Perm (Fin m)} (hp : Product.IsProd E (Q.ρ ⟨g, hg⟩) σ hh) (v w v' w' : Ω) :
    (∀ i ≤ r, pbit Q E i (g v) (g w) = pbit Q E i (g v') (g w')) ↔
      ∀ i ≤ r, pbit Q E i v w = pbit Q E i v' w' := by
  simp only [pbit_smul Q E hg hp]
  constructor
  · intro h i hi
    by_cases hir : i < r
    · have := h (σ.symm ⟨i, hir⟩) (by have := (σ.symm ⟨i, hir⟩).2; omega)
      simpa [(σ.symm ⟨i, hir⟩).2] using this
    · have := h i hi
      simpa [hir] using this
  · intro h i hi
    by_cases hir : i < r
    · simpa [hir] using h _ (σ ⟨i, hir⟩).2.le
    · simpa [hir] using h i hi

/-- **`G` keeps the relation "equal masks".** -/
theorem pmask_smul_iff (hS : Q.ProductStructure m l r E) {g : Perm Ω} (hg : g ∈ S.G)
    (v w v' w' : Ω) :
    pmask Q E (g v) (g w) = pmask Q E (g v') (g w') ↔ pmask Q E v w = pmask Q E v' w' := by
  obtain ⟨σ, hh, hp⟩ := hS.1 _ ⟨⟨g, hg⟩, rfl⟩
  rw [pmask_eq_iff, pmask_eq_iff]
  exact pbits_smul_iff Q E hg hp v w v' w'

/-- Membership in the coordinate group. -/
theorem mem_coordinateGroup_iff (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l)
    {g : Perm Ω} (hg : g ∈ S.G) :
    g ∈ Q.coordinateGroup E hS hb ↔ ∃ hh, Product.IsProd E (Q.ρ ⟨g, hg⟩) 1 hh := by
  unfold PrimitiveQuotient.coordinateGroup
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := (Product.coordHom_eq_one_iff E Q.ρ.range hS.1 hb (Q.ρ.rangeRestrict x)).1 hx
    simpa using this
  · intro h
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    exact (Product.coordHom_eq_one_iff E Q.ρ.range hS.1 hb (Q.ρ.rangeRestrict ⟨g, hg⟩)).2
      (by simpa using h)

/-- **The stabilizer of the masks is the coordinate group.** -/
theorem pmask_stab_iff (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l) {g : Perm Ω}
    (hg : g ∈ S.G) :
    (∀ v w, pmask Q E (g v) (g w) = pmask Q E v w) ↔ g ∈ Q.coordinateGroup E hS hb := by
  classical
  rw [mem_coordinateGroup_iff Q E hS hb hg]
  obtain ⟨σ, hh, hp⟩ := hS.1 _ ⟨⟨g, hg⟩, rfl⟩
  constructor
  · intro hall
    suffices hσ : σ = 1 by subst hσ; exact ⟨hh, hp⟩
    ext i
    by_contra hne
    have hne' : σ i ≠ i := fun h => hne (congrArg Fin.val h)
    have hcard : 1 < Fintype.card (Product.KSet m l) := by
      rw [Fintype.card_finset_len, Fintype.card_fin]; omega
    obtain ⟨A, B, hAB⟩ := Fintype.exists_pair_of_one_lt_card hcard
    obtain ⟨v, hv, hbv⟩ := Q.onto (E.symm fun _ => A)
    obtain ⟨w, hw, hbw⟩ := Q.onto (E.symm (Function.update (fun _ => B) (σ i) A))
    have h1 := (pmask_eq_iff Q E _ _ _ _).1 (hall v w) i i.2.le
    rw [pbit_smul Q E hg hp, dif_pos i.2] at h1
    have hb1 : pbit Q E (σ i) v w = 1 := by
      unfold pbit
      have hE : E (Q.blk v) ⟨σ i, (σ i).2⟩ = E (Q.blk w) ⟨σ i, (σ i).2⟩ := by
        rw [hbv, hbw, E.apply_symm_apply, E.apply_symm_apply]
        simp
      rw [dif_pos (σ i).2, if_pos (Or.inl ⟨hv, hw, hE⟩)]
    have hb0 : pbit Q E i v w = 0 := by
      unfold pbit
      rw [dif_pos i.2, if_neg]
      rintro (⟨-, -, h⟩ | ⟨h, -⟩)
      · rw [hbv, hbw, E.apply_symm_apply, E.apply_symm_apply,
          Function.update_of_ne (fun h => hne' h.symm)] at h
        exact hAB h
      · exact h hv
    simp only [Fin.eta] at h1
    omega
  · rintro ⟨hh', hp'⟩ v w
    rw [pmask_eq_iff Q]
    intro i _
    rw [pbit_smul Q E hg hp']
    split_ifs <;> rfl

/-! ### On `Fin k` -/

variable {k : ℕ} (e : Ω ≃ Fin k)

/-- The masks as a labeling of the pairs of points of `Fin k`. -/
noncomputable def maskF (j : Fin (k * k)) : ℕ :=
  pmask Q E (e.symm (finProdFinEquiv.symm j).1) (e.symm (finProdFinEquiv.symm j).2)

/-- The leading ones as a labeling of the pairs. -/
noncomputable def leadF (j : Fin (k * k)) : ℕ :=
  plead Q E (e.symm (finProdFinEquiv.symm j).1) (e.symm (finProdFinEquiv.symm j).2)

theorem toFin_symm_apply' (h : Perm Ω) (p : Fin k) : e.symm (toFin e h p) = h (e.symm p) := by
  show e.symm (e (h (e.symm p))) = _
  simp

theorem maskF_sq (h : Perm Ω) (j : Fin (k * k)) :
    maskF Q E e (sqPerm (toFin e h) j) =
      pmask Q E (h (e.symm (finProdFinEquiv.symm j).1)) (h (e.symm (finProdFinEquiv.symm j).2)) := by
  simp [maskF, sqPerm]

/-- **The stabilizer of the mask labeling is the coordinate group.** -/
theorem sqAct_maskF_iff (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l) {h : Perm Ω}
    (hh : h ∈ S.G) :
    sqAct (toFin e h) (maskF Q E e) = maskF Q E e ↔ h ∈ Q.coordinateGroup E hS hb := by
  have hinv : h⁻¹ ∈ S.G := S.G.inv_mem hh
  rw [← Subgroup.inv_mem_iff, ← pmask_stab_iff Q E hS hb hinv]
  have e1 : ∀ j, sqAct (toFin e h) (maskF Q E e) j = maskF Q E e (sqPerm (toFin e h⁻¹) j) := by
    intro j
    simp only [sqAct, labAct, map_inv]
    congr 1
  constructor
  · intro heq v w
    have := congrFun heq (finProdFinEquiv (e v, e w))
    rw [e1, maskF_sq] at this
    simpa [maskF] using this
  · intro hall
    funext j
    rw [e1, maskF_sq, hall]
    rfl

/-- **The square of `G` keeps the relation "equal masks".** -/
theorem maskF_pres (hS : Q.ProductStructure m l r E) {x : Perm (Fin (k * k))}
    (hx : x ∈ (groupFin e S.G).map sqHom) (i j : Fin (k * k)) :
    maskF Q E e (x i) = maskF Q E e (x j) ↔ maskF Q E e i = maskF Q E e j := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 ht
  change maskF Q E e (sqPerm (toFin e h) i) = maskF Q E e (sqPerm (toFin e h) j) ↔ _
  rw [maskF_sq, maskF_sq]
  exact pmask_smul_iff Q E hS hh _ _ _ _

/-- **The kernel on the classes of equal masks is the square of the coordinate group.** -/
theorem maskF_kernel (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l)
    (x : Perm (Fin (k * k))) :
    (x ∈ (groupFin e S.G).map sqHom ∧ ∀ j, maskF Q E e (x j) = maskF Q E e j) ↔
      x ∈ (groupFin e (Q.coordinateGroup E hS hb)).map sqHom := by
  constructor
  · rintro ⟨hx, hall⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 ht
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ((pmask_stab_iff Q E hS hb hh).1
      fun v w => ?_))
    have := hall (finProdFinEquiv (e v, e w))
    change maskF Q E e (sqPerm (toFin e h) _) = _ at this
    rw [maskF_sq] at this
    simpa [maskF] using this
  · intro hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 ht
    have hG : h ∈ S.G := (Subgroup.map_subtype_le _ : Q.coordinateGroup E hS hb ≤ S.G) hh
    refine ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hG), fun j => ?_⟩
    change maskF Q E e (sqPerm (toFin e h) _) = _
    rw [maskF_sq, (pmask_stab_iff Q E hS hb hG).2 hh]
    rfl

/-- **The orbit of the mask labeling has at most `r!` points**: an orbit point depends only on
the coordinate permutation. -/
theorem ncard_orbit_mask_le (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l)
    {gs : List (Perm (Fin k))} (hG : genGroup gs = groupFin e S.G) :
    (actOrbit sqAct gs (maskF Q E e)).ncard ≤ r.factorial := by
  classical
  set ψ := (Product.coordHom E Q.ρ.range hS.1 hb).comp Q.ρ.rangeRestrict with hψ
  let F : Perm (Fin r) → (Fin (k * k) → ℕ) := fun σ =>
    if h : ∃ x : S.G, ψ x = σ then sqAct (toFin e (h.choose : Perm Ω)) (maskF Q E e)
    else maskF Q E e
  have hsub : actOrbit sqAct gs (maskF Q E e) ⊆ Set.range F := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hG] at ht
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ht
    have h : ∃ x : S.G, ψ x = ψ ⟨g, hg⟩ := ⟨_, rfl⟩
    refine ⟨ψ ⟨g, hg⟩, ?_⟩
    simp only [F, dif_pos h]
    set x' := h.choose with hx'
    have hx := h.choose_spec
    rw [← hx'] at hx
    have hmem : ((x'⁻¹ * ⟨g, hg⟩ : S.G) : Perm Ω) ∈ Q.coordinateGroup E hS hb :=
      ⟨x'⁻¹ * ⟨g, hg⟩, by
        change ψ (x'⁻¹ * ⟨g, hg⟩) = 1
        rw [map_mul, map_inv, hx, inv_mul_cancel], rfl⟩
    have hst := (sqAct_maskF_iff Q E e hS hb (x'⁻¹ * ⟨g, hg⟩ : S.G).2).2 hmem
    have e1 : (toFin e g : Perm (Fin k)) = toFin e (x' : Perm Ω) *
        toFin e ((x'⁻¹ * ⟨g, hg⟩ : S.G) : Perm Ω) := by
      rw [← map_mul]; simp
    change sqAct (toFin e (x' : Perm Ω)) (maskF Q E e) = sqAct (toFin e g) (maskF Q E e)
    rw [e1, isAct_sq.mul, hst]
  calc (actOrbit sqAct gs (maskF Q E e)).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (F '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Perm (Fin r))).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = r.factorial := by rw [Set.ncard_univ, Nat.card_perm, Nat.card_fin]

theorem pbit_eq_one_lt {i : ℕ} (hi : i < r) (v w : Ω) :
    pbit Q E i v w = 1 ↔ (v ∈ S.dom ∧ w ∈ S.dom ∧ E (Q.blk v) ⟨i, hi⟩ = E (Q.blk w) ⟨i, hi⟩) ∨
      (v ∉ S.dom ∧ w ∉ S.dom) := by
  unfold pbit; rw [dif_pos hi]; split_ifs with h <;> simp [h]

theorem pbit_eq_one_ge {i : ℕ} (hi : r ≤ i) (v w : Ω) :
    pbit Q E i v w = 1 ↔ (v ∈ S.dom ↔ w ∈ S.dom) := by
  unfold pbit; rw [dif_neg (by omega)]; split_ifs with h <;> simp [h]

/-- **The coordinate partitions from the leading ones.** Two positions agree in all
coordinates `j ≥ s` exactly when the bits `r, r - 1, …, s` are `1`. -/
theorem coordPart_iff_plead {s : ℕ} (hs : s ≤ r) (v w : Ω) :
    (Q.coordPart E s).r v w ↔ r + 1 - s ≤ plead Q E v w := by
  rw [plead, le_leadN_iff _ r (show r + 1 - s ≤ r + 1 by omega)]
  show ((v ∈ S.dom ∧ w ∈ S.dom ∧ ∀ j : Fin r, s ≤ j.val → E (Q.blk v) j = E (Q.blk w) j) ∨
    (v ∉ S.dom ∧ w ∉ S.dom)) ↔ _
  constructor
  · intro h u hu
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · rw [Nat.sub_zero, pbit_eq_one_ge Q E le_rfl]
      rcases h with ⟨hv, hw, -⟩ | ⟨hv, hw⟩
      · exact iff_of_true hv hw
      · exact iff_of_false hv hw
    · rw [pbit_eq_one_lt Q E (show r - u < r by omega)]
      rcases h with ⟨hv, hw, hE⟩ | h
      · exact Or.inl ⟨hv, hw, hE ⟨r - u, by omega⟩ (by simp; omega)⟩
      · exact Or.inr h
  · intro h
    have h0 := (pbit_eq_one_ge Q E (le_refl r) v w).1 (by simpa using h 0 (by omega))
    by_cases hv : v ∈ S.dom
    · refine Or.inl ⟨hv, h0.1 hv, fun j hj => ?_⟩
      have := (pbit_eq_one_lt Q E j.2 v w).1 (by
        have := h (r - j) (by have := j.2; omega)
        rwa [show r - (r - (j : ℕ)) = j by have := j.2; omega] at this)
      rcases this with ⟨-, -, hE⟩ | ⟨hv', -⟩
      · exact hE
      · exact absurd hv hv'
    · exact Or.inr ⟨hv, fun hw => hv (h0.2 hw)⟩

theorem plead_self (v : Ω) : plead Q E v v = r + 1 := by
  apply le_antisymm (leadN_le _ _ _)
  rw [le_leadN_iff _ r le_rfl]
  intro u _
  exact pbit_self Q E _ v

end bits

end GI.Impl
