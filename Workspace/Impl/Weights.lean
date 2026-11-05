module

public import Workspace.Impl.Orbit
public import Workspace.Impl.Threshold
public import Workspace.Impl.ContSel
public import Workspace.Lang.Prims.Reduce

@[expose] public section

/-!
# Weights of canonical values and the work bound

Obligation (c) of the trusted statement asks that every `Continue` or `GiantStep` node does work
at most `E_N = exp(cw (log(N+2))²)` (`Iface.WorkReq`). The work of a node is the cost of its
case, of choosing the case, of the dispatch, and the setup of its `Solve` children. Each of these
is a polynomial in the weight of a canonical state value and of a canonical answer. This file
shows that these weights are polynomial in `N`, so that every polynomial step cost fits in
`E_N`.

* `stateW_le_of_small`: on a `Small` state with `k ≤ N` positions, the weight bound `stateW` of a
  canonical value is at most `10⁴ (N + 2)⁶`. So is the weight of the value itself
  (`Canon.wt_le_poly`).
* `pow_le_expLogSq`: `A (N + 2)^D ≤ exp(3 (log A + D) (log(N+2))²)`.

The file also fixes the choices of the interface (`Iface`) that the implemented steps determine
(`Rest.iface`), leaves the others as the fields of `Rest`, and proves `WorkReq` from polynomial
bounds on the remaining ones (`Rest.workReq`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### Polynomial bounds in `ℕ` -/

theorem pow_mono_exp {M : ℕ} (hM : 1 ≤ M) {E D : ℕ} (h : E ≤ D) : M ^ E ≤ M ^ D :=
  Nat.pow_le_pow_right hM h

/-- If `x ≤ A M^E` with `M ≥ 1`, then `(x + 1)^d ≤ (A + 1)^d M^(E d)`. -/
theorem succ_pow_le {x A M E : ℕ} (hM : 1 ≤ M) (h : x ≤ A * M ^ E) (d : ℕ) :
    (x + 1) ^ d ≤ (A + 1) ^ d * M ^ (E * d) := by
  have h1 : 1 ≤ M ^ E := Nat.one_le_pow _ _ hM
  have h2 : x + 1 ≤ (A + 1) * M ^ E := by rw [Nat.add_mul, one_mul]; omega
  calc (x + 1) ^ d ≤ ((A + 1) * M ^ E) ^ d := Nat.pow_le_pow_left h2 d
    _ = (A + 1) ^ d * M ^ (E * d) := by rw [mul_pow, ← pow_mul]

/-! ### The weight of a canonical value is polynomial in `N` -/

theorem partW_le {k M : ℕ} (hk : k + 1 ≤ M) : partW k ≤ 5 * M ^ 2 := by
  unfold partW
  have : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hk 2
  nlinarith

theorem intervalW_le {k M : ℕ} (hk : k + 1 ≤ M) {I : Interval Ω} (hr : I.ratio + 2 ≤ M)
    (hc : I.cap + 2 ≤ M) (ho : I.origin + 2 ≤ M) : intervalW k I ≤ 20 * M ^ 2 := by
  unfold intervalW
  have := partW_le hk
  have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

theorem hierW_le {k M N : ℕ} (hk : k + 1 ≤ M) (hN : N + 2 ≤ M) {l : List (Interval Ω)}
    (hl : l.length ≤ N) (hI : ∀ I ∈ l, I.ratio ≤ N ∧ I.cap ≤ N ∧ I.origin ≤ N) :
    hierW k l ≤ 50 * M ^ 3 := by
  unfold hierW
  have hs : (l.map (intervalW k)).sum ≤ l.length * (20 * M ^ 2) := by
    have := List.sum_le_card_nsmul (l.map (intervalW k)) (20 * M ^ 2) (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ I hIl rfl
      obtain ⟨h1, h2, h3⟩ := hI I hIl
      exact intervalW_le hk (by omega) (by omega) (by omega))
    simpa using this
  have h1 : l.length * (20 * M ^ 2) ≤ M * (20 * M ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have e : M * (20 * M ^ 2) = 20 * M ^ 3 := by ring
  have : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem rowsW_le {k M N : ℕ} (hk : k + 1 ≤ M) (hN : N + 2 ≤ M) {o : Option (RowRecord Ω)}
    (ho : ∀ R ∈ o, R.m ≤ N) : rowsW k o ≤ 100 * M ^ 2 := by
  have hp := partW_le hk
  have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  cases o with
  | none => simp only [rowsW]; nlinarith
  | some R =>
    have := ho R rfl
    simp only [rowsW]
    omega

theorem groupW_le {k M : ℕ} (hk : k + 1 ≤ M) : groupW k ≤ 160 * M ^ 6 := by
  unfold groupW
  have h1 : (k ^ 2 + 2) * (k + 1) ≤ 2 * (k + 1) ^ 3 := by nlinarith
  have h2 : ((k ^ 2 + 2) * (k + 1)) ^ 2 ≤ 4 * (k + 1) ^ 6 := by
    calc ((k ^ 2 + 2) * (k + 1)) ^ 2 ≤ (2 * (k + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 4 * (k + 1) ^ 6 := by ring
  have h3 : (k + 1) ^ 6 ≤ M ^ 6 := Nat.pow_le_pow_left hk 6
  omega

/-- **The weight bound of a canonical value is polynomial in `N`**: on a `Small` state with
`k ≤ N` positions, `stateW k S ≤ 10⁴ (N + 2)⁶`. -/
theorem stateW_le_of_small {S : State Ω C} (hk : k ≤ S.N) (hs : Small S) :
    stateW k S ≤ 10 ^ 4 * (S.N + 2) ^ 6 := by
  obtain ⟨hl, hI, hr⟩ := hs
  have hkM : k + 1 ≤ S.N + 2 := by omega
  have hNM : S.N + 2 ≤ S.N + 2 := le_rfl
  have g := groupW_le hkM
  have hh := hierW_le hkM hNM hl hI
  have hro := rowsW_le hkM hNM hr
  have hle := S.h_le
  generalize hM : S.N + 2 = M at *
  have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have m36 : M ^ 3 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk2 : k * (2 * (2 * k) + 5) + 4 ≤ 5 * M ^ 2 := by
    have : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hkM 2
    nlinarith
  unfold stateW
  omega

/-- **The weight of a canonical value is polynomial in `N`.** -/
theorem Canon.wt_le_poly {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val} {S : State Ω C}
    (h : Canon e c v S) : v.wt ≤ 10 ^ 4 * (S.N + 2) ^ 6 :=
  h.wt_le.trans (stateW_le_of_small h.fits h.small')

/-- The weight bound of a canonical answer on `k ≤ N` positions. -/
theorem ansW_le_N {k N : ℕ} (hk : k ≤ N) : ansW k ≤ 1000 * (N + 2) ^ 6 :=
  (ansW_le k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))

/-! ### Polynomials fit in `E_N` -/

/-- **A polynomial in `N` is at most `exp(cw (log(N+2))²)`**:
`A (N + 2)^D ≤ exp(3 (log A + D) (log(N+2))²)` for `A ≥ 1`. -/
theorem pow_le_expLogSq {A : ℝ} (hA : 1 ≤ A) (D N : ℕ) :
    A * ((N : ℝ) + 2) ^ D ≤ expLogSq (3 * (Real.log A + D)) N := by
  unfold expLogSq
  have hX : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  set L := Real.log ((N : ℝ) + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [N.cast_nonneg (α := ℝ)])
  have hl2 := Real.log_two_gt_d9
  have hL0 : (0.69 : ℝ) ≤ L := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hlhs : A * ((N : ℝ) + 2) ^ D = Real.exp (Real.log A + D * L) := by
    rw [Real.exp_add, Real.exp_log (by linarith), hL, ← Real.log_rpow hX,
      Real.exp_log (by positivity), Real.rpow_natCast]
  rw [hlhs, Real.exp_le_exp]
  have h1 : Real.log A ≤ 3 * Real.log A * L ^ 2 := by
    have : 1 ≤ 3 * L ^ 2 := by nlinarith
    nlinarith
  have h2 : D * L ≤ 3 * D * L ^ 2 := by
    have : L ≤ 3 * L ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-! ### Canonical answers from the coset normal form -/

/-- A canonical answer is a value in the coset normal form (`GI.Lang.CosetC`) of the image of
the answer. So `GI.Lang.cosetNF_spec` turns any answer value into a canonical one. -/
theorem ansC_iff_cosetC (e : Ω ≃ Fin k) (u : Val) (A : Set (Perm Ω)) :
    AnsC e u A ↔ CosetC k u (toFin e '' A) := by
  unfold AnsC CosetC
  rw [Set.image_eq_empty]

/-! ### The value of the supplied labels -/

open Classical in
/-- **The Johnson block map of the constituent as a value**: entry `i` is, for a position
`e⁻¹ i` of the domain, the indicator of its block (a subset of the `q` labels), and `[]` off
the domain. -/
noncomputable def blkMapVal (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (B : JohnsonBlocks S L) : Val :=
  .list ((List.finRange k).map fun i =>
    if h : e.symm i ∈ S.dom then encFun (fun j : Fin L.q => if j ∈ B.p ⟨e.symm i, h⟩ then 1 else 0)
    else .list [])

/-- **The value of the supplied labels** of a `GiantStep` call:
`[q, pairs, sel, h, f, blocks]`, where

* `pairs` lists `[g, π g]` for the entries `g` of a generating list of the group with at most
  `k²` entries, and `π g ∈ Alt(q)` is the label image of `g` (as a permutation of `Fin q`); they
  determine the label map `π` on the group;
* `sel` is the index of the selected interval (`SuppliedLabels.sel`);
* `h`, `f` and `blocks` are the Johnson block map of the constituent (`JohnsonBlocks`): the block
  size, the fiber size, and the block of each position of the domain (`blkMapVal`).

So the value determines the labels (`LabValStd.unique`): a giant step receives exactly the labels
that the normalization computed, with their selected interval and block map. -/
def LabValStd (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val) (L : SuppliedLabels S) : Prop :=
  ∃ ps : List (Perm (Fin k) × Perm (Fin L.q)),
    lv = .list [.nat L.q, .list (ps.map fun p => .list [encPerm p.1, encPerm p.2]), .nat L.sel,
      .nat L.con.blocks.h, .nat L.con.blocks.f, blkMapVal e L.con.blocks] ∧
    ps.length ≤ k ^ 2 ∧ gens (ps.map Prod.fst) = groupFin e S.G ∧
    ∀ p ∈ ps, ∀ hg : (toFin e).symm p.1 ∈ S.G,
      ((L.π ⟨(toFin e).symm p.1, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = p.2

/-- The weight bound of a label value on `k` positions in a phase of size `N`. -/
def labWStd (k N : ℕ) : ℕ := 2000 * (k + 1) ^ 4 + 2 * N + 100

/-- Two homomorphisms on `G` that agree on the preimages of a generating list of the image of `G`
are equal. -/
theorem hom_eq_of_gens {e : Ω ≃ Fin k} {G : Subgroup (Perm Ω)} {H : Type} [Group H]
    (π π' : G →* H) (gs : List (Perm (Fin k))) (hgen : gens gs = groupFin e G)
    (h : ∀ x ∈ gs, ∀ hg : (toFin e).symm x ∈ G, π ⟨_, hg⟩ = π' ⟨_, hg⟩) : π = π' := by
  have hmem : ∀ x, x ∈ gens gs → (toFin e).symm x ∈ G := fun x hx => by
    rw [hgen] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    change (toFin e).symm (toFin e g) ∈ G
    rw [MulEquiv.symm_apply_apply]
    exact hg
  have key : ∀ x (hx : x ∈ gens gs), ∀ hg : (toFin e).symm x ∈ G, π ⟨_, hg⟩ = π' ⟨_, hg⟩ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one =>
      intro hg
      have : (⟨(toFin e).symm 1, hg⟩ : G) = 1 := Subtype.ext (map_one _)
      rw [this, map_one, map_one]
    | mul x y hx hy ihx ihy =>
      intro hg
      have : (⟨(toFin e).symm (x * y), hg⟩ : G) =
          ⟨(toFin e).symm x, hmem x hx⟩ * ⟨(toFin e).symm y, hmem y hy⟩ := Subtype.ext (map_mul _ _ _)
      rw [this, map_mul, map_mul, ihx, ihy]
    | inv x hx ihx =>
      intro hg
      have : (⟨(toFin e).symm x⁻¹, hg⟩ : G) = (⟨(toFin e).symm x, hmem x hx⟩)⁻¹ :=
        Subtype.ext (map_inv _ _)
      rw [this, map_inv, map_inv, ihx]
  ext g
  have hx : toFin e g ∈ gens gs := by rw [hgen]; exact ⟨g, g.2, rfl⟩
  have hg' : (toFin e).symm (toFin e g) ∈ G := by rw [MulEquiv.symm_apply_apply]; exact g.2
  have := key _ hx hg'
  have hgg : (⟨(toFin e).symm (toFin e g), hg'⟩ : G) = g :=
    Subtype.ext (MulEquiv.symm_apply_apply _ _)
  rw [hgg] at this
  rw [this]

theorem pairVal_injective {n q : ℕ} :
    Function.Injective fun p : Perm (Fin n) × Perm (Fin q) => Val.list [encPerm p.1, encPerm p.2] := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Val.list.injEq, List.cons.injEq, and_true] at h
  rw [encPerm_injective h.1, encPerm_injective h.2]

theorem encFun_injective {n : ℕ} : Function.Injective (encFun (n := n)) := by
  intro f g h
  funext i
  simp only [encFun, Val.list.injEq] at h
  have := List.map_inj_left.1 h i (List.mem_finRange i)
  simpa using this

open Classical in
/-- **The label value determines the labels.** -/
theorem LabValStd.unique {e : Ω ≃ Fin k} {S : State Ω C} {lv : Val} {L L' : SuppliedLabels S}
    (h : LabValStd e S lv L) (h' : LabValStd e S lv L') : L = L' := by
  obtain ⟨ps, rfl, -, hgen, hπ⟩ := h
  obtain ⟨ps', heq, -, -, hπ'⟩ := h'
  obtain ⟨⟨q, π, hsurj⟩, ⟨hdom, B, hkills⟩, sel, hsu, hsk⟩ := L
  obtain ⟨⟨q', π', hsurj'⟩, ⟨hdom', B', hkills'⟩, sel', hsu', hsk'⟩ := L'
  simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at heq
  obtain ⟨rfl, hps, hsel, hh, hf, hblk⟩ := heq
  have hps' : ps = ps' := (List.map_injective_iff.2 pairVal_injective) hps
  subst hps'
  have hsel' : sel = sel' := Fin.ext hsel
  subst hsel'
  have hππ : π = π' := hom_eq_of_gens π π' (ps.map Prod.fst) hgen fun x hx hg => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact Subtype.ext ((hπ p hp hg).trans (hπ' p hp hg).symm)
  subst hππ
  obtain ⟨bh, bf, bp, beq, bcard, bfib, b1, bhalf⟩ := B
  obtain ⟨bh', bf', bp', beq', bcard', bfib', b1', bhalf'⟩ := B'
  simp only [blkMapVal, Val.list.injEq] at hh hf hblk
  subst hh hf
  have hp : bp = bp' := by
    funext v
    have hl := List.map_inj_left.1 hblk (e v.1) (List.mem_finRange _)
    have hv : e.symm (e v.1) ∈ S.dom := by simpa using v.2
    simp only [dif_pos hv] at hl
    have hfun := encFun_injective hl
    have hvv : (⟨e.symm (e v.1), hv⟩ : S.dom) = v := Subtype.ext (by simp)
    rw [hvv] at hfun
    ext j
    have := congrFun hfun j
    by_cases h1 : j ∈ bp v <;> by_cases h2 : j ∈ bp' v <;> simp_all
  subst hp
  rfl

/-- The label set has at most `k + 2` points: `Alt(q)` is a quotient of a group of permutations
of `k` points, so `q! / 2 ≤ k!`. -/
theorem GiantLabels.q_le {S : State Ω C} (e : Ω ≃ Fin k) (L : GiantLabels S) : L.q ≤ k + 2 := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  by_contra hq
  push Not at hq
  have h1 : Nat.card (alternatingGroup (Fin L.q)) ≤ Nat.card S.G :=
    Nat.card_le_card_of_surjective _ L.π_surj
  have h2 : Nat.card S.G ≤ Nat.card (Perm Ω) := Subgroup.card_le_card_group _
  have h3 : Nat.card (Perm Ω) = k.factorial := by
    rw [Nat.card_perm, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  haveI : Nontrivial (Fin L.q) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h4 := two_mul_nat_card_alternatingGroup (α := Fin L.q)
  have h5 : Nat.card (Perm (Fin L.q)) = L.q.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h6 : (k + 3).factorial ≤ L.q.factorial := Nat.factorial_le hq
  have h7 : (k + 3).factorial = (k + 3) * ((k + 2) * ((k + 1) * k.factorial)) := by
    simp [Nat.factorial_succ]
  have h8 := k.factorial_pos
  have h9 : 6 * k.factorial ≤ (k + 3) * ((k + 2) * ((k + 1) * k.factorial)) := by
    have : 1 * k.factorial ≤ (k + 1) * k.factorial := Nat.mul_le_mul_right _ (by omega)
    have : 2 * k.factorial ≤ (k + 2) * ((k + 1) * k.factorial) := by nlinarith
    nlinarith
  omega

/-- The fiber size of a Johnson block map is at most the number of positions. -/
theorem johnson_f_le {S : State Ω C} {L : GiantLabels S} (e : Ω ≃ Fin k)
    (B : JohnsonBlocks S L) : B.f ≤ k := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨Bl, -, hBl⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin L.q)))
    (n := B.h) (by simpa using (by have := B.half; omega : B.h ≤ L.q))
  rw [← B.fibers Bl hBl]
  calc Nat.card {v : S.dom // B.p v = Bl} ≤ Nat.card S.dom :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card Ω := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = k := by rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

open Classical in
/-- The block-map value weighs at most `30 (k + 3)²`. -/
theorem blkMapVal_wt_le {S : State Ω C} {L : GiantLabels S} (e : Ω ≃ Fin k)
    (B : JohnsonBlocks S L) (hq : L.q ≤ k + 2) : (blkMapVal e B).wt ≤ 30 * (k + 3) ^ 2 := by
  have hent : ∀ v ∈ (List.finRange k).map (fun i =>
      if h : e.symm i ∈ S.dom then encFun (fun j : Fin L.q => if j ∈ B.p ⟨e.symm i, h⟩ then 1 else 0)
      else Val.list []), v.wt ≤ 7 * (k + 3) := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
    split_ifs with h
    · refine (wt_encFun_le _ (B := 1) fun j => by split_ifs <;> omega).trans ?_
      nlinarith
    · rw [wt_list_nil]; omega
  have hsum : (((List.finRange k).map (fun i =>
      if h : e.symm i ∈ S.dom then encFun (fun j : Fin L.q => if j ∈ B.p ⟨e.symm i, h⟩ then 1 else 0)
      else Val.list [])).map Val.wt).sum ≤ k * (7 * (k + 3)) := by
    have := List.sum_le_card_nsmul _ (7 * (k + 3)) (fun x hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact hent v hv)
    simpa using this
  have h1 := wt_list_le ((List.finRange k).map (fun i =>
      if h : e.symm i ∈ S.dom then encFun (fun j : Fin L.q => if j ∈ B.p ⟨e.symm i, h⟩ then 1 else 0)
      else Val.list []))
  simp only [List.length_map, List.length_finRange] at h1
  unfold blkMapVal
  nlinarith

/-- **A label value weighs at most `labWStd k N`** when the hierarchy has at most `N` intervals
(the selected interval is one of them). -/
theorem LabValStd.wt_le {e : Ω ≃ Fin k} {S : State Ω C} {lv : Val} {L : SuppliedLabels S}
    {N : ℕ} (h : LabValStd e S lv L) (hN : S.hier.length ≤ N) : lv.wt ≤ labWStd k N := by
  obtain ⟨ps, rfl, hl, -, -⟩ := h
  have hq := GiantLabels.q_le e L.toGiantLabels
  have hpair : ∀ p : Perm (Fin k) × Perm (Fin L.q),
      (Val.list [encPerm p.1, encPerm p.2]).wt ≤ 100 * (k + 1) ^ 2 := by
    intro p
    have := wt_list2_le (encPerm p.1) (encPerm p.2)
    have := wt_encPerm_le p.1
    have := wt_encPerm_le p.2
    have : (L.q + 1) ^ 2 ≤ 9 * (k + 1) ^ 2 := by
      calc (L.q + 1) ^ 2 ≤ (3 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 9 * (k + 1) ^ 2 := by ring
    have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  set ws := ps.map fun p => Val.list [encPerm p.1, encPerm p.2] with hws
  have hsum : (ws.map Val.wt).sum ≤ ws.length * (100 * (k + 1) ^ 2) := by
    have := List.sum_le_card_nsmul (ws.map Val.wt) (100 * (k + 1) ^ 2) (by
      simp only [hws, List.map_map, List.mem_map, Function.comp_apply, forall_exists_index,
        and_imp]
      rintro _ p - rfl
      exact hpair p)
    simpa using this
  have hlen : ws.length = ps.length := by simp [hws]
  have h1 := wt_list_le ws
  have h2 := wt_list_le [.nat L.q, .list ws, .nat L.sel, .nat L.con.blocks.h, .nat L.con.blocks.f,
    blkMapVal e L.con.blocks]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at h2
  have h3 := wt_nat_le L.q
  have hs := wt_nat_le L.sel
  have hsel : (L.sel : ℕ) < S.hier.length := L.sel.2
  have hh := wt_nat_le L.con.blocks.h
  have hh' := L.con.blocks.half
  have hf := wt_nat_le L.con.blocks.f
  have hf' := johnson_f_le e L.con.blocks
  have hb := blkMapVal_wt_le e L.con.blocks hq
  have h4 : ws.length * (100 * (k + 1) ^ 2) ≤ (k + 1) ^ 2 * (100 * (k + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by have : k ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2; omega)
  have e : (k + 1) ^ 2 * (100 * (k + 1) ^ 2) = 100 * (k + 1) ^ 4 := by ring
  have h5 : (k + 1) ^ 2 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : k ≤ (k + 1) ^ 2 := by nlinarith
  have h7 : k ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h8 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h9 : (k + 3) ^ 2 ≤ 9 * (k + 1) ^ 2 := by nlinarith
  unfold labWStd
  omega

/-! ### The interface

The implemented steps fix part of the interface: the work `W` at threshold, floor-reset and
orbit-chain nodes (`ThresholdW`, `FloorW`, `OrbitW`), the part of `selW` that the selector of
`Continue` spends before it calls the rest of the selector (`contSel_spec`), the lower bounds on
`Ks` and `ds` of the selector of `Solve` (`solveSel_spec`), and the label format. The rest are
the fields of `Rest`. -/

/-- **The choices left to the steps that are not implemented yet.**

* `solveK`, `solveD`: the direct enumeration and the fresh phase of `Solve` must cost at most
  `solveK (wt v + 1)^solveD` on an input `v`, besides their children (`Rest.solve_own`).
* `restSelB`: the cost bound of the rest of the selector of `Continue` (`Iface.RestSelSpec`:
  transitivity and the column floor).
* `giantSelW`: the work of the selector of `GiantStep` (the row case test).
* `Wgeneral`, `Wrow`, `Wagg`: the work of the general dispatcher (`Run.dispatch`,
  `Run.normalize`), of the row step (`Run.rowTerminal`, `Run.rowColumns`) and of the aggregation
  round (`Run.aggregate`), at their nodes. -/
structure Rest where
  solveK : ℕ
  solveD : ℕ
  restSelB : ∀ {Ω C : Type}, State Ω C → ℝ
  giantSelW : ∀ {Ω C : Type}, State Ω C → ℝ
  Wgeneral : Node P₀ → ℝ
  Wrow : Node P₀ → ℝ
  Wagg : Node P₀ → ℝ

namespace Rest

variable (R : Rest)

/-- The work of the case at a node, by its kind. -/
noncomputable def W (nd : Node P₀) : ℝ :=
  match nd.run.kind with
  | .threshold => ((stateW (Nat.card nd.Ω) nd.S + ansW (Nat.card nd.Ω) + 2 : ℕ) : ℝ)
  | .floorReset => ((50 * stateW (Nat.card nd.Ω) nd.S + ansW (Nat.card nd.Ω) + 700 : ℕ) : ℝ)
  | .orbitStop => ((orbK * (stateW (Nat.card nd.Ω) nd.S + ansW (Nat.card nd.Ω) + 1) ^ 15 : ℕ) : ℝ)
  | .orbitChain => ((orbK * (stateW (Nat.card nd.Ω) nd.S + ansW (Nat.card nd.Ω) + 1) ^ 15 : ℕ) : ℝ)
  | .dispatch => R.Wgeneral nd
  | .normalize => R.Wgeneral nd
  | .rowTerminal => R.Wrow nd
  | .rowColumns => R.Wrow nd
  | .aggregate => R.Wagg nd
  | .direct => 0
  | .fresh => 0

/-- The work of the selector of a call. -/
noncomputable def selW (m : Mode) {Ω C : Type} (S : State Ω C) : ℝ :=
  match m with
  | .solve => 0
  | .cont => (contSelCost (stateW (Nat.card Ω) S) S.N : ℝ) + max 0 (R.restSelB S)
  | .giant => R.giantSelW S

/-- **The concrete interface.** -/
noncomputable def iface : Iface where
  LabVal := fun e S lv L => LabValStd e S lv L
  labW := labWStd
  Ks := solveSelK + R.solveK
  ds := max 2 R.solveD
  W := R.W
  selW := fun m _ _ S => R.selW m S

theorem thresholdW : R.iface.ThresholdW := by
  intro nd hk
  simp only [iface, W, hk, le_refl]

theorem floorW : R.iface.FloorW := by
  intro nd hk
  simp only [iface, W, hk, le_refl]

theorem orbitW : R.iface.OrbitW := by
  rintro nd (hk | hk) <;> simp only [iface, W, hk, le_refl]

/-- The selector of `Solve` (`solveSel_spec`) meets its specification for this interface. -/
theorem solveSel {Pg : Program} {b : ℕ} (h : Pg.HasAt b (solveSelFuns b)) :
    R.iface.SelSpec Pg .solve Iface.solveCases b :=
  solveSel_spec R.iface h (by simp [iface]) (by simp [iface])

/-- The selector of `Continue` (`contSel_spec`) meets its specification for this interface, when
the rest of the selector costs at most `restSelB`. -/
theorem contSel {Pg : Program} {b rest : ℕ} (h : Pg.HasAt b (contSelFuns b rest))
    (hrest : R.iface.RestSelSpec Pg rest R.restSelB) :
    R.iface.SelSpec Pg .cont Iface.contCases b :=
  R.iface.contSel_spec Pg h hrest fun S => by simp [iface, selW]

/-- The cost allowed to a step of `Solve`: a step that costs at most `solveK (wt v + 1)^solveD`
besides its children meets the bound of `StepSpec`. -/
theorem solve_own {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P₀ .solve S L A) (v : Val) :
    (R.solveK : ℝ) * ((v.wt : ℝ) + 1) ^ R.solveD ≤ R.iface.own .solve r v := by
  simp only [Iface.own, if_true, iface]
  have hx : (1 : ℝ) ≤ (v.wt : ℝ) + 1 := by have := (Nat.cast_nonneg v.wt : (0 : ℝ) ≤ _); linarith
  have h1 : ((v.wt : ℝ) + 1) ^ R.solveD ≤ ((v.wt : ℝ) + 1) ^ max 2 R.solveD :=
    pow_le_pow_right₀ hx (le_max_right _ _)
  push_cast
  have h2 : (0 : ℝ) ≤ ((v.wt : ℝ) + 1) ^ max 2 R.solveD := by positivity
  have h3 : (0 : ℝ) ≤ (solveSelK : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (R.solveK : ℝ) := Nat.cast_nonneg _
  nlinarith

end Rest

/-! ### The work bound

At a node that fits its phase (`k ≤ N` positions, `Small` state), the work of the node is the
work `W` of its case, the work `selW` of its selector, the dispatch overhead and the setup of its
`Solve` children. For the implemented kinds each of these is a polynomial in `N`:

* `W ≤ orbK (stateW + ansW + 1)^15 ≤ orbK (2·10⁴)^15 (N+2)^90` (`W_impl_le`);
* the part `contSelCost` of the selector of `Continue` is at most
  `(sizeK + 1000) (2·10⁴)^10 (N+2)^60` (`contSelCost_le`);
* the overhead is at most `10⁶ (N+2)⁶` (`ovh_le`);
* the only `Solve` child is that of the threshold step, on the same state, with setup
  `K₀ (stateW + 1)^d₀ ≤ K₀ (10⁴ + 1)^d₀ (N+2)^(6 d₀)` (`charges_impl`). -/

/-- `2 · 10⁴`: `stateW + ansW + 1 ≤ cQ (N + 2)⁶` on fitting nodes (`sum_le_poly`). -/
@[irreducible] def cQ : ℕ := 20000

/-- The constant of the work of an implemented case. -/
@[irreducible] def cW : ℕ := orbK * cQ ^ 15

/-- The constant of the part `contSelCost` of the selector of `Continue`. -/
@[irreducible] def cS : ℕ := (sizeK + 1000) * cQ ^ 10

theorem cQ_pos : 0 < cQ := by unfold cQ; norm_num

/-- The kinds whose steps are implemented. -/
def implKinds : List CallKind := [.threshold, .orbitStop, .orbitChain, .floorReset]

/-- The implemented kinds are kinds of `Continue`. -/
theorem mode_of_impl (nd : Node P₀) (hk : nd.run.kind ∈ implKinds) : nd.m = .cont := by
  obtain ⟨m, Ω, C, S, L, A, r⟩ := nd
  cases r <;> simp [implKinds, Run.kind] at hk ⊢

/-- **The setup of the children of an implemented step**: only the threshold step has a `Solve`
child, on its own state. -/
theorem charges_impl (I : Iface) (nd : Node P₀) (hk : nd.run.kind ∈ implKinds) :
    (nd.run.children.map I.charge).sum ≤
      (I.K₀ : ℝ) * ((stateW (Nat.card nd.Ω) nd.S : ℝ) + 1) ^ I.d₀ := by
  obtain ⟨m, Ω, C, S, L, A, r⟩ := nd
  have hpos : (0 : ℝ) ≤ (I.K₀ : ℝ) * ((stateW (Nat.card Ω) S : ℝ) + 1) ^ I.d₀ := by positivity
  cases r <;> simp [implKinds, Run.kind] at hk <;> simp [Run.children, Iface.charge, hpos]

theorem sum_le_poly {k : ℕ} {S : State Ω C} (hk : k ≤ S.N) (hs : Small S) :
    stateW k S + ansW k + 1 ≤ cQ * (S.N + 2) ^ 6 := by
  have h1 := stateW_le_of_small hk hs
  have h2 := ansW_le_N hk
  have h3 : 1 ≤ (S.N + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold cQ
  omega

/-- The work of an implemented case, in `ℕ`. -/
theorem W_impl_le_nat {k : ℕ} {S : State Ω C} (hk : k ≤ S.N) (hs : Small S) :
    (stateW k S + ansW k + 2 ≤ cW * (S.N + 2) ^ 90) ∧
    (50 * stateW k S + ansW k + 700 ≤ cW * (S.N + 2) ^ 90) ∧
    (orbK * (stateW k S + ansW k + 1) ^ 15 ≤ cW * (S.N + 2) ^ 90) := by
  have h := sum_le_poly hk hs
  have hp : (stateW k S + ansW k + 1) ^ 15 ≤ cQ ^ 15 * (S.N + 2) ^ 90 := by
    calc (stateW k S + ansW k + 1) ^ 15 ≤ (cQ * (S.N + 2) ^ 6) ^ 15 :=
          Nat.pow_le_pow_left h 15
      _ = cQ ^ 15 * (S.N + 2) ^ 90 := by rw [mul_pow, ← pow_mul]
  have hB : stateW k S + ansW k + 1 ≤ (stateW k S + ansW k + 1) ^ 15 :=
    Nat.le_self_pow (by norm_num) _
  have hK : orbK * (stateW k S + ansW k + 1) ^ 15 ≤ orbK * (cQ ^ 15 * (S.N + 2) ^ 90) :=
    Nat.mul_le_mul_left _ hp
  have ecW : cW * (S.N + 2) ^ 90 = orbK * (cQ ^ 15 * (S.N + 2) ^ 90) := by unfold cW; ring
  rw [← ecW] at hK
  have hO : 700 * (stateW k S + ansW k + 1) ^ 15 ≤ orbK * (stateW k S + ansW k + 1) ^ 15 :=
    Nat.mul_le_mul_right _ (by simp [orbK])
  refine ⟨by omega, by omega, hK⟩

/-- **The work of an implemented case** is at most `orbK (2·10⁴)^15 (N+2)^90`. -/
theorem W_impl_le (R : Rest) (nd : Node P₀) (hk : nd.run.kind ∈ implKinds)
    (hN : Nat.card nd.Ω ≤ nd.S.N) (hs : Small nd.S) :
    R.W nd ≤ ((cW * (nd.S.N + 2) ^ 90 : ℕ) : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := W_impl_le_nat hN hs
  simp only [implKinds, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with hk | hk | hk | hk
  · simp only [Rest.W, hk]; exact Nat.cast_le.mpr h1
  · simp only [Rest.W, hk]; exact Nat.cast_le.mpr h3
  · simp only [Rest.W, hk]; exact Nat.cast_le.mpr h3
  · simp only [Rest.W, hk]; exact Nat.cast_le.mpr h2

/-- The part of the selector of `Continue` before the rest of the selector. -/
theorem contSelCost_le {k : ℕ} {S : State Ω C} (hk : k ≤ S.N) (hs : Small S) :
    contSelCost (stateW k S) S.N ≤ cS * (S.N + 2) ^ 60 := by
  have h := sum_le_poly hk hs
  generalize hs' : stateW k S = s at h
  have hM1 : 1 ≤ S.N + 2 := by omega
  generalize hZ : cQ ^ 10 * (S.N + 2) ^ 60 = Z
  have hs1 : s + 1 ≤ cQ * (S.N + 2) ^ 6 := by omega
  have hY : (s + 1) ^ 10 ≤ Z := by
    rw [← hZ]
    calc (s + 1) ^ 10 ≤ (cQ * (S.N + 2) ^ 6) ^ 10 := Nat.pow_le_pow_left hs1 10
      _ = cQ ^ 10 * (S.N + 2) ^ 60 := by rw [mul_pow, ← pow_mul]
  have h2 : (s + 1) ^ 2 ≤ (s + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : s + 1 ≤ (s + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM : (S.N + 2) ^ 60 ≤ Z := by
    rw [← hZ]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos cQ_pos)
  have hN9 : (S.N + 1) ^ 9 ≤ (S.N + 2) ^ 60 :=
    le_trans (Nat.pow_le_pow_left (by omega) 9) (Nat.pow_le_pow_right hM1 (by omega))
  have hN1 : S.N + 2 ≤ (S.N + 2) ^ 60 := Nat.le_self_pow (by norm_num) _
  have hsz : sizeK * (s + 1) ^ 2 ≤ sizeK * Z := Nat.mul_le_mul_left _ (h2.trans hY)
  have e : cS * (S.N + 2) ^ 60 = sizeK * Z + 1000 * Z := by rw [← hZ]; unfold cS; ring
  rw [e]
  unfold contSelCost
  omega

/-- The dispatch overhead at a fitting node of the concrete interface. -/
theorem ovh_le (R : Rest) {m : Mode} (hm : m ≠ .solve) {S : State Ω C}
    (hk : Nat.card Ω ≤ S.N) (hs : Small S) :
    R.iface.ovh m S ≤ ((10 ^ 6 * (S.N + 2) ^ 6 : ℕ) : ℝ) := by
  have h1 := stateW_le_of_small hk hs
  have h2 := ansW_le_N hk
  have h3 : labWStd (Nat.card Ω) S.N ≤ 3000 * (S.N + 2) ^ 6 := by
    unfold labWStd
    have : (Nat.card Ω + 1) ^ 4 ≤ (S.N + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have : (S.N + 2) ^ 4 ≤ (S.N + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have : S.N + 2 ≤ (S.N + 2) ^ 6 := Nat.le_self_pow (by norm_num) _
    omega
  have h4 : 1 ≤ (S.N + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hin : R.iface.inW m S ≤ 3 * 10 ^ 4 * (S.N + 2) ^ 6 := by
    cases m with
    | solve => exact absurd rfl hm
    | cont => simp only [Iface.inW]; omega
    | giant =>
      have : R.iface.labW (Nat.card Ω) S.N = labWStd (Nat.card Ω) S.N := rfl
      simp only [Iface.inW]; omega
  have hn : 3 * R.iface.inW m S + 11 * ansW (Nat.card Ω) + 300 ≤ 10 ^ 6 * (S.N + 2) ^ 6 := by
    omega
  simp only [Iface.ovh]
  exact_mod_cast hn

/-- **The work of a fitting node**, from bounds on its case, its selector and the setup of its
children. -/
theorem work_le (R : Rest) (nd : Node P₀) (hm : nd.m ≠ .solve) (hk : Nat.card nd.Ω ≤ nd.S.N)
    (hs : Small nd.S) {a1 a2 a3 : ℝ} (h1 : max 0 (R.W nd) ≤ a1)
    (h2 : max 0 (R.selW nd.m nd.S) ≤ a2) (h3 : (nd.run.children.map R.iface.charge).sum ≤ a3) :
    R.iface.work nd ≤ a1 + a2 + ((10 ^ 6 * (nd.S.N + 2) ^ 6 : ℕ) : ℝ) + a3 := by
  have hf : Iface.Fits nd := Or.inr ⟨hk, hs⟩
  have ho := ovh_le R hm hk hs
  simp only [Iface.work, if_pos hf, Iface.base, if_neg hm]
  change max 0 (R.W nd) + max 0 (R.selW nd.m nd.S) + R.iface.ovh nd.m nd.S +
    (nd.run.children.map R.iface.charge).sum ≤ _
  linarith

/-! ### `WorkReq` -/

/-- The base `N + 2 ≥ 1` raised to a smaller exponent is smaller. -/
theorem pow_le_pow_N {N : ℕ} {a b : ℕ} (h : a ≤ b) :
    ((N : ℝ) + 2) ^ a ≤ ((N : ℝ) + 2) ^ b :=
  pow_le_pow_right₀ (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ _); linarith) h

/-- The kinds of the general dispatcher of `Continue`. -/
def generalKinds : List CallKind := [.dispatch, .normalize]

/-- **What the steps that are not implemented must satisfy** for obligation (c): there are `A`
and `D` such that at every `Continue` or `GiantStep` node that fits its phase (`k ≤ N`
positions, `s ≤ N`, `Small` state), with `X = N + 2`,

* the rest of the selector of `Continue` and the selector of `GiantStep` cost at most `A X^D`;
* the general dispatcher (`Wgeneral` at `dispatch` and `normalize`) costs at most
  `E_N = exp(A (log X)²)`: the enumeration of a small primitive quotient lists up to
  `exp(a (log d)²)` elements (Section 7.2, row "Primitive enumeration");
* the row terminal (`Wrow` at `rowTerminal`) costs at most `E_N = exp(A (log X)²)`: Theorem
  `thm:transitive-gat-terminal` allows `exp(O(log²(b+2) + log(m+2) log(b+2)))` extra work, and
  the phase recurrence charges it as `E_N` per node ("where `c_T` bounds the row terminal's extra
  work");
* the column step (`Wrow` at `rowColumns`) and the aggregation round (`Wagg` at `aggregate`) cost
  at most `A X^D`;
* a node of these last kinds has at most `A X^D` children, and every `Solve` child (a script
  call of the row terminal or of an aggregation) has a state whose canonical weight bound is at
  most `A X^D`. (The children of the general dispatcher are `Continue` and `GiantStep` calls,
  which need no setup, `charges_general`.) The last clause holds for every run
  (`GI.Assembly.req_children`); it needs `s ≤ N`, which `WorkReq` supplies. -/
def Rest.Req (R : Rest) : Prop :=
  ∃ A D : ℕ, ∀ nd : Node P₀, nd.m ≠ .solve → nd.S.size ≤ nd.S.N → Nat.card nd.Ω ≤ nd.S.N →
    Small nd.S →
    (nd.m = .cont → R.restSelB nd.S ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
    (nd.m = .giant → R.giantSelW nd.S ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
    (nd.run.kind = .dispatch ∨ nd.run.kind = .normalize → R.Wgeneral nd ≤ expLogSq A nd.S.N) ∧
    (nd.run.kind = .rowTerminal → R.Wrow nd ≤ expLogSq A nd.S.N) ∧
    (nd.run.kind = .rowColumns → R.Wrow nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
    (nd.run.kind = .aggregate → R.Wagg nd ≤ A * ((nd.S.N : ℝ) + 2) ^ D) ∧
    (nd.run.kind ∉ implKinds → nd.run.kind ∉ generalKinds →
      nd.run.children.length ≤ A * (nd.S.N + 2) ^ D ∧
      ∀ c ∈ nd.run.children, c.m = .solve → stateW (Nat.card c.Ω) c.S ≤ A * (nd.S.N + 2) ^ D)

/-- The constant of the polynomial bound of the implemented parts (the selector part, the
overhead and the threshold's `Solve` child). -/
noncomputable def Rest.cImpl (R : Rest) : ℕ :=
  cS + 10 ^ 6 + R.iface.K₀ * (10 ^ 4 + 1) ^ R.iface.d₀

/-- The exponent of the polynomial bound. -/
noncomputable def Rest.expo (R : Rest) (D : ℕ) : ℕ := 90 + 6 * R.iface.d₀ + D * (R.iface.d₀ + 1)

/-- The setup of the children of a node of a kind that is not implemented. -/
theorem charges_rest_le (R : Rest) (nd : Node P₀) {A D : ℕ}
    (hl : nd.run.children.length ≤ A * (nd.S.N + 2) ^ D)
    (hc : ∀ c ∈ nd.run.children, c.m = .solve → stateW (Nat.card c.Ω) c.S ≤ A * (nd.S.N + 2) ^ D) :
    (nd.run.children.map R.iface.charge).sum ≤
      ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ * (nd.S.N + 2) ^ (D * (R.iface.d₀ + 1)) : ℕ) : ℝ) := by
  set I := R.iface
  set B : ℕ := I.K₀ * ((A + 1) ^ I.d₀ * (nd.S.N + 2) ^ (D * I.d₀)) with hB
  have hone : ∀ c ∈ nd.run.children, I.charge c ≤ (B : ℝ) := by
    intro c hc'
    unfold Iface.charge
    split_ifs with hm
    · have h1 := succ_pow_le (by omega) (hc c hc' hm) I.d₀
      have h2 : ((stateW (Nat.card c.Ω) c.S : ℝ) + 1) ^ I.d₀ ≤
          (((A + 1) ^ I.d₀ * (nd.S.N + 2) ^ (D * I.d₀) : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hB]
      push_cast at h2 ⊢
      exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    · positivity
  have hsum : (nd.run.children.map I.charge).sum ≤ nd.run.children.length * (B : ℝ) := by
    have := List.sum_le_card_nsmul (nd.run.children.map I.charge) (B : ℝ) (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ c hc' rfl
      exact hone c hc')
    simpa using this
  have hl' : (nd.run.children.length : ℝ) ≤ ((A * (nd.S.N + 2) ^ D : ℕ) : ℝ) := by
    exact_mod_cast hl
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  refine hsum.trans ((mul_le_mul_of_nonneg_right hl' hB0).trans (le_of_eq ?_))
  rw [hB]
  push_cast
  ring

/-- **The children of the general dispatcher need no setup**: they are `Continue` calls (a
dispatcher reduction) or `Continue` and `GiantStep` calls (a normalization). -/
theorem charges_general (I : Iface) (nd : Node P₀) (hk : nd.run.kind ∈ generalKinds) :
    (nd.run.children.map I.charge).sum = 0 := by
  obtain ⟨m, Ω, C, S, L, A, r⟩ := nd
  cases r with
  | dispatch =>
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hx
    simp only [Run.children] at hc'
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hc'
    simp [Iface.charge]
  | normalize hs htr hfl Q hsm c hq hkc hkl N hN m' hmode A' r' =>
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hx
    simp only [Run.children] at hc'
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hc'
    have hm' : m' ≠ .solve := by
      rcases hmode j with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp
    simp [Iface.charge, hm']
  | _ => simp [generalKinds, Run.kind] at hk

/-- **The work of a fitting node** is at most the work `Wb` of its case plus a polynomial in `N`,
from the bounds on its selector and on the setup of its children. -/
theorem work_le_poly (R : Rest) {A D : ℕ} (nd : Node P₀) (hm : nd.m ≠ .solve)
    (hk : Nat.card nd.Ω ≤ nd.S.N) (hs : Small nd.S)
    (hsc : nd.m = .cont → R.restSelB nd.S ≤ A * ((nd.S.N : ℝ) + 2) ^ D)
    (hsg : nd.m = .giant → R.giantSelW nd.S ≤ A * ((nd.S.N : ℝ) + 2) ^ D)
    {Wb : ℝ} (hW : max 0 (R.W nd) ≤ Wb)
    (hch : nd.run.kind ∉ implKinds → (nd.run.children.map R.iface.charge).sum ≤
      ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ * (nd.S.N + 2) ^ (D * (R.iface.d₀ + 1)) : ℕ) : ℝ)) :
    R.iface.work nd ≤ Wb +
      ((R.cImpl + A + A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) *
        ((nd.S.N : ℝ) + 2) ^ R.expo D := by
  set X : ℝ := (nd.S.N : ℝ) + 2 with hX
  set E := R.expo D with hE
  have hX1 : (1 : ℝ) ≤ X := by have := (Nat.cast_nonneg nd.S.N : (0 : ℝ) ≤ _); linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXE : (0 : ℝ) ≤ X ^ E := pow_nonneg hX0 _
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hAX : (0 : ℝ) ≤ A * X ^ D := mul_nonneg hA0 (pow_nonneg hX0 _)
  have hD : X ^ D ≤ X ^ E := pow_le_pow_N (by simp only [hE, Rest.expo]; nlinarith)
  -- the selector
  have h2 : max 0 (R.selW nd.m nd.S) ≤
      ((cS : ℕ) : ℝ) * X ^ E + A * X ^ E := by
    have hc0 : (0 : ℝ) ≤ ((cS : ℕ) : ℝ) := Nat.cast_nonneg _
    have h60 : X ^ 60 ≤ X ^ E := pow_le_pow_N (by simp only [hE, Rest.expo]; omega)
    have hAE : (A : ℝ) * X ^ D ≤ A * X ^ E := mul_le_mul_of_nonneg_left hD hA0
    have hcE : ((cS : ℕ) : ℝ) * X ^ 60 ≤
        ((cS : ℕ) : ℝ) * X ^ E := mul_le_mul_of_nonneg_left h60 hc0
    have hpos : (0 : ℝ) ≤ ((cS : ℕ) : ℝ) * X ^ 60 := by
      exact mul_nonneg hc0 (pow_nonneg hX0 _)
    obtain ⟨m, Ω, C, S, L, A', r⟩ := nd
    simp only at hm hk hs hsc hsg hX ⊢
    cases m with
    | solve => exact absurd rfl hm
    | cont =>
      have hcs := contSelCost_le hk hs
      have hcs' : (contSelCost (stateW (Nat.card Ω) S) S.N : ℝ) ≤
          ((cS : ℕ) : ℝ) * X ^ 60 := by
        rw [hX]; exact_mod_cast hcs
      have hr := hsc rfl
      have : max 0 (R.restSelB S) ≤ A * X ^ D := max_le hAX hr
      simp only [Rest.selW]
      have : (0 : ℝ) ≤ (contSelCost (stateW (Nat.card Ω) S) S.N : ℝ) + max 0 (R.restSelB S) := by
        have := le_max_left 0 (R.restSelB S); exact add_nonneg (Nat.cast_nonneg _) this
      rw [max_eq_right this]
      linarith
    | giant =>
      have hr := hsg rfl
      simp only [Rest.selW]
      exact max_le (add_nonneg (mul_nonneg hc0 hXE) (mul_nonneg hA0 hXE)) (by linarith)
  -- the children
  have h3 : (nd.run.children.map R.iface.charge).sum ≤
      ((R.iface.K₀ * (10 ^ 4 + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ E +
        ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ E := by
    have hc1 : (0 : ℝ) ≤ ((R.iface.K₀ * (10 ^ 4 + 1) ^ R.iface.d₀ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc2 : (0 : ℝ) ≤ ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hp1 : (0 : ℝ) ≤ ((R.iface.K₀ * (10 ^ 4 + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ E := by
      exact mul_nonneg hc1 hXE
    have hp2 : (0 : ℝ) ≤ ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ E := by
      exact mul_nonneg hc2 hXE
    by_cases hk' : nd.run.kind ∈ implKinds
    · have hc := charges_impl R.iface nd hk'
      have hst := succ_pow_le (by omega) (stateW_le_of_small hk hs) R.iface.d₀
      have h6 : X ^ (6 * R.iface.d₀) ≤ X ^ E := pow_le_pow_N (by simp only [hE, Rest.expo]; omega)
      have hst' : ((stateW (Nat.card nd.Ω) nd.S : ℝ) + 1) ^ R.iface.d₀ ≤
          (((10 ^ 4 + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ (6 * R.iface.d₀) := by
        rw [hX]; exact_mod_cast hst
      have hK : (0 : ℝ) ≤ R.iface.K₀ := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_left hst' hK
      have e : (R.iface.K₀ : ℝ) * ((((10 ^ 4 + 1) ^ R.iface.d₀ : ℕ) : ℝ) *
          X ^ (6 * R.iface.d₀)) =
          ((R.iface.K₀ * (10 ^ 4 + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ (6 * R.iface.d₀) := by
        push_cast; ring
      have := mul_le_mul_of_nonneg_left h6 hc1
      linarith
    · have := hch hk'
      have hDE : X ^ (D * (R.iface.d₀ + 1)) ≤ X ^ E :=
        pow_le_pow_N (by simp only [hE, Rest.expo]; omega)
      have e : ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ * (nd.S.N + 2) ^ (D * (R.iface.d₀ + 1)) :
          ℕ) : ℝ) = ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) *
            X ^ (D * (R.iface.d₀ + 1)) := by rw [hX]; push_cast; ring
      rw [e] at this
      have := mul_le_mul_of_nonneg_left hDE hc2
      linarith
  -- the overhead
  have h6 : X ^ 6 ≤ X ^ E := pow_le_pow_N (by simp only [hE, Rest.expo]; omega)
  have hw := work_le R nd hm hk hs hW h2 h3
  have e : ((10 ^ 6 * (nd.S.N + 2) ^ 6 : ℕ) : ℝ) = ((10 ^ 6 : ℕ) : ℝ) * X ^ 6 := by
    rw [hX]; push_cast; ring
  rw [e] at hw
  have h6' := mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg (α := ℝ) (10 ^ 6))
  have e2 : (((R.cImpl + A + A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ E) =
      (((cS : ℕ) : ℝ) * X ^ E + A * X ^ E) +
      ((10 ^ 6 : ℕ) : ℝ) * X ^ E +
      (((R.iface.K₀ * (10 ^ 4 + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ E +
        ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ E) := by
    simp only [Rest.cImpl]; push_cast; ring
  rw [e2]
  linarith

/-- Two quasi-polynomial bounds add up to one: `E_a + E_b ≤ E_{a + b + 3}` for `a, b ≥ 0`. -/
theorem expLogSq_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    expLogSq a N + expLogSq b N ≤ expLogSq (a + b + 3) N := by
  unfold expLogSq
  set L := Real.log ((N : ℝ) + 2) ^ 2 with hL
  have hl2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [N.cast_nonneg (α := ℝ)])
  have hl := Real.log_two_gt_d9
  have hL0 : (0.48 : ℝ) ≤ L := by rw [hL]; nlinarith
  have h1 : Real.exp (a * L) ≤ Real.exp ((a + b) * L) := Real.exp_le_exp.2 (by nlinarith)
  have h2 : Real.exp (b * L) ≤ Real.exp ((a + b) * L) := Real.exp_le_exp.2 (by nlinarith)
  have h3 : (2 : ℝ) ≤ Real.exp (3 * L) := by
    have := Real.add_one_le_exp (3 * L); linarith
  have e : Real.exp ((a + b + 3) * L) = Real.exp ((a + b) * L) * Real.exp (3 * L) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp := Real.exp_pos ((a + b) * L)
  nlinarith

theorem expLogSq_nonneg (a : ℝ) (N : ℕ) : 0 ≤ expLogSq a N := (Real.exp_pos _).le

/-- **`WorkReq` for the concrete interface**, from the bounds on the remaining steps. -/
theorem Rest.workReq (R : Rest) (hR : R.Req) : R.iface.WorkReq := by
  obtain ⟨A, D, hA⟩ := hR
  set c : ℝ := ((cW + A + R.cImpl + A + A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) + 1
  have hc : (1 : ℝ) ≤ c := by have := Nat.cast_nonneg (α := ℝ) (cW + A + R.cImpl + A +
    A * R.iface.K₀ * (A + 1) ^ R.iface.d₀); linarith
  have hlc : 0 ≤ 3 * (Real.log c + R.expo D) := by
    have := Real.log_nonneg hc; have := Nat.cast_nonneg (α := ℝ) (R.expo D); positivity
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  refine ⟨A + 3 * (Real.log c + R.expo D) + 3, by positivity, fun nd hm hsz hk hs => ?_⟩
  obtain ⟨hsc, hsg, hgen, hrowT, hrow, hagg, hch⟩ := hA nd hm hsz hk hs
  set X : ℝ := (nd.S.N : ℝ) + 2 with hX
  have hX1 : (1 : ℝ) ≤ X := by have := (Nat.cast_nonneg nd.S.N : (0 : ℝ) ≤ _); linarith
  have hXE : (0 : ℝ) ≤ X ^ R.expo D := by positivity
  have hDE : X ^ D ≤ X ^ R.expo D := pow_le_pow_N (by simp only [Rest.expo]; nlinarith)
  have h90 : X ^ 90 ≤ X ^ R.expo D := pow_le_pow_N (by simp only [Rest.expo]; omega)
  have hcW : (0 : ℝ) ≤ ((cW : ℕ) : ℝ) := Nat.cast_nonneg _
  -- the case costs at most `E_A + (cW + A) X^E`
  have hWb : max 0 (R.W nd) ≤ expLogSq A nd.S.N + (((cW : ℕ) : ℝ) + A) * X ^ R.expo D := by
    have hE0 := expLogSq_nonneg A nd.S.N
    have hpos : (0 : ℝ) ≤ (((cW : ℕ) : ℝ) + A) * X ^ R.expo D := by positivity
    refine max_le (by linarith) ?_
    by_cases hk' : nd.run.kind ∈ implKinds
    · have := W_impl_le R nd hk' hk hs
      have e : ((cW * (nd.S.N + 2) ^ 90 : ℕ) : ℝ) = ((cW : ℕ) : ℝ) * X ^ 90 := by
        rw [hX]; push_cast; ring
      rw [e] at this
      have := mul_le_mul_of_nonneg_left h90 hcW
      nlinarith
    · have hAD : (A : ℝ) * X ^ D ≤ A * X ^ R.expo D := mul_le_mul_of_nonneg_left hDE hA0
      have hcWX : (0 : ℝ) ≤ ((cW : ℕ) : ℝ) * X ^ R.expo D := mul_nonneg hcW hXE
      have hsplit : (((cW : ℕ) : ℝ) + A) * X ^ R.expo D =
          ((cW : ℕ) : ℝ) * X ^ R.expo D + A * X ^ R.expo D := by ring
      rw [hsplit]
      simp only [implKinds, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hk'
      obtain ⟨h1, h2, h3, h4⟩ := hk'
      cases hkd : nd.run.kind with
      | threshold => exact absurd hkd h1
      | orbitStop => exact absurd hkd h2
      | orbitChain => exact absurd hkd h3
      | floorReset => exact absurd hkd h4
      | dispatch => simp only [Rest.W, hkd]; have := hgen (Or.inl hkd); linarith
      | normalize => simp only [Rest.W, hkd]; have := hgen (Or.inr hkd); linarith
      | rowTerminal => simp only [Rest.W, hkd]; have := hrowT hkd; linarith
      | rowColumns => simp only [Rest.W, hkd]; have := hrow hkd; linarith
      | aggregate => simp only [Rest.W, hkd]; have := hagg hkd; linarith
      | direct => simp only [Rest.W, hkd]; linarith
      | fresh => simp only [Rest.W, hkd]; linarith
  have hchildren : nd.run.kind ∉ implKinds → (nd.run.children.map R.iface.charge).sum ≤
      ((A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ * (nd.S.N + 2) ^ (D * (R.iface.d₀ + 1)) : ℕ) : ℝ) := by
    intro hk'
    by_cases hg : nd.run.kind ∈ generalKinds
    · rw [charges_general R.iface nd hg]; positivity
    · obtain ⟨hl, hc'⟩ := hch hk' hg
      exact charges_rest_le R nd hl hc'
  have hw := work_le_poly R nd hm hk hs (A := A) (D := D) hsc hsg hWb hchildren
  have hpoly : (((cW : ℕ) : ℝ) + A) * X ^ R.expo D +
      ((R.cImpl + A + A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ R.expo D ≤
      expLogSq (3 * (Real.log c + R.expo D)) nd.S.N := by
    refine le_trans ?_ (pow_le_expLogSq hc _ _)
    have e : (((cW : ℕ) : ℝ) + A) * X ^ R.expo D +
        ((R.cImpl + A + A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ R.expo D =
        (c - 1) * X ^ R.expo D := by simp only [c]; push_cast; ring
    rw [e]
    nlinarith
  have hsum := expLogSq_add_le hA0 hlc nd.S.N
  linarith

/-- **`WorkReq` restricted to the implemented kinds** (threshold, orbit chain, floor reset): if
the rest of the selector of `Continue` costs at most `A (N+2)^D` on fitting states, then every
fitting node of these kinds does work at most `exp(cw (log(N+2))²)`. -/
theorem Rest.work_le_impl (R : Rest) {A D : ℕ}
    (hsel : ∀ {Ω C : Type} (S : State Ω C), Nat.card Ω ≤ S.N → Small S →
      R.restSelB S ≤ A * ((S.N : ℝ) + 2) ^ D) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∀ nd : Node P₀, nd.run.kind ∈ implKinds → nd.m ≠ .solve →
      Nat.card nd.Ω ≤ nd.S.N → Small nd.S → R.iface.work nd ≤ expLogSq cw nd.S.N := by
  set c : ℝ := ((cW + R.cImpl + A + A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) + 1
  have hc : (1 : ℝ) ≤ c := by have := Nat.cast_nonneg (α := ℝ) (cW + R.cImpl + A +
    A * R.iface.K₀ * (A + 1) ^ R.iface.d₀); linarith
  refine ⟨3 * (Real.log c + R.expo D), by
    have := Real.log_nonneg hc; have := Nat.cast_nonneg (α := ℝ) (R.expo D); positivity,
    fun nd hk' hm hk hs => ?_⟩
  have hcont := mode_of_impl nd hk'
  set X : ℝ := (nd.S.N : ℝ) + 2 with hX
  have hX1 : (1 : ℝ) ≤ X := by have := (Nat.cast_nonneg nd.S.N : (0 : ℝ) ≤ _); linarith
  have hXE : (0 : ℝ) ≤ X ^ R.expo D := by positivity
  have h90 : X ^ 90 ≤ X ^ R.expo D := pow_le_pow_N (by simp only [Rest.expo]; omega)
  have hcW : (0 : ℝ) ≤ ((cW : ℕ) : ℝ) := Nat.cast_nonneg _
  have hWb : max 0 (R.W nd) ≤ ((cW : ℕ) : ℝ) * X ^ R.expo D := by
    have := W_impl_le R nd hk' hk hs
    have e : ((cW * (nd.S.N + 2) ^ 90 : ℕ) : ℝ) = ((cW : ℕ) : ℝ) * X ^ 90 := by
      rw [hX]; push_cast; ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left h90 hcW
    exact max_le (mul_nonneg hcW hXE) (by linarith)
  have hw := work_le_poly R nd hm hk hs (A := A) (D := D) (fun _ => hsel nd.S hk hs)
    (fun h => absurd (hcont.symm.trans h) (by simp)) hWb (fun h => absurd hk' h)
  refine hw.trans (le_trans ?_ (pow_le_expLogSq hc _ _))
  have e : ((cW : ℕ) : ℝ) * X ^ R.expo D +
      ((R.cImpl + A + A * R.iface.K₀ * (A + 1) ^ R.iface.d₀ : ℕ) : ℝ) * X ^ R.expo D =
      (c - 1) * X ^ R.expo D := by simp only [c]; push_cast; ring
  rw [e]
  nlinarith

/-- **The trusted statement for the concrete interface**: from the step specifications
(`Layout.OK`), the graph wrapper (b) and the polynomial bounds on the remaining steps
(`Rest.Req`). -/
theorem Rest.final
    (R : Rest) {Pg : Program} {L : Iface.Layout} (h : Iface.Layout.OK R.iface Pg L)
    {fm : ℕ} (hb : GraphWrapper Pg fm L.F.solve) (hR : R.Req) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  Iface.Layout.final R.iface Pg h hb (R.workReq hR)

end GI.Impl
