import Workspace.Impl.AggPT
import Workspace.Lang.Lib.Schreier

/-!
# The orbit of a test tuple under a graph group

The certificate phase asks, for a test set `T` of `κ` labels and a subgroup `A ≤ P_T`, how
`A` acts on `T`: whether the image `φ_T(A) ≤ Alt(T)` is everything (`Full`), or trivial
(`VisibleOrbit`), and one element of `A` for each coset of the kernel `ker(φ_T|_A)` (the coset
representatives of `CheckNewWindow`). All three come from one computation.

List `T` as a tuple `t = (t₁, …, t_κ)` of distinct labels. The elements of `A` move `T` to
itself, so `a ↦ π(a) ∘ t` maps `A` onto the orbit of `t` under the label group `π(A)`, and two
elements have the same image exactly when they lie in the same coset of the kernel. So

* the orbit of `t` has `|φ_T(A)|` points (`ncard_tupOrbit`);
* a transversal of the orbit is a set of coset representatives (`AggCosets.lean`).

A program keeps `A` in graph form (pairs `(a, π a)`, `PairGens`), encoded as permutations
`a ⊕ π a` of `Fin (k + q)`. The label `c` is the point `k + c` there, so the orbit of the tuple
of points `k + tᵢ` under the encoded pairs is the orbit of `t` under `π(A)`, and the orbit
program with a transversal (`Workspace/Lang/Lib/OrbitT.lean`) computes it with the action
"apply `g` to every entry" (`tupOrb_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {n : ℕ}

/-! ### Applying a permutation to a list of points -/

/-- The key of a list of points: the list of their numbers. -/
def ptsKey (xs : List (Fin n)) : List ℕ := xs.map Fin.val

theorem ptsKey_injective : Function.Injective (ptsKey (n := n)) := fun _ _ h =>
  List.map_injective_iff.mpr Fin.val_injective h

theorem isAct_mapPts : IsAct (n := n) (fun g (xs : List (Fin n)) => xs.map g) :=
  ⟨fun xs => by simp, fun g h xs => by simp [List.map_map]⟩

theorem wt_ptsKey_le (xs : List (Fin n)) :
    (natList (ptsKey xs)).wt ≤ xs.length * (2 * n + 5) + 4 := by
  have := wt_natList_le (xs := ptsKey xs) (B := n) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact i.isLt.le)
  simpa [ptsKey] using this

/-- **Applying a permutation to a list of points.** `compose` on `[encPerm σ, natList xs]` reads
`σ` at every entry of `xs`. -/
theorem composePts_spec {P : Program} {b : ℕ} (h : P.HasAt b (composeFuns b))
    (σ : Perm (Fin n)) (xs : List (Fin n)) :
    FunDet P b (.list [encPerm σ, natList (ptsKey xs)]) (natList (ptsKey (xs.map σ)))
      (10 ^ 5 * (n + xs.length + 1) ^ 3) := by
  have hE := wt_encPerm_le σ
  have hX := wt_ptsKey_le xs
  have hX' := wt_ptsKey_le (xs.map σ)
  rw [List.length_map] at hX'
  have hf : ∀ x ∈ (ptsKey xs).map Val.nat,
      FunAll P (b + 3) (.list [encPerm σ, x]) (fun w cost =>
        (∀ i : Fin n, x = .nat i → w = .nat (σ i)) ∧ cost ≤ 100 * (n + 1) ^ 2) := by
    intro x hx
    simp only [ptsKey, List.map_map, List.mem_map, Function.comp_apply] at hx
    obtain ⟨j, -, rfl⟩ := hx
    have hb : P.funs[b + 3]? = some composeF := by
      simpa [composeFuns, mapFuns, loopFuns] using h.right.single
    refine FunAll.intro hb ((Det.applyPerm (Det.arg' (rest := []) (j := 0) rfl)
      (Det.arg' (j := 1) rfl)).post fun cost hc => ⟨fun i hi => ?_, ?_⟩)
    · simp only [Val.nat.injEq] at hi
      rw [Fin.ext hi]
    · have h1 := wt_list2_le (encPerm σ) (.nat j)
      have h2 := wt_nat_le j
      have h3 := wt_nat_le (σ j)
      have h4 := j.isLt
      have h5 := (σ j).isLt
      nlinarith
  refine ((map_spec h.left hf).mono fun w cost hw => ?_)
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = (ptsKey (xs.map σ)).map Val.nat := by
    have hx : (ptsKey xs).map Val.nat = xs.map fun i : Fin n => Val.nat i.val := by
      simp [ptsKey, Function.comp_def]
    rw [hx] at hws
    have := forall₂_map_eq (l := xs) (f := fun i : Fin n => Val.nat i.val)
      (g := fun i : Fin n => Val.nat (σ i).val) (fun a _ w hw => hw a rfl) hws
    rw [this]; simp [ptsKey, Function.comp_def]
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map] at hc
  have hlen : (ptsKey xs).length = xs.length := by simp [ptsKey]
  have hs : ((ptsKey xs).map ((fun _ => 100 * (n + 1) ^ 2) ∘ Val.nat)).sum =
      xs.length * (100 * (n + 1) ^ 2) := by
    rw [show ((fun _ => 100 * (n + 1) ^ 2) ∘ Val.nat) = fun _ => 100 * (n + 1) ^ 2 from rfl,
      List.map_const', List.sum_replicate, hlen, smul_eq_mul]
  rw [hs, hlen] at hc
  have e1 : (Val.list [encPerm σ, .list ((ptsKey xs).map Val.nat)]).wt =
    (Val.list [encPerm σ, natList (ptsKey xs)]).wt := rfl
  have e2 : (Val.list ((ptsKey (xs.map σ)).map Val.nat)).wt = (natList (ptsKey (xs.map σ))).wt :=
    rfl
  rw [e1, e2] at hc
  have ha := wt_list2_le (encPerm σ) (natList (ptsKey xs))
  set M := n + xs.length + 1 with hM
  have m1 : (n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have m2 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have m3 : M ≤ M ^ 2 := Nat.le_self_pow (by omega) _
  have h1 : xs.length * (2 * n + 5) ≤ 5 * M ^ 2 := by nlinarith
  have h2 : mapK * (xs.length + 1) * ((Val.list [encPerm σ, natList (ptsKey xs)]).wt +
      (natList (ptsKey (xs.map σ))).wt + 1) ≤ mapK * M * (50 * M ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h3 : mapK * M * (50 * M ^ 2) = 50000 * M ^ 3 := by simp only [mapK]; ring
  have h4 : xs.length * (100 * (n + 1) ^ 2) ≤ 100 * M ^ 3 := by
    have : xs.length * (n + 1) ^ 2 ≤ M * M ^ 2 := Nat.mul_le_mul (by omega) m1
    have e : M * M ^ 2 = M ^ 3 := by ring
    nlinarith
  omega

/-- The action on lists of points: on `[ac, encPerm g, natList xs]`, apply `g` to every
entry. -/
theorem mapPtsAct_spec {P : Program} {f comp : ℕ} (hf : P.funs[f]? = some (permActF comp))
    (hc : P.HasAt comp (composeFuns comp)) (ac : Val) (g : Perm (Fin n)) (xs : List (Fin n)) :
    FunDet P f (.list [ac, encPerm g, natList (ptsKey xs)]) (natList (ptsKey (xs.map g)))
      (10 ^ 5 * (n + xs.length + 1) ^ 3 + (Val.list [ac, encPerm g, natList (ptsKey xs)]).wt * 20
        + 3 * (natList (ptsKey (xs.map g))).wt + 30) := by
  have d1 := Det.arg' (P := P) (vs := [ac, encPerm g, natList (ptsKey xs)]) (rest := []) (j := 1)
    rfl
  have d2 := Det.arg' (P := P) (vs := [ac, encPerm g, natList (ptsKey xs)]) (rest := []) (j := 2)
    rfl
  refine FunDet.intro hf ((Det.call (Det.mk2 d1 d2) (composePts_spec hc g xs)).mono ?_)
  have w1 := wt_list3_le ac (encPerm g) (natList (ptsKey xs))
  have w5 := wt_list2_le (encPerm g) (natList (ptsKey xs))
  have e1 : (encPerm g).wt < (Val.list [ac, encPerm g, natList (ptsKey xs)]).wt :=
    wt_le_wt_list (by simp)
  have e2 : (natList (ptsKey xs)).wt < (Val.list [ac, encPerm g, natList (ptsKey xs)]).wt :=
    wt_le_wt_list (by simp)
  omega

/-! ### The orbit program on tuples of points -/

/-- The orbit program with the action on lists of points, at base `b` (23 functions). The
action uses the composition inside the orbit program. -/
def tupOrbFuns (b : ℕ) : List Expr := orbTFuns b (b + 22) ++ [permActF (b + 12)]

/-- The cost constant of the orbit program on tuples. -/
def tupK : ℕ := 10 ^ 8

/-- **The orbit of a tuple of points.** On `[0, gens, natList x₀, B, n]`, when the orbit of
the list `x₀` under `G = ⟨gs⟩` has at most `B` points, the result is a list of pairs `(y, t)`:
the points `y` are the orbit, without repeats, and `t ∈ G` maps `x₀` to `y` entrywise; the first
pair is `(x₀, 1)`. -/
theorem tupOrb_spec {P : Program} {b : ℕ} (h : P.HasAt b (tupOrbFuns b))
    (gs : List (Perm (Fin n))) (x₀ : List (Fin n)) {B : ℕ}
    (hB : (actOrbit (fun g (xs : List (Fin n)) => xs.map g) gs x₀).ncard ≤ B) :
    FunAll P b (.list [.nat 0, .list (gs.map encPerm), natList (ptsKey x₀), .nat B, .nat n])
      (fun w cost => ∃ L : List (List (Fin n) × Perm (Fin n)), w = encPairs ptsKey L ∧
        (L.map Prod.fst).Nodup ∧
        (∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit (fun g (xs : List (Fin n)) => xs.map g) gs x₀) ∧
        (∀ p ∈ L, p.2 ∈ genGroup gs ∧ x₀.map p.2 = p.1) ∧ L.head? = some (x₀, 1) ∧
        cost ≤ tupK * (gs.length + n + B + x₀.length + 20) ^ 12) := by
  have hO := h.left
  have hA : P.funs[b + 22]? = some (permActF (b + 12)) := by
    simpa [length_orbTFuns] using h.right.single
  obtain ⟨-, -, hP, -⟩ := OrbTAt.pieces hO
  have hc : P.HasAt (b + 12) (composeFuns (b + 12)) := by simpa [Nat.add_assoc] using hP.comp
  set T := gs.length + n + B + x₀.length + 20 with hT
  set S := T ^ 2 with hS
  have hT1 : 1 ≤ T := by omega
  have hTS : T ≤ S := Nat.le_self_pow (by norm_num) T
  have hkey : ∀ y ∈ actOrbit (fun g (xs : List (Fin n)) => xs.map g) gs x₀,
      y.length = x₀.length := by
    rintro y ⟨g, -, rfl⟩; simp
  have hpt : ∀ y : List (Fin n), y.length = x₀.length → (natList (ptsKey y)).wt ≤ S := by
    intro y hy
    have := wt_ptsKey_le y
    rw [hy] at this
    have : x₀.length * (2 * n + 5) ≤ T * (2 * T) := Nat.mul_le_mul (by omega) (by omega)
    have e : T * (2 * T) = 2 * T ^ 2 := by ring
    nlinarith
  have hn3 : (n + x₀.length + 1) ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hT3 : T ^ 3 ≤ S ^ 2 := by
    rw [hS, ← pow_mul]; exact Nat.pow_le_pow_right hT1 (by norm_num)
  have H : OrbTHyp P (b + 22) ptsKey (fun g (xs : List (Fin n)) => xs.map g) gs x₀ (.nat 0) S
      (10 ^ 6 * S ^ 2) :=
    { isAct := isAct_mapPts
      key_inj := ptsKey_injective
      hn := by omega
      hm := by omega
      hac := by have := wt_nat_le 0; omega
      hkey := fun y hy => hpt y (hkey y hy)
      hfa := fun g hg y hy => (mapPtsAct_spec hA hc (.nat 0) g y).mono (by
        have hy' := hkey y hy
        have hgy : (g * 1 : Perm (Fin n)) = g := mul_one g
        have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
        have w1 := wt_list3_le (.nat 0) (encPerm g) (natList (ptsKey y))
        have w2 := wt_encPerm_le g
        have w3 := hpt y hy'
        have w4 := hpt (y.map g) (by simp [hy'])
        have hn2 : (n + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have e3 : (n + y.length + 1) ^ 3 ≤ T ^ 3 := by rw [hy']; exact hn3
        have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) S
        omega) }
  refine (orbT_spec hO H (by omega) hB).mono fun w cost hw => ?_
  obtain ⟨L, h1, h2, h3, h4, h5, h6⟩ := hw
  refine ⟨L, h1, h2, h3, h4, h5, ?_⟩
  have p6 : S ^ 2 * (10 ^ 6 * S ^ 2) = 10 ^ 6 * S ^ 4 := by ring
  have p46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have pS : S ^ 6 = T ^ 12 := by rw [hS, ← pow_mul]
  simp only [tupK, orbTK] at h6 ⊢
  omega

/-! ### The orbit of the test tuple is the image of `φ_T` -/

section Labels

variable {k q : ℕ}

/-- The labels of a list, as the points `k + c` of `Fin (k + q)`. -/
def labPts (k : ℕ) (t : List (Fin q)) : List (Fin (k + q)) := t.map (Fin.natAdd k)

theorem labPts_injective : Function.Injective (labPts (q := q) k) := fun _ _ h =>
  (List.map_injective_iff.mpr fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)) h

theorem encPair_natAdd (p : Perm (Fin k) × Perm (Fin q)) (c : Fin q) :
    encPair p (Fin.natAdd k c) = Fin.natAdd k (p.2 c) :=
  Fin.ext (by rw [encPair_eq, sumToFin_sumCongr_natAdd]; rfl)

theorem map_encPair_labPts (p : Perm (Fin k) × Perm (Fin q)) (t : List (Fin q)) :
    (labPts k t).map (encPair p) = labPts k (t.map p.2) := by
  simp [labPts, List.map_map, Function.comp_def, encPair_natAdd]

/-- **The orbit of the tuple of label points** under the encoded pairs: the tuples `σ ∘ t` for
`σ` in the group of the second parts. -/
theorem mem_tupOrbit {ps : List (Perm (Fin k) × Perm (Fin q))} {t : List (Fin q)}
    {y : List (Fin (k + q))} :
    y ∈ actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair) (labPts k t) ↔
      ∃ σ ∈ gens (ps.map Prod.snd), labPts k (t.map σ) = y := by
  show (∃ g ∈ genGroup (ps.map encPair), _) ↔ _
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨p, hp, rfl⟩ := mem_gens_encPair.1 hg
    refine ⟨p.2, ?_, (map_encPair_labPts p t).symm⟩
    rw [gens_snd]; exact ⟨p, hp, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    rw [gens_snd] at hσ
    obtain ⟨p, hp, rfl⟩ := hσ
    exact ⟨encPair p, mem_gens_encPair.2 ⟨p, hp, rfl⟩, map_encPair_labPts p t⟩

end Labels

section Img

open GI.LocalGroups GI.Endpoint

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- The test set `T` as a list of labels, in increasing order. -/
def tlist {q : ℕ} (T : Finset (Fin q)) : List (Fin q) := T.sort (· ≤ ·)

theorem mem_tlist {q : ℕ} {T : Finset (Fin q)} {c : Fin q} : c ∈ tlist T ↔ c ∈ T :=
  Finset.mem_sort _

theorem length_tlist {q : ℕ} (T : Finset (Fin q)) : (tlist T).length = T.card :=
  Finset.length_sort _

/-- The tuple of an element `ρ` of `Alt(T)`: `ρ` applied to the list of `T`. -/
def altTup {q : ℕ} (T : Finset (Fin q)) (ρ : alternatingGroup T) : List (Fin (k + q)) :=
  labPts k ((tlist T).map (ofSubtype (ρ : Perm T)))

theorem altTup_injective {q : ℕ} (T : Finset (Fin q)) :
    Function.Injective (altTup (k := k) T) := by
  intro ρ ρ' h
  have h1 := List.map_inj_left.1 (labPts_injective h)
  apply Subtype.ext
  ext ⟨c, hc⟩
  have := h1 c (mem_tlist.2 hc)
  rw [ofSubtype_apply_of_mem _ hc, ofSubtype_apply_of_mem _ hc] at this
  exact congrArg Fin.val this

variable (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **The orbit of the test tuple is the image of `φ_T`**: for `A ≤ P_T` in graph form, the
orbit of the label points of `T` under the encoded pairs is the set of tuples of the elements
of `φ_T(A)`. -/
theorem tupOrbit_eq (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) {T : Finset (Fin L.q)}
    {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps) :
    actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (ps.map encPair)
      (labPts k (tlist T)) = altTup T '' (img (phiT S.domGroup πd T) A : Set _) := by
  ext y
  rw [mem_tupOrbit]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨g, hg, hgA, rfl⟩ := (mem_gens_snd hps σ).1 hσ
    obtain ⟨hg', haA⟩ := State.mem_liftGroup.1 hgA
    set a := S.domHom ⟨g, hg⟩ with ha
    replace haA : a ∈ A := haA
    have hP : a ∈ Pgrp S.domGroup πd T := hA haA
    refine ⟨phiT S.domGroup πd T ⟨a, hP⟩, (mem_img _).2 ⟨⟨a, hP⟩, haA, rfl⟩, ?_⟩
    unfold altTup
    congr 1
    refine List.map_congr_left fun c hc => ?_
    have hcT := mem_tlist.1 hc
    rw [ofSubtype_apply_of_mem _ hcT]
    rw [phiT_apply, lab_of_mem (show a ∈ S.domGroup from ⟨⟨g, hg⟩, rfl⟩), ← hπ ⟨g, hg⟩]
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨⟨a, hP⟩, haA, rfl⟩ := (mem_img _).1 hρ
    have hdom : a ∈ S.domGroup := (Pgrp_le (G := S.domGroup) hP)
    obtain ⟨⟨g, hg⟩, hga⟩ := hdom
    refine ⟨(L.π ⟨g, hg⟩ : Perm (Fin L.q)), (mem_gens_snd hps _).2
      ⟨g, hg, State.mem_liftGroup.2 ⟨hg, by rw [hga]; exact haA⟩, rfl⟩, ?_⟩
    unfold altTup
    congr 1
    refine List.map_congr_left fun c hc => ?_
    have hcT := mem_tlist.1 hc
    rw [ofSubtype_apply_of_mem _ hcT, phiT_apply]
    subst hga
    rw [lab_of_mem (show S.domHom ⟨g, hg⟩ ∈ S.domGroup from ⟨⟨g, hg⟩, rfl⟩), hπ ⟨g, hg⟩]

/-- **The size of the orbit is the order of `φ_T(A)`.** -/
theorem ncard_tupOrbit (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps) :
    (actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (ps.map encPair)
      (labPts k (tlist T))).ncard = Nat.card (img (phiT S.domGroup πd T) A) := by
  rw [tupOrbit_eq πd hπ hA hps, Set.ncard_image_of_injective _ (altTup_injective T),
    ← Nat.card_coe_set_eq]
  rfl

end Img

end GI.Impl
