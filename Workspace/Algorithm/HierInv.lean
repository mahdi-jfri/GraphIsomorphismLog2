import Workspace.Algorithm.Interfaces

/-!
# The hierarchy invariant of reachable states

Section 3.3: "A block system is a partition of `Ω` that every allowed relabeling permutes. …
We keep a hierarchy of such partitions down to singletons. … When a recursive call restricts
the allowed relabelings and selects one orbit, it intersects the old partitions with that
orbit. The old hierarchy is retained; new invariant partitions only refine it. … When an
interval of new ratio `d'` inherits a bound `c`, we store `min{c, d'}`. Thus every stored bound
is at most its current interval ratio, including after an orbit restriction."

Section 6.1: "At a fresh intransitive instance, initialize the hierarchy and interval bounds on
each original orbit … Every later call inherits the state of the original orbit containing it."

Section 7.1: "Every eventual child is an actual subgroup-orbit restriction of that original
action and inherits its tower."

This file states what the recursion keeps true about the hierarchy (`HierInv`). The hierarchy
is a list of intervals, from the finest to the coarsest. The fine end of the first interval is
the partition into points (`⊥`), and the fine end of each later interval is the coarse end of
the one before. On the active domain `D` of a group `G`:

* every coarse end is `G`-invariant, and coarser than its fine end (`Chain`);
* the stored ratio of an interval bounds the number of fine classes in one coarse class of one
  orbit (`Chain`, the count `classCount`). After an orbit restriction the true number can only
  drop. So a stored ratio is an upper bound for the current ratio, and it is exact at the start
  of a phase and wherever the recursion recomputes it (the exposed quotient,
  `Workspace/Algorithm/Expose.lean`);
* every stored bound is at most its stored ratio (`Chain`, "every stored bound is at most its
  current interval ratio");
* the last coarse end puts each orbit of `G` in one class (`TopOn`): the hierarchy reaches the
  whole orbit.

Since the conditions are about orbits, one list of partitions of `Ω` holds the hierarchies of
all original orbits at once: on each orbit it is that orbit's hierarchy. A fresh state stores
the one-interval hierarchy from the points to the orbits (`orbitHier`), which is the initial
hierarchy of every original orbit, with the size of a largest orbit as its ratio and bound.

The invariant passes to a subgroup on a smaller domain (`HierInv.mono`): the partitions stay
invariant, and an orbit of the subgroup lies in an orbit of the group, so it meets no more fine
classes. A cap update keeps it (`HierInv.capUpdate`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω : Type}

/-! ### Counting classes -/

/-- The number of classes of `f` that meet the set `X`: the size of the quotient of `X` by `f`. -/
noncomputable def classCount (f : Setoid Ω) (X : Set Ω) : ℕ :=
  Nat.card (Quotient (Setoid.comap (Subtype.val : X → Ω) f))

/-- A subset meets no more classes. -/
theorem classCount_mono [Finite Ω] (f : Setoid Ω) {X Y : Set Ω} (h : X ⊆ Y) :
    classCount f X ≤ classCount f Y := by
  unfold classCount
  refine Nat.card_le_card_of_injective
    (Quotient.map (Set.inclusion h) (fun a b hab => hab)) ?_
  intro a b hab
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp only [Quotient.map_mk] at hab
  have hr := Quotient.exact hab
  exact Quotient.sound hr

/-- Two partitions that agree on `X` meet `X` in the same number of classes. -/
theorem classCount_congr {f f' : Setoid Ω} {X : Set Ω}
    (h : ∀ v ∈ X, ∀ w ∈ X, f.r v w ↔ f'.r v w) : classCount f X = classCount f' X := by
  have : Setoid.comap (Subtype.val : X → Ω) f = Setoid.comap Subtype.val f' := by
    ext a b
    exact h a a.2 b b.2
  unfold classCount
  rw [this]

/-- A permutation that maps `X` onto `Y` and keeps the relation `f` on `X` maps the classes. -/
theorem classCount_image (f : Setoid Ω) (g : Perm Ω) (X : Set Ω)
    (h : ∀ v ∈ X, ∀ w ∈ X, f.r (g v) (g w) ↔ f.r v w) :
    classCount f (g '' X) = classCount f X := by
  unfold classCount
  refine Nat.card_congr (Quotient.congr (Equiv.Set.image g X g.injective).symm ?_)
  rintro ⟨_, v, hv, rfl⟩ ⟨_, w, hw, rfl⟩
  have e1 : (Equiv.Set.image g X g.injective).symm ⟨g v, v, hv, rfl⟩ = ⟨v, hv⟩ := by
    rw [Equiv.symm_apply_eq]; rfl
  have e2 : (Equiv.Set.image g X g.injective).symm ⟨g w, w, hw, rfl⟩ = ⟨w, hw⟩ := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [e1, e2]
  exact h v hv w hw

/-- The points of `X` are the classes of `⊥`. -/
theorem classCount_bot (X : Set Ω) : classCount ⊥ X = Nat.card X := by
  unfold classCount
  refine (Nat.card_eq_of_bijective (Quotient.mk _) ⟨fun a b hab => ?_,
    Quotient.mk_surjective⟩).symm
  have := Quotient.exact hab
  exact Subtype.ext this

/-- A nonempty set meets at least one class. -/
theorem one_le_classCount [Finite Ω] (f : Setoid Ω) {X : Set Ω} (h : X.Nonempty) :
    1 ≤ classCount f X := by
  obtain ⟨v, hv⟩ := h
  unfold classCount
  exact Nat.card_pos_iff.2 ⟨⟨Quotient.mk _ ⟨v, hv⟩⟩, inferInstance⟩

/-! ### The invariant -/

/-- The coarse end of the last interval of `l`, or `f` when `l` is empty. Starting from `⊥`, it
is the coarsest partition of the hierarchy. -/
def fineEnd (f : Setoid Ω) (l : List (Interval Ω)) : Setoid Ω := l.foldl (fun _ I => I.part) f

@[simp] theorem fineEnd_nil (f : Setoid Ω) : fineEnd f [] = f := rfl

@[simp] theorem fineEnd_cons (f : Setoid Ω) (I : Interval Ω) (l : List (Interval Ω)) :
    fineEnd f (I :: l) = fineEnd I.part l := rfl

theorem fineEnd_take_succ : ∀ (f : Setoid Ω) (l : List (Interval Ω)) (j : ℕ) (h : j < l.length),
    fineEnd f (l.take (j + 1)) = l[j].part
  | _, [], _, h => absurd h (by simp)
  | _, I :: l, 0, _ => by simp [fineEnd]
  | _, I :: l, j + 1, h => by
    rw [List.take_succ_cons, fineEnd_cons, fineEnd_take_succ I.part l j (by simpa using h)]
    rfl

theorem fineEnd_take_zero (f : Setoid Ω) (l : List (Interval Ω)) : fineEnd f (l.take 0) = f := by
  simp [fineEnd]

theorem fineEnd_append (f : Setoid Ω) (l₁ l₂ : List (Interval Ω)) :
    fineEnd f (l₁ ++ l₂) = fineEnd (fineEnd f l₁) l₂ := List.foldl_append

/-- The points of one coarse class of `a` in its `G`-orbit, inside `D`. -/
def classIn (G : Subgroup (Perm Ω)) (D : Set Ω) (c : Setoid Ω) (a : Ω) : Set Ω :=
  {w | w ∈ D ∧ w ∈ orb G a ∧ c.r a w}

theorem mem_orb_mono {G G' : Subgroup (Perm Ω)} (hG : G' ≤ G) {a w : Ω} (h : w ∈ orb G' a) :
    w ∈ orb G a := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, hG hg, rfl⟩

theorem classIn_mono {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} (hG : G' ≤ G) (hD : D' ⊆ D)
    (c : Setoid Ω) (a : Ω) : classIn G' D' c a ⊆ classIn G D c a :=
  fun _ ⟨h1, h2, h3⟩ => ⟨hD h1, mem_orb_mono hG h2, h3⟩


/-! ### The meaning of a stored bound

Section 3.3: "Each interval of the hierarchy also carries an upper bound `c_i` on the alternating
sections that can occur in that interval. A section means a quotient of a subgroup. … An interval
bound `c_i` is a bound on this quantity [the alternating width] for its entire constituent
action."

The constituent action of an interval at a point `a` is the action of the stabilizer of the
coarse class of `a` on the fine classes inside it. `CapAt G D f c b a` says that every
alternating section `Alt(t)`, `t ≥ 5`, of this action has `t ≤ b`: for every subgroup `U` of `G`
that keeps the coarse class of `a`, and every map of `U` onto `Alt(t)` that kills the elements
fixing every fine class of that coarse class (so that it is a section of the constituent action),
`t ≤ b`. So `CapAt` is "the alternating width of the constituent action is at most `b`": such
a map factors through the image of `U` in the permutations of the fine classes, and conversely
a section of that image pulls back to its preimage in the stabilizer. -/

/-- **The bound `b` is valid for the constituent action at `a`** of the interval from `f` to
`c`: every alternating section of degree `t ≥ 5` of the action of the stabilizer of the coarse
class of `a` on the fine classes inside it has `t ≤ b`. -/
def CapAt (G : Subgroup (Perm Ω)) (D : Set Ω) (f c : Setoid Ω) (b : ℕ) (a : Ω) : Prop :=
  ∀ U : Subgroup (Perm Ω), U ≤ G → (∀ u ∈ U, u a ∈ classIn G D c a) →
    ∀ t : ℕ, 5 ≤ t → ∀ φ : U →* alternatingGroup (Fin t), Function.Surjective φ →
      (∀ u : U, (∀ w ∈ classIn G D c a, f.r ((u : Perm Ω) w) w) → φ u = 1) → t ≤ b

/-- The bound is valid at every point of the domain. -/
def CapOK (G : Subgroup (Perm Ω)) (D : Set Ω) (f c : Setoid Ω) (b : ℕ) : Prop :=
  ∀ a ∈ D, CapAt G D f c b a

/-- **The caps of a hierarchy are valid**, read from the fine end `f`. -/
def Caps (G : Subgroup (Perm Ω)) (D : Set Ω) : Setoid Ω → List (Interval Ω) → Prop
  | _, [] => True
  | f, I :: l => CapOK G D f I.part I.cap ∧ Caps G D I.part l

theorem CapAt.le {G : Subgroup (Perm Ω)} {D : Set Ω} {f c : Setoid Ω} {b b' : ℕ} {a : Ω}
    (h : CapAt G D f c b a) (hb : b ≤ b') : CapAt G D f c b' a :=
  fun U hU hUa t ht φ hφ hk => (h U hU hUa t ht φ hφ hk).trans hb

theorem CapAt.min {G : Subgroup (Perm Ω)} {D : Set Ω} {f c : Setoid Ω} {b b' : ℕ} {a : Ω}
    (h : CapAt G D f c b a) (h' : CapAt G D f c b' a) : CapAt G D f c (min b b') a :=
  fun U hU hUa t ht φ hφ hk => le_min (h U hU hUa t ht φ hφ hk) (h' U hU hUa t ht φ hφ hk)

/-- **A sub-interval keeps the bound** (Section 3.3: "it ensures that the bound remains valid
after further restrictions and quotient actions"). If every element of the smaller group that
keeps the new coarse class of `a` keeps the old one, and fixes every new fine class there when
it fixes every old fine class of the old coarse class, then the constituent at `a` of the new
interval is a section of the old one. -/
theorem CapAt.sub {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} {f c f' c' : Setoid Ω} {b : ℕ}
    {a : Ω} (h : CapAt G D f c b a) (hG : G' ≤ G)
    (hcls : ∀ u ∈ G', u a ∈ classIn G' D' c' a → u a ∈ classIn G D c a)
    (hfix : ∀ u ∈ G', u a ∈ classIn G' D' c' a → (∀ w ∈ classIn G D c a, f.r (u w) w) →
      ∀ w ∈ classIn G' D' c' a, f'.r (u w) w) :
    CapAt G' D' f' c' b a := by
  intro U hU hUa t ht φ hφ hk
  refine h U (hU.trans hG) (fun u hu => hcls u (hU hu) (hUa u hu)) t ht φ hφ fun u hu => ?_
  exact hk u (hfix u (hU u.2) (hUa u u.2) hu)

theorem classIn_mem_self {G : Subgroup (Perm Ω)} {D : Set Ω} (c : Setoid Ω) {a : Ω}
    (ha : a ∈ D) : a ∈ classIn G D c a :=
  ⟨ha, ⟨1, G.one_mem, rfl⟩, c.refl a⟩

/-- **The constituent at `a` passes to a subgroup on a smaller domain.** -/
theorem CapAt.mono {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} {f c : Setoid Ω} {b : ℕ} {a : Ω}
    (h : CapAt G D f c b a) (hG : G' ≤ G) (hD : D' ⊆ D) : CapAt G' D' f c b a :=
  h.sub hG (fun _ _ hu => classIn_mono hG hD c a hu)
    (fun _ _ _ hfix w hw => hfix w (classIn_mono hG hD c a hw))

theorem CapOK.mono {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} {f c : Setoid Ω} {b : ℕ}
    (h : CapOK G D f c b) (hG : G' ≤ G) (hD : D' ⊆ D) : CapOK G' D' f c b :=
  fun a ha => (h a (hD ha)).mono hG hD

theorem Caps.mono {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} (hG : G' ≤ G) (hD : D' ⊆ D) :
    ∀ {f : Setoid Ω} {l : List (Interval Ω)}, Caps G D f l → Caps G' D' f l
  | _, [], _ => trivial
  | _, _ :: _, ⟨h1, h2⟩ => ⟨h1.mono hG hD, Caps.mono hG hD h2⟩

/-- An element of `G` that moves `a` inside its coarse class maps the class into itself, when
the domain and the coarse partition are `G`-invariant. -/
theorem classIn_maps {G : Subgroup (Perm Ω)} {D : Set Ω} {c : Setoid Ω} (hD : Invariant G D)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w) {a : Ω} {g : Perm Ω}
    (hg : g ∈ G) (hga : g a ∈ classIn G D c a) {w : Ω} (hw : w ∈ classIn G D c a) :
    g w ∈ classIn G D c a := by
  obtain ⟨hwD, ⟨k, hk, rfl⟩, hcw⟩ := hw
  have haD : a ∈ D := (hD k hk a).1 hwD
  refine ⟨(hD g hg _).2 hwD, ⟨g * k, G.mul_mem hg hk, rfl⟩, ?_⟩
  exact c.trans hga.2.2 ((hc g hg a haD (k a) hwD).2 hcw)

/-- With invariance, an element of `G` that moves `a` inside its coarse class has an inverse
that does the same. -/
theorem classIn_inv_mem {G : Subgroup (Perm Ω)} {D : Set Ω} {c : Setoid Ω} (hD : Invariant G D)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w) {a : Ω} {g : Perm Ω}
    (hg : g ∈ G) (hga : g a ∈ classIn G D c a) : g⁻¹ a ∈ classIn G D c a := by
  have haD : a ∈ D := hga.1 |> fun h => (hD g hg a).1 h
  have hiD : g⁻¹ a ∈ D := hD.inv_mem hg haD
  refine ⟨hiD, ⟨g⁻¹, G.inv_mem hg, rfl⟩, ?_⟩
  have := (hc g hg (g⁻¹ a) hiD a haD).1
  simp only [Perm.apply_inv_self] at this
  exact c.symm (this hga.2.2)

/-- The action of `U` on the fine classes inside a set `X` that `U` keeps, as permutations. -/
noncomputable def classPermHom {U : Subgroup (Perm Ω)} {X : Set Ω} {f : Setoid Ω}
    (hX : ∀ u ∈ U, ∀ w ∈ X, u w ∈ X)
    (hf : ∀ u ∈ U, ∀ v ∈ X, ∀ w ∈ X, f.r (u v) (u w) ↔ f.r v w) :
    U →* Perm (Quotient (Setoid.comap (Subtype.val : X → Ω) f)) where
  toFun u :=
    { toFun := Quotient.map (fun w : X => ⟨(u : Perm Ω) w, hX u u.2 w w.2⟩)
        fun v w h => (hf u u.2 v v.2 w w.2).2 h
      invFun := Quotient.map (fun w : X => ⟨(u⁻¹ : Perm Ω) w, hX _ (U.inv_mem u.2) w w.2⟩)
        fun v w h => (hf _ (U.inv_mem u.2) v v.2 w w.2).2 h
      left_inv := fun x => by
        induction x using Quotient.inductionOn with
        | h w =>
          simp only [Quotient.map_mk]
          congr 1
          exact Subtype.ext (by simp)
      right_inv := fun x => by
        induction x using Quotient.inductionOn with
        | h w =>
          simp only [Quotient.map_mk]
          congr 1
          exact Subtype.ext (by simp) }
  map_one' := by
    ext x
    induction x using Quotient.inductionOn with
    | h w => rfl
  map_mul' u v := by
    ext x
    induction x using Quotient.inductionOn with
    | h w => rfl

theorem classPermHom_eq_one {U : Subgroup (Perm Ω)} {X : Set Ω} {f : Setoid Ω}
    (hX : ∀ u ∈ U, ∀ w ∈ X, u w ∈ X)
    (hf : ∀ u ∈ U, ∀ v ∈ X, ∀ w ∈ X, f.r (u v) (u w) ↔ f.r v w) {u : U}
    (h : classPermHom hX hf u = 1) : ∀ w ∈ X, f.r ((u : Perm Ω) w) w := by
  intro w hw
  have := congrArg (fun p => p (Quotient.mk _ ⟨w, hw⟩)) h
  simp only [classPermHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Quotient.map_mk,
    Perm.one_apply] at this
  exact Quotient.exact (s := Setoid.comap (Subtype.val : X → Ω) f) this

theorem classPermHom_eq_one_iff {U : Subgroup (Perm Ω)} {X : Set Ω} {f : Setoid Ω}
    (hX : ∀ u ∈ U, ∀ w ∈ X, u w ∈ X)
    (hf : ∀ u ∈ U, ∀ v ∈ X, ∀ w ∈ X, f.r (u v) (u w) ↔ f.r v w) (u : U) :
    classPermHom hX hf u = 1 ↔ ∀ w ∈ X, f.r ((u : Perm Ω) w) w := by
  refine ⟨classPermHom_eq_one hX hf, fun h => ?_⟩
  ext x
  induction x using Quotient.inductionOn with
  | h w => exact Quotient.sound (h w.1 w.2)

/-- A valid bound below `5` bounds nothing: every bound is then valid. -/
theorem CapAt.of_lt_five {G : Subgroup (Perm Ω)} {D : Set Ω} {f c : Setoid Ω} {r : ℕ} {a : Ω}
    (h : CapAt G D f c r a) (hr : r < 5) (b : ℕ) : CapAt G D f c b a :=
  fun U hU hUa t ht φ hφ hk => absurd (h U hU hUa t ht φ hφ hk) (by omega)

/-- **Moving an alternating section to another subgroup.** Let `ρ : K → P`, and `U, V₀ ≤ K`.
If `φ : U ↠ Alt(t)` kills the kernel of `ρ` on `U`, and every element of `U` has the same image
under `ρ` as some element of `V₀`, then some `V ≤ V₀` maps onto `Alt(t)` by a map that kills
the kernel of `ρ` on `V`. -/
theorem section_transfer {K V₀ U : Subgroup (Perm Ω)} {P : Type*} [Group P] (ρ : K →* P)
    (hU : U ≤ K) (hV₀ : V₀ ≤ K) {t : ℕ} (φ : U →* alternatingGroup (Fin t))
    (hφ : Function.Surjective φ) (hk : ∀ u : U, ρ (Subgroup.inclusion hU u) = 1 → φ u = 1)
    (hcorr : ∀ u : U, ∃ v : V₀, ρ (Subgroup.inclusion hV₀ v) = ρ (Subgroup.inclusion hU u)) :
    ∃ (V : Subgroup (Perm Ω)) (hV : V ≤ V₀) (φ' : V →* alternatingGroup (Fin t)),
      Function.Surjective φ' ∧
        ∀ v : V, ρ (Subgroup.inclusion (hV.trans hV₀) v) = 1 → φ' v = 1 := by
  let p : U →* P := ρ.comp (Subgroup.inclusion hU)
  have hpk : p.rangeRestrict.ker ≤ φ.ker := fun u hu => hk u (congrArg Subtype.val hu)
  let φb := GI.HomDescent.factor p.rangeRestrict (GI.QuotientImage.range_surjective p) φ hpk
  let ρV : V₀ →* P := ρ.comp (Subgroup.inclusion hV₀)
  let V' : Subgroup V₀ := p.range.comap ρV
  refine ⟨V'.map V₀.subtype, Subgroup.map_subtype_le _, ?_⟩
  -- the map `V → p.range`
  have hmem : ∀ v : V'.map V₀.subtype, ∃ w : V₀, w ∈ V' ∧ (w : Perm Ω) = v := fun v => by
    obtain ⟨w, hw, he⟩ := v.2
    exact ⟨w, hw, he⟩
  let back : V'.map V₀.subtype →* V₀ := Subgroup.inclusion (Subgroup.map_subtype_le V')
  have hback : ∀ v : V'.map V₀.subtype, back v ∈ V' := fun v => by
    obtain ⟨w, hw, he⟩ := hmem v
    have : back v = w := Subtype.ext he.symm
    rw [this]; exact hw
  let ψ : V'.map V₀.subtype →* p.range :=
    (ρV.comp back).codRestrict p.range fun v => hback v
  have hinc : ∀ v : V'.map V₀.subtype,
      Subgroup.inclusion ((Subgroup.map_subtype_le V').trans hV₀) v =
        Subgroup.inclusion hV₀ (back v) := fun _ => rfl
  refine ⟨φb.comp ψ, ?_, fun v hv => ?_⟩
  · intro σ
    obtain ⟨y, hy⟩ := GI.HomDescent.factor_surjective _ _ φ hpk hφ σ
    obtain ⟨u, hu⟩ := GI.QuotientImage.range_surjective p y
    obtain ⟨w, hw⟩ := hcorr u
    have hwV : w ∈ V' := by
      show ρV w ∈ p.range
      exact ⟨u, hw.symm⟩
    refine ⟨⟨w, w, hwV, rfl⟩, ?_⟩
    have : ψ ⟨w, w, hwV, rfl⟩ = y := by
      apply Subtype.ext
      rw [← hu]
      show ρV (back ⟨w, w, hwV, rfl⟩) = p u
      have : back ⟨w, w, hwV, rfl⟩ = w := Subtype.ext rfl
      rw [this]
      exact hw
    show φb (ψ _) = σ
    rw [this, hy]
  · have : ψ v = 1 := by
      apply Subtype.ext
      show ρ (Subgroup.inclusion hV₀ (back v)) = 1
      rw [← hinc]; exact hv
    show φb (ψ v) = 1
    rw [this, map_one]

/-- **The bound at a point moves along the group** (the constituents at `a` and at `g a` are
conjugate). -/
theorem CapAt.conj {G : Subgroup (Perm Ω)} {D : Set Ω} {f c : Setoid Ω} {b : ℕ} {a : Ω}
    (h : CapAt G D f c b a) (hD : Invariant G D)
    (hf : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, f.r (g v) (g w) ↔ f.r v w)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w) {g : Perm Ω} (hg : g ∈ G)
    (ha : a ∈ D) : CapAt G D f c b (g a) := by
  -- the class of `g a` is the image of the class of `a`
  have himg : ∀ w, w ∈ classIn G D c (g a) ↔ g⁻¹ w ∈ classIn G D c a := by
    intro w
    constructor
    · rintro ⟨hw, ⟨k, hk, rfl⟩, hcw⟩
      refine ⟨hD.inv_mem hg hw, ⟨g⁻¹ * k * g, G.mul_mem (G.mul_mem (G.inv_mem hg) hk) hg, ?_⟩, ?_⟩
      · simp [Perm.mul_apply]
      · have := (hc g hg a ha (g⁻¹ (k (g a))) (hD.inv_mem hg hw)).1
        simp only [Perm.apply_inv_self] at this
        exact this hcw
    · rintro ⟨hw, ⟨k, hk, hkw⟩, hcw⟩
      have hw' : w ∈ D := by have := (hD g hg (g⁻¹ w)).2 hw; simpa using this
      refine ⟨hw', ⟨g * k * g⁻¹, G.mul_mem (G.mul_mem hg hk) (G.inv_mem hg), ?_⟩, ?_⟩
      · simp [Perm.mul_apply, hkw]
      · have := (hc g hg a ha (g⁻¹ w) hw).2 hcw
        simpa using this
  intro U hU hUa t ht φ hφ hk
  let cj : Perm Ω →* Perm Ω := MulAut.conj g⁻¹
  have hinj : Function.Injective cj := (MulAut.conj g⁻¹).injective
  let U' : Subgroup (Perm Ω) := U.map cj
  let e : U ≃* U' := U.equivMapOfInjective cj hinj
  have hcj : ∀ x, cj x = g⁻¹ * x * g := fun x => by simp [cj]
  refine h U' ?_ ?_ t ht (φ.comp e.symm.toMonoidHom) (hφ.comp e.symm.surjective) ?_
  · rintro _ ⟨u, hu, rfl⟩
    rw [hcj]
    exact G.mul_mem (G.mul_mem (G.inv_mem hg) (hU hu)) hg
  · rintro _ ⟨u, hu, rfl⟩
    rw [hcj]
    have := (himg (u (g a))).1 (hUa u hu)
    simpa [Perm.mul_apply] using this
  · intro u' hu'
    obtain ⟨u, rfl⟩ := e.surjective u'
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    refine hk u fun w hw => ?_
    have hw' := (himg w).1 hw
    have h1 := hu' (g⁻¹ w) hw'
    have he : ((e u : U') : Perm Ω) = g⁻¹ * u * g := by
      rw [← hcj]; rfl
    rw [he] at h1
    simp only [Perm.mul_apply, Perm.apply_inv_self] at h1
    have huD : (u : Perm Ω) w ∈ D := (hD u (hU u.2) w).2 hw.1
    have := (hf g hg (g⁻¹ ((u : Perm Ω) w)) (hD.inv_mem hg huD) (g⁻¹ w) (hD.inv_mem hg hw.1)).2 h1
    simpa using this

/-- The stabilizer in `G` of the class of `a`, when the coarse partition is a block system. -/
def classStab (G : Subgroup (Perm Ω)) (D : Set Ω) (c : Setoid Ω) (a : Ω) (hD : Invariant G D)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w) (ha : a ∈ D) :
    Subgroup (Perm Ω) where
  carrier := {u | u ∈ G ∧ u a ∈ classIn G D c a}
  mul_mem' := fun {u v} hu hv => ⟨G.mul_mem hu.1 hv.1, by
    show u (v a) ∈ _
    exact classIn_maps hD hc hu.1 hu.2 hv.2⟩
  one_mem' := ⟨G.one_mem, classIn_mem_self c ha⟩
  inv_mem' := fun {u} hu => ⟨G.inv_mem hu.1, classIn_inv_mem hD hc hu.1 hu.2⟩

/-- **Moving a bound to a coarser interval** (Lemma A.14: the upper pieces of the column step).
Let the old coarse class of `a` lie in the new one. Assume that an element of `G` that keeps the
old class and fixes each old fine class in it also fixes each new fine class in the new class.
Assume also that every element of `G` that keeps the new class acts on the new fine classes
there as some element that keeps the old class. Then the new constituent at `a` is a section of
the old one, so the old bound holds for it. -/
theorem CapAt.transfer {G : Subgroup (Perm Ω)} {D : Set Ω} {f c f' c' : Setoid Ω} {b : ℕ}
    {a : Ω} (h : CapAt G D f c b a) (hD : Invariant G D) (ha : a ∈ D)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w)
    (hc' : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c'.r (g v) (g w) ↔ c'.r v w)
    (hf' : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, f'.r (g v) (g w) ↔ f'.r v w)
    (hsub : ∀ w ∈ classIn G D c a, w ∈ classIn G D c' a)
    (hker : ∀ v ∈ G, v a ∈ classIn G D c a → (∀ w ∈ classIn G D c a, f.r (v w) w) →
      ∀ w ∈ classIn G D c' a, f'.r (v w) w)
    (hcorr : ∀ u ∈ G, u a ∈ classIn G D c' a → ∃ v ∈ G, v a ∈ classIn G D c a ∧
      ∀ w ∈ classIn G D c' a, f'.r (v w) (u w)) :
    CapAt G D f' c' b a := by
  intro U hU hUa t ht φ hφ hk
  set X := classIn G D c' a
  let K := classStab G D c' a hD hc' ha
  let V₀ := classStab G D c a hD hc ha
  have hKG : K ≤ G := fun u hu => hu.1
  have hUK : U ≤ K := fun u hu => ⟨hU hu, hUa u hu⟩
  have hV₀K : V₀ ≤ K := fun v hv => ⟨hv.1, hsub _ hv.2⟩
  have hX : ∀ u ∈ K, ∀ w ∈ X, u w ∈ X := fun u hu w hw => classIn_maps hD hc' hu.1 hu.2 hw
  have hfX : ∀ u ∈ K, ∀ v ∈ X, ∀ w ∈ X, f'.r (u v) (u w) ↔ f'.r v w :=
    fun u hu v hv w hw => hf' u hu.1 v hv.1 w hw.1
  let ρ := classPermHom hX hfX
  obtain ⟨V, hV, φ', hφ', hk'⟩ := section_transfer ρ hUK hV₀K φ hφ
    (fun u hu => hk u ((classPermHom_eq_one_iff hX hfX _).1 hu)) fun u => by
      obtain ⟨v, hvG, hva, hvw⟩ := hcorr u (hU u.2) (hUa u u.2)
      refine ⟨⟨v, hvG, hva⟩, ?_⟩
      ext x
      induction x using Quotient.inductionOn with
      | h w => exact Quotient.sound (hvw w.1 w.2)
  refine h V (hV.trans fun v hv => hv.1) (fun v hv => (hV hv).2) t ht φ' hφ' fun v hv => ?_
  refine hk' v ((classPermHom_eq_one_iff hX hfX _).2 ?_)
  exact hker v (hV v.2).1 (hV v.2).2 hv

/-- **The ratio is a valid bound** (Section 3.3: "The initial bound `c_i = d_i` is always
available"): the constituent at `a` permutes the fine classes of the coarse class of `a`, so its
alternating sections have degree at most their number. -/
theorem capAt_of_count [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} {f c : Setoid Ω} {r : ℕ}
    {a : Ω} (hD : Invariant G D)
    (hf : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, f.r (g v) (g w) ↔ f.r v w)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w)
    (hr : classCount f (classIn G D c a) ≤ r) : CapAt G D f c r a := by
  classical
  intro U hU hUa t ht φ hφ hk
  have hX : ∀ u ∈ U, ∀ w ∈ classIn G D c a, u w ∈ classIn G D c a :=
    fun u hu w hw => classIn_maps hD hc (hU hu) (hUa u hu) hw
  have hfX : ∀ u ∈ U, ∀ v ∈ classIn G D c a, ∀ w ∈ classIn G D c a,
      f.r (u v) (u w) ↔ f.r v w := fun u hu v hv w hw => hf u (hU hu) v hv.1 w hw.1
  let p := classPermHom hX hfX
  letI : Fintype (Quotient (Setoid.comap (Subtype.val : classIn G D c a → Ω) f)) :=
    Fintype.ofFinite _
  have hcap := GI.SectionCaps.permutations
    (V := Quotient (Setoid.comap (Subtype.val : classIn G D c a → Ω) f))
  have := GI.SectionCaps.quotient_degree_le hcap ht p φ hφ fun u hu =>
    hk u (classPermHom_eq_one hX hfX hu)
  refine this.trans (le_trans (le_of_eq ?_) hr)
  rw [← Nat.card_eq_fintype_card]
  rfl

/-- **The bounds of an interval with counted ratio**: `min{c, d}` is valid when `c` is and the
ratio `d` bounds the fine classes in each coarse class (Section 3.3: "When an interval of new
ratio `d'` inherits a bound `c`, we store `min{c, d'}`"). -/
theorem capAt_min_count [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} {f c : Setoid Ω}
    {b r : ℕ} {a : Ω} (h : CapAt G D f c b a) (hD : Invariant G D)
    (hf : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, f.r (g v) (g w) ↔ f.r v w)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w)
    (hr : classCount f (classIn G D c a) ≤ r) : CapAt G D f c (min b r) a :=
  h.min (capAt_of_count hD hf hc hr)

/-- **The labels give a section of the constituent** (Section 7.2: "The old cap is at least `q`
because the selected alternating section belongs to that whole constituent"). Let
`π : G ↠ Alt(q)`, `q ≥ 5`. If the kernel of `π` moves every point into the coarse class of `a`
up to an element of `G` (so that the stabilizer of the class maps onto `Alt(q)`), and every
element of `G` that keeps the class and fixes each fine class in it has trivial label image,
then a valid bound is at least `q`. -/
theorem le_of_capAt {G : Subgroup (Perm Ω)} {D : Set Ω} {f c : Setoid Ω} {b q : ℕ} {a : Ω}
    (h : CapAt G D f c b a) (hD : Invariant G D)
    (hc : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, c.r (g v) (g w) ↔ c.r v w) (ha : a ∈ D)
    (π : G →* alternatingGroup (Fin q)) (hπ : Function.Surjective π) (hq : 5 ≤ q)
    (hmove : ∀ g : G, ∃ k : G, π k = 1 ∧ ((k * g : G) : Perm Ω) a ∈ classIn G D c a)
    (hker : ∀ g : G, (g : Perm Ω) a ∈ classIn G D c a →
      (∀ w ∈ classIn G D c a, f.r ((g : Perm Ω) w) w) → π g = 1) : q ≤ b := by
  classical
  -- The stabilizer of the class in `G`.
  let U : Subgroup (Perm Ω) :=
    { carrier := {u | u ∈ G ∧ u a ∈ classIn G D c a}
      mul_mem' := fun {u v} hu hv => ⟨G.mul_mem hu.1 hv.1, by
        show u (v a) ∈ _
        exact classIn_maps hD hc hu.1 hu.2 hv.2⟩
      one_mem' := ⟨G.one_mem, classIn_mem_self c ha⟩
      inv_mem' := fun {u} hu => ⟨G.inv_mem hu.1, classIn_inv_mem hD hc hu.1 hu.2⟩ }
  have hUG : U ≤ G := fun u hu => hu.1
  let φ : U →* alternatingGroup (Fin q) := π.comp (Subgroup.inclusion hUG)
  refine h U hUG (fun u hu => hu.2) q hq φ ?_ ?_
  · intro σ
    obtain ⟨g, rfl⟩ := hπ σ
    obtain ⟨k, hk, hka⟩ := hmove g
    refine ⟨⟨(k * g : G), (k * g : G).2, hka⟩, ?_⟩
    show π (k * g) = π g
    rw [map_mul, hk, one_mul]
  · intro u hu
    exact hker ⟨u, u.2.1⟩ u.2.2 hu

/-- **The chain condition**, read from the fine end `f`: each interval has a `G`-invariant
coarse end, coarser than its fine end on `D`; its stored ratio bounds the number of fine classes
in one coarse class of an orbit; and its stored bound is at most its ratio. -/
def Chain (G : Subgroup (Perm Ω)) (D : Set Ω) : Setoid Ω → List (Interval Ω) → Prop
  | _, [] => True
  | f, I :: l => (∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, I.part.r (g v) (g w) ↔ I.part.r v w) ∧
      (∀ v ∈ D, ∀ w ∈ D, f.r v w → I.part.r v w) ∧
      (∀ a ∈ D, classCount f (classIn G D I.part a) ≤ I.ratio) ∧
      I.cap ≤ I.ratio ∧ Chain G D I.part l

/-- **The top condition**: each orbit of `G` in `D` lies in one class of `f`. -/
def TopOn (G : Subgroup (Perm Ω)) (D : Set Ω) (f : Setoid Ω) : Prop :=
  ∀ a ∈ D, ∀ w ∈ D, w ∈ orb G a → f.r a w

/-- **The hierarchy invariant**: the hierarchy is a tower of block systems of every orbit of the
current action on its domain, from the points to the whole orbit, with upper-bound ratios and
clamped bounds, and every stored bound is valid for its constituent action (Section 3.3: "An
interval bound `c_i` is a bound on this quantity for its entire constituent action"). -/
structure HierInv (G : Subgroup (Perm Ω)) (D : Set Ω) (l : List (Interval Ω)) : Prop where
  chain : Chain G D ⊥ l
  top : TopOn G D (fineEnd ⊥ l)
  caps : Caps G D ⊥ l

/-- The hierarchy invariant of a state. -/
def State.HierInv {C : Type} (S : State Ω C) : Prop := GI.Algorithm.HierInv S.G S.dom S.hier

/-! ### Basic facts -/

theorem Chain.mono [Finite Ω] {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} (hG : G' ≤ G)
    (hD : D' ⊆ D) : ∀ {f : Setoid Ω} {l : List (Interval Ω)}, Chain G D f l → Chain G' D' f l
  | _, [], _ => trivial
  | f, I :: _, ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨fun g hg v hv w hw => h1 g (hG hg) v (hD hv) w (hD hw),
      fun v hv w hw => h2 v (hD hv) w (hD hw),
      fun a ha => (classCount_mono f (classIn_mono hG hD I.part a)).trans (h3 a (hD ha)), h4,
      Chain.mono hG hD h5⟩

theorem TopOn.mono {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} (hG : G' ≤ G) (hD : D' ⊆ D)
    {f : Setoid Ω} (h : TopOn G D f) : TopOn G' D' f :=
  fun a ha w hw hwa => h a (hD ha) w (hD hw) (mem_orb_mono hG hwa)

/-- **The invariant passes to a subgroup on a smaller domain** (Section 3.3: "When a recursive
call restricts the allowed relabelings and selects one orbit, it intersects the old partitions
with that orbit. The old hierarchy is retained"). -/
theorem HierInv.mono [Finite Ω] {G G' : Subgroup (Perm Ω)} {D D' : Set Ω}
    {l : List (Interval Ω)} (h : HierInv G D l) (hG : G' ≤ G) (hD : D' ⊆ D) :
    HierInv G' D' l :=
  ⟨h.chain.mono hG hD, h.top.mono hG hD, h.caps.mono hG hD⟩

theorem chain_append {G : Subgroup (Perm Ω)} {D : Set Ω} :
    ∀ {f : Setoid Ω} {l₁ l₂ : List (Interval Ω)},
      Chain G D f (l₁ ++ l₂) ↔ Chain G D f l₁ ∧ Chain G D (fineEnd f l₁) l₂
  | _, [], _ => by simp [Chain]
  | f, I :: l₁, l₂ => by
    simp only [List.cons_append, Chain, fineEnd_cons]
    rw [chain_append]
    tauto

theorem caps_append {G : Subgroup (Perm Ω)} {D : Set Ω} :
    ∀ {f : Setoid Ω} {l₁ l₂ : List (Interval Ω)},
      Caps G D f (l₁ ++ l₂) ↔ Caps G D f l₁ ∧ Caps G D (fineEnd f l₁) l₂
  | _, [], _ => by simp [Caps]
  | f, I :: l₁, l₂ => by
    simp only [List.cons_append, Caps, fineEnd_cons]
    rw [caps_append]
    tauto

/-- Two fine ends that agree on `D` give the same chain conditions. -/
theorem chain_congr {G : Subgroup (Perm Ω)} {D : Set Ω} {f f' : Setoid Ω}
    (h : ∀ v ∈ D, ∀ w ∈ D, f.r v w ↔ f'.r v w) :
    ∀ {l : List (Interval Ω)}, Chain G D f l ↔ Chain G D f' l
  | [] => Iff.rfl
  | I :: l => by
    simp only [Chain]
    have hc : ∀ a, classCount f (classIn G D I.part a) = classCount f' (classIn G D I.part a) :=
      fun a => classCount_congr fun v hv w hw => h v hv.1 w hw.1
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, fun v hv w hw hf => h2 v hv w hw ((h v hv w hw).2 hf),
        fun a ha => (hc a) ▸ h3 a ha, h4, h5⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, fun v hv w hw hf => h2 v hv w hw ((h v hv w hw).1 hf),
        fun a ha => (hc a).symm ▸ h3 a ha, h4, h5⟩

/-- Two fine ends that agree on an invariant `D` give the same constituent bounds. -/
theorem capAt_congr {G : Subgroup (Perm Ω)} {D : Set Ω} {f f' c : Setoid Ω} {b : ℕ} {a : Ω}
    (hD : Invariant G D) (h : ∀ v ∈ D, ∀ w ∈ D, f.r v w ↔ f'.r v w) :
    CapAt G D f c b a ↔ CapAt G D f' c b a := by
  have key : ∀ {f f' : Setoid Ω}, (∀ v ∈ D, ∀ w ∈ D, f.r v w ↔ f'.r v w) →
      CapAt G D f c b a → CapAt G D f' c b a := by
    intro f f' h hc
    refine hc.sub le_rfl (fun _ _ h => h) fun u hu _ hfix w hw => ?_
    exact (h _ ((hD u hu w).2 hw.1) w hw.1).1 (hfix w hw)
  exact ⟨key h, key fun v hv w hw => (h v hv w hw).symm⟩

theorem caps_congr {G : Subgroup (Perm Ω)} {D : Set Ω} {f f' : Setoid Ω} (hD : Invariant G D)
    (h : ∀ v ∈ D, ∀ w ∈ D, f.r v w ↔ f'.r v w) :
    ∀ {l : List (Interval Ω)}, Caps G D f l ↔ Caps G D f' l
  | [] => Iff.rfl
  | I :: l => by
    simp only [Caps, CapOK]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun a ha => (capAt_congr hD h).1 (h1 a ha), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun a ha => (capAt_congr hD h).2 (h1 a ha), h2⟩

theorem fineEnd_congr {D : Set Ω} {f f' : Setoid Ω} (h : ∀ v ∈ D, ∀ w ∈ D, f.r v w ↔ f'.r v w) :
    ∀ (l : List (Interval Ω)), ∀ v ∈ D, ∀ w ∈ D, (fineEnd f l).r v w ↔ (fineEnd f' l).r v w
  | [] => h
  | _ :: _ => fun _ _ _ _ => Iff.rfl

/-- The coarsest partition of a chain is `G`-invariant on `D` when its fine end is. -/
theorem Chain.fineEnd_inv {G : Subgroup (Perm Ω)} {D : Set Ω} :
    ∀ {f : Setoid Ω} {l : List (Interval Ω)}, Chain G D f l →
      (∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, f.r (g v) (g w) ↔ f.r v w) →
      ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, (fineEnd f l).r (g v) (g w) ↔ (fineEnd f l).r v w
  | _, [], _, hf => hf
  | _, I :: l, h, _ => Chain.fineEnd_inv (f := I.part) (l := l) h.2.2.2.2 h.1

/-- The point partition is invariant. -/
theorem bot_inv (G : Subgroup (Perm Ω)) (D : Set Ω) :
    ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, (⊥ : Setoid Ω).r (g v) (g w) ↔ (⊥ : Setoid Ω).r v w := by
  intro g _ v _ w _
  change g v = g w ↔ v = w
  exact g.injective.eq_iff

/-! ### Interval bounds that only decrease -/

/-- `l'` has the partitions and ratios of `l`, and bounds at most those of `l`. -/
def CapsBelow (l l' : List (Interval Ω)) : Prop :=
  List.Forall₂ (fun I J : Interval Ω => J.part = I.part ∧ J.ratio = I.ratio ∧ J.cap ≤ I.cap) l l'

theorem CapsBelow.chain {G : Subgroup (Perm Ω)} {D : Set Ω} :
    ∀ {f : Setoid Ω} {l l' : List (Interval Ω)}, CapsBelow l l' → Chain G D f l →
      Chain G D f l' ∧ fineEnd f l' = fineEnd f l
  | _, [], [], _, _ => ⟨trivial, rfl⟩
  | f, I :: l, J :: l', List.Forall₂.cons ⟨hp, hr, hc⟩ hrest, ⟨h1, h2, h3, h4, h5⟩ => by
    obtain ⟨ih1, ih2⟩ := CapsBelow.chain hrest (hp ▸ h5)
    refine ⟨⟨hp ▸ h1, hp ▸ h2, fun a ha => hp ▸ hr ▸ h3 a ha, hr ▸ hc.trans h4, ih1⟩, ?_⟩
    simp only [fineEnd_cons]
    rw [ih2, hp]

/-- Lower bounds keep the chain and the top condition; they keep the invariant when they are
valid. -/
theorem CapsBelow.hierInv {G : Subgroup (Perm Ω)} {D : Set Ω} {l l' : List (Interval Ω)}
    (hc : CapsBelow l l') (h : HierInv G D l) (hcaps : Caps G D ⊥ l') : HierInv G D l' := by
  obtain ⟨h1, h2⟩ := hc.chain h.chain
  exact ⟨h1, h2 ▸ h.top, hcaps⟩

theorem capsBelow_refl : ∀ (l : List (Interval Ω)), CapsBelow l l
  | [] => List.Forall₂.nil
  | _ :: l => List.Forall₂.cons ⟨rfl, rfl, le_rfl⟩ (capsBelow_refl l)

theorem capsBelow_set : ∀ (l : List (Interval Ω)) (i : ℕ) (J : Interval Ω), (hi : i < l.length) →
    J.part = l[i].part → J.ratio = l[i].ratio → J.cap ≤ l[i].cap → CapsBelow l (l.set i J)
  | [], _, _, hi, _, _, _ => absurd hi (by simp)
  | _ :: l, 0, J, _, hp, hr, hc => List.Forall₂.cons ⟨hp, hr, hc⟩ (capsBelow_refl l)
  | _ :: l, i + 1, J, hi, hp, hr, hc =>
    List.Forall₂.cons ⟨rfl, rfl, le_rfl⟩
      (capsBelow_set l i J (by simpa using hi) hp hr hc)

/-- The validity of one bound, read from the fine end. -/
theorem caps_getElem {G : Subgroup (Perm Ω)} {D : Set Ω} :
    ∀ (f : Setoid Ω) (l : List (Interval Ω)), Caps G D f l → ∀ (i : ℕ) (hi : i < l.length),
      CapOK G D (fineEnd f (l.take i)) l[i].part l[i].cap
  | _, [], _, _, hi => absurd hi (by simp)
  | _, _ :: _, h, 0, _ => h.1
  | _, I :: l, h, i + 1, hi => by
    simpa using caps_getElem I.part l h.2 i (by simpa using hi)

/-- **Setting one bound to a valid value keeps the caps valid.** -/
theorem caps_set {G : Subgroup (Perm Ω)} {D : Set Ω} :
    ∀ (f : Setoid Ω) (l : List (Interval Ω)) (i : ℕ) (hi : i < l.length) (J : Interval Ω),
      J.part = l[i].part → Caps G D f l → CapOK G D (fineEnd f (l.take i)) J.part J.cap →
      Caps G D f (l.set i J)
  | _, [], _, hi, _, _, _, _ => absurd hi (by simp)
  | _, I :: l, 0, _, J, hp, h, hv => ⟨hv, by simp only [List.getElem_cons_zero] at hp; rw [hp]; exact h.2⟩
  | _, I :: l, i + 1, hi, J, hp, h, hv =>
    ⟨h.1, caps_set I.part l i (by simpa using hi) J hp h.2 (by simpa using hv)⟩

/-- **A cap update keeps the invariant** when the new bound is valid (Algorithm 3,
`LiftAndContinue`: the selected bound becomes `min{c, βq}`; the partitions and ratios are
unchanged; Section 7.2: "the new cap bounds its entire restricted action"). -/
theorem HierInv.capUpdate {P : Params} {G : Subgroup (Perm Ω)} {D : Set Ω}
    {l : List (Interval Ω)} {q : ℕ} (i : Fin l.length) (h : HierInv G D l)
    (hv : CapOK G D (fineEnd ⊥ (l.take i)) l[i].part ⌊P.β * q⌋₊) :
    HierInv G D (l.set i { l[i] with cap := min l[i].cap ⌊P.β * q⌋₊ }) := by
  refine (capsBelow_set l i { l[i] with cap := min l[i].cap ⌊P.β * q⌋₊ } i.2 rfl rfl
    (min_le_left _ _)).hierInv h (caps_set ⊥ l i i.2 _ rfl h.caps fun a ha => ?_)
  have h1 := caps_getElem ⊥ l h.caps i i.2 a ha
  exact h1.min (hv a ha)

/-! ### The hierarchy of a fresh phase -/

/-- The orbit partition of `G`: two points are related when they lie in one orbit. -/
def orbitSetoid (G : Subgroup (Perm Ω)) : Setoid Ω where
  r v w := w ∈ orb G v
  iseqv := ⟨fun v => ⟨1, G.one_mem, rfl⟩,
    fun {v w} h => by
      obtain ⟨g, hg, rfl⟩ := h
      exact ⟨g⁻¹, G.inv_mem hg, by simp⟩,
    fun {u v w} h1 h2 => by
      obtain ⟨g, hg, rfl⟩ := h1
      obtain ⟨k, hk, rfl⟩ := h2
      exact ⟨k * g, G.mul_mem hk hg, rfl⟩⟩

theorem orbitSetoid_inv (G : Subgroup (Perm Ω)) :
    ∀ g ∈ G, ∀ v w, (orbitSetoid G).r (g v) (g w) ↔ (orbitSetoid G).r v w := by
  intro g hg v w
  change g w ∈ orb G (g v) ↔ w ∈ orb G v
  constructor
  · rintro ⟨k, hk, hkw⟩
    refine ⟨g⁻¹ * k * g, G.mul_mem (G.mul_mem (G.inv_mem hg) hk) hg, ?_⟩
    simp only [Perm.mul_apply, hkw, Perm.inv_apply_self]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨g * k * g⁻¹, G.mul_mem (G.mul_mem hg hk) (G.inv_mem hg), ?_⟩
    simp

/-- **The hierarchy of a fresh phase** (Algorithm 5, `Solve`: "Initialize each original orbit's
hierarchy and interval bounds"; Section 3.3: "The initial bound `c_i = d_i` is always
available"): one interval from the points to the orbits, with ratio and bound `M`, the size of a
largest orbit. On each original orbit it is the hierarchy from the points to that orbit. -/
def orbitHier (G : Subgroup (Perm Ω)) (M : ℕ) : List (Interval Ω) :=
  [⟨orbitSetoid G, M, M, 0⟩]

theorem orbitHier_hierInv [Finite Ω] (G : Subgroup (Perm Ω)) {D : Set Ω} {M : ℕ}
    (hD : Invariant G D) (hM : ∀ a ∈ D, Nat.card (orb G a) ≤ M) :
    HierInv G D (orbitHier G M) := by
  have hcount : ∀ a ∈ D, classCount ⊥ (classIn G D (orbitSetoid G) a) ≤ M := fun a ha => by
    rw [classCount_bot]
    refine le_trans ?_ (hM a ha)
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun w hw => hw.2.1) (Set.toFinite _)
  refine ⟨⟨fun g hg v _ w _ => orbitSetoid_inv G g hg v w, fun v _ w _ h => ?_, hcount,
    le_rfl, trivial⟩, fun a _ w _ hw => hw, ⟨fun a ha => ?_, trivial⟩⟩
  · have : v = w := h
    subst this
    exact (orbitSetoid G).refl v
  · -- Section 3.3: "The initial bound `c_i = d_i` is always available".
    exact capAt_of_count hD (bot_inv G D) (fun g hg v _ w _ => orbitSetoid_inv G g hg v w)
      (hcount a ha)

end GI.Algorithm
