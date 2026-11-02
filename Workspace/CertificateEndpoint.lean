import Workspace.Transport
import Workspace.Localization
import Workspace.OrbitLocalization
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The endpoint procedure of a constant-size local certificate

Paper, Appendix A, Section "Constant-size certificates and exact comparisons"
(`sec:certificates`), subsection "Endpoint construction", and Algorithm
`alg:local-certificate` in Section 4.

This file is generic. A subgroup `P ≤ Sym(V)` carries a homomorphism
`phi : P →* Q` (in the paper, `P = P_T`, `Q = Alt(T)`, `phi = φ_T`). For a
subgroup `A` we write `img phi A` for `φ(A ∩ P)`; the groups of the procedure
all lie in `P`. A string is `x : V → C`. The masked string `x^W` (`mask x W`)
keeps the colors on `W` and gives the complement a fresh marker (`none`).
`Aut_A(z)` is `GI.automorphisms A z`.

The procedure is defined mathematically, as a sequence of stages
`stage phi x t = (A_t, W_t)`. The tests are the paper's:

1. stop (nonfull) if `φ(A_t) ≠ φ(P)`-image `⊤`;
2. `E_t` = points outside `W_t` whose stabilizer in `A_t` has proper image;
   if nonempty, `V_t = E_t`;
3. otherwise, with `U_t = Ω \ W_t`, stop (full) if `φ((A_t)_{(U_t)}) = ⊤`;
4. otherwise `V_t` = union of the `A_t`-orbits `Δ` in `U_t` with
   `φ((A_t)_{(Δ)}) = 1`;
5. `W_{t+1} = W_t ∪ V_t` and `A_{t+1} = Aut_{A_t}(x^{V_t})`.

At a stop, the increment is empty, so the sequence is constant from then on.
Rule 5 uses the masked string on `V_t`: since `V_t` is `A_t`-invariant
(`increment_invariant`), an element of `A_t` preserves `x^{V_t}` exactly when
it preserves the colors of `x` on `V_t`, which is the paper's
`Aut^{V_t}_{A_t}(x)` (`mem_autWindow_iff`).

The algorithmic clauses (how `CheckNewWindow` computes `A_{t+1}` with
kernel-coset enumeration and `Continue`, and the polynomial cost) belong to the
machine level (`Workspace/Impl/`) and are not formalized here.
-/

namespace GI.Endpoint

open Equiv Equiv.Perm

variable {V C Q : Type*} [Group Q]

/-! ### Masked strings, stabilizers, pointwise stabilizers, orbits -/

section Basic

variable [DecidableEq V]

/-- The masked string `x^W`: the colors of `x` on `W`, a fresh marker `none`
on the complement. -/
def mask (x : V → C) (W : Finset V) : V → Option C :=
  fun v => if v ∈ W then some (x v) else none

theorem transports_mask_iff (x y : V → C) (W W' : Finset V) (g : Perm V) :
    Transports (mask x W) (mask y W') g ↔
      (∀ v, g v ∈ W' ↔ v ∈ W) ∧ ∀ v ∈ W, y (g v) = x v := by
  constructor
  · intro h
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have he := h v
      unfold mask at he
      by_cases hv : v ∈ W <;> by_cases hgv : g v ∈ W' <;> simp_all
    · have he := h v
      unfold mask at he
      by_cases hgv : g v ∈ W' <;> simp_all
  · rintro ⟨hW, hc⟩ v
    unfold mask
    by_cases hv : v ∈ W
    · simp [hv, (hW v).2 hv, hc v hv]
    · have : g v ∉ W' := fun h => hv ((hW v).1 h)
      simp [hv, this]

/-- `A` leaves `W` invariant. -/
def Invariant (A : Subgroup (Perm V)) (W : Finset V) : Prop :=
  ∀ a ∈ A, ∀ v, a v ∈ W ↔ v ∈ W

theorem mem_automorphisms_mask_iff (A : Subgroup (Perm V)) (x : V → C) (W : Finset V)
    (g : Perm V) :
    g ∈ automorphisms A (mask x W) ↔
      g ∈ A ∧ (∀ v, g v ∈ W ↔ v ∈ W) ∧ ∀ v ∈ W, x (g v) = x v := by
  change g ∈ A ∧ Transports _ _ g ↔ _
  rw [transports_mask_iff]

omit [DecidableEq V] in
theorem automorphisms_le (A : Subgroup (Perm V)) (z : V → C) : automorphisms A z ≤ A :=
  fun _ h => h.1

/-- The paper's `Aut^{V}_{A}(x)`, for an `A`-invariant window `V`, is the group of
masked automorphisms. -/
theorem mem_autWindow_iff (A : Subgroup (Perm V)) (x : V → C) (D : Finset V)
    (hD : Invariant A D) (g : Perm V) :
    g ∈ automorphisms A (mask x D) ↔ g ∈ A ∧ ∀ v ∈ D, x (g v) = x v := by
  rw [mem_automorphisms_mask_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hD g h.1, h.2⟩⟩

theorem invariant_automorphisms_mask (A : Subgroup (Perm V)) (x : V → C) (W : Finset V) :
    Invariant (automorphisms A (mask x W)) W := fun a ha =>
  ((mem_automorphisms_mask_iff A x W a).1 ha).2.1

theorem automorphisms_mask_empty (A : Subgroup (Perm V)) (x : V → C) :
    automorphisms A (mask x ∅) = A := by
  ext g
  rw [mem_automorphisms_mask_iff]
  simp

end Basic

/-- The stabilizer `A_v` of a point in `A`. -/
def stab (A : Subgroup (Perm V)) (v : V) : Subgroup (Perm V) :=
  A ⊓ MulAction.stabilizer (Perm V) v

theorem mem_stab {A : Subgroup (Perm V)} {v : V} {g : Perm V} :
    g ∈ stab A v ↔ g ∈ A ∧ g v = v := by
  simp [stab, MulAction.mem_stabilizer_iff, Perm.smul_def]

/-- The pointwise stabilizer `A_{(U)}` of a set `U`. -/
def fix (A : Subgroup (Perm V)) (U : Set V) : Subgroup (Perm V) :=
  A ⊓ fixingSubgroup (Perm V) U

theorem mem_fix {A : Subgroup (Perm V)} {U : Set V} {g : Perm V} :
    g ∈ fix A U ↔ g ∈ A ∧ ∀ u ∈ U, g u = u := by
  simp [fix, mem_fixingSubgroup_iff, Perm.smul_def]

/-- The `A`-orbit `v^A` of a point. -/
def orb (A : Subgroup (Perm V)) (v : V) : Set V := {w | ∃ a ∈ A, a v = w}

theorem orb_eq_orbit (A : Subgroup (Perm V)) (v : V) : orb A v = MulAction.orbit A v := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩

theorem mem_orb_self (A : Subgroup (Perm V)) (v : V) : v ∈ orb A v := ⟨1, A.one_mem, rfl⟩

/-! ### Images under the test quotient -/

section Image

variable {P : Subgroup (Perm V)} (phi : P →* Q)

/-- `φ(A)`: the image of `A ∩ P` under `phi`. -/
def img (A : Subgroup (Perm V)) : Subgroup Q := (A.subgroupOf P).map phi

theorem mem_img {A : Subgroup (Perm V)} {q : Q} :
    q ∈ img phi A ↔ ∃ a : P, (a : Perm V) ∈ A ∧ phi a = q := by
  simp [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem img_mono {A B : Subgroup (Perm V)} (h : A ≤ B) : img phi A ≤ img phi B := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := (mem_img phi).1 hq
  exact (mem_img phi).2 ⟨a, h ha, rfl⟩

/-- The image of the kernel part: `N = A ∩ ker φ` (as a subgroup of `Sym(V)`). -/
def kernelIn (A : Subgroup (Perm V)) : Subgroup (Perm V) := A ⊓ phi.ker.map P.subtype

theorem mem_kernelIn {A : Subgroup (Perm V)} {g : Perm V} :
    g ∈ kernelIn phi A ↔ g ∈ A ∧ ∃ h : g ∈ P, phi ⟨g, h⟩ = 1 := by
  simp only [kernelIn, Subgroup.mem_inf, Subgroup.mem_map, MonoidHom.mem_ker,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨hA, ⟨a, ha, rfl⟩⟩
    exact ⟨hA, a.2, ha⟩
  · rintro ⟨hA, h, hg⟩
    exact ⟨hA, ⟨g, h⟩, hg, rfl⟩

/-- Rule 1: the full test action is realized. -/
def Full (A : Subgroup (Perm V)) : Prop := img phi A = ⊤

/-- Rule 2: `v` is affected by `A`: the stabilizer `A_v` has a proper image. -/
def Affected (A : Subgroup (Perm V)) (v : V) : Prop := img phi (stab A v) ≠ ⊤

/-- Rule 4: the test quotient is visible on the orbit `Δ = v^A`:
`φ(A_{(Δ)}) = 1`. -/
def VisibleOrbit (A : Subgroup (Perm V)) (v : V) : Prop := img phi (fix A (orb A v)) = ⊥

variable [DecidableEq V] [Fintype V]

/-- The complement `U = Ω \ W` of a window. -/
def outside (W : Finset V) : Set V := {v | v ∉ W}

open Classical in
/-- Rule 2: `E`, the affected points outside the window. -/
noncomputable def affectedSet (A : Subgroup (Perm V)) (W : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ W ∧ Affected phi A v)

open Classical in
/-- Rule 4: the union of the `A`-orbits `Δ` in `U` with `φ(A_{(Δ)}) = 1`. -/
noncomputable def extraSet (A : Subgroup (Perm V)) (W : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ W ∧ VisibleOrbit phi A v)

theorem mem_affectedSet {A : Subgroup (Perm V)} {W : Finset V} {v : V} :
    v ∈ affectedSet phi A W ↔ v ∉ W ∧ Affected phi A v := by
  classical
  simp [affectedSet]

theorem mem_extraSet {A : Subgroup (Perm V)} {W : Finset V} {v : V} :
    v ∈ extraSet phi A W ↔ v ∉ W ∧ VisibleOrbit phi A v := by
  classical
  simp [extraSet]

/-- The two stopping tests (rules 1 and 3). -/
def Stopped (A : Subgroup (Perm V)) (W : Finset V) : Prop :=
  ¬ Full phi A ∨ (affectedSet phi A W = ∅ ∧ Full phi (fix A (outside W)))

open Classical in
/-- The window increment `V_t` chosen by rules 1 to 4 (empty at a stop). -/
noncomputable def increment (A : Subgroup (Perm V)) (W : Finset V) : Finset V :=
  if ¬ Full phi A then ∅
  else if (affectedSet phi A W).Nonempty then affectedSet phi A W
  else if Full phi (fix A (outside W)) then ∅
  else extraSet phi A W

/-- The stages `(A_t, W_t)` of the endpoint procedure for the string `x`:
`A_0 = P`, `W_0 = ∅`, `A_{t+1} = Aut_{A_t}(x^{V_t})`, `W_{t+1} = W_t ∪ V_t`. -/
noncomputable def stage (x : V → C) : ℕ → Subgroup (Perm V) × Finset V
  | 0 => (P, ∅)
  | t + 1 =>
    ((automorphisms (stage x t).1 (mask x (increment phi (stage x t).1 (stage x t).2))),
      (stage x t).2 ∪ increment phi (stage x t).1 (stage x t).2)

/-- The group `A_t`. -/
noncomputable abbrev grp (x : V → C) (t : ℕ) : Subgroup (Perm V) := (stage phi x t).1

/-- The window `W_t`. -/
noncomputable abbrev win (x : V → C) (t : ℕ) : Finset V := (stage phi x t).2

/-- The increment `V_t`. -/
noncomputable abbrev inc (x : V → C) (t : ℕ) : Finset V :=
  increment phi (grp phi x t) (win phi x t)

theorem grp_zero (x : V → C) : grp phi x 0 = P := rfl

theorem win_zero (x : V → C) : win phi x 0 = ∅ := rfl

theorem grp_succ (x : V → C) (t : ℕ) :
    grp phi x (t + 1) = automorphisms (grp phi x t) (mask x (inc phi x t)) := rfl

theorem win_succ (x : V → C) (t : ℕ) : win phi x (t + 1) = win phi x t ∪ inc phi x t := rfl

theorem win_mono (x : V → C) {i j : ℕ} (hij : i ≤ j) : win phi x i ⊆ win phi x j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j _ ih =>
    refine ih.trans ?_
    rw [win_succ]
    exact Finset.subset_union_left

theorem inc_subset_win (x : V → C) {i t : ℕ} (hit : i < t) : inc phi x i ⊆ win phi x t := by
  have h : inc phi x i ⊆ win phi x (i + 1) := by
    rw [win_succ]; exact Finset.subset_union_right
  exact h.trans (win_mono phi x hit)

theorem grp_le (x : V → C) (t : ℕ) : grp phi x t ≤ P := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (automorphisms_le _ _).trans ih

end Image

/-! ### Conjugation -/

section Conj

/-- The conjugate subgroup `g A g⁻¹`. -/
def cmap (g : Perm V) (A : Subgroup (Perm V)) : Subgroup (Perm V) :=
  A.map (MulAut.conj g).toMonoidHom

theorem mem_cmap {g b : Perm V} {A : Subgroup (Perm V)} : b ∈ cmap g A ↔ g⁻¹ * b * g ∈ A := by
  simp only [cmap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem conj_mem_cmap {g a : Perm V} {A : Subgroup (Perm V)} (ha : a ∈ A) :
    g * a * g⁻¹ ∈ cmap g A := by
  rw [mem_cmap]; simpa [mul_assoc] using ha

theorem cmap_of_mem {g : Perm V} {A : Subgroup (Perm V)} (hg : g ∈ A) : cmap g A = A := by
  ext b
  rw [mem_cmap]
  constructor
  · intro h
    have := A.mul_mem (A.mul_mem hg h) (A.inv_mem hg)
    simpa [mul_assoc] using this
  · intro h
    exact A.mul_mem (A.mul_mem (A.inv_mem hg) h) hg

theorem cmap_mul (g h : Perm V) (A : Subgroup (Perm V)) : cmap (g * h) A = cmap g (cmap h A) := by
  ext b
  simp only [mem_cmap, mul_inv_rev, mul_assoc]

theorem cmap_one (A : Subgroup (Perm V)) : cmap 1 A = A := cmap_of_mem A.one_mem

theorem cmap_mono {g : Perm V} {A B : Subgroup (Perm V)} (h : A ≤ B) : cmap g A ≤ cmap g B :=
  fun _ hb => mem_cmap.2 (h (mem_cmap.1 hb))

theorem cmap_inf (g : Perm V) (A B : Subgroup (Perm V)) :
    cmap g (A ⊓ B) = cmap g A ⊓ cmap g B := by
  ext b; simp only [Subgroup.mem_inf, mem_cmap]

theorem stab_cmap (g : Perm V) (A : Subgroup (Perm V)) (v : V) :
    stab (cmap g A) (g v) = cmap g (stab A v) := by
  ext b
  simp only [mem_stab, mem_cmap, Perm.mul_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2]; simp
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg g h2
    simpa using this

theorem fix_cmap (g : Perm V) (A : Subgroup (Perm V)) (U : Set V) :
    fix (cmap g A) (g '' U) = cmap g (fix A U) := by
  ext b
  simp only [mem_fix, mem_cmap, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Perm.mul_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => by rw [h2 u hu]; simp⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => by simpa using congrArg g (h2 u hu)⟩

theorem orb_cmap (g : Perm V) (A : Subgroup (Perm V)) (v : V) :
    orb (cmap g A) (g v) = g '' orb A v := by
  ext w
  simp only [orb, Set.mem_setOf_eq, Set.mem_image, mem_cmap]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨_, ⟨_, hb, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g * a * g⁻¹, by simpa [mul_assoc] using ha, by simp⟩

/-- `g W` as a finset. -/
abbrev wmap (g : Perm V) (W : Finset V) : Finset V := W.map g.toEmbedding

theorem mem_wmap {g : Perm V} {W : Finset V} {w : V} : w ∈ wmap g W ↔ g⁻¹ w ∈ W :=
  Finset.mem_map_equiv

theorem apply_mem_wmap {g : Perm V} {W : Finset V} {v : V} : g v ∈ wmap g W ↔ v ∈ W := by
  rw [mem_wmap]; simp

theorem outside_wmap (g : Perm V) (W : Finset V) : outside (wmap g W) = g '' outside W := by
  ext w
  simp only [outside, Set.mem_setOf_eq, Set.mem_image, mem_wmap]
  constructor
  · intro h; exact ⟨g⁻¹ w, h, by simp⟩
  · rintro ⟨v, hv, rfl⟩; simpa using hv

theorem wmap_of_invariant {A : Subgroup (Perm V)} {W : Finset V} (hW : Invariant A W)
    {a : Perm V} (ha : a ∈ A) : wmap a W = W := by
  ext w
  rw [mem_wmap, hW _ (A.inv_mem ha)]

theorem wmap_mul (g h : Perm V) (W : Finset V) : wmap (g * h) W = wmap g (wmap h W) := by
  ext w
  rw [mem_wmap, mem_wmap, mem_wmap, mul_inv_rev, Perm.mul_apply]

/-- `g` conjugates `A` with string `z` to `g A g⁻¹` with a string `z'` that `g`
transports `z` to. -/
theorem automorphisms_cmap {D : Type*} {g : Perm V} {z z' : V → D} (hg : Transports z z' g)
    (A : Subgroup (Perm V)) :
    automorphisms (cmap g A) z' = cmap g (automorphisms A z) := by
  ext b
  rw [mem_cmap]
  change b ∈ cmap g A ∧ Transports z' z' b ↔ g⁻¹ * b * g ∈ A ∧ Transports z z (g⁻¹ * b * g)
  rw [mem_cmap]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h v
    have h1 := h (g v)
    simp only [Perm.mul_apply]
    rw [← hg, ← hg v]
    simpa using h1
  · intro h w
    have h1 := h (g⁻¹ w)
    have e1 := hg (g⁻¹ (b w))
    have e2 := hg (g⁻¹ w)
    have k1 : g (g⁻¹ (b w)) = b w := by simp
    have k2 : g (g⁻¹ w) = w := by simp
    have k3 : (g⁻¹ * b * g) (g⁻¹ w) = g⁻¹ (b w) := by simp [Perm.mul_apply]
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at h1
    rw [e1, e2, h1]

end Conj

/-! ### Compatible test quotients and equivariance of the procedure -/

section Compat

variable {Q' : Type*} [Group Q'] {P P' : Subgroup (Perm V)}

/-- `g` carries the test data `(P, phi)` to `(P', phi')` along the isomorphism
`θ` of test quotients: `g P g⁻¹ = P'` and `phi'(g a g⁻¹) = θ(phi a)`. -/
structure Compat (phi : P →* Q) (phi' : P' →* Q') (g : Perm V) (θ : Q ≃* Q') : Prop where
  mem : ∀ a, a ∈ P ↔ g * a * g⁻¹ ∈ P'
  map : ∀ a : P, phi' ⟨g * a * g⁻¹, (mem a).1 a.2⟩ = θ (phi a)

/-- An element of `P` carries the test data to itself, along conjugation in `Q`. -/
theorem Compat.self (phi : P →* Q) (a : P) :
    Compat phi phi (a : Perm V) (MulAut.conj (phi a)) where
  mem b := by
    constructor
    · intro hb; exact P.mul_mem (P.mul_mem a.2 hb) (P.inv_mem a.2)
    · intro hb
      have := P.mul_mem (P.mul_mem (P.inv_mem a.2) hb) a.2
      simpa [mul_assoc] using this
  map b := by
    have : (⟨(a : Perm V) * b * (a : Perm V)⁻¹, P.mul_mem (P.mul_mem a.2 b.2) (P.inv_mem a.2)⟩ : P)
        = a * b * a⁻¹ := rfl
    rw [this]
    simp [MulAut.conj_apply]

variable {phi : P →* Q} {phi' : P' →* Q'} {g : Perm V} {θ : Q ≃* Q'}

theorem Compat.cmap_P (hc : Compat phi phi' g θ) : cmap g P = P' := by
  ext b
  rw [mem_cmap, hc.mem]
  simp [mul_assoc]

theorem Compat.img_cmap (hc : Compat phi phi' g θ) (A : Subgroup (Perm V)) :
    img phi' (cmap g A) = (img phi A).map θ.toMonoidHom := by
  ext q
  rw [mem_img, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hbP : g⁻¹ * (b : Perm V) * g ∈ P := by
      rw [hc.mem]; simpa [mul_assoc] using b.2
    refine ⟨phi ⟨_, hbP⟩, (mem_img phi).2 ⟨⟨_, hbP⟩, mem_cmap.1 hb, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← hc.map]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  · rintro ⟨_, hq, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (mem_img phi).1 hq
    exact ⟨⟨_, (hc.mem a).1 a.2⟩, conj_mem_cmap ha, hc.map a⟩

theorem map_equiv_eq_top_iff {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂] (θ : Q₁ ≃* Q₂)
    (H : Subgroup Q₁) : H.map θ.toMonoidHom = ⊤ ↔ H = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro q _
    have : θ q ∈ H.map θ.toMonoidHom := by rw [h]; trivial
    obtain ⟨r, hr, he⟩ := this
    rw [θ.injective he] at hr
    exact hr
  · intro h; rw [h, Subgroup.map_top_of_surjective _ θ.surjective]

theorem map_equiv_eq_bot_iff {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂] (θ : Q₁ ≃* Q₂)
    (H : Subgroup Q₁) : H.map θ.toMonoidHom = ⊥ ↔ H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective H θ.injective

theorem Compat.full_iff (hc : Compat phi phi' g θ) (A : Subgroup (Perm V)) :
    Full phi' (cmap g A) ↔ Full phi A := by
  unfold Full; rw [hc.img_cmap, map_equiv_eq_top_iff]

theorem Compat.affected_iff (hc : Compat phi phi' g θ) (A : Subgroup (Perm V)) (v : V) :
    Affected phi' (cmap g A) (g v) ↔ Affected phi A v := by
  unfold Affected; rw [stab_cmap, hc.img_cmap, ne_eq, ne_eq, map_equiv_eq_top_iff]

theorem Compat.visibleOrbit_iff (hc : Compat phi phi' g θ) (A : Subgroup (Perm V)) (v : V) :
    VisibleOrbit phi' (cmap g A) (g v) ↔ VisibleOrbit phi A v := by
  unfold VisibleOrbit; rw [orb_cmap, fix_cmap, hc.img_cmap, map_equiv_eq_bot_iff]

theorem Compat.fixOutside_full_iff (hc : Compat phi phi' g θ) (A : Subgroup (Perm V))
    (W : Finset V) :
    Full phi' (fix (cmap g A) (outside (wmap g W))) ↔ Full phi (fix A (outside W)) := by
  rw [outside_wmap, fix_cmap, hc.full_iff]

variable [DecidableEq V] [Fintype V]

theorem Compat.affectedSet_cmap (hc : Compat phi phi' g θ) (A : Subgroup (Perm V))
    (W : Finset V) : affectedSet phi' (cmap g A) (wmap g W) = wmap g (affectedSet phi A W) := by
  ext w
  obtain ⟨v, rfl⟩ : ∃ v, g v = w := ⟨g⁻¹ w, by simp⟩
  rw [mem_affectedSet, apply_mem_wmap, apply_mem_wmap, mem_affectedSet, hc.affected_iff]

theorem Compat.extraSet_cmap (hc : Compat phi phi' g θ) (A : Subgroup (Perm V))
    (W : Finset V) : extraSet phi' (cmap g A) (wmap g W) = wmap g (extraSet phi A W) := by
  ext w
  obtain ⟨v, rfl⟩ : ∃ v, g v = w := ⟨g⁻¹ w, by simp⟩
  rw [mem_extraSet, apply_mem_wmap, apply_mem_wmap, mem_extraSet, hc.visibleOrbit_iff]

theorem Compat.stopped_iff (hc : Compat phi phi' g θ) (A : Subgroup (Perm V)) (W : Finset V) :
    Stopped phi' (cmap g A) (wmap g W) ↔ Stopped phi A W := by
  unfold Stopped
  rw [hc.full_iff, hc.affectedSet_cmap, hc.fixOutside_full_iff]
  simp

theorem Compat.increment_cmap (hc : Compat phi phi' g θ) (A : Subgroup (Perm V))
    (W : Finset V) : increment phi' (cmap g A) (wmap g W) = wmap g (increment phi A W) := by
  classical
  unfold increment
  simp only [hc.full_iff, hc.affectedSet_cmap, hc.fixOutside_full_iff, hc.extraSet_cmap,
    Finset.map_nonempty]
  split_ifs <;> simp

end Compat

/-! ### Invariance of the windows -/

section Invariance

variable [DecidableEq V] [Fintype V] {P : Subgroup (Perm V)} (phi : P →* Q)

/-- The increment chosen by rules 2 and 4 is `A`-invariant: the rules are
conjugation-equivariant and involve no choice. -/
theorem increment_invariant {A : Subgroup (Perm V)} (hAP : A ≤ P) {W : Finset V}
    (hW : Invariant A W) : Invariant A (increment phi A W) := by
  intro a ha v
  have hc := Compat.self phi ⟨a, hAP ha⟩
  have h := hc.increment_cmap A W
  simp only [cmap_of_mem ha, wmap_of_invariant hW ha] at h
  conv_lhs => rw [h]
  exact apply_mem_wmap

/-- The invariant of the paper: `W_t` is `A_t`-invariant. -/
theorem win_invariant (x : V → C) (t : ℕ) : Invariant (grp phi x t) (win phi x t) := by
  induction t with
  | zero => intro a _ v; simp [win_zero]
  | succ t ih =>
    intro a ha v
    rw [win_succ, grp_succ] at *
    have hA := automorphisms_le _ _ ha
    simp only [Finset.mem_union]
    rw [ih a hA v, invariant_automorphisms_mask _ x _ a ha v]

theorem inc_invariant (x : V → C) (t : ℕ) : Invariant (grp phi x t) (inc phi x t) :=
  increment_invariant phi (grp_le phi x t) (win_invariant phi x t)

/-- Every member of `A_t` preserves the colors of `x` on `W_t`. -/
theorem grp_colors (x : V → C) (t : ℕ) : ∀ a ∈ grp phi x t, ∀ v ∈ win phi x t, x (a v) = x v := by
  induction t with
  | zero => intro a _ v hv; simp [win_zero] at hv
  | succ t ih =>
    intro a ha v hv
    rw [win_succ, Finset.mem_union] at hv
    rw [grp_succ] at ha
    rcases hv with hv | hv
    · exact ih a (automorphisms_le _ _ ha) v hv
    · exact ((mem_automorphisms_mask_iff _ x _ a).1 ha).2.2 v hv

/-- **Prefix recovery.** An element of `P` that preserves the colors of `x` on
the window `W_t` lies in `A_t`. The induction recovers every earlier window:
membership in `A_i` makes it preserve the `A_i`-invariant increment `V_i`. -/
theorem mem_grp_of_colors (x : V → C) {t : ℕ} {g : Perm V} (hgP : g ∈ P)
    (hx : ∀ v ∈ win phi x t, x (g v) = x v) : ∀ j ≤ t, g ∈ grp phi x j := by
  intro j
  induction j with
  | zero => intro _; exact hgP
  | succ j ih =>
    intro hj
    have hg := ih (by omega)
    rw [grp_succ, mem_autWindow_iff _ x _ (inc_invariant phi x j)]
    exact ⟨hg, fun v hv => hx v (inc_subset_win phi x (by omega) hv)⟩

/-- **The endpoint identity** `A_j = Aut_{P}(x^{W_j})`. -/
theorem grp_eq_automorphisms_mask (x : V → C) (t : ℕ) :
    grp phi x t = automorphisms P (mask x (win phi x t)) := by
  ext g
  rw [mem_automorphisms_mask_iff]
  constructor
  · intro hg
    exact ⟨grp_le phi x t hg, win_invariant phi x t g hg, grp_colors phi x t g hg⟩
  · rintro ⟨hgP, _, hx⟩
    exact mem_grp_of_colors phi x hgP hx t le_rfl

/-- Every automorphism of the whole string in `P` lies in every `A_t`. -/
theorem automorphisms_le_grp (x : V → C) (t : ℕ) : automorphisms P x ≤ grp phi x t :=
  fun _ hg => mem_grp_of_colors phi x hg.1 (fun v _ => hg.2 v) t le_rfl

end Invariance

end GI.Endpoint
