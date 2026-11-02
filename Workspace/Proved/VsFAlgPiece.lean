import Workspace.Proved.VsFAlgEig
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Artinian.Module

/-!
# Splitting a commutative algebra of endomorphisms

Let `B` be a commutative subalgebra of `End V`, for `V` a finite-dimensional space over
`ZMod p`. The Frobenius map `x ↦ x ^ p` is linear on `B`. This file proves what its kernel and
its fixed points tell about `B` and `V`.

* `vsFNil_eq_zero`: if `y ^ p = 0` forces `y = 0` in `B`, then `B` has no nonzero nilpotent.
* `vsFAnn B`: the common kernel of all `y ∈ B` with `y ^ p = 0`. It is nonzero
  (`vsFAnn_ne_bot`), proper when some such `y` is nonzero (`vsFAnn_ne_top`), and mapped into
  itself by every unit `T` with `T⁻¹ B T ⊆ B` (`vsFAnn_map`).
* `vsFEig f a`: the joint eigenspace of a family `f` with eigenvalues `a`. When the `f i` lie in
  the fixed points of the Frobenius map and span them, every fixed point acts on `vsFEig f a`
  as a scalar (`vsFEig_scalar`), every `b ∈ B` acts on it as `0` or injectively when `B` is
  reduced (`vsFEig_zero_or_inj`), and every `T` normalizing `B` maps a nonzero joint
  eigenspace onto a joint eigenspace (`vsFEig_map`).
* `vsFSpin_irred`: if every nonzero `b ∈ B` is injective and `B v₀ = V` for one `v₀`, then
  every nonzero `B`-invariant subspace is `V`.
-/

namespace GI.Proved

open Module Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-! ### Nilpotent elements -/

/-- If `y ^ p = 0` forces `y = 0` for `y ∈ B`, then every nilpotent `x ∈ B` is `0`: from
`x ^ (m + 2) = 0`, the element `y = x ^ (m + 1)` has `y ^ p = 0` (as `(m + 1) p ≥ m + 2`), so
`x ^ (m + 1) = 0`, and we go down. -/
theorem vsFNil_eq_zero (B : Subalgebra (ZMod p) (End (ZMod p) V))
    (hN : ∀ y ∈ B, y ^ p = 0 → y = 0) {x : End (ZMod p) V} (hx : x ∈ B) (hn : IsNilpotent x) :
    x = 0 := by
  obtain ⟨n, hn⟩ := hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn, ih with
    | 0, hn, _ => simpa using congrArg (x * ·) hn
    | 1, hn, _ => simpa using hn
    | m + 2, hn, ih =>
      have h2 := hp.out.two_le
      have hy : (x ^ (m + 1)) ^ p = 0 := by
        rw [← pow_mul]
        exact pow_eq_zero_of_le (by nlinarith) hn
      exact ih (m + 1) (by omega) (hN _ (B.pow_mem hx _) hy)

/-! ### The common kernel of the nilpotent part -/

/-- The common kernel of the `y ∈ B` with `y ^ p = 0`. -/
def vsFAnn (B : Subalgebra (ZMod p) (End (ZMod p) V)) : Submodule (ZMod p) V :=
  ⨅ (y : End (ZMod p) V) (_ : y ∈ B ∧ y ^ p = 0), LinearMap.ker y

theorem mem_vsFAnn (B : Subalgebra (ZMod p) (End (ZMod p) V)) (v : V) :
    v ∈ vsFAnn B ↔ ∀ y ∈ B, y ^ p = 0 → y v = 0 := by
  simp only [vsFAnn, Submodule.mem_iInf, LinearMap.mem_ker, and_imp]

/-- For a map `y` with `y ^ p = 0` and a nonzero `y`-invariant `W`, some nonzero `u ∈ W` has
`y u = 0`: take the last nonzero `y ^ j w`. -/
theorem vsFA_exists_ker (y : End (ZMod p) V) (hy : y ^ p = 0) (W : Submodule (ZMod p) V)
    (hW : ∀ w ∈ W, y w ∈ W) (hW0 : W ≠ ⊥) : ∃ u ∈ W, u ≠ 0 ∧ y u = 0 := by
  classical
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hex : ∃ j, (y ^ j) w = 0 := ⟨p, by rw [hy]; rfl⟩
  have hmemW : ∀ j, (y ^ j) w ∈ W := by
    intro j
    induction j with
    | zero => simpa using hw
    | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact hW _ ih
  set n := Nat.find hex with hn
  have hn0 : n ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hn, h] at this
    exact hw0 (by simpa using this)
  refine ⟨(y ^ (n - 1)) w, hmemW _, Nat.find_min hex (by omega), ?_⟩
  have := Nat.find_spec hex
  rw [← hn, ← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0), pow_succ',
    Module.End.mul_apply] at this
  exact this

/-- `vsFAnn B` is nonzero. Take a minimal nonzero subspace `W` that every nilpotent-part element
maps into itself. For such a `y`, the subspace `W ∩ ker y` has the same property (the elements
of `B` commute) and is nonzero (`vsFA_exists_ker`), so it is `W`. -/
theorem vsFAnn_ne_bot [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (B : Subalgebra (ZMod p) (End (ZMod p) V)) (hB : ∀ x ∈ B, ∀ y ∈ B, Commute x y) :
    vsFAnn B ≠ ⊥ := by
  let 𝒲 : Set (Submodule (ZMod p) V) :=
    {W | W ≠ ⊥ ∧ ∀ y ∈ B, y ^ p = 0 → ∀ w ∈ W, y w ∈ W}
  obtain ⟨W, ⟨hW0, hWinv⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt 𝒲 ⟨⊤, top_ne_bot, fun _ _ _ _ _ => trivial⟩
  have hle : W ≤ vsFAnn B := by
    intro w hw
    rw [mem_vsFAnn]
    intro y hy hyp
    let W' := W ⊓ LinearMap.ker y
    have hW' : W' ∈ 𝒲 := by
      refine ⟨?_, fun z hz hzp u hu => ⟨hWinv z hz hzp u hu.1, ?_⟩⟩
      · obtain ⟨u, huW, hu0, hyu⟩ := vsFA_exists_ker y hyp W (hWinv y hy hyp) hW0
        intro h
        have : u ∈ W' := ⟨huW, hyu⟩
        rw [h] at this
        exact hu0 ((Submodule.mem_bot _).1 this)
      · have hc : y * z = z * y := hB y hy z hz
        show y (z u) = 0
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply, LinearMap.mem_ker.1 hu.2, map_zero]
    have hEq : W' = W := eq_of_le_of_not_lt inf_le_left (hmin W' hW')
    have : w ∈ W' := hEq ▸ hw
    exact this.2
  intro h
  exact hW0 (le_bot_iff.1 (h ▸ hle))

theorem vsFAnn_ne_top (B : Subalgebra (ZMod p) (End (ZMod p) V)) {y : End (ZMod p) V}
    (hy : y ∈ B) (hyp : y ^ p = 0) (hy0 : y ≠ 0) : vsFAnn B ≠ ⊤ := by
  intro h
  apply hy0
  ext v
  have hv : v ∈ vsFAnn B := h ▸ Submodule.mem_top
  exact (mem_vsFAnn B v).1 hv y hy hyp

theorem vsFA_conj_pow (T : (End (ZMod p) V)ˣ) (x : End (ZMod p) V) (n : ℕ) :
    ((↑T⁻¹ : End (ZMod p) V) * x * ↑T) ^ n = ↑T⁻¹ * x ^ n * ↑T := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.mul_inv_cancel_left]

/-- A unit `T` with `T⁻¹ B T ⊆ B` maps `vsFAnn B` into itself: for `y` in the nilpotent part,
`y (T v) = T ((T⁻¹ y T) v)` and `T⁻¹ y T` is again in the nilpotent part. -/
theorem vsFAnn_map (B : Subalgebra (ZMod p) (End (ZMod p) V)) (T : (End (ZMod p) V)ˣ)
    (hT : ∀ x ∈ B, (↑T⁻¹ : End (ZMod p) V) * x * ↑T ∈ B) {v : V} (hv : v ∈ vsFAnn B) :
    (T : End (ZMod p) V) v ∈ vsFAnn B := by
  rw [mem_vsFAnn] at hv ⊢
  intro y hy hyp
  have h1 := hv _ (hT y hy) (by rw [vsFA_conj_pow, hyp, mul_zero, zero_mul])
  have h3 : y ((T : End (ZMod p) V) v) =
      (T : End (ZMod p) V) (((↑T⁻¹ : End (ZMod p) V) * y * ↑T) v) := by
    simp only [Module.End.mul_apply]
    rw [← Module.End.mul_apply (T : End (ZMod p) V) (↑T⁻¹ : End (ZMod p) V), Units.mul_inv,
      Module.End.one_apply]
  rw [h3, h1, map_zero]

/-! ### Joint eigenspaces of the Frobenius fixed points -/

/-- The joint eigenspace of the family `f` with eigenvalues `a`. -/
def vsFEig {ι : Type*} (f : ι → End (ZMod p) V) (a : ι → ZMod p) : Submodule (ZMod p) V :=
  ⨅ i, (f i).eigenspace (a i)

theorem mem_vsFEig {ι : Type*} (f : ι → End (ZMod p) V) (a : ι → ZMod p) (v : V) :
    v ∈ vsFEig f a ↔ ∀ i, f i v = a i • v := by
  simp only [vsFEig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- Every element of the span of the family acts on a joint eigenspace as a scalar. -/
theorem vsFEig_scalar {ι : Type*} (f : ι → End (ZMod p) V) (a : ι → ZMod p)
    {s : End (ZMod p) V} (hs : s ∈ Submodule.span (ZMod p) (Set.range f)) :
    ∃ c : ZMod p, ∀ v ∈ vsFEig f a, s v = c • v := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i, fun v hv => (mem_vsFEig f a v).1 hv i⟩
  | zero => exact ⟨0, fun v _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, fun v hv => by simp [hc v hv, hd v hv, add_smul]⟩
  | smul k x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨k * c, fun v hv => by simp [hc v hv, mul_smul]⟩

/-- Some `g` with `g(0) ≠ 0` has `b g(b) = 0`, for `b` in a reduced `B`. Write the
characteristic polynomial as `X ^ k g` with `X ∤ g`. Then `(b g(b)) ^ (k + 1)` is a multiple of
`χ(b) = 0` (Cayley–Hamilton), so `b g(b)` is nilpotent, hence `0`. -/
theorem vsFA_exists_annih [FiniteDimensional (ZMod p) V]
    (B : Subalgebra (ZMod p) (End (ZMod p) V)) (hN : ∀ y ∈ B, y ^ p = 0 → y = 0)
    {b : End (ZMod p) V} (hb : b ∈ B) :
    ∃ g : (ZMod p)[X], g.coeff 0 ≠ 0 ∧ b * aeval b g = 0 := by
  obtain ⟨g, hfac, hnd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd b.charpoly (LinearMap.charpoly_monic b).ne_zero 0
  simp only [map_zero, sub_zero] at hfac hnd
  refine ⟨g, fun h => hnd (X_dvd_iff.2 h), ?_⟩
  set k := rootMultiplicity 0 b.charpoly
  have hgB : aeval b g ∈ B := by
    have := aeval_subalgebra_coe g B ⟨b, hb⟩
    rw [← this]
    exact Subtype.coe_prop _
  refine vsFNil_eq_zero B hN (B.mul_mem hb hgB) ⟨k + 1, ?_⟩
  have h1 : b * aeval b g = aeval b (X * g) := by simp
  have h2 : (X * g) ^ (k + 1) = (X ^ k * g) * (X * g ^ k) := by ring
  rw [h1, ← map_pow, h2, ← hfac, map_mul, LinearMap.aeval_self_charpoly, zero_mul]

/-- On a joint eigenspace of a spanning family of Frobenius fixed points, every `b` in a reduced
`B` acts as `0` or injectively. With `g` from `vsFA_exists_annih`, the element
`e = g(0)⁻¹ g(b)` is idempotent, hence a fixed point, hence the scalar `0` or `1` on the
eigenspace. If `1`: `b = b e = 0` there. If `0`: `1 = e - g(0)⁻¹ g'(b) b`, so `b u = 0` gives
`u = 0`. -/
theorem vsFEig_zero_or_inj [FiniteDimensional (ZMod p) V]
    (B : Subalgebra (ZMod p) (End (ZMod p) V)) (hN : ∀ y ∈ B, y ^ p = 0 → y = 0)
    {ι : Type*} (f : ι → End (ZMod p) V) (a : ι → ZMod p)
    (hspan : ∀ s ∈ B, s ^ p = s → s ∈ Submodule.span (ZMod p) (Set.range f))
    {b : End (ZMod p) V} (hb : b ∈ B) :
    (∀ u ∈ vsFEig f a, b u = 0) ∨ (∀ u ∈ vsFEig f a, b u = 0 → u = 0) := by
  obtain ⟨g, hg0, hbg⟩ := vsFA_exists_annih B hN hb
  set g0 := g.coeff 0
  set g' := g.divX
  have hgsplit : aeval b g = g0 • 1 + b * aeval b g' := by
    have h := congrArg (aeval b) (X_mul_divX_add g)
    rw [map_add, map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
    rw [← h, add_comm]
  have hgB : aeval b g ∈ B := by
    have := aeval_subalgebra_coe g B ⟨b, hb⟩
    rw [← this]
    exact Subtype.coe_prop _
  set e := g0⁻¹ • aeval b g with he
  have heB : e ∈ B := B.smul_mem hgB _
  have hcomm' : aeval b g' * b = b * aeval b g' := by
    have h1 : aeval b (g' * X) = aeval b (X * g') := by rw [mul_comm]
    simpa using h1
  have hcomm : aeval b g * b = b * aeval b g := by
    have h1 : aeval b (g * X) = aeval b (X * g) := by rw [mul_comm]
    simpa using h1
  have hbe : b * e = 0 := by rw [he, mul_smul_comm, hbg, smul_zero]
  have hg0' : g0⁻¹ * g0 = 1 := inv_mul_cancel₀ hg0
  have he1 : e = 1 + g0⁻¹ • (b * aeval b g') := by
    rw [he, hgsplit, smul_add, smul_smul, hg0', one_smul]
  have heb0 : e * b = 0 := by rw [he, smul_mul_assoc, hcomm, hbg, smul_zero]
  have hee : e * e = e := by
    calc e * e = e * (1 + g0⁻¹ • (b * aeval b g')) := by rw [← he1]
      _ = e := by rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc, heb0, zero_mul, smul_zero,
        add_zero]
  have hep : e ^ p = e := by
    have h := IsIdempotentElem.pow_succ_eq (p - 1) (hee : IsIdempotentElem e)
    rwa [Nat.sub_add_cancel hp.out.one_lt.le] at h
  obtain ⟨c, hc⟩ := vsFEig_scalar f a (hspan e heB hep)
  by_cases hall : ∀ u ∈ vsFEig f a, u = 0
  · left
    intro u hu
    rw [hall u hu, map_zero]
  push Not at hall
  obtain ⟨u0, hu0, hu00⟩ := hall
  have hcc : c * c = c := by
    have h1 : e (e u0) = e u0 := by rw [← Module.End.mul_apply, hee]
    rw [hc u0 hu0, map_smul, hc u0 hu0, smul_smul] at h1
    have h2 : (c * c - c) • u0 = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hu00)
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases hc01 with h0 | h1
  · right
    intro u hu hbu
    have h1 := hc u hu
    rw [h0, zero_smul, he1, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      ← hcomm', Module.End.mul_apply, hbu, map_zero, smul_zero, add_zero] at h1
    exact h1
  · left
    intro u hu
    have h2 : e u = u := by rw [hc u hu, h1, one_smul]
    rw [← h2, ← Module.End.mul_apply, hbe, LinearMap.zero_apply]

/-- A unit `T` with `T⁻¹ B T ⊆ B` maps a nonzero joint eigenspace into a joint eigenspace:
`f i (T v) = T ((T⁻¹ f_i T) v)`, and `T⁻¹ f_i T` is a fixed point in `B`, so a scalar on the
eigenspace (`vsFEig_scalar`). -/
theorem vsFEig_map_le (B : Subalgebra (ZMod p) (End (ZMod p) V))
    {ι : Type*} (f : ι → End (ZMod p) V) (hfB : ∀ i, f i ∈ B) (hf : ∀ i, f i ^ p = f i)
    (hspan : ∀ s ∈ B, s ^ p = s → s ∈ Submodule.span (ZMod p) (Set.range f))
    (T : (End (ZMod p) V)ˣ) (hT : ∀ x ∈ B, (↑T⁻¹ : End (ZMod p) V) * x * ↑T ∈ B)
    (a : ι → ZMod p) : ∃ a' : ι → ZMod p, (vsFEig f a).map (T : End (ZMod p) V) ≤ vsFEig f a' := by
  have h : ∀ i, ∃ c : ZMod p, ∀ v ∈ vsFEig f a,
      ((↑T⁻¹ : End (ZMod p) V) * f i * ↑T) v = c • v := fun i =>
    vsFEig_scalar f a (hspan _ (hT _ (hfB i)) (by rw [vsFA_conj_pow, hf i]))
  choose a' ha' using h
  refine ⟨a', ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_vsFEig]
  intro i
  have h1 := congrArg (T : End (ZMod p) V) (ha' i v hv)
  rw [map_smul] at h1
  rw [← h1]
  simp only [Module.End.mul_apply]
  rw [← Module.End.mul_apply (T : End (ZMod p) V) (↑T⁻¹ : End (ZMod p) V), Units.mul_inv,
    Module.End.one_apply]

theorem vsFEig_disjoint {ι : Type*} (f : ι → End (ZMod p) V) {a b : ι → ZMod p} (hab : a ≠ b)
    {v : V} (ha : v ∈ vsFEig f a) (hb : v ∈ vsFEig f b) : v = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
  have h := ((mem_vsFEig f a v).1 ha i).symm.trans ((mem_vsFEig f b v).1 hb i)
  have h2 : (a i - b i) • v = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hi)

/-- A unit `T` normalizing `B` (both `T⁻¹ B T ⊆ B` and `T B T⁻¹ ⊆ B`) maps each nonzero joint
eigenspace onto a joint eigenspace. By `vsFEig_map_le` for `T` and for `T⁻¹`, the eigenspace
`E(a)` lies in some `E(a'')`; two different joint eigenspaces meet only in `0`, so `a'' = a`. -/
theorem vsFEig_map (B : Subalgebra (ZMod p) (End (ZMod p) V))
    {ι : Type*} (f : ι → End (ZMod p) V) (hfB : ∀ i, f i ∈ B) (hf : ∀ i, f i ^ p = f i)
    (hspan : ∀ s ∈ B, s ^ p = s → s ∈ Submodule.span (ZMod p) (Set.range f))
    (T : (End (ZMod p) V)ˣ) (hT : ∀ x ∈ B, (↑T⁻¹ : End (ZMod p) V) * x * ↑T ∈ B)
    (hT' : ∀ x ∈ B, (↑T : End (ZMod p) V) * x * ↑T⁻¹ ∈ B)
    (a : ι → ZMod p) (ha : vsFEig f a ≠ ⊥) :
    ∃ a' : ι → ZMod p, (vsFEig f a).map (T : End (ZMod p) V) = vsFEig f a' := by
  obtain ⟨a', h1⟩ := vsFEig_map_le B f hfB hf hspan T hT a
  obtain ⟨a'', h2⟩ := vsFEig_map_le B f hfB hf hspan T⁻¹ (by simpa using hT') a'
  have hTT : ∀ v, (↑T⁻¹ : End (ZMod p) V) ((T : End (ZMod p) V) v) = v := fun v => by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  have hTT' : ∀ v, (T : End (ZMod p) V) ((↑T⁻¹ : End (ZMod p) V) v) = v := fun v => by
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have h3 : vsFEig f a ≤ vsFEig f a'' := by
    intro v hv
    have : (T : End (ZMod p) V) v ∈ vsFEig f a' := h1 ⟨v, hv, rfl⟩
    have := h2 ⟨_, this, rfl⟩
    rwa [hTT] at this
  have haa : a'' = a := by
    by_contra hne
    apply ha
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot _).2 (vsFEig_disjoint f (Ne.symm hne) hv (h3 hv))
  subst haa
  refine ⟨a', le_antisymm h1 ?_⟩
  intro v hv
  exact ⟨_, h2 ⟨v, hv, rfl⟩, hTT' v⟩

/-- The joint eigenspaces of a family of Frobenius fixed points in a commutative `B` span `V`. -/
theorem vsFEig_iSup [FiniteDimensional (ZMod p) V] (B : Subalgebra (ZMod p) (End (ZMod p) V))
    (hB : ∀ x ∈ B, ∀ y ∈ B, Commute x y) {ι : Type*} (f : ι → End (ZMod p) V)
    (hfB : ∀ i, f i ∈ B) (hf : ∀ i, f i ^ p = f i) : ⨆ a, vsFEig f a = ⊤ :=
  vsFA_iSup_joint f (fun i j => hB _ (hfB i) _ (hfB j)) hf

/-- The joint eigenspaces of a family of Frobenius fixed points in a commutative `B` are
independent, so `V` is their direct sum. -/
theorem vsFEig_indep (B : Subalgebra (ZMod p) (End (ZMod p) V))
    (hB : ∀ x ∈ B, ∀ y ∈ B, Commute x y) {ι : Type*} (f : ι → End (ZMod p) V)
    (hfB : ∀ i, f i ∈ B) (hf : ∀ i, f i ^ p = f i) : iSupIndep fun a => vsFEig f a :=
  vsFA_indep_joint f (fun i j => hB _ (hfB i) _ (hfB j)) hf

/-- If one joint eigenspace is all of `V` and `B` is reduced, every nonzero `b ∈ B` is
injective (so `B` is a field). This is `vsFEig_zero_or_inj` for the eigenspace `V`. -/
theorem vsFField_of_top [FiniteDimensional (ZMod p) V] (B : Subalgebra (ZMod p) (End (ZMod p) V))
    (hN : ∀ y ∈ B, y ^ p = 0 → y = 0) {ι : Type*} (f : ι → End (ZMod p) V) (a : ι → ZMod p)
    (hspan : ∀ s ∈ B, s ^ p = s → s ∈ Submodule.span (ZMod p) (Set.range f))
    (htop : vsFEig f a = ⊤) : ∀ b ∈ B, b = 0 ∨ ∀ v, b v = 0 → v = 0 := by
  intro b hb
  rcases vsFEig_zero_or_inj B hN f a hspan hb with h | h
  · left
    ext v
    exact h v (htop ▸ Submodule.mem_top)
  · right
    intro v hv
    exact h v (htop ▸ Submodule.mem_top) hv

/-! ### Irreducibility by spinning -/

/-- If every nonzero `b ∈ B` is injective and the vectors `b v₀` (`b ∈ B`) span `V`, then every
nonzero `B`-invariant subspace `W` is `V`. For `0 ≠ w ∈ W`, the map `b ↦ b w` is injective on
`B` with image in `W`, so `dim W ≥ dim B ≥ dim V`. -/
theorem vsFSpin_irred [FiniteDimensional (ZMod p) V] (B : Subalgebra (ZMod p) (End (ZMod p) V))
    (hF : ∀ b ∈ B, b = 0 ∨ ∀ v, b v = 0 → v = 0) {v₀ : V}
    (hspan : Submodule.map (LinearMap.applyₗ v₀) (Subalgebra.toSubmodule B) = ⊤)
    (W : Submodule (ZMod p) V) (hW : ∀ b ∈ B, ∀ w ∈ W, b w ∈ W) (hW0 : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  let φ := (LinearMap.applyₗ (R := ZMod p) (M₂ := V) w).domRestrict (Subalgebra.toSubmodule B)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    rcases hF x.1 x.2 with h | h
    · exact Subtype.ext h
    · exact absurd (h w hx) hw0
  have hrange : LinearMap.range φ ≤ W := by
    rintro _ ⟨x, rfl⟩
    exact hW x.1 x.2 w hw
  have h1 : finrank (ZMod p) (Subalgebra.toSubmodule B) = finrank (ZMod p) (LinearMap.range φ) :=
    (LinearMap.finrank_range_of_inj hinj).symm
  have h2 : finrank (ZMod p) V ≤ finrank (ZMod p) (Subalgebra.toSubmodule B) := by
    have := Submodule.finrank_map_le (LinearMap.applyₗ (R := ZMod p) (M₂ := V) v₀)
      (Subalgebra.toSubmodule B)
    rwa [hspan, finrank_top] at this
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le W)
    (h2.trans (h1.le.trans (Submodule.finrank_mono hrange)))

end GI.Proved
