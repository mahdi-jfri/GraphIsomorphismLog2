module

public import Workspace.Impl.AddEquivGroup
public import Workspace.Impl.TermGlueLabRT
public import Workspace.Lang.Lib.LinIntVector

@[expose] public section

/-!
# The contract of the finite abelian affine transporter procedure

Proof of Theorem A.20, "Solving the affine compatibility condition": a solvable
permutation group acts affinely on a finite abelian group `V`, given in finite-abelian
coordinates. Split `V` into primary components `V_p` with the filtrations `p^j V_p`, transport
modulo one level at a time, homogenize to a linear representation over `𝔽_p`, call Luks–Miyazaki's
VectorStabilizer ([LM, Theorem 1.4 and Section 5.2]), use the two-copy wreath extension for
transporters, and lift with straight-line programs. "Every characteristic satisfies `p ≤ b`"
(Theorem A.23 adds the orientation factor: "the characteristic bound is `p ≤ max{b, 2}`"),
and "the entire affine calculation is polynomial in `b + M`, including lifting".

Theorem A.23 uses the same procedure ("The finite abelian affine transporter procedure in the
proof of Theorem A.20 now imposes both labels in polynomial time within this radical coset").
`TmGLAffineSpec Pg K D j` states it as a function `j` of a `GI.Lang` program, built from
the `Lin*` programs; `TermGlueObjSpec` and the label step both call it.

**Data.** A solvable `S = ⟨gs⟩ ≤ Sym(n)`; moduli `m : Fin d → ℕ`, all positive, with every prime
divisor at most `max n 2`; the coordinates `V = ∏_i ℤ/m_i` (`tmGLVec m`); a left affine action
`g · v = ρ(g) v + c(g)`, with `ρ : S →* Aut(V)` and the cocycle identity
`c(gh) = ρ(g) c(h) + c(g)`; two points `v, w`. The action need not be faithful.

**Encoding** (`tmGLAffIn`). `[gens S, m, [item_g for g in gs], v, w]`, with
`item_g = [M(ρ g), c g, M(ρ g⁻¹), c g⁻¹]`. A matrix `M(f)` has entry `(i, j)` equal to the
reduced coordinate `i` of `f(e_j)` (`tmGLMat`, the convention of `linFiniteMatrix`); vectors
are reduced coordinate lists. All numbers are integers in binary (`encInt`, `linVecVal`,
`encIntMatrix`). The data of the inverse are given too: they are free for the callers, and
the procedure then needs no inversion in `V`.

**Output** (`TmGLAffOut`). `[]` if no `g ∈ S` has `g · v = w`; otherwise `[t, gens L]` with
`{g ∈ S | g · v = w} = t ⟨L⟩`. So `⟨L⟩` is the stabilizer of `v` and `t` a transporter.

**Cost.** `K (wt + 1)^D` in the input weight.

The convention is a left action because `VecStabInst` and the `Lin*` programs use
homomorphisms. The paper writes right actions; a right action `F` becomes the left action
`g · v = F_{g⁻¹}(v)` (`tmGL_left_of_right`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open scoped Pointwise

/-! ### Finite abelian coordinates -/

/-- **Finite abelian coordinates** `∏_i ℤ/m_i`. -/
abbrev tmGLVec {d : ℕ} (m : Fin d → ℕ) : Type := ∀ i, ZMod (m i)

/-- The reduced coordinates of a vector. -/
def tmGLVecZ {d : ℕ} {m : Fin d → ℕ} (v : tmGLVec m) : Fin d → ℤ := fun i => ((v i).val : ℤ)

/-- The matrix of an additive map: entry `(i, j)` is the reduced coordinate `i` of the image of
the basis vector `e_j`. -/
noncomputable def tmGLMat {d : ℕ} (m : Fin d → ℕ) (f : tmGLVec m →+ tmGLVec m) :
    Matrix (Fin d) (Fin d) ℤ :=
  fun i j => ((f (Pi.single j 1) i).val : ℤ)

/-- The moduli as a vector. -/
def tmGLModZ {d : ℕ} (m : Fin d → ℕ) : Fin d → ℤ := fun i => (m i : ℤ)

/-! ### The encoding -/

variable {n d : ℕ}

/-- The data of one element: `[M(ρ g), c g, M(ρ g⁻¹), c g⁻¹]`. -/
noncomputable def tmGLAffItem (gs : List (Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (tmGLVec m ≃+ tmGLVec m)) (c : gens gs → tmGLVec m) (g : gens gs) : Val :=
  .list [encIntMatrix (tmGLMat m (ρ g).toAddMonoidHom), linVecVal (tmGLVecZ (c g)),
    encIntMatrix (tmGLMat m (ρ g⁻¹).toAddMonoidHom), linVecVal (tmGLVecZ (c g⁻¹))]

/-- **The input of the procedure**: `[gens S, m, [item_g], v, w]`. -/
noncomputable def tmGLAffIn (gs : List (Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (tmGLVec m ≃+ tmGLVec m)) (c : gens gs → tmGLVec m) (v w : tmGLVec m) :
    Val :=
  .list [encGroup gs, linVecVal (tmGLModZ m),
    .list (gs.attach.map fun g => tmGLAffItem gs m ρ c ⟨g.1, Subgroup.subset_closure g.2⟩),
    linVecVal (tmGLVecZ v), linVecVal (tmGLVecZ w)]

/-- **The transporter** `{g ∈ S | ρ(g) v + c(g) = w}`, as permutations. -/
def tmGLAffTrans (gs : List (Perm (Fin n))) {m : Fin d → ℕ}
    (ρ : gens gs →* (tmGLVec m ≃+ tmGLVec m)) (c : gens gs → tmGLVec m) (v w : tmGLVec m) :
    Set (Perm (Fin n)) :=
  Subtype.val '' {g : gens gs | ρ g v + c g = w}

/-- **The output**: `[]` for an empty transporter, else `[t, gens L]` with transporter `t ⟨L⟩`. -/
def TmGLAffOut (n : ℕ) (u : Val) (T : Set (Perm (Fin n))) : Prop :=
  (u = .list [] ∧ T = ∅) ∨ ∃ (t : Perm (Fin n)) (L : List (Perm (Fin n))),
    u = .list [encPerm t, encGroup L] ∧ T = t • (gens L : Set (Perm (Fin n)))

namespace Iface

/-- **The finite abelian affine transporter procedure** (proof of Theorem A.20, "Solving the
affine compatibility condition"), as the function `j` of `Pg`. -/
def TmGLAffineSpec (Pg : Program) (K D j : ℕ) : Prop :=
  ∀ {n d : ℕ} (gs : List (Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (tmGLVec m ≃+ tmGLVec m)) (c : gens gs → tmGLVec m) (v w : tmGLVec m),
    IsSolvable ρ.range →
    (∀ i, 0 < m i) →
    -- "the invariant factors ... have no prime divisors above `b`" (with the orientation
    -- factor, `p ≤ max {b, 2}`)
    (∀ i p, p.Prime → p ∣ m i → p ≤ max n 2) →
    -- the cocycle identity: `g · v = ρ(g) v + c(g)` is an action
    (∀ g h, c (g * h) = ρ g (c h) + c g) →
    FunAll Pg j (tmGLAffIn gs m ρ c v w) (fun u cost =>
      TmGLAffOut n u (tmGLAffTrans gs ρ c v w) ∧
      cost ≤ K * ((tmGLAffIn gs m ρ c v w).wt + 1) ^ D)

end Iface

/-! ### Right actions -/

/-- **A right action as a left action.** If `F` is a right action of a group `G` (`F_{gh} =
F_h ∘ F_g`, `F_1 = id`), then `g · v = F_{g⁻¹}(v)` is a left action, and its transporter from
`w` to `v` is the inverse of the right transporter from `v` to `w`. -/
theorem tmGL_left_of_right {G X : Type*} [Group G] (F : G → X → X)
    (hone : ∀ v, F 1 v = v) (hmul : ∀ g h v, F (g * h) v = F h (F g v)) (v w : X) (g : G) :
    F g⁻¹ w = v ↔ F g v = w := by
  constructor
  · rintro rfl
    rw [← hmul, inv_mul_cancel, hone]
  · rintro rfl
    rw [← hmul, mul_inv_cancel, hone]

/-- **Encoding a right action for the contract.** Let `F` be a right action of `⟨gs⟩` on `X`
that keeps a set `Q`, and let `E : X → V` be injective on `Q` with
`ρ(g) E(p) + c(g) = E(F_{g⁻¹} p)` for `p ∈ Q`. Then the contract's transporter from `E p'` to
`E p` is the right transporter of `F` from `p` to `p'`. -/
theorem tmGL_enc_trans {X : Type*} (gs : List (Perm (Fin n))) {m : Fin d → ℕ}
    (F : Perm (Fin n) → X → X) (hone : ∀ v, F 1 v = v)
    (hmul : ∀ g ∈ gens gs, ∀ h ∈ gens gs, ∀ v, F (g * h) v = F h (F g v))
    (Q : Set X) (hQ : ∀ g ∈ gens gs, ∀ p ∈ Q, F g p ∈ Q) (E : X → tmGLVec m)
    (hE : Set.InjOn E Q) (ρ : gens gs →* (tmGLVec m ≃+ tmGLVec m)) (c : gens gs → tmGLVec m)
    (hρ : ∀ g : gens gs, ∀ p ∈ Q, ρ g (E p) + c g = E (F (g : Perm (Fin n))⁻¹ p))
    {p p' : X} (hp : p ∈ Q) (hp' : p' ∈ Q) :
    tmGLAffTrans gs ρ c (E p') (E p) = {g | g ∈ gens gs ∧ F g p = p'} := by
  ext g
  simp only [tmGLAffTrans, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨g, hg⟩, he, rfl⟩
    refine ⟨hg, ?_⟩
    rw [hρ ⟨g, hg⟩ p' hp'] at he
    have h1 := hE (hQ _ ((gens gs).inv_mem hg) p' hp') hp he
    show F g p = p'
    rw [← h1, ← hmul _ ((gens gs).inv_mem hg) g hg, inv_mul_cancel, hone]
  · rintro ⟨hg, he⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [hρ ⟨g, hg⟩ p' hp', ← he]
    congr 1
    show F g⁻¹ (F g p) = p
    rw [← hmul g hg _ ((gens gs).inv_mem hg), mul_inv_cancel, hone]

end GI.Impl
