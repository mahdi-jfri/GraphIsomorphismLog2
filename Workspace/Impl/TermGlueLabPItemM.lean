module

public import Workspace.Impl.TermGlueLabPMat
public import Workspace.Impl.TermGlueLabPPoly
public import Workspace.Impl.TermGlueLabPOff

@[expose] public section

/-!
# The matrices of one generator (step 5)

Step 5 of the label program (proof of Theorem A.23). For a generator `g` of the
supplement `S = ⟨gs⟩`, the contract of the affine procedure needs the matrices of `ρ(g)` and
`ρ(g⁻¹)` in the coordinates `E` of `A/B(x)`. The left action is `λ(g) = κ_{g⁻¹}`
(`tmGLlam`), and `κ_{g⁻¹}` sends the class with coordinates `z` to the class with
coordinates `z C`, where row `j` of `C` holds coordinates of `g a_j g⁻¹`
(`tmGLP_κ_g`, `tmGLP_coord_class`). With `E(class of z) = z V mod d` and `U V = 1`, the
matrix is `(i, j) ↦ (U C V)_{j i} mod d_i` (`tmGLP_mat`). This is `tmGLP_item_mat`.

The matrix program `tmGLPMatF` computes exactly this from `C`, and `tmGLPCMatF` computes `C`
on `[gens N, [g, g⁻¹]]` (for `ρ(g)`) and on `[gens N, [g⁻¹, g]]` (for `ρ(g⁻¹)`).
-/

namespace GI.Impl

open GI.Multicoset GI.Cited Equiv

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}
  {x : Fin q → Ω}

/-- The stored generators of `N` lie in `N`. -/
theorem tmGLP_stored_mem {σN : List (Perm (Fin n))} (hN : gens σN = N) (i : Fin σN.length) :
    σN[i.val] ∈ N :=
  hN ▸ Subgroup.subset_closure (List.getElem_mem _)

/-- **The matrix of `ρ(g)`.** Let `E` be coordinates of `A/B(x)` with `E(class of z) = z V mod d`
for the stored generators of `N`, let `U V = 1`, and let row `j` of `C` be coordinates of
`g a_j g⁻¹`. Then the contract's matrix of `ρ(g) = E ∘ κ_{g⁻¹} ∘ E⁻¹` is
`(i, j) ↦ (U C V)_{j i} mod d_i`. -/
theorem tmGLP_item_mat {hn : GI.Multicoset.Normalizes H N} {hker : TmGLKer N H φ} {hNH : N ≤ H}
    {gs : List (Perm (Fin n))} {hgs : gens gs ≤ Aut H (types N x)}
    {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {U V D C : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (hUV : U * V = 1) (E : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z) (g : gens gs)
    (hCm : ∀ j : Fin σN.length, (g : Perm (Fin n)) * σN[j.val] * (g : Perm (Fin n))⁻¹ ∈ gens σN)
    (hC : ∀ j : Fin σN.length,
      TmGLPCoordOf σN ((g : Perm (Fin n)) * σN[j.val] * (g : Perm (Fin n))⁻¹) (C j)) :
    tmGLMat (tmGLQMod D) (tmGLρE E (tmGLlam hn hker hgs hNH) g).toAddMonoidHom =
      fun i j => (U * C * V) j i % D i i := by
  have hD : (g : Perm (Fin n))⁻¹ ∈ Aut H (types N x) := hgs ((gens gs).inv_mem g.2)
  have hC' : ∀ j, tmGLPg N φ x (fun i => σN[i.val]) (C j) =
      Additive.ofMul (tmGLc N φ x (((g : Perm (Fin n))⁻¹)⁻¹ * σN[j.val] * (g : Perm (Fin n))⁻¹)) := by
    intro j
    rw [inv_inv]
    exact tmGLP_coord_class hN (hCm j) (hC j)
  refine tmGLP_mat hpos hUV E hE (tmGLlam hn hker hgs hNH g).toMonoidHom ?_ _ ?_
  · intro z
    exact tmGLP_κ_g (hn := hn) (hker := hker) (tmGLP_stored_mem hN) hD hC' z
  · intro w
    exact tmGLρE_apply E _ g (Additive.toMul w)

/-- **The matrix of `ρ(g⁻¹)`**: the same with `g⁻¹`, so row `j` of `C` holds coordinates of
`g⁻¹ a_j g`. -/
theorem tmGLP_item_mat_inv {hn : GI.Multicoset.Normalizes H N} {hker : TmGLKer N H φ}
    {hNH : N ≤ H} {gs : List (Perm (Fin n))} {hgs : gens gs ≤ Aut H (types N x)}
    {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {U V D C : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (hUV : U * V = 1) (E : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z) (g : gens gs)
    (hCm : ∀ j : Fin σN.length, (g : Perm (Fin n))⁻¹ * σN[j.val] * (g : Perm (Fin n)) ∈ gens σN)
    (hC : ∀ j : Fin σN.length,
      TmGLPCoordOf σN ((g : Perm (Fin n))⁻¹ * σN[j.val] * (g : Perm (Fin n))) (C j)) :
    tmGLMat (tmGLQMod D) (tmGLρE E (tmGLlam hn hker hgs hNH) g⁻¹).toAddMonoidHom =
      fun i j => (U * C * V) j i % D i i := by
  refine tmGLP_item_mat hN hpos hUV E hE g⁻¹ (fun j => ?_) (fun j => ?_)
  · simpa using hCm j
  · simpa using hC j

/-! ### The offsets -/

/-- **A sum of coordinate vectors gives the product of the classes.** -/
theorem tmGLP_csum_class {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {ys : List (Perm (Fin n))} (hy : ∀ y ∈ ys, y ∈ gens σN) {zs : List (Fin σN.length → ℤ)}
    (hz : List.Forall₂ (TmGLPCoordOf σN) ys zs) :
    tmGLPg N φ x (fun i => σN[i.val]) zs.sum = Additive.ofMul (ys.map (tmGLc N φ x)).prod := by
  induction hz with
  | nil => simp
  | @cons y z ys zs hyz _ ih =>
    rw [List.sum_cons, map_add, ih fun w hw => hy w (List.mem_cons_of_mem _ hw),
      tmGLP_coord_class hN (hy y (List.mem_cons_self ..)) hyz, List.map_cons, List.prod_cons]
    rfl

/-- The same for the list `1 :: xs` that `tmGLPCSum_spec` reads. -/
theorem tmGLP_csum_class' {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {xs : List (Perm (Fin n))} (hx : ∀ y ∈ xs, y ∈ gens σN) {zs : List (Fin σN.length → ℤ)}
    (hz : List.Forall₂ (TmGLPCoordOf σN) (1 :: xs) zs) :
    tmGLPg N φ x (fun i => σN[i.val]) zs.sum = Additive.ofMul (xs.map (tmGLc N φ x)).prod := by
  rw [tmGLP_csum_class hN (fun y hy => ?_) hz, List.map_cons, List.prod_cons, tmGLc_one, one_mul]
  rcases List.mem_cons.mp hy with rfl | hy
  · exact (gens σN).one_mem
  · exact hx y hy

/-- **The offset vector of a generator.** If the classes of `xs` multiply to the offset
`o(g)` and `zs` are coordinate vectors of `1 :: xs`, then the contract's offset vector is
`(Σ zs) V mod d`. -/
theorem tmGLP_item_off {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (E : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z)
    {gs : List (Perm (Fin n))} (o : gens gs → tmGLV N φ x) (g : gens gs)
    {xs : List (Perm (Fin n))} (hx : ∀ y ∈ xs, y ∈ gens σN)
    (hu : (xs.map (tmGLc N φ x)).prod = o g) {zs : List (Fin σN.length → ℤ)}
    (hz : List.Forall₂ (TmGLPCoordOf σN) (1 :: xs) zs) :
    tmGLVecZ (tmGLcE E o g) = fun i => Matrix.vecMul zs.sum V i % D i i := by
  rw [tmGLcE, ← hu, ← tmGLP_csum_class' hN hx hz, hE]
  exact tmGLP_vecZ hpos _

/-- The classes of a list of row transporters followed by a list of lift parts. -/
theorem tmGLP_prod_ofFn (s t : Fin q → Perm (Fin n)) :
    ((List.ofFn s ++ List.ofFn t).map (tmGLc N φ x)).prod =
      (∏ i, tmGLc N φ x (s i)) * ∏ i, tmGLc N φ x (t i) := by
  rw [List.map_append, List.prod_append, List.map_ofFn, List.map_ofFn, List.prod_ofFn,
    List.prod_ofFn]
  rfl

/-- **The offset of a generator from the program's data.** For `g ∈ S`, put `h = g⁻¹`. Let
`s_i ∈ N` be row transporters `rep(type x_i)^h = rep(type x_i ^h)^{s_i}` and let `k(h) ν` be a
blockwise lift with `ν` zero-sum. Then the list `s_0, …, s_{q-1}, h⁻¹ k(h)_0 ν_0, …` has class
product `o(g) = u(g⁻¹)` (`tmGLP_u_rows`). -/
theorem tmGLP_item_u (hn : GI.Multicoset.Normalizes H N) (hker : TmGLKer N H φ)
    {k : Perm (Fin n) → Fin q → Perm (Fin n)} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) {gs : List (Perm (Fin n))} (g : gens gs)
    (hD : (g : Perm (Fin n))⁻¹ ∈ Aut H (types N x)) {s : Fin q → Perm (Fin n)}
    (hs : ∀ i, s i ∈ N)
    (hsr : ∀ i, rep (orbitN N (x i)) ↼ (g : Perm (Fin n))⁻¹ =
      rep (orbitN N (x i) ↼ (g : Perm (Fin n))⁻¹) ↼ s i)
    {ν : Fin q → Perm (Fin n)} (hν : TmGLZero N φ ν) :
    ((List.ofFn s ++ List.ofFn fun i => (g : Perm (Fin n)) * (k (g : Perm (Fin n))⁻¹ i * ν i)).map
      (tmGLc N φ x)).prod = tmGLo rep k g := by
  rw [tmGLP_prod_ofFn, tmGLo, ← tmGLP_u_rows hn hker hk hrep hD hs hsr hν, inv_inv]

end GI.Impl
