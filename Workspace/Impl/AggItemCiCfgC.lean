module

public import Workspace.Impl.AggItemCiCfgR

@[expose] public section

/-!
# The configuration query: the canonical value of the pair structure

The program asks `Solve` on the pair structure `itcqPT X Y hc` of the fibers. Its canonical
value (`Canon`) uses the numbering `itciPE n` of the positions and:
* the group by the diagonal transpositions `itciD n (swap i j)`, `i < j` (they generate the
  diagonal group, `itcq_sw_closure`);
* the domain: everything;
* the colors: `c'` numbers a color by its first place in the list `itcqCL` of all pair colors of
  `X` then of `Y` (`itcqCode`, injective, below `2 n²` on the colors that occur);
* no hierarchy, no rows, `h = 2`, `N = n²`.
`itcq_canon` is the statement, and `itcq_goodLt` gives the measure decrease when `q² < N`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup)

noncomputable section

variable {q : ℕ}

/-- The transpositions `swap i j` of `Fin n`, numbered by `g = n i + j` (with `i = j` giving
the identity). -/
def itcqSw (n : ℕ) : List (Perm (Fin n)) :=
  (List.finRange (n * n)).map fun g => swap ((itciPE n).symm g).1 ((itciPE n).symm g).2

theorem itcq_sw_length (n : ℕ) : (itcqSw n).length ≤ n * n := by
  simp [itcqSw]

theorem itcq_sw_closure (n : ℕ) : Subgroup.closure {s | s ∈ itcqSw n} = ⊤ := by
  rw [eq_top_iff, ← closure_isSwap]
  refine Subgroup.closure_le _ |>.2 fun σ ⟨x, y, _, h⟩ => ?_
  subst h
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_setOf_eq, itcqSw, List.mem_map, List.mem_finRange, true_and]
  exact ⟨itciPE n (x, y), by simp⟩

/-- The generators of the diagonal group, numbered. -/
def itcqGs (n : ℕ) : List (Perm (Fin (n * n))) := (itcqSw n).map (itciD n)

theorem itcq_group (n : ℕ) :
    GroupValC (n * n) (encGroup (itcqGs n)) (groupFin (itciPE n) (diagHom n).range) := by
  refine ⟨itcqGs n, rfl, ?_, ?_⟩
  · unfold gens itcqGs groupFin
    have : {g | g ∈ (itcqSw n).map (itciD n)} = (itciD n) '' {s | s ∈ itcqSw n} := by
      ext g; simp
    rw [this, ← MonoidHom.map_closure, itcq_sw_closure, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
    rfl
  · rw [itcqGs, List.length_map]
    have := itcq_sw_length n
    have : n * n ≤ (n * n) ^ 2 := by nlinarith
    omega

/-- All pair colors of `X` then of `Y`, by numbered position. -/
def itcqCL (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) : List ℕ :=
  (List.finRange (X.fiber.card * X.fiber.card)).map (fun t => itcqPC X rfl ((itciPE _).symm t)) ++
    (List.finRange (X.fiber.card * X.fiber.card)).map
      (fun t => itcqPC Y hc.symm ((itciPE _).symm t))

theorem itcqCL_length (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) :
    (itcqCL X Y hc).length = 2 * (X.fiber.card * X.fiber.card) := by
  simp [itcqCL]; ring

/-- The color code: the first place in `itcqCL`, or past the list. -/
def itcqCode (l : List ℕ) (v : ℕ) : ℕ := if v ∈ l then l.idxOf v else l.length + v

theorem itcqCode_injective (l : List ℕ) : Function.Injective (itcqCode l) := by
  intro v w h
  unfold itcqCode at h
  by_cases hv : v ∈ l <;> by_cases hw : w ∈ l <;> simp only [hv, hw, if_true, if_false] at h
  · exact (List.idxOf_inj hv).1 h
  · have := List.idxOf_lt_length_iff.2 hv; omega
  · have := List.idxOf_lt_length_iff.2 hw; omega
  · omega

theorem itcqCode_lt {l : List ℕ} {v : ℕ} (hv : v ∈ l) : itcqCode l v < l.length := by
  rw [itcqCode, if_pos hv]; exact List.idxOf_lt_length_iff.2 hv

/-- The colors of the pair structure, as numbers. -/
def itcqXV (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) : Val :=
  encFun fun t : Fin (X.fiber.card * X.fiber.card) =>
    itcqCode (itcqCL X Y hc) (itcqPC X rfl ((itciPE _).symm t))

def itcqYV (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) : Val :=
  encFun fun t : Fin (X.fiber.card * X.fiber.card) =>
    itcqCode (itcqCL X Y hc) (itcqPC Y hc.symm ((itciPE _).symm t))

/-- **The canonical value of the pair structure.** -/
def itcqArg (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) : Val :=
  .list [.nat (X.fiber.card * X.fiber.card), encGroup (itcqGs X.fiber.card),
    encFun fun _ : Fin (X.fiber.card * X.fiber.card) => 1, itcqXV X Y hc, itcqYV X Y hc,
    .list [], .list [], boolVal false, .nat 2, .nat (X.fiber.card * X.fiber.card)]

theorem itcq_canon (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) :
    Canon (itciPE X.fiber.card) (itcqCode (itcqCL X Y hc)) (itcqArg X Y hc) (itcqPT X Y hc) := by
  refine ⟨⟨_, _, _, _, _, _, itcq_group _, ?_, rfl, rfl, ⟨[], rfl, List.Forall₂.nil⟩, rfl, rfl⟩,
    fun a => ⟨?_, ?_⟩, le_rfl, ⟨fun I hI => by simp [itcqPT, pairState] at hI, by
      simp [itcqPT, pairState, rhoNat], fun R hR => by simp [itcqPT, pairState] at hR⟩⟩
  · show encFun _ = encFun _
    congr 1
    funext i
    simp [itcqPT, pairState]
  · rw [← itcqCL_length]
    refine itcqCode_lt ?_
    simp only [itcqCL, List.mem_append, List.mem_map, List.mem_finRange, true_and]
    exact Or.inl ⟨itciPE _ a, by simp [itcqPT, pairState]⟩
  · rw [← itcqCL_length]
    refine itcqCode_lt ?_
    simp only [itcqCL, List.mem_append, List.mem_map, List.mem_finRange, true_and]
    exact Or.inr ⟨itciPE _ a, by simp [itcqPT, pairState]⟩

theorem itcq_size (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) :
    (itcqPT X Y hc).size = X.fiber.card * X.fiber.card := pairState_size _ _ _

/-- `q² < N` from the exact test `q⁵ ≤ N²` (for `q ≥ 2`). -/
theorem itcq_sq_lt {N : ℕ} (h : q ^ 5 ≤ N ^ 2) (hq : 2 ≤ q) : q * q < N := by
  by_contra hN
  push_neg at hN
  have h1 : N ^ 2 ≤ (q * q) ^ 2 := Nat.pow_le_pow_left hN 2
  have h2 : (q * q) ^ 2 < q ^ 5 := by
    have : (q * q) ^ 2 = q ^ 4 := by ring
    rw [this]; exact Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

/-- **The measure decreases** for the pair structure when `n² < N`. -/
theorem itcq_lt {Ω C : Type} {S : State Ω C} (X Y : PairCfg q)
    (hc : X.fiber.card = Y.fiber.card) (h : X.fiber.card * X.fiber.card < S.N) :
    MLt (measure P₀ .solve (itcqPT X Y hc)) (measure P₀ .giant S) := by
  rw [mlt_iff]
  left
  simp only [Algorithm.measure, Algorithm.major]
  rw [itcq_size]
  exact h

end

end GI.Impl
