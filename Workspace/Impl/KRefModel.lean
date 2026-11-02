import Workspace.Cited.AlgoRefinement
import Mathlib.Data.Nat.Digits.Defs

/-!
# The joint `k`-ary Weisfeiler–Leman refinement as Lean functions

This file defines, as plain Lean functions, what the `k`-ary refinement program computes. It
follows [H] = Helfgott–Bajpai–Dona, arXiv:1710.04574v1, Sections 2.3–2.5 (`k`-ary
Weisfeiler–Leman, Algorithm 3), run on the two input colorings at once.

The two colorings are one function `col : Bool → (Fin k → Fin n) → ℕ` (`false` is the first
input, `true` the second). One round gives each tuple `x` of input `β` a signature, a list of
numbers:
* its old color `col β x`;
* its equality pattern `krefPat x` (for each entry, the first position holding the same point);
* the colors `col β (x ∘ τ)` for all maps `τ : Fin k → Fin k`;
* for each `u`, the number of points `z` whose vector `(col β (x with entry i replaced by z))_i`
  has rank `u` among the vectors of both inputs.

Lists are turned into numbers by Horner's rule in a base `B` above every entry
(`krefHorner`), and the new color of `x` is the rank of its signature code among the codes of
all tuples of both inputs (`krefRank`: the number of codes below it). The rank does not depend
on how the tuples are named, and it is below the number `2 n^k` of tuples.
-/

namespace GI.Impl

open GI.Cited Equiv

/-! ### Horner codes -/

/-- Horner's rule in base `B`, starting from `a`. -/
def krefHornerFrom (B a : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc d => acc * B + d) a

/-- Horner's rule in base `B`. -/
def krefHorner (B : ℕ) (l : List ℕ) : ℕ := krefHornerFrom B 0 l

theorem krefHornerFrom_append (B a : ℕ) (l₁ l₂ : List ℕ) :
    krefHornerFrom B a (l₁ ++ l₂) = krefHornerFrom B (krefHornerFrom B a l₁) l₂ :=
  List.foldl_append

theorem krefHornerFrom_eq (B a : ℕ) (l : List ℕ) :
    krefHornerFrom B a l = a * B ^ l.length + Nat.ofDigits B l.reverse := by
  induction l using List.reverseRecOn generalizing a with
  | nil => simp [krefHornerFrom]
  | append_singleton l d ih =>
    rw [krefHornerFrom_append, ih]
    simp only [krefHornerFrom, List.foldl_cons, List.foldl_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      Nat.ofDigits_cons, List.length_append, List.length_singleton, pow_succ]
    ring

theorem krefHorner_eq (B : ℕ) (l : List ℕ) : krefHorner B l = Nat.ofDigits B l.reverse := by
  simp [krefHorner, krefHornerFrom_eq]

/-- Horner codes of lists of the same length with entries below `B` are equal only for equal
lists. -/
theorem krefHorner_inj {B : ℕ} (hB : 1 < B) {l₁ l₂ : List ℕ} (hl : l₁.length = l₂.length)
    (h₁ : ∀ a ∈ l₁, a < B) (h₂ : ∀ a ∈ l₂, a < B) (h : krefHorner B l₁ = krefHorner B l₂) :
    l₁ = l₂ := by
  rw [krefHorner_eq, krefHorner_eq] at h
  have := Nat.ofDigits_inj_of_len_eq hB (by simpa using hl) (by simpa using h₁)
    (by simpa using h₂) h
  simpa using this

/-! ### Ranks -/

/-- The rank of `q` in `L`: the number of entries of `L` below `q`. -/
def krefRank (L : List ℕ) (q : ℕ) : ℕ := L.countP fun y => decide (y < q)

theorem krefRank_le_of_lt {p q : ℕ} (h : p < q) (L : List ℕ) : krefRank L p ≤ krefRank L q := by
  induction L with
  | nil => simp [krefRank]
  | cons a L ih =>
    simp only [krefRank, List.countP_cons] at ih ⊢
    by_cases ha : a < p
    · simp [ha, show a < q by omega]; omega
    · by_cases hb : a < q <;> simp [ha, hb] <;> omega

theorem krefRank_lt_of_lt {p q : ℕ} (h : p < q) {L : List ℕ} (hp : p ∈ L) :
    krefRank L p < krefRank L q := by
  induction L with
  | nil => simp at hp
  | cons a L ih =>
    have hle := krefRank_le_of_lt h L
    simp only [krefRank, List.countP_cons] at hle ih ⊢
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [h]; omega
    · have := ih hp
      by_cases ha : a < p
      · simp [ha, show a < q by omega]; omega
      · by_cases hb : a < q <;> simp [ha, hb] <;> omega

/-- The rank is one-to-one on the entries of `L`. -/
theorem krefRank_inj {L : List ℕ} {p q : ℕ} (hp : p ∈ L) (hq : q ∈ L)
    (h : krefRank L p = krefRank L q) : p = q := by
  rcases lt_trichotomy p q with hl | rfl | hl
  · exact absurd h (krefRank_lt_of_lt hl hp).ne
  · rfl
  · exact absurd h (krefRank_lt_of_lt hl hq).ne'

theorem krefRank_lt_length {L : List ℕ} {q : ℕ} (hq : q ∈ L) : krefRank L q < L.length := by
  unfold krefRank
  have h1 := List.countP_le_length (p := fun y => decide (y < q)) (l := L)
  have h2 : L.countP (fun y => decide (y < q)) ≠ L.length := by
    rw [Ne, List.countP_eq_length]
    intro h
    simpa using h q hq
  omega

/-! ### Tuples -/

/-- The tuples `Fin k → Fin n` in the order of their indices under `finFunctionFinEquiv`. -/
def krefTups (n k : ℕ) : List (Fin k → Fin n) :=
  (List.finRange (n ^ k)).map finFunctionFinEquiv.symm

theorem mem_krefTups {n k : ℕ} (x : Fin k → Fin n) : x ∈ krefTups n k := by
  unfold krefTups
  exact List.mem_map.mpr ⟨finFunctionFinEquiv x, List.mem_finRange _, by simp⟩

theorem length_krefTups (n k : ℕ) : (krefTups n k).length = n ^ k := by simp [krefTups]

/-- The entries of a tuple, as numbers. -/
def krefDig {n k : ℕ} (x : Fin k → Fin n) : List ℕ := List.ofFn fun i => (x i : ℕ)

/-- The equality pattern of a tuple: for each entry, the first position holding the same point. -/
def krefPat {n k : ℕ} (x : Fin k → Fin n) : List ℕ :=
  (krefDig x).map fun a => (krefDig x).findIdx fun y => decide (y = a)

/-! ### One round -/

/-- Two `k`-ary colorings of `Fin n` at once: `false` is the first input, `true` the second. -/
abbrev KCol (n k : ℕ) : Type := Bool → (Fin k → Fin n) → ℕ

/-- The base of the Horner codes: above every color (at most `2 n^k`), every count (at most `n`)
and every entry of a pattern (below `k`). -/
def krefB (n k : ℕ) : ℕ := 2 * n ^ k + n + k + 2

/-- The number of vectors of both inputs together. -/
def krefM (n k : ℕ) : ℕ := 2 * n ^ k * n

variable {n k : ℕ}

/-- The vector of `x` at `z`: the colors of `x` with entry `i` replaced by `z`. -/
def krefVec (col : KCol n k) (β : Bool) (x : Fin k → Fin n) (z : Fin n) : List ℕ :=
  List.ofFn fun i => col β (Function.update x i z)

/-- The codes of the vectors of input `β`, one list over `z` for each tuple. -/
def krefVCodes (col : KCol n k) (β : Bool) : List (List ℕ) :=
  (krefTups n k).map fun x => List.ofFn fun z => krefHorner (krefB n k) (krefVec col β x z)

/-- The codes of the vectors of both inputs. -/
def krefVAll (col : KCol n k) : List ℕ :=
  (krefVCodes col false).flatten ++ (krefVCodes col true).flatten

/-- The ranks of the vectors of `x`, over `z`. -/
def krefRl (col : KCol n k) (β : Bool) (x : Fin k → Fin n) : List ℕ :=
  List.ofFn fun z => krefRank (krefVAll col) (krefHorner (krefB n k) (krefVec col β x z))

/-- For each rank `u`, the number of points `z` whose vector has rank `u`. -/
def krefCounts (col : KCol n k) (β : Bool) (x : Fin k → Fin n) : List ℕ :=
  (List.range (krefM n k)).map fun u => (krefRl col β x).count u

/-- The colors of `x ∘ τ` for all maps `τ`. -/
def krefTauCols (col : KCol n k) (β : Bool) (x : Fin k → Fin n) : List ℕ :=
  (krefTups k k).map fun τ => col β (x ∘ τ)

/-- The signature of `x`. -/
def krefSig (col : KCol n k) (β : Bool) (x : Fin k → Fin n) : List ℕ :=
  [col β x] ++ krefPat x ++ krefTauCols col β x ++ krefCounts col β x

/-- The signature codes of input `β`. -/
def krefSCodes (col : KCol n k) (β : Bool) : List ℕ :=
  (krefTups n k).map fun x => krefHorner (krefB n k) (krefSig col β x)

/-- The signature codes of both inputs. -/
def krefSAll (col : KCol n k) : List ℕ := krefSCodes col false ++ krefSCodes col true

/-- One round: the rank of the signature code among all signature codes. -/
def krefStep (col : KCol n k) : KCol n k :=
  fun β x => krefRank (krefSAll col) (krefHorner (krefB n k) (krefSig col β x))

/-- The two inputs as one joint coloring. -/
def krefJoin (c c' : (Fin k → Fin n) → ℕ) : KCol n k := fun β => if β then c' else c

/-- `t` rounds. -/
def krefIter (c c' : (Fin k → Fin n) → ℕ) : ℕ → KCol n k
  | 0 => krefJoin c c'
  | t + 1 => krefStep (krefIter c c' t)

end GI.Impl
