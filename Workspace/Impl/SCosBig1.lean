import Workspace.Impl.SCosBigMath3
import Workspace.Impl.SCosPaste5

/-!
# Function 5 (`bigF`), the tools

Function `5` is a chain of nine `let`s followed by the children and the paste. We bound every
step by one budget `scosBigD n c`, a power of the scale `scosBigS n c = M Q` (with
`Q = (N + 1)^6`, `M = scosPasteM n c`, `N = n + n`), so that the final sum is easy.

* `ScosBigPost X`: the postcondition of `scos_big_spec`, with the own cost `X`.
  `scosBig_letR` takes one `let` off the chain: it adds the cost of the bound value and the
  weight of the answer (at most `700 Q`).
* Small facts used by the steps: the value of `scosPowE`, the class representatives of the
  labels `labN` (`scosBig_reprVal`), the labels as a `gather` (`scosBig_gather_eq`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### The scale and the budget -/

/-- The scale: `M Q`, with `M = scosPasteM n c` and `Q = (n + n + 1)^6`. -/
def scosBigS (n c : ℕ) : ℕ := scosPasteM n c * (n + n + 1) ^ 6

/-- The budget of one step of the chain. -/
def scosBigD (n c : ℕ) : ℕ := 10 ^ 40 * (c + 1) * scosBigS n c ^ 7

theorem scosBigS_facts (n c : ℕ) : (n + n + 1) ^ 6 ≤ scosBigS n c ∧
    (n + n + 1) ^ 6 * (n + n + 1) ^ 6 ≤ scosBigS n c ∧ scosPasteM n c ≤ scosBigS n c ∧
    (n + n + 1) ^ c + 1 ≤ scosBigS n c ∧ 1 ≤ scosBigS n c := by
  have hQ := (scosPaste_Q n).1
  have hB : 1 ≤ (n + n + 1) ^ c + 1 := by omega
  have hM1 : (n + n + 1) ^ 6 ≤ scosPasteM n c := Nat.le_mul_of_pos_right _ hB
  have hM2 : (n + n + 1) ^ c + 1 ≤ scosPasteM n c := Nat.le_mul_of_pos_left _ hQ
  have hS1 : scosPasteM n c ≤ scosBigS n c := Nat.le_mul_of_pos_right _ hQ
  have hS2 : (n + n + 1) ^ 6 * (n + n + 1) ^ 6 ≤ scosBigS n c := Nat.mul_le_mul_right _ hM1
  refine ⟨by omega, hS2, hS1, by omega, by omega⟩

/-! ### The postcondition -/

/-- The postcondition of `scos_big_spec`, with own cost `X`. -/
def ScosBigPost (n c : ℕ) (T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ)
    (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n) (Φ : Finset (Fin n)) (X : ℕ) (w : Val)
    (cost : ℕ) : Prop :=
  ScosAns n w x 𝒢 Φ ∧ ∃ (K : Subgroup (ScosPair n)) (m s ℓ : ℕ), K ≤ 𝒢 ∧ 2 ≤ m ∧ 1 ≤ s ∧
    m * s ≤ Φ.card ∧ ℓ ≤ (m + 1) ^ c ∧ scosMo K Φ ≤ s ∧ cost ≤ X + ℓ * (scosOwnC n c + T K Φ)

section Post

variable {c : ℕ} {T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ} {𝒢 : Subgroup (ScosPair n)}
  {x : ScosPair n} {Φ : Finset (Fin n)}

theorem ScosBigPost.add {X Y : ℕ} {w : Val} {cb cost : ℕ} (h : ScosBigPost n c T 𝒢 x Φ X w cb)
    (hc : cost ≤ cb + Y) : ScosBigPost n c T 𝒢 x Φ (X + Y) w cost := by
  obtain ⟨hw, K, m, s, ℓ, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hw, K, m, s, ℓ, h1, h2, h3, h4, h5, h6, by omega⟩

theorem ScosBigPost.mono {X Y : ℕ} {w : Val} {cost : ℕ} (h : ScosBigPost n c T 𝒢 x Φ X w cost)
    (hXY : X ≤ Y) : ScosBigPost n c T 𝒢 x Φ Y w cost := by
  obtain ⟨hw, K, m, s, ℓ, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hw, K, m, s, ℓ, h1, h2, h3, h4, h5, h6, by omega⟩

/-- **One `let` of the chain**, whose bound value has the property `R` at cost at most `ca`. -/
theorem scosBig_letR {P : Program} {env : List Val} {e body : Expr} {R : Val → Prop} {ca X : ℕ}
    (ha : EvalAll P env e (fun v c' => R v ∧ c' ≤ ca))
    (hb : ∀ v, R v → EvalAll P (env ++ [v]) body (ScosBigPost n c T 𝒢 x Φ X)) :
    EvalAll P env (.letE e body)
      (ScosBigPost n c T 𝒢 x Φ (X + (ca + 700 * (n + n + 1) ^ 6 + 1))) :=
  EvalAll.letE ha fun v ca' h => (hb v h.1).mono fun w cb hw =>
    hw.add (by have := scosPaste_wt_ans hw.1; have := h.2; omega)

/-- **One deterministic `let` of the chain.** -/
theorem scosBig_let {P : Program} {env : List Val} {e body : Expr} {v : Val} {ca X : ℕ}
    (ha : Det P env e v ca) (hb : EvalAll P (env ++ [v]) body (ScosBigPost n c T 𝒢 x Φ X)) :
    EvalAll P env (.letE e body)
      (ScosBigPost n c T 𝒢 x Φ (X + (ca + 700 * (n + n + 1) ^ 6 + 1))) :=
  scosBig_letR (R := fun w => w = v) ha fun _ h => h ▸ hb

end Post

/-! ### Small facts -/

/-- **The power of `scosPowE`.** -/
theorem scosBig_powE {P : Program} {env : List Val} {e : Expr} {m ce : ℕ}
    (he : Det P env e (.nat m) ce) (hm : 1 ≤ m) :
    ∀ c, Det P env (scosPowE c e) (.nat (m ^ c)) (c * (ce + m ^ c + 3) + 4)
  | 0 => by simpa [scosPowE] using (Det.nat (P := P) (env := env) 1)
  | c + 1 => by
    have ih := scosBig_powE he hm c
    have h := Det.arith' (op := BinOp.mul) ih he (z := m ^ (c + 1)) (by
      simp [BinOp.eval, pow_succ])
    refine h.mono ?_
    have h1 : m ^ c ≤ m ^ (c + 1) := Nat.pow_le_pow_right hm (by omega)
    have h2 : c * (ce + m ^ c + 3) ≤ c * (ce + m ^ (c + 1) + 3) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (c + 1) * (ce + m ^ (c + 1) + 3) = c * (ce + m ^ (c + 1) + 3) +
      (ce + m ^ (c + 1) + 3) := by ring
    omega

theorem scosBig_genGroup (gs : List (Perm (Fin (n + n)))) : genGroup (1 :: gs) = gens gs := by
  have : {g | g ∈ (1 :: gs)} = insert 1 {g | g ∈ gs} := by ext g; simp
  rw [genGroup, this, Subgroup.closure_insert_one]; rfl

theorem scosBig_gens_one (gs : List (Perm (Fin (n + n)))) : gens (1 :: gs) = gens gs :=
  scosBig_genGroup gs

theorem scosBig_boundSize_mono (p : Prim) {B B' : ℕ} (h : B ≤ B') :
    p.boundSize B ≤ p.boundSize B' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem scosBMk_le (Φ : Finset (Fin n)) : scosBMk Φ ≤ n := by
  rw [scosBMk_eq]; simpa using Finset.card_le_univ Φ

/-- The number of generators is less than the weight of a group value. -/
theorem scosBig_length_lt {k : ℕ} (gs : List (Perm (Fin k))) :
    gs.length + 1 < (encGroup gs).wt := by
  have h1 := length_lt_wt_list ((1 :: gs).map encPerm)
  have h2 : (Val.list ((1 :: gs).map encPerm)).wt <
      (Val.list [.nat k, .list ((1 :: gs).map encPerm)]).wt := wt_le_wt_list (by simp)
  simp only [List.length_map, List.length_cons] at h1
  exact lt_of_lt_of_le (by omega) h2.le

/-! ### The class representatives of `labN` -/

section Lab

variable (Φ : Finset (Fin n)) (lab : Fin (scosBMk Φ) → ℕ)

/-- The key of the class program equals as `labN`. -/
theorem scosBig_key_iff (hlt : ∀ j, lab j < scosBMk Φ) (i j : Fin (n + n)) :
    Cls.keyOf (scosBMLab Φ lab) (indF (Equiv.refl _) (scosPhiF Φ)) i =
        Cls.keyOf (scosBMLab Φ lab) (indF (Equiv.refl _) (scosPhiF Φ)) j ↔
      scosBMLab Φ lab i = scosBMLab Φ lab j := by
  classical
  have hk := scosBMk_le Φ
  have hind : ∀ y : Fin (n + n), indF (Equiv.refl _) (scosPhiF Φ) y =
      if y ∈ scosPhiF Φ then 1 else 0 := fun y => rfl
  unfold Cls.keyOf
  rw [hind i, hind j]
  by_cases hi : i ∈ scosPhiF Φ <;> by_cases hj : j ∈ scosPhiF Φ <;>
    simp only [hi, hj, one_ne_zero, ↓reduceIte]
  · have h1 := scosBMLab_lt Φ lab hlt hi
    have h2 := scosBMLab_off Φ lab hj
    constructor <;> intro h <;> omega
  · have h1 := scosBMLab_lt Φ lab hlt hj
    have h2 := scosBMLab_off Φ lab hi
    constructor <;> intro h <;> omega
  · simp [scosBMLab_off Φ lab hi, scosBMLab_off Φ lab hj]

/-- **The representatives give the relation "same label".** -/
theorem scosBig_reprVal (hlt : ∀ j, lab j < scosBMk Φ) :
    ReprVal (n + n)
      (encFun (Cls.repOf (Cls.keyOf (scosBMLab Φ lab) (indF (Equiv.refl _) (scosPhiF Φ)))))
      (fun i j => scosBMLab Φ lab i = scosBMLab Φ lab j) := by
  refine ⟨fun i => ⟨Cls.repOf (Cls.keyOf (scosBMLab Φ lab) (indF (Equiv.refl _) (scosPhiF Φ))) i,
    Cls.repOf_lt _ i⟩, rfl, fun i j => ?_, fun i => ?_⟩
  · rw [Fin.mk.injEq, Cls.repOf_eq_iff, scosBig_key_iff Φ lab hlt]
  · exact Fin.ext (Cls.repOf_idem _ i)

theorem scosBig_getD_map (l : List ℕ) (j : ℕ) :
    (l.map Val.nat).getD j (.nat 0) = .nat (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

/-- **The labels `labN` as a `gather`.** -/
theorem scosBig_gather_eq :
    Val.list (((List.finRange (n + n)).map fun i : Fin (n + n) =>
        posOf (domNat (Equiv.refl _) (scosPhiF Φ)) i).map fun i =>
      (((List.finRange (scosBMk Φ)).map fun j => Val.nat (lab j)) ++
        [Val.nat (scosBMk Φ)]).getD i (.nat 0)) = encFun (scosBMLab Φ lab) := by
  have e : ((List.finRange (scosBMk Φ)).map fun j => Val.nat (lab j)) ++ [Val.nat (scosBMk Φ)] =
      ((List.finRange (scosBMk Φ)).map lab ++ [scosBMk Φ]).map Val.nat := by
    simp [List.map_map, Function.comp_def]
  rw [e]
  simp only [List.map_map, encFun]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, scosBig_getD_map]
  rfl

end Lab

end GI.Impl
