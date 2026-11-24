/-
Checks of the bit encodings in `Workspace.Statement.Turing`.

We prove that the input and output encodings determine the objects they encode:
* `natBits` is prefix-free and therefore injective.
* `mapBits` is prefix-free and injective on maps `Fin n → Fin n` for a fixed `n`.
* `answerBits` is prefix-free and injective on `Answer G H` for fixed graphs `G` and `H`.
* `adjBits` is injective, `inputBits` determines both graphs on a fixed `Fin n`, and graphs on
  different sizes `Fin n` and `Fin m` have inputs of different lengths.
-/
module

public import Workspace.Turing.Wrap.Bits

@[expose] public section

namespace GI.Turing

open GI.Statement

/-! ### Prefix-freeness and injectivity of `natBits` -/

private theorem encodeDigits_prefix_free :
    ∀ {l₁ l₂ : List ℕ} {s t : List Bool},
      (∀ d ∈ l₁, d < 2) → (∀ d ∈ l₂, d < 2) →
      l₁.flatMap (fun d => [true, decide (d = 1)]) ++ (false :: s) =
        l₂.flatMap (fun d => [true, decide (d = 1)]) ++ (false :: t) →
      l₁ = l₂ ∧ s = t
  | [], [], _, _, _, _, h => by
      simp only [List.flatMap_nil, List.nil_append] at h
      exact ⟨rfl, (List.cons.inj h).2⟩
  | [], _ :: _, _, _, _, _, h => by
      simp only [List.flatMap_nil, List.flatMap_cons, List.nil_append, List.cons_append] at h
      cases h
  | _ :: _, [], _, _, _, _, h => by
      simp only [List.flatMap_nil, List.flatMap_cons, List.nil_append, List.cons_append] at h
      cases h
  | d₁ :: l₁, d₂ :: l₂, _, _, hl₁, hl₂, h => by
      simp only [List.flatMap_cons, List.cons_append, List.nil_append] at h
      have h1 := (List.cons.inj h).2
      have hdec : decide (d₁ = 1) = decide (d₂ = 1) := (List.cons.inj h1).1
      have htail := (List.cons.inj h1).2
      have hd₁ : d₁ < 2 := hl₁ d₁ (List.mem_cons_self)
      have hd₂ : d₂ < 2 := hl₂ d₂ (List.mem_cons_self)
      have hd : d₁ = d₂ := by
        by_cases h1eq : d₁ = 1
        · have h2eq : decide (d₂ = 1) = true := by rw [← hdec]; simp [h1eq]
          have := of_decide_eq_true h2eq
          omega
        · have h2eq : decide (d₂ = 1) = false := by rw [← hdec]; simp [h1eq]
          have := of_decide_eq_false h2eq
          omega
      obtain ⟨hl, hst⟩ := encodeDigits_prefix_free
        (fun d hd => hl₁ d (List.mem_cons_of_mem _ hd))
        (fun d hd => hl₂ d (List.mem_cons_of_mem _ hd))
        htail
      exact ⟨congrArg₂ List.cons hd hl, hst⟩

/-- `natBits` is prefix-free: if `natBits a ++ s = natBits b ++ t`, then `a = b` and `s = t`. -/
theorem natBits_prefix_free {a b : ℕ} {s t : List Bool}
    (h : natBits a ++ s = natBits b ++ t) : a = b ∧ s = t := by
  unfold natBits at h
  simp only [List.append_assoc, List.singleton_append] at h
  obtain ⟨hdig, hst⟩ := encodeDigits_prefix_free
    (fun d hd => Nat.digits_lt_base (by norm_num) hd)
    (fun d hd => Nat.digits_lt_base (by norm_num) hd)
    h
  have hab : a = b := by
    rw [← Nat.ofDigits_digits 2 a, ← Nat.ofDigits_digits 2 b, hdig]
  exact ⟨hab, hst⟩

/-- `natBits` is injective. -/
theorem natBits_injective : Function.Injective natBits := by
  intro a b h
  have h' : natBits a ++ [] = natBits b ++ [] := by simpa using h
  exact (natBits_prefix_free h').1

/-! ### Prefix-freeness and injectivity of `mapBits` -/

private theorem flatMap_natBits_prefix_free {α : Type*} :
    ∀ (l : List α) {f g : α → ℕ} {s t : List Bool},
      (l.flatMap fun i => natBits (f i)) ++ s = (l.flatMap fun i => natBits (g i)) ++ t →
      (∀ i ∈ l, f i = g i) ∧ s = t
  | [], _, _, _, _, h => by
      simp only [List.flatMap_nil, List.nil_append] at h
      exact ⟨fun _ hi => by simp at hi, h⟩
  | a :: l, f, g, _, _, h => by
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨ha, htail⟩ := natBits_prefix_free h
      obtain ⟨hl, hst⟩ := flatMap_natBits_prefix_free l htail
      refine ⟨fun i hi => ?_, hst⟩
      rcases List.mem_cons.mp hi with rfl | hi'
      · exact ha
      · exact hl i hi'

/-- `mapBits` is prefix-free on maps `Fin n → Fin n` for a fixed `n`. -/
theorem mapBits_prefix_free {n : ℕ} {f g : Fin n → Fin n} {s t : List Bool}
    (h : mapBits f ++ s = mapBits g ++ t) : f = g ∧ s = t := by
  obtain ⟨hval, hst⟩ := flatMap_natBits_prefix_free (List.finRange n) h
  exact ⟨funext fun i => Fin.ext (hval i (List.mem_finRange i)), hst⟩

/-- `mapBits` is injective on maps `Fin n → Fin n` for a fixed `n`. -/
theorem mapBits_injective (n : ℕ) : Function.Injective (mapBits (n := n)) := by
  intro f g h
  have h' : mapBits f ++ [] = mapBits g ++ [] := by simpa using h
  exact (mapBits_prefix_free h').1

/-! ### Prefix-freeness and injectivity of `answerBits` -/

private theorem gensBits_prefix_free {n : ℕ} :
    ∀ {gens₁ gens₂ : List (Equiv.Perm (Fin n))} {s t : List Bool},
      (gens₁.flatMap fun g => true :: mapBits (fun i => g i)) ++ (false :: s) =
        (gens₂.flatMap fun g => true :: mapBits (fun i => g i)) ++ (false :: t) →
      gens₁ = gens₂ ∧ s = t
  | [], [], _, _, h => by
      simp only [List.flatMap_nil, List.nil_append] at h
      exact ⟨rfl, (List.cons.inj h).2⟩
  | [], _ :: _, _, _, h => by
      simp only [List.flatMap_nil, List.flatMap_cons, List.nil_append, List.cons_append] at h
      cases h
  | _ :: _, [], _, _, h => by
      simp only [List.flatMap_nil, List.flatMap_cons, List.nil_append, List.cons_append] at h
      cases h
  | g₁ :: gens₁, g₂ :: gens₂, _, _, h => by
      simp only [List.flatMap_cons, List.cons_append, List.append_assoc] at h
      have h1 := (List.cons.inj h).2
      obtain ⟨hf, htail⟩ := mapBits_prefix_free h1
      have hg : g₁ = g₂ := Equiv.ext fun i => congrFun hf i
      obtain ⟨hgens, hst⟩ := gensBits_prefix_free htail
      exact ⟨congrArg₂ List.cons hg hgens, hst⟩

/-- `answerBits` is prefix-free for fixed graphs `G` and `H`. -/
theorem answerBits_prefix_free {n : ℕ} {G H : SimpleGraph (Fin n)} {a b : Answer G H}
    {s t : List Bool} (h : answerBits a ++ s = answerBits b ++ t) : a = b ∧ s = t := by
  cases a with
  | none =>
    cases b with
    | none =>
      simp only [answerBits, List.cons_append, List.nil_append] at h
      exact ⟨rfl, (List.cons.inj h).2⟩
    | some p =>
      rcases p with ⟨σ, gens⟩
      simp only [answerBits, List.cons_append, List.nil_append] at h
      cases h
  | some p₁ =>
    rcases p₁ with ⟨σ₁, gens₁⟩
    cases b with
    | none =>
      simp only [answerBits, List.cons_append, List.nil_append] at h
      cases h
    | some p₂ =>
      rcases p₂ with ⟨σ₂, gens₂⟩
      simp only [answerBits, List.cons_append, List.nil_append, List.append_assoc] at h
      have h1 := (List.cons.inj h).2
      obtain ⟨hσf, htail⟩ := mapBits_prefix_free h1
      have hσ : σ₁ = σ₂ := RelIso.ext fun i => congrFun hσf i
      obtain ⟨hgens, hst⟩ := gensBits_prefix_free htail
      subst hσ hgens
      exact ⟨rfl, hst⟩

/-- `answerBits` is injective for fixed graphs `G` and `H`. -/
theorem answerBits_injective {n : ℕ} {G H : SimpleGraph (Fin n)} :
    Function.Injective (answerBits (G := G) (H := H)) := by
  intro a b h
  have h' : answerBits a ++ [] = answerBits b ++ [] := by simpa using h
  exact (answerBits_prefix_free h').1

/-! ### Injectivity of `adjBits` and `inputBits` -/

open Classical in
/-- `adjBits` is injective on graphs on `Fin n`. -/
theorem adjBits_injective (n : ℕ) : Function.Injective (adjBits (n := n)) := by
  intro G G' h
  ext i j
  have hij := congrArg (fun l => l[n * (i : ℕ) + j]?) h
  rw [adjBits_getElem? G i j, adjBits_getElem? G' i j] at hij
  have hdec : decide (G.Adj i j) = decide (G'.Adj i j) := Option.some.inj hij
  by_cases hG : G.Adj i j
  · have hG' : decide (G'.Adj i j) = true := by rw [← hdec]; simp [hG]
    exact ⟨fun _ => of_decide_eq_true hG', fun _ => hG⟩
  · have hG' : decide (G'.Adj i j) = false := by rw [← hdec]; simp [hG]
    exact ⟨fun h1 => absurd h1 hG, fun h2 => absurd h2 (of_decide_eq_false hG')⟩

/-- `inputBits` determines both graphs on a fixed `Fin n`. -/
theorem inputBits_injective {n : ℕ} {G H G' H' : SimpleGraph (Fin n)}
    (h : inputBits G H = inputBits G' H') : G = G' ∧ H = H' := by
  unfold inputBits at h
  have hlen : (adjBits G).length = (adjBits G').length := by
    rw [adjBits_length, adjBits_length]
  obtain ⟨hG, hH⟩ := List.append_inj h hlen
  exact ⟨adjBits_injective n hG, adjBits_injective n hH⟩

/-- Graphs on `Fin n` and `Fin m` with `n ≠ m` have input bit strings of different lengths. -/
theorem inputBits_length_ne_of_ne {n m : ℕ} (G H : SimpleGraph (Fin n))
    (G' H' : SimpleGraph (Fin m)) (hnm : n ≠ m) :
    (inputBits G H).length ≠ (inputBits G' H').length := by
  rw [inputBits_length, inputBits_length]
  intro heq
  have hsq : n * n = m * m := by
    rw [Nat.mul_assoc, Nat.mul_assoc] at heq
    exact Nat.eq_of_mul_eq_mul_left (by omega) heq
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · have h1 : n * n ≤ n * m := Nat.mul_le_mul_left n hlt.le
    have h2 : n * m < m * m := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega
  · have h1 : m * m ≤ m * n := Nat.mul_le_mul_left m hlt.le
    have h2 : m * n < n * n := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega

/-- Graphs on `Fin n` and `Fin m` with `n ≠ m` have different input bit strings. -/
theorem inputBits_ne_of_ne {n m : ℕ} (G H : SimpleGraph (Fin n))
    (G' H' : SimpleGraph (Fin m)) (hnm : n ≠ m) :
    inputBits G H ≠ inputBits G' H' := fun h =>
  inputBits_length_ne_of_ne G H G' H' hnm (congrArg List.length h)

end GI.Turing
