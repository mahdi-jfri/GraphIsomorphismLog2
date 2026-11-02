import Workspace.Cited.AlgoTerminal

/-! Straight-line programs in the abelian-coordinate construction of Theorem A.20.
The homomorphism law justifies replacing generators of N by zero. This file proves
mathematical evaluation; a language implementation and its cost are separate. -/
namespace GI.Impl
open GI.Cited

/-- One instruction with references checked against earlier entries. -/
def linSlpStep {G : Type*} [Group G] (gs acc : List G) : SlpInstr → Option G
  | .gen i => gs[i]?
  | .inv j => acc[j]?.map (·⁻¹)
  | .mul j k => do
      let a ← acc[j]?
      let b ← acc[k]?
      pure (a * b)

/-- Evaluate a program in an arbitrary group. -/
def linSlpEntries {G : Type*} [Group G] (gs : List G) :
    List SlpInstr → List G → Option (List G)
  | [], acc => some acc
  | ins :: prog, acc => do
      let g ← linSlpStep gs acc ins
      linSlpEntries gs prog (acc ++ [g])

/-- Agreement with the permutation evaluator. -/
theorem linSlpEntries_perm {n : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (prog : List SlpInstr) (acc : List (Equiv.Perm (Fin n))) :
    linSlpEntries gs prog acc = slpEntries gs prog acc := by
  induction prog generalizing acc with
  | nil => rfl
  | cons ins prog ih =>
    have hstep : slpEntries gs (ins :: prog) acc =
        match linSlpStep gs acc ins with
        | none => none
        | some g => slpEntries gs prog (acc ++ [g]) := by
      cases ins <;> rfl
    rw [hstep]
    simp only [linSlpEntries]
    cases linSlpStep gs acc ins <;> simp [ih]

/-- Every instruction commutes with a group homomorphism. -/
theorem linSlpStep_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (gs acc : List G) (ins : SlpInstr) :
    linSlpStep (gs.map f) (acc.map f) ins = (linSlpStep gs acc ins).map f := by
  cases ins with
  | gen i => simp [linSlpStep]
  | inv j => simp [linSlpStep, Option.map_map, Function.comp_def]
  | mul j k =>
    simp only [linSlpStep, List.getElem?_map]
    cases hs0 : acc[j]? <;> cases hs1 : acc[k]? <;> simp [map_mul]

/-- All entries, including the last, commute with homomorphisms. -/
theorem linSlpEntries_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (gs : List G) (prog : List SlpInstr) (acc : List G) :
    linSlpEntries (gs.map f) prog (acc.map f) =
      (linSlpEntries gs prog acc).map (List.map f) := by
  induction prog generalizing acc with
  | nil => rfl
  | cons ins prog ih =>
    simp only [linSlpEntries, linSlpStep_map]
    cases hs : linSlpStep gs acc ins with
    | none => rfl
    | some g => simpa only [Option.map_some, Option.bind_some, List.map_append,
        List.map_cons, List.map_nil] using ih (acc ++ [g])

/-- The empty program denotes the identity, as in the cited task. -/
def linSlpValue {G : Type*} [Group G] (gs : List G) (prog : List SlpInstr) : Option G :=
  (linSlpEntries gs prog []).map (fun es => es.getLast?.getD 1)

/-- The represented element commutes with homomorphisms. -/
theorem linSlpValue_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (gs : List G) (prog : List SlpInstr) :
    linSlpValue (gs.map f) prog = (linSlpValue gs prog).map f := by
  unfold linSlpValue
  rw [show ([] : List H) = ([] : List G).map f from rfl, linSlpEntries_map]
  simp only [Option.map_map]
  congr 1
  funext es
  cases es using List.reverseRecOn with
  | nil => simp
  | append_singleton es g => simp

/-- A cited membership witness still reaches the image under a homomorphism. -/
theorem linSlpReaches_map {n : ℕ} {H : Type*} [Group H]
    (f : Equiv.Perm (Fin n) →* H) {gs : List (Equiv.Perm (Fin n))}
    {prog : List SlpInstr} {x : Equiv.Perm (Fin n)} (h : SlpReaches gs prog x) :
    linSlpValue (gs.map f) prog = some (f x) := by
  obtain ⟨es, he, hx⟩ := h
  rw [linSlpValue_map]
  simp only [linSlpValue, linSlpEntries_perm, he, Option.map_some, hx]

/-- Every index in an instruction is below B. -/
def linSlpRefs (B : ℕ) : SlpInstr → Prop
  | .gen i => i < B
  | .inv j => j < B
  | .mul j k => j < B ∧ k < B

theorem linSlpRefs_mono {B C : ℕ} (h : B ≤ C) {ins : SlpInstr}
    (hi : linSlpRefs B ins) : linSlpRefs C ins := by
  cases ins <;> simp_all [linSlpRefs] <;> omega

private theorem linGetIndex {G : Type*} {xs : List G} {i : ℕ} {x : G}
    (h : xs[i]? = some x) : i < xs.length := by
  by_contra hi
  rw [List.getElem?_eq_none (by omega)] at h
  contradiction

/-- Successful instructions only use existing indices. -/
theorem linSlpStep_refs {G : Type*} [Group G] {gs acc : List G} {ins : SlpInstr} {x : G}
    (h : linSlpStep gs acc ins = some x) :
    linSlpRefs (gs.length + acc.length + 1) ins := by
  cases ins with
  | gen i =>
    have := linGetIndex h
    simp only [linSlpRefs]; omega
  | inv j =>
    simp only [linSlpStep, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, _⟩ := h
    have := linGetIndex ha
    simp only [linSlpRefs]; omega
  | mul j k =>
    cases ha : acc[j]? with
    | none => simp [linSlpStep, ha] at h
    | some a =>
      cases hb : acc[k]? with
      | none => simp [linSlpStep, hb] at h
      | some b =>
        have := linGetIndex ha
        have := linGetIndex hb
        simp only [linSlpRefs]; omega

/-- Valid programs have the expected number of entries and bounded instruction indices. -/
theorem linSlpEntries_refs {G : Type*} [Group G] {gs : List G} (prog : List SlpInstr)
    (acc es : List G) (h : linSlpEntries gs prog acc = some es) :
    es.length = acc.length + prog.length ∧
      ∀ ins ∈ prog, linSlpRefs (gs.length + acc.length + prog.length + 1) ins := by
  induction prog generalizing acc with
  | nil =>
    simp only [linSlpEntries, Option.some.injEq] at h
    subst es
    simp
  | cons ins prog ih =>
    obtain ⟨x, hx⟩ : ∃ x, linSlpStep gs acc ins = some x := by
      cases hx : linSlpStep gs acc ins with
      | none => simp [linSlpEntries, hx] at h
      | some x => exact ⟨x, rfl⟩
    have he : linSlpEntries gs prog (acc ++ [x]) = some es := by
      simpa only [linSlpEntries, hx, Option.bind_some] using h
    obtain ⟨hl, hr⟩ := ih (acc ++ [x]) he
    constructor
    · simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact linSlpRefs_mono (by simp only [List.length_cons]; omega) (linSlpStep_refs hx)
      · have := hr i hi
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- Regard the generators as elements of a subgroup containing them. -/
def linSubgroupGenerators {G : Type*} [Group G] (A : Subgroup G) (gs : List G)
    (hg : ∀ g ∈ gs, g ∈ A) : List A :=
  gs.attach.map fun g => ⟨g.val, hg g.val g.property⟩

/-- Forgetting subgroup membership recovers the original generating list. -/
theorem linSubgroupGenerators_map {G : Type*} [Group G] (A : Subgroup G) (gs : List G)
    (hg : ∀ g ∈ gs, g ∈ A) : (linSubgroupGenerators A gs hg).map A.subtype = gs := by
  simp [linSubgroupGenerators, List.map_map, Function.comp_def]

/-- A permutation SLP can be evaluated inside A before applying A → A/N.
This avoids requiring a homomorphism from the whole ambient symmetric group. -/
theorem linSlpReaches_subgroup {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (gs : List (Equiv.Perm (Fin n))) (hg : ∀ g ∈ gs, g ∈ A)
    (prog : List SlpInstr) (x : Equiv.Perm (Fin n)) (hx : SlpReaches gs prog x) :
    ∃ y : A, y.val = x ∧ linSlpValue (linSubgroupGenerators A gs hg) prog = some y := by
  have ht : linSlpValue gs prog = some x := by
    obtain ⟨es, he, hx⟩ := hx
    simp only [linSlpValue, linSlpEntries_perm, he, Option.map_some, hx]
  rw [← linSubgroupGenerators_map A gs hg, linSlpValue_map] at ht
  obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.mp ht
  exact ⟨y, hyx, hy⟩

end GI.Impl
