module

public import Workspace.Impl.TermGlueLabNTest
public import Workspace.Impl.TermGlueLabPXLab

@[expose] public section

/-!
# The label driver: the test "all types are distinct"

Proof of Theorem A.23, step 5. The paper adds the orientation coordinate exactly
when all types of `x` are distinct. The labels of `x` (`tmGLPXLab_spec`) are pairs
`[J_k, a_k]`, where `J_k` is the first row of the type of row `k`. By `tmGLN_nodup_iff`, all
types are distinct exactly when `J_k = k` for every `k`. The program `tmGLNDistFuns` checks
this with one loop over the labels: it keeps a flag that stays `1` while every label so far has
`J_k = k`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm)

/-- The first number of a list value (`0` for anything else). -/
def tmGLNFst : Val → ℕ
  | .list (.nat n :: _) => n
  | _ => 0

/-- One step, on `[xl, i, flag]`: keep the flag only if entry `i` starts with `i`. -/
def tmGLNDistStep : Expr :=
  .ite (arg 2) (.arith .eq (.get (.get (arg 0) (arg 1)) (.nat 0)) (arg 1)) (.nat 0)

/-- **The test** (3 functions): on `xl`, `1` if every entry `k` starts with `k`, else `0`. -/
def tmGLNDistFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (.var 0)) (.nat 1) tmGLNDistStep

theorem length_tmGLNDistFuns (b : ℕ) : (tmGLNDistFuns b).length = 3 := rfl

/-- The flag after the entries `j < i`. -/
abbrev tmGLNDInv (xl : List Val) (i : ℕ) (acc : Val) : Prop :=
  acc = boolVal (decide (∀ j (hj : j < xl.length), j < i → tmGLNFst xl[j] = j))

private theorem tmGLN_dist_succ (xl : List Val) (i : ℕ) (hi : i < xl.length) :
    (∀ j (hj : j < xl.length), j < i + 1 → tmGLNFst xl[j] = j) ↔
      (∀ j (hj : j < xl.length), j < i → tmGLNFst xl[j] = j) ∧ tmGLNFst xl[i] = i := by
  constructor
  · intro h
    exact ⟨fun j hj hji => h j hj (by omega), h i hi (by omega)⟩
  · rintro ⟨h, hi'⟩ j hj hji
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hlt | rfl
    · exact h j hj hlt
    · exact hi'

private theorem tmGLN_dist_ar {A I K : ℕ} (hI : I < K) :
    2 * (2 * (A + I + 3) + 11) + 2 + 5 + (2 * (2 * (A + I + 3) + 11) + 1 + 5) + A + 1 + 3 + A +
      1 + (2 * (2 * (A + I + 3) + 11) + 1 + 5) + 1 + 3 + 3 + (2 * (2 * (A + I + 3) + 11) + 2 + 5)
      + 3 + 1 ≤ 0 + 100 * (A + K + 3 + 1) := by
  omega

/-- **The test.** If every entry of `xl` is a list that starts with a number, the program returns
`1` when entry `k` starts with `k` for every `k`, and `0` otherwise. -/
theorem tmGLNDist_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLNDistFuns b)) (xl : List Val)
    (hx : ∀ v ∈ xl, ∃ (n : ℕ) (r : List Val), v = .list (.nat n :: r)) :
    FunDet P b (.list xl) (boolVal (decide (∀ j (hj : j < xl.length), tmGLNFst xl[j] = j)))
      (loopModK * (xl.length + 1) * ((Val.list xl).wt + xl.length + 4)) := by
  set a : Val := .list xl with ha
  have hk : Det P [a] (.length (.var 0)) (.nat xl.length) (a.wt + 1 + xl.length + 3) :=
    Det.length (Det.var' rfl)
  have hlen := length_lt_wt_list xl
  refine (loopBdd_spec h hk (Det.nat 1) ?_ (M := 3) (Inv := tmGLNDInv xl) (D := fun _ => 0)
    ?_ (fun i acc _ h => h ▸ wt_boolVal_le _) ?_).mono ?_
  · omega
  · simp [tmGLNDInv]
  · rintro i acc hi rfl
    set t := decide (∀ j (hj : j < xl.length), j < i → tmGLNFst xl[j] = j) with ht
    have hW := wt_stepArg_le a i (boolVal t)
    have hbt := wt_boolVal_le t
    have hW' : (Val.list [a, .nat i, boolVal t]).wt ≤ 2 * (a.wt + i + 3) + 11 := by omega
    obtain ⟨n, r, hv⟩ := hx xl[i] (List.getElem_mem hi)
    have hxi : xl[i].wt < a.wt := wt_le_wt_list (List.getElem_mem hi)
    have hni : (Val.nat n).wt < xl[i].wt := by rw [hv]; exact wt_le_wt_list (by simp)
    have hfst : tmGLNFst xl[i] = n := by rw [hv]; rfl
    set t' := decide (∀ j (hj : j < xl.length), j < i + 1 → tmGLNFst xl[j] = j) with ht'
    have hbt' := wt_boolVal_le t'
    have d2 : Det P [.list [a, .nat i, boolVal t]] (arg 2) (.nat t.toNat)
        (2 * (Val.list [a, .nat i, boolVal t]).wt + 2 + 5) := Det.arg' rfl
    have d1 : Det P [.list [a, .nat i, boolVal t]] (arg 1) (.nat i)
        (2 * (Val.list [a, .nat i, boolVal t]).wt + 1 + 5) := Det.arg' rfl
    have d0 : Det P [.list [a, .nat i, boolVal t]] (arg 0) (.list xl)
        (2 * (Val.list [a, .nat i, boolVal t]).wt + 0 + 5) := Det.arg' rfl
    have dg := Det.get' d0 d1 (show xl[i]? = some xl[i] from List.getElem?_eq_getElem hi)
    rw [hv] at dg
    have dg2 := Det.get' dg (Det.nat 0) (v := .nat n) (x := 0) rfl
    have deq := Det.arith' (op := .eq) dg2 d1 (z := (decide (n = i)).toNat)
      (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp_all)
    rw [← hv] at deq
    refine (Det.ite d2 (v := boolVal t')
      (ct := 2 * (Val.list [a, .nat i, boolVal t]).wt + 0 + 5 +
        (2 * (Val.list [a, .nat i, boolVal t]).wt + 1 + 5) + xl[i].wt + 1 + (0 + 3) +
        (Val.nat n).wt + 1 + (2 * (Val.list [a, .nat i, boolVal t]).wt + 1 + 5) +
        (decide (n = i)).toNat + 3) (ce := 3)
      (fun hx0 => ?_) (fun hx0 => ?_)).post fun cost hc => ⟨rfl, ?_⟩
    · have htt : t = true := by
        cases htv : t
        · rw [htv] at hx0; exact absurd rfl hx0
        · rfl
      have hall : ∀ j (hj : j < xl.length), j < i → tmGLNFst xl[j] = j := of_decide_eq_true htt
      have e : t' = decide (n = i) := by
        rw [ht']
        refine decide_eq_decide.mpr ?_
        rw [tmGLN_dist_succ xl i hi, hfst]
        exact ⟨fun h => h.2, fun h => ⟨hall, h⟩⟩
      rw [e]; exact deq
    · have htf : t = false := by
        cases htv : t
        · rfl
        · rw [htv] at hx0; exact absurd hx0 (by decide)
      have hn : ¬ ∀ j (hj : j < xl.length), j < i → tmGLNFst xl[j] = j := of_decide_eq_false htf
      have e : t' = false := by
        rw [ht']
        refine decide_eq_false fun h' => hn ?_
        exact ((tmGLN_dist_succ xl i hi).mp h').1
      rw [e]; exact Det.nat 0
    · have hct : (decide (n = i)).toNat ≤ 1 := Bool.toNat_le _
      have hn2 := wt_nat_le t.toNat
      have hmax : max (2 * (Val.list [a, .nat i, boolVal t]).wt + 0 + 5 +
          (2 * (Val.list [a, .nat i, boolVal t]).wt + 1 + 5) + xl[i].wt + 1 + (0 + 3) +
          (Val.nat n).wt + 1 + (2 * (Val.list [a, .nat i, boolVal t]).wt + 1 + 5) +
          (decide (n = i)).toNat + 3) 3 ≤
          (2 * (2 * (a.wt + i + 3) + 11) + 1 + 5) + (2 * (2 * (a.wt + i + 3) + 11) + 1 + 5) +
          a.wt + 1 + 3 + a.wt + 1 + (2 * (2 * (a.wt + i + 3) + 11) + 1 + 5) + 1 + 3 := by
        refine max_le ?_ (by omega)
        omega
      have := tmGLN_dist_ar (A := a.wt) (I := i) (K := xl.length) hi
      omega
  · rintro w c ⟨hw, hc⟩
    have e : (∀ j (hj : j < xl.length), j < xl.length → tmGLNFst xl[j] = j) ↔
        (∀ j (hj : j < xl.length), tmGLNFst xl[j] = j) :=
      ⟨fun h j hj => h j hj hj, fun h j hj _ => h j hj⟩
    refine ⟨hw.trans ?_, ?_⟩
    · rw [decide_eq_decide.mpr e]
    · simpa using hc

/-! ### The test on the labels of `x` -/

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- **The test decides whether all types are distinct.** On the labels of `x` (`TmGLPXOut`),
the flag is `1` exactly when the types of `x` are distinct (`tmGLN_nodup_iff`). -/
theorem tmGLNDist_types {P : Program} {b : ℕ} (h : P.HasAt b (tmGLNDistFuns b))
    {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {xl : List Val}
    (hxl : TmGLPXOut N X (.list xl)) :
    FunDet P b (.list xl) (boolVal (decide (types N X).Nodup))
      (loopModK * (xl.length + 1) * ((Val.list xl).wt + xl.length + 4)) := by
  obtain ⟨l, hl, hlen, hk⟩ := hxl
  obtain rfl : xl = l := by injection hl
  -- the entries of the labels, and their first rows
  have hent : ∀ k : Fin q, ∃ J : Fin q, ∃ x : Perm (Fin n), xl[k.1]? =
      some (.list [.nat J, encPerm x]) ∧ TmGLPFirst N X (X k) J := by
    intro k
    obtain ⟨v, hv, J, x, -, rfl, hJ, -⟩ := hk k
    exact ⟨J, x, hv, hJ⟩
  have hx : ∀ v ∈ xl, ∃ (n : ℕ) (r : List Val), v = .list (.nat n :: r) := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    obtain ⟨_, _, hJv', -⟩ := hent ⟨i, hlen ▸ hi⟩
    rw [List.getElem?_eq_getElem hi] at hJv'
    exact ⟨_, _, Option.some.inj hJv'⟩
  choose J x hJv hJ using hent
  have hfst : ∀ k : Fin q, ∀ hk : k.1 < xl.length, tmGLNFst xl[k.1] = (J k).1 := by
    intro k hk
    have := hJv k
    rw [List.getElem?_eq_getElem hk] at this
    rw [Option.some.inj this]; rfl
  have heq : (∀ j (hj : j < xl.length), tmGLNFst xl[j] = j) ↔ (types N X).Nodup := by
    rw [tmGLN_nodup_iff hJ]
    constructor
    · intro h k
      exact Fin.ext ((hfst k (hlen ▸ k.2)).symm.trans (h k.1 (hlen ▸ k.2)))
    · intro h j hj
      have := hfst ⟨j, hlen ▸ hj⟩ hj
      rw [this, h]
  have := tmGLNDist_spec h xl hx
  rwa [decide_eq_decide.mpr heq] at this

end GI.Impl
