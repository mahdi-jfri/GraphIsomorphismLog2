module

public import Workspace.Impl.JohnProg
public import Workspace.Proved.JohnOrbital

@[expose] public section

/-!
# The pair generators and their orbits

`johnPgF` turns a generator `g` into the permutation `johnPairPerm g` of `Fin (n * n)`
(`john_pgF_spec`), and `mapFuns 4 7` does this for every generator (`john_mapPg_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

theorem john_encPerm_get (σ : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    ((List.finRange n).map fun j => Val.nat (σ j))[i]? = some (.nat (σ ⟨i, hi⟩)) := by
  simp [hi]

/-- The value of `johnPairPerm σ` at the index `q`. -/
theorem john_pairPerm_val (σ : Perm (Fin n)) (q : Fin (n * n)) :
    (johnPairPerm σ q : ℕ) = n * σ ⟨q / n, Nat.div_lt_of_lt_mul q.isLt⟩ +
      σ ⟨q % n, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt q.isLt))⟩ := by
  simp only [johnPairPerm, Equiv.permCongr_apply, Equiv.prodCongr_apply, Prod.map,
    finProdFinEquiv_apply_val]
  rw [Nat.add_comm]
  rfl

theorem john_wt_list2 {a b : Val} {A : ℕ} (ha : a.wt ≤ A) (hb : b.wt ≤ A) :
    (Val.list [a, b]).wt ≤ 4 * A + 6 := by
  have := wt_list2_le a b; omega

/-- **One entry of a pair generator.** -/
theorem john_pgE_spec (σ : Perm (Fin n)) {p : ℕ} (hp : p < n * n) :
    FunDet johnProgram 11 (.list [.list [encPerm σ, .nat n], .nat p])
      (.nat (n * σ ⟨p / n, Nat.div_lt_of_lt_mul hp⟩ +
        σ ⟨p % n, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hp))⟩))
      (2000 * (n + 1) ^ 2) := by
  have hn : 0 < n := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hp)
  have hd : p / n < n := Nat.div_lt_of_lt_mul hp
  have hm : p % n < n := Nat.mod_lt _ hn
  set a := Val.list [.list [encPerm σ, .nat n], .nat p] with ha
  have hc : Det johnProgram [a] (arg 0) (.list [encPerm σ, .nat n]) (2 * a.wt + 5) := Det.arg' rfl
  have hg : Det johnProgram [a] (.get (arg 0) (.nat 0)) (encPerm σ) _ :=
    Det.get' hc (Det.nat 0) (show [encPerm σ, Val.nat n][0]? = some (encPerm σ) from rfl)
  have hN : Det johnProgram [a] (.get (arg 0) (.nat 1)) (.nat n) _ :=
    Det.get' hc (Det.nat 1) (show [encPerm σ, Val.nat n][1]? = some (.nat n) from rfl)
  have hP : Det johnProgram [a] (arg 1) (.nat p) (2 * a.wt + 6) := Det.arg' rfl
  have h1 := Det.get' hg (Det.arith (op := .div) hP hN) (john_encPerm_get σ hd)
  have h2 := Det.get' hg (Det.arith (op := .mod) hP hN) (john_encPerm_get σ hm)
  have h3 := Det.arith (op := .add) (Det.arith (op := .mul) hN h1) h2
  refine FunDet.intro john_at_pgE.single (h3.mono ?_)
  -- The bound.
  have wσ := wt_encPerm_le σ
  have wa : a.wt ≤ 4 * (4 * (4 * (n + 1) ^ 2) + 6) + 6 + 4 * (n * n + 2) := by
    have e1 := wt_list2_le (encPerm σ) (.nat n)
    have e2 := wt_list2_le (.list [encPerm σ, .nat n]) (.nat p)
    have := wt_nat_le n; have := wt_nat_le p
    have : n ≤ (n + 1) ^ 2 := by nlinarith
    have : a.wt = (Val.list [.list [encPerm σ, .nat n], .nat p]).wt := rfl
    omega
  have wv : ∀ x, x ≤ n * n + n → (Val.nat x).wt ≤ n * n + n + 2 := fun x hx => by
    have := wt_nat_le x; omega
  have q1 := wv (BinOp.eval .div p n) (by simp only [BinOp.eval]; nlinarith)
  have q2 := wv (BinOp.eval .mod p n) (by simp only [BinOp.eval]; nlinarith)
  have hsn : (σ ⟨p / n, hd⟩ : ℕ) < n := (σ _).isLt
  have hsm : (σ ⟨p % n, hm⟩ : ℕ) < n := (σ _).isLt
  have q3 := wv (σ ⟨p / n, hd⟩) (by omega)
  have q4 := wv (σ ⟨p % n, hm⟩) (by omega)
  have hmul : n * (σ ⟨p / n, hd⟩ : ℕ) ≤ n * n := Nat.mul_le_mul_left _ hsn.le
  have q5 := wv (BinOp.eval .mul n (σ ⟨p / n, hd⟩)) (by simp only [BinOp.eval]; omega)
  have q6 := wv (BinOp.eval .add (BinOp.eval .mul n (σ ⟨p / n, hd⟩)) (σ ⟨p % n, hm⟩))
    (by simp only [BinOp.eval]; omega)
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le n
  have hY : n * n + n + 2 ≤ 2 * (n + 1) ^ 2 := by nlinarith
  have hY1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hlist : (Val.list [encPerm σ, Val.nat n]).wt ≤ a.wt :=
    (wt_le_wt_list (by simp)).le
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

theorem john_encPerm_inj {σ τ : Perm (Fin n)} (h : encPerm σ = encPerm τ) : σ = τ := by
  ext i
  have := congrArg (fun v => match v with | .list vs => vs[(i : ℕ)]? | .nat _ => none) h
  simp only [encPerm, john_encPerm_get σ i.isLt, john_encPerm_get τ i.isLt, Option.some.injEq,
    Val.nat.injEq] at this
  exact this

/-- The weight of the points `0, …, n * n - 1`. -/
theorem john_wt_R2 : (natList (List.range (n * n))).wt ≤ 4 * (n + 1) ^ 4 := by
  rw [← encFun_id]
  have h1 := wt_ids_le (n * n)
  have h2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    rw [show (n + 1) ^ 4 = ((n + 1) ^ 2) ^ 2 by ring]
    exact Nat.pow_le_pow_left (by nlinarith) 2
  omega

/-- **A pair generator.** -/
theorem john_pgF_spec (σ : Perm (Fin n)) :
    FunDet johnProgram 7 (.list [.list [.nat n, natList (List.range (n * n))], encPerm σ])
      (encPerm (johnPairPerm σ)) (1000000 * (n + 1) ^ 6) := by
  have hT := tabulate_spec (m := n * n) john_at_mapPgE (c := .list [encPerm σ, .nat n])
    (F := fun q => .nat (johnPairPerm σ q)) (B := 2000 * (n + 1) ^ 2) fun q => by
      have := john_pgE_spec σ q.isLt
      show FunDet _ _ _ (Val.nat (johnPairPerm σ q)) _
      rw [john_pairPerm_val σ q]
      exact this
  rw [encFun_id] at hT
  set a := Val.list [.list [.nat n, natList (List.range (n * n))], encPerm σ]
  have hc : Det johnProgram [a] (arg 0) (.list [.nat n, natList (List.range (n * n))])
      (2 * a.wt + 5) := Det.arg' rfl
  have hg : Det johnProgram [a] (arg 1) (encPerm σ) (2 * a.wt + 6) := Det.arg' rfl
  have hN := Det.get' hc (Det.nat 0)
    (show [Val.nat n, natList (List.range (n * n))][0]? = some (.nat n) from rfl)
  have hR := Det.get' hc (Det.nat 1)
    (show [Val.nat n, natList (List.range (n * n))][1]? = some (natList (List.range (n * n)))
      from rfl)
  have hcall := Det.call (Det.mk2 (Det.mk2 hg hN) hR) hT
  refine FunDet.intro john_at_pgF.single (hcall.mono ?_)
  -- The bound.
  have wσ := wt_encPerm_le σ
  have wτ := wt_encPerm_le (johnPairPerm σ)
  have wR := john_wt_R2 (n := n)
  have hout : Val.list ((List.finRange (n * n)).map fun q => Val.nat (johnPairPerm σ q)) =
      encPerm (johnPairPerm σ) := rfl
  rw [hout]
  have e1 := wt_list2_le (encPerm σ) (.nat n)
  have e2 := wt_list2_le (.list [encPerm σ, .nat n]) (natList (List.range (n * n)))
  have e3 := wt_list2_le (.nat n) (natList (List.range (n * n)))
  have e4 := wt_list2_le (.list [.nat n, natList (List.range (n * n))]) (encPerm σ)
  have ea : a.wt = (Val.list [.list [.nat n, natList (List.range (n * n))], encPerm σ]).wt := rfl
  have := wt_nat_le n; have := wt_nat_le 0; have := wt_nat_le 1
  have h2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    rw [show (n + 1) ^ 4 = ((n + 1) ^ 2) ^ 2 by ring]
    exact Nat.pow_le_pow_left (by nlinarith) 2
  have y12 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have y24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have y46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : n * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have p1 : n * n * (2000 * (n + 1) ^ 2) ≤ 2000 * (n + 1) ^ 4 := by
    calc n * n * (2000 * (n + 1) ^ 2) ≤ (n + 1) ^ 2 * (2000 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2000 * (n + 1) ^ 4 := by ring
  set W := (Val.list [.list [encPerm σ, .nat n], natList (List.range (n * n))]).wt
  have hW : W + (encPerm (johnPairPerm σ)).wt + 1 ≤ 200 * (n + 1) ^ 4 := by omega
  have p2 : (n * n + 1) * (W + (encPerm (johnPairPerm σ)).wt + 1) ≤ 200 * (n + 1) ^ 6 := by
    calc (n * n + 1) * (W + (encPerm (johnPairPerm σ)).wt + 1)
        ≤ (n + 1) ^ 2 * (200 * (n + 1) ^ 4) := Nat.mul_le_mul hm hW
      _ = 200 * (n + 1) ^ 6 := by ring
  have p3 : mapK * (n * n + 1) * (W + (encPerm (johnPairPerm σ)).wt + 1) ≤
      1000 * (200 * (n + 1) ^ 6) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ p2
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem john_sum_le {α : Type} {l : List α} {f : α → ℕ} {B : ℕ} (h : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  have := List.sum_le_card_nsmul (l.map f) B (by simpa using h)
  simpa using this

/-- The weight of a list whose entries weigh at most `B`. -/
theorem john_wt_list_le {vs : List Val} {B : ℕ} (h : ∀ v ∈ vs, v.wt ≤ B) :
    (Val.list vs).wt ≤ vs.length * (2 * B + 1) + 4 := by
  have h1 := wt_list_le vs
  have h2 := john_sum_le h
  rw [Nat.mul_add, Nat.mul_comm vs.length (2 * B)]
  have : vs.length * B * 2 = 2 * B * vs.length := by ring
  omega

variable {n : ℕ}

/-- **The pair generators.** On `[[n, R2], gens]`, the list of the pair generators. -/
theorem john_mapPg_spec (gs : List (Perm (Fin n))) :
    FunDet johnProgram 4 (.list [.list [.nat n, natList (List.range (n * n))],
        .list (gs.map encPerm)])
      (.list (gs.map fun g => encPerm (johnPairPerm g))) (100000000 * (n + gs.length + 1) ^ 8) := by
  have hM := map_spec john_at_mapPg (c := .list [.nat n, natList (List.range (n * n))])
    (xs := gs.map encPerm) (R := fun x w => ∃ σ, x = encPerm σ ∧ w = encPerm (johnPairPerm σ))
    (B := fun _ => 1000000 * (n + 1) ^ 6) (by
      intro x hx
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx
      exact FunAll.mono (john_pgF_spec σ) fun w c h => ⟨⟨σ, rfl, h.1⟩, h.2⟩)
  refine hM.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = gs.map fun g => encPerm (johnPairPerm g) :=
    forall₂_map_eq (fun a _ w hR => by
      obtain ⟨σ, hσ, rfl⟩ := hR
      rw [john_encPerm_inj hσ]) hws
  subst hws'
  refine ⟨rfl, ?_⟩
  -- The bound.
  set Y := n + gs.length + 1
  have hY : 1 ≤ Y := by omega
  have hn1 : n + 1 ≤ Y := by omega
  have ht : gs.length + 1 ≤ Y := by omega
  have y2 : (n + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hn1 2
  have y4 : (n + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hn1 4
  have y6 : (n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hn1 6
  have hsum : ((gs.map encPerm).map fun _ => 1000000 * (n + 1) ^ 6).sum ≤
      (gs.map encPerm).length * (1000000 * (n + 1) ^ 6) := john_sum_le fun _ _ => le_rfl
  rw [List.length_map] at hsum
  have wx : (Val.list (gs.map encPerm)).wt ≤ gs.length * (2 * (4 * (n + 1) ^ 2) + 1) + 4 := by
    have := john_wt_list_le (vs := gs.map encPerm) (B := 4 * (n + 1) ^ 2) (by
      intro v hv; obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv; exact wt_encPerm_le σ)
    simpa using this
  have ww : (Val.list (gs.map fun g => encPerm (johnPairPerm g))).wt ≤
      gs.length * (2 * (4 * (n * n + 1) ^ 2) + 1) + 4 := by
    have := john_wt_list_le (vs := gs.map fun g => encPerm (johnPairPerm g))
      (B := 4 * (n * n + 1) ^ 2) (by
        intro v hv; obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv; exact wt_encPerm_le _)
    simpa using this
  have h2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    rw [show (n + 1) ^ 4 = ((n + 1) ^ 2) ^ 2 by ring]
    exact Nat.pow_le_pow_left (by nlinarith) 2
  have wR := john_wt_R2 (n := n)
  have e1 := wt_list2_le (.nat n) (natList (List.range (n * n)))
  have e2 := wt_list2_le (.list [.nat n, natList (List.range (n * n))]) (.list (gs.map encPerm))
  have := wt_nat_le n
  -- Products.
  have q1 : gs.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ 9 * Y ^ 3 := by
    calc gs.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ Y * (9 * Y ^ 2) :=
          Nat.mul_le_mul (by omega) (by have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
      _ = 9 * Y ^ 3 := by ring
  have q2 : gs.length * (2 * (4 * (n * n + 1) ^ 2) + 1) ≤ 9 * Y ^ 5 := by
    calc gs.length * (2 * (4 * (n * n + 1) ^ 2) + 1) ≤ Y * (9 * Y ^ 4) :=
          Nat.mul_le_mul (by omega) (by have : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega); omega)
      _ = 9 * Y ^ 5 := by ring
  have q3 : gs.length * (1000000 * (n + 1) ^ 6) ≤ 1000000 * Y ^ 7 := by
    calc gs.length * (1000000 * (n + 1) ^ 6) ≤ Y * (1000000 * Y ^ 6) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ y6)
      _ = 1000000 * Y ^ 7 := by ring
  have z3 : Y ^ 3 ≤ Y ^ 7 := Nat.pow_le_pow_right hY (by omega)
  have z4 : Y ^ 4 ≤ Y ^ 7 := Nat.pow_le_pow_right hY (by omega)
  have z5 : Y ^ 5 ≤ Y ^ 7 := Nat.pow_le_pow_right hY (by omega)
  have z1 : 1 ≤ Y ^ 7 := Nat.one_le_pow _ _ hY
  have z0 : Y ≤ Y ^ 7 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ 7 := Nat.pow_le_pow_right hY (by omega)
  set A := (Val.list [.list [.nat n, natList (List.range (n * n))], .list (gs.map encPerm)]).wt
  set Wo := (Val.list (gs.map fun g => encPerm (johnPairPerm g))).wt
  have hA : A + Wo + 1 ≤ 100 * Y ^ 7 := by omega
  have q4 : mapK * ((gs.map encPerm).length + 1) * (A + Wo + 1) ≤ 1000 * (100 * Y ^ 8) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc ((gs.map encPerm).length + 1) * (A + Wo + 1) ≤ Y * (100 * Y ^ 7) :=
          Nat.mul_le_mul (by simp; omega) hA
      _ = 100 * Y ^ 8 := by ring
  have z78 : Y ^ 7 ≤ Y ^ 8 := Nat.pow_le_pow_right hY (by omega)
  omega

end GI.Impl
