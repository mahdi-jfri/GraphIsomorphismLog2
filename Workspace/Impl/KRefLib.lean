module

public import Workspace.Lang.Lib.NatList
public import Workspace.Lang.Lib.Tabulate

@[expose] public section

/-!
# Deterministic library combinators with one-parameter cost bounds

The `k`-ary refinement program is built from the library loops `map`, `foldl` and `iterate`
(`Workspace/Lang/Lib/`). This file restates them for deterministic bodies, with every cost
bound of the form `K * (Y + 1) ^ d` for one parameter `Y` that bounds the weights of all values
involved. Then the bound of a composed function is again of this form.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

theorem kref_forall₂_eq {xs ws : List Val} {F : Val → Val}
    (h : List.Forall₂ (fun x w => w = F x) xs ws) : ws = xs.map F := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem kref_sum_wt_le {xs : List Val} {F : Val → Val} {C : ℕ} (h : ∀ x ∈ xs, (F x).wt ≤ C) :
    ((xs.map F).map Val.wt).sum ≤ xs.length * C := by
  have := List.sum_le_card_nsmul ((xs.map F).map Val.wt) C (by
    simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact h)
  simpa using this

/-- The weight of `xs.map F` when every `F x` weighs at most `C`. -/
theorem kref_wt_map_le {xs : List Val} {F : Val → Val} {C : ℕ} (h : ∀ x ∈ xs, (F x).wt ≤ C) :
    (Val.list (xs.map F)).wt ≤ 2 * (xs.length * C) + xs.length + 4 := by
  have h1 := wt_list_le (xs.map F)
  have h2 := kref_sum_wt_le h
  simp only [List.length_map] at h1
  omega

/-- **Map with a deterministic body.** -/
theorem kref_map {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {xs : List Val} {F : Val → Val} {Y K d : ℕ}
    (hf : ∀ x ∈ xs, FunDet P f (.list [c, x]) (F x) (K * (Y + 1) ^ d))
    (hc : c.wt ≤ Y) (hxs : (Val.list xs).wt ≤ Y) :
    FunDet P b (.list [c, .list xs]) (.list (xs.map F)) (mapK * (3 * K + 11) * (Y + 1) ^ (d + 2)) := by
  refine (map_spec h (R := fun x w => w = F x) (B := fun _ => K * (Y + 1) ^ d)
    fun x hx => FunAll.mono (hf x hx) fun w c h => ⟨h.1, h.2⟩).mono ?_
  rintro w cost ⟨ws, rfl, hws, hcost⟩
  rw [kref_forall₂_eq hws] at hcost ⊢
  refine ⟨rfl, ?_⟩
  obtain ⟨T, hT⟩ : ∃ T, T = (Y + 1) ^ d := ⟨_, rfl⟩
  rw [← hT] at hcost
  have hT1 : 1 ≤ T := hT ▸ Nat.one_le_pow _ _ (by omega)
  have hL := length_lt_wt_list xs
  have hw := kref_wt_map_le (xs := xs) (F := F) (C := K * T) fun x hx => by
    have := FunDet.wt_lt (hf x hx); rw [← hT] at this; omega
  have ha := wt_list2_le c (.list xs)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hcost
  obtain ⟨S, hS⟩ : ∃ S, S = Y + 1 := ⟨_, rfl⟩
  have e1 : (Y + 1) ^ (d + 2) = S * S * T := by rw [pow_add, hT, hS]; ring
  rw [e1]
  set L := xs.length
  have k1 : L * (K * T) ≤ S * (K * T) := Nat.mul_le_mul_right _ (by omega)
  have k2 : S ≤ S * T := Nat.le_mul_of_pos_right _ hT1
  have k3 : S * (K * T) ≤ S * S * T * K := by
    have : S * (K * T) * 1 ≤ S * (K * T) * S := Nat.mul_le_mul_left _ (by omega)
    calc S * (K * T) = S * (K * T) * 1 := by ring
      _ ≤ S * (K * T) * S := this
      _ = S * S * T * K := by ring
  have k4 : (Val.list [c, .list xs]).wt + (Val.list (xs.map F)).wt + 1 ≤
      2 * (S * (K * T)) + 11 * (S * T) := by omega
  have k5 : (L + 1) * ((Val.list [c, .list xs]).wt + (Val.list (xs.map F)).wt + 1) ≤
      S * (2 * (S * (K * T)) + 11 * (S * T)) := Nat.mul_le_mul (by omega) k4
  have e2 : S * (2 * (S * (K * T)) + 11 * (S * T)) = 2 * (S * S * T * K) + 11 * (S * S * T) := by
    ring
  have e3 : mapK * (3 * K + 11) * (S * S * T) = 3000 * (S * S * T * K) + 11000 * (S * S * T) := by
    simp only [mapK]; ring
  have e4 : mapK * (L + 1) * ((Val.list [c, .list xs]).wt + (Val.list (xs.map F)).wt + 1) =
      1000 * ((L + 1) * ((Val.list [c, .list xs]).wt + (Val.list (xs.map F)).wt + 1)) := by
    simp only [mapK]; ring
  rw [e3]
  rw [e4] at hcost
  omega

/-- **Foldl with a deterministic body.** -/
theorem kref_foldl {P : Program} {b g : ℕ} (h : P.HasAt b (foldlFuns b g)) {c acc0 : Val}
    {xs : List Val} {G : Val → Val → Val} {Y K d : ℕ}
    (hg : ∀ i (hi : i < xs.length), FunDet P g (.list [c, (xs.take i).foldl G acc0, xs[i]])
      (G ((xs.take i).foldl G acc0) xs[i]) (K * (Y + 1) ^ d))
    (hM : ∀ i ≤ xs.length, ((xs.take i).foldl G acc0).wt ≤ Y)
    (hc : c.wt ≤ Y) (hxs : (Val.list xs).wt ≤ Y) :
    FunDet P b (.list [c, .list xs, acc0]) (xs.foldl G acc0)
      (loopModK * (K + 10) * (Y + 1) ^ (d + 2)) := by
  refine (foldl_spec_fun h hM hg).mono ?_
  obtain ⟨T, hT⟩ : ∃ T, T = (Y + 1) ^ d := ⟨_, rfl⟩
  rw [← hT]
  have hT1 : 1 ≤ T := hT ▸ Nat.one_le_pow _ _ (by omega)
  have hL := length_lt_wt_list xs
  have h0 := hM 0 (Nat.zero_le _)
  simp only [List.take_zero, List.foldl_nil] at h0
  have ha := wt_list3_le c (.list xs) acc0
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  obtain ⟨S, hS⟩ : ∃ S, S = Y + 1 := ⟨_, rfl⟩
  have e1 : (Y + 1) ^ (d + 2) = S * S * T := by rw [pow_add, hT, hS]; ring
  rw [e1]
  set L := xs.length
  have k1 : L * (K * T) ≤ S * S * T * K := by
    have : L * (K * T) ≤ S * (K * T) := Nat.mul_le_mul_right _ (by omega)
    have h2 : S * (K * T) * 1 ≤ S * (K * T) * S := Nat.mul_le_mul_left _ (by omega)
    calc L * (K * T) ≤ S * (K * T) * 1 := by omega
      _ ≤ S * (K * T) * S := h2
      _ = S * S * T * K := by ring
  have k2 : S ≤ S * T := Nat.le_mul_of_pos_right _ hT1
  have k5 : (L + 1) * ((Val.list [c, .list xs, acc0]).wt + L + Y + 1) ≤ S * (10 * (S * T)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : S * (10 * (S * T)) = 10 * (S * S * T) := by ring
  have e3 : loopModK * (K + 10) * (S * S * T) = 1000 * (S * S * T * K) + 10000 * (S * S * T) := by
    simp only [loopModK]; ring
  have e4 : loopModK * (L + 1) * ((Val.list [c, .list xs, acc0]).wt + L + Y + 1) =
      1000 * ((L + 1) * ((Val.list [c, .list xs, acc0]).wt + L + Y + 1)) := by
    simp only [loopModK]; ring
  rw [e3, e4]
  omega

/-- **Iterate with a deterministic body.** -/
theorem kref_iter {P : Program} {b g : ℕ} (h : P.HasAt b (iterFuns b g)) {c : Val} {n : ℕ}
    {accs : ℕ → Val} {Y K d : ℕ}
    (hg : ∀ i < n, FunDet P g (.list [c, .nat i, accs i]) (accs (i + 1)) (K * (Y + 1) ^ d))
    (hM : ∀ i ≤ n, (accs i).wt ≤ Y) (hc : c.wt ≤ Y) (hn : n ≤ Y) :
    FunDet P b (.list [c, .nat n, accs 0]) (accs n) (loopModK * (K + 20) * (Y + 1) ^ (d + 2)) := by
  refine (iter_spec h (Inv := fun i acc => acc = accs i) (M := Y) (B := fun _ => K * (Y + 1) ^ d)
    rfl (fun i acc hi h => h ▸ hM i hi) fun i acc hi hacc => hacc ▸ FunAll.mono (hg i hi)
      fun w c h => ⟨h.1, h.2⟩).mono ?_
  rintro w cost ⟨rfl, hcost⟩
  refine ⟨rfl, ?_⟩
  obtain ⟨T, hT⟩ : ∃ T, T = (Y + 1) ^ d := ⟨_, rfl⟩
  rw [← hT] at hcost
  have hT1 : 1 ≤ T := hT ▸ Nat.one_le_pow _ _ (by omega)
  have h0 := hM 0 (Nat.zero_le _)
  have ha := wt_list3_le c (.nat n) (accs 0)
  have hn2 := wt_nat_le n
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcost
  obtain ⟨S, hS⟩ : ∃ S, S = Y + 1 := ⟨_, rfl⟩
  have e1 : (Y + 1) ^ (d + 2) = S * S * T := by rw [pow_add, hT, hS]; ring
  rw [e1]
  have k1 : n * (K * T) ≤ S * S * T * K := by
    have : n * (K * T) ≤ S * (K * T) := Nat.mul_le_mul_right _ (by omega)
    have h2 : S * (K * T) * 1 ≤ S * (K * T) * S := Nat.mul_le_mul_left _ (by omega)
    calc n * (K * T) ≤ S * (K * T) * 1 := by omega
      _ ≤ S * (K * T) * S := h2
      _ = S * S * T * K := by ring
  have k2 : S ≤ S * T := Nat.le_mul_of_pos_right _ hT1
  have k5 : (n + 1) * ((Val.list [c, .nat n, accs 0]).wt + n + Y + 1) ≤ S * (20 * (S * T)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : S * (20 * (S * T)) = 20 * (S * S * T) := by ring
  have e3 : loopModK * (K + 20) * (S * S * T) = 1000 * (S * S * T * K) + 20000 * (S * S * T) := by
    simp only [loopModK]; ring
  have e4 : loopModK * (n + 1) * ((Val.list [c, .nat n, accs 0]).wt + n + Y + 1) =
      1000 * ((n + 1) * ((Val.list [c, .nat n, accs 0]).wt + n + Y + 1)) := by
    simp only [loopModK]; ring
  rw [e3]
  rw [e4] at hcost
  omega

/-! ### Reading arguments -/

/-- Entry `l` of entry `j` of the argument. -/
theorem Det.arg2 {P : Program} {vs : List Val} {rest : List Val} {j l : ℕ} {ws : List Val}
    {u : Val} (hv : vs[j]? = some (.list ws)) (hw : ws[l]? = some u) :
    Det P (.list vs :: rest) (.get (GI.Lang.arg j) (.nat l)) u (3 * (Val.list vs).wt + j + l + 9) := by
  refine (Det.get' (Det.arg' hv) (Det.nat l) hw).mono ?_
  have h1 : (Val.list ws).wt < (Val.list vs).wt :=
    wt_le_wt_list (List.mem_of_getElem? hv)
  have h2 : u.wt < (Val.list ws).wt := wt_le_wt_list (List.mem_of_getElem? hw)
  omega

/-- `(Y + 1) ^ d` is at least `Y + 1` for `d ≥ 1`. -/
theorem kref_le_pow {Y d : ℕ} (hd : 1 ≤ d) : Y + 1 ≤ (Y + 1) ^ d := by
  calc Y + 1 = (Y + 1) ^ 1 := (pow_one _).symm
    _ ≤ (Y + 1) ^ d := Nat.pow_le_pow_right (by omega) hd

theorem kref_pow_mono {Y d d' : ℕ} (h : d ≤ d') : (Y + 1) ^ d ≤ (Y + 1) ^ d' :=
  Nat.pow_le_pow_right (by omega) h

theorem kref_one_le_pow (Y d : ℕ) : 1 ≤ (Y + 1) ^ d := Nat.one_le_pow _ _ (by omega)


/-! ### Scaled forms: arguments up to `A * (Y + 1)` -/

theorem kref_scale (A Y e : ℕ) : (A * (Y + 1) + 1) ^ e ≤ (A + 1) ^ e * (Y + 1) ^ e := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by rw [Nat.add_mul]; nlinarith) e

theorem kref_body_mono {K Y A d : ℕ} (hA : 1 ≤ A) : K * (Y + 1) ^ d ≤ K * (A * (Y + 1) + 1) ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) d)

theorem kref_mapA {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {xs : List Val} {F : Val → Val} {Y K d A : ℕ} (hA : 1 ≤ A)
    (hf : ∀ x ∈ xs, FunDet P f (.list [c, x]) (F x) (K * (Y + 1) ^ d))
    (hc : c.wt ≤ A * (Y + 1)) (hxs : (Val.list xs).wt ≤ A * (Y + 1)) :
    FunDet P b (.list [c, .list xs]) (.list (xs.map F))
      (mapK * (3 * K + 11) * (A + 1) ^ (d + 2) * (Y + 1) ^ (d + 2)) := by
  refine (kref_map h (Y := A * (Y + 1)) (fun x hx => (hf x hx).mono (kref_body_mono hA)) hc
    hxs).mono ?_
  rw [Nat.mul_assoc _ ((A + 1) ^ (d + 2))]
  exact Nat.mul_le_mul_left _ (kref_scale A Y _)

theorem kref_foldlA {P : Program} {b g : ℕ} (h : P.HasAt b (foldlFuns b g)) {c acc0 : Val}
    {xs : List Val} {G : Val → Val → Val} {Y K d A : ℕ} (hA : 1 ≤ A)
    (hg : ∀ i (hi : i < xs.length), FunDet P g (.list [c, (xs.take i).foldl G acc0, xs[i]])
      (G ((xs.take i).foldl G acc0) xs[i]) (K * (Y + 1) ^ d))
    (hM : ∀ i ≤ xs.length, ((xs.take i).foldl G acc0).wt ≤ A * (Y + 1))
    (hc : c.wt ≤ A * (Y + 1)) (hxs : (Val.list xs).wt ≤ A * (Y + 1)) :
    FunDet P b (.list [c, .list xs, acc0]) (xs.foldl G acc0)
      (loopModK * (K + 10) * (A + 1) ^ (d + 2) * (Y + 1) ^ (d + 2)) := by
  refine (kref_foldl h (Y := A * (Y + 1)) (fun i hi => (hg i hi).mono (kref_body_mono hA)) hM hc
    hxs).mono ?_
  rw [Nat.mul_assoc _ ((A + 1) ^ (d + 2))]
  exact Nat.mul_le_mul_left _ (kref_scale A Y _)

theorem kref_iterA {P : Program} {b g : ℕ} (h : P.HasAt b (iterFuns b g)) {c : Val} {n : ℕ}
    {accs : ℕ → Val} {Y K d A : ℕ} (hA : 1 ≤ A)
    (hg : ∀ i < n, FunDet P g (.list [c, .nat i, accs i]) (accs (i + 1)) (K * (Y + 1) ^ d))
    (hM : ∀ i ≤ n, (accs i).wt ≤ A * (Y + 1)) (hc : c.wt ≤ A * (Y + 1)) (hn : n ≤ A * (Y + 1)) :
    FunDet P b (.list [c, .nat n, accs 0]) (accs n)
      (loopModK * (K + 20) * (A + 1) ^ (d + 2) * (Y + 1) ^ (d + 2)) := by
  refine (kref_iter h (Y := A * (Y + 1)) (fun i hi => (hg i hi).mono (kref_body_mono hA)) hM hc
    hn).mono ?_
  rw [Nat.mul_assoc _ ((A + 1) ^ (d + 2))]
  exact Nat.mul_le_mul_left _ (kref_scale A Y _)


/-! ### Maps over encoded lists -/

/-- The number in a value (`0` for a list). -/
def krefN : Val → ℕ
  | .nat a => a
  | .list _ => 0

@[simp] theorem krefN_nat (a : ℕ) : krefN (.nat a) = a := rfl

/-- **Map over an encoded list.** The body computes `F a` from `enc a`; `F` must agree on
entries with the same encoding. -/
theorem kref_mapL {α : Type} {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {l : List α} {enc : α → Val} {F : α → Val} {Y K d A : ℕ} (hA : 1 ≤ A)
    (henc : ∀ a ∈ l, ∀ a' ∈ l, enc a = enc a' → F a = F a')
    (hf : ∀ a ∈ l, FunDet P f (.list [c, enc a]) (F a) (K * (Y + 1) ^ d))
    (hc : c.wt ≤ A * (Y + 1)) (hxs : (Val.list (l.map enc)).wt ≤ A * (Y + 1)) :
    FunDet P b (.list [c, .list (l.map enc)]) (.list (l.map F))
      (mapK * (3 * K + 11) * (A + 1) ^ (d + 2) * (Y + 1) ^ (d + 2)) := by
  classical
  let G : Val → Val := fun v => if hv : ∃ a ∈ l, enc a = v then F hv.choose else .nat 0
  have hG : ∀ a ∈ l, G (enc a) = F a := by
    intro a ha
    have hv : ∃ a' ∈ l, enc a' = enc a := ⟨a, ha, rfl⟩
    simp only [G, dif_pos hv]
    exact henc _ hv.choose_spec.1 _ ha hv.choose_spec.2
  have := kref_mapA h (F := G) hA (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [hG a ha]; exact hf a ha) hc hxs
  have e : List.map (G ∘ enc) l = List.map F l := List.map_congr_left fun a ha => hG a ha
  rwa [List.map_map, e] at this

end GI.Lang
