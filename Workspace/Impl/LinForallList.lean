module

public import Workspace.Impl.LinObjectLocalRelations

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linForall₂_take {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (n : ℕ) : List.Forall₂ R (xs.take n) (ys.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons h _ ih => cases n with
    | zero => simp
    | succ n => exact .cons h (ih n)

theorem linForall₂_drop {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (n : ℕ) : List.Forall₂ R (xs.drop n) (ys.drop n) := by
  induction h generalizing n with
  | nil => simp
  | cons h _ ih => cases n with
    | zero => exact .cons h (ih 0)
    | succ n => exact ih n

theorem linForall₂_mem_left {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {a : α} (ha : a ∈ xs) : ∃ b ∈ ys, R a b := by
  induction h with
  | nil => simp at ha
  | cons h _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, by simp, h⟩
    · obtain ⟨b, hb, hab⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem linForall₂_mem_right {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {b : β} (hb : b ∈ ys) : ∃ a ∈ xs, R a b := by
  induction h with
  | nil => simp at hb
  | cons h _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, by simp, h⟩
    · obtain ⟨a, ha, hab⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem linForall₂_comp {α β γ : Type*} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} {xs : List α} {ys : List β} {zs : List γ}
    (h : List.Forall₂ R xs ys) (h' : List.Forall₂ S ys zs)
    (hc : ∀ a b c, R a b → S b c → T a c) : List.Forall₂ T xs zs := by
  induction h generalizing zs with
  | nil => cases h'; exact .nil
  | cons h _ ih => cases h' with
    | cons hs ht => exact .cons (hc _ _ _ h hs) (ih ht)

theorem linForall₂_source {α : Type*} (enc : α → Val) (he : Function.Injective enc)
    (R : α → Val → Prop) {xs : List α} {ws : List Val}
    (h : List.Forall₂ (fun v w => ∃ x, v = enc x ∧ R x w) (xs.map enc) ws) :
    List.Forall₂ R xs ws := by
  rw [List.forall₂_map_left_iff] at h
  exact h.imp fun _ _ ⟨x, hx, hr⟩ => (he hx) ▸ hr

end GI.Impl
