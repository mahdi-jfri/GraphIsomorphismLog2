module

public import Workspace.Impl.LinPrimeSeparation
public import Workspace.Impl.LinPrimeEval

@[expose] public section

/-! The mixed-primary loop imposes the zero equation for bounded prime
characteristics in increasing order. Each partial equation is characteristic. -/
namespace GI.Impl

variable {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)

def linMixedFiber (j : ℕ) (x : linFiniteVec m) : Prop :=
  ∀ p (hp : p.Prime), p ≤ j → linPrimeProjection (linTrialPrimaryData m p hp hm) x = 0

theorem linMixedFiber_zero (j : ℕ) : linMixedFiber m hm j 0 := by
  intro p hp hj
  exact map_zero _

theorem linMixedFiber_start (x : linFiniteVec m) : linMixedFiber m hm 0 x := by
  intro p hp hj
  have hh := hp.two_le
  omega

theorem linMixedFiber_mono {i j : ℕ} (hij : i ≤ j) {x : linFiniteVec m}
    (hx : linMixedFiber m hm j x) : linMixedFiber m hm i x :=
  fun p hp hpi => hx p hp (hpi.trans hij)

theorem linMixedFiber_map (j : ℕ) (f : linFiniteVec m →+ linFiniteVec m) (x : linFiniteVec m)
    (hx : linMixedFiber m hm j x) : linMixedFiber m hm j (f x) := by
  intro p hp hj
  exact linPrimeProjection_preserved _ hm f x (hx p hp hj)

theorem linMixedFiber_add (j : ℕ) {x y : linFiniteVec m}
    (hx : linMixedFiber m hm j x) (hy : linMixedFiber m hm j y) :
    linMixedFiber m hm j (x + y) := by
  intro p hp hj
  rw [map_add, hx p hp hj, hy p hp hj, add_zero]

theorem linMixedFiber_eval {G : Type*} [Group G] (j : ℕ)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (g : G) (x : linFiniteVec m) (hx : linMixedFiber m hm j x)
    (hc : linMixedFiber m hm j (c g)) : linMixedFiber m hm j (linFiniteEval ρ c g x) :=
  linMixedFiber_add m hm j (linMixedFiber_map m hm j (ρ g).toAddMonoidHom x hx) hc

theorem linMixedFiber_next {j : ℕ} {x : linFiniteVec m}
    (hx : linMixedFiber m hm j x)
    (hnew : ∀ hp : (j + 1).Prime,
      linPrimeProjection (linTrialPrimaryData m (j + 1) hp hm) x = 0) :
    linMixedFiber m hm (j + 1) x := by
  intro p hp hpj
  rcases Nat.eq_or_lt_of_le hpj with he | hl
  · subst p
    exact hnew hp
  · exact hx p hp (by omega)

theorem linMixedFiber_skip {j : ℕ} (h : ¬ (j + 1).Prime) {x : linFiniteVec m}
    (hx : linMixedFiber m hm j x) : linMixedFiber m hm (j + 1) x :=
  linMixedFiber_next m hm hx (fun hp => (h hp).elim)

theorem linMixedFiber_terminal (bound : ℕ)
    (hbound : ∀ i p, p.Prime → p ∣ m i → p ≤ bound) (x : linFiniteVec m)
    (hx : linMixedFiber m hm bound x) : x = 0 :=
  linPrimeProjection_all_zero m hm bound hbound x hx

end GI.Impl
