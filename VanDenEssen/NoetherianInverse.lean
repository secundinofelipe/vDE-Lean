import RequestProject.VanDenEssen.Basic

/-!
# From one-sided to two-sided inverses

The mathematical content of this file is the classical observation of
**Vasconcelos / Strooker** that a *surjective* endomorphism of a Noetherian
commutative ring is automatically injective.  Applied to the polynomial ring
`k[x₁, …, xₙ]` (Noetherian by the Hilbert basis theorem) it yields the *reduction
step* used by van den Essen: to invert a polynomial map it suffices to produce a
**one-sided** polynomial inverse.

Informally: let `f : R → R` be a surjective ring endomorphism.  The kernels
`ker fⁿ` form an ascending chain of ideals, hence stabilise at some `N`.  If
`f x = 0`, write `x = f^N y` using surjectivity; then `f^(N+1) y = 0`, so
`y ∈ ker f^(N+1) = ker f^N`, whence `x = f^N y = 0`.
-/

namespace VanDenEssen

open MvPolynomial Function

/-- **A surjective endomorphism of a Noetherian commutative ring is injective.** -/
theorem injective_of_surjective_of_isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hf : Surjective f) : Injective f := by
  -- The kernels of the iterates form an ascending chain of ideals.
  have mono : Monotone (fun k : ℕ => RingHom.ker (f ^ k)) := by
    intro a b hab x hx
    simp only [RingHom.mem_ker] at *
    have hb : b = (b - a) + a := by omega
    rw [hb, pow_add]
    show (f ^ (b - a)) ((f ^ a) x) = 0
    rw [hx, map_zero]
  -- Noetherianity makes the chain stabilise.
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.2 (by infer_instance)) ⟨_, mono⟩
  simp only [OrderHom.coe_mk] at hN
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (Function.Surjective.iterate hf N) x
  have hy : y ∈ RingHom.ker (f ^ (N + 1)) := by
    simp only [RingHom.mem_ker, pow_succ']
    show f ((f ^ N) y) = 0
    exact hx
  rw [← hN (N + 1) (by omega)] at hy
  simpa [RingHom.mem_ker] using hy

variable {n : Nat} {K : Type*} [Field K]

/-- **Lemma 3 (Reduction step).**  A polynomial map with a one-sided polynomial inverse
is a polynomial automorphism: if `G ∘ F = id` then automatically `F ∘ G = id`. -/
theorem isPolynomialAutomorphism_of_left_inverse {F G : PolyMap n K}
    (h : comp G F = idMap) : IsPolynomialAutomorphism F ∧ comp F G = idMap := by
  -- `comp G F = idMap` says that `aeval F ∘ aeval G = id`, so `aeval F` is surjective.
  have hsurj : Surjective (aeval F : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K) :=
    aeval_surjective_of_comp_eq_id h
  -- The polynomial ring is Noetherian, so `aeval F` is also injective, hence bijective.
  have hinj : Injective (aeval F : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K) := by
    have := injective_of_surjective_of_isNoetherianRing
      ((aeval F : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K).toRingHom) hsurj
    exact this
  -- Now `aeval G` is a two-sided inverse of `aeval F`.
  have hGF : ∀ p, aeval F (aeval G p) = p := (comp_eq_idMap_iff G F).1 h
  have hFG : comp F G = idMap := by
    funext i
    apply hinj
    simp only [comp_apply, idMap_apply, hGF, aeval_X]
  exact ⟨⟨G, hFG, h⟩, hFG⟩

/-- A polynomial map admitting a left inverse is an automorphism. -/
theorem isPolynomialAutomorphism_of_exists_left_inverse {F : PolyMap n K}
    (h : ∃ G : PolyMap n K, comp G F = idMap) : IsPolynomialAutomorphism F := by
  obtain ⟨G, hG⟩ := h
  exact (isPolynomialAutomorphism_of_left_inverse hG).1

end VanDenEssen
