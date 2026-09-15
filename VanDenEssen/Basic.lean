import Mathlib

/-!
# Polynomial maps, their composition, and their Jacobians

This file sets up the basic vocabulary used throughout the formalisation of the
*Van den Essen inversion criterion*.

A polynomial map `F : kⁿ → kⁿ` is recorded simply as an `n`-tuple of polynomials
in `n` variables, i.e. as a term of `PolyMap n K = Fin n → MvPolynomial (Fin n) K`.
Composition of polynomial maps is substitution of polynomials, and a *polynomial
automorphism* is a polynomial map admitting a two–sided inverse polynomial map.

We also introduce the Jacobian matrix `𝒥(F)` of a polynomial map and prove the
chain rule `𝒥(F ∘ G) = (𝒥 F)(G) ⬝ 𝒥 G`, together with the multiplicativity of
the Jacobian determinant.
-/

namespace VanDenEssen

open MvPolynomial

section Defs

variable {n : Nat} {K : Type*} [CommRing K]

/-- A polynomial map `kⁿ → kⁿ` is an `n`-tuple of polynomials in `n` variables. -/
abbrev PolyMap (n : Nat) (K : Type*) [CommRing K] := Fin n → MvPolynomial (Fin n) K

/-- The identity polynomial map `x ↦ x`. -/
noncomputable def idMap : PolyMap n K := fun i => X i

/-- Composition of polynomial maps: `comp F G` represents `F ∘ G`, obtained by
substituting the components of `G` for the variables of `F`. -/
noncomputable def comp (F G : PolyMap n K) : PolyMap n K := fun i => aeval G (F i)

/-- `F` is a polynomial automorphism when it has a two-sided inverse
which is again a polynomial map. -/
def IsPolynomialAutomorphism (F : PolyMap n K) : Prop :=
  ∃ G : PolyMap n K, comp F G = idMap ∧ comp G F = idMap

@[simp] lemma idMap_apply (i : Fin n) : (idMap : PolyMap n K) i = X i := rfl

@[simp] lemma comp_apply (F G : PolyMap n K) (i : Fin n) : comp F G i = aeval G (F i) := rfl

/-- Substitution is functorial: evaluating `p` at `F` and then at `G` is the same as
evaluating `p` at `comp F G`. -/
lemma aeval_aeval_eq_aeval_comp (F G : PolyMap n K) (p : MvPolynomial (Fin n) K) :
    aeval G (aeval F p) = aeval (comp F G) p := by
  rw [← AlgHom.comp_apply, comp_aeval]
  rfl

/-- `comp F G = idMap` exactly says that `aeval G ∘ aeval F` is the identity endomorphism. -/
lemma comp_eq_idMap_iff (F G : PolyMap n K) :
    comp F G = idMap ↔ ∀ p : MvPolynomial (Fin n) K, aeval G (aeval F p) = p := by
  constructor
  · intro h p
    rw [aeval_aeval_eq_aeval_comp, h]
    exact aeval_X_left_apply p
  · intro h
    funext i
    have := h (X i)
    simpa using this

/-- If `comp F G = idMap` then substitution by `F` is injective. -/
lemma aeval_injective_of_comp_eq_id {F G : PolyMap n K} (h : comp F G = idMap) :
    Function.Injective (aeval F : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K) := by
  intro p q hpq
  have hp := (comp_eq_idMap_iff F G).1 h p
  have hq := (comp_eq_idMap_iff F G).1 h q
  rw [← hp, ← hq, hpq]

/-- If `comp F G = idMap` then substitution by `G` is surjective. -/
lemma aeval_surjective_of_comp_eq_id {F G : PolyMap n K} (h : comp F G = idMap) :
    Function.Surjective (aeval G : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K) :=
  fun p => ⟨aeval F p, (comp_eq_idMap_iff F G).1 h p⟩

/-- A one-sided inverse of a polynomial map is unique, provided substitution by `F`
is injective. -/
lemma comp_left_inverse_unique {F G G' : PolyMap n K}
    (hinj : Function.Injective (aeval F : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K))
    (h : comp G F = idMap) (h' : comp G' F = idMap) : G = G' := by
  funext i
  apply hinj
  have hi : aeval F (G i) = X i := congrFun h i
  have hi' : aeval F (G' i) = X i := congrFun h' i
  rw [hi, hi']

end Defs

/-! ## The Jacobian matrix and the chain rule -/

section Jacobian

variable {n : Nat} {K : Type*} [CommRing K]

/-- The Jacobian matrix `𝒥(F)` of a polynomial map, with entries
`𝒥(F) i j = ∂Fᵢ / ∂xⱼ`. -/
noncomputable def jacobian (F : PolyMap n K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  Matrix.of fun i j => pderiv j (F i)

/-- The Jacobian determinant `det 𝒥(F)`. -/
noncomputable def jacobianDet (F : PolyMap n K) : MvPolynomial (Fin n) K :=
  (jacobian F).det

@[simp] lemma jacobian_apply (F : PolyMap n K) (i j : Fin n) :
    jacobian F i j = pderiv j (F i) := rfl

/-- **Chain rule for partial derivatives.**  Differentiating a substituted polynomial
`p(G₁, …, Gₙ)` with respect to `xⱼ` produces the familiar sum
`∑ₖ (∂p/∂xₖ)(G) · ∂Gₖ/∂xⱼ`. -/
theorem pderiv_aeval (G : PolyMap n K) (p : MvPolynomial (Fin n) K) (j : Fin n) :
    pderiv j (aeval G p) = ∑ k : Fin n, (aeval G (pderiv k p)) * pderiv j (G k) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [map_add, map_add, add_mul]
  | mul_X p i hp =>
      have hpd : ∀ k : Fin n, pderiv k (p * X i) = pderiv k p * X i + (if k = i then p else 0) := by
        intro k
        rw [Derivation.leibniz, pderiv_X]
        by_cases hk : k = i <;> simp [hk, smul_eq_mul, Pi.single_apply] <;> ring
      have hterm : ∀ k : Fin n, aeval G (pderiv k (p * X i)) * pderiv j (G k)
          = (aeval G (pderiv k p) * pderiv j (G k)) * G i
            + (if k = i then aeval G p * pderiv j (G k) else 0) := by
        intro k
        rw [hpd k]
        by_cases hk : k = i <;> simp [hk, map_add, map_mul] <;> ring
      rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k),
        Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ i
        (fun k => aeval G p * pderiv j (G k))]
      rw [map_mul, aeval_X, Derivation.leibniz, hp]
      simp [smul_eq_mul]
      ring

/-- **Lemma 1 (Chain rule for the Jacobian).**  The Jacobian matrix of a composition is
the (substituted) product of the Jacobian matrices. -/
theorem jacobian_comp (F G : PolyMap n K) :
    jacobian (comp F G) =
      ((jacobian F).map (aeval G : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K)) *
        jacobian G := by
  refine Matrix.ext fun i j => ?_
  simp only [jacobian, Matrix.of_apply, comp_apply, Matrix.mul_apply, Matrix.map_apply]
  exact pderiv_aeval G (F i) j

/-- **Multiplicativity of the Jacobian determinant.** -/
theorem jacobianDet_comp (F G : PolyMap n K) :
    jacobianDet (comp F G) = aeval G (jacobianDet F) * jacobianDet G := by
  let f : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K :=
    (aeval G : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K).toRingHom
  unfold jacobianDet
  rw [jacobian_comp, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det f (jacobian F)).symm

/-- The Jacobian matrix of the identity map is the identity matrix. -/
@[simp] lemma jacobian_idMap : jacobian (idMap : PolyMap n K) = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [jacobian_apply, idMap_apply, pderiv_X, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, Pi.single_apply]

@[simp] lemma jacobianDet_idMap : jacobianDet (idMap : PolyMap n K) = 1 := by
  rw [jacobianDet, jacobian_idMap, Matrix.det_one]

/-- **The Jacobian determinant of a polynomial automorphism is a unit.**
This is the classical necessary condition underlying the Jacobian conjecture. -/
theorem isUnit_jacobianDet (F : PolyMap n K) (hF : IsPolynomialAutomorphism F) :
    IsUnit (jacobianDet F) := by
  obtain ⟨G, hFG, hGF⟩ := hF
  have h := jacobianDet_comp G F
  rw [hGF, jacobianDet_idMap] at h
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h.symm)

end Jacobian

end VanDenEssen
