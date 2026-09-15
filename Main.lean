import RequestProject.VanDenEssen.Basic
import RequestProject.VanDenEssen.NoetherianInverse
import RequestProject.VanDenEssen.GraphIdeal
import RequestProject.VanDenEssen.Groebner
import RequestProject.VanDenEssen.Criterion
import RequestProject.VanDenEssen.Existence

/-!
# The Van den Essen inversion criterion — top-level statements

This file collects the user-facing statements of the project.  The supporting theory lives in

* `RequestProject.VanDenEssen.Basic` — polynomial maps, composition, automorphisms,
  the Jacobian matrix, the chain rule and multiplicativity of the Jacobian determinant;
* `RequestProject.VanDenEssen.NoetherianInverse` — a surjective endomorphism of a Noetherian
  ring is injective, hence a one-sided polynomial inverse is automatically two-sided;
* `RequestProject.VanDenEssen.GraphIdeal` — the graph ideal `I(F) = ⟨y - F(x)⟩` and the
  identification `I(F) = ker (y ↦ F(x))`;
* `RequestProject.VanDenEssen.Groebner` — the lexicographic elimination order, Gröbner and
  reduced Gröbner bases, and the Van den Essen shape;
* `RequestProject.VanDenEssen.Criterion` — the criterion itself;
* `RequestProject.VanDenEssen.Existence` — every automorphism really does have such a basis,
  so the criterion is not vacuous.

The hypothesis `[CharZero K]` is carried in the statements below because it was requested;
the proofs do not use it — the criterion is valid over an arbitrary field.
-/

namespace VanDenEssen

open MvPolynomial

variable {n : Nat} {K : Type*} [Field K]

/-- **The Van den Essen inversion criterion.**

Let `F : kⁿ → kⁿ` be a polynomial map and let `G` be a reduced Gröbner basis of its graph
ideal `I(F) = ⟨y₁ - F₁(x), …, yₙ - Fₙ(x)⟩` with respect to the lexicographic order in which
all `x`-variables dominate all `y`-variables.  Then `F` is a polynomial automorphism if and
only if `G` consists exactly of polynomials `xᵢ - qᵢ(y)`, one for each `i`. -/
theorem vanDenEssenCriterion [CharZero K]
    (F : PolyMap n K) (G : List (MvPolynomial (Fin (2 * n)) K))
    (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder) :
    IsPolynomialAutomorphism F ↔ hasVanDenEssenShape G :=
  criterion_of_reduced_groebner hG

/-- **Reading the inverse off the Gröbner basis.**

If the reduced Gröbner basis `G` of the graph ideal of `F` has Van den Essen shape
`{x₁ - q₁(y), …, xₙ - qₙ(y)}`, then the inverse of `F` is `(q₁, …, qₙ)`. -/
theorem inverse_of_shape [CharZero K]
    (F : PolyMap n K) (G : List (MvPolynomial (Fin (2 * n)) K))
    (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder)
    (hS : hasVanDenEssenShape G) :
    inverse F = extractInverse G :=
  inverse_from_groebner_shape hG hS

/-- **Closed form of the criterion.**  A polynomial map is an automorphism precisely when the
graph ideal admits a reduced Gröbner basis (for the lexicographic elimination order) in
Van den Essen shape. -/
theorem isPolynomialAutomorphism_iff_exists_vanDenEssenBasis (F : PolyMap n K) :
    IsPolynomialAutomorphism F ↔
      ∃ G : List (MvPolynomial (Fin (2 * n)) K),
        isReducedGrobnerBasis G (graphIdeal F) lexOrder ∧ hasVanDenEssenShape G := by
  refine ⟨exists_reducedGrobnerBasis_of_isPolynomialAutomorphism, ?_⟩
  rintro ⟨G, hG, hS⟩
  exact (criterion_of_reduced_groebner hG).2 hS

end VanDenEssen
