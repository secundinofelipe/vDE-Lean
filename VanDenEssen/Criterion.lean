import RequestProject.VanDenEssen.Groebner
import RequestProject.VanDenEssen.NoetherianInverse

/-!
# The Van den Essen inversion criterion

Let `F : kⁿ → kⁿ` be a polynomial map over a field `k`, let

`I(F) = ⟨y₁ - F₁(x), …, yₙ - Fₙ(x)⟩ ⊆ k[x₁,…,xₙ,y₁,…,yₙ]`

be its graph ideal and let `G` be the reduced Gröbner basis of `I(F)` for the lexicographic
order with `x₁ > ⋯ > xₙ > y₁ > ⋯ > yₙ`.  Van den Essen's criterion states:

> `F` is a polynomial automorphism **iff** `G = {x₁ - q₁(y), …, xₙ - qₙ(y)}`,
> and in that case `F⁻¹ = (q₁, …, qₙ)`.

The proof assembled here runs as follows.

* `mem_graphIdeal_iff` (Lemma 2) identifies `I(F)` with the kernel of the substitution
  `y := F(x)`.  In particular `xᵢ - qᵢ(y) ∈ I(F)` holds exactly when `q ∘ F = id`.
* If the basis has the stated shape, its members lie in `I(F)`, so the `qᵢ` form a **left**
  inverse of `F`; the Noetherian reduction step (Lemma 3) upgrades this to a genuine inverse.
* Conversely, if `F` is invertible with inverse `H`, then `xᵢ - Hᵢ(y) ∈ I(F)` and its leading
  monomial is `xᵢ`.  The Gröbner property forces `G` to contain an element whose leading
  monomial divides `xᵢ`; properness of `I(F)` rules out a constant, so the leading monomial is
  exactly `xᵢ`.  Reducedness then forces the remaining monomials of that element — and of every
  element of `G` — to be free of `x`-variables, which pins down the shape.
-/

namespace VanDenEssen

open MvPolynomial

section Criterion

variable {n : Nat} {K : Type*} [Field K]

open Classical in
/-- The inverse of a polynomial automorphism (junk value `0` for non-automorphisms). -/
noncomputable def inverse (F : PolyMap n K) : PolyMap n K :=
  if h : IsPolynomialAutomorphism F then h.choose else fun _ => 0

lemma inverse_spec {F : PolyMap n K} (h : IsPolynomialAutomorphism F) :
    comp F (inverse F) = idMap ∧ comp (inverse F) F = idMap := by
  rw [inverse, dif_pos h]
  exact h.choose_spec

/-- A polynomial whose monomials involve no `x`-variable comes from `k[y]`. -/
lemma exists_rename_yv_of_support (p : MvPolynomial (Fin (2 * n)) K)
    (h : ∀ d ∈ p.support, ∀ j : Fin n, d (xv j) = 0) :
    ∃ q : MvPolynomial (Fin n) K, rename yv q = p := by
  refine exists_rename_eq_of_vars_subset_range p yv yv_injective ?_
  intro k hk
  rw [Finset.mem_coe, mem_vars] at hk
  obtain ⟨d, hd, hkd⟩ := hk
  rcases xv_or_yv k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact absurd (h d hd i) (Finsupp.mem_support_iff.1 hkd)
  · exact ⟨i, rfl⟩

/-! ### The easy direction: the shape produces an inverse -/

/-- If a Gröbner basis of `I(F)` has Van den Essen shape then `extractInverse G` is a
left inverse of `F`. -/
theorem comp_extractInverse_eq_id {F : PolyMap n K} {G : List (MvPolynomial (Fin (2 * n)) K)}
    (hG : isGrobnerBasis G (graphIdeal F) lexOrder) (hS : hasVanDenEssenShape G) :
    comp (extractInverse G) F = idMap := by
  refine (forall_X_xv_sub_mem_iff F (extractInverse G)).1 fun i => ?_
  exact hG.mem_ideal (extractInverse_spec hS i)

/-- **Van den Essen, sufficiency.**  A basis of the graph ideal in Van den Essen shape
certifies that `F` is a polynomial automorphism. -/
theorem isPolynomialAutomorphism_of_shape {F : PolyMap n K}
    {G : List (MvPolynomial (Fin (2 * n)) K)}
    (hG : isGrobnerBasis G (graphIdeal F) lexOrder) (hS : hasVanDenEssenShape G) :
    IsPolynomialAutomorphism F :=
  (isPolynomialAutomorphism_of_left_inverse (comp_extractInverse_eq_id hG hS)).1

/-! ### The hard direction: invertibility forces the shape -/

variable {F : PolyMap n K} {G : List (MvPolynomial (Fin (2 * n)) K)}

/-- Step A: for every `i` the reduced Gröbner basis contains an element with leading
monomial exactly `xᵢ`. -/
theorem exists_mem_degree_eq_single (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder)
    (hF : IsPolynomialAutomorphism F) (i : Fin n) :
    ∃ g ∈ G, lexOrder.degree g = Finsupp.single (xv i) 1 := by
  obtain ⟨H, hFH, hHF⟩ := hF
  -- `xᵢ - Hᵢ(y)` lies in the graph ideal and its leading monomial is `xᵢ`.
  have hmem : (X (xv i) - rename yv (H i)) ∈ graphIdeal F :=
    (forall_X_xv_sub_mem_iff F H).2 hHF i
  have hne := X_xv_sub_rename_yv_ne_zero (K := K) i (H i)
  obtain ⟨g, hg, hg0, hle⟩ := hG.exists_degree_le _ hmem hne
  rw [degree_X_xv_sub_rename_yv] at hle
  rcases le_single_one_iff.1 hle with h0 | h1
  · -- a member with trivial leading monomial would be the constant `1`, but `I(F)` is proper
    exfalso
    have hgC : g = C (lexOrder.leadingCoeff g) := MonomialOrder.eq_C_of_degree_eq_zero h0
    rw [hG.monic g hg, map_one] at hgC
    exact one_notMem_graphIdeal F (hgC ▸ hG.mem_ideal hg)
  · exact ⟨g, hg, h1⟩

/-- Step B: in a reduced Gröbner basis of the graph ideal of an automorphism, the only
monomial of a member that can involve an `x`-variable is its leading monomial. -/
theorem eq_degree_of_mem_support_of_apply_xv_ne_zero
    (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder) (hF : IsPolynomialAutomorphism F)
    {h : MvPolynomial (Fin (2 * n)) K} (hh : h ∈ G) {d : Fin (2 * n) →₀ ℕ}
    (hd : d ∈ h.support) {j : Fin n} (hdj : d (xv j) ≠ 0) : d = lexOrder.degree h := by
  obtain ⟨g, hgG, hgdeg⟩ := exists_mem_degree_eq_single hG hF j
  have hdvd : lexOrder.degree g ≤ d := by
    rw [hgdeg, Finsupp.le_def]
    intro a
    rcases eq_or_ne (xv j) a with rfl | hne
    · rw [Finsupp.single_eq_same]; omega
    · rw [Finsupp.single_apply, if_neg hne]; exact Nat.zero_le _
  -- reducedness forbids `xⱼ` from dividing a monomial of a *different* member
  have hgh : g = h := by
    by_contra hne
    exact hG.reduced h hh d hd g hgG hne hdvd
  subst hgh
  have h1 : lexOrder.toSyn (lexOrder.degree g) ≤ lexOrder.toSyn d := lexOrder.toSyn_monotone hdvd
  have h2 : lexOrder.toSyn d ≤ lexOrder.toSyn (lexOrder.degree g) := MonomialOrder.le_degree hd
  exact lexOrder.toSyn.injective (le_antisymm h2 h1)

/-- Step C: every member of the basis has the form `xᵢ - q(y)`. -/
theorem mem_form_of_reduced (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder)
    (hF : IsPolynomialAutomorphism F) {h : MvPolynomial (Fin (2 * n)) K} (hh : h ∈ G) :
    ∃ (i : Fin n) (q : MvPolynomial (Fin n) K), h = X (xv i) - rename yv q := by
  have hne0 : h ≠ 0 := hG.ne_zero hh
  by_cases hx : ∃ j : Fin n, (lexOrder.degree h) (xv j) ≠ 0
  · -- the leading monomial involves some `xⱼ`; reducedness pins it down to be exactly `xⱼ`
    obtain ⟨j, hj⟩ := hx
    obtain ⟨g, hgG, hgdeg⟩ := exists_mem_degree_eq_single hG hF j
    have hdvd : lexOrder.degree g ≤ lexOrder.degree h := by
      rw [hgdeg, Finsupp.le_def]
      intro a
      rcases eq_or_ne (xv j) a with rfl | hne
      · rw [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_apply, if_neg hne]; exact Nat.zero_le _
    have hgh : g = h := by
      by_contra hne
      exact hG.reduced h hh (lexOrder.degree h) (MonomialOrder.degree_mem_support hne0) g hgG hne
        hdvd
    have hdeg : lexOrder.degree h = Finsupp.single (xv j) 1 := hgh ▸ hgdeg
    have hc1 : coeff (Finsupp.single (xv j) 1) h = 1 := by
      have hlc : coeff (lexOrder.degree h) h = 1 := hG.monic h hh
      rwa [hdeg] at hlc
    -- all the remaining monomials are free of `x`-variables
    have hpure : ∀ d ∈ (h - X (xv j)).support, ∀ j' : Fin n, d (xv j') = 0 := by
      intro d hd j'
      have hcoeff : coeff d (h - X (xv j)) ≠ 0 := mem_support_iff.1 hd
      have hdne : d ≠ Finsupp.single (xv j) 1 := by
        rintro rfl
        exact hcoeff (by simp [coeff_sub, coeff_X', hc1])
      have hdh : d ∈ h.support := by
        refine mem_support_iff.2 fun hc => hcoeff ?_
        simp [coeff_sub, hc, coeff_X', Ne.symm hdne]
      by_contra hdj'
      exact hdne (by rw [eq_degree_of_mem_support_of_apply_xv_ne_zero hG hF hh hdh hdj', hdeg])
    obtain ⟨q, hq⟩ := exists_rename_yv_of_support (h - X (xv j)) hpure
    refine ⟨j, -q, ?_⟩
    rw [map_neg, hq]
    ring
  · -- otherwise every monomial of `h` is free of `x`, forcing `h = 0`
    exfalso
    push_neg at hx
    have hpure : ∀ d ∈ h.support, ∀ j : Fin n, d (xv j) = 0 := by
      intro d hd j
      by_contra hdj
      rw [eq_degree_of_mem_support_of_apply_xv_ne_zero hG hF hh hd hdj] at hdj
      exact hdj (hx j)
    obtain ⟨q, hq⟩ := exists_rename_yv_of_support h hpure
    have hmem : h ∈ graphIdeal F := hG.mem_ideal hh
    rw [← hq] at hmem
    have hq0 : aeval F q = 0 := (rename_yv_mem_graphIdeal_iff F q).1 hmem
    obtain ⟨H, hFH, _⟩ := hF
    have hinj := aeval_injective_of_comp_eq_id hFH
    have hq00 : q = 0 := hinj (by simpa using hq0)
    rw [hq00, map_zero] at hq
    exact hne0 hq.symm

/-- **Van den Essen, necessity.**  If `F` is an automorphism, the reduced Gröbner basis of its
graph ideal has Van den Essen shape. -/
theorem shape_of_reduced_groebner (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder)
    (hF : IsPolynomialAutomorphism F) : hasVanDenEssenShape G := by
  refine ⟨fun i => ?_, fun h hh => mem_form_of_reduced hG hF hh⟩
  obtain ⟨g, hgG, hgdeg⟩ := exists_mem_degree_eq_single hG hF i
  obtain ⟨i', q, rfl⟩ := mem_form_of_reduced hG hF hgG
  rw [degree_X_xv_sub_rename_yv] at hgdeg
  obtain rfl := xv_injective (Finsupp.single_left_injective one_ne_zero hgdeg)
  exact ⟨q, hgG⟩

/-! ### The criterion and the extraction of the inverse -/

/-- **The Van den Essen inversion criterion.** -/
theorem criterion_of_reduced_groebner (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder) :
    IsPolynomialAutomorphism F ↔ hasVanDenEssenShape G :=
  ⟨shape_of_reduced_groebner hG, isPolynomialAutomorphism_of_shape hG.toisGrobnerBasis⟩

/-- **Extraction of the inverse.**  Once the reduced Gröbner basis has Van den Essen shape,
its members `xᵢ - qᵢ(y)` display the inverse of `F`. -/
theorem inverse_from_groebner_shape (hG : isReducedGrobnerBasis G (graphIdeal F) lexOrder)
    (hS : hasVanDenEssenShape G) : inverse F = extractInverse G := by
  have hauto : IsPolynomialAutomorphism F :=
    isPolynomialAutomorphism_of_shape hG.toisGrobnerBasis hS
  obtain ⟨hFi, hiF⟩ := inverse_spec hauto
  have hinj := aeval_injective_of_comp_eq_id hFi
  exact comp_left_inverse_unique hinj hiF (comp_extractInverse_eq_id hG.toisGrobnerBasis hS)

end Criterion

end VanDenEssen
