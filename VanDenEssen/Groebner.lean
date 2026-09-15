import RequestProject.VanDenEssen.GraphIdeal

/-!
# Gröbner bases and the Van den Essen shape

Van den Essen's inversion algorithm computes a **reduced Gröbner basis** of the graph ideal
`I(F) ⊆ k[x, y]` for the *lexicographic* order in which all `x`-variables dominate all
`y`-variables, and then inspects its shape.

This file contains:

* `lexOrder`, the lexicographic monomial order on `Fin (2 * n)` (the `x`-indices come first,
  hence are the largest variables);
* the order-theoretic facts we need about it, in particular that the leading monomial of
  `xᵢ - q(y)` is `xᵢ`;
* the definitions `isGrobnerBasis` and `isReducedGrobnerBasis`.  We use the *leading term*
  characterisation: `G` is a Gröbner basis of `I` when `G` generates `I` and the leading
  monomial of every nonzero element of `I` is divisible by the leading monomial of some
  element of `G`.  A Gröbner basis is *reduced* when each of its members is monic and no
  monomial occurring in a member is divisible by the leading monomial of a *different*
  member;
* `hasVanDenEssenShape`, the shape predicate: the basis consists exactly of polynomials
  `xᵢ - qᵢ(y)`, one for each `i`.
-/

namespace VanDenEssen

open MvPolynomial

section Lex

variable {n : Nat}

/-- The lexicographic monomial order on `k[x₁,…,xₙ,y₁,…,yₙ]`.  Since the `x`-indices are the
small ones in `Fin (2 * n)`, this is the order with `x₁ > x₂ > ⋯ > xₙ > y₁ > ⋯ > yₙ`, which is
an elimination order for the `x`-variables. -/
noncomputable def lexOrder : MonomialOrder (Fin (2 * n)) := MonomialOrder.lex

/-- A monomial involving only `y`-variables is strictly smaller than `xᵢ`. -/
lemma lex_lt_single_xv {i : Fin n} {d : Fin (2 * n) →₀ ℕ} (hd : ∀ j : Fin n, d (xv j) = 0) :
    lexOrder.toSyn d < lexOrder.toSyn (Finsupp.single (xv i) 1) := by
  rw [lexOrder, MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  simp only [ofLex_toLex]
  refine ⟨xv i, ?_, ?_⟩
  · intro j hj
    have hjv : j.val < i.val := by simpa using hj
    have hi := i.isLt
    have hje : j = xv ⟨j.val, by omega⟩ := Fin.ext (by simp)
    rw [hje, hd, Finsupp.single_apply, if_neg]
    intro hcon
    have hv : (xv i).val = (xv (⟨j.val, by omega⟩ : Fin n)).val := congrArg Fin.val hcon
    simp only [xv_val] at hv
    omega
  · rw [hd i, Finsupp.single_eq_same]
    norm_num

variable {K : Type*} [CommRing K]

/-- Monomials of a polynomial in the `y`-variables involve no `x`-variable. -/
lemma support_rename_yv_apply_xv {q : MvPolynomial (Fin n) K}
    {d : Fin (2 * n) →₀ ℕ} (hd : d ∈ (rename yv q).support) (j : Fin n) : d (xv j) = 0 := by
  classical
  rw [support_rename_of_injective yv_injective] at hd
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.1 hd
  refine Finsupp.mapDomain_notin_range e (xv j) ?_
  rintro ⟨l, hl⟩
  exact xv_ne_yv j l hl.symm

/-- The leading monomial of a polynomial in the `y`-variables involves no `x`-variable. -/
lemma degree_rename_yv_apply_xv (q : MvPolynomial (Fin n) K) (j : Fin n) :
    lexOrder.degree (rename yv q) (xv j) = 0 := by
  by_cases hq : (rename yv q : MvPolynomial (Fin (2 * n)) K) = 0
  · rw [hq, MonomialOrder.degree_zero]; rfl
  · exact support_rename_yv_apply_xv (MonomialOrder.degree_mem_support hq) j

variable [Nontrivial K]

/-- **The leading monomial of `xᵢ - q(y)` is `xᵢ`.**  This is the reason van den Essen uses a
lexicographic (elimination) order. -/
lemma degree_X_xv_sub_rename_yv (i : Fin n) (q : MvPolynomial (Fin n) K) :
    lexOrder.degree (X (xv i) - rename yv q) = Finsupp.single (xv i) 1 := by
  have hlt : lexOrder.toSyn (lexOrder.degree (-(rename yv q) : MvPolynomial (Fin (2 * n)) K)) <
      lexOrder.toSyn (lexOrder.degree (X (xv i) : MvPolynomial (Fin (2 * n)) K)) := by
    rw [MonomialOrder.degree_neg, MonomialOrder.degree_X]
    exact lex_lt_single_xv (degree_rename_yv_apply_xv q)
  rw [sub_eq_add_neg, MonomialOrder.degree_add_of_lt hlt, MonomialOrder.degree_X]

lemma monic_X_xv_sub_rename_yv (i : Fin n) (q : MvPolynomial (Fin n) K) :
    lexOrder.leadingCoeff (X (xv i) - rename yv q) = 1 := by
  have hlt : lexOrder.toSyn (lexOrder.degree (-(rename yv q) : MvPolynomial (Fin (2 * n)) K)) <
      lexOrder.toSyn (lexOrder.degree (X (xv i) : MvPolynomial (Fin (2 * n)) K)) := by
    rw [MonomialOrder.degree_neg, MonomialOrder.degree_X]
    exact lex_lt_single_xv (degree_rename_yv_apply_xv q)
  rw [sub_eq_add_neg, MonomialOrder.leadingCoeff_add_of_lt hlt, MonomialOrder.leadingCoeff_X]

lemma X_xv_sub_rename_yv_ne_zero (i : Fin n) (q : MvPolynomial (Fin n) K) :
    (X (xv i) - rename yv q : MvPolynomial (Fin (2 * n)) K) ≠ 0 := by
  intro h
  have := monic_X_xv_sub_rename_yv i q
  rw [h, MonomialOrder.leadingCoeff_zero] at this
  exact zero_ne_one this

end Lex

section Divisibility

variable {σ : Type*}

/-- A monomial dividing a single variable is either `1` or that variable. -/
lemma le_single_one_iff {s : σ} {d : σ →₀ ℕ} :
    d ≤ Finsupp.single s 1 ↔ d = 0 ∨ d = Finsupp.single s 1 := by
  classical
  constructor
  · intro h
    by_cases hs : d s = 0
    · left
      ext t
      by_cases ht : t = s
      · rw [ht, hs]; rfl
      · have := h t
        rw [Finsupp.single_apply, if_neg (Ne.symm ht)] at this
        simpa using Nat.le_zero.1 this
    · right
      have hs1 : d s = 1 := by
        have := h s
        rw [Finsupp.single_eq_same] at this
        omega
      ext t
      by_cases ht : t = s
      · rw [ht, hs1, Finsupp.single_eq_same]
      · have := h t
        rw [Finsupp.single_apply, if_neg (Ne.symm ht)] at this
        rw [Finsupp.single_apply, if_neg (Ne.symm ht)]
        simpa using Nat.le_zero.1 this
  · rintro (rfl | rfl)
    · exact zero_le _
    · exact le_rfl

end Divisibility

section GroebnerDefs

variable {n : Nat} {K : Type*} [CommRing K]

/-- `G` is a **Gröbner basis** of the ideal `I` for the monomial order `m`:
`G` generates `I`, and the leading monomial of any nonzero element of `I` is divisible by
the leading monomial of some element of `G`. -/
structure isGrobnerBasis (G : List (MvPolynomial (Fin (2 * n)) K))
    (I : Ideal (MvPolynomial (Fin (2 * n)) K)) (m : MonomialOrder (Fin (2 * n))) : Prop where
  /-- `G` generates the ideal `I`. -/
  span_eq : Ideal.span {g | g ∈ G} = I
  /-- Leading monomials of `G` generate the initial ideal of `I`. -/
  exists_degree_le : ∀ p ∈ I, p ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p

/-- `G` is a **reduced Gröbner basis** of `I`: a Gröbner basis whose elements are monic and
in which no monomial of a member is divisible by the leading monomial of another member. -/
structure isReducedGrobnerBasis (G : List (MvPolynomial (Fin (2 * n)) K))
    (I : Ideal (MvPolynomial (Fin (2 * n)) K)) (m : MonomialOrder (Fin (2 * n))) : Prop
    extends isGrobnerBasis G I m where
  /-- Each member of a reduced basis is monic. -/
  monic : ∀ g ∈ G, m.leadingCoeff g = 1
  /-- No monomial of a member is divisible by the leading monomial of a different member. -/
  reduced : ∀ g ∈ G, ∀ d ∈ g.support, ∀ h ∈ G, h ≠ g → ¬ (m.degree h ≤ d)

variable {G : List (MvPolynomial (Fin (2 * n)) K)} {I : Ideal (MvPolynomial (Fin (2 * n)) K)}
  {m : MonomialOrder (Fin (2 * n))}

lemma isGrobnerBasis.mem_ideal (hG : isGrobnerBasis G I m) {g : MvPolynomial (Fin (2 * n)) K}
    (hg : g ∈ G) : g ∈ I := by
  rw [← hG.span_eq]
  exact Ideal.subset_span hg

lemma isReducedGrobnerBasis.ne_zero [Nontrivial K] (hG : isReducedGrobnerBasis G I m)
    {g : MvPolynomial (Fin (2 * n)) K} (hg : g ∈ G) : g ≠ 0 := by
  intro h
  have := hG.monic g hg
  rw [h, MonomialOrder.leadingCoeff_zero] at this
  exact zero_ne_one this

/-- The **Van den Essen shape**: the basis consists precisely of polynomials `xᵢ - qᵢ(y)`,
one for each variable `xᵢ`.  Reading off the `qᵢ` gives the inverse map. -/
structure hasVanDenEssenShape (G : List (MvPolynomial (Fin (2 * n)) K)) : Prop where
  /-- For every `i` the basis contains an element of the form `xᵢ - qᵢ(y)`. -/
  exists_component : ∀ i : Fin n, ∃ q : MvPolynomial (Fin n) K, (X (xv i) - rename yv q) ∈ G
  /-- Every element of the basis has this form. -/
  mem_form : ∀ h ∈ G, ∃ (i : Fin n) (q : MvPolynomial (Fin n) K), h = X (xv i) - rename yv q

open Classical in
/-- Read off the candidate inverse from a basis in Van den Essen shape. -/
noncomputable def extractInverse (G : List (MvPolynomial (Fin (2 * n)) K)) : PolyMap n K :=
  fun i =>
    if h : ∃ q : MvPolynomial (Fin n) K, (X (xv i) - rename yv q) ∈ G then h.choose else 0

lemma extractInverse_spec (hS : hasVanDenEssenShape G) (i : Fin n) :
    (X (xv i) - rename yv (extractInverse G i)) ∈ G := by
  have h := hS.exists_component i
  rw [extractInverse, dif_pos h]
  exact h.choose_spec

end GroebnerDefs

end VanDenEssen
