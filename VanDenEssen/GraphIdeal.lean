import RequestProject.VanDenEssen.Basic

/-!
# The graph ideal of a polynomial map

Van den Essen's algorithm works inside the polynomial ring in `2n` variables
`k[x₁,…,xₙ, y₁,…,yₙ]`.  We realise this as `MvPolynomial (Fin (2*n)) K`, where the
first `n` indices carry the `x`-variables (`xv`) and the last `n` the `y`-variables
(`yv`).

The *graph ideal* of a polynomial map `F` is
`I(F) = ⟨y₁ - F₁(x), …, yₙ - Fₙ(x)⟩`.
Geometrically it is the ideal of the graph `{(a, F a)}` of `F`.

The central algebraic fact, proved here, is that `I(F)` is exactly the kernel of the
substitution homomorphism
`ψ_F : k[x, y] → k[x]`, `xᵢ ↦ xᵢ`, `yᵢ ↦ Fᵢ(x)`.
Consequently `k[x,y]/I(F) ≅ k[x]`, so `I(F)` is a proper ideal, and membership of
particular polynomials in `I(F)` can be checked by a single substitution.  This is the
bridge that converts Gröbner-basis information about `I(F)` into statements about
inverses of `F`.
-/

namespace VanDenEssen

open MvPolynomial

section Variables

variable {n : Nat}

/-- The `i`-th `x`-variable index inside `Fin (2 * n)`. -/
def xv (i : Fin n) : Fin (2 * n) := ⟨i.val, by have := i.isLt; omega⟩

/-- The `i`-th `y`-variable index inside `Fin (2 * n)`. -/
def yv (i : Fin n) : Fin (2 * n) := ⟨n + i.val, by have := i.isLt; omega⟩

@[simp] lemma xv_val (i : Fin n) : (xv i).val = i.val := rfl
@[simp] lemma yv_val (i : Fin n) : (yv i).val = n + i.val := rfl

lemma xv_injective : Function.Injective (xv (n := n)) := by
  intro i j h
  have hv : (xv i).val = (xv j).val := by rw [h]
  simp only [xv_val] at hv
  exact Fin.ext hv

lemma yv_injective : Function.Injective (yv (n := n)) := by
  intro i j h
  have hv : (yv i).val = (yv j).val := by rw [h]
  simp only [yv_val] at hv
  exact Fin.ext (by omega)

lemma xv_ne_yv (i j : Fin n) : xv i ≠ yv j := by
  intro h
  have hv : (xv i).val = (yv j).val := by rw [h]
  simp only [xv_val, yv_val] at hv
  have := i.isLt
  omega

lemma xv_lt_yv (i j : Fin n) : xv i < yv j := by
  have := i.isLt
  rw [Fin.lt_def, xv_val, yv_val]
  omega

/-- Every index of `Fin (2 * n)` is either an `x`-index or a `y`-index. -/
def splitVar (k : Fin (2 * n)) : Fin n ⊕ Fin n :=
  if h : k.val < n then Sum.inl ⟨k.val, h⟩ else Sum.inr ⟨k.val - n, by have := k.isLt; omega⟩

@[simp] lemma splitVar_xv (i : Fin n) : splitVar (xv i) = Sum.inl i := by
  rw [splitVar, dif_pos (by simp only [xv_val]; exact i.isLt)]
  exact congrArg Sum.inl (Fin.ext rfl)

@[simp] lemma splitVar_yv (i : Fin n) : splitVar (yv i) = Sum.inr i := by
  have hi := i.isLt
  rw [splitVar, dif_neg (by simp only [yv_val]; omega)]
  exact congrArg Sum.inr (Fin.ext (by simp only [yv_val]; omega))

lemma sum_elim_splitVar (k : Fin (2 * n)) : Sum.elim xv yv (splitVar k) = k := by
  have hk := k.isLt
  rw [splitVar]
  split
  · next h => exact Fin.ext rfl
  · next h => exact Fin.ext (by simp only [yv_val, Sum.elim_inr]; omega)

/-- Case analysis on an index of `Fin (2 * n)`. -/
lemma xv_or_yv (k : Fin (2 * n)) : (∃ i, k = xv i) ∨ (∃ i, k = yv i) := by
  have h := sum_elim_splitVar k
  rcases hs : splitVar k with i | i
  · exact Or.inl ⟨i, by rw [hs] at h; exact h.symm⟩
  · exact Or.inr ⟨i, by rw [hs] at h; exact h.symm⟩

end Variables

section GraphIdeal

variable {n : Nat} {K : Type*} [CommRing K]

/-- The substitution `xᵢ ↦ xᵢ`, `yᵢ ↦ Fᵢ(x)` on the index set. -/
noncomputable def graphSubst (F : PolyMap n K) : Fin (2 * n) → MvPolynomial (Fin n) K :=
  fun k => Sum.elim X F (splitVar k)

/-- The substitution homomorphism `ψ_F : k[x, y] → k[x]` given by `xᵢ ↦ xᵢ`, `yᵢ ↦ Fᵢ(x)`. -/
noncomputable def graphHom (F : PolyMap n K) :
    MvPolynomial (Fin (2 * n)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (graphSubst F)

@[simp] lemma graphSubst_xv (F : PolyMap n K) (i : Fin n) : graphSubst F (xv i) = X i := by
  simp [graphSubst]

@[simp] lemma graphSubst_yv (F : PolyMap n K) (i : Fin n) : graphSubst F (yv i) = F i := by
  simp [graphSubst]

@[simp] lemma graphHom_X_xv (F : PolyMap n K) (i : Fin n) : graphHom F (X (xv i)) = X i := by
  simp [graphHom]

@[simp] lemma graphHom_X_yv (F : PolyMap n K) (i : Fin n) : graphHom F (X (yv i)) = F i := by
  simp [graphHom]

/-- `ψ_F` undoes the inclusion `k[x] ↪ k[x,y]`. -/
@[simp] lemma graphHom_rename_xv (F : PolyMap n K) (q : MvPolynomial (Fin n) K) :
    graphHom F (rename xv q) = q := by
  rw [graphHom, aeval_rename]
  have : (graphSubst F) ∘ (xv (n := n)) = X := by
    funext i; simp
  rw [this]
  exact aeval_X_left_apply q

/-- `ψ_F` evaluates a polynomial in the `y`-variables at `F`. -/
@[simp] lemma graphHom_rename_yv (F : PolyMap n K) (q : MvPolynomial (Fin n) K) :
    graphHom F (rename yv q) = aeval F q := by
  rw [graphHom, aeval_rename]
  have : (graphSubst F) ∘ (yv (n := n)) = F := by
    funext i; simp
  rw [this]

/-- The generators `yᵢ - Fᵢ(x)` of the graph ideal. -/
noncomputable def graphGen (F : PolyMap n K) (i : Fin n) : MvPolynomial (Fin (2 * n)) K :=
  X (yv i) - rename xv (F i)

/-- The **graph ideal** `I(F) = ⟨y₁ - F₁(x), …, yₙ - Fₙ(x)⟩ ⊆ k[x, y]`. -/
noncomputable def graphIdeal (F : PolyMap n K) : Ideal (MvPolynomial (Fin (2 * n)) K) :=
  Ideal.span (Set.range (graphGen F))

lemma graphGen_mem (F : PolyMap n K) (i : Fin n) : graphGen F i ∈ graphIdeal F :=
  Ideal.subset_span ⟨i, rfl⟩

/-- The "graph reduction" endomorphism `θ = (k[x] ↪ k[x,y]) ∘ ψ_F` of `k[x,y]`,
which replaces every `yᵢ` by `Fᵢ(x)`. -/
noncomputable def graphReduce (F : PolyMap n K) :
    MvPolynomial (Fin (2 * n)) K →ₐ[K] MvPolynomial (Fin (2 * n)) K :=
  (rename xv).comp (graphHom F)

lemma X_sub_graphReduce_mem (F : PolyMap n K) (k : Fin (2 * n)) :
    X k - graphReduce F (X k) ∈ graphIdeal F := by
  rcases xv_or_yv k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp only [graphReduce, AlgHom.comp_apply, graphHom_X_xv, rename_X, sub_self]
    exact Ideal.zero_mem _
  · have : graphReduce F (X (yv i)) = rename xv (F i) := by
      simp [graphReduce]
    rw [this]
    exact graphGen_mem F i

/-- Every polynomial is congruent modulo `I(F)` to its `y`-free reduction. -/
lemma sub_graphReduce_mem (F : PolyMap n K) (p : MvPolynomial (Fin (2 * n)) K) :
    p - graphReduce F p ∈ graphIdeal F := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [graphReduce]
  | add p q hp hq =>
      have : p + q - graphReduce F (p + q) = (p - graphReduce F p) + (q - graphReduce F q) := by
        rw [map_add]; ring
      rw [this]
      exact Ideal.add_mem _ hp hq
  | mul_X p k hp =>
      have hsplit : p * X k - graphReduce F (p * X k)
          = (p - graphReduce F p) * X k + graphReduce F p * (X k - graphReduce F (X k)) := by
        rw [map_mul]; ring
      rw [hsplit]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
        (Ideal.mul_mem_left _ _ (X_sub_graphReduce_mem F k))

/-- **Lemma 2 (Graph ideal = kernel of the substitution map).**
A polynomial lies in the graph ideal of `F` exactly when substituting `y := F(x)` kills it. -/
theorem mem_graphIdeal_iff (F : PolyMap n K) (p : MvPolynomial (Fin (2 * n)) K) :
    p ∈ graphIdeal F ↔ graphHom F p = 0 := by
  constructor
  · intro hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro q ⟨i, rfl⟩
      simp [graphGen]
    · simp
    · intro a b _ _ ha hb; simp [ha, hb]
    · intro a b _ hb; simp [hb]
  · intro hp
    have h := sub_graphReduce_mem F p
    have hz : graphReduce F p = 0 := by simp [graphReduce, hp]
    rwa [hz, sub_zero] at h

/-- The graph ideal is a proper ideal: `k[x,y]/I(F) ≅ k[x]` is nonzero. -/
theorem one_notMem_graphIdeal [Nontrivial K] (F : PolyMap n K) :
    (1 : MvPolynomial (Fin (2 * n)) K) ∉ graphIdeal F := by
  rw [mem_graphIdeal_iff]
  simp

theorem graphIdeal_ne_top [Nontrivial K] (F : PolyMap n K) : graphIdeal F ≠ ⊤ := by
  intro h
  exact one_notMem_graphIdeal F (h ▸ Submodule.mem_top)

/-! ### Dictionary between graph-ideal membership and inverses -/

/-- `xᵢ - qᵢ(y) ∈ I(F)` exactly says that the `i`-th component of `q ∘ F` is `xᵢ`. -/
theorem X_xv_sub_rename_yv_mem_graphIdeal_iff (F : PolyMap n K) (i : Fin n)
    (q : MvPolynomial (Fin n) K) :
    (X (xv i) - rename yv q) ∈ graphIdeal F ↔ aeval F q = X i := by
  rw [mem_graphIdeal_iff]
  simp only [map_sub, graphHom_X_xv, graphHom_rename_yv, sub_eq_zero]
  exact eq_comm

/-- A polynomial in the `y`-variables alone lies in `I(F)` iff it vanishes on substituting `F`. -/
theorem rename_yv_mem_graphIdeal_iff (F : PolyMap n K) (q : MvPolynomial (Fin n) K) :
    rename yv q ∈ graphIdeal F ↔ aeval F q = 0 := by
  rw [mem_graphIdeal_iff, graphHom_rename_yv]

/-- The family `(xᵢ - Gᵢ(y))ᵢ` lies in `I(F)` exactly when `G` is a left inverse of `F`. -/
theorem forall_X_xv_sub_mem_iff (F G : PolyMap n K) :
    (∀ i, (X (xv i) - rename yv (G i)) ∈ graphIdeal F) ↔ comp G F = idMap := by
  constructor
  · intro h
    funext i
    simpa using (X_xv_sub_rename_yv_mem_graphIdeal_iff F i (G i)).1 (h i)
  · intro h i
    rw [X_xv_sub_rename_yv_mem_graphIdeal_iff]
    simpa using congrFun h i

end GraphIdeal

end VanDenEssen
