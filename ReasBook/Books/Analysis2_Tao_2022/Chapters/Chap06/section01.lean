import Mathlib

section Chap06
section Section01

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The norm induced by a linear map `B : E → E*` via `x ↦ sqrt((Bx)(x))`. -/
noncomputable def inducedEuclideanNorm (B : E →ₗ[ℝ] Module.Dual ℝ E) (x : E) : ℝ :=
  Real.sqrt ((B x) x)

/-- A linear map `B : E → E*` is self-adjoint and positive definite. -/
structure IsSelfAdjointPositiveDefinite (B : E →ₗ[ℝ] Module.Dual ℝ E) : Prop where
  selfAdjoint : ∀ x y : E, (B x) y = (B y) x
  positiveDefinite : ∀ x : E, x ≠ 0 → 0 < (B x) x

/-- Predicate expressing convexity for an extended-real-valued function. -/
def IsConvexERealFunction (f : E → EReal) : Prop := sorry

/-- In statement form, an `EReal`-valued function models `ℝ ∪ {+∞}` and is proper convex. -/
structure IsProperConvex (f : E → EReal) : Prop where
  noNegInfinity : ∀ x : E, f x ≠ ⊥
  exists_ne_top : ∃ x : E, f x ≠ ⊤
  convex : IsConvexERealFunction (E := E) f

/-- Definition 6.1: Let `E` be a finite-dimensional real vector space and let
`B : E → E*` be self-adjoint and positive definite, with Euclidean norm
`x ↦ Real.sqrt ((B x) x)`. For a proper convex `f : E → ℝ ∪ {+∞}` (modeled as
`f : E → EReal` with no `-∞` values and not identically `+∞`), the Fenchel conjugate
`f_* : E* → ℝ ∪ {+∞}` is `f_*(s) = sup_{x ∈ E} ((s x) - f(x))`. -/
noncomputable def fenchelConjugate [FiniteDimensional ℝ E]
    (B : E →ₗ[ℝ] Module.Dual ℝ E)
    (_hB : IsSelfAdjointPositiveDefinite (E := E) B)
    (f : E → EReal)
    (_hf : IsProperConvex (E := E) f) :
    Module.Dual ℝ E → EReal :=
  fun s => sSup (Set.range (fun x : E => (s x : EReal) - f x))

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real-valued Fenchel conjugate, viewed in `EReal`. -/
noncomputable def realFenchelConjugate (f : E → ℝ) (s : E →L[ℝ] ℝ) : EReal :=
  sSup (Set.range (fun x : E => ((s x - f x : ℝ) : EReal)))

/-- The effective domain of the real-valued Fenchel conjugate. -/
def realFenchelConjugateDom (f : E → ℝ) : Set (E →L[ℝ] ℝ) :=
  {s : E →L[ℝ] ℝ | realFenchelConjugate (E := E) f s < ⊤}

/-- Proposition 6.1: Let `E` be a finite-dimensional real normed space, `f : E → ℝ`
be convex, and assume `f x ≤ f 0 + L * ‖x‖` for all `x` with `L ≥ 0`.
If `f_*` is the conjugate `f_*(s) = sup_x (⟪s, x⟫ - f x)`, then every
`s` in `dom f_*` satisfies `‖s‖ ≤ L`; in particular, `dom f_*` is bounded. -/
theorem dual_norm_le_of_mem_realFenchelConjugateDom_of_linear_growth
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (L : ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hL : 0 ≤ L)
    (hgrowth : ∀ x : E, f x ≤ f 0 + L * ‖x‖) :
    (∀ s : E →L[ℝ] ℝ, s ∈ realFenchelConjugateDom (E := E) f → ‖s‖ ≤ L) ∧
      ∃ R : ℝ, 0 ≤ R ∧
        ∀ s : E →L[ℝ] ℝ, s ∈ realFenchelConjugateDom (E := E) f → ‖s‖ ≤ R := sorry

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Fenchel conjugate of an `EReal`-valued function using the inner-product pairing. -/
noncomputable def innerFenchelConjugate (f : E → EReal) (g : E) : EReal :=
  sSup (Set.range (fun y : E => (inner ℝ g y : EReal) - f y))

/-- The effective domain of the Fenchel conjugate defined via the inner-product pairing. -/
def innerFenchelConjugateDom (f : E → EReal) : Set E :=
  {s : E | innerFenchelConjugate (E := E) f s < ⊤}

/-- The finite-real effective domain of the Fenchel conjugate. -/
def innerFenchelConjugateRealDom (f : E → EReal) : Set E :=
  {s : E | innerFenchelConjugate (E := E) f s ≠ ⊥ ∧
    innerFenchelConjugate (E := E) f s < ⊤}

/-- Example 6.1.1: For finitely many affine forms indexed by `ι` (equivalently
`j = 1, …, m`), define
`f(x) = max_j |⟪a_j, x⟫ - b_j|`, let `A u = ∑ j u_j • a_j`, and let
`φ(u) = ∑ j b_j u_j`.
Then `f` admits the `ℓ¹`-ball and simplex max/sup representations, and its
Fenchel conjugate is represented as the constrained infimum
`f_*(s) = inf {φ(u) | A u = s, ∑ j |u_j| ≤ 1}`. -/
theorem maxAbsAffineInner_eq_sup_l1Ball_and_simplex
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → E) (b : ι → ℝ) :
    let A : (ι → ℝ) → E := fun u => ∑ j, u j • a j
    let φ : (ι → ℝ) → ℝ := fun u => ∑ j, b j * u j
    let f : E → ℝ :=
      fun x => sSup (Set.range (fun j : ι => |inner ℝ (a j) x - b j|))
    (∀ x : E,
      f x =
        sSup (Set.range (fun u : {u : ι → ℝ // (∑ j, |u j|) ≤ (1 : ℝ)} =>
          inner ℝ (A u.1) x - φ u.1))) ∧
    (∀ x : E,
      f x =
        sSup (Set.range (fun u :
          {u : (ι → ℝ) × (ι → ℝ) //
            (∀ j : ι, 0 ≤ u.1 j) ∧
            (∀ j : ι, 0 ≤ u.2 j) ∧
            (∑ j, (u.1 j + u.2 j)) = (1 : ℝ)} =>
          inner ℝ (A (fun j => u.1.1 j - u.1.2 j)) x -
            φ (fun j => u.1.1 j - u.1.2 j)))) ∧
    (∀ s : E,
      innerFenchelConjugate (E := E) (fun x : E => ((f x : ℝ) : EReal)) s =
        sInf (Set.range (fun u : {u : ι → ℝ //
          A u = s ∧ (∑ j, |u j|) ≤ (1 : ℝ)} =>
          ((φ u.1 : ℝ) : EReal)))) := sorry

/-- Lemma 6.1.1: For a proper, closed, convex `f : E → ℝ ∪ {+∞}` with conjugate
`f_*(s) = sup_y (⟪s, y⟫ - f y)`, the biconjugate formula holds:
for every `x : E`, `f x` equals the supremum of
`s ↦ ⟪s, x⟫ - f_*(s)`. -/
theorem fenchel_biconjugate_eq_sSup_on_innerFenchelConjugateDom
    (f : E → EReal)
    (hf_proper_convex : IsProperConvex (E := E) f)
    (hf_closed : IsClosed {p : E × EReal | f p.1 ≤ p.2}) :
    ∀ x : E,
      f x = sSup (Set.range
        (fun s : E => (inner ℝ s x : EReal) - innerFenchelConjugate (E := E) f s)) := sorry

/-- `g` is a subgradient of `f` at `x` when the supporting-hyperplane inequality holds. -/
def IsSubgradientAt (f : E → EReal) (x g : E) : Prop :=
  ∀ y : E, f y ≥ f x + ((inner ℝ g (y - x) : ℝ) : EReal)

/-- Proposition 6.2: For a finite-dimensional real inner product space `E` and a proper
convex `f : E → ℝ ∪ {+∞}` with conjugate
`f_*(g) = sup_y (⟪g, y⟫ - f y)`, if `g ∈ ∂f(x)` then
`f(x) + f_*(g) = ⟪g, x⟫`; in particular, `x ∈ ∂f_*(g)`. -/
theorem fenchelYoung_eq_and_subgradient_conjugate_of_mem_subgradient
    (f : E → EReal) (hf : IsProperConvex (E := E) f) {x g : E}
    (hg : IsSubgradientAt (E := E) f x g) :
    f x + innerFenchelConjugate (E := E) f g = (inner ℝ g x : EReal) ∧
      IsSubgradientAt (E := E) (innerFenchelConjugate (E := E) f) g x := sorry

/-- The dual norm induced by a linear map representing `B⁻¹` via
`s ↦ sqrt(⟪s, B⁻¹ s⟫)`. -/
noncomputable def dualNormFromInverse
    (BInv : E →ₗ[ℝ] Module.Dual ℝ E) (s : E) : ℝ :=
  Real.sqrt ((BInv s) s)

/-- The image set of objective values used in the smooth-approximation supremum at `x`. -/
def smoothApproximationObjectiveSet
    (fStar : E → ℝ)
    (domfStar : Set E)
    (dualNorm : E → ℝ)
    (μ : NNReal)
    (x : E) : Set ℝ :=
  (fun s : E => inner ℝ s x - fStar s - ((1 / 2 : ℝ) * (μ : ℝ) * (dualNorm s) ^ 2)) '' domfStar

/-- Generic smooth-approximation formula built from real-valued Fenchel data
`(f_*, dom f_*, ‖·‖*)`, using a supremum over `dom f_*`. -/
noncomputable def smoothApproximationFromFenchelData
    (fStar : E → ℝ)
    (domfStar : Set E)
    (dualNorm : E → ℝ)
    (μ : NNReal)
    (x : E) : ℝ :=
  sSup (smoothApproximationObjectiveSet (E := E) fStar domfStar dualNorm μ x)

/-- Auxiliary extended-real smooth-approximation formula over `dom f_*`. -/
noncomputable def smoothApproximationEReal
    (f : E → EReal)
    (BInv : E →ₗ[ℝ] Module.Dual ℝ E)
    (μ : NNReal)
    (x : E) : EReal :=
  sSup (Set.range (fun s : {s : E // s ∈ innerFenchelConjugateDom (E := E) f} =>
    (inner ℝ s.1 x : EReal)
      - innerFenchelConjugate (E := E) f s.1
      - ((((1 / 2 : ℝ) * (μ : ℝ) * (dualNormFromInverse (E := E) BInv s.1) ^ 2) : ℝ) : EReal)))

/-- Definition 6.2: Let `f : E → ℝ ∪ {+∞}` be proper, closed, and convex, with
Fenchel conjugate `f_*`. For `μ ≥ 0`, define the smooth approximation by
`f_μ(x) = sup_{s ∈ dom f_*} (⟪s, x⟫ - f_*(s) - (1/2) μ ‖s‖*^2)`, where
`‖s‖* = sqrt((B⁻¹ s) s)`. This is encoded as a real-valued supremum over
the finite-real effective domain of `f_*`
`innerFenchelConjugateRealDom f`, so `f_*(s)` is represented by `.toReal`; under
standard attainment hypotheses, this
supremum agrees with the textbook `max`. -/
noncomputable def smoothApproximation
    (f : E → EReal)
    (BInv : E →ₗ[ℝ] Module.Dual ℝ E)
    (μ : NNReal)
    (x : E) : ℝ :=
  sSup (smoothApproximationObjectiveSet (E := E)
    (fun s : E => (innerFenchelConjugate (E := E) f s).toReal)
    (innerFenchelConjugateRealDom (E := E) f)
    (dualNormFromInverse (E := E) BInv)
    μ x)

/-- For proper closed convex data, the auxiliary extended-real smoothing value is finite. -/
theorem smoothApproximationEReal_ne_top_ne_bot_of_proper_closed_convex
    (f : E → EReal)
    (hf_proper_convex : IsProperConvex (E := E) f)
    (hf_closed : IsClosed {p : E × EReal | f p.1 ≤ p.2})
    (BInv : E →ₗ[ℝ] Module.Dual ℝ E)
    (μ : NNReal)
    (x : E) :
    smoothApproximationEReal (E := E) f BInv μ x ≠ ⊤ ∧
      smoothApproximationEReal (E := E) f BInv μ x ≠ ⊥ := sorry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Uniform-ball smoothing of a function, defined as expectation under a random vector
uniformly distributed on the unit Euclidean ball. -/
noncomputable def uniformBallSmoothing (f : F → ℝ) (μ : ℝ) : F → ℝ := sorry

/-- Lemma 6.1.2: Let `F` be a finite-dimensional real normed space, with dual norm on
`F →L[ℝ] ℝ` given by the standard operator norm. Assume a fixed inner-product
structure only to define the uniform-ball smoothing
`f_μ(x) = 𝔼[f (x + μU)]`. If `f : F → ℝ` is convex and `1`-Lipschitz with respect to
`‖·‖`, then for `μ > 0` the smoothing is differentiable, and the derivative map is
`(1 / μ)`-Lipschitz in the operator norm. -/
theorem gradient_lipschitz_of_uniformBallSmoothing_of_convex_lipschitz
    (f : F → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lipschitz : ∀ x y : F, |f x - f y| ≤ ‖x - y‖)
    {μ : ℝ} (hμ : 0 < μ) :
    Differentiable ℝ (uniformBallSmoothing (F := F) f μ) ∧
      ∀ x₁ x₂ : F,
        ‖fderiv ℝ (uniformBallSmoothing (F := F) f μ) x₁ -
            fderiv ℝ (uniformBallSmoothing (F := F) f μ) x₂‖ ≤
          (1 / μ) * ‖x₁ - x₂‖ := sorry

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  [FiniteDimensional ℝ E₂]

/-- Definition 6.3: For a linear operator `A : E₁ → (E₂ →L[ℝ] ℝ)`, define
`‖A‖_{1,2}` as the supremum of the pairings `(A x) u` over all unit vectors
`x : E₁` and `u : E₂`. In finite-dimensional spaces this equals the stated maximum. -/
noncomputable def operatorNormOneTwo
    (A : E₁ →ₗ[ℝ] (E₂ →L[ℝ] ℝ)) : ℝ :=
  sSup {r : ℝ | ∃ x : E₁, ∃ u : E₂, ‖x‖ = (1 : ℝ) ∧ ‖u‖ = (1 : ℝ) ∧ r = (A x) u}

/-- In finite dimensions, the supremum in `operatorNormOneTwo` is attained on unit vectors. -/
theorem operatorNormOneTwo_exists_unit_attainer
    (A : E₁ →ₗ[ℝ] (E₂ →L[ℝ] ℝ)) :
    ∃ x : E₁, ∃ u : E₂,
      ‖x‖ = (1 : ℝ) ∧ ‖u‖ = (1 : ℝ) ∧ operatorNormOneTwo (E₁ := E₁) (E₂ := E₂) A = (A x) u := sorry

/-- Proposition 6.3: Let `A : E₁ → E₂*` be linear and let `AAdj : E₂ → E₁*` satisfy
`⟪A x, u⟫ = ⟪x, AAdj u⟫` for all `x` and `u` (encoded by `hAdj : (A x) u = (AAdj u) x`).
Then the two operator norms are equal; each is attained on a unit vector; and for all
`x : E₁` and `u : E₂` one has `‖A x‖ ≤ ‖A‖ ‖x‖` and `‖AAdj u‖ ≤ ‖A‖ ‖u‖`. -/
theorem operatorNorm_eq_adjointOperatorNorm_and_bounds
    (A : E₁ →L[ℝ] (E₂ →L[ℝ] ℝ))
    (AAdj : E₂ →L[ℝ] (E₁ →L[ℝ] ℝ))
    (hAdj : ∀ x : E₁, ∀ u : E₂, (A x) u = (AAdj u) x) :
    ‖A‖ = ‖AAdj‖ ∧
      (∃ x : E₁, ‖x‖ = (1 : ℝ) ∧ ‖A x‖ = ‖A‖) ∧
      (∃ u : E₂, ‖u‖ = (1 : ℝ) ∧ ‖AAdj u‖ = ‖AAdj‖) ∧
      (∀ x : E₁, ‖A x‖ ≤ ‖A‖ * ‖x‖) ∧
      (∀ u : E₂, ‖AAdj u‖ ≤ ‖A‖ * ‖u‖) := sorry

/-- Data for a primal convex minimization problem: a nonempty closed bounded convex
feasible set and an objective defined on that feasible set. -/
structure PrimalConvexMinimizationProblem (E₁ : Type*) [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] where
  Q₁ : Set E₁
  hne : Q₁.Nonempty
  hclosed : IsClosed Q₁
  hbounded : Bornology.IsBounded Q₁
  hconvex : Convex ℝ Q₁
  f : E₁ → ℝ
  hcont : ContinuousOn f Q₁
  hfconvex : ConvexOn ℝ Q₁ f

/-- Definition 6.4 [Primal convex minimization problem]: for feasible set `Q₁` and
continuous convex objective `f`, define the primal optimal value corresponding to
`min_{x ∈ Q₁} f(x)` by taking the infimum over objective values on `Q₁`. -/
noncomputable def primalOptimalValue
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    (P : PrimalConvexMinimizationProblem E₁) : ℝ :=
  sInf (P.f '' P.Q₁)

/-- Under the definition's assumptions, the primal optimal value is attained. -/
theorem exists_primalOptimalValue_eq
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    (P : PrimalConvexMinimizationProblem E₁) :
    ∃ x ∈ P.Q₁, primalOptimalValue P = P.f x := sorry

/-- Data and regularity assumptions used to define a structured objective model. -/
structure StructuredObjectiveModelData (E₁ E₂ : Type*)
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] where
  Q₁ : Set E₁
  hQ₁_nonempty : Q₁.Nonempty
  hQ₁_bounded : Bornology.IsBounded Q₁
  hQ₁_closed : IsClosed Q₁
  hQ₁_convex : Convex ℝ Q₁
  Q₂ : Set E₂
  hQ₂_nonempty : Q₂.Nonempty
  hQ₂_bounded : Bornology.IsBounded Q₂
  hQ₂_closed : IsClosed Q₂
  hQ₂_convex : Convex ℝ Q₂
  fHat : E₁ → ℝ
  hfHat_cont : ContinuousOn fHat Q₁
  hfHat_convex : ConvexOn ℝ Q₁ fHat
  φHat : E₂ → ℝ
  hφHat_cont : ContinuousOn φHat Q₂
  hφHat_convex : ConvexOn ℝ Q₂ φHat
  A : E₁ →L[ℝ] (E₂ →L[ℝ] ℝ)

/-- Definition 6.5 [Structured objective model]: let `Q₁ ⊆ E₁` and `Q₂ ⊆ E₂` be bounded
closed convex sets in finite-dimensional real spaces, let `fHat : E₁ → ℝ` and
`φHat : E₂ → ℝ` be continuous convex on `Q₁` and `Q₂`, and let `A : E₁ → E₂*` be linear.
For `x ∈ Q₁`, define
`f(x) = fHat x + sup_{u ∈ Q₂} ((A x) u - φHat u)`, which matches the textbook maximum
since bounded closed subsets are compact in finite dimensions. -/
noncomputable def structuredObjectiveModel
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (M : StructuredObjectiveModelData E₁ E₂) :
    M.Q₁ → ℝ :=
  fun x =>
    M.fHat x.1 + sSup ((fun u : E₂ => (M.A x.1) u - M.φHat u) '' M.Q₂)

/-- The saddle function (6.u50) on `Q₁ × Q₂`:
`Ψ(x, u) = fHat x + (A x) u - φHat u`, where `(A x) u` is the model's
dual pairing corresponding to `⟨A x, u⟩_{E₂}`. -/
noncomputable def saddleFunction
    (M : StructuredObjectiveModelData E₁ E₂) :
    M.Q₁ → M.Q₂ → ℝ :=
  fun x u => M.fHat x.1 + (M.A x.1) u.1 - M.φHat u.1

/-- The primal saddle-point value for (6.u51), modeled as
`inf_{x ∈ Q₁} sup_{u ∈ Q₂} Ψ(x, u)` in `ℝ`; this `inf/sup` form records the
book's `min/max`, with attainment handled separately. -/
noncomputable def primalSaddleOptimalValue
    (M : StructuredObjectiveModelData E₁ E₂) : ℝ :=
  sInf (Set.range (fun x : M.Q₁ =>
    sSup (Set.range (fun u : M.Q₂ => saddleFunction M x u))))

/-- The adjoint objective (6.u52):
`φ(u) = -φHat u + inf_{x ∈ Q₁} ((A x) u + fHat x)` for `u ∈ Q₂`, where
`inf` records the corresponding minimization value. -/
noncomputable def adjointObjective
    (M : StructuredObjectiveModelData E₁ E₂) :
    M.Q₂ → ℝ :=
  fun u => -M.φHat u.1 +
    sInf (Set.range (fun x : M.Q₁ => (M.A x.1) u.1 + M.fHat x.1))

/-- The adjoint optimal value (6.u53), written as
`sup_{u ∈ Q₂} φ(u)` in `ℝ`, representing the corresponding maximum value. -/
noncomputable def adjointOptimalValue
    (M : StructuredObjectiveModelData E₁ E₂) : ℝ :=
  sSup (Set.range (fun u : M.Q₂ => adjointObjective M u))

/-- The primal optimal value `f^*` for the structured model from Definition 6.5,
written as the infimum of the structured objective over `Q₁`. -/
noncomputable def primalOptimalValueFromStructuredModel
    (M : StructuredObjectiveModelData E₁ E₂) : ℝ :=
  sInf (Set.range (fun x : M.Q₁ => structuredObjectiveModel M x))

/-- Components of the saddle-point/adjoint reformulation data. -/
structure SaddleAdjointReformulationData (M : StructuredObjectiveModelData E₁ E₂) where
  Ψ : M.Q₁ → M.Q₂ → ℝ
  primalSaddleExpr : ℝ
  φ : M.Q₂ → ℝ
  fStar : ℝ

/-- Definition 6.6 [Saddle-point reformulation and adjoint problem]:
define (6.u50) `Ψ(x, u) = fHat x + (A x) u - φHat u` on `Q₁ × Q₂`;
define (6.u51) the primal saddle expression
`inf_{x ∈ Q₁} sup_{u ∈ Q₂} Ψ(x, u)`;
define (6.u52) `φ(u) = -φHat u + inf_{x ∈ Q₁} ((A x) u + fHat x)`;
and define (6.u53) `f_* = sup_{u ∈ Q₂} φ(u)`.
Here `(A x) u` denotes the model's dual pairing for `⟨A x, u⟩_{E₂}`. -/
noncomputable def saddleAdjointReformulation
    (M : StructuredObjectiveModelData E₁ E₂) :
    SaddleAdjointReformulationData M :=
  { Ψ := saddleFunction M
    primalSaddleExpr := primalSaddleOptimalValue M
    φ := adjointObjective M
    fStar := adjointOptimalValue M }

/-- A prox-function on `Q₂` is differentiable and `1`-strongly convex on `Q₂`. -/
structure IsProxFunctionOn
    (Q₂ : Set E₂) (d₂ : E₂ → ℝ) : Prop where
  differentiableOn : DifferentiableOn ℝ d₂ Q₂
  stronglyConvexOn : StrongConvexOn Q₂ 1 d₂

/-- A prox-center is a minimizer of `d₂` on `Q₂` with normalized value `0`. -/
structure IsProxCenterOn
    (Q₂ : Set E₂) (d₂ : E₂ → ℝ) (ν₀ : E₂) : Prop where
  mem : ν₀ ∈ Q₂
  isMinOn : IsMinOn d₂ Q₂ ν₀
  value_eq_zero : d₂ ν₀ = 0

/-- Definition 6.7 [Smoothing via a prox-function]: for structured-model data `M`,
`d₂ : E₂ → ℝ` a prox-function on `Q₂`, prox-center `ν₀` with `d₂(ν₀) = 0`, and
`μ > 0`, define the smoothed approximation by
`f_μ(x) = max_{u ∈ Q₂} ((A x) u - φHat u - μ d₂ u)` for `x ∈ Q₁`, and choose
`u_μ(x)` as any maximizer in this definition. -/
structure ProxSmoothedApproximationData
    (M : StructuredObjectiveModelData E₁ E₂) where
  d₂ : E₂ → ℝ
  proxFunction : IsProxFunctionOn M.Q₂ d₂
  ν₀ : E₂
  proxCenter : IsProxCenterOn M.Q₂ d₂ ν₀
  μ : ℝ
  μ_pos : 0 < μ
  fμ : M.Q₁ → ℝ
  fμ_eq : ∀ x : M.Q₁,
    fμ x = sSup (Set.range (fun u : M.Q₂ =>
      (M.A x.1) u.1 - M.φHat u.1 - μ * d₂ u.1))
  uμ : M.Q₁ → M.Q₂
  uμ_isMaximizer : ∀ x : M.Q₁,
    IsGreatest (Set.range (fun u : M.Q₂ =>
      (M.A x.1) u.1 - M.φHat u.1 - μ * d₂ u.1))
      ((M.A x.1) (uμ x).1 - M.φHat (uμ x).1 - μ * d₂ (uμ x).1)

/-- The primal optimal value from Definition 6.5 equals the saddle expression
from (6.u51). -/
theorem primalOptimalValueFromStructuredModel_eq_primalSaddleOptimalValue
    (M : StructuredObjectiveModelData E₁ E₂) :
    primalOptimalValueFromStructuredModel M = primalSaddleOptimalValue M := sorry

/-- Proposition 6.4 [Weak duality for the structured model]:
for nonempty sets `Q₁` and `Q₂` and `Ψ : Q₁ × Q₂ → ℝ` (encoded as `Ψ : α → β → ℝ`),
assume each inner extremum exists,
`f^* = min_{x ∈ Q₁} max_{u ∈ Q₂} Ψ(x,u)` is attained,
and `f_* = max_{u ∈ Q₂} min_{x ∈ Q₁} Ψ(x,u)` is attained.
Then `f^* ≥ f_*`, equivalently
`min_{x ∈ Q₁} max_{u ∈ Q₂} Ψ(x,u) ≥ max_{u ∈ Q₂} min_{x ∈ Q₁} Ψ(x,u)`. -/
theorem weakDuality_minimax_structuredModel
    {α β : Type*}
    (Q₁ : Set α) (Q₂ : Set β)
    (hQ₁ : Q₁.Nonempty) (hQ₂ : Q₂.Nonempty)
    (Ψ : α → β → ℝ)
    (fStar fSub : ℝ)
    (hinnerMax : ∀ x ∈ Q₁, ∃ m : ℝ, IsGreatest ((fun u : β => Ψ x u) '' Q₂) m)
    (hinnerMin : ∀ u ∈ Q₂, ∃ m : ℝ, IsLeast ((fun x : α => Ψ x u) '' Q₁) m)
    (hfStar : IsLeast ((fun x : α => sSup ((fun u : β => Ψ x u) '' Q₂)) '' Q₁) fStar)
    (hfSub : IsGreatest ((fun u : β => sInf ((fun x : α => Ψ x u) '' Q₁)) '' Q₂) fSub) :
    fStar ≥ fSub := sorry

/-- Proposition 6.5 [Quadratic lower bound induced by the prox-center]:
let `Q₂ ⊆ E₂` be convex, and let `d₂ : E₂ → ℝ` be differentiable and
`1`-strongly convex on `Q₂`, i.e. for all `u, v ∈ Q₂`,
`d₂ v ≥ d₂ u + (fderivWithin ℝ d₂ Q₂ u) (v - u) + (1/2) * ‖v - u‖^2`.
If `u₀` is a minimizer of `d₂` on `Q₂` with
`d₂ u₀ = 0`, then for every `u ∈ Q₂` one has
`d₂ u ≥ (1/2) * ‖u - u₀‖^2`. -/
theorem proxCenter_quadraticLowerBound
    (Q₂ : Set E₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (d₂ : E₂ → ℝ)
    (hd₂_differentiableOn : DifferentiableOn ℝ d₂ Q₂)
    (hd₂_firstOrderStrongConvexOn : ∀ u ∈ Q₂, ∀ v ∈ Q₂,
      d₂ v ≥ d₂ u + (fderivWithin ℝ d₂ Q₂ u) (v - u) +
        (1 / 2 : ℝ) * ‖v - u‖ ^ (2 : ℕ))
    (u₀ : E₂)
    (hu₀_isMinOn : IsMinOn d₂ Q₂ u₀)
    (hd₂_u₀_eq_zero : d₂ u₀ = 0) :
    ∀ u ∈ Q₂, d₂ u ≥ (1 / 2 : ℝ) * ‖u - u₀‖ ^ (2 : ℕ) := sorry

/-- Predicate for convexity of an extended-real-valued function restricted to a set. -/
def IsConvexOnERealFunction (Q : Set E₂) (f : E₂ → EReal) : Prop := sorry

/-- Proposition 6.6 [Uniqueness of the smoothed maximizer]: assume `Q₂` is nonempty
and convex, `d₂ : E₂ → ℝ` is `1`-strongly convex on `Q₂`, `μ > 0`, `φHat` is convex
on `Q₂` as an extended-real-valued function (`ℝ ∪ {+∞}`), and `A : E₁ → E₂*` is linear.
For fixed `x ∈ Q₁`, if the maximization problem
`max_{u ∈ Q₂} ((A x) u - φHat u - μ d₂ u)` has an optimal solution, then this
optimal solution is unique; equivalently, whenever the maximizer exists, `u_μ(x)`
is uniquely defined. -/
theorem smoothedMaximizer_unique_of_exists
    (Q₁ : Set E₁)
    (Q₂ : Set E₂)
    (hQ₂_nonempty : Q₂.Nonempty)
    (hQ₂_convex : Convex ℝ Q₂)
    (d₂ : E₂ → ℝ)
    (hd₂_stronglyConvex : StrongConvexOn Q₂ (1 : ℝ) d₂)
    (μ : ℝ)
    (hμ : 0 < μ)
    (φHat : E₂ → EReal)
    (hφHat_noNegInfinity : ∀ u ∈ Q₂, φHat u ≠ ⊥)
    (hφHat_convex : IsConvexOnERealFunction (E₂ := E₂) Q₂ φHat)
    (A : E₁ →ₗ[ℝ] Module.Dual ℝ E₂)
    (x : E₁)
    (hx : x ∈ Q₁) :
    (∃ u : E₂, u ∈ Q₂ ∧
      ∀ v ∈ Q₂,
        ((A x) v : EReal) - φHat v - (μ * d₂ v : EReal) ≤
          ((A x) u : EReal) - φHat u - (μ * d₂ u : EReal)) →
    ∃! u : E₂, u ∈ Q₂ ∧
      ∀ v ∈ Q₂,
        ((A x) v : EReal) - φHat v - (μ * d₂ v : EReal) ≤
          ((A x) u : EReal) - φHat u - (μ * d₂ u : EReal) := sorry

end Section01
end Chap06
