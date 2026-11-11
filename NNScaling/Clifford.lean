import NNScaling.Foundations

/-!
# 0B. Nonstandard Clifford Analysis Foundations

This module extends {lit}`NNScaling.Foundations` to **Nonstandard Clifford Analysis**, combining
Robinson's hyperreal valuation ring $`\mathbb{L} \subset {}^*\mathbb{R}` with Mathlib's
{name}`CliffordAlgebra` over standard ($`\mathbb{R}`), limited ($`\mathbb{L}`), and full hyperreal
($`\mathbb{R}^*`) scalar rings.

It establishes four foundational pillars used across Stage 2 of the monograph:

1. **Valuation Subring and Infinitesimal Ideal**: The limited hyperreals form a commutative subring
   {lit}`LimitedSubring` ($`\mathbb{L} \subset \mathbb{R}^*`), the infinitesimals form an ideal
   {lit}`InfinitesimalIdeal` ($`\mathbb{I} \triangleleft \mathbb{L}`), and the standard-part map packages
   into a surjective ring homomorphism {lit}`stRingHom` ($`\operatorname{st} : \mathbb{L} \to \mathbb{R}`)
   with exact kernel $`\mathbb{I}`.
2. **Geometric Product, Unit Bivectors, and Spinor Rotors**: Over any commutative ring $`R` (including
   $`\mathbb{R}`, $`\mathbb{L}`, and $`\mathbb{R}^*`), orthogonal unit vectors $`e_1, e_2` generate a unit
   bivector $`\hat{B} = e_1 e_2` satisfying $`\hat{B}^{\sim} = -\hat{B}` and $`\hat{B}^2 = -1`, giving
   both the Cho–Saul half-angle/full-angle rotor sandwich and the $`\operatorname{Spin}(m)` eigenframe
   repulsion sign in Geometric Dyson Brownian Motion.
3. **Versor Reflections and Hestenes Left Contractions**: Exact algebraic identities for Householder
   versor actions $`u x u` and the graded Leibniz rule for {name}`CliffordAlgebra.contractLeft`,
   underpinning coordinate-free blade projections in Gaussian conditioning and double descent.
4. **Standard-Part Homomorphism on Hyperreal Clifford Algebras**: Lifting {lit}`stRingHom` via
   {name}`CliffordAlgebra.lift` produces a canonical ring homomorphism {lit}`stCliffordHom`
   ($`\operatorname{st}_{\mathcal{C}\ell} : \mathcal{C}\ell_n(\mathbb{L}) \to \mathcal{C}\ell_n(\mathbb{R})`)
   that commutes with the full geometric product and annihilates infinitesimal scalars and vectors.
-/

noncomputable section

namespace NNScaling

open scoped Hyperreal
open BigOperators

section ValuationRing

/-- The valuation subring $`\mathbb{L} \subset \mathbb{R}^*` of limited hyperreals. -/
def LimitedSubring : Subring ℝ* where
  carrier := {x : ℝ* | Limited x}
  mul_mem' hx hy := hx.mul hy
  one_mem' := limited_one
  add_mem' hx hy := hx.add hy
  zero_mem' := limited_zero
  neg_mem' hx := hx.neg

@[simp]
theorem mem_limitedSubring_iff {x : ℝ*} : x ∈ LimitedSubring ↔ Limited x := Iff.rfl

/-- Canonical embedding of a standard real $`r \in \mathbb{R}` into $`\mathbb{L}`. -/
def coeLimited (r : ℝ) : LimitedSubring := ⟨(r : ℝ*), limited_coe r⟩

@[simp]
theorem coe_coeLimited (r : ℝ) : ((coeLimited r : LimitedSubring) : ℝ*) = (r : ℝ*) := rfl

/-- The maximal ideal $`\mathbb{I} \triangleleft \mathbb{L}` of infinitesimal hyperreals. -/
def InfinitesimalIdeal : Ideal LimitedSubring where
  carrier := {x : LimitedSubring | IsInfinitesimal (x : ℝ*)}
  add_mem' hx hy := hx.add hy
  zero_mem' := isInfinitesimal_zero
  smul_mem' c _ hx := c.2.mul_isInfinitesimal hx

@[simp]
theorem mem_infinitesimalIdeal_iff {x : LimitedSubring} :
    x ∈ InfinitesimalIdeal ↔ IsInfinitesimal (x : ℝ*) := Iff.rfl

/-- The standard-part map packaged as a ring homomorphism $`\operatorname{st} : \mathbb{L} \to \mathbb{R}`. -/
def stRingHom : LimitedSubring →+* ℝ where
  toFun x := st (x : ℝ*)
  map_one' := st_one
  map_mul' x y := st_mul x.2 y.2
  map_zero' := st_zero
  map_add' x y := st_add x.2 y.2

@[simp]
theorem stRingHom_apply (x : LimitedSubring) : stRingHom x = st (x : ℝ*) := rfl

@[simp]
theorem stRingHom_coeLimited (r : ℝ) : stRingHom (coeLimited r) = r := st_coe r

/-- Surjectivity of $`\operatorname{st} : \mathbb{L} \to \mathbb{R}`. -/
theorem stRingHom_surjective : Function.Surjective stRingHom :=
  fun r => ⟨coeLimited r, stRingHom_coeLimited r⟩

/-- A limited hyperreal has zero shadow if and only if it is infinitesimal:
$`\ker(\operatorname{st}) = \mathbb{I}`. -/
theorem ker_stRingHom : RingHom.ker stRingHom = InfinitesimalIdeal := by
  ext x
  rw [RingHom.mem_ker, stRingHom_apply, mem_infinitesimalIdeal_iff]
  constructor
  · intro hst
    have hclose : (x : ℝ*) ≊ ((st (x : ℝ*) : ℝ) : ℝ*) := x.2.infClose_st
    rw [hst, Hyperreal.coe_zero, InfClose, sub_zero] at hclose
    exact hclose
  · exact IsInfinitesimal.st_eq_zero

end ValuationRing

section CliffordIdentities

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Fundamental Clifford vector-square law $`v^2 = Q(v) \cdot 1`, used for $`\xi_\ell^2 = \|\xi_\ell\|^2`
in hyperfinite variance recursions. -/
theorem clifford_vec_sq (Q : QuadraticForm R M) (v : M) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v = algebraMap R _ (Q v) :=
  CliffordAlgebra.ι_sq_scalar Q v

/-- Symmetric part of the geometric product of two vectors:
$`u v + v u = \operatorname{polar}_Q(u, v) \cdot 1`. -/
theorem clifford_symm_polar (Q : QuadraticForm R M) (u v : M) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v +
      CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u =
    algebraMap R _ (QuadraticMap.polar Q u v) :=
  CliffordAlgebra.ι_mul_ι_add_swap u v

/-- Orthogonal vectors anticommute in $`\mathcal{C}\ell(Q)`: $`u v = - v u`. -/
theorem clifford_ortho_anticomm {Q : QuadraticForm R M} {u v : M} (h : Q.IsOrtho u v) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v =
      -(CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h

/-- Reversion negates any orthogonal 2-blade (bivector):
$`(e_1 e_2)^{\sim} = e_2 e_1 = - e_1 e_2`. -/
theorem bivector_reverse_neg {Q : QuadraticForm R M} {e₁ e₂ : M} (h : Q.IsOrtho e₁ e₂) :
    CliffordAlgebra.reverse (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) =
      -(CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) := by
  rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_ι]
  rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h, neg_neg]

/-- Every unit orthogonal bivector $`\hat{B} = e_1 e_2` satisfies $`\hat{B}^2 = -1`, providing the
geometric imaginary unit behind Cho–Saul ReLU kernels, $`\mathcal{C}\ell_2^+` Cauchy–Dirac Stieltjes
transforms, and $`\operatorname{Spin}(m)` Dyson eigenvalue repulsion. -/
theorem unit_bivector_sq_neg_one {Q : QuadraticForm R M} {e₁ e₂ : M}
    (he₁ : Q e₁ = 1) (he₂ : Q e₂ = 1) (h : Q.IsOrtho e₁ e₂) :
    (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) *
      (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) = -1 := by
  calc
    (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) *
        (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂)
      = (-(CliffordAlgebra.ι Q e₂ * CliffordAlgebra.ι Q e₁)) *
          (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) :=
          congrArg (· * (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂))
            (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h)
    _ = -(CliffordAlgebra.ι Q e₂ *
          (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₁) *
          CliffordAlgebra.ι Q e₂) := by
          simp only [neg_mul, mul_assoc]
    _ = -(CliffordAlgebra.ι Q e₂ * algebraMap R _ (Q e₁) * CliffordAlgebra.ι Q e₂) := by
          rw [CliffordAlgebra.ι_sq_scalar]
    _ = -(CliffordAlgebra.ι Q e₂ * CliffordAlgebra.ι Q e₂) := by
          rw [he₁, map_one, mul_one]
    _ = -1 := by
          rw [CliffordAlgebra.ι_sq_scalar, he₂, map_one]

/-- Planar even-grade rotor $`R = c + s \, e_1 e_2 \in \mathcal{C}\ell^+(Q)`. -/
def planarRotor (Q : QuadraticForm R M) (e₁ e₂ : M) (c s : R) : CliffordAlgebra Q :=
  c • (1 : CliffordAlgebra Q) + s • (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂)

/-- Reversion of a planar rotor flips the bivector sign:
$`(c + s \, e_1 e_2)^{\sim} = c - s \, e_1 e_2`. -/
theorem planarRotor_reverse {Q : QuadraticForm R M} {e₁ e₂ : M}
    (h : Q.IsOrtho e₁ e₂) (c s : R) :
    CliffordAlgebra.reverse (planarRotor Q e₁ e₂ c s) =
      c • (1 : CliffordAlgebra Q) - s • (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) := by
  simp [planarRotor, bivector_reverse_neg h, sub_eq_add_neg]

/-- Spinor norm of a planar rotor: $`R R^{\sim} = (c^2 + s^2) \cdot 1`. -/
theorem planarRotor_mul_reverse {Q : QuadraticForm R M} {e₁ e₂ : M}
    (he₁ : Q e₁ = 1) (he₂ : Q e₂ = 1) (h : Q.IsOrtho e₁ e₂) (c s : R) :
    planarRotor Q e₁ e₂ c s * CliffordAlgebra.reverse (planarRotor Q e₁ e₂ c s) =
      (c ^ 2 + s ^ 2) • (1 : CliffordAlgebra Q) := by
  rw [planarRotor_reverse h, planarRotor]
  set B : CliffordAlgebra Q := CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂
  have hB2 : B * B = -1 := unit_bivector_sq_neg_one he₁ he₂ h
  have hcomm : (s • B) * (c • (1 : CliffordAlgebra Q)) = (c * s) • B := by
    rw [smul_mul_smul_comm, mul_one, mul_comm]
  calc
    (c • (1 : CliffordAlgebra Q) + s • B) * (c • (1 : CliffordAlgebra Q) - s • B)
      = (c * c) • (1 : CliffordAlgebra Q) - (c * s) • B +
          (s • B) * (c • (1 : CliffordAlgebra Q)) - (s * s) • (B * B) := by
          simp only [add_mul, mul_sub, smul_mul_smul_comm, mul_one, one_mul]
          abel
    _ = (c ^ 2 + s ^ 2) • (1 : CliffordAlgebra Q) := by
          rw [hcomm, sub_add_cancel, hB2, smul_neg, sub_neg_eq_add, sq, sq, add_smul]

/-- When $`c^2 + s^2 = 1` (e.g., $`c = \cos(\theta/2), s = \sin(\theta/2)`), the planar rotor
satisfies the unit spinor normalization $`R R^{\sim} = 1`. -/
theorem planarRotor_unit_norm {Q : QuadraticForm R M} {e₁ e₂ : M}
    (he₁ : Q e₁ = 1) (he₂ : Q e₂ = 1) (h : Q.IsOrtho e₁ e₂) {c s : R}
    (hcs : c ^ 2 + s ^ 2 = 1) :
    planarRotor Q e₁ e₂ c s * CliffordAlgebra.reverse (planarRotor Q e₁ e₂ c s) = 1 := by
  rw [planarRotor_mul_reverse he₁ he₂ h, hcs, one_smul]

/-- Two-sided spinor sandwich action on $`e_1`:
$`(c + s \, e_1 e_2) \, e_1 \, (c + s \, e_1 e_2)^{\sim} = (c^2 - s^2) e_1 - 2 c s \, e_2`.
Setting $`c = \cos(\theta/2), s = \sin(\theta/2)` yields the full-angle rotation
$`\cos\theta \, e_1 - \sin\theta \, e_2`, and Taylor-expanding $`c = 1 - \frac{1}{8}(d\omega)^2`,
$`s = \frac{1}{2} d\omega` yields the $`\operatorname{Spin}(m)` second-order eigenframe drift
$`(1 - \frac{1}{2}(d\omega)^2) e_1 - d\omega \, e_2` in Theorem 6.9. -/
theorem planarRotor_sandwich_e1 {Q : QuadraticForm R M} {e₁ e₂ : M}
    (he₁ : Q e₁ = 1) (he₂ : Q e₂ = 1) (h : Q.IsOrtho e₁ e₂) (c s : R) :
    planarRotor Q e₁ e₂ c s * CliffordAlgebra.ι Q e₁ *
        CliffordAlgebra.reverse (planarRotor Q e₁ e₂ c s) =
      (c ^ 2 - s ^ 2) • CliffordAlgebra.ι Q e₁ - (2 * c * s) • CliffordAlgebra.ι Q e₂ := by
  rw [planarRotor_reverse h, planarRotor]
  set B : CliffordAlgebra Q := CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂
  have hBe1 : B * CliffordAlgebra.ι Q e₁ = -CliffordAlgebra.ι Q e₂ := by
    calc
      (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂) * CliffordAlgebra.ι Q e₁
        = (-(CliffordAlgebra.ι Q e₂ * CliffordAlgebra.ι Q e₁)) * CliffordAlgebra.ι Q e₁ :=
            congrArg (· * CliffordAlgebra.ι Q e₁) (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h)
      _ = -(CliffordAlgebra.ι Q e₂ * (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₁)) := by
            rw [neg_mul, mul_assoc]
      _ = -CliffordAlgebra.ι Q e₂ := by
            rw [CliffordAlgebra.ι_sq_scalar, he₁, map_one, mul_one]
  have he1B : CliffordAlgebra.ι Q e₁ * B = CliffordAlgebra.ι Q e₂ := by
    dsimp [B]
    rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar, he₁, map_one, one_mul]
  have he2B : CliffordAlgebra.ι Q e₂ * B = -CliffordAlgebra.ι Q e₁ := by
    calc
      CliffordAlgebra.ι Q e₂ * (CliffordAlgebra.ι Q e₁ * CliffordAlgebra.ι Q e₂)
        = CliffordAlgebra.ι Q e₂ * (-(CliffordAlgebra.ι Q e₂ * CliffordAlgebra.ι Q e₁)) :=
            congrArg (CliffordAlgebra.ι Q e₂ * ·) (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h)
      _ = -((CliffordAlgebra.ι Q e₂ * CliffordAlgebra.ι Q e₂) * CliffordAlgebra.ι Q e₁) := by
            rw [mul_neg, ← mul_assoc]
      _ = -CliffordAlgebra.ι Q e₁ := by
            rw [CliffordAlgebra.ι_sq_scalar, he₂, map_one, one_mul]
  have hstep1 :
      (c • (1 : CliffordAlgebra Q) + s • B) * CliffordAlgebra.ι Q e₁ =
        c • CliffordAlgebra.ι Q e₁ - s • CliffordAlgebra.ι Q e₂ := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hBe1, smul_neg, sub_eq_add_neg]
  rw [hstep1]
  have hstep2 :
      (c • CliffordAlgebra.ι Q e₁ - s • CliffordAlgebra.ι Q e₂) *
          (c • (1 : CliffordAlgebra Q) - s • B) =
        (c * c) • CliffordAlgebra.ι Q e₁ - (c * s) • (CliffordAlgebra.ι Q e₁ * B) -
          (s * c) • CliffordAlgebra.ι Q e₂ + (s * s) • (CliffordAlgebra.ι Q e₂ * B) := by
    simp only [sub_mul, mul_sub, smul_mul_smul_comm, mul_one]
    abel
  rw [hstep2, he1B, he2B, smul_neg]
  have h2cs : 2 * c * s = c * s + s * c := by ring
  rw [sq, sq, sub_smul, h2cs, add_smul]
  abel

/-- Householder versor reflection identity in $`\mathcal{C}\ell(Q)`:
$`u x u = \operatorname{polar}_Q(u, x) \, u - Q(u) \, x`. -/
theorem versor_reflection_isometry (Q : QuadraticForm R M) (u x : M) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q u =
      CliffordAlgebra.ι Q (QuadraticMap.polar Q u x • u - Q u • x) :=
  CliffordAlgebra.ι_mul_ι_mul_ι u x

/-- Hestenes' graded left-contraction derivation rule:
$`d \lrcorner (a b) = d(a) \, b - a \, (d \lrcorner b)`. -/
theorem contraction_leibniz (Q : QuadraticForm R M) (d : Module.Dual R M)
    (a : M) (b : CliffordAlgebra Q) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.ι Q a * b) =
      d a • b - CliffordAlgebra.ι Q a * CliffordAlgebra.contractLeft d b :=
  CliffordAlgebra.contractLeft_ι_mul d a b

end CliffordIdentities

section HyperrealCliffordShadow

/-- Standard Euclidean sum-of-squares quadratic form $`Q_n(v) = \sum_{i=0}^{n-1} v_i^2` on
$`\operatorname{Fin} n \to R`. -/
def euclideanQuadForm (R : Type*) [CommRing R] (n : ℕ) : QuadraticForm R (Fin n → R) :=
  QuadraticMap.weightedSumSquares R (fun _ : Fin n => (1 : R))

@[simp]
theorem euclideanQuadForm_apply {R : Type*} [CommRing R] (n : ℕ) (v : Fin n → R) :
    euclideanQuadForm R n v = ∑ i : Fin n, v i * v i := by
  simp [euclideanQuadForm]

/-- Functorial change-of-scalars ring homomorphism $`\mathcal{C}\ell(Q_1) \to \mathcal{C}\ell(Q_2)`
induced by any ring homomorphism $`\varphi : R \to S` and $`\varphi`-semilinear map $`f : M_1 \to M_2`
compatible with the quadratic forms. -/
def cliffordChangeRingHom {R S M₁ M₂ : Type*}
    [CommRing R] [CommRing S] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module S M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm S M₂)
    (φ : R →+* S) (f : M₁ →+ M₂)
    (hf_smul : ∀ (r : R) (m : M₁), f (r • m) = φ r • f m)
    (hf_quad : ∀ m : M₁, Q₂ (f m) = φ (Q₁ m)) :
    CliffordAlgebra Q₁ →+* CliffordAlgebra Q₂ :=
  letI : Algebra R (CliffordAlgebra Q₂) :=
    ((algebraMap S (CliffordAlgebra Q₂)).comp φ).toAlgebra'
      (fun c x => Algebra.commutes (φ c) x)
  let g : M₁ →ₗ[R] CliffordAlgebra Q₂ :=
    { toFun := fun m => CliffordAlgebra.ι Q₂ (f m)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun r m => by
        dsimp
        rw [hf_smul, map_smul, Algebra.smul_def]
        rfl }
  (CliffordAlgebra.lift Q₁ ⟨g, fun m => by
    dsimp [g]
    rw [CliffordAlgebra.ι_sq_scalar, hf_quad]
    rfl⟩).toRingHom

@[simp]
theorem cliffordChangeRingHom_ι {R S M₁ M₂ : Type*}
    [CommRing R] [CommRing S] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module S M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm S M₂)
    (φ : R →+* S) (f : M₁ →+ M₂)
    (hf_smul : ∀ (r : R) (m : M₁), f (r • m) = φ r • f m)
    (hf_quad : ∀ m : M₁, Q₂ (f m) = φ (Q₁ m)) (m : M₁) :
    cliffordChangeRingHom Q₁ Q₂ φ f hf_smul hf_quad (CliffordAlgebra.ι Q₁ m) =
      CliffordAlgebra.ι Q₂ (f m) := by
  let _ : Algebra R (CliffordAlgebra Q₂) :=
    ((algebraMap S (CliffordAlgebra Q₂)).comp φ).toAlgebra'
      (fun c x => Algebra.commutes (φ c) x)
  exact CliffordAlgebra.lift_ι_apply _ _ m

@[simp]
theorem cliffordChangeRingHom_algebraMap {R S M₁ M₂ : Type*}
    [CommRing R] [CommRing S] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module S M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm S M₂)
    (φ : R →+* S) (f : M₁ →+ M₂)
    (hf_smul : ∀ (r : R) (m : M₁), f (r • m) = φ r • f m)
    (hf_quad : ∀ m : M₁, Q₂ (f m) = φ (Q₁ m)) (r : R) :
    cliffordChangeRingHom Q₁ Q₂ φ f hf_smul hf_quad (algebraMap R (CliffordAlgebra Q₁) r) =
      algebraMap S (CliffordAlgebra Q₂) (φ r) := by
  let _ : Algebra R (CliffordAlgebra Q₂) :=
    ((algebraMap S (CliffordAlgebra Q₂)).comp φ).toAlgebra'
      (fun c x => Algebra.commutes (φ c) x)
  exact AlgHom.commutes _ r

/-- Coordinatewise standard-part additive homomorphism $`\mathbb{L}^n \to \mathbb{R}^n`. -/
def stVecAddHom (n : ℕ) : (Fin n → LimitedSubring) →+ (Fin n → ℝ) where
  toFun v i := stRingHom (v i)
  map_zero' := by ext i; exact map_zero stRingHom
  map_add' u v := by ext i; exact map_add stRingHom (u i) (v i)

@[simp]
theorem stVecAddHom_apply (n : ℕ) (v : Fin n → LimitedSubring) (i : Fin n) :
    stVecAddHom n v i = st ((v i : LimitedSubring) : ℝ*) := rfl

theorem stVecAddHom_smul (n : ℕ) (r : LimitedSubring) (v : Fin n → LimitedSubring) :
    stVecAddHom n (r • v) = stRingHom r • stVecAddHom n v := by
  ext i
  exact map_mul stRingHom r (v i)

theorem stVecAddHom_quad (n : ℕ) (v : Fin n → LimitedSubring) :
    euclideanQuadForm ℝ n (stVecAddHom n v) =
      stRingHom (euclideanQuadForm LimitedSubring n v) := by
  rw [euclideanQuadForm_apply, euclideanQuadForm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (map_mul stRingHom (v i) (v i)).symm

/-- The **Nonstandard Clifford Standard-Part Homomorphism**
$`\operatorname{st}_{\mathcal{C}\ell} : \mathcal{C}\ell_n(\mathbb{L}) \to \mathcal{C}\ell_n(\mathbb{R})`,
projecting any limited-coefficient hyperreal multivector to its standard real multivector shadow
while preserving all multivector sums and geometric products. -/
def stCliffordHom (n : ℕ) :
    CliffordAlgebra (euclideanQuadForm LimitedSubring n) →+*
      CliffordAlgebra (euclideanQuadForm ℝ n) :=
  cliffordChangeRingHom
    (euclideanQuadForm LimitedSubring n)
    (euclideanQuadForm ℝ n)
    stRingHom
    (stVecAddHom n)
    (stVecAddHom_smul n)
    (stVecAddHom_quad n)

@[simp]
theorem stCliffordHom_ι (n : ℕ) (v : Fin n → LimitedSubring) :
    stCliffordHom n (CliffordAlgebra.ι (euclideanQuadForm LimitedSubring n) v) =
      CliffordAlgebra.ι (euclideanQuadForm ℝ n) (stVecAddHom n v) :=
  cliffordChangeRingHom_ι _ _ _ _ _ _ v

@[simp]
theorem stCliffordHom_algebraMap (n : ℕ) (c : LimitedSubring) :
    stCliffordHom n (algebraMap LimitedSubring _ c) =
      algebraMap ℝ _ (st (c : ℝ*)) :=
  cliffordChangeRingHom_algebraMap _ _ _ _ _ _ c

/-- Infinitesimal scalars lie in the kernel of $`\operatorname{st}_{\mathcal{C}\ell}`. -/
theorem stCliffordHom_infinitesimal_scalar (n : ℕ) {c : LimitedSubring}
    (hc : IsInfinitesimal (c : ℝ*)) :
    stCliffordHom n (algebraMap LimitedSubring _ c) = 0 := by
  rw [stCliffordHom_algebraMap, hc.st_eq_zero, map_zero]

/-- Infinitesimal vectors in $`\mathbb{I}^n \subset \mathbb{L}^n` project to $`0` under
$`\operatorname{st}_{\mathcal{C}\ell}`. -/
theorem stCliffordHom_infinitesimal_vec (n : ℕ) {v : Fin n → LimitedSubring}
    (hv : ∀ i : Fin n, IsInfinitesimal ((v i : LimitedSubring) : ℝ*)) :
    stCliffordHom n (CliffordAlgebra.ι (euclideanQuadForm LimitedSubring n) v) = 0 := by
  rw [stCliffordHom_ι]
  have hzero : stVecAddHom n v = 0 := by
    ext i
    exact (hv i).st_eq_zero
  rw [hzero, map_zero]

end HyperrealCliffordShadow

end NNScaling
