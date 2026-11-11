import NNScaling.Clifford

/-!
# 1. Introduction

These lecture notes focus on _scaling limits_ of neural networks, reformulated in **Nonstandard
Clifford Analysis** over the hyperreals $`\mathbb{R}^* = {}^*\mathbb{R}`, Loeb probability spaces
$`(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))`, and Euclidean Clifford algebras
$`\mathcal{C}\ell_n(\mathbb{R})` and $`{}^*\mathcal{C}\ell_N`.

## 1.1 Motivation: Scaling Laws as Infinitesimal Microscopes

In empirical deep learning practice, test loss often decreases predictably as a power law in training
compute, dataset size, or non-embedding parameter count when the remaining resources are not
bottlenecking. Viewing a trained network at unlimited hyperfinite compute budget
$`N \in {}^*\mathbb{N} \setminus \mathbb{N}` as an internal point $`x_N \in {}^*\mathcal{X}` infinitely close
to its standard shadow $`x_\infty \in \mathcal{X}` turns Equation (1.1) of Mufan Li's notes into an
exact hyperreal expansion:
$$`{}^*L(x_N) = L_\infty + c s_N + \delta s_N, \qquad c \in \mathbb{R} \setminus \{0\}, \quad \delta \approx 0,`
where $`s_N = N^{-\alpha} \in \mathbb{I}_+` is the positive infinitesimal scale of the finite-compute
correction. Applying an _infinitesimal microscope_ of magnification $`s_N^{-1} = N^\alpha` extracts
the exact scaling-law coefficient $`c` via the standard-part map $`\operatorname{st}`.
-/

noncomputable section

namespace NNScaling.Ch01

open NNScaling
open scoped Hyperreal NNScaling

/-- **Equation (1.1) (Hyperfinite Scaling-Law Expansion).** An observable value $`L_N \in {}^*\mathbb{R}`
admits a nondegenerate scaling-law expansion around $`L_\infty \in \mathbb{R}` at infinitesimal scale
$`s_N \in \mathbb{I} \setminus \{0\}` with standard amplitude $`c \in \mathbb{R} \setminus \{0\}` if
$`L_N = L_\infty + c s_N + \delta s_N` for some infinitesimal $`\delta \approx 0`. -/
structure ScalingLawExpansion (L_N : ℝ*) (L_inf c : ℝ) (s_N : ℝ*) : Prop where
  scale_infinitesimal : IsInfinitesimal s_N
  scale_ne_zero : s_N ≠ 0
  coeff_ne_zero : c ≠ 0
  exists_rem : ∃ rem : ℝ*, IsInfinitesimal rem ∧ L_N = (L_inf : ℝ*) + (c : ℝ*) * s_N + rem * s_N

/-- **Shadow Convergence of a Scaling Law.** Under Equation (1.1), $`L_N \approx L_\infty`, so
$`\operatorname{st}(L_N) = L_\infty`. -/
theorem ScalingLawExpansion.st_eq {L_N : ℝ*} {L_inf c : ℝ} {s_N : ℝ*}
    (h : ScalingLawExpansion L_N L_inf c s_N) :
    st L_N = L_inf := by
  rcases h.exists_rem with ⟨rem, hrem, rfl⟩
  apply st_eq_of_infClose
  rw [InfClose]
  have h1 : IsInfinitesimal ((c : ℝ*) * s_N) :=
    (limited_coe c).mul_isInfinitesimal h.scale_infinitesimal
  have h2 : IsInfinitesimal (rem * s_N) :=
    hrem.limited.mul_isInfinitesimal h.scale_infinitesimal
  convert h1.add h2 using 1
  ring

/-- **Infinitesimal Microscope Theorem (Equation (1.1)).** Magnifying the hyperfinite discrepancy
$`L_N - L_\infty` by $`s_N^{-1}` places it in the appreciable ring $`\mathbb{A}` with standard part
$`\operatorname{st}((L_N - L_\infty) / s_N) = c`. -/
theorem ScalingLawExpansion.microscope_st {L_N : ℝ*} {L_inf c : ℝ} {s_N : ℝ*}
    (h : ScalingLawExpansion L_N L_inf c s_N) :
    st ((L_N - (L_inf : ℝ*)) / s_N) = c := by
  rcases h.exists_rem with ⟨rem, hrem, rfl⟩
  have hdiv : (((L_inf : ℝ*) + (c : ℝ*) * s_N + rem * s_N - (L_inf : ℝ*)) / s_N) = (c : ℝ*) + rem := by
    have hs := h.scale_ne_zero
    field_simp
    ring
  rw [hdiv]
  apply st_eq_of_infClose
  simpa [InfClose] using hrem

/-- Under Equation (1.1), the rescaled discrepancy $`(L_N - L_\infty)/s_N` is appreciable, i.e.
$`L_N - L_\infty \asymp s_N`. -/
theorem ScalingLawExpansion.scaleEq {L_N : ℝ*} {L_inf c : ℝ} {s_N : ℝ*}
    (h : ScalingLawExpansion L_N L_inf c s_N) :
    (L_N - (L_inf : ℝ*)) ≍ₛ s_N := by
  have hst := h.microscope_st
  rcases h.exists_rem with ⟨rem, hrem, hL⟩
  have hquot_eq : (L_N - (L_inf : ℝ*)) / s_N = (c : ℝ*) + rem := by
    rw [hL]
    have hs := h.scale_ne_zero
    field_simp
    ring
  have hlim : Limited ((L_N - (L_inf : ℝ*)) / s_N) := by
    rw [hquot_eq]
    exact (limited_coe c).add hrem.limited
  have happ : Appreciable ((L_N - (L_inf : ℝ*)) / s_N) := by
    refine ⟨hlim, fun hinf => h.coeff_ne_zero ?_⟩
    rw [← hst]
    exact hinf.st_eq_zero
  refine ⟨?_, h.scale_ne_zero, happ⟩
  intro hzero
  rw [hzero, zero_div] at happ
  exact happ.ne_zero rfl

/-!
## 1.2 Examples of Scaling Limits at Hyperfinite Scale

The three classical scaling limits of Section 1.2 share the four-ingredient nonstandard checklist
(**Remark 1.6**):

1. **Hyperfinite CLT & Anderson's Brownian Motion (Definition 1.1, Theorem 1.2):** For $`N` internal
   i.i.d. centered summands of variance $`\sigma^2 \in (0,\infty)`, normalization by $`1/(\sigma\sqrt{N})`
   keeps total internal variance equal to $`1 \in \mathbb{A}` while each step variance is
   $`1/N \in \mathbb{I}`. Anderson's theorem identifies standard Brownian motion as the uniform shadow
   $`B_t = \operatorname{st}(Z_t^{(N)})` of the interpolated hyperfinite walk.
2. **Wigner Semicircle Law & $`\mathcal{C}\ell_2^+` Cauchy–Dirac Resolvent (Theorem 1.4, Remark 1.5):**
   For an internal $`N \times N` symmetric Wigner matrix $`X`, the Loeb standard-part pushforward of
   the internal ESD of $`N^{-1/2}X` equals the deterministic semicircle density
   $`\rho_{\mathrm{sc}}(x) = \frac{\sqrt{(4-x^2)_+}}{2\pi}` on $`[-2, 2]`, extracted via the even
   Clifford subalgebra $`\mathcal{C}\ell_2^+ \cong \mathbb{C}` ($`\mathbf{i} = e_1 e_2`, $`\mathbf{i}^2 = -1`).
3. **Interacting Particle System & Scalar Dirac Divergence (Equations (1.8)–(1.11)):** For $`N` particles
   evolving by $`\partial_t X_i = \frac{1}{N}\sum_{j=1}^N {}^*\mathcal{K}(X_i - X_j)`, the Loeb shadow
   $`\rho_t = L(\rho_t^{(N)}) \circ \operatorname{st}^{-1}` solves the weak continuity equation
   $`\partial_t \rho_t + \langle \partial_x(b(\cdot,\rho_t)\rho_t)\rangle_0 = 0`.
-/

/-- **CLT Variance Balance (Equation (1.2)).** If $`N` is unlimited and each independent summand
has standard variance $`\sigma^2 > 0`, the normalized sum $`(\sigma\sqrt{N})^{-1}\sum_{i=1}^N X_i` has
unit total variance while each individual summand has infinitesimal variance $`1 / N \in \mathbb{I}`. -/
theorem clt_step_variance_infinitesimal {N : ℝ*} (hN : Unlimited N) :
    IsInfinitesimal ((1 : ℝ*) / N) :=
  empirical_variance_isInfinitesimal limited_one hN

/-- **Wigner Semicircle Density (Equation (1.7)).** The standard semicircle density
$`\rho_{\mathrm{sc}}(x) = \sqrt{\max(4 - x^2, 0)} / (2\pi)` is everywhere nonnegative and vanishes
outside $`[-2, 2]`. -/
def wignerSemicircleDensity (x : ℝ) : ℝ :=
  Real.sqrt (max (4 - x ^ 2) 0) / (2 * Real.pi)

theorem wignerSemicircleDensity_nonneg (x : ℝ) : 0 ≤ wignerSemicircleDensity x := by
  unfold wignerSemicircleDensity
  exact div_nonneg (Real.sqrt_nonneg _) (by positivity)

theorem wignerSemicircleDensity_eq_zero_of_abs_ge {x : ℝ} (hx : 2 ≤ |x|) :
    wignerSemicircleDensity x = 0 := by
  unfold wignerSemicircleDensity
  have hsq : 4 ≤ x ^ 2 := by
    have h2 : (2 : ℝ) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
    rw [sq_abs] at h2
    linarith
  have hmax : max (4 - x ^ 2) 0 = 0 := max_eq_right (by linarith)
  simp [hmax]

/-- **Remark 1.5 (Cauchy–Dirac Resolvent Denominator in $`\mathcal{C}\ell_2^+`).**
Identifying a spectral point $`z = x + \eta \, e_1 e_2 \in \mathcal{C}\ell^+(Q)` for orthonormal
$`e_1, e_2` ($`Q(e_1) = Q(e_2) = 1`, $`e_1 \perp_Q e_2`), multiplying $`z` by its Clifford reverse
$`z^{\sim} = x - \eta \, e_1 e_2` yields the positive scalar denominator $`(x^2 + \eta^2) \cdot 1`. -/
theorem cauchy_dirac_resolvent_norm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} {e₁ e₂ : M}
    (he₁ : Q e₁ = 1) (he₂ : Q e₂ = 1) (h : Q.IsOrtho e₁ e₂) (x η : R) :
    planarRotor Q e₁ e₂ x η * CliffordAlgebra.reverse (planarRotor Q e₁ e₂ x η) =
      (x ^ 2 + η ^ 2) • (1 : CliffordAlgebra Q) :=
  planarRotor_mul_reverse he₁ he₂ h x η

end NNScaling.Ch01
