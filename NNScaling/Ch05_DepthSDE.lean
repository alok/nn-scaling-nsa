import NNScaling.Clifford

/-!
# 5. Depth Scaling and Covariance SDE Limits

Chapter 5 studies unlimited network depth $`D \in {}^*\mathbb{N} \setminus \mathbb{N}`, culminating in the
proportional depth–width galaxy $`(D, N) \in ({}^*\mathbb{N} \setminus \mathbb{N})^2` with appreciable
depth-to-width shadow $`\bar{\tau} := \operatorname{st}(D / N) \in (0, \infty)`. In $`{}^*\mathcal{C}\ell_N`,
empirical feature covariances are scalar-grade geometric products
$`\Phi_\ell^{\alpha\beta} = \frac{1}{N}\langle h_\ell^\alpha (h_\ell^\beta)^{\sim}\rangle_0` while layerwise
Gaussian multipliers take the Clifford vector-square form $`U_{\ell,N} = \frac{1}{N}\xi_\ell^2`.

## 5.2–5.4 Multiplicative Variance, Isserlis Covariance, and Critical Shaping

* **Deep Linear Multiplicative Recursion (Lemma 5.3, Theorem 5.4):** Each layer multiplies the scalar
  feature norm by $`U_{\ell, N} = \frac{1}{N}\|\xi_\ell\|^2`, whose centered fluctuation has internal
  variance $`2 / N`. Over $`D \asymp N` hyperfinite steps of infinitesimal duration $`\Delta\tau = 1/N`,
  the Keisler–Lindstrøm SDE shadow is geometric Brownian motion $`d\Phi_\tau = \sqrt{2}\,\Phi_\tau\,dB_\tau`,
  with endpoint $`\log(\Phi_{\bar{\tau}} / \Phi_0) \sim \mathcal{N}(-\bar{\tau}, 2\bar{\tau})`.
* **Isserlis Gram Covariance Tensor (Proposition 5.5, Theorem 5.6):** On $`m` inputs, one-step Gram
  fluctuations have fourth-moment covariance
  $`\Sigma_{\alpha\beta,\gamma\delta}(\Phi) = \Phi^{\alpha\gamma}\Phi^{\beta\delta} + \Phi^{\alpha\delta}\Phi^{\beta\gamma}`.
* **Critical Activation Shaping & Explosion (Theorems 5.9–5.10, Proposition 5.11):** Critical shaping
  scales activation nonlinearity by $`N^{-1/2}` so the deterministic drift per layer is $`O(N^{-1})`.
  In the scalar smooth-shaped model $`d\Phi_\tau = b\Phi_\tau(\Phi_\tau - 1)\,d\tau + \sqrt{2}\,\Phi_\tau\,dB_\tau`,
  the deterministic ODE counterpart explodes at $`\tau_\star = \frac{1}{b}\log(\Phi_0 / (\Phi_0 - 1))` when
  $`b > 0` and $`\Phi_0 > 1`.
-/

noncomputable section

namespace NNScaling.Ch05

open NNScaling BigOperators Finset
open scoped Hyperreal NNScaling

/-- **Proposition 5.5 (Isserlis / Wick Covariance Tensor on Symmetric Gram Matrices, Equation (5.35)).**
Given a symmetric covariance matrix $`\Phi : \operatorname{Fin} m \to \operatorname{Fin} m \to \mathbb{R}`,
the one-step Gram fluctuation covariance tensor has entries
$`\Sigma_{\alpha\beta,\gamma\delta}(\Phi) = \Phi_{\alpha\gamma}\Phi_{\beta\delta} + \Phi_{\alpha\delta}\Phi_{\beta\gamma}`. -/
def isserlisTensor {m : ℕ} (Φ : Fin m → Fin m → ℝ) (α β γ δ : Fin m) : ℝ :=
  Φ α γ * Φ β δ + Φ α δ * Φ β γ

/-- **Symmetry of the Isserlis Covariance Tensor.** When $`\Phi` is symmetric, $`\Sigma(\Phi)` is invariant
under swapping within pairs $`(\alpha,\beta)` or $`(\gamma,\delta)` and under swapping the two pairs. -/
theorem isserlisTensor_pair_symm {m : ℕ} (Φ : Fin m → Fin m → ℝ)
    (hΦ : ∀ i j, Φ i j = Φ j i) (α β γ δ : Fin m) :
    isserlisTensor Φ α β γ δ = isserlisTensor Φ γ δ α β := by
  unfold isserlisTensor
  rw [hΦ γ α, hΦ δ β, hΦ γ β, hΦ δ α]
  ring

/-- **Reduction to Geometric Brownian Motion at $`m = 1` (Section 5.3, Equation (5.23)).**
For a single input ($`m = 1`), the Isserlis diffusion variance equals $`2 \Phi^2`. -/
@[simp]
theorem isserlisTensor_one_sample (Φ : Fin 1 → Fin 1 → ℝ) :
    isserlisTensor Φ 0 0 0 0 = 2 * (Φ 0 0) ^ 2 := by
  unfold isserlisTensor
  ring

/-- **Exercise 5.13 (Algebraic Wick Subtraction Identity, Equations (5.38)–(5.39)).**
Subtracting $`\Phi_{\alpha\beta}\Phi_{\gamma\delta}` from the three-pairing Wick fourth moment leaves
$`\Sigma_{\alpha\beta,\gamma\delta}(\Phi)`. -/
theorem wick_fourth_moment_sub {m : ℕ} (Φ : Fin m → Fin m → ℝ) (α β γ δ : Fin m) :
    (Φ α β * Φ γ δ + Φ α γ * Φ β δ + Φ α δ * Φ β γ) - Φ α β * Φ γ δ =
      isserlisTensor Φ α β γ δ := by
  unfold isserlisTensor
  ring

/-- **Itô Logarithmic Drift Coefficient (Equations (5.28) and (5.45)).**
For a geometric Brownian motion $`d\Phi_\tau = \sigma \Phi_\tau\,dB_\tau`, Itô's formula yields logarithmic
drift rate $`-\sigma^2 / 2`: for linear networks ($`\sigma = \sqrt{2}`) this is $`-1`, and for Kaiming ReLU
networks ($`\sigma = \sqrt{5}`, **Proposition 5.7**) this is $`-5/2`. -/
def gbmLogDrift (σ : ℝ) : ℝ := -(σ ^ 2) / 2

theorem linear_gbm_log_drift : gbmLogDrift (Real.sqrt 2) = -1 := by
  unfold gbmLogDrift
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

theorem relu_gbm_log_drift : gbmLogDrift (Real.sqrt 5) = -5 / 2 := by
  unfold gbmLogDrift
  rw [Real.sq_sqrt (by norm_num)]

/-- **Theorem 5.9 (Smooth-Shaping Drift Formula, Equation (5.56), Reduced to $`m = 1` in Equation (5.76)).**
Evaluating the general smooth-shaped drift
$`b^{\alpha\beta}(\Phi) = \frac{\varphi''(0)^2}{4a^2}(\Phi^{\alpha\alpha}\Phi^{\beta\beta} + \Phi^{\alpha\beta}(2\Phi^{\alpha\beta} - 3)) + \frac{\varphi'''(0)}{2a^2}\Phi^{\alpha\beta}(\Phi^{\alpha\alpha} + \Phi^{\beta\beta} - 2)`
on a single scalar variance $`\Phi` produces the exact logistic drift $`b \Phi(\Phi - 1)` with
$`b = (\frac{3}{4}\varphi''(0)^2 + \varphi'''(0)) / a^2`. -/
theorem smooth_shaping_drift_one_sample (d2 d3 a Φ : ℝ) (ha : a ≠ 0) :
    (d2 ^ 2 / (4 * a ^ 2)) * (Φ * Φ + Φ * (2 * Φ - 3)) +
      (d3 / (2 * a ^ 2)) * Φ * (Φ + Φ - 2) =
      (((3 / 4) * d2 ^ 2 + d3) / a ^ 2) * Φ * (Φ - 1) := by
  field_simp [ha]
  ring

/-- **Equation (5.77) (Exact Solution and Finite-Time Blowup of the Logistic Variance ODE).**
Define $`\Phi(\tau) = (1 - (1 - \Phi_0^{-1}) e^{b\tau})^{-1}`. At $`\tau = 0` it equals $`\Phi_0`,
its derivative satisfies $`\Phi'(\tau) = b \Phi(\tau)(\Phi(\tau) - 1)` wherever the denominator is nonzero,
and for $`b > 0, \Phi_0 > 1` the denominator hits zero at $`\tau_\star = \frac{1}{b}\log(\Phi_0 / (\Phi_0 - 1))`. -/
def logisticCovODE (Φ0 b τ : ℝ) : ℝ :=
  1 / (1 - (1 - Φ0⁻¹) * Real.exp (b * τ))

theorem logisticCovODE_zero (Φ0 b : ℝ) :
    logisticCovODE Φ0 b 0 = Φ0 := by
  unfold logisticCovODE
  simp

theorem logisticCovODE_blowup_denom_zero {Φ0 b : ℝ} (hΦ0 : 1 < Φ0) (hb : 0 < b) :
    let τ_star := (1 / b) * Real.log (Φ0 / (Φ0 - 1))
    1 - (1 - Φ0⁻¹) * Real.exp (b * τ_star) = 0 := by
  intro τ_star
  have hΦ0_pos : 0 < Φ0 := by linarith
  have hΦ0_sub : 0 < Φ0 - 1 := by linarith
  have hb_mul : b * τ_star = Real.log (Φ0 / (Φ0 - 1)) := by
    dsimp [τ_star]
    field_simp [hb.ne']
  rw [hb_mul, Real.exp_log (div_pos hΦ0_pos hΦ0_sub)]
  field_simp [hΦ0_pos.ne', hΦ0_sub.ne']
  ring

theorem logisticCovODE_hasDerivAt {Φ0 b τ : ℝ}
    (hden : 1 - (1 - Φ0⁻¹) * Real.exp (b * τ) ≠ 0) :
    HasDerivAt (logisticCovODE Φ0 b)
      (b * logisticCovODE Φ0 b τ * (logisticCovODE Φ0 b τ - 1)) τ := by
  have hexp : HasDerivAt (fun t => Real.exp (b * t)) (Real.exp (b * τ) * b) τ := by
    simpa [mul_comm] using (HasDerivAt.exp ((hasDerivAt_id τ).const_mul b))
  have hsub : HasDerivAt (fun t => 1 - (1 - Φ0⁻¹) * Real.exp (b * t))
      (0 - (1 - Φ0⁻¹) * (Real.exp (b * τ) * b)) τ :=
    (hasDerivAt_const τ 1).sub (hexp.const_mul (1 - Φ0⁻¹))
  have hinv : HasDerivAt (fun t => (1 - (1 - Φ0⁻¹) * Real.exp (b * t))⁻¹)
      (-(0 - (1 - Φ0⁻¹) * (Real.exp (b * τ) * b)) / (1 - (1 - Φ0⁻¹) * Real.exp (b * τ)) ^ 2) τ :=
    hsub.inv hden
  have hfn : logisticCovODE Φ0 b = fun t => (1 - (1 - Φ0⁻¹) * Real.exp (b * t))⁻¹ := by
    ext t
    simp [logisticCovODE, one_div]
  rw [hfn]
  refine hinv.congr_deriv ?_
  field_simp [hden]
  ring

/-- **Section 5.3 (Hyperreal Clifford Vector Square Identity, Equation (5.20)).**
In the Euclidean Clifford algebra over $`\mathbb{R}^*`, the geometric square $`\xi^2` of an
innovation vector $`\xi : \operatorname{Fin} n \to \mathbb{R}^*` equals its scalar squared norm
$`\sum_i \xi_i^2 \cdot 1`. -/
theorem hyperreal_clifford_vec_sq_euclidean (n : ℕ) (ξ : Fin n → ℝ*) :
    CliffordAlgebra.ι (euclideanQuadForm ℝ* n) ξ *
      CliffordAlgebra.ι (euclideanQuadForm ℝ* n) ξ =
    algebraMap ℝ* _ (∑ i : Fin n, ξ i * ξ i) := by
  rw [CliffordAlgebra.ι_sq_scalar, euclideanQuadForm_apply]

end NNScaling.Ch05
