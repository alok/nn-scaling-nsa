import NNScaling.Foundations

/-!
# 2. Kernel Limits for Wide Networks: NNGP and NTK

Chapter 2 studies two distinct hyperfinite-width limits ($`N \in {}^*\mathbb{N} \setminus \mathbb{N}` at
standard depth $`d`, input dimension $`n_0`, and dataset size $`m`):

1. **Initialization (NNGP, Sections 2.1–2.2):** Conditioned on the hidden pre-activations, Gaussian
   readout weights make the output vector _exactly_ internally Gaussian with covariance $`\Phi^{(N)}`.
   By the hyperfinite law of large numbers, $`\Phi^{(N)} \approx \Phi` $`L({}^*\mathbb{P})`-almost surely,
   yielding a standard Gaussian process shadow $`\operatorname{GP}(0, \Phi)` (**Theorem 2.3**) and the
   deep recursion $`\Phi_{\ell+1} = \mathcal{C}_\varphi(\Phi_\ell)` (**Theorem 2.13**).
2. **Training (NTK, Sections 2.3–2.5):** Along gradient flow $`\partial_t \theta = -\nabla_\theta L(\theta)`,
   the residual obeys $`\partial_t r = -\frac{1}{m} K_t^{(N)} r` (**Proposition 2.15**), loss dissipates at
   rate $`-\frac{1}{m^2} r^\top K_t^{(N)} r \le 0` (**Proposition 2.17**), and for a depth-$`d` MLP the
   empirical NTK decomposes via Hadamard products as
   $`K_t^{(N)} = \sum_{\ell=0}^d G_{\ell+1}^{(N)} \odot \Phi_\ell^{(N)}` (**Proposition 2.25**). Because
   per-neuron parameter displacement is $`O(N^{-1}) \subset \mathbb{I}`, $`K_t^{(N)} \approx K` remains
   frozen at its deterministic shadow, yielding exponential loss decay (**Proposition 2.22**).
-/

noncomputable section

namespace NNScaling.Ch02

open NNScaling Matrix BigOperators Finset
open scoped Hyperreal NNScaling

/-- **Equation (2.9) (Positive Semidefiniteness of Empirical & Limiting Feature Gram Matrices).**
For any feature map $`\psi : \operatorname{Fin} m \to \iota \to \mathbb{R}` and weights $`u : \operatorname{Fin} m \to \mathbb{R}`,
the Gram quadratic form $`\sum_{\alpha,\beta} u_\alpha u_\beta \langle \psi(\alpha), \psi(\beta)\rangle` is a sum of squares
and hence nonnegative. -/
theorem gram_quadForm_nonneg {m n : ℕ} (ψ : Fin m → Fin n → ℝ) (u : Fin m → ℝ) :
    0 ≤ ∑ α : Fin m, ∑ β : Fin m, u α * u β * (∑ i : Fin n, ψ α i * ψ β i) := by
  have h_eq :
      (∑ α : Fin m, ∑ β : Fin m, u α * u β * (∑ i : Fin n, ψ α i * ψ β i)) =
        ∑ i : Fin n, (∑ α : Fin m, u α * ψ α i) ^ 2 := by
    calc
      (∑ α : Fin m, ∑ β : Fin m, u α * u β * (∑ i : Fin n, ψ α i * ψ β i))
          = ∑ α : Fin m, ∑ β : Fin m, ∑ i : Fin n, (u α * ψ α i) * (u β * ψ β i) := by
            refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin n, ∑ α : Fin m, ∑ β : Fin m, (u α * ψ α i) * (u β * ψ β i) := by
            rw [Finset.sum_congr rfl fun α _ => Finset.sum_comm]
            exact Finset.sum_comm
      _ = ∑ i : Fin n, (∑ α : Fin m, u α * ψ α i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [Finset.mul_sum]
  rw [h_eq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **Proposition 2.5 (Cho–Saul Derivative Kernel Bounds).** For correlation $`\rho \in [-1, 1]`,
the ReLU derivative kernel $`k_1(\rho) = \frac{1}{4} + \frac{1}{2\pi}\arcsin(\rho)` takes $`1/4` at $`\rho = 0`,
$`1/2` at $`\rho = 1`, and $`0` at $`\rho = -1`. -/
def choSaulDeriv (ρ : ℝ) : ℝ := 1 / 4 + Real.arcsin ρ / (2 * Real.pi)

@[simp]
theorem choSaulDeriv_zero : choSaulDeriv 0 = 1 / 4 := by
  simp [choSaulDeriv]

theorem choSaulDeriv_one : choSaulDeriv 1 = 1 / 2 := by
  unfold choSaulDeriv
  rw [Real.arcsin_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem choSaulDeriv_neg_one : choSaulDeriv (-1) = 0 := by
  unfold choSaulDeriv
  rw [Real.arcsin_neg, Real.arcsin_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Empirical NTK Matrix (Equation (2.40)).** Given parameter gradients
$`J : \operatorname{Fin} m \to \operatorname{Fin} P \to \mathbb{R}`, the empirical NTK has entries
$`K_{\alpha\beta} = \langle J(\alpha), J(\beta) \rangle`. -/
def empiricalNTK {m P : ℕ} (J : Fin m → Fin P → ℝ) (α β : Fin m) : ℝ :=
  ∑ p : Fin P, J α p * J β p

/-- **Proposition 2.15 & 2.17 (Residual Velocity and Risk Dissipation Identity).**
When parameter velocity is $`\dot{\theta}_p = -\frac{1}{m}\sum_\beta r_\beta J_{\beta p}`, the output velocity
$`\dot{f}_\alpha = \sum_p J_{\alpha p} \dot{\theta}_p` equals $`-\frac{1}{m}\sum_\beta K_{\alpha\beta} r_\beta`,
and the loss time-derivative $`\frac{1}{m}\sum_\alpha r_\alpha \dot{f}_\alpha` equals
$`-\frac{1}{m^2} \sum_{\alpha,\beta} r_\alpha K_{\alpha\beta} r_\beta \le 0`. -/
theorem residual_velocity_eq {m P : ℕ} (J : Fin m → Fin P → ℝ) (r : Fin m → ℝ) (α : Fin m) :
    (∑ p : Fin P, J α p * (-(1 / (m : ℝ)) * ∑ β : Fin m, r β * J β p)) =
      -(1 / (m : ℝ)) * ∑ β : Fin m, empiricalNTK J α β * r β := by
  unfold empiricalNTK
  calc
    (∑ p : Fin P, J α p * (-(1 / (m : ℝ)) * ∑ β : Fin m, r β * J β p))
        = -(1 / (m : ℝ)) * ∑ p : Fin P, ∑ β : Fin m, J α p * (r β * J β p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => by ring
    _ = -(1 / (m : ℝ)) * ∑ β : Fin m, ∑ p : Fin P, (J α p * J β p) * r β := by
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun p _ => by ring
    _ = -(1 / (m : ℝ)) * ∑ β : Fin m, (∑ p : Fin P, J α p * J β p) * r β := by
          congr 1
          refine Finset.sum_congr rfl fun β _ => by rw [Finset.sum_mul]

theorem risk_dissipation_nonpos {m P : ℕ} (J : Fin m → Fin P → ℝ) (r : Fin m → ℝ) :
    (1 / (m : ℝ)) * (∑ α : Fin m, r α * (-(1 / (m : ℝ)) * ∑ β : Fin m, empiricalNTK J α β * r β)) ≤ 0 := by
  have hrew :
      (1 / (m : ℝ)) * (∑ α : Fin m, r α * (-(1 / (m : ℝ)) * ∑ β : Fin m, empiricalNTK J α β * r β)) =
        -((1 / (m : ℝ)) ^ 2 * ∑ α : Fin m, ∑ β : Fin m, r α * r β * empiricalNTK J α β) := by
    rw [← neg_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← mul_assoc, ← mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => by ring
  rw [hrew]
  exact neg_nonpos.2 (mul_nonneg (sq_nonneg _) (gram_quadForm_nonneg J r))

/-- **Proposition 2.22 (Exponential Decay in Eigenmode Coordinates, Equations (2.59)–(2.61)).**
If eigenmode residuals evolve as $`r_i(t) = \exp(-\lambda_i t / m) r_i(0)` with $`\lambda_{\min} \le \lambda_i`
and $`t \ge 0`, $`m > 0`, then $`\sum_i r_i(t)^2 \le \exp(-2\lambda_{\min} t / m) \sum_i r_i(0)^2`. -/
theorem fixed_kernel_loss_bound {m : ℕ} (hm : 0 < (m : ℝ)) {t lam_min : ℝ} (ht : 0 ≤ t)
    (lam : Fin m → ℝ) (hlam : ∀ i, lam_min ≤ lam i) (r0 : Fin m → ℝ) :
    (∑ i : Fin m, (Real.exp (-(lam i) * t / m) * r0 i) ^ 2) ≤
      Real.exp (-2 * lam_min * t / m) * ∑ i : Fin m, (r0 i) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hexp_sq :
      (Real.exp (-(lam i) * t / m) * r0 i) ^ 2 = Real.exp (-2 * lam i * t / m) * (r0 i) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [hexp_sq]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
  have h1 : lam_min * t ≤ lam i * t := mul_le_mul_of_nonneg_right (hlam i) ht
  have h2 : -2 * lam i * t ≤ -2 * lam_min * t := by linarith
  exact div_le_div_of_nonneg_right h2 hm.le

/-- **Hyperfinite Lazy-Training Displacement Bound (Equation (2.55)).**
If $`t L_0 \in \mathbb{L}` is limited and network width $`N \in {}^*\mathbb{R}` is unlimited,
the normalized mean-square parameter displacement bound $`(t L_0) / N` is infinitesimal. -/
theorem ntk_displacement_infinitesimal {tL0 N : ℝ*} (hL : Limited tL0) (hN : Unlimited N) :
    IsInfinitesimal (tL0 / N) :=
  empirical_variance_isInfinitesimal hL hN

/-- **Proposition 2.25 (Layerwise Hadamard NTK Decomposition, Equations (2.77)–(2.80)).**
For each hidden weight block $`W_\ell` whose gradient with respect to input $`\alpha` is the rank-one
outer product $`\frac{1}{N} g_{\ell+1}^\alpha (\varphi_\ell^\alpha)^\top`, the Frobenius inner product of
layer-$`\ell` gradients factors into the product of backward covariance $`G_{\ell+1}^{\alpha\beta}` and
forward kernel $`\Phi_\ell^{\alpha\beta}`. -/
theorem rankOne_frobenius_product {N : ℕ} (gα gβ φα φβ : Fin N → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N,
        ((1 / (N : ℝ)) * gα i * φα j) * ((1 / (N : ℝ)) * gβ i * φβ j)) =
      ((1 / (N : ℝ)) * ∑ i : Fin N, gα i * gβ i) *
        ((1 / (N : ℝ)) * ∑ j : Fin N, φα j * φβ j) := by
  calc
    (∑ i : Fin N, ∑ j : Fin N,
        ((1 / (N : ℝ)) * gα i * φα j) * ((1 / (N : ℝ)) * gβ i * φβ j))
        = ∑ i : Fin N, ((1 / (N : ℝ)) * gα i * gβ i) *
            ((1 / (N : ℝ)) * ∑ j : Fin N, φα j * φβ j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
    _ = ((1 / (N : ℝ)) * ∑ i : Fin N, gα i * gβ i) *
          ((1 / (N : ℝ)) * ∑ j : Fin N, φα j * φβ j) := by
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring

end NNScaling.Ch02
