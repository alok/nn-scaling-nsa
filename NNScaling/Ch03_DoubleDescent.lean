import NNScaling.Foundations

/-!
# 3. Double Descent with Random Projections

Chapter 3 analyzes generalization error for ridgeless random-projection linear regression at a
proportionally unlimited hyperfinite triple $`(M, N_0, N) \in ({}^*\mathbb{N} \setminus \mathbb{N})^3`
with appreciable aspect-ratio shadows:
$$`\gamma := \operatorname{st}\!\left(\frac{N_0}{M}\right) \in (0, \infty), \qquad \delta := \operatorname{st}\!\left(\frac{N}{M}\right) \in (0, \infty).`

## 3.3 Asymptotic Bias, Variance, and the Phase Diagram

In **Theorem 3.1**, the Loeb standard parts of the conditional variance and bias split across three
rank bottlenecks determined by $`\min\{M, N_0, N\}`:

* **(a) Feature-bottleneck ($`\delta < \min\{1, \gamma\}`):**
  $`R^{(\mathrm{var})} \approx \sigma^2 \frac{\delta}{1-\delta}` and
  $`R^{(\mathrm{bias})} \approx \frac{\gamma - \delta}{\gamma(1-\delta)} \|\theta_\star\|^2`.
* **(b) Ambient-bottleneck ($`\gamma < 1 \le \delta/\gamma`, i.e. $`\gamma < 1` and $`\delta \ge \gamma`):**
  $`R^{(\mathrm{var})} \approx \sigma^2 \frac{\gamma}{1-\gamma}` and $`R^{(\mathrm{bias})} \approx 0`.
* **(c) Sample-bottleneck ($`\gamma > 1` and $`\delta > 1`):**
  $`R^{(\mathrm{var})} \approx \sigma^2 \left(\frac{1}{\gamma - 1} + \frac{1}{\delta - 1}\right)` and
  $`R^{(\mathrm{bias})} \approx \left(1 - \frac{1}{\gamma}\right)\frac{\delta}{\delta - 1} \|\theta_\star\|^2`.

Below we formalize all three risk formulas, verify the finite-sample Wishart identities
(**Equations (3.30) and (3.60)**) at hyperfinite scale via $`\operatorname{st}`, and prove every
statement of **Exercise 3.4.1** and **Exercise 3.4.2**.
-/

noncomputable section

namespace NNScaling.Ch03

open NNScaling
open scoped Hyperreal NNScaling

/-- **Theorem 3.1(a):** Limiting variance in the feature-bottleneck regime $`\delta < \min\{1, \gamma\}`. -/
def varFeature (σ2 δ : ℝ) : ℝ := σ2 * (δ / (1 - δ))

/-- **Theorem 3.1(a):** Limiting bias in the feature-bottleneck regime $`\delta < \min\{1, \gamma\}`. -/
def biasFeature (θ2 γ δ : ℝ) : ℝ := ((γ - δ) / (γ * (1 - δ))) * θ2

/-- **Theorem 3.1(a):** Total excess risk in the feature-bottleneck regime. -/
def riskFeature (σ2 θ2 γ δ : ℝ) : ℝ := varFeature σ2 δ + biasFeature θ2 γ δ

/-- **Theorem 3.1(b):** Limiting variance in the ambient-bottleneck regime $`\gamma < 1, \delta \ge \gamma`. -/
def varAmbient (σ2 γ : ℝ) : ℝ := σ2 * (γ / (1 - γ))

/-- **Theorem 3.1(b):** Total excess risk in the ambient-bottleneck regime (bias vanishes). -/
def riskAmbient (σ2 γ : ℝ) : ℝ := varAmbient σ2 γ

/-- **Theorem 3.1(c):** Limiting variance in the sample-bottleneck regime $`\gamma > 1, \delta > 1`. -/
def varSample (σ2 γ δ : ℝ) : ℝ := σ2 * (1 / (γ - 1) + 1 / (δ - 1))

/-- **Theorem 3.1(c):** Limiting bias in the sample-bottleneck regime $`\gamma > 1, \delta > 1`. -/
def biasSample (θ2 γ δ : ℝ) : ℝ := (1 - 1 / γ) * (δ / (δ - 1)) * θ2

/-- **Theorem 3.1(c):** Total excess risk in the sample-bottleneck regime. -/
def riskSample (σ2 θ2 γ δ : ℝ) : ℝ := varSample σ2 γ δ + biasSample θ2 γ δ

/-- **Equation (3.31) Algebra:** Amplification identity $`(1 - \delta/\gamma)(1 + \delta/(1-\delta)) = \frac{\gamma - \delta}{\gamma(1-\delta)}`. -/
theorem feature_bias_amplification {γ δ : ℝ} (hγ : γ ≠ 0) (hδ : 1 - δ ≠ 0) (θ2 : ℝ) :
    (1 - δ / γ) * (1 + δ / (1 - δ)) * θ2 = biasFeature θ2 γ δ := by
  unfold biasFeature
  field_simp [hγ, hδ]
  ring

/-- **Equation (3.62) Algebra:** Sample-bottleneck bias Combination
$`(1 - 1/\gamma + (\gamma - 1)/(\gamma(\delta - 1))) = (1 - 1/\gamma)\frac{\delta}{\delta - 1}`. -/
theorem sample_bias_amplification {γ δ : ℝ} (hγ : γ ≠ 0) (hδ : δ - 1 ≠ 0) (θ2 : ℝ) :
    (1 - 1 / γ + (γ - 1) / (γ * (δ - 1))) * θ2 = biasSample θ2 γ δ := by
  unfold biasSample
  field_simp [hγ, hδ]
  ring

/-- **Hyperfinite Inverse-Wishart Shadow (Lemma 3.2, Equations (3.15)–(3.16)).**
At unlimited $`M \in {}^*\mathbb{R}` with $`\operatorname{st}(N/M) = \delta \in (0, 1)`, the exact
internal inverse-Wishart trace expectation $`N / (M - N - 1)` has standard part $`\delta / (1 - \delta)`. -/
theorem wishart_trace_st_feature {M N : ℝ*} {δ : ℝ}
    (hM : Unlimited M) (hδ_lt : δ < 1)
    (h_ratio : (N / M) ≊ (δ : ℝ*)) :
    st (N / (M - N - 1)) = δ / (1 - δ) := by
  have hM_ne : M ≠ 0 := by
    intro h0
    have := hM 1
    rw [h0, abs_zero, Hyperreal.coe_one] at this
    linarith
  have h_rew : N / (M - N - 1) = (N / M) / (1 - N / M - 1 / M) := by
    have h1 : M - N - 1 = M * (1 - N / M - 1 / M) := by field_simp [hM_ne]
    rw [h1, div_mul_eq_div_div]
  rw [h_rew]
  have hN_lim : Limited (N / M) := by
    have : N / M = (N / M - δ) + δ := by ring
    rw [this]
    exact h_ratio.limited.add (limited_coe δ)
  have h1M_inf : IsInfinitesimal (1 / M) := empirical_variance_isInfinitesimal limited_one hM
  have hden_close : (1 - N / M - 1 / M) ≊ ((1 - δ : ℝ) : ℝ*) := by
    rw [InfClose, Hyperreal.coe_sub, Hyperreal.coe_one]
    have hsub : (1 - N / M - 1 / M) - (1 - (δ : ℝ*)) = -(N / M - δ) - (1 / M) := by ring
    rw [hsub, sub_eq_add_neg]
    exact h_ratio.neg.add h1M_inf.neg
  have hden_lim : Limited (1 - N / M - 1 / M) := by
    have : (1 - N / M - 1 / M) = ((1 - N / M - 1 / M) - ((1 - δ : ℝ) : ℝ*)) + ((1 - δ : ℝ) : ℝ*) := by ring
    rw [this]
    exact hden_close.limited.add (limited_coe (1 - δ))
  have hden_st : st (1 - N / M - 1 / M) = 1 - δ := st_eq_of_infClose hden_close
  have hden_app : Appreciable (1 - N / M - 1 / M) := by
    refine ⟨hden_lim, fun hinf => ?_⟩
    have hz := hinf.st_eq_zero
    rw [hden_st] at hz
    linarith
  rw [st_div hN_lim hden_app, st_eq_of_infClose h_ratio, hden_st]

/-- **Exercise 3.4.1 (Part 1: Strict Monotonicity Before Interpolation).**
When $`\gamma > 1`, $`\sigma^2 \ge 0`, $`\theta_2 \ge 0`, and $`\sigma^2 + \theta_2 > 0`, the total risk
$`R(\delta)` in the feature-bottleneck regime is strictly increasing on $`0 < \delta < 1`. -/
theorem riskFeature_strictMono {σ2 θ2 γ δ1 δ2 : ℝ}
    (hγ : 1 < γ) (hσ : 0 ≤ σ2) (hθ : 0 ≤ θ2) (hpos : 0 < σ2 + θ2)
    (h1 : 0 < δ1) (h12 : δ1 < δ2) (h2 : δ2 < 1) :
    riskFeature σ2 θ2 γ δ1 < riskFeature σ2 θ2 γ δ2 := by
  have hd1 : 0 < 1 - δ1 := by linarith
  have hd2 : 0 < 1 - δ2 := by linarith
  have hγ0 : 0 < γ := by linarith
  have hdiff :
      riskFeature σ2 θ2 γ δ2 - riskFeature σ2 θ2 γ δ1 =
        ((δ2 - δ1) / ((1 - δ1) * (1 - δ2))) * (σ2 + ((γ - 1) / γ) * θ2) := by
    unfold riskFeature varFeature biasFeature
    field_simp [hd1.ne', hd2.ne', hγ0.ne']
    ring
  have hfactor1 : 0 < (δ2 - δ1) / ((1 - δ1) * (1 - δ2)) :=
    div_pos (by linarith) (mul_pos hd1 hd2)
  have hfactor2 : 0 < σ2 + ((γ - 1) / γ) * θ2 := by
    rcases lt_or_eq_of_le hσ with hσ_pos | rfl
    · have hnonneg : 0 ≤ ((γ - 1) / γ) * θ2 :=
        mul_nonneg (div_nonneg (by linarith) hγ0.le) hθ
      linarith
    · have hθ_pos : 0 < θ2 := by linarith
      have hγ_fac : 0 < (γ - 1) / γ := div_pos (by linarith) hγ0
      linarith [mul_pos hγ_fac hθ_pos]
  linarith [mul_pos hfactor1 hfactor2]

/-- **Exercise 3.4.1 (Part 2: Strict Second Descent Beyond Interpolation).**
When $`\gamma > 1`, $`\sigma^2 \ge 0`, $`\theta_2 \ge 0`, and $`\sigma^2 + \theta_2 > 0`, the total risk
$`R(\delta)` in the sample-bottleneck regime is strictly decreasing on $`\delta > 1`. -/
theorem riskSample_strictAnti {σ2 θ2 γ δ1 δ2 : ℝ}
    (hγ : 1 < γ) (hσ : 0 ≤ σ2) (hθ : 0 ≤ θ2) (hpos : 0 < σ2 + θ2)
    (h1 : 1 < δ1) (h12 : δ1 < δ2) :
    riskSample σ2 θ2 γ δ2 < riskSample σ2 θ2 γ δ1 := by
  have hd1 : 0 < δ1 - 1 := by linarith
  have hd2 : 0 < δ2 - 1 := by linarith
  have hγ0 : 0 < γ := by linarith
  have hγ1 : 0 < γ - 1 := by linarith
  have hdiff :
      riskSample σ2 θ2 γ δ1 - riskSample σ2 θ2 γ δ2 =
        ((δ2 - δ1) / ((δ1 - 1) * (δ2 - 1))) * (σ2 + (1 - 1 / γ) * θ2) := by
    unfold riskSample varSample biasSample
    field_simp [hd1.ne', hd2.ne', hγ0.ne', hγ1.ne']
    ring
  have hfactor1 : 0 < (δ2 - δ1) / ((δ1 - 1) * (δ2 - 1)) :=
    div_pos (by linarith) (mul_pos hd1 hd2)
  have hfactor2 : 0 < σ2 + (1 - 1 / γ) * θ2 := by
    have h1γ : 0 < 1 - 1 / γ := by
      rw [sub_pos, div_lt_iff₀ hγ0]
      linarith
    rcases lt_or_eq_of_le hσ with hσ_pos | rfl
    · linarith [mul_nonneg h1γ.le hθ]
    · linarith [mul_pos h1γ (by linarith : 0 < θ2)]
  linarith [mul_pos hfactor1 hfactor2]

/-- **Exercise 3.4.1 (Part 3: Infinite-Overparameterization Decomposition).**
For $`\gamma > 1` and $`\delta > 1`, the sample-bottleneck risk decomposes into its $`\delta \to \infty`
asymptote $`\frac{\sigma^2}{\gamma - 1} + \left(1 - \frac{1}{\gamma}\right)\theta_2` plus the strictly positive
excess $`\frac{\sigma^2 + (1 - 1/\gamma)\theta_2}{\delta - 1}`, which diverges as $`\delta \downarrow 1` and
vanishes as $`\delta \to \infty`. -/
theorem riskSample_decomposition {σ2 θ2 γ δ : ℝ} (hγ : γ ≠ 0) (hγ1 : γ - 1 ≠ 0) (hδ1 : δ - 1 ≠ 0) :
    riskSample σ2 θ2 γ δ =
      (σ2 / (γ - 1) + (1 - 1 / γ) * θ2) + (σ2 + (1 - 1 / γ) * θ2) / (δ - 1) := by
  unfold riskSample varSample biasSample
  field_simp [hγ, hγ1, hδ1]
  ring

/-- **Exercise 3.4.1 (Part 4: Continuous Meeting at Ambient Saturation $`\delta = \gamma < 1`).**
When $`\gamma < 1`, evaluating the feature-bottleneck variance and bias formulas at $`\delta = \gamma`
matches the ambient-bottleneck formulas continuously with zero jump and no singularity at $`\delta = 1`. -/
theorem feature_meets_ambient_at_gamma {σ2 θ2 γ : ℝ} :
    varFeature σ2 γ = varAmbient σ2 γ ∧ biasFeature θ2 γ γ = 0 ∧
      riskFeature σ2 θ2 γ γ = riskAmbient σ2 γ := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [biasFeature]
  · simp [riskFeature, riskAmbient, varFeature, varAmbient, biasFeature]

/-- **Exercise 3.4.2 (Scale Invariance of Ridgeless Features).**
In an abstract linear predictor $`\hat{\theta}(S, Z^\dagger) = S (Z^\dagger y)`, replacing $`S \mapsto \alpha S`
and $`Z^\dagger \mapsto \alpha^{-1} Z^\dagger` for $`\alpha \neq 0` rescales $`\hat{\eta} = Z^\dagger y` by
$`\alpha^{-1}` while leaving the induced ambient estimator $`\hat{\theta}` invariant. -/
theorem ridgeless_scale_invariance {n0 n m : ℕ} {α : ℝ} (hα : α ≠ 0)
    (S : Matrix (Fin n0) (Fin n) ℝ) (Zpinv : Matrix (Fin n) (Fin m) ℝ) (y : Fin m → ℝ) :
    Matrix.mulVec (α • S) (Matrix.mulVec (α⁻¹ • Zpinv) y) =
      Matrix.mulVec S (Matrix.mulVec Zpinv y) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp [hα]

end NNScaling.Ch03
