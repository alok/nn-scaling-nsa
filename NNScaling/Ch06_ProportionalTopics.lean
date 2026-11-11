import NNScaling.Clifford

/-!
# 6. Further Topics in Proportional Depth–Width Scaling

Chapter 6 develops three applications of proportional hyperfinite depth–width scaling
($`D, N \in {}^*\mathbb{N} \setminus \mathbb{N}` with $`\operatorname{st}(D/N) = \bar{\tau} \in (0,\infty)`)
in **Nonstandard Clifford Analysis**:

1. **Shaped Transformers & Key–Query Multivectors (Section 6.1):** Decomposing $`k^\alpha q^\beta = \langle k^\alpha q^\beta\rangle_0 + k^\alpha \wedge q^\beta \in {}^*\mathcal{C}\ell_{n_k}`
   shows how standard Softmax logits retain the scalar inner part while discarding the token-plane bivector;
   temperature scaling $`s = s_0\sqrt{N n_k}`, uniform centering, and an identity shift produce
   $`A_\ell^s = I_m + \operatorname{Softmax}(s^{-1} S_\ell) - \frac{1}{m}\mathbf{1}\mathbf{1}^\top`,
   preventing rank collapse and yielding a covariance SDE shadow (**Theorem 6.4**).
2. **Spectrum of the Linear Covariance SDE & $`\operatorname{Spin}(m)` Repulsion (Section 6.2):**
   Congruence invariance of $`g_\Phi(A, B) = \frac{1}{2}\operatorname{Tr}(\Phi^{-1} A \Phi^{-1} B)`
   (**Proposition 6.8**) and two-sided spinor rotor evolution $`u_k(\tau) = R_\tau e_k R_\tau^{\sim}`
   with $`R_\tau \in \operatorname{Spin}(m) \subset \mathcal{C}\ell_m^+` ($`(e_i \wedge e_j)^2 = -1`)
   yield Geometric Dyson Brownian Motion (**Theorem 6.9**), while the $`\mathcal{C}\ell_2^+` Cauchy–Dirac
   kernel yields the inviscid Burgers PDE $`\partial_\tau G_\tau = -z G_\tau \partial_z G_\tau` and free
   log-normal fixed point (**Theorem 6.11**).
3. **One Step of Feature Learning in the Proportional Limit (Section 6.3):** In a deep linear network,
   the forward–backward overlap $`Q_\ell = \frac{1}{\sqrt{N}}\langle h_\ell g_\ell^{\sim}\rangle_0` is
   _exact_ depth-invariant, the updated feature kernel satisfies $`\Phi_\ell^+ - \Phi_\ell = 2 R_\ell^h + \dot{\Phi}_\ell`,
   and the telescoping prediction update $`f^+ - f = R_D^g = -\eta r \sum_{\ell=1}^{D-1} (\Phi_\ell + R_\ell^h) G_{\ell+1}`
   isolates the non-NTK layer-interaction term $`R_\ell^h G_{\ell+1}` (**Theorem 6.16**).
-/

noncomputable section

namespace NNScaling.Ch06

open NNScaling Matrix BigOperators Finset
open scoped Hyperreal NNScaling

/-- **Definition 6.1 (Column-Stochastic Property of Shaped Attention, Equation (6.8)).**
For any column-stochastic matrix $`P` ($`\sum_\alpha P_{\alpha\beta} = 1` for every query column $`\beta`),
the shaped attention matrix $`A_{\alpha\beta}^s = \delta_{\alpha\beta} + P_{\alpha\beta} - \frac{1}{m}` still has
every column summing to $`1`. -/
theorem shapedAttention_colSum_eq_one {m : ℕ} (hm : m ≠ 0)
    (P : Fin m → Fin m → ℝ) (hP : ∀ β, ∑ α : Fin m, P α β = 1) (β : Fin m) :
    (∑ α : Fin m, ((if α = β then (1 : ℝ) else 0) + P α β - 1 / (m : ℝ))) = 1 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [hP β, hmR]

/-- **Lemma 6.3 (Algebraic Core of the Uniform-Point Softmax Expansion, Equation (6.12)).**
The second-order Taylor ratio $`(1 + a + b) \cdot (1 - c - d + c^2)` matches
$`1 + (a - c) + (b - d - c(a - c))` up to third-order terms; for $`a = r_\alpha/s`, $`b = r_\alpha^2/(2s^2)`,
$`c = \bar{r}/s`, and $`d = \overline{r^2}/(2s^2)`, the quadratic numerator identity is
$`r_\alpha^2 - \overline{r^2} - 2\bar{r}(r_\alpha - \bar{r}) = (r_\alpha - \bar{r})^2 - (\overline{r^2} - \bar{r}^2)`. -/
theorem softmax_quadratic_numerator_identity (rα rbar r2bar : ℝ) :
    rα ^ 2 - r2bar - 2 * rbar * (rα - rbar) = (rα - rbar) ^ 2 - (r2bar - rbar ^ 2) := by
  ring

/-- **Proposition 6.8 (Congruence Invariance of the Affine-Invariant Metric on $`\operatorname{SPD}(m)`, Equations (6.40)–(6.41)).**
For invertible matrices $`\Phi` and $`P`, with $`\Phi' = P \Phi P^\top` and inverse $`(\Phi')^{-1} = P^{-\top} \Phi^{-1} P^{-1}`,
the trace metric $`\frac{1}{2}\operatorname{Tr}(\Phi^{-1} A \Phi^{-1} B)` is invariant under
$`(\Phi, A, B) \mapsto (P\Phi P^\top, P A P^\top, P B P^\top)`. -/
theorem affineInvariantMetric_congruence {m : ℕ} [DecidableEq (Fin m)]
    (Φinv P Pinv A B : Matrix (Fin m) (Fin m) ℝ)
    (hP : Pinv * P = 1) (hPt : Pᵀ * Pinvᵀ = 1) :
    let Φ'_inv := Pinvᵀ * Φinv * Pinv
    let A' := P * A * Pᵀ
    let B' := P * B * Pᵀ
    (1 / (2 : ℝ)) * Matrix.trace (Φ'_inv * A' * Φ'_inv * B') =
      (1 / (2 : ℝ)) * Matrix.trace (Φinv * A * Φinv * B) := by
  intro Φ'_inv A' B'
  congr 1
  dsimp [Φ'_inv, A', B']
  have h1 : Pinvᵀ * Φinv * Pinv * (P * A * Pᵀ) = Pinvᵀ * (Φinv * A) * Pᵀ := by
    calc
      Pinvᵀ * Φinv * Pinv * (P * A * Pᵀ)
          = Pinvᵀ * Φinv * (Pinv * P) * A * Pᵀ := by simp [Matrix.mul_assoc]
      _ = Pinvᵀ * (Φinv * A) * Pᵀ := by simp [hP, Matrix.mul_assoc]
  have h2 : Pinvᵀ * (Φinv * A) * Pᵀ * (Pinvᵀ * Φinv * Pinv) * (P * B * Pᵀ) =
      Pinvᵀ * (Φinv * A * Φinv * B) * Pᵀ := by
    calc
      Pinvᵀ * (Φinv * A) * Pᵀ * (Pinvᵀ * Φinv * Pinv) * (P * B * Pᵀ)
          = Pinvᵀ * (Φinv * A) * (Pᵀ * Pinvᵀ) * Φinv * (Pinv * P) * B * Pᵀ := by
            simp [Matrix.mul_assoc]
      _ = Pinvᵀ * (Φinv * A * Φinv * B) * Pᵀ := by
            simp [hPt, hP, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPt, Matrix.one_mul]

/-- **Theorem 6.11 Proof Sketch (Symmetric Burgers Kernel Identity, Equation (6.57)).**
For $`f_z(x) = \frac{x}{z - x}` with $`f_z'(x) = \frac{z}{(z - x)^2}` and $`\partial_z f_z(x) = -\frac{x}{(z - x)^2}`,
we have the exact algebraic identity
$`x y \frac{f_z'(x) - f_z'(y)}{x - y} = -z (f_z(x)\,\partial_z f_z(y) + f_z(y)\,\partial_z f_z(x))`. -/
theorem burgers_symmetric_kernel_identity {x y z : ℝ}
    (hx : z - x ≠ 0) (hy : z - y ≠ 0) (hxy : x - y ≠ 0) :
    let fz := fun u => u / (z - u)
    let dfz_dx := fun u => z / (z - u) ^ 2
    let dfz_dz := fun u => -u / (z - u) ^ 2
    x * y * ((dfz_dx x - dfz_dx y) / (x - y)) =
      -z * (fz x * dfz_dz y + fz y * dfz_dz x) := by
  intro fz dfz_dx dfz_dz
  dsimp [fz, dfz_dx, dfz_dz]
  field_simp [hx, hy, hxy]
  ring

/-- **Section 6.2.5 (Small-$`\tau` Marchenko–Pastur Spectral Edges, Equations (6.61)–(6.62)).**
With $`\lambda_\pm = (\sqrt{1 + \tau} \pm \sqrt{\tau})^2` for $`\tau \ge 0`, the quadratic discriminant
$`(z - 1)^2 - 4 z \tau` factors exactly as $`(z - \lambda_-)(z - \lambda_+)`. -/
theorem small_tau_discriminant_factorization {z τ : ℝ} (hτ : 0 ≤ τ) :
    let lam_minus := (Real.sqrt (1 + τ) - Real.sqrt τ) ^ 2
    let lam_plus := (Real.sqrt (1 + τ) + Real.sqrt τ) ^ 2
    (z - 1) ^ 2 - 4 * z * τ = (z - lam_minus) * (z - lam_plus) := by
  intro lam_minus lam_plus
  dsimp [lam_minus, lam_plus]
  have h1 : 0 ≤ 1 + τ := by linarith
  have hsq1 : Real.sqrt (1 + τ) ^ 2 = 1 + τ := Real.sq_sqrt h1
  have hsq2 : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ
  calc
    (z - 1) ^ 2 - 4 * z * τ
        = z ^ 2 - 2 * z * (1 + 2 * τ) + 1 := by ring
    _ = z ^ 2 - 2 * z * (Real.sqrt (1 + τ) ^ 2 + Real.sqrt τ ^ 2) +
          (Real.sqrt (1 + τ) ^ 2 - Real.sqrt τ ^ 2) ^ 2 := by
          rw [hsq1, hsq2]
          ring
    _ = (z - (Real.sqrt (1 + τ) - Real.sqrt τ) ^ 2) *
          (z - (Real.sqrt (1 + τ) + Real.sqrt τ) ^ 2) := by ring

/-- **Section 6.3.1 (Exact Depth-Invariance of Forward–Backward Overlap $`Q_\ell`, Equation (6.70)).**
When $`h_{\ell+1} = \frac{1}{\sqrt{N}} W_\ell h_\ell` and $`g_\ell = \frac{1}{\sqrt{N}} W_\ell^\top g_{\ell+1}`,
the scalar overlap $`Q_\ell = \frac{1}{\sqrt{N}}\langle h_\ell, g_\ell\rangle` satisfies $`Q_{\ell+1} = Q_\ell`
identically at every finite or hyperfinite width $`N`. -/
theorem overlap_Q_depth_invariant {N : ℕ} (rtN : ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (hℓ gℓ1 : Fin N → ℝ) :
    let hℓ1 := (rtN⁻¹) • (W *ᵥ hℓ)
    let gℓ := (rtN⁻¹) • (Wᵀ *ᵥ gℓ1)
    (rtN⁻¹) * dotProduct hℓ1 gℓ1 = (rtN⁻¹) * dotProduct hℓ gℓ := by
  intro hℓ1 gℓ
  dsimp [hℓ1, gℓ]
  rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **Section 6.3.2 (Exact One-Step Feature Kernel Change, Equation (6.84)).**
With $`h_\ell^+ = h_\ell + \Delta h_\ell`, $`\Phi_\ell = \frac{1}{N}\|h_\ell\|^2`,
$`R_\ell^h = \frac{1}{N}\langle \Delta h_\ell, h_\ell\rangle`, and $`\dot{\Phi}_\ell = \frac{1}{N}\|\Delta h_\ell\|^2`,
we have $`\Phi_\ell^+ - \Phi_\ell = 2 R_\ell^h + \dot{\Phi}_\ell`. -/
theorem kernel_one_step_change {N : ℕ} (hℓ Δhℓ : Fin N → ℝ) :
    ((1 / (N : ℝ)) * ∑ i : Fin N, (hℓ i + Δhℓ i) ^ 2) -
      ((1 / (N : ℝ)) * ∑ i : Fin N, (hℓ i) ^ 2) =
      2 * ((1 / (N : ℝ)) * ∑ i : Fin N, Δhℓ i * hℓ i) +
        ((1 / (N : ℝ)) * ∑ i : Fin N, (Δhℓ i) ^ 2) := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have h1 :
      2 * ((1 / (N : ℝ)) * ∑ i : Fin N, Δhℓ i * hℓ i) +
        ((1 / (N : ℝ)) * ∑ i : Fin N, (Δhℓ i) ^ 2) =
        (1 / (N : ℝ)) * ∑ i : Fin N, (2 * (Δhℓ i * hℓ i) + (Δhℓ i) ^ 2) := by
    rw [Finset.sum_add_distrib, mul_add, ← mul_assoc, mul_comm 2, mul_assoc, Finset.mul_sum]
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Section 6.3.2 (Telescoping Prediction Update with Layer Interaction, Equations (6.87) & (6.105)).**
If $`R_1^g = 0` and $`R_{\ell+1}^g - R_\ell^g = -\eta r (\Phi_\ell + R_\ell^h) G_{\ell+1}` for $`1 \le \ell \le D - 1`,
then $`R_D^g = -\eta r \sum_{\ell=1}^{D-1} (\Phi_\ell + R_\ell^h) G_{\ell+1}`. -/
theorem overlap_Rg_telescope :
    ∀ (d_minus1 : ℕ) (Rg Φ Rh G_next : ℕ → ℝ) (η r : ℝ),
      Rg 0 = 0 →
      (∀ k < d_minus1, Rg (k + 1) - Rg k = -η * r * (Φ k + Rh k) * G_next k) →
      Rg d_minus1 = -η * r * ∑ k ∈ Finset.range d_minus1, (Φ k + Rh k) * G_next k := by
  intro d_minus1
  induction d_minus1 with
  | zero =>
    intro Rg Φ Rh G_next η r h0 _
    simp [h0]
  | succ n ih =>
    intro Rg Φ Rh G_next η r h0 hstep
    have hprev := ih Rg Φ Rh G_next η r h0 (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hlast := hstep n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ, mul_add]
    linarith

/-- **Theorem 6.9 ($`\operatorname{Spin}(m)` Rotor Repulsion Drift Balance).**
In the instantaneous eigenframe $`u_k(\tau) = R_\tau e_k R_\tau^{\sim}` ($`R_\tau \in \operatorname{Spin}(m)`),
the second-order sandwich expansion from $`(e_i \wedge e_j)^2 = -1` relates the diagonal drift to
the squared angular-velocity variance $`d\omega_{ij}^2 = \frac{\lambda_i \lambda_j}{(\lambda_i - \lambda_j)^2}\,d\tau`
via $`d\lambda_i - (\lambda_i - \lambda_j)\,d\omega_{ij}^2 = 0`, forcing the repulsive Dyson drift
$`d\lambda_i = \frac{\lambda_i \lambda_j}{\lambda_i - \lambda_j}\,d\tau`. -/
theorem spin_eigenframe_repulsion_balance {lami lamj dlami dω_sq dτ : ℝ}
    (hgap : lami - lamj ≠ 0)
    (hdΦii : dlami - (lami - lamj) * dω_sq = 0)
    (hdω : dω_sq = (lami * lamj / (lami - lamj) ^ 2) * dτ) :
    dlami = (lami * lamj / (lami - lamj)) * dτ := by
  have h1 : dlami = (lami - lamj) * dω_sq := sub_eq_zero.1 hdΦii
  rw [h1, hdω]
  field_simp [hgap]

end NNScaling.Ch06
