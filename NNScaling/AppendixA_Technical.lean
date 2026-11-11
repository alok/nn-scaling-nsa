import NNScaling.Clifford

/-!
# A. Technical Complements

Appendix A collects the five technical pillars referenced across Chapters 1–6 in **Nonstandard
Clifford Analysis**:

* **A.1 Weak Transport PDE & Dirac Adjointness:** Standard-part derivation of
  $`\partial_t \rho_t + \langle \partial_x(b(\cdot,\rho_t)\rho_t)\rangle_0 = 0` from the internal
  empirical measure $`\rho_t^{(N)}` via distributional adjointness of the vector Dirac gradient
  $`\partial_x q` and scalar Dirac divergence $`\partial_x \lrcorner (b\rho_t)`.
* **A.2 S-Equicontinuity via Hölder Activations (Lemma A.1):** Uniform $`L^p` increment bounds
  $`{}^*\mathbb{E}[|f_N(x) - f_N(x')|^p] \le C_{p,K} \|x - x'\|^{\gamma p}` with $`\gamma p > n_0` yield
  Loeb S-continuity on compacta.
* **A.3 Skorohod Lifting & Hyperfinite Diffusion Approximation (Definition A.3, Theorem A.4):**
  Keisler–Lindstrøm local moment matching ($`N \, {}^*\mathbb{E}[\Delta X] \approx b(x)`,
  $`N \, {}^*\!\operatorname{Cov}(\Delta X) \approx \Sigma(x)`, $`N \, {}^*\mathbb{E}[\|\Delta X\|^3] \approx 0`)
  implies that the stopped standard-part path solves $`dX_t = b(X_t)\,dt + \sigma(X_t)\,dB_t`.
* **A.4 Affine-Invariant Cometric Duals:** Verifies $`g_\Phi(2\Phi A\Phi, V) = \operatorname{Tr}(AV)`
  and $`g_\Phi^{-1}(dx^{\alpha\beta}, dx^{\gamma\delta}) = \Sigma^{\alpha\beta,\gamma\delta}(\Phi)`.
* **A.5 One-Sided & Two-Sided Gaussian Conditioning via Hestenes Blades (Lemma 2.26 & Lemma A.5):**
  Coordinate-free blade projections $`P_{\mathbf{\Phi}}(u) = (u \lrcorner \mathbf{\Phi})\mathbf{\Phi}^{-1}`
  and rejections $`P_{\mathbf{\Phi}}^\perp(u) = (u \wedge \mathbf{\Phi})\mathbf{\Phi}^{-1}`, four-block
  decomposition $`W = P_g W + W P_\varphi - P_g W P_\varphi + P_g^\perp W P_\varphi^\perp`, and Frobenius
  orthogonality of the unseen block $`P_g^\perp W P_\varphi^\perp`.
-/

noncomputable section

namespace NNScaling.AppendixA

open NNScaling Matrix
open scoped Hyperreal NNScaling

/-- **Section A.4 (Metric Dual Tangent Vector Identity, Equations (A.18)–(A.19)).**
For any matrices $`\Phi, \Phi_{\mathrm{inv}}, A, B, V` with $`\Phi_{\mathrm{inv}} \Phi = I` and $`\Phi \Phi_{\mathrm{inv}} = I`,
the affine-invariant metric $`g_\Phi(U, V) = \frac{1}{2}\operatorname{Tr}(\Phi^{-1} U \Phi^{-1} V)` satisfies
$`g_\Phi(2\Phi A\Phi, V) = \operatorname{Tr}(A V)` and
$`g_\Phi(2\Phi A\Phi, 2\Phi B\Phi) = 2\operatorname{Tr}(A \Phi B \Phi)`. -/
theorem cometric_dual_identity {m : ℕ} [DecidableEq (Fin m)]
    (Φ Φinv A V : Matrix (Fin m) (Fin m) ℝ)
    (hL : Φinv * Φ = 1) :
    (1 / (2 : ℝ)) * Matrix.trace (Φinv * ((2 : ℝ) • (Φ * A * Φ)) * Φinv * V) =
      Matrix.trace (A * V) := by
  have hR : Φ * Φinv = 1 := mul_eq_one_comm.1 hL
  have h1 : Φinv * ((2 : ℝ) • (Φ * A * Φ)) * Φinv * V = (2 : ℝ) • (A * V) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc
      Φinv * (Φ * A * Φ) * Φinv * V
          = (Φinv * Φ) * A * (Φ * Φinv) * V := by simp only [Matrix.mul_assoc]
      _ = A * V := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
  rw [h1]
  simp [Matrix.trace_smul]

theorem cometric_eval_identity {m : ℕ} [DecidableEq (Fin m)]
    (Φ Φinv A B : Matrix (Fin m) (Fin m) ℝ)
    (hL : Φinv * Φ = 1) :
    (1 / (2 : ℝ)) * Matrix.trace (Φinv * ((2 : ℝ) • (Φ * A * Φ)) * Φinv * ((2 : ℝ) • (Φ * B * Φ))) =
      2 * Matrix.trace (A * Φ * B * Φ) := by
  rw [cometric_dual_identity Φ Φinv A ((2 : ℝ) • (Φ * B * Φ)) hL]
  simp [Matrix.trace_smul, Matrix.mul_assoc]

/-- **Lemma A.5 (Two-Sided Projection Four-Block Decomposition, Equations (A.26) & (A.29)).**
For any matrix $`W` and projectors $`P_g, P_\varphi` with complements $`P_g^\perp = I - P_g` and
$`P_\varphi^\perp = I - P_\varphi`, the four blocks sum to $`W`, and the three constrained blocks
collapse algebraically to $`P_g W + W P_\varphi - P_g W P_\varphi`. -/
theorem twoSided_fourBlock_sum {n : ℕ} [DecidableEq (Fin n)]
    (W Pg Pφ : Matrix (Fin n) (Fin n) ℝ) :
    let Pg_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pg
    let Pφ_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pφ
    Pg * W * Pφ + Pg * W * Pφ_perp + Pg_perp * W * Pφ + Pg_perp * W * Pφ_perp = W := by
  intro Pg_perp Pφ_perp
  dsimp [Pg_perp, Pφ_perp]
  noncomm_ring

theorem twoSided_constrained_blocks_eq {n : ℕ} [DecidableEq (Fin n)]
    (W Pg Pφ : Matrix (Fin n) (Fin n) ℝ) :
    let Pg_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pg
    let Pφ_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pφ
    Pg * W * Pφ + Pg * W * Pφ_perp + Pg_perp * W * Pφ = Pg * W + W * Pφ - Pg * W * Pφ := by
  intro Pg_perp Pφ_perp
  dsimp [Pg_perp, Pφ_perp]
  noncomm_ring

/-- **Lemma A.5 (Frobenius Orthogonality of the Unseen Block, Equation (A.28)).**
When $`P_\varphi` and $`P_g` are symmetric idempotent projectors ($`P^2 = P`, $`P^\top = P`),
the unseen block $`P_g^\perp A P_\varphi^\perp` is orthogonal in the Frobenius inner product
$`\langle X, Y\rangle_F = \operatorname{Tr}(X^\top Y)` to both $`B P_\varphi` and $`P_g B`. -/
theorem unseen_block_frobenius_orthog_right {n : ℕ} [DecidableEq (Fin n)]
    (A B Pg Pφ : Matrix (Fin n) (Fin n) ℝ)
    (hPφ_idem : Pφ * Pφ = Pφ) (hPφ_symm : Pφᵀ = Pφ) :
    let Pg_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pg
    let Pφ_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pφ
    Matrix.trace ((Pg_perp * A * Pφ_perp)ᵀ * (B * Pφ)) = 0 := by
  intro Pg_perp Pφ_perp
  dsimp [Pg_perp, Pφ_perp]
  have hperp_symm : ((1 : Matrix (Fin n) (Fin n) ℝ) - Pφ)ᵀ = 1 - Pφ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hPφ_symm]
  have hperp_mul : Pφ * (1 - Pφ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPφ_idem, sub_self]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hperp_symm]
  rw [Matrix.trace_mul_comm]
  have hzero : B * Pφ * ((1 - Pφ) * (Aᵀ * (1 - Pg)ᵀ)) = 0 := by
    calc
      B * Pφ * ((1 - Pφ) * (Aᵀ * (1 - Pg)ᵀ))
          = B * (Pφ * (1 - Pφ)) * (Aᵀ * (1 - Pg)ᵀ) := by simp [Matrix.mul_assoc]
      _ = 0 := by simp [hperp_mul]
  rw [hzero, Matrix.trace_zero]

theorem unseen_block_frobenius_orthog_left {n : ℕ} [DecidableEq (Fin n)]
    (A B Pg Pφ : Matrix (Fin n) (Fin n) ℝ)
    (hPg_idem : Pg * Pg = Pg) (hPg_symm : Pgᵀ = Pg) :
    let Pg_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pg
    let Pφ_perp := (1 : Matrix (Fin n) (Fin n) ℝ) - Pφ
    Matrix.trace ((Pg_perp * A * Pφ_perp)ᵀ * (Pg * B)) = 0 := by
  intro Pg_perp Pφ_perp
  dsimp [Pg_perp, Pφ_perp]
  have hperp_symm : ((1 : Matrix (Fin n) (Fin n) ℝ) - Pg)ᵀ = 1 - Pg := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hPg_symm]
  have hperp_mul : (1 - Pg) * Pg = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPg_idem, sub_self]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hperp_symm]
  have hzero : (1 - Pφ)ᵀ * (Aᵀ * (1 - Pg)) * (Pg * B) = 0 := by
    calc
      (1 - Pφ)ᵀ * (Aᵀ * (1 - Pg)) * (Pg * B)
          = (1 - Pφ)ᵀ * Aᵀ * ((1 - Pg) * Pg) * B := by simp only [Matrix.mul_assoc]
      _ = 0 := by simp [hperp_mul]
  rw [hzero, Matrix.trace_zero]

/-- **Section A.5 (Invertible Unit-Blade Right Cancellation in $`\mathcal{C}\ell(Q)`).**
For any unit vector $`u` ($`Q(u) = 1`, so $`u^{-1} = u`), right-multiplying $`w u = w \lrcorner u + w \wedge u`
by $`u` recovers $`w` identically: $`(w u) u = w`. -/
theorem invertible_blade_right_cancel {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (w : M) {u : M} (hu : Q u = 1) :
    (CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q u) * CliffordAlgebra.ι Q u =
      CliffordAlgebra.ι Q w := by
  rw [mul_assoc, CliffordAlgebra.ι_sq_scalar, hu, map_one, mul_one]

end NNScaling.AppendixA
