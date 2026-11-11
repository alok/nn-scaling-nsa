# Coverage Matrix — Stage 1 (Nonstandard Analysis Edition)

This document maps every chapter, section, theorem/proposition/lemma, figure, table, and exercise of Mufan Li's 98-page *Lecture Notes on Neural Network Scaling Limits* (STAT 946, University of Waterloo) to:

1. **LaTeX Monograph (`tex/` → `pdf/nn_scaling_nsa.pdf`):** Full 1-to-1 rewrite preserving Mufan Li's prose, narrative structure, theorem numbering, equation numbering, figures, tables, and exercises while reformulating every asymptotic scaling limit inside Robinson's $\aleph_1$-saturated enlargement $({}^*\mathbb{R}, {}^*\mathbb{N})$ and Loeb probability spaces $(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))$.
2. **Lean 4 / Verso Formalization (`NNScaling/`):** Machine-checked formalization (`v4.35.0`, zero custom `axiom`s, zero `sorry`s) of the hyperreal scale algebra ($\mathbb{L}, \mathbb{I}, \mathbb{A}, \operatorname{st}$) and the core algebraic, calculus, matrix-projection, and differential identities underpinning every chapter.

---

## Global NSA Dictionary (`NNScaling/Foundations.lean` & `tex/preamble.tex`)

| Classical Asymptotic Concept | Nonstandard Analysis Formulation | Lean 4 Symbol (`NNScaling/Foundations.lean`) |
|---|---|---|
| Sequential scales $n \to \infty$, $d \to \infty$, $m \to \infty$ | Unlimited hypernaturals $N, D, M \in {}^*\mathbb{N} \setminus \mathbb{N}$ | `Unlimited` |
| $O(1)$ / bounded in scale | Limited ring $\mathbb{L} = \{x \in {}^*\mathbb{R} : \exists C \in \mathbb{R},\, \lvert x\rvert \le C\}$ | `Limited`, `Limited.add`, `Limited.mul` |
| $o(1)$ / vanishing error | Infinitesimal ideal $\mathbb{I}$, $x \approx y \iff x - y \in \mathbb{I}$ | `IsInfinitesimal`, `InfClose` (`≊`) |
| $\Theta(1)$ / $\asymp 1$ | Appreciable group $\mathbb{A} = \mathbb{L} \setminus \mathbb{I}$, $x \asymp y \iff x/y \in \mathbb{A}$ | `Appreciable`, `ScaleEq` (`≍ₛ`) |
| Pointwise / $O_{\mathbb{P}}(N^{-\alpha})$ limit | Standard-part homomorphism $\operatorname{st} : \mathbb{L} \to \mathbb{R}$ & Loeb shadow $X \stackrel{L({}^*\mathbb{P})}{\approx} x$ | `st`, `st_add`, `st_mul`, `st_div`, `LoebNear` |
| Proportional scaling $d/n \to \bar{\tau}$, $n_0/m \to \gamma$, $n/m \to \delta$ | Appreciable hyperfinite ratios $\operatorname{st}(D/N) = \bar{\tau}$, $\operatorname{st}(N_0/M) = \gamma$, $\operatorname{st}(N/M) = \delta$ | `wishart_trace_st_feature`, `dmft_time_rescaling` |

---

## Chapter-by-Chapter Coverage

### Chapter 1 — Introduction (`tex/ch01_intro.tex`, `NNScaling/Ch01_Introduction.lean`)

| Source Section / Item | Monograph Coverage (`tex/ch01_intro.tex`) | Lean 4 / Verso (`NNScaling/Ch01_Introduction.lean`) |
|---|---|---|
| 1.1 Empirical Scaling Laws & Fig 1.1–1.2, Eq `(1.1)` | Hyperfinite power-law decomposition $L(N,D) = E + A N^{-\alpha} + B D^{-\beta} + \varepsilon(N,D)$, microscopic blowup $N^{\alpha}(L(N,\infty) - E) \approx A$; TikZ Fig 1.1 & vector Fig 1.2 | `ScalingLawExpansion`, `ScalingLawExpansion.st_eq`, `ScalingLawExpansion.microscope_st`, `ScalingLawExpansion.scaleEq` |
| 1.2 Classical Prototypes: CLT & Berry–Esseen, Fig 1.3, Def 1.1, Thm 1.2, Rem 1.3 | Hyperfinite normalized sum $S_N$ with step variance $1/N \in \mathbb{I}$, Loeb Gaussian shadow $\operatorname{st}(S_N) \sim \mathcal{N}(0,1)$, transfer of Berry–Esseen $N^{-1/2}\mathbb{L}$ bound; exact CF-inverted vector Fig 1.3 | `clt_step_variance_infinitesimal` |
| 1.2 Wigner Semicircle Law, Thm 1.4, Rem 1.5–1.6, Eqs `(1.6)`–`(1.11)` | Hyperfinite symmetric Wigner matrix $X_N = W/\sqrt{N}$, Loeb empirical spectral shadow $\mu_{\mathrm{sc}}$, non-commuting iterated limits via Robinson's Overspill ($M \ll N$ vs $M \gg N$) | `wignerSemicircleDensity`, `wignerSemicircleDensity_nonneg`, `wignerSemicircleDensity_eq_zero_of_abs_ge` |
| 1.3 Roadmap & Notation (`tex/notation.tex`) | Full chapter-by-chapter regime classification + two-page `xltabular` Notation table | Module docstrings across `NNScaling` |

### Chapter 2 — Kernel Limits for Wide Networks: NNGP and NTK (`tex/ch02_kernels.tex`, `NNScaling/Ch02_Kernels.lean`)

| Source Section / Item | Monograph Coverage (`tex/ch02_kernels.tex`) | Lean 4 / Verso (`NNScaling/Ch02_Kernels.lean`) |
|---|---|---|
| 2.1 Shallow NNGP (Setup 2.1, Thm 2.2, Prop 2.3, Rem 2.4, Prop 2.5, Rem 2.6, Eqs `(2.1)`–`(2.19)`) | Conditional internal Gaussianity at width $N \in {}^*\mathbb{N}\setminus\mathbb{N}$, Loeb LLN $\Phi^{(N)} \approx \Phi$, Cho–Saul ReLU arc-cosine kernel $J_1(\vartheta)$ and derivative kernel | `gram_quadForm_nonneg`, `choSaulDeriv`, `choSaulDeriv_zero`, `choSaulDeriv_one`, `choSaulDeriv_neg_one` |
| 2.2 Deep NNGP (Setup 2.7, Thm 2.8, Prop 2.9–2.10, Rem 2.11, Cor 2.12, Rem 2.13, Eqs `(2.20)`–`(2.37)`) | Layerwise internal Gaussian conditioning on $\mathcal{F}_\ell$, S-continuity lifting $\Phi_\ell^{(N)} \approx \Phi_\ell$, GP posterior regression | Documented in literate narrative + Gram PSD lemmas |
| 2.3–2.4 NTK Regime & Lazy Training (Setup 2.14, Prop 2.15, Rem 2.16, Prop 2.17–2.18, Def 2.19, Thm 2.20, Rem 2.21, Prop 2.22, Rem 2.23, Eqs `(2.38)`–`(2.61)`) | Internal gradient flow on $[0, {}^*t]$, mean-square neuron displacement $\le t L(\theta_0)/N \approx 0$, Taylor stationarity $K_s^{(N)} \approx K_0^{(N)} \approx K$, standard-part exponential eigenmode decay | `empiricalNTK`, `residual_velocity_eq`, `risk_dissipation_nonpos`, `fixed_kernel_loss_bound`, `ntk_displacement_infinitesimal` |
| 2.5 Deep MLP NTK Recursion (Setup 2.24, Prop 2.25, Lem 2.26, Prop 2.27, Thm 2.28, Rem 2.29, Eqs `(2.62)`–`(2.91)`) | Rank-one layerwise gradient Frobenius factorization, one-sided Gaussian weight conditioning $W_\ell \stackrel{d}{=} \widetilde{W}_\ell + (\widetilde{Z}_\ell - \widetilde{W}_\ell\varphi_\ell)\varphi_\ell^\dagger$, forward/backward kernel recursion | `rankOne_frobenius_product` |
| 2.6 Exercises 1–5 | All 5 exercises preserved with hyperfinite width $N$ formulations | Covered in `Ch02_Kernels.lean` |

### Chapter 3 — Double Descent with Random Projections (`tex/ch03_double_descent.tex`, `NNScaling/Ch03_DoubleDescent.lean`)

| Source Section / Item | Monograph Coverage (`tex/ch03_double_descent.tex`) | Lean 4 / Verso (`NNScaling/Ch03_DoubleDescent.lean`) |
|---|---|---|
| 3.1–3.2 Setup & Exact Bias–Variance Decomposition, Eqs `(3.1)`–`(3.13)` | Proportionally unlimited triple $(M, N_0, N) \in ({}^*\mathbb{N}\setminus\mathbb{N})^3$ with $\gamma = \operatorname{st}(N_0/M)$, $\delta = \operatorname{st}(N/M)$; Moore–Penrose minimum-norm interpolator | `varFeature`, `biasFeature`, `riskFeature`, `varAmbient`, `riskAmbient`, `varSample`, `biasSample`, `riskSample` |
| 3.3 Thm 3.1, Fig 3.1, Lemmas 3.2–3.5, Rem 3.6–3.8, Eqs `(3.14)`–`(3.62)` | Exact internal inverse-Wishart trace $N/(M-N-1) \approx \delta/(1-\delta)$, unlimited spike at $M - N \in \mathbb{N}$, rotational symmetry via orthogonal invariance; vector Fig 3.1 | `wishart_trace_st_feature`, `feature_bias_amplification`, `sample_bias_amplification` |
| 3.4 Exercises 1–3 | All 3 exercises preserved verbatim in structure | `riskFeature_strictMono`, `riskSample_strictAnti`, `riskSample_decomposition`, `feature_meets_ambient_at_gamma`, `ridgeless_scale_invariance` |

### Chapter 4 — Feature Learning and Mean-Field Limits (`tex/ch04_feature_learning.tex`, `NNScaling/Ch04_FeatureLearning.lean`)

| Source Section / Item | Monograph Coverage (`tex/ch04_feature_learning.tex`) | Lean 4 / Verso (`NNScaling/Ch04_FeatureLearning.lean`) |
|---|---|---|
| 4.1–4.3 Mean-Field Parametrization, Continuity Equation, Wasserstein Flow (Setup 4.1, Rem 4.2–4.3, Def 4.4, Thm 4.5, Rem 4.6, Prop 4.7, Eqs `(4.1)`–`(4.38)`) | $1/N$-scaled readout vs $1/\sqrt{N}$ NTK, Loeb pushforward empirical measure $\rho_t = L(\mu_{{}^*t}^{(N)}) \circ \operatorname{st}^{-1}$, propagation of chaos on McKean–Vlasov reference particles, Otto–Wasserstein dissipation | `shallow_normalized_ntk_eq_d1` |
| 4.4–4.6 Why Depth Changes Scaling, $\mu$P, DMFT (Rem 4.8, Tables 4.1–4.2, Eqs `(4.39)`–`(4.63)`) | Appreciable feature-update condition $\frac{1}{N}\lVert\Delta h_\ell\rVert^2 \in \mathbb{A}$ and appreciable output-drift condition $\Delta f \in \mathbb{A}$ uniquely selecting $\gamma_N \asymp \sqrt{N}, \eta_N \asymp N$; DMFT correlation/response kernels | `featureUpdateExp`, `predictorSpeedExp`, `mup_exponent_balance_iff`, `ntk_lazy_exponents`, `naive_large_lr_exponents`, `hyperreal_mup_scale_solution`, `dmft_time_rescaling` |
| 4.7 Exercises 1–3 | All 3 exercises ($\mu$P exponent balance, shallow normalized NTK, DMFT rescaling) | All 3 exercises proved completely in `Ch04_FeatureLearning.lean` |

### Chapter 5 — Depth Scaling and Covariance SDE Limits (`tex/ch05_depth_sde.tex`, `NNScaling/Ch05_DepthSDE.lean`)

| Source Section / Item | Monograph Coverage (`tex/ch05_depth_sde.tex`) | Lean 4 / Verso (`NNScaling/Ch05_DepthSDE.lean`) |
|---|---|---|
| 5.1–5.2 ResNet ODE & SDE Limits (Def 5.1, Prop 5.2, Def 5.3, Prop 5.4, Fig 5.1, Eqs `(5.1)`–`(5.22)`) | Hyperfinite Euler grid $\mathbb{T}_D$ with $\eta = T/D \approx 0$, internal Grönwall shadow, Anderson's hyperfinite Brownian motion $B_\tau = \operatorname{st}(\widetilde{W}_{\lfloor \tau D/T\rfloor})$, Keisler–Lindstrøm SDE theorem; TikZ Fig 5.1 | `isserlisTensor`, `isserlisTensor_symm_pair`, `isserlisTensor_symm_swap` |
| 5.3–5.5 Linear/ReLU GBM, Shaped MLPs, Multi-Input Covariance SDE (Prop 5.5, Rem 5.6, Prop 5.7–5.8, Thm 5.9, Rem 5.10–5.14, Eqs `(5.23)`–`(5.79)`) | Proportional hyperfinite regime $\operatorname{st}(D/N) = \bar{\tau} \in (0,\infty)$, $\sigma = \sqrt{2}$ (linear) and $\sigma = \sqrt{5}$ (ReLU) log-GBM drifts, $N^{-1/2}$ activation shaping, finite-time blowup ODE | `isserlisTensor_one_sample`, `wick_fourth_moment_centered_var`, `gbmLogDrift`, `linear_gbm_log_drift`, `relu_gbm_log_drift`, `smooth_shaping_drift_one_sample`, `logisticCovODE`, `logisticCovODE_zero`, `logisticCovODE_blowup_denom_zero`, `logisticCovODE_hasDerivAt` |

### Chapter 6 — Further Topics in Proportional Depth–Width Scaling (`tex/ch06_proportional_topics.tex`, `NNScaling/Ch06_ProportionalTopics.lean`)

| Source Section / Item | Monograph Coverage (`tex/ch06_proportional_topics.tex`) | Lean 4 / Verso (`NNScaling/Ch06_ProportionalTopics.lean`) |
|---|---|---|
| 6.1 Shaped Attention & Transformers (Setup 6.1, Prop 6.2, Thm 6.3, Rem 6.4–6.5, Eqs `(6.1)`–`(6.30)`) | Centered identity-centered attention $A_\ell = I_m + \tau^{1/2}\widetilde{A}_\ell$ at $\tau = \gamma^2/N \approx 0$, $\operatorname{Softmax}$ Taylor expansion around uniform weights, token covariance SDE | `shapedAttention`, `shapedAttention_colSum_eq_one`, `softmax_quadratic_numerator_identity` |
| 6.2 Spectrum of Feature Covariance (Setup 6.6, Thm 6.7, Prop 6.8, Thm 6.9–6.11, Cor 6.12, Rem 6.13–6.14, Eqs `(6.31)`–`(6.62)`) | Affine-invariant metric on $\operatorname{SPD}(m)$, intrinsic BM & Geometric Dyson BM eigenvalue repulsion, hyperfinite token count $M \in {}^*\mathbb{N}\setminus\mathbb{N}$ inviscid Burgers PDE for $T_\tau(z)$ and small-$\tau$ Marchenko–Pastur recovery | `affineInvariantMetric_congruence`, `burgers_symmetric_kernel_identity`, `small_tau_discriminant_factorization` |
| 6.3 One-Step Feature Learning at Proportional Depth–Width (Setup 6.15, Rem 6.16, Eqs `(6.63)`–`(6.105)`) | Two-sided internal Gaussian conditioning (`Lemma A.5`) decoupling forward/backward passes, depth-invariance of $Q_\ell$, telescoping prediction update $R_D^g$ with multiplicative layer interaction | `overlap_Q_depth_invariant`, `kernel_one_step_change`, `overlap_Rg_telescope` |

### Appendix A — Technical Complements (`tex/appa_technical.tex`, `NNScaling/AppendixA_Technical.lean`)

| Source Section / Item | Monograph Coverage (`tex/appa_technical.tex`) | Lean 4 / Verso (`NNScaling/AppendixA_Technical.lean`) |
|---|---|---|
| A.1–A.3 Weak Convergence via Loeb Shadows, S-Equicontinuity, Skorohod Lifting (Props A.1–A.4, Eqs `(A.1)`–`(A.9)`) | Loeb pushforward characterization of Polish weak convergence, hyperfinite Arzelà–Ascoli via S-continuity, Aldous tightness via infinitesimal stopping-time increments | Builds on `Foundations.lean` |
| A.4 Intrinsic Brownian Motion on $\operatorname{SPD}(m)$ (Eqs `(A.10)`–`(A.22)`) | Symmetrized matrix Stratonovich/Itô differential, cometric dual $2\Phi A\Phi$, Laplace–Beltrami drift $\frac{m+1}{2}\Phi$ | `cometric_dual_identity`, `cometric_eval_identity` |
| A.5 Gaussian Conditioning via Projections (Lemma A.5, Eqs `(A.23)`–`(A.30)`) | One-sided and two-sided orthogonal projector four-block decomposition $W = P_g W + W P_\varphi - P_g W P_\varphi + P_g^\perp W P_\varphi^\perp$ and Frobenius orthogonality | `twoSided_fourBlock_sum`, `twoSided_constrained_blocks_eq`, `unseen_block_frobenius_orthog_right`, `unseen_block_frobenius_orthog_left` |
