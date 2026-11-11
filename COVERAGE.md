# Coverage Matrix — Stage 1 (`nsa`) & Stage 2 (`main`, Nonstandard Clifford Analysis)

This document maps every chapter, section, theorem/proposition/lemma, figure, table, and exercise of Mufan Li's 98-page *Lecture Notes on Neural Network Scaling Limits* (STAT 946, University of Waterloo) across both stages of our rewrite:

1. **Stage 1 — Pure Nonstandard Analysis (`nsa` bookmark, `pdf/nn_scaling_nsa.pdf`, 108 pages):** Full 1-to-1 rewrite preserving Mufan Li's prose, narrative structure, theorem numbering, equation numbering, figures, tables, and exercises while reformulating every asymptotic scaling limit inside Robinson's $\aleph_1$-saturated enlargement $({}^*\mathbb{R}, {}^*\mathbb{N})$ and Loeb probability spaces $(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))$.
2. **Stage 2 — Nonstandard Clifford Analysis (`main` bookmark, `pdf/nn_scaling_clifford.pdf`, 111 pages):** Built strictly on top of Stage 1, upgrading inner products, projections, Schur complements, gradient flows, Wasserstein continuity PDEs, key–query attention logits, and eigenvalue SDEs into Euclidean and hyperreal Clifford algebras $\mathcal{C}\ell_n(\mathbb{R})$, $\mathcal{C}\ell_n(\mathbb{L})$, and ${}^*\mathcal{C}\ell_N$.
3. **Lean 4 / Verso Formalization (`NNScaling/`):** Machine-checked formalization (`v4.35.0`, `autoImplicit = false`, **zero** custom `axiom`s, **zero** `sorry`s) of both the hyperreal scale algebra (`NNScaling/Foundations.lean`) and the hyperreal Clifford algebra & standard-part multivector homomorphism (`NNScaling/Clifford.lean`), together with chapter-by-chapter algebraic, differential, and geometric theorems.

---

## Global NSA & Clifford Dictionary (`NNScaling/Foundations.lean`, `NNScaling/Clifford.lean`, `tex/preamble.tex`)

| Classical Concept | Stage 1 (NSA) | Stage 2 (Nonstandard Clifford Analysis) | Lean 4 Symbol |
|---|---|---|---|
| Sequential scales $n, d, m \to \infty$ | Unlimited hypernaturals $N, D, M \in {}^*\mathbb{N} \setminus \mathbb{N}$ | Hyperfinite Clifford dimensions ${}^*\mathcal{C}\ell_N, {}^*\mathcal{C}\ell_{n_k}, {}^*\mathcal{C}\ell_{\dim(\theta)}$ | `Unlimited` |
| $O(1)$ / bounded in scale | Limited ring $\mathbb{L} \subset {}^*\mathbb{R}$ | Valuation subring $\mathbb{L}$ & $\mathcal{C}\ell_n(\mathbb{L})$ | `Limited`, `LimitedSubring` |
| $o(1)$ / vanishing error | Infinitesimal ideal $\mathbb{I}$, $x \approx y$ | Maximal ideal $\mathbb{I} \triangleleft \mathbb{L}$ | `IsInfinitesimal`, `InfinitesimalIdeal`, `InfClose` (`≊`) |
| $\Theta(1)$ / $\asymp 1$ | Appreciable group $\mathbb{A} = \mathbb{L} \setminus \mathbb{I}$ | Appreciable scalar norms $\frac{1}{N}\langle (\Delta h)^{\sim}\Delta h\rangle_0 \in \mathbb{A}$ | `Appreciable`, `ScaleEq` (`≍ₛ`) |
| Limit / shadow | Standard part $\operatorname{st} : \mathbb{L} \to \mathbb{R}$ | Multivector shadow homomorphism $\operatorname{st}_{\mathcal{C}\ell} : \mathcal{C}\ell_n(\mathbb{L}) \to \mathcal{C}\ell_n(\mathbb{R})$ | `st`, `stRingHom`, `ker_stRingHom`, `stCliffordHom` |
| Feature / gradient inner product | $\frac{1}{N}\langle u, v\rangle$ | Grade-$0$ reverse product $\frac{1}{N}\langle u v^{\sim}\rangle_0$ in ${}^*\mathcal{C}\ell_N$ | `clifford_vec_sq`, `clifford_symm_polar` |
| Planar rotation / spectral $i$ | $2\times 2$ rotation / $z \in \mathbb{C}$ | Even rotor $R = c + s\,\hat{B} \in \mathcal{C}\ell_2^+$ ($\hat{B}^2 = -1, \hat{B}^{\sim} = -\hat{B}$) | `unit_bivector_sq_neg_one`, `planarRotor_unit_norm`, `planarRotor_sandwich_e1` |
| Subspace projection $P_\phi, P_S$ | $\phi(\phi^\top\phi)^\dagger\phi^\top$ | Hestenes blade contraction $(w \lrcorner \bm{\Phi})\bm{\Phi}^{-1}$ & rejection $(w \wedge \bm{\Phi})\bm{\Phi}^{-1}$ | `contraction_leibniz`, `versor_reflection_isometry`, `invertible_blade_right_cancel` |
| Transport divergence $\nabla \cdot (v\rho)$ | $\partial_x(b\rho_t)$ / $\nabla_{(a,w)}\cdot(v_t\rho_t)$ | Scalar Dirac divergence $\langle \partial_\theta (v_t\rho_t)\rangle_0$ & curl-freeness $\langle \partial_\theta v_t\rangle_2 = 0$ | `monogenic_gradient_bivector_curl_zero` |

---

## Chapter-by-Chapter Coverage

### Foundations (`NNScaling/Foundations.lean` & `NNScaling/Clifford.lean`)

| Module | Formalized Content | Key Declarations |
|---|---|---|
| `NNScaling/Foundations.lean` | Hyperreal scale classes $\mathbb{L}, \mathbb{I}, \mathbb{A}$, monads, Dedekind `sSup` standard part $\operatorname{st}$, ring/quotient laws, Loeb probability interfaces | `Limited`, `Unlimited`, `IsInfinitesimal`, `Appreciable`, `InfClose`, `ScaleEq`, `st`, `Limited.infClose_st`, `st_add`, `st_mul`, `st_div`, `LoebSpace` |
| `NNScaling/Clifford.lean` | Valuation subring $\mathbb{L}$, ideal $\mathbb{I} = \ker(\operatorname{st})$, universal bivector/rotor identities, Hestenes contraction Leibniz rule, functorial scalar-change `cliffordChangeRingHom`, hyperreal Clifford shadow `stCliffordHom` | `LimitedSubring`, `InfinitesimalIdeal`, `stRingHom`, `ker_stRingHom`, `bivector_reverse_neg`, `unit_bivector_sq_neg_one`, `planarRotor_mul_reverse`, `planarRotor_unit_norm`, `planarRotor_sandwich_e1`, `versor_reflection_isometry`, `contraction_leibniz`, `euclideanQuadForm`, `stCliffordHom`, `stCliffordHom_infinitesimal_scalar`, `stCliffordHom_infinitesimal_vec` |

### Chapter 1 — Introduction (`tex/ch01_intro.tex`, `NNScaling/Ch01_Introduction.lean`)

| Source Section / Item | Stage 1 (NSA) & Stage 2 (Clifford) Monograph Coverage | Lean 4 / Verso (`NNScaling/Ch01_Introduction.lean`) |
|---|---|---|
| 1.1 Empirical Scaling Laws & Figs 1.1–1.2, Eq `(1.1)` | Hyperfinite power-law decomposition, infinitesimal microscope $s_N^{-1}(L_N - L_\infty) \approx c$; TikZ Fig 1.1 & vector Fig 1.2 | `ScalingLawExpansion`, `ScalingLawExpansion.st_eq`, `ScalingLawExpansion.microscope_st`, `ScalingLawExpansion.scaleEq` |
| 1.2 CLT, Wigner Semicircle, & Interacting Particles, Fig 1.3, Thms 1.2 & 1.4, Rems 1.5–1.6 | Loeb Gaussian & semicircle shadows; **Stage 2:** Cauchy–Dirac resolvent $(z - N^{-1/2}X)^{-1}$ in $\mathcal{C}\ell_2^+$ ($\bm{i} = e_1 e_2$) and scalar Dirac divergence $\langle \partial_x(b\rho_t)\rangle_0 = 0$ | `clt_step_variance_infinitesimal`, `wignerSemicircleDensity_nonneg`, `wignerSemicircleDensity_eq_zero_of_abs_ge`, `cauchy_dirac_resolvent_norm` |
| 1.3 Roadmap & Notation (`tex/notation.tex`) | Complete regime table + `xltabular` Notation table with both NSA and Clifford symbols ($\mathcal{C}\ell_k, {}^*\mathcal{C}\ell_N, M^{\sim}, \langle M\rangle_r, \lrcorner, \partial_\theta, \operatorname{Spin}(k)$) | Module docstrings across `NNScaling` |

### Chapter 2 — Kernel Limits for Wide Networks: NNGP and NTK (`tex/ch02_kernels.tex`, `NNScaling/Ch02_Kernels.lean`)

| Source Section / Item | Stage 1 (NSA) & Stage 2 (Clifford) Monograph Coverage | Lean 4 / Verso (`NNScaling/Ch02_Kernels.lean`) |
|---|---|---|
| 2.1–2.2 Shallow & Deep NNGP (Thms 2.3 & 2.13, Prop 2.5, Rem 2.8) | Conditional internal Gaussianity in ${}^*\mathcal{C}\ell_N$ via $\Phi^{(N),\alpha\beta} = \frac{1}{N}\langle {}^*\varphi(h^\alpha){}^*\varphi(h^\beta)^{\sim}\rangle_0$; **Stage 2:** Cho–Saul arc-cosine kernel via input-plane rotor $u_1 u_2 = \rho + \sqrt{1-\rho^2}\,\hat{B}$ | `gram_quadForm_nonneg`, `choSaulDeriv_zero`, `choSaulDeriv_one`, `choSaulDeriv_neg_one`, `choSaul_rotor_unit_norm` |
| 2.3–2.4 NTK Regime & Lazy Training (Props 2.15, 2.17, 2.22, Thm 2.20) | **Stage 2:** Dirac gradient decomposition $\rev{(\partial_\theta f_\alpha)}(\partial_\theta f_\beta) = K_t^{(N),\alpha\beta} + \Omega_t^{(N),\alpha\beta}$ in ${}^*\mathcal{C}\ell_{\dim(\theta)}$, vanishing of bivector curl $\Omega_t^{(N)}$ in risk dissipation, $O(N^{-1}) \subset \mathbb{I}$ lazy freezing | `empiricalNTK`, `residual_velocity_eq`, `risk_dissipation_nonpos`, `bivector_curl_quadForm_zero`, `fixed_kernel_loss_bound`, `ntk_displacement_infinitesimal` |
| 2.5–2.6 Deep MLP NTK & Conditioning (Prop 2.25, Lem 2.26, Thm 2.28, Exercises 1–5) | **Stage 2:** Hestenes blade projection $(w \lrcorner \bm{\Phi})\bm{\Phi}^{-1}$ and rejection $(w \wedge \bm{\Phi})\bm{\Phi}^{-1}$ in one-sided Gaussian conditioning | `rankOne_frobenius_product` |

### Chapter 3 — Double Descent with Random Projections (`tex/ch03_double_descent.tex`, `NNScaling/Ch03_DoubleDescent.lean`)

| Source Section / Item | Stage 1 (NSA) & Stage 2 (Clifford) Monograph Coverage | Lean 4 / Verso (`NNScaling/Ch03_DoubleDescent.lean`) |
|---|---|---|
| 3.1–3.3 Proportional Triple $(M, N_0, N)$, Thm 3.1, Lemmas 3.2–3.5, Fig 3.1 | **Stage 2:** Inverse-Wishart Schur complement as exterior wedge-blade volume ratio $\lVert g_1 \wedge \bm{G}_2\rVert^2 / \lVert \bm{G}_2\rVert^2$ exploding at pseudoscalar saturation $Q = P$; subspace blade $\bm{S} \in \bigwedge^N({}^*\mathbb{R}^{N_0})$ signal decomposition | `wishart_trace_st_feature`, `feature_bias_amplification`, `sample_bias_amplification`, `lagrange_bivector_wedge_norm`, `lagrange_bivector_schur_complement` |
| 3.4 Exercises 1–3 | Strict monotonicity before/after interpolation, $\delta\to\infty$ decomposition, continuous meeting at $\delta = \gamma < 1$, ridgeless scale invariance | `riskFeature_strictMono`, `riskSample_strictAnti`, `riskSample_decomposition`, `feature_meets_ambient_at_gamma`, `ridgeless_scale_invariance` |

### Chapter 4 — Feature Learning and Mean-Field Limits (`tex/ch04_feature_learning.tex`, `NNScaling/Ch04_FeatureLearning.lean`)

| Source Section / Item | Stage 1 (NSA) & Stage 2 (Clifford) Monograph Coverage | Lean 4 / Verso (`NNScaling/Ch04_FeatureLearning.lean`) |
|---|---|---|
| 4.1–4.3 Mean-Field Continuity PDE & Otto–Wasserstein Flow (Defs 4.1 & 4.4, Thm 4.5, Prop 4.7) | **Stage 2:** Parameter Dirac operator $\partial_\theta = e_a \partial_a + \sum_k e_k \partial_{w_k} \in \mathcal{C}\ell_{1+n_0}$ ($\partial_\theta^2 = \Delta_{(a,w)}$), continuity PDE $\partial_t \rho_t + \langle \partial_\theta(v_t\rho_t)\rangle_0 = 0$, monogenic curl-freeness $\langle \partial_\theta v_t\rangle_2 = 0$ | `shallow_normalized_ntk_eq_d1`, `monogenic_gradient_bivector_curl_zero` |
| 4.4–4.7 Deep $\mu$P, DMFT, Tables 4.1–4.2, Exercises 1–3 | **Stage 2:** Appreciable scalar-grade update $\frac{1}{N}\langle (\Delta h_\ell)^{\sim}\Delta h_\ell\rangle_0 \in \mathbb{A}$ uniquely selecting $(p,q) = (1/2, 1)$ | `mup_exponent_balance_iff`, `ntk_lazy_exponents`, `naive_large_lr_exponents`, `hyperreal_mup_scale_solution`, `dmft_time_rescaling` |

### Chapter 5 — Depth Scaling and Covariance SDE Limits (`tex/ch05_depth_sde.tex`, `NNScaling/Ch05_DepthSDE.lean`)

| Source Section / Item | Stage 1 (NSA) & Stage 2 (Clifford) Monograph Coverage | Lean 4 / Verso (`NNScaling/Ch05_DepthSDE.lean`) |
|---|---|---|
| 5.1–5.5 ResNet ODE/SDE, Proportional GBM, Isserlis Covariance SDE, Critical Shaping, Fig 5.1 | **Stage 2:** Clifford vector square $U_{\ell,N} = \frac{1}{N}\xi_\ell^2$ in ${}^*\mathcal{C}\ell_N$, scalar-grade Gram matrix $\Phi_\ell^{\alpha\beta} = \frac{1}{N}\langle h_\ell^\alpha (h_\ell^\beta)^{\sim}\rangle_0$, complementary expected 2-blade area $(1 - N^{-1})\det\Phi_\ell|_{2\times 2}$ | `isserlisTensor_pair_symm`, `isserlisTensor_one_sample`, `wick_fourth_moment_sub`, `linear_gbm_log_drift`, `relu_gbm_log_drift`, `smooth_shaping_drift_one_sample`, `logisticCovODE_blowup_denom_zero`, `logisticCovODE_hasDerivAt`, `hyperreal_clifford_vec_sq_euclidean` |

### Chapter 6 — Further Topics in Proportional Depth–Width Scaling (`tex/ch06_proportional_topics.tex`, `NNScaling/Ch06_ProportionalTopics.lean`)

| Source Section / Item | Stage 1 (NSA) & Stage 2 (Clifford) Monograph Coverage | Lean 4 / Verso (`NNScaling/Ch06_ProportionalTopics.lean`) |
|---|---|---|
| 6.1 Shaped Attention & Key–Query Multivectors | **Stage 2:** Geometric key–query decomposition $k^\alpha q^\beta = \langle k^\alpha q^\beta\rangle_0 + k^\alpha \wedge q^\beta \in {}^*\mathcal{C}\ell_{n_k}$, shaped Softmax expansion, token covariance SDE | `shapedAttention_colSum_eq_one`, `softmax_quadratic_numerator_identity` |
| 6.2 Spectrum, $\operatorname{Spin}(m)$ Dyson BM, & $\mathcal{C}\ell_2^+$ Burgers PDE | **Stage 2:** Spinor eigenframe evolution $u_k(\tau) = R_\tau e_k R_\tau^{\sim}$ ($R_\tau \in \operatorname{Spin}(m)$) deriving eigenvalue repulsion directly from $(e_i \wedge e_j)^2 = -1$; $\mathcal{C}\ell_2^+$ Cauchy–Dirac Stieltjes inversion | `affineInvariantMetric_congruence`, `spin_eigenframe_repulsion_balance`, `burgers_symmetric_kernel_identity`, `small_tau_discriminant_factorization` |
| 6.3 One-Step Feature Learning at Proportional Depth–Width | Exact depth-invariance of $Q_\ell$, one-step kernel shift, telescoping prediction update $R_D^g$ | `overlap_Q_depth_invariant`, `kernel_one_step_change`, `overlap_Rg_telescope` |

### Appendix A — Technical Complements (`tex/appa_technical.tex`, `NNScaling/AppendixA_Technical.lean`)

| Source Section / Item | Stage 1 (NSA) & Stage 2 (Clifford) Monograph Coverage | Lean 4 / Verso (`NNScaling/AppendixA_Technical.lean`) |
|---|---|---|
| A.1–A.4 Weak Transport, S-Equicontinuity, Skorohod Diffusion Lifting, $\operatorname{SPD}(m)$ Cometric | **Stage 2:** Distributional adjointness of vector Dirac gradient $\partial_x q$ and scalar Dirac divergence $\partial_x \lrcorner (b\rho_t)$; Keisler–Lindstrøm diffusion theorem; cometric duals | `cometric_dual_identity`, `cometric_eval_identity` |
| A.5 One-Sided & Two-Sided Gaussian Conditioning via Hestenes Blades | **Stage 2:** Coordinate-free blade projections $(u\lrcorner\bm{\Phi})\bm{\Phi}^{-1}, (v\lrcorner\bm{G})\bm{G}^{-1}$ and rejections $(u\wedge\bm{\Phi})\bm{\Phi}^{-1}, (v\wedge\bm{G})\bm{G}^{-1}$ | `twoSided_fourBlock_sum`, `twoSided_constrained_blocks_eq`, `unseen_block_frobenius_orthog_right`, `unseen_block_frobenius_orthog_left`, `invertible_blade_right_cancel` |
